
use std::fmt;

use crate::{compiler, error, expr, structure, types};
use error::{Error, error, error_raw, TextLocation};
use expr::{Expr, ExprContent, UIDGenerator, Uid, RefStr, StringCache};
use structure::{
  Node, NodeId, ReferenceId, Content, PrimitiveVal, LabelId,
  VarScope, GlobalType, Reference, Nodes,
};
use types::{
  Type, PType, TypeDefinition, FunctionInit, SymbolDefinition,
  TypeDirectory, SymbolInit, SymbolId, AbstractType,
  SignatureBuilder, TypeMapping, TypeContent,
};
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(Uid);

pub enum Assertion {
  Assert(TypeSymbol, Type),
  AssertTypeDef {
    typename: RefStr,
    fields : Vec<Option<(Type, TextLocation)>>,
  },
}

pub struct Constraint {
  pub id : Uid,
  pub content : ConstraintContent,
}

pub enum ConstraintContent {
  Equalivalent(TypeSymbol, TypeSymbol),
  Branch { output : TypeSymbol, cases : Vec<TypeSymbol> },
  TypeParameter{ parent : TypeSymbol, parameter : TypeSymbol },
  Convert{ val : TypeSymbol, into_type_ts : TypeSymbol },
  SizeOf{ node : NodeId, ts : TypeSymbol },
  FieldAccess {
    container : TypeSymbol,
    field : Reference,
    result : TypeSymbol,
  },
  Constructor {
    def_ts : TypeSymbol,
    fields : Vec<(Option<Reference>, TypeSymbol)>,
  },
  Function {
    function : TypeSymbol,
    args : Vec<TypeSymbol>,
    return_type : TypeSymbol,
  },
  SymbolDef {
    symbol_id: SymbolId,
    type_symbol: TypeSymbol,
  },
  SymbolReference {
    node : NodeId,
    name : RefStr,
    result : TypeSymbol,
  },
}

impl  fmt::Display for Constraint {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ConstraintContent::*;
    match &self.content {
      Equalivalent(_, _) => write!(f, "Equalivalent"),
      Branch{ .. } => write!(f, "Branch"),
      TypeParameter{ .. } => write!(f, "TypeParameter"),
      Convert{ .. } => write!(f, "Convert"),
      FieldAccess { field, .. } => write!(f, "FieldAccess {}", field.name),
      Constructor { .. } => write!(f, "Constructor"),
      Function { args, .. } =>
        write!(f, "FunctionCall ({} args)", args.len()),
      SymbolDef { .. } => write!(f, "SymbolDef"),
      SymbolReference { name, .. } => write!(f, "SymbolRef {}", name),
      SizeOf{ .. } => write!(f, "SizeOf"),
    }
  }
}

pub struct Constraints {
  pub symbols : HashMap<TypeSymbol, TextLocation>,
  pub node_symbols : HashMap<NodeId, TypeSymbol>,
  pub literals : Vec<NodeId>,
  pub variable_symbols : HashMap<ReferenceId, TypeSymbol>,
  pub constraints : Vec<Constraint>,
  pub assertions : Vec<Assertion>,
}

impl Constraints {
  pub fn new() -> Self {
    Constraints {
      symbols: HashMap::new(),
      node_symbols: HashMap::new(),
      literals: vec![],
      variable_symbols: HashMap::new(),
      constraints: vec![],
      assertions: vec![],
    }
  }
}

#[derive(Default)]
pub struct Errors {
  pub concrete_errors : Vec<Error>,

  /// to avoid duplicate errors
  pub failed_constraint_ids : HashSet<Uid>,
}

impl Errors {
  pub fn new() -> Self { Default::default() }

  pub fn push(&mut self, e : Error) {
    self.concrete_errors.push(e);
  }

  pub fn is_empty(&self) -> bool {
    self.concrete_errors.is_empty()
  }
}

pub fn get_module_constraints(
  nodes : &Nodes,
  t : &mut TypeDirectory,
  mapping : &mut TypeMapping,
  cache : &StringCache,
  gen : &mut UIDGenerator,
  errors : &mut Errors,
) -> Constraints
{
  let mut c = Constraints::new();
  let mut type_parameters = vec![];
  ConstraintGenerator::new(&mut type_parameters, t, mapping, cache, gen, &mut c, errors)
    .process_node(nodes, nodes.root);
  c
}

pub fn get_polymorphic_function_instance_constraints(
  n : &Nodes,
  id : NodeId,
  instanced_function_type : Type,
  instanced_type_vars : &[Type],
  t : &mut TypeDirectory,
  mapping : &mut TypeMapping,
  cache : &StringCache,
  gen : &mut UIDGenerator,
  errors : &mut Errors,
) -> (Constraints, SymbolId)
{
  let mut c = Constraints::new();
  let mut type_parameters = vec![];
  let symbol_id =
    ConstraintGenerator::new(
      &mut type_parameters, t, mapping, cache, gen, &mut c, errors)
    .process_polymorphic_function_instance(n, id, instanced_function_type, instanced_type_vars);
  (c, symbol_id)
}

pub struct ConstraintGenerator<'l, 't> {
  labels : HashMap<LabelId, TypeSymbol>,
  type_parameters : &'l mut Vec<(RefStr, Type)>,
  t : &'l mut TypeDirectory<'t>,
  mapping : &'l mut TypeMapping,
  cache : &'l StringCache,
  gen : &'l mut UIDGenerator,
  c : &'l mut Constraints,
  errors : &'l mut Errors,
}

impl <'l, 't> ConstraintGenerator<'l, 't> {

  pub fn new(
    type_parameters : &'l mut Vec<(RefStr, Type)>,
    t : &'l mut TypeDirectory<'t>,
    mapping : &'l mut TypeMapping,
    cache : &'l StringCache,
    gen : &'l mut UIDGenerator,
    c : &'l mut Constraints,
    errors : &'l mut Errors,
  ) -> Self
  {
    ConstraintGenerator {
      labels: HashMap::new(),
      type_parameters,
      cache, t, mapping, gen, c,
      errors,
    }
  }

  fn log_error<V>(&mut self, r : Result<V, Error>) -> Option<V> {
    match r {
      Ok(v) => Some(v),
      Err(e) => { self.errors.push(e); None } 
    }
  }

  fn type_symbol(&mut self, loc : TextLocation) -> TypeSymbol {
    let ts = TypeSymbol(self.gen.next().into());
    self.c.symbols.insert(ts, loc);
    ts
  }

  fn node_to_symbol(&mut self, n : &Node) -> TypeSymbol {
    if let Some(ts) = self.c.node_symbols.get(&n.id) { *ts }
    else {
      let ts = self.type_symbol(n.loc);
      self.c.node_symbols.insert(n.id, ts);
      ts
    }
  }

  fn variable_to_type_symbol(&mut self, v : &Reference) -> TypeSymbol {
    if let Some(ts) = self.c.variable_symbols.get(&v.id) { *ts }
    else {
      let ts = self.type_symbol(v.loc);
      self.c.variable_symbols.insert(v.id, ts);
      ts
    }
  }

  fn constraint(&mut self, c : ConstraintContent) {
    let c = Constraint { id: self.gen.next(), content: c };
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.constraint(ConstraintContent::Equalivalent(a, b));
  }

  fn assertion(&mut self, a : Assertion) {
    self.c.assertions.push(a);
  }

  fn assert_type(&mut self, ts : TypeSymbol, t : Type) {
    self.assertion(Assertion::Assert(ts, t));
  }

  fn assert(&mut self, ts : TypeSymbol, t : PType) {
    self.assert_type(ts, t.into());
  }

  fn tag_symbol(&mut self, ts : TypeSymbol, type_expr : &Expr) {
    if let Some(t) = self.expr_to_type(type_expr) {
      self.assert_type(ts, t);
    }
  }

  fn create_symbol_id(&mut self, node_id : NodeId) -> SymbolId {
    let symbol_id = self.t.new_unit_id().new_symbol_id(self.gen);
    self.mapping.symbol_def_nodes.insert(symbol_id, node_id);
    symbol_id
  }

  fn process_function_def(
    &mut self,
    n : &Nodes, id : NodeId,
    function_type : Type,
    type_vars : &[RefStr],
    args : Vec<Reference>,
    body : NodeId,
    name : &RefStr)
      -> SymbolId
  {
    use ConstraintContent::*;
    let node = n.node(id);
    // Assert type of the symbol
    let symbol_ts = self.type_symbol(node.loc);
    self.assert_type(symbol_ts, function_type);
    // Process the body
    let is_polymorphic_def = type_vars.len() > 0;
    if !is_polymorphic_def {
      // Register argument types. MUST happen before gathering the body constraints.
      let args = args.iter().map(|arg| self.variable_to_type_symbol(arg)).collect();
      // Need new scope stack for new function body.
      let mut ngc = ConstraintGenerator::new(
        self.type_parameters, self.t, self.mapping, self.cache,
        self.gen, self.c, self.errors
      );
      // Gather constraints for the body of the function. The arguments MUST be processed
      // first so that their type symbols are available.
      let body_ts = ngc.process_node(n, body);
      ngc.constraint(Function {
        function: symbol_ts,
        args,
        return_type: body_ts,
      });
    }
    // Register the symbol definition
    let symbol_id = self.create_symbol_id(id);
    self.t.create_symbol({
      let name_for_codegen =
      self.cache.get(format!("{}.{}", name, self.gen.next()).as_str());
      let f = FunctionInit {
        body: body,
        name_for_codegen,
        args,
      };
      SymbolDefinition {
        id: symbol_id,
        unit_id: self.t.new_unit_id(),
        name: name.clone(),
        type_tag: Type::any(),
        initialiser: SymbolInit::Function(f),
        type_vars: type_vars.iter().cloned().collect(),
      }
    });
    // Bind the symbol definition to its type symbol
    self.constraint(SymbolDef {
      symbol_id,
      type_symbol: symbol_ts,
    });
    symbol_id
  }

  pub fn process_polymorphic_function_instance(&mut self, n : &Nodes, id : NodeId, instanced_function_type : Type, instanced_type_vars : &[Type]) 
    -> SymbolId
  {
    let node = n.node(id);
    match &node.content {
      Content::FunctionDefinition{ name, args, return_tag:_, type_vars, body } => {
        if DEBUG {
          println!("####################################################");
          println!("Process polymorphic instance: {}", name);
          println!("Instance signature: {}", instanced_function_type);
          print!("Args: [");
          for (r, e) in args {
            print!("{} : {:?}, ", r.name, e);
          }
          println!("]");
          println!("Type var instances: {:?}",
            type_vars.iter().zip(instanced_type_vars).collect::<Vec<_>>());
          println!("####################################################");
        }
        self.with_instanced_type_parameters(type_vars.as_slice(), instanced_type_vars, |gc| {
          let args = args.iter().map(|x| x.0.clone()).collect();
          gc.process_function_def(n, id, instanced_function_type, &[], args, *body, name)
        })
      }
      _ => panic!("unexpected node! expected polymorphic function definition."),
    }
  }

  pub fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
    use ConstraintContent::*;
    let node = n.node(id);
    let ts = self.node_to_symbol(node);
    match &node.content {
      Content::Literal(val) => {
        use PrimitiveVal::*;
        let t : Type = match val {
          Float(_) => {
            AbstractType::Float.into()
          }
          Int(_) => {
            AbstractType::Integer.into()
          }
          Bool(_) => PType::Bool.into(),
          Void => PType::Void.into(),
          String(_) => {
            Type::unresolved_def(self.cache.get("string"))
          }
        };
        self.assert_type(ts, t);
        self.c.literals.push(id);
      }
      Content::VariableInitialise{ name, type_tag, value, var_scope } => {
        self.assert(ts, PType::Void);
        let var_type_symbol = match var_scope {
          VarScope::Local => self.variable_to_type_symbol(name),
          VarScope::Global(_) => self.type_symbol(name.loc),
        };
        if let Some(t) = type_tag {
          self.tag_symbol(var_type_symbol, t);
        }
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
        if let VarScope::Global(global_type) = *var_scope {
          let initialiser = match global_type {
            GlobalType::CBind => SymbolInit::CBind,
            GlobalType::Normal => SymbolInit::Expression(*value),
          };
          let symbol_id = self.create_symbol_id(id);
          self.t.create_symbol(SymbolDefinition {
            id: symbol_id,
            unit_id: self.t.new_unit_id(),
            name: name.name.clone(),
            type_tag: Type::any(),
            initialiser,
            type_vars: vec![],
          });
          self.constraint(SymbolDef{
            symbol_id,
            type_symbol: var_type_symbol,
          });          
        }
      }
      Content::Assignment{ assignee , value } => {
        self.assert(ts, PType::Void);
        let a = self.process_node(n, *assignee);
        let b = self.process_node(n, *value);
        self.equalivalent(a, b);
      }
      Content::IfThen{ condition, then_branch } => {
        self.assert(ts, PType::Void);
        let cond = self.process_node(n, *condition);
        self.assert(cond, PType::Bool);
        self.process_node(n, *then_branch);
      }
      Content::IfThenElse{ condition, then_branch, else_branch } => {
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        let else_br = self.process_node(n, *else_branch);
        self.assert(cond, PType::Bool);
        self.constraint(Branch { output: ts, cases: vec![then_br, else_br]});
      }
      Content::Block(ns) => {
        let len = ns.len();
        if len > 0 {
          for child in &ns[0..(len-1)] {
            self.process_node(n, *child);
          }
          let c = self.process_node(n, ns[len-1]);
          self.equalivalent(ts, c);
        }
        else {
          self.assert(ts, PType::Void);
        }
      }
      Content::Quote(_e) => {
        let t = Type::unresolved_def(self.cache.get("expr"));
        self.assert_type(ts, Type::ptr_to(t));
      }
      Content::Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_type_symbol(n.symbol(*refers_to));
          self.equalivalent(ts, var_type);
        }
        else {
          self.constraint(SymbolReference{ node: id, name: name.clone(), result: ts });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, type_vars, body } => {
        self.assert(ts, PType::Void);
        self.with_type_parameters(type_vars.as_slice(), |gc, polytypes| {
          let is_polymorphic_def = polytypes.len() > 0;
          // Determine return type
          let return_type : Type = {
            if let Some(rt) = return_tag.as_ref().and_then(|e| gc.expr_to_type(e)) {
              rt
            }
            // Polymorphic defs assume no explicit return type means void.
            // Monomorphic defs can infer it from the body.
            else if is_polymorphic_def {
              PType::Void.into()
            }
            else {
              Type::any()
            }
          };
          // Build initial function signature
          let mut sig = SignatureBuilder::new(return_type);
          let mut arg_names = vec!();
          for (arg, type_tag) in args.iter() {
            arg_names.push(arg.clone());
            if let Some(t) = type_tag.as_ref().and_then(|e| gc.expr_to_type(e)) {
              sig.append_arg(t);
            }
            else {
              sig.append_arg(Type::any());
            }
          }
          gc.process_function_def(
            n, id, sig.into(), polytypes.as_slice(), arg_names, *body, name);
        });
      }
      Content::CBind { name, type_tag } => {
        self.assert(ts, PType::Void);
        let cbind_ts = self.type_symbol(node.loc);
        if let Some(t) = self.expr_to_type(type_tag) {
          self.assert_type(cbind_ts, t);
        }
        let symbol_id = self.create_symbol_id(id);
        self.constraint(SymbolDef {
          symbol_id,
          type_symbol: cbind_ts,
        });
        self.t.create_symbol(SymbolDefinition {
          id: symbol_id,
          unit_id: self.t.new_unit_id(),
          name: name.clone(),
          initialiser: SymbolInit::CBind,
          type_tag: Type::any(),
          type_vars: vec![],
        });
      }
      Content::TypeAlias { alias, type_aliased } => {
        // TODO: not yet implemented
        self.assert(ts, PType::Void);
      }
      Content::TypeDefinition{ name, kind, fields, type_vars } => {
        self.assert(ts, PType::Void);
        if self.t.find_type_def(name.as_ref()).is_some() {
          let e = error_raw(node.loc, "type with this name already defined");
          self.errors.push(e)
        }
        else {
          self.with_type_parameters(type_vars.as_slice(), |gc, type_vars| {
            // TODO: check for duplicate fields?
            let mut field_types = vec![];
            for (_, type_tag) in fields.iter() {
              field_types.push(
                type_tag.as_ref()
                  .and_then(|e| gc.expr_to_type(e).map(|t| (t, e.loc)))
              );
            }
            gc.assertion(Assertion::AssertTypeDef {
              typename: name.clone(), fields: field_types,
            });
            let def = TypeDefinition {
              name: name.clone(),
              unit_id: gc.t.new_unit_id(),
              fields: fields.iter().map(|(f, _)| (f.clone(), Type::any())).collect(),
              kind: *kind,
              type_vars,
            };
            gc.mapping.type_def_nodes.insert(name.clone(), id);
            gc.t.create_type_def(def);
          });
        }
      }
      Content::TypeConstructor{ name, field_values } => {
        let mut fields = vec![];
        for (field, value) in field_values.iter() {
          let field_type_symbol = self.process_node(n, *value);
          let field = field.clone();
          fields.push((field, field_type_symbol));
        }
        let def_type = Type::unresolved_def(name.name.clone());
        self.assert_type(ts, def_type);
        let tc = Constructor{ def_ts: ts, fields };
        self.constraint(tc);
      }
      Content::FieldAccess{ container, field } => {
        let fa = FieldAccess {
          container: self.process_node(n, *container),
          field: field.clone(),
          result: ts,
        };
        self.constraint(fa);
      }
      Content::ArrayLiteral(ns) => {
        let element_ts = self.type_symbol(node.loc);
        for element in ns.iter() {
          let el = self.process_node(n, *element);
          self.equalivalent(el, element_ts);
        }
        let mut array_type = Type::unresolved_def(self.cache.get("array"));
        array_type.children.push(Type::any());
        self.assert_type(ts, array_type);
        self.constraint(TypeParameter{ parent: ts, parameter: element_ts });
      }
      Content::FunctionCall{ function, args } => {
        let function = self.process_node(n, *function);
        let fc = Function {
          function,
          args: args.iter().map(|id| self.process_node(n, *id)).collect(),
          return_type: ts,
        };
        self.constraint(fc);
      }
      Content::While{ condition, body } => {
        self.assert(ts, PType::Void);
        let cond = self.process_node(n, *condition);
        self.process_node(n, *body);
        self.assert(cond, PType::Bool);
      }
      Content::Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        self.tag_symbol(ts, into_type);
        let c = Convert { val: v, into_type_ts: ts };
        self.constraint(c);
      }
      Content::SizeOf{ type_tag } => {
        let size_ts = self.type_symbol(type_tag.loc);
        self.tag_symbol(size_ts, type_tag);
        self.constraint(SizeOf{
          node: id,
          ts : size_ts
        });
        self.assert(ts, PType::U64);
      }
      Content::Label{ label, body } => {
        self.labels.insert(*label, ts);
        let body = self.process_node(n, *body);
        self.equalivalent(ts, body);
      }
      Content::BreakToLabel{ label, return_value } => {
        self.assert(ts, PType::Void);
        let label_ts = *self.labels.get(label).unwrap();
        if let Some(v) = return_value {
          let v = self.process_node(n, *v);
          self.equalivalent(label_ts, v);
        }
        else {
          self.assert(label_ts, PType::Void);
        }
      }
    }
    ts
  }

  fn with_instanced_type_parameters<F, T>(
    &mut self, type_parameters : &[RefStr],
    types : &[Type],
    f : F
  ) -> T
    where F : FnOnce(&mut ConstraintGenerator) -> T
  {
    for (i, pt) in type_parameters.iter().enumerate() {
      let t = types[i].clone();
      self.type_parameters.push((pt.clone(), t));
    }
    let result = f(self);
    self.type_parameters.drain((self.type_parameters.len()-type_parameters.len())..);
    result
  }

  fn with_type_parameters<F>(&mut self, type_parameters : &[RefStr], f : F)
    where F : Fn(&mut ConstraintGenerator, Vec<RefStr>)
  {
    for pt in type_parameters.iter() {
      let t = TypeContent::Polytype(pt.clone()).into();
      self.type_parameters.push((pt.clone(), t));
    }
    f(self, type_parameters.iter().cloned().collect());
    self.type_parameters.drain((self.type_parameters.len()-type_parameters.len())..);
  }

  fn symbol_to_type(&mut self, name : &str) -> Type {
      // Check for polytypes
      for (polytype_name, t) in self.type_parameters.iter().rev() {
        if polytype_name.as_ref() == name {
          return t.clone();
        }
      }
      // Assume type definition
      let name = self.cache.get(name);
      return Type::unresolved_def(name);
  }

  /// Converts expression into type.
  fn expr_to_type(&mut self, expr : &Expr) -> Option<Type> {
    fn expr_to_type_internal(gc: &mut ConstraintGenerator, expr : &Expr) -> Result<Type, Error> {
      if let ExprContent::LiteralUnit = &expr.content {
        return Ok(PType::Void.into());
      }
      if let Some(name) = expr.try_symbol() {
        // Check for primitive types
        if let Some(t) = Type::from_string(name) {
          return Ok(t);
        }
        return Ok(gc.symbol_to_type(name));
      }
      match expr.try_construct() {
        Some(("fun", es)) => {
          if let Some(args) = es.get(0) {
            let return_type = 
              if let Some(t) = es.get(1) { expr_to_type_internal(gc, t)? }
              else { PType::Void.into() };
            let mut sig = SignatureBuilder::new(return_type);
            for e in args.children().iter() {
              let e = if let Some((":", [_name, tag])) = e.try_construct() {tag} else {e};
              sig.append_arg(expr_to_type_internal(gc, e)?);
            }
            return Ok(sig.into());
          }
        }
        Some(("call", exprs)) => {
          let name = &exprs[0];
          match name.unwrap_symbol()? {
            "ptr" => {
              if let [t] = &exprs[1..] {
                let t = expr_to_type_internal(gc, t)?;
                return Ok(t.ptr_to())
              }
            }
            name => {
              let mut t = gc.symbol_to_type(name);
              for e in &exprs[1..] {
                t.children.push(expr_to_type_internal(gc, e)?);
              }
              return Ok(t);
            }
          }
        }
        _ => ()
      }
      error(expr, format!("invalid type expression {}", expr))
    }
    let r = expr_to_type_internal(self, expr);
    self.log_error(r)
  }
}  