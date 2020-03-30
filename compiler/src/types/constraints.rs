
use std::fmt;

use crate::{common, compiler, error, expr, structure};
use common::*;
use error::{Error, error, error_raw, TextLocation};
use expr::{Expr, ExprContent};
use structure::{
  Node, NodeId, ReferenceId, Content, PrimitiveVal, LabelId,
  VarScope, GlobalType, Reference, Nodes,
};
use crate::types::types::{
  Type, PType, TypeDefinition, FunctionInit, SymbolDefinition,
  SymbolInit, SymbolId, AbstractType,
  SignatureBuilder, TypeMapping, TypeContent,
  ResolvedSymbol, TypeInfo,
};
use crate::types::type_errors::TypeErrors;
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;

use std::collections::{HashMap, HashSet};

// A position in the program which requires a type
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSlot(Uid);

pub enum Assertion {
  Assert(TypeSlot, Type),
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
  Equalivalent(TypeSlot, TypeSlot),
  Branch { output : TypeSlot, cases : Vec<TypeSlot> },
  TypeParameter{ parent : TypeSlot, parameter : TypeSlot },
  Convert{ val : TypeSlot, into_type_slot : TypeSlot },
  SizeOf{ node : NodeId, slot : TypeSlot },
  FieldAccess {
    container : TypeSlot,
    field : Reference,
    result : TypeSlot,
  },
  Constructor {
    def_slot : TypeSlot,
    fields : Vec<(Option<Reference>, TypeSlot)>,
  },
  Function {
    function : TypeSlot,
    args : Vec<TypeSlot>,
    return_type : TypeSlot,
  },
  SymbolDef {
    symbol_id: SymbolId,
    slot: TypeSlot,
  },
  SymbolReference {
    node : NodeId,
    name : RefStr,
    result : TypeSlot,
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
  pub slots : HashMap<TypeSlot, TextLocation>,
  pub node_slots : HashMap<NodeId, TypeSlot>,
  pub literals : Vec<NodeId>,
  pub variable_slots : HashMap<ReferenceId, TypeSlot>,
  pub constraints : Vec<Constraint>,
  pub assertions : Vec<Assertion>,
}

impl Constraints {
  pub fn new() -> Self {
    Constraints {
      slots: HashMap::new(),
      node_slots: HashMap::new(),
      literals: vec![],
      variable_slots: HashMap::new(),
      constraints: vec![],
      assertions: vec![],
    }
  }

  pub fn loc(&self, slot : TypeSlot) -> TextLocation {
    *self.slots.get(&slot).unwrap()
  }
}

pub fn get_module_constraints(
  nodes : &Nodes,
  t : &mut TypeDirectory,
  mapping : &mut TypeMapping,
  cache : &StringCache,
  gen : &mut UIDGenerator,
  errors : &mut TypeErrors,
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
  errors : &mut TypeErrors,
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
  labels : HashMap<LabelId, TypeSlot>,
  type_parameters : &'l mut Vec<(RefStr, Type)>,
  t : &'l mut TypeDirectory<'t>,
  mapping : &'l mut TypeMapping,
  cache : &'l StringCache,
  gen : &'l mut UIDGenerator,
  c : &'l mut Constraints,
  errors : &'l mut TypeErrors,
}

impl <'l, 't> ConstraintGenerator<'l, 't> {

  pub fn new(
    type_parameters : &'l mut Vec<(RefStr, Type)>,
    t : &'l mut TypeDirectory<'t>,
    mapping : &'l mut TypeMapping,
    cache : &'l StringCache,
    gen : &'l mut UIDGenerator,
    c : &'l mut Constraints,
    errors : &'l mut TypeErrors,
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

  fn new_slot(&mut self, loc : TextLocation) -> TypeSlot {
    let slot = TypeSlot(self.gen.next().into());
    self.c.slots.insert(slot, loc);
    slot
  }

  fn node_to_slot(&mut self, n : &Node) -> TypeSlot {
    if let Some(slot) = self.c.node_slots.get(&n.id) { *slot }
    else {
      let slot = self.new_slot(n.loc);
      self.c.node_slots.insert(n.id, slot);
      slot
    }
  }

  fn variable_to_slot(&mut self, v : &Reference) -> TypeSlot {
    if let Some(slot) = self.c.variable_slots.get(&v.id) { *slot }
    else {
      let slot = self.new_slot(v.loc);
      self.c.variable_slots.insert(v.id, slot);
      slot
    }
  }

  fn constraint(&mut self, c : ConstraintContent) {
    let c = Constraint { id: self.gen.next(), content: c };
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSlot, b : TypeSlot) {
    self.constraint(ConstraintContent::Equalivalent(a, b));
  }

  fn assertion(&mut self, a : Assertion) {
    self.c.assertions.push(a);
  }

  fn assert_type(&mut self, slot : TypeSlot, t : Type) {
    self.assertion(Assertion::Assert(slot, t));
  }

  fn assert(&mut self, slot : TypeSlot, t : PType) {
    self.assert_type(slot, t.into());
  }

  fn tag_slot(&mut self, slot : TypeSlot, type_expr : &Expr) {
    if let Some(t) = self.expr_to_type(type_expr) {
      self.assert_type(slot, t);
    }
  }

  fn create_symbol_id(&mut self, node_id : NodeId) -> SymbolId {
    let symbol_id = self.t.new_unit_id.new_symbol_id(self.gen);
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
    let symbol_slot = self.new_slot(node.loc);
    self.assert_type(symbol_slot, function_type);
    // Process the body
    let is_polymorphic_def = type_vars.len() > 0;
    if !is_polymorphic_def {
      // Register argument types. MUST happen before gathering the body constraints.
      let args = args.iter().map(|arg| self.variable_to_slot(arg)).collect();
      // Need new scope stack for new function body.
      let mut ngc = ConstraintGenerator::new(
        self.type_parameters, self.t, self.mapping, self.cache,
        self.gen, self.c, self.errors
      );
      // Gather constraints for the body of the function. The arguments MUST be processed
      // first so that their type symbols are available.
      let body_slot = ngc.process_node(n, body);
      ngc.constraint(Function {
        function: symbol_slot,
        args,
        return_type: body_slot,
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
        unit_id: self.t.new_unit_id,
        name: name.clone(),
        type_tag: Type::any(),
        initialiser: SymbolInit::Function(f),
        type_vars: type_vars.iter().cloned().collect(),
      }
    });
    // Bind the symbol definition to its type symbol
    self.constraint(SymbolDef {
      symbol_id,
      slot: symbol_slot,
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

  pub fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSlot {
    use ConstraintContent::*;
    let node = n.node(id);
    let slot = self.node_to_slot(node);
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
        self.assert_type(slot, t);
        self.c.literals.push(id);
      }
      Content::VariableInitialise{ name, type_tag, value, var_scope } => {
        self.assert(slot, PType::Void);
        let var_slot = match var_scope {
          VarScope::Local => self.variable_to_slot(name),
          VarScope::Global(_) => self.new_slot(name.loc),
        };
        if let Some(t) = type_tag {
          self.tag_slot(var_slot, t);
        }
        let vid = self.process_node(n, *value);
        self.equalivalent(var_slot, vid);
        if let VarScope::Global(global_type) = *var_scope {
          let initialiser = match global_type {
            GlobalType::CBind => SymbolInit::CBind,
            GlobalType::Normal => SymbolInit::Expression(*value),
          };
          let symbol_id = self.create_symbol_id(id);
          self.t.create_symbol(SymbolDefinition {
            id: symbol_id,
            unit_id: self.t.new_unit_id,
            name: name.name.clone(),
            type_tag: Type::any(),
            initialiser,
            type_vars: vec![],
          });
          self.constraint(SymbolDef{
            symbol_id,
            slot: var_slot,
          });          
        }
      }
      Content::Assignment{ assignee , value } => {
        self.assert(slot, PType::Void);
        let a = self.process_node(n, *assignee);
        let b = self.process_node(n, *value);
        self.equalivalent(a, b);
      }
      Content::IfThen{ condition, then_branch } => {
        self.assert(slot, PType::Void);
        let cond = self.process_node(n, *condition);
        self.assert(cond, PType::Bool);
        self.process_node(n, *then_branch);
      }
      Content::IfThenElse{ condition, then_branch, else_branch } => {
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        let else_br = self.process_node(n, *else_branch);
        self.assert(cond, PType::Bool);
        self.constraint(Branch { output: slot, cases: vec![then_br, else_br]});
      }
      Content::Block(ns) => {
        let len = ns.len();
        if len > 0 {
          for child in &ns[0..(len-1)] {
            self.process_node(n, *child);
          }
          let c = self.process_node(n, ns[len-1]);
          self.equalivalent(slot, c);
        }
        else {
          self.assert(slot, PType::Void);
        }
      }
      Content::Quote(_e) => {
        let t = Type::unresolved_def(self.cache.get("expr"));
        self.assert_type(slot, Type::ptr_to(t));
      }
      Content::Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_slot(n.symbol(*refers_to));
          self.equalivalent(slot, var_type);
        }
        else {
          self.constraint(SymbolReference{ node: id, name: name.clone(), result: slot });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, type_vars, body } => {
        self.assert(slot, PType::Void);
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
          let sig : Type = sig.into();
          if is_polymorphic_def {
            let mut polytypes_used = HashSet::new();
            sig.find_polytypes(&mut polytypes_used);
            let unused_polytypes =
              polytypes.iter()
              .filter(|&v| !polytypes_used.contains(v.as_ref()))
              .cloned().collect::<Vec<_>>();
            if unused_polytypes.len() > 0 {
              let m = format!("unused type vars {:?} in polymorphic function definition", unused_polytypes);
              gc.errors.push(error_raw(node.loc, m));
            }
          }
          gc.process_function_def(
            n, id, sig, polytypes.as_slice(), arg_names, *body, name);
        });
      }
      Content::CBind { name, type_tag } => {
        self.assert(slot, PType::Void);
        let cbind_slot = self.new_slot(node.loc);
        if let Some(t) = self.expr_to_type(type_tag) {
          self.assert_type(cbind_slot, t);
        }
        let symbol_id = self.create_symbol_id(id);
        self.constraint(SymbolDef {
          symbol_id,
          slot: cbind_slot,
        });
        self.t.create_symbol(SymbolDefinition {
          id: symbol_id,
          unit_id: self.t.new_unit_id,
          name: name.clone(),
          initialiser: SymbolInit::CBind,
          type_tag: Type::any(),
          type_vars: vec![],
        });
      }
      Content::TypeAlias { alias, type_aliased } => {
        // TODO: not yet implemented
        self.assert(slot, PType::Void);
      }
      Content::TypeDefinition{ name, kind, fields, type_vars } => {
        self.assert(slot, PType::Void);
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
              unit_id: gc.t.new_unit_id,
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
          let field_slot = self.process_node(n, *value);
          let field = field.clone();
          fields.push((field, field_slot));
        }
        let def_type = Type::unresolved_def(name.name.clone());
        self.assert_type(slot, def_type);
        let tc = Constructor{ def_slot: slot, fields };
        self.constraint(tc);
      }
      Content::FieldAccess{ container, field } => {
        let fa = FieldAccess {
          container: self.process_node(n, *container),
          field: field.clone(),
          result: slot,
        };
        self.constraint(fa);
      }
      Content::ArrayLiteral(ns) => {
        let element_slot = self.new_slot(node.loc);
        for element in ns.iter() {
          let el = self.process_node(n, *element);
          self.equalivalent(el, element_slot);
        }
        let mut array_type = Type::unresolved_def(self.cache.get("array"));
        array_type.children.push(Type::any());
        self.assert_type(slot, array_type);
        self.constraint(TypeParameter{ parent: slot, parameter: element_slot });
      }
      Content::FunctionCall{ function, args } => {
        let function = self.process_node(n, *function);
        let fc = Function {
          function,
          args: args.iter().map(|id| self.process_node(n, *id)).collect(),
          return_type: slot,
        };
        let mut sig = SignatureBuilder::new(Type::any());
        for _ in args {
          sig.append_arg(Type::any());
        }
        self.assert_type(function, sig.into());
        self.constraint(fc);
      }
      Content::While{ condition, body } => {
        self.assert(slot, PType::Void);
        let cond = self.process_node(n, *condition);
        self.process_node(n, *body);
        self.assert(cond, PType::Bool);
      }
      Content::Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        self.tag_slot(slot, into_type);
        let c = Convert { val: v, into_type_slot: slot };
        self.constraint(c);
      }
      Content::SizeOf{ type_tag } => {
        let size_slot = self.new_slot(type_tag.loc);
        self.tag_slot(size_slot, type_tag);
        self.constraint(SizeOf{
          node: id,
          slot : size_slot
        });
        self.assert(slot, PType::U64);
      }
      Content::Label{ label, body } => {
        self.labels.insert(*label, slot);
        let body = self.process_node(n, *body);
        self.equalivalent(slot, body);
      }
      Content::BreakToLabel{ label, return_value } => {
        self.assert(slot, PType::Void);
        let label_slot = *self.labels.get(label).unwrap();
        if let Some(v) = return_value {
          let v = self.process_node(n, *v);
          self.equalivalent(label_slot, v);
        }
        else {
          self.assert(label_slot, PType::Void);
        }
      }
    }
    slot
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

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  pub imports : Vec<UnitId>,
  pub new_unit_id : UnitId,
  pub types : &'a mut HashMap<UnitId, TypeInfo>,
  polytype_bindings : HashMap<RefStr, Type>,
  symbol_results : Vec<ResolvedSymbol>,
}

// TODO: A lot of these functions are slow because they iterate through everything.
// This could probably be improved with some caching, although any caching needs to
// be wary of new symbols being added.
impl <'a> TypeDirectory<'a> {
  pub fn new(imports : Vec<UnitId>, new_unit_id : UnitId, types : &'a mut HashMap<UnitId, TypeInfo>) -> Self {
    TypeDirectory {
      imports, new_unit_id, types,
      polytype_bindings: HashMap::new(),
      symbol_results: vec![],
    }
  }

  pub fn get_symbol(&self, id : SymbolId) -> &SymbolDefinition {
    self.types.get(&id.uid).unwrap().symbols.get(&id).unwrap()
  }

  pub fn get_symbol_mut(&mut self, id : SymbolId) -> &mut SymbolDefinition {
    self.types.get_mut(&id.uid).unwrap()
      .symbols.get_mut(&id).unwrap()
  }

  pub fn get_type_def(&self, name : &str, unit_id : UnitId) -> &TypeDefinition {
    self.types.get(&unit_id).unwrap()
      .type_defs.get(name).unwrap()
  }

  pub fn get_type_def_mut(&mut self, name : &str) -> &mut TypeDefinition {
    self.types.get_mut(&self.new_unit_id).unwrap()
      .type_defs.get_mut(name).unwrap()
  }

  pub fn create_type_def(&mut self, def : TypeDefinition) {
    self.types.get_mut(&self.new_unit_id).unwrap()
      .type_defs.insert(def.name.clone(), def);
  }

  pub fn create_symbol(&mut self, def : SymbolDefinition) {
    self.types.get_mut(&self.new_unit_id).unwrap()
      .symbols.insert(def.id, def);
  }

  /// Returns a slice of all matching definitions
  pub fn find_symbol(
    &mut self,
    name : &str,
    t : &Type,
  )
    -> &[ResolvedSymbol]
  {
    self.polytype_bindings.clear();
    self.symbol_results.clear();
    self.types.get(&self.new_unit_id).unwrap()
      .find_symbol(name, t, &mut self.polytype_bindings, &mut self.symbol_results);
    for uid in self.imports.iter() {
      let type_info = self.types.get(uid).unwrap();
      type_info.find_symbol(name, t, &mut self.polytype_bindings, &mut self.symbol_results);
    }
    self.symbol_results.as_slice()
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
    self.types.get(&self.new_unit_id).unwrap()
      .find_type_def(name).or_else(||
        self.imports.iter().rev().flat_map(|uid| {
          let type_info = self.types.get(uid).unwrap();
          type_info.find_type_def(name)
        }).next()
      )
  }
}
