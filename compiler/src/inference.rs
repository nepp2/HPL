
use std::fmt;
use itertools::Itertools;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{Expr, UIDGenerator, RefStr, StringCache};
use crate::structure::{
  Node, NodeId, Nodes, SymbolId,
  Content, Val, LabelId, TypeKind,
  VarScope, GlobalType, Symbol,
};
use crate::types::{
  Type, TypeContent, PType, TypeInfo, TypeDefinition, ConcreteGlobal,
  FunctionInit, GlobalDefinition, TypeDirectory, GlobalInit,
  AbstractType, SignatureBuilder, incremental_unify, IncrementalUnifyResult
};
use crate::modules::TypedModule;

use std::collections::HashMap;

use TypeContent::*;

pub fn infer_types(
  nodes : Nodes,
  imports : &[&TypeInfo],
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<TypedModule, Vec<Error>>
{
  let mut c = Constraints::new();
  let mut cg = CodegenInfo::new();
  let mut errors = vec![];
  let module_id = gen.next().into();
  let mut new_module = TypeInfo::new(module_id);
  let mut type_directory =
  TypeDirectory::new(module_id, imports, &mut new_module);
  gather_constraints(
    &mut type_directory, &mut cg, cache,
    gen, &mut c, &mut errors, &nodes);
  let mut i = 
    Inference::new(
      &nodes, &mut type_directory,
      &mut cg, &c, cache, gen, &mut errors);
  i.infer();
  if errors.len() > 0 {
    Err(errors)
  }
  else {
    Ok(TypedModule::new(module_id, nodes, new_module, cg))
  }
}

pub struct CodegenInfo {
  pub node_type : HashMap<NodeId, Type>,
  pub sizeof_info : HashMap<NodeId, Type>,
  pub symbol_references : HashMap<NodeId, GlobalDefinition>, // TODO: this is slow and stupid
  pub type_def_references : HashMap<RefStr, TypeDefinition>, // TODO: this is slow and stupid
}

impl CodegenInfo {
  pub fn new() -> Self {
    CodegenInfo {
      node_type: HashMap::new(),
      sizeof_info: HashMap::new(),
      symbol_references: HashMap::new(),
      type_def_references: HashMap::new(),
    }
  }
}

struct Inference<'a> {
  nodes : &'a Nodes,
  t : &'a mut TypeDirectory<'a>,
  cg : &'a mut CodegenInfo,
  c : &'a Constraints,
  cache : &'a StringCache,
  gen : &'a mut UIDGenerator,
  errors : &'a mut Vec<Error>,
  resolved : HashMap<TypeSymbol, Type>,
  resolution_step : i64,
}

impl <'a> Inference<'a> {

  fn new(
    nodes : &'a Nodes,
    t : &'a mut TypeDirectory<'a>,
    cg : &'a mut CodegenInfo,
    c : &'a Constraints,
    cache : &'a StringCache,
    gen : &'a mut UIDGenerator,
    errors : &'a mut Vec<Error>)
      -> Self
  {
    Inference {
      nodes, t, cg, c, cache, gen, errors,
      resolved: HashMap::new(),
      resolution_step : 0,
    }
  }

  fn get_type(&self, ts : TypeSymbol) -> Option<&Type> {
    self.resolved.get(&ts)
  }

  fn unify_mut(&mut self, ts : TypeSymbol, t : &mut Type) -> IncrementalUnifyResult {
    if let Some(prev_t) = self.resolved.get(&ts) {
      let r = incremental_unify(prev_t, t);
      if r == IncrementalUnifyResult::Failure {
        let e = error_raw(self.loc(ts), format!("conflicting types inferred; {} and {}.", t, prev_t));
        self.errors.push(e);
      }
      r
    }
    else {
      IncrementalUnifyResult::ChangedOld
    }
  }

  fn unify(&mut self, ts : TypeSymbol, mut t : Type) -> Option<Type> {
    if self.unify_mut(ts, &mut t) == IncrementalUnifyResult::ChangedOld {
      return Some(t);
    }
    None
  }

  fn type_updated(&mut self, ts : TypeSymbol) {
    self.resolution_step += 1;
    let aaa = (); // TODO: trigger recalculations
  }

  fn update_type(&mut self, ts : TypeSymbol, t : Type) {
    if let Some(t) = self.unify(ts, t) {
      self.resolved.insert(ts, t);
      self.type_updated(ts);
    }
  }

  fn update_type_mut(&mut self, ts : TypeSymbol, t : &mut Type) -> IncrementalUnifyResult {
    let r = self.unify_mut(ts, t);
    if r == IncrementalUnifyResult::ChangedOld {
      self.resolved.insert(ts, t.clone());
      self.type_updated(ts);
    }
    r
  }

  fn loc(&self, ts : TypeSymbol) -> TextLocation {
    *self.c.symbols.get(&ts).unwrap()
  }

  fn unresolved_constraint_error(&mut self, c : &Constraint) {
    let e = match c  {
      Constraint::Assert(_ts, _t) => panic!(),
      Constraint::Equalivalent(_a, _b) => return,
      Constraint::FunctionDef{ name, loc, args, .. } => {
        error_raw(loc,
          format!("function definition '{}({})' not resolved", name,
            args.iter().map(|(s, ts)| {
              let t = self.get_type(*ts)
                .map(|t| format!("{}", t))
                .unwrap_or_else(|| "???".into());
              format!("{} : {}", s.name, t)
            }).join(", ")))
      }
      // this error should always be accompanied by other unresolved constraints
      Constraint::FunctionCall{ function:_, args:_, result:_ } => return,
      Constraint::Constructor { type_name, fields:_, result } => {
        error_raw(self.loc(*result),
          format!("constructor for '{}' not resolved", type_name))
      }
      Constraint::Convert { val, into_type } => {
        let any = Type::any();
        let t = self.get_type(*val).unwrap_or(&any);
        let s = format!("type conversion from {} into {} not supported", t, into_type);
        error_raw(self.loc(*val), s)
      }
      Constraint::GlobalDef { name, type_symbol:_, initialiser:_, loc } => {
        error_raw(loc,
          format!("global definition '{}' not resolved", name))
      }
      Constraint::GlobalReference { node:_, name, result } => {
        let any = Type::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols = self.t.find_global(&name, t, self.gen);
        let s = symbols.iter().map(|g| format!("      {} : {}", g.def.name, g.concrete_type)).join("\n");
        error_raw(self.loc(*result),
          format!("Reference '{}' of type '{}' not resolved\n   Symbols available:\n{}", name, t, s))
      }
      Constraint::FieldAccess{ container:_, field, result:_ } => {
        error_raw(field.loc,
          format!("field access '{}' not resolved", field.name))
      }
      Constraint::Array{ array, element:_ } => {
        error_raw(self.loc(*array), "array literal not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, def : GlobalDefinition) {
    self.cg.symbol_references.insert(node, def);
  }

  fn find_global(&mut self, name : &str, t : &Type)
    -> Option<Result<ConcreteGlobal, ()>>
  {
    match self.t.find_global(name, t, self.gen) {
      [g] => Some(Ok(g.clone())),
      _ => None,
    }
  }

  fn process_constraint(&mut self, c : &Constraint) -> bool {
    match c  {
      Constraint::Assert(ts, t) => {
        self.update_type(*ts, t.clone());
        return true;
      }
      Constraint::Equalivalent(a, b) => {
        if let Some(t) = self.get_type(*a) {
          if t.is_concrete() {
            let t = t.clone();
            self.update_type(*b, t);
            //return true;
          }
        }
        if let Some(t) = self.get_type(*b) {
          if t.is_concrete() {
            let t = t.clone();
            self.update_type(*a, t);
            //return true;
          }
        }
      }
      Constraint::FunctionDef{ name, return_type, args, body, loc } => {
        let resolved_args_count = args.iter().flat_map(|(_, ts)| self.get_type(*ts)).count();
        let return_type = self.get_type(*return_type);
        if resolved_args_count == args.len() && return_type.is_some() {
          let mut sig = SignatureBuilder::new(return_type.unwrap().clone());
          let mut arg_names = vec!();
          for (arg, arg_ts) in args.iter() {
            arg_names.push(arg.clone());
            sig.append_arg(self.get_type(*arg_ts).unwrap().clone());
          }
          let name_for_codegen =
            self.cache.get(format!("{}.{}", name, self.gen.next()).as_str());
          let f = FunctionInit {
            body: *body,
            name_for_codegen,
            args: arg_names,
          };
          let g = GlobalDefinition {
            module_id: self.t.new_module_id(),
            name: name.clone(),
            type_tag: sig.into(),
            initialiser: GlobalInit::Function(f),
            loc: *loc,
          };
          self.t.create_global(g);
          return true;
        }
      }
      Constraint::FunctionCall{ function, args, result } => {
        if let Some(t) = self.get_type(*function) {
          if let Some(mut sig) = t.sig_builder() {
            for (i, t) in sig.args().iter_mut().enumerate() {
              self.update_type_mut(args[i].1, t);
            }
            let rt = sig.return_type();
            self.update_type_mut(*result, rt);
            self.update_type(*function, sig.into());
          }
        }
        else {
          let any = Type::any();
          let return_type = self.get_type(*result).cloned().unwrap_or(any.clone());
          let mut sig = SignatureBuilder::new(return_type);
          for arg in args {
            let arg = self.get_type(arg.1).cloned().unwrap_or(any.clone());
            sig.append_arg(arg);
          }
          self.update_type(*function, sig.into());
        }
        if self.get_type(*function).unwrap().is_concrete() {
          return true;
        }
      }
      Constraint::Constructor { type_name, fields, result } => {
        if let Some(def) = self.t.find_type_def(type_name) {
          match def.kind {
            TypeKind::Struct => {
              if fields.len() == def.fields.len() {
                let it = fields.iter().zip(def.fields.iter());
                let mut arg_types = vec![];
                for ((field_name, _), (expected_name, expected_type)) in it {
                  if let Some(field_name) = field_name {
                    if field_name.name != expected_name.name {
                      self.errors.push(error_raw(field_name.loc, "incorrect field name"));
                    }
                  }
                  arg_types.push(expected_type.clone());
                }
                for(i, t) in arg_types.into_iter().enumerate() {
                  self.update_type(fields[i].1, t);
                }
              }
              else{
                let e = error_raw(self.loc(*result), "incorrect number of field arguments for struct");
                self.errors.push(e);
              }
            }
            TypeKind::Union => {
              if let [(Some(sym), ts)] = fields.as_slice() {
                if let Some((_, t)) = def.fields.iter().find(|(n, _)| n.name == sym.name) {
                  let t = t.clone();
                  self.update_type(*ts, t);
                }
                else {
                  self.errors.push(error_raw(sym.loc, "field does not exist in this union"));
                }
              }
              else {
                let s = format!("incorrect number of field arguments for union '{}'", type_name);
                let e = error_raw(self.loc(*result), s);
                self.errors.push(e);
              }
            }
          }
          self.update_type(*result, Type::def(type_name.clone()));
          return true;
        }
      }
      Constraint::Convert { val, into_type } => {
        if let Some(t) = self.get_type(*val) {
          fn abstract_contains(t : &Type, into_type : &Type) -> bool {
            if let Abstract(abs_t) = &t.content {
              return abs_t.contains_type(into_type);
            }
            false
          }
          if
            abstract_contains(t, into_type) ||
            (t.pointer() && into_type.pointer()) ||
            (t.number() && into_type.number()) ||
            (t.pointer() && into_type.unsigned_int()) ||
            (t.unsigned_int() && into_type.pointer())
          {
            return true;
          }
        }
      }
      Constraint::GlobalDef{ name, type_symbol, initialiser, loc } => {
        if let Some(t) = self.get_type(*type_symbol) {
          let g = GlobalDefinition {
            module_id: self.t.new_module_id(),
            name: name.clone(),
            initialiser: initialiser.clone(),
            type_tag: t.clone(),
            loc: *loc,
          };
          self.t.create_global(g);
          return true;
        }
      }
      Constraint::GlobalReference { node, name, result } => {
        let any = Type::any();
        let t = self.get_type(*result).cloned().unwrap_or(any);
        if let Some(r) = self.find_global(&name, &t) {
          if let Ok(g) = r {
            self.register_def(*node, g.def);
            self.update_type(*result, g.concrete_type);
          }
          return true;
        }
      }
      Constraint::FieldAccess{ container, field, result } => {
        let ct = self.get_type(*container);
        if let Some(mut ct) = ct {
          // Dereference any pointers
          while let Some(inner) = ct.ptr() {
            ct = inner;
          }
          if let Def(name) = &ct.content {
            if let Some(def) = self.t.find_type_def(&name) {
              let f = def.fields.iter().find(|(n, _)| n.name == field.name);
              if let Some((_, t)) = f.cloned() {
                self.update_type(*result, t);
              }
              else {
                let s = format!("type '{}' has no field '{}'", def.name, field.name);
                self.errors.push(error_raw(field.loc, s));
              }
              return true;
            }
          }
        }
      }
      Constraint::Array{ array, element } => {
        if let Some(array_type) = self.get_type(*array) {
          if let Some(element_type) = array_type.array() {
            let et = element_type.clone();
            self.update_type(*element, et);
            return true;
          }
        }
        if let Some(element_type) = self.get_type(*element) {
          let et = element_type.clone();
          self.update_type(*array, Type::array_of(et));
          return true;
        }
      }
    }
    false
  }

  fn try_resolve_abstract_types(&mut self) -> bool {
    let mut count = 0;
    for r in self.resolved.values_mut() {
      if let Abstract(ab) = &r.content {
        if let Some(t) = ab.default_type() {
          *r = t;
          count += 1;
        }
      }
    }
    count > 0
  }

  fn infer(&mut self) {
    println!("To resolve: {}", self.c.symbols.len());
    let mut unused_constraints = vec![];
    for c in self.c.constraints.iter() {
      if !self.process_constraint(c) {
        unused_constraints.push(c);
      }
    }
    let mut total_passes = 1;
    while unused_constraints.len() > 0 {
      total_passes += 1;
      let remaining_before_pass = unused_constraints.len();
      let resolution_step_before_pass = self.resolution_step;
      unused_constraints.retain(|c| !self.process_constraint(c));
      // Continue if some constraints were resolved in the last pass
      if unused_constraints.len() < remaining_before_pass {
        continue;
      }
      // Continue if a type was resolved
      if resolution_step_before_pass != self.resolution_step {
        continue;
      }
      // Continue if some literals can be hardened into specific types
      if self.try_resolve_abstract_types() {
        continue;
      }
      break;
    }
    println!("Passes taken: {}\n", total_passes);
    
    // Generate errors for unresolved constraints
    for c in unused_constraints.iter() {
      self.unresolved_constraint_error(c);
    }

    // Sanity check to make sure that programs with unresolved symbols contain errors
    let unresolved_symbol_count = self.c.symbols.len() - self.resolved.len();
    if unresolved_symbol_count > 0 && self.errors.len() == 0 {
      panic!("Symbol unresolved! Some kind of error should be generated!");
    }

    // Assign types to all of the nodes
    if self.errors.len() == 0 {
      for (n, ts) in self.c.node_symbols.iter() {
        let mut t = self.get_type(*ts).unwrap().clone();
        // Make sure the type isn't abstract
        if let Ok(()) = t.to_concrete() {
          self.cg.node_type.insert(*n, t);
        }
        else {
          let loc = self.loc(*ts);
          let e = error_raw(loc, "unresolved type");
          self.errors.push(e);
        }
      }
    }

    // Print errors (if there are any)
    if self.errors.len() > 0 {
      println!("\nErrors:");
      for e in self.errors.iter() {
        println!("         {}", e);
      }
      println!();
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(u64);

pub enum Function {
  Value(TypeSymbol),
  Name(Symbol),
}

pub enum Constraint {
  Assert(TypeSymbol, Type),
  Equalivalent(TypeSymbol, TypeSymbol),
  Array{ array : TypeSymbol, element : TypeSymbol },
  Convert{ val : TypeSymbol, into_type : Type },
  FieldAccess {
    container : TypeSymbol,
    field : Symbol,
    result : TypeSymbol,
  },
  Constructor {
    type_name : RefStr,
    fields : Vec<(Option<Symbol>, TypeSymbol)>,
    result : TypeSymbol,
  },
  FunctionDef {
    name : RefStr,
    return_type : TypeSymbol,
    args : Vec<(Symbol, TypeSymbol)>,
    body : NodeId,
    loc : TextLocation,
  },
  FunctionCall {
    function : TypeSymbol,
    args : Vec<(Option<SymbolId>, TypeSymbol)>,
    result : TypeSymbol,
  },
  GlobalDef {
    name: RefStr,
    type_symbol: TypeSymbol,
    initialiser: GlobalInit,
    loc: TextLocation,
  },
  GlobalReference {
    node : NodeId,
    name : RefStr,
    result : TypeSymbol,
  },
}

impl  fmt::Display for Constraint {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Constraint::*;
    match self {
      Assert(_, t) => write!(f, "Assert {}", t),
      Equalivalent(_, _) => write!(f, "Equalivalent"),
      Array{ .. } => write!(f, "Array"),
      Convert{ into_type, .. } => write!(f, "Convert into {}", into_type),
      FieldAccess { field, .. } => write!(f, "FieldAccess {}", field.name),
      Constructor { type_name, .. } => write!(f, "Constructor {}", type_name),
      FunctionDef { name, .. } => write!(f, "FunctionDef {}", name),
      FunctionCall { args, .. } =>
        write!(f, "FunctionCall ({} args)", args.len()),
      GlobalDef { name, .. } => write!(f, "GlobalDef {}", name),
      GlobalReference { name, .. } => write!(f, "GlobalRef {}", name),
    }
  }
}

struct Constraints {
  symbols : HashMap<TypeSymbol, TextLocation>,
  node_symbols : HashMap<NodeId, TypeSymbol>,
  variable_symbols : HashMap<SymbolId, TypeSymbol>,
  constraints : Vec<Constraint>,
}

impl Constraints {
  fn new() -> Self {
    Constraints {
      symbols: HashMap::new(),
      node_symbols: HashMap::new(),
      variable_symbols: HashMap::new(),
      constraints: vec![],
    }
  }

  fn loc(&self, ts : TypeSymbol) -> TextLocation {
    *self.symbols.get(&ts).unwrap()
  }
}

fn gather_constraints(
  t : &mut TypeDirectory,
  cg : &mut CodegenInfo,
  cache : &StringCache,
  gen : &mut UIDGenerator,
  c : &mut Constraints,
  errors : &mut Vec<Error>,
  n : &Nodes)
{
  let mut type_def_refs = vec![];
  let mut gc = GatherConstraints::new(t, cg, cache, gen, c, errors, &mut type_def_refs);
  gc.process_node(n, n.root);
  for (name, loc) in gc.type_def_refs.iter() {
    if let Some(def) = gc.t.find_type_def(name) {
      gc.cg.type_def_references.insert(def.name.clone(), def.clone());
    }
    else {
      let e = error_raw(loc, format!("No type definition named '{}' found.", name));
      gc.errors.push(e);
    }
  }
}

struct GatherConstraints<'l, 't> {
  labels : HashMap<LabelId, TypeSymbol>,
  t : &'l mut TypeDirectory<'t>,
  cg : &'l mut CodegenInfo,
  cache : &'l StringCache,
  gen : &'l mut UIDGenerator,
  c : &'l mut Constraints,
  errors : &'l mut Vec<Error>,
  type_def_refs : &'l mut Vec<(RefStr, TextLocation)>,
}

impl <'l, 't> GatherConstraints<'l, 't> {

  fn new(
    t : &'l mut TypeDirectory<'t>,
    cg : &'l mut CodegenInfo,
    cache : &'l StringCache,
    gen : &'l mut UIDGenerator,
    c : &'l mut Constraints,
    errors : &'l mut Vec<Error>,
    type_def_refs : &'l mut Vec<(RefStr, TextLocation)>,
  ) -> Self
  {
    GatherConstraints {
      labels: HashMap::new(),
      cache, t, cg, gen, c,
      errors, type_def_refs,
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

  fn variable_to_type_symbol(&mut self, v : &Symbol) -> TypeSymbol {
    if let Some(ts) = self.c.variable_symbols.get(&v.id) { *ts }
    else {
      let ts = self.type_symbol(v.loc);
      self.c.variable_symbols.insert(v.id, ts);
      ts
    }
  }

  fn constraint(&mut self, c : Constraint) {
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.constraint(Constraint::Equalivalent(a, b));
  }

  fn assert(&mut self, ts : TypeSymbol, t : PType) {
    self.constraint(Constraint::Assert(ts, t.into()));
  }

  fn assert_type(&mut self, ts : TypeSymbol, t : Type) {
    self.constraint(Constraint::Assert(ts, t));
  }

  fn tagged_symbol(&mut self, ts : TypeSymbol, type_expr : &Option<Box<Expr>>) {
    if let Some(type_expr) = type_expr {
      if let Some(t) = self.try_expr_to_type(type_expr) {
        self.assert_type(ts, t);
      }
    }
  }

  fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
    let node = n.node(id);
    let ts = self.node_to_symbol(node);
    match &node.content {
      Content::Literal(val) => {
        use Val::*;
        let t : Type = match val {
          F64(_) | F32(_) => {
            AbstractType::Float.into()
          }
          I64(_) | I32(_) | U64(_) | U32(_) | U16(_) | U8(_) => {
            AbstractType::Integer.into()
          }
          Bool(_) => PType::Bool.into(),
          Void => PType::Void.into(),
          String(_) => {
            self.type_def(node.loc, self.cache.get("string"))
          }
        };
        self.assert_type(ts, t);
      }
      Content::VariableInitialise{ name, type_tag, value, var_scope } => {
        self.assert(ts, PType::Void);
        let var_type_symbol = match var_scope {
          VarScope::Local => self.variable_to_type_symbol(name),
          VarScope::Global(_) => self.type_symbol(name.loc),
        };
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
        if let VarScope::Global(global_type) = *var_scope {
          let initialiser = match global_type {
            GlobalType::CBind => GlobalInit::CBind,
            GlobalType::Normal => GlobalInit::Expression(*value),
          };
          self.constraint(Constraint::GlobalDef{
            name: name.name.clone(),
            type_symbol: var_type_symbol,
            initialiser,
            loc: node.loc,
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
        let then_br = self.process_node(n, *then_branch);
        self.assert(cond, PType::Bool);
        self.assert(then_br, PType::Void);
      }
      Content::IfThenElse{ condition, then_branch, else_branch } => {
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        let else_br = self.process_node(n, *else_branch);
        self.equalivalent(ts, then_br);
        self.assert(cond, PType::Bool);
        self.equalivalent(then_br, else_br);
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
        let t = self.type_def(node.loc, self.cache.get("expr"));
        self.assert_type(ts, Type::ptr_to(t));
      }
      Content::Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_type_symbol(n.symbol(*refers_to));
          self.equalivalent(ts, var_type);
        }
        else {
          self.constraint(Constraint::GlobalReference{ node: id, name: name.clone(), result: ts });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, body } => {
        self.assert(ts, PType::Void);
        let mut ts_args : Vec<(Symbol, TypeSymbol)> = vec![];
        for (arg, type_tag) in args.iter() {
          let arg_type_symbol = self.variable_to_type_symbol(arg);
          self.tagged_symbol(arg_type_symbol, type_tag);
          ts_args.push((arg.clone(), arg_type_symbol));
        }
        let body_ts = {
          // Need new scope stack for new function
          let mut gc =
            GatherConstraints::new(self.t, self.cg, self.cache, self.gen, self.c, self.errors, self.type_def_refs);
          gc.process_node(n, *body)
        };
        self.tagged_symbol(body_ts, return_tag);
        let f = Constraint::FunctionDef {
          name: name.clone(), args: ts_args,
          return_type: body_ts, body: *body, loc: node.loc };
        self.constraint(f);
      }
      Content::CBind { name, type_tag } => {
        self.assert(ts, PType::Void);
        let cbind_ts = self.type_symbol(node.loc);
        if let Some(t) = self.try_expr_to_type(type_tag) {
          self.assert_type(cbind_ts, t.clone());
          let g = GlobalDefinition {
            module_id: self.t.new_module_id(),
            name: name.clone(),
            initialiser: GlobalInit::CBind,
            type_tag: t,
            loc: node.loc,
          };
          self.t.create_global(g);
        }
      }
      Content::TypeDefinition{ name, kind, fields } => {
        self.assert(ts, PType::Void);
        if self.t.find_type_def(name.as_ref()).is_some() {
          let e = error_raw(node.loc, "type with this name already defined");
          self.errors.push(e)
        }
        else {
          // TODO: check for duplicate fields?
          let mut typed_fields = vec![];
          for (field, type_tag) in fields.iter() {
            if let Some(t) = self.try_expr_to_type(type_tag.as_ref().unwrap()) {
              typed_fields.push((field.clone(), t));
            }
          }
          // TODO: Generics?
          let def = TypeDefinition {
            name: name.clone(),
            fields: typed_fields,
            kind: *kind,
            drop_function: None, clone_function: None,
            definition_location: node.loc,
          };
          self.t.create_type_def(def);
        }
      }
      Content::TypeConstructor{ name, field_values } => {
        let mut fields = vec![];
        for (field, value) in field_values.iter() {
          let field_type_symbol = self.process_node(n, *value);
          let field = field.clone();
          fields.push((field, field_type_symbol));
        }
        let tc = Constraint::Constructor{ type_name: name.clone(), fields, result: ts };
        let def_type = self.type_def(node.loc, name.clone());
        self.assert_type(ts, def_type);
        self.constraint(tc);
      }
      Content::FieldAccess{ container, field } => {
        let fa = Constraint::FieldAccess {
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
        self.constraint(Constraint::Array{ array: ts, element: element_ts });
      }
      Content::FunctionCall{ function, args } => {
        let function = self.process_node(n, *function);
        let fc = Constraint::FunctionCall {
          function,
          args: args.iter().map(|id| (None, self.process_node(n, *id))).collect(),
          result: ts,
        };
        self.constraint(fc);
      }
      Content::While{ condition, body } => {
        self.assert(ts, PType::Void);
        let cond = self.process_node(n, *condition);
        let body = self.process_node(n, *body);
        self.assert(cond, PType::Bool);
        self.assert(body, PType::Void);
      }
      Content::Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        if let Some(t) = self.try_expr_to_type(into_type) {
          self.assert_type(ts, t.clone());
          let c = Constraint::Convert { val: v, into_type: t };
          self.constraint(c);
        }
      }
      Content::SizeOf{ type_tag } => {
        if let Some(tid) = self.try_expr_to_type(type_tag) {
          self.cg.sizeof_info.insert(node.id, tid);
        }
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

  fn try_expr_to_type(&mut self, e : &Expr) -> Option<Type> {
    let r = self.expr_to_type(e);
    self.log_error(r)
  }

  fn type_def(&mut self, loc : TextLocation, name : RefStr) -> Type {
    self.type_def_refs.push((name.clone(), loc));
    Type::def(name)
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn expr_to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      let name = self.cache.get(name);
      return Ok(self.type_def(expr.loc, name));
    }
    match expr.try_construct() {
      Some(("fun", es)) => {
        if let Some(args) = es.get(0) {
          let return_type = 
            if let Some(t) = es.get(1) { self.expr_to_type(t)? }
            else { PType::Void.into() };
          let mut sig = SignatureBuilder::new(return_type);
          for e in args.children().iter() {
            let e = if let Some((":", [_name, tag])) = e.try_construct() {tag} else {e};
            sig.append_arg(self.expr_to_type(e)?);
          }
          return Ok(sig.into());
        }
      }
      Some(("call", [name, t])) => {
        match name.unwrap_symbol()? {
          "ptr" => {
            let t = self.expr_to_type(t)?;
            return Ok(Type::ptr_to(t))
          }
          "array" => {
            let t = self.expr_to_type(t)?;
            return Ok(Type::array_of(t))
          }
          _ => (),
        }
      }
      _ => ()
    }
    error(expr, "invalid type expression")
  }
}
