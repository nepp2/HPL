
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment it is nondeterministic because it
/// iterates over Rust's secure HashMaps.

use std::fmt;
use itertools::Itertools;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{Expr, UIDGenerator, RefStr, StringCache};
use crate::structure::{
  Node, NodeId, SymbolId, Content, PrimitiveVal, LabelId, TypeKind,
  VarScope, GlobalType, Symbol, Nodes,
};
use crate::types::{
  Type, TypeContent, PType, TypeInfo, TypeDefinition, FunctionInit,
  GlobalDefinition, TypeDirectory, GlobalInit, GlobalId, AbstractType,
  SignatureBuilder, unify_types, incremental_unify, IncrementalUnifyResult,
  GenericId, MonoType, MonoTypeError,
};
use crate::modules::TypedModule;

use std::collections::{HashMap, VecDeque};

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
  dependency_map : ConstraintDependencyMap<'a>,
  next_edge_set : HashMap<u64, &'a Constraint>,
  resolved : HashMap<TypeSymbol, MonoType>,
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
      dependency_map: ConstraintDependencyMap::new(),
      next_edge_set: HashMap::new(),
      resolved: HashMap::new(),
    }
  }

  fn get_type(&self, ts : TypeSymbol) -> Option<&MonoType> {
    self.resolved.get(&ts)
  }

  fn unify_mut(&mut self, ts : TypeSymbol, t : &mut MonoType) -> IncrementalUnifyResult {
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

  fn unify(&mut self, ts : TypeSymbol, mut t : MonoType) -> Option<MonoType> {
    if self.unify_mut(ts, &mut t) == IncrementalUnifyResult::ChangedOld {
      return Some(t);
    }
    None
  }

  fn type_updated(&mut self, ts : TypeSymbol) {
    if let Some(cs) = self.dependency_map.ts_map.get(&ts) {
      for &c in cs.iter() {
        self.next_edge_set.insert(c.id, c);
      }
    }
  }

  fn update_type(&mut self, ts : TypeSymbol, t : MonoType) {
    if let Some(t) = self.unify(ts, t) {
      self.resolved.insert(ts, t);
      self.type_updated(ts);
    }
  }

  fn update_type_mut(&mut self, ts : TypeSymbol, t : &mut MonoType) -> IncrementalUnifyResult {
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
    use ConstraintContent::*;
    let e = match &c.content  {
      Assert(_ts, _t) => return,
      Equalivalent(_a, _b) => return,
      // this error should always be accompanied by other unresolved constraints
      Function{ function:_, args:_, return_type:_ } => return,
      Constructor { type_name, fields:_, result } => {
        error_raw(self.loc(*result),
          format!("constructor for '{}' not resolved", type_name))
      }
      Convert { val:_, into_type:_ } => return,
      GlobalDef { global_id, type_symbol:_ } => {
        let def = self.t.get_global(*global_id);
        error_raw(def.loc,
          format!("global definition '{}' not resolved", def.name))
      }
      GlobalReference { node:_, name, result } => {
        let any = MonoType::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols = self.t.find_global(&name, t, self.gen);
        let s = symbols.iter().map(|g| format!("      {} : {}", g.def.name, g.resolved_type)).join("\n");
        error_raw(self.loc(*result),
          format!("Reference '{}' of type '{}' not resolved\n   Symbols available:\n{}", name, t, s))
      }
      FieldAccess{ container:_, field, result:_ } => {
        error_raw(field.loc,
          format!("field access '{}' not resolved", field.name))
      }
      Array{ array, element:_ } => {
        error_raw(self.loc(*array), "array literal not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, def : GlobalDefinition) {
    self.cg.symbol_references.insert(node, def);
  }

  fn to_monotype(&mut self, t : &Type, loc : TextLocation) -> MonoType {
    to_monotype(t, &self.t, loc, &mut self.errors)
  }

  fn process_constraint(&mut self, c : &Constraint) {
    use ConstraintContent::*;
    match &c.content  {
      Assert(ts, t) => {
        let t = self.to_monotype(t, self.loc(*ts));
        self.update_type(*ts, t);
      }
      Equalivalent(a, b) => {
        if let Some(t) = self.get_type(*a) {
          let t = t.clone();
          self.update_type(*b, t);
        }
        if let Some(t) = self.get_type(*b) {
          let t = t.clone();
          self.update_type(*a, t);
        }
      }
      Function{ function, args, return_type } => {
        if let Some(t) = self.get_type(*function) {
          if let Some(mut sig) = t.sig_builder() {
            for (i, t) in sig.args().iter_mut().enumerate() {
              self.update_type_mut(args[i], t);
            }
            let rt = sig.return_type();
            self.update_type_mut(*return_type, rt);
            self.update_type(*function, sig.into());
          }
        }
        else {
          let any = MonoType::any();
          let return_type = self.get_type(*return_type).cloned().unwrap_or(any.clone());
          let mut sig = SignatureBuilder::new(return_type.into());
          for &arg in args {
            let arg = self.get_type(arg).cloned().unwrap_or(any.clone());
            sig.append_arg(arg);
          }
          self.update_type(*function, sig.into());
        }
      }
      Constructor { type_name, fields, result } => {
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
                  arg_types.push(
                    to_monotype(expected_type, &self.t, expected_name.loc, &mut self.errors));
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
                  let t = self.to_monotype(t, sym.loc);
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
          let monotype = self.to_monotype(&Type::def(type_name.clone()), self.loc(*result));
          self.update_type(*result, monotype);
        }
      }
      Convert { val, into_type } => {
        if let Some(t) = self.get_type(*val) {
          if t.as_type().is_concrete() {
            fn abstract_contains(t : &Type, into_type : &Type) -> bool {
              if let Abstract(abs_t) = &t.content {
                return abs_t.contains_type(into_type);
              }
              false
            }
            let valid =
              abstract_contains(t.as_type(), into_type) ||
              (t.as_type().pointer() && into_type.pointer()) ||
              (t.as_type().number() && into_type.number()) ||
              (t.as_type().pointer() && into_type.unsigned_int()) ||
              (t.as_type().unsigned_int() && into_type.pointer());
            if !valid {
              let s = format!("type conversion from {} into {} not supported", t, into_type);
              self.errors.push(error_raw(self.loc(*val), s));
            }
          }
        }
      }
      GlobalDef{ global_id, type_symbol } => {
        if let Some(t) = self.resolved.get(type_symbol) {
          let def = self.t.get_global(*global_id);
          if !def.polymorphic {
            let monotype = self.to_monotype(&def.type_tag, self.loc(*type_symbol));
            if let Some(unified_type) = unify_types(t, &monotype) {
              def.type_tag = unified_type.into();
              // Trigger any constraints looking for this name or type
              if let Some(cs) = self.dependency_map.global_map.get(&def.name) {
                for &c in cs.iter() {
                  self.next_edge_set.insert(c.id, c);
                }
              }
            }
            else {
              let e = error_raw(def.loc, format!("conflicting types inferred; {} and {}.", t, def.type_tag));
              self.errors.push(e);
            }
          }
        }
      }
      GlobalReference { node, name, result } => {
        let any = MonoType::any();
        let t = self.get_type(*result).cloned().unwrap_or(any);
        match self.t.find_global(&name, &t, self.gen) {
          [g] => {
            let g = g.clone();
            self.register_def(*node, g.def);
            self.update_type(*result, g.resolved_type);
          }
          [] => {
            let s = format!("no global '{}' matches type '{}'", name, t);
            self.errors.push(error_raw(self.loc(*result), s));          
          }
          _ => (), // Multiple matches. Global can't be resolved yet.
        }
      }
      FieldAccess{ container, field, result } => {
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
            }
          }
        }
      }
      Array{ array, element } => {
        if let Some(array_type) = self.get_type(*array) {
          if let Some(element_type) = array_type.array() {
            let et = element_type.clone();
            self.update_type(*element, et);
          }
        }
        if let Some(element_type) = self.get_type(*element) {
          let et = element_type.clone();
          self.update_type(*array, Type::array_of(et));
        }
      }
    }
  }

  /// Tries to harden a type symbol into a concrete type
  fn try_harden_type_symbol(&mut self, ts : TypeSymbol) {
    if let Abstract(ab) = &self.resolved.get(&ts).unwrap().content {
      if let Some(default) = ab.default_type() {
        self.update_type(ts, default);
      }
    }
  }

  fn infer(&mut self) {
    println!("To resolve: {}", self.c.symbols.len());
    self.dependency_map.clear();
    for c in self.c.constraints.iter() {
      self.dependency_map.populate_dependency_map(c);
      self.next_edge_set.insert(c.id, c);
    }
    let mut literals = VecDeque::with_capacity(self.c.literals.len());
    for lit in self.c.literals.iter() {
      literals.push_back(*self.c.node_symbols.get(lit).unwrap());
    }
    let mut total_constraints_processed = 0;
    let mut active_edge_set = HashMap::new();
    while self.next_edge_set.len() > 0 || literals.len() > 0 {
      std::mem::swap(&mut self.next_edge_set, &mut active_edge_set);
      for (_, c) in active_edge_set.drain() {
        total_constraints_processed += 1;
        self.process_constraint(c);
      }
      // If nothing was resolved, try to harden a literal (in lexical order)
      if self.next_edge_set.is_empty() && literals.len() > 0 {
        self.try_harden_type_symbol(literals.pop_back().unwrap());
      }
    }
    println!("Unique constraints: {}\n", self.c.constraints.len());
    println!("Constraints processed (including duplicates): {}\n", total_constraints_processed);

    // Assign types to all of the nodes
    if self.errors.is_empty() {
      for (n, ts) in self.c.node_symbols.iter() {
        let t = self.get_type(*ts).unwrap().clone();
        // Make sure the type isn't abstract
        if t.is_concrete() {
          self.cg.node_type.insert(*n, t);
        }
      }
    }

    // Generate errors if program has unresolved symbols contain errors
    let mut unresolved = 0;
    if self.errors.is_empty() {
      for (ts, _) in self.c.symbols.iter() {
        if !self.resolved.get(ts).map(|t| t.is_concrete()).unwrap_or(false) {
          unresolved += 1;
          for c in self.dependency_map.ts_map.get(ts).unwrap() {
            active_edge_set.insert(c.id, c);
          }
        }
      }
      // Generate errors for unresolved constraints
      for (_, c) in active_edge_set.drain() {
        self.unresolved_constraint_error(c);
      }
    }

    if self.errors.is_empty() && unresolved > 0 {
      panic!("Unresolved types found, but no errors generated!");
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

/// Clones a type while recursively checking that its type definitions
/// actually exist. Instantiates any type parameters that it may have.
/// Spits out errors if a type doesn't match the definition.
fn to_monotype(t : &Type, td : &TypeDirectory, loc : TextLocation, errors : &mut Vec<Error>) -> MonoType {
  match t.to_monotype(td) {
    Ok(t) => t,
    Err(e) => {
      let e = match e {
        MonoTypeError::DefDoesNotExist(name) =>
          error_raw(loc, format!("type {} does not exist", name)),
        MonoTypeError::WrongNumberOfTypeParameters =>
          error_raw(loc, "incorrect number of type parameters provided"),
      };
      errors.push(e);
      MonoType::any()
    },
  }
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(u64);

pub enum Function {
  Value(TypeSymbol),
  Name(Symbol),
}

pub struct Constraint {
  id : u64,
  content : ConstraintContent,
}

pub enum ConstraintContent {
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
  Function {
    function : TypeSymbol,
    args : Vec<TypeSymbol>,
    return_type : TypeSymbol,
  },
  GlobalDef {
    global_id: GlobalId,
    type_symbol: TypeSymbol,
  },
  GlobalReference {
    node : NodeId,
    name : RefStr,
    result : TypeSymbol,
  },
}

struct ConstraintDependencyMap<'a> {
  global_map : HashMap<RefStr, Vec<&'a Constraint>>,
  ts_map : HashMap<TypeSymbol, Vec<&'a Constraint>>,
}

impl <'a> ConstraintDependencyMap<'a> {

  fn new() -> Self {
    ConstraintDependencyMap { global_map: HashMap::new(), ts_map: HashMap::new() }
  }

  fn clear(&mut self) {
    self.ts_map.clear();
    self.global_map.clear();
  }

  fn ts(&mut self, ts : &TypeSymbol, c : &'a Constraint) {
    self.ts_map.entry(*ts).or_insert(vec![]).push(c);
  }

  fn global(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.global_map.get_mut(name) { cs.push(c); }
    else { self.global_map.insert(name.clone(), vec![c]); }
  }

  fn populate_dependency_map(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content {
      Assert(ts, _) => self.ts(ts, c),
      Equalivalent(a, b) => {
        self.ts(a, c);
        self.ts(b, c);
      }
      Array{ array, element } => {
        self.ts(array, c);
        self.ts(element, c);
      },
      Convert{ val, into_type:_ } => self.ts(val, c),
      FieldAccess { container, field:_, result } => {
        self.ts(container, c);
        self.ts(result, c);
      },
      Constructor { type_name:_, fields, result } => {
        for (_, ts) in fields { self.ts(ts, c) }
        self.ts(result, c);
      },
      Function { function, args, return_type } => {
        self.ts(function, c);
        for ts in args { self.ts(ts, c) }
        self.ts(return_type, c);
      },
      GlobalDef { global_id:_, type_symbol } => self.ts(type_symbol, c),
      GlobalReference { node:_, name, result } => {
        self.global(name, c);
        self.ts(result, c);
      }
    }
  }
}

impl  fmt::Display for Constraint {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use ConstraintContent::*;
    match &self.content {
      Assert(_, t) => write!(f, "Assert {}", t),
      Equalivalent(_, _) => write!(f, "Equalivalent"),
      Array{ .. } => write!(f, "Array"),
      Convert{ into_type, .. } => write!(f, "Convert into {}", into_type),
      FieldAccess { field, .. } => write!(f, "FieldAccess {}", field.name),
      Constructor { type_name, .. } => write!(f, "Constructor {}", type_name),
      Function { args, .. } =>
        write!(f, "FunctionCall ({} args)", args.len()),
      GlobalDef { .. } => write!(f, "GlobalDef"),
      GlobalReference { name, .. } => write!(f, "GlobalRef {}", name),
    }
  }
}

struct Constraints {
  symbols : HashMap<TypeSymbol, TextLocation>,
  node_symbols : HashMap<NodeId, TypeSymbol>,
  literals : Vec<NodeId>,
  variable_symbols : HashMap<SymbolId, TypeSymbol>,
  constraints : Vec<Constraint>,
}

impl Constraints {
  fn new() -> Self {
    Constraints {
      symbols: HashMap::new(),
      node_symbols: HashMap::new(),
      literals: vec![],
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
  polytype_ids : Vec<(RefStr, GenericId)>,
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
      polytype_ids : vec![],
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

  fn constraint(&mut self, c : ConstraintContent) {
    let c = Constraint { id: self.gen.next(), content: c };
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.constraint(ConstraintContent::Equalivalent(a, b));
  }

  fn assert(&mut self, ts : TypeSymbol, t : PType) {
    self.constraint(ConstraintContent::Assert(ts, t.into()));
  }

  fn assert_type(&mut self, ts : TypeSymbol, t : Type) {
    self.constraint(ConstraintContent::Assert(ts, t));
  }

  fn tagged_symbol(&mut self, ts : TypeSymbol, type_expr : &Option<Box<Expr>>) {
    if let Some(type_expr) = type_expr {
      if let Some(t) = self.try_expr_to_type(type_expr) {
        self.assert_type(ts, t);
      }
    }
  }

  fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
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
            self.type_def(self.cache.get("string"), node.loc)
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
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
        if let VarScope::Global(global_type) = *var_scope {
          let initialiser = match global_type {
            GlobalType::CBind => GlobalInit::CBind,
            GlobalType::Normal => GlobalInit::Expression(*value),
          };
          let global_id = self.gen.next().into();
          self.t.create_global(GlobalDefinition {
            id: global_id,
            module_id: self.t.new_module_id(),
            name: name.name.clone(),
            type_tag: Type::any(),
            initialiser,
            polymorphic: false,
            loc: node.loc,
          });
          self.constraint(GlobalDef{
            global_id,
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
        let t = self.type_def(self.cache.get("expr"), node.loc);
        self.assert_type(ts, Type::ptr_to(t));
      }
      Content::Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_type_symbol(n.symbol(*refers_to));
          self.equalivalent(ts, var_type);
        }
        else {
          self.constraint(GlobalReference{ node: id, name: name.clone(), result: ts });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, polytypes, body } => {
        self.assert(ts, PType::Void);
        self.with_polytypes(polytypes.as_slice(), |gc, polytypes| {
          let global_id = gc.gen.next().into();
          let body_ts = {
            // Need new scope stack for new function
            let mut gc = GatherConstraints::new(
              gc.t, gc.cg, gc.cache, gc.gen,
              gc.c, gc.errors, gc.type_def_refs
            );
            gc.process_node(n, *body)
          };
          gc.tagged_symbol(body_ts, return_tag);
          let mut arg_types : Vec<TypeSymbol> = vec![];
          let mut arg_names = vec!();
          for (arg, type_tag) in args.iter() {
            arg_names.push(arg.clone());
            let arg_type_symbol = gc.variable_to_type_symbol(arg);
            gc.tagged_symbol(arg_type_symbol, type_tag);
            arg_types.push(arg_type_symbol);
          }
          let global_ts = gc.type_symbol(node.loc);
          gc.constraint(Function {
            function: global_ts,
            args: arg_types,
            return_type: body_ts,
          });
          gc.constraint(GlobalDef {
            global_id,
            type_symbol: global_ts,
          });
          gc.t.create_global({
            let name_for_codegen =
              gc.cache.get(format!("{}.{}", name, gc.gen.next()).as_str());
            let f = FunctionInit {
              body: *body,
              name_for_codegen,
              args: arg_names,
            };
            GlobalDefinition {
              id: global_id,
              module_id: gc.t.new_module_id(),
              name: name.clone(),
              type_tag: Type::any(),
              initialiser: GlobalInit::Function(f),
              polymorphic: polytypes.len() > 0,
              loc: node.loc,
            }
          });
        });
      }
      Content::CBind { name, type_tag } => {
        self.assert(ts, PType::Void);
        let cbind_ts = self.type_symbol(node.loc);
        if let Some(t) = self.try_expr_to_type(type_tag) {
          self.assert_type(cbind_ts, t.clone());
          let g = GlobalDefinition {
            id: self.gen.next().into(),
            module_id: self.t.new_module_id(),
            name: name.clone(),
            initialiser: GlobalInit::CBind,
            type_tag: t,
            polymorphic: false,
            loc: node.loc,
          };
          self.t.create_global(g);
        }
      }
      Content::TypeDefinition{ name, kind, fields, polytypes } => {
        self.assert(ts, PType::Void);
        if self.t.find_type_def(name.as_ref()).is_some() {
          let e = error_raw(node.loc, "type with this name already defined");
          self.errors.push(e)
        }
        else {
          self.with_polytypes(polytypes.as_slice(), |gc, polytypes| {
            // TODO: check for duplicate fields?
            let mut typed_fields = vec![];
            for (field, type_tag) in fields.iter() {
              if let Some(t) = gc.try_expr_to_type(type_tag.as_ref().unwrap()) {
                typed_fields.push((field.clone(), t));
              }
            }
            let def = TypeDefinition {
              name: name.clone(),
              fields: typed_fields,
              kind: *kind,
              polytypes,
              drop_function: None, clone_function: None,
              definition_location: node.loc,
            };
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
        let tc = Constructor{ type_name: name.clone(), fields, result: ts };
        let def_type = self.type_def(name.clone(), node.loc);
        self.assert_type(ts, def_type);
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
        self.constraint(Array{ array: ts, element: element_ts });
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
        let body = self.process_node(n, *body);
        self.assert(cond, PType::Bool);
        self.assert(body, PType::Void);
      }
      Content::Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        if let Some(t) = self.try_expr_to_type(into_type) {
          self.assert_type(ts, t.clone());
          let c = Convert { val: v, into_type: t };
          self.constraint(c);
        }
      }
      Content::SizeOf{ type_tag } => {
        if let Some(t) = self.try_expr_to_type(type_tag) {
          self.cg.sizeof_info.insert(node.id, t);
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

  fn type_def(&mut self, name : RefStr, loc : TextLocation) -> Type {
    self.type_def_refs.push((name.clone(), loc));
    Type::def(name)
  }

  fn with_polytypes<F>(&mut self, polytypes : &[RefStr], f : F)
    where F : Fn(&mut GatherConstraints, Vec<GenericId>)
  {
    let mut polytype_ids = vec![];
    for pt in polytypes.iter() {
      let id = self.gen.next().into();
      polytype_ids.push(id);
      self.polytype_ids.push((pt.clone(), id));
    }
    f(self, polytype_ids);
    self.polytype_ids.drain((self.polytype_ids.len()-polytypes.len())..);
  }

  fn symbol_to_type(&mut self, loc : TextLocation, name : &str) -> Type {
      // Check for polytypes
      for (polytype_name, generic_id) in self.polytype_ids.iter() {
        if polytype_name.as_ref() == name {
          return (*generic_id).into();
        }
      }
      // Assume type definition
      let name = self.cache.get(name);
      return self.type_def(name, loc);
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn expr_to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      // Check for primitive types
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      return Ok(self.symbol_to_type(expr.loc, name));
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
      Some(("call", exprs)) => {
        let name = &exprs[0];
        match name.unwrap_symbol()? {
          "ptr" => {
            if let [t] = &exprs[1..] {
              let t = self.expr_to_type(t)?;
              return Ok(Type::ptr_to(t))
            }
          }
          "array" => {
            if let [t] = &exprs[1..] {
              let t = self.expr_to_type(t)?;
              return Ok(Type::array_of(t))
            }
          }
          name => {
            let mut t = self.symbol_to_type(exprs[0].loc, name);
            for e in &exprs[1..] {
              t.children.push(self.expr_to_type(e)?);
            }
            return Ok(t);
          }
        }
      }
      _ => ()
    }
    error(expr, format!("invalid type expression {}", expr))
  }
}
