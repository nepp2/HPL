
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment the error reporting for incorrect
/// programs is nondeterministic due to iteration over Rust's secure, randomised
/// HashMaps. This should be fixed at some point so that the most useful error
/// messages are reliably shown to users.

use itertools::Itertools;

use crate::{error, expr, structure, types, inference_constraints, code_store};

use error::{Error, error, error_raw, TextLocation, ErrorContent};
use expr::{UIDGenerator, Uid, RefStr, StringCache};
use structure::{
  NodeId, Nodes
};
use types::{
  Type, TypeContent, TypeInfo, TypeDirectory, SymbolId,
  SignatureBuilder, incremental_unify, TypeMapping,
  UnifyResult, UnitId, AbstractType, SymbolInfo, SymbolDefinition,
};
use inference_constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSymbol,
};
use code_store::CodeStore;

use std::collections::{HashMap, VecDeque};

use TypeContent::*;

pub fn infer_types(
  unit_id : UnitId,
  code_store : &CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<(TypeInfo, TypeMapping), Error>
{
  let mut mapping = TypeMapping::new();
  let mut errors = vec![];
  let mut new_types = TypeInfo::new(unit_id);
  let imports : Vec<_> =
    code_store.types.values().collect();
  let mut type_directory =
    TypeDirectory::new(unit_id, imports.as_slice(), &mut new_types);
  let nodes = code_store.nodes(unit_id);
  let c =
    inference_constraints::get_module_constraints(
      &nodes, &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, code_store, &mut type_directory,
    &mut mapping, &c, cache, gen, &mut errors);
  i.infer();
  if errors.len() > 0 {    
    let c = ErrorContent::InnerErrors("type errors".into(), errors);
    error(nodes.root().loc, c)
  }
  else {
    Ok((new_types, mapping))
  }
}

pub fn typecheck_polymorphic_function_instance(
  instance_unit : UnitId,
  poly_function : &SymbolDefinition,
  instance_type : &Type,
  code_store : &CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<(TypeInfo, TypeMapping, SymbolId), Error>
{
  let mut mapping = TypeMapping::new();
  let mut errors = vec![];
  let mut new_types = TypeInfo::new(instance_unit);
  let aaa = (); // TODO: type directory should just take the code store, and be a lot simpler
  let imports : Vec<_> = code_store.types.values().collect();
  let mut type_directory =
    TypeDirectory::new(instance_unit, imports.as_slice(), &mut new_types);
  let nodes = code_store.nodes(poly_function.unit_id);
  let source_node =
    *code_store.type_mapping(poly_function.unit_id)
    .symbol_def_nodes.get(&poly_function.id).unwrap();
  let instanced_type_vars = poly_function.instanced_type_vars(instance_type);
  let (c, symbol_id) =
    inference_constraints::get_polymorphic_function_instance_constraints(
      &nodes, source_node, instance_type.clone(), instanced_type_vars.as_slice(),
      &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, code_store, &mut type_directory,
    &mut mapping, &c, cache, gen, &mut errors);
  i.infer();
  if errors.len() > 0 {
    let c = ErrorContent::InnerErrors("type errors".into(), errors);
    error(nodes.root().loc, c)
  }
  else {
    Ok((new_types, mapping, symbol_id))
  }
}

fn recursive_mut_deref<A>(t : &mut Type, mut f : impl FnMut(&mut Type) -> A) -> A {
  if let Some(inner) = t.ptr_mut() {
    recursive_mut_deref(inner, f)
  }
  else {
    f(t)
  }
}

struct Inference<'a> {
  nodes : &'a Nodes,
  code_store : &'a CodeStore,
  t : &'a mut TypeDirectory<'a>,
  mapping : &'a mut TypeMapping,
  c : &'a Constraints,
  cache : &'a StringCache,
  gen : &'a mut UIDGenerator,
  errors : &'a mut Vec<Error>,
  dependency_map : ConstraintDependencyMap<'a>,
  next_edge_set : HashMap<Uid, &'a Constraint>,
  resolved : HashMap<TypeSymbol, Type>,
}

impl <'a> Inference<'a> {

  fn new(
    nodes : &'a Nodes,
    code_store : &'a CodeStore,
    t : &'a mut TypeDirectory<'a>,
    mapping : &'a mut TypeMapping,
    c : &'a Constraints,
    cache : &'a StringCache,
    gen : &'a mut UIDGenerator,
    errors : &'a mut Vec<Error>)
      -> Self
  {
    Inference {
      nodes, code_store, t, mapping, c, cache, gen, errors,
      dependency_map: ConstraintDependencyMap::new(),
      next_edge_set: HashMap::new(),
      resolved: HashMap::new(),
    }
  }

  fn get_type(&self, ts : TypeSymbol) -> Option<&Type> {
    self.resolved.get(&ts)
  }

  fn type_updated(&mut self, ts : TypeSymbol) {
    if let Some(cs) = self.dependency_map.ts_map.get(&ts) {
      for &c in cs.iter() {
        self.next_edge_set.insert(c.id, c);
      }
    }
  }

  fn update_type(&mut self, ts : TypeSymbol, t : &Type) -> UnifyResult {
    let ts_type = if let Some(t) = self.resolved.get_mut(&ts) {
      t
    }
    else {
      self.resolved.entry(ts).or_insert(Type::any())
    };
    let r = incremental_unify(t, ts_type);
    if !r.unify_success {
      let s = format!("conflicting types inferred; {} and {}.", t, ts_type);
      let e = error_raw(self.loc(ts), s);
      self.errors.push(e);
    }
    if r.mutable_type_changed {
      self.type_updated(ts);
    }
    r
  }

  /// returns true if the input type `t` was mutated
  fn update_type_mut(&mut self, ts : TypeSymbol, t : &mut Type) -> bool {
    let r = self.update_type(ts, t);
    if r.immutable_type_changed && r.unify_success {
      let r = incremental_unify(self.resolved.get(&ts).unwrap(), t);
      if !r.unify_success { panic!("unification is not commutable!") }
      true
    }
    else {
      false
    }
  }

  fn loc(&self, ts : TypeSymbol) -> TextLocation {
    *self.c.symbols.get(&ts).unwrap()
  }

  fn unresolved_constraint_error(&mut self, c : &Constraint) {
    use ConstraintContent::*;
    let e = match &c.content  {
      Assert(_, _) => return,
      Equalivalent(_a, _b) => return,
      // this error should always be accompanied by other unresolved constraints
      Function{ function:_, args:_, return_type:_ } => return,
      StructDef { typename , def_ts } => {
        let any = Type::any();
        let t = self.resolved.get(def_ts).unwrap_or(&any);
        error_raw(typename.loc,
          format!("Struct def '{}' not resolved. Inferred type {}.", typename.name, t))
      },
      StructReference { typename , def_ts } => {
        let any = Type::any();
        let t = self.resolved.get(def_ts).unwrap_or(&any);
        error_raw(typename.loc,
          format!("Struct reference '{}' not resolved. Inferred type {}.", typename.name, t))
      },
      Struct { def_ts:_ , fields:_ } => return,
      Convert { val:_, into_type_ts:_ } => return,
      SymbolDef { symbol_id, type_symbol:_ } => {
        let def = self.t.get_symbol_mut(*symbol_id);
        let node_id = *self.mapping.symbol_def_nodes.get(symbol_id).unwrap();
        let loc = self.nodes.node(node_id).loc;
        error_raw(loc,
          format!("Symbol definition '{}' not resolved. Inferred type {}.", def.name, def.type_tag))
      }
      SymbolReference { node:_, name, result } => {
        let any = Type::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols = self.t.find_symbol(&name, t);
        let cs = &self.code_store;
        let s = symbols.iter().map(|g| {
          let def = cs.symbol_def(g.symbol_id);
          format!("      {} : {}", def.name, g.resolved_type)
        }).join("\n");
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
      SizeOf { node:_, ts } => {
        error_raw(self.loc(*ts), "sizeof type not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, symbol_id : SymbolId) {
    self.mapping.symbol_references.insert(node, symbol_id);
  }

  fn resolve_defs(&mut self, loc : TextLocation, t : &mut Type, c : &'a Constraint)
    -> Result<(), Error> 
  {
    match &t.content {
      Def(name, unit_id) => {
        let def = self.t.get_type_def(name, *unit_id);
        self.dependency_map.new_struct_ref(name, c);
        *t = def.type_tag.clone();
      }
      Abstract(AbstractType::Def(name)) => {
        if let Some(def) = self.t.find_type_def(name) {
          self.dependency_map.new_struct_ref(name, c);
          *t = def.type_tag.clone();
        }
        else {
          return error(loc, format!("type definition '{}' was not found", name));
        }
      }
      _ => (),
    };
    for t in t.children.iter_mut() {
      self.resolve_defs(loc, t, c)?;
    }
    Ok(())
  }

  fn process_constraint(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content  {
      Assert(ts, t) => {
        let loc = self.loc(*ts);
        let mut t = t.clone();
        match self.resolve_defs(loc, &mut t, c) {
          Ok(()) => {
            self.update_type(*ts, &t);
          }
          Err(e) => {
            self.errors.push(e);
          }
        }
      }
      Equalivalent(a, b) => {
        if let Some(t) = self.get_type(*a) {
          let t = t.clone();
          self.update_type(*b, &t);
        }
        if let Some(t) = self.get_type(*b) {
          let t = t.clone();
          self.update_type(*a, &t);
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
            self.update_type(*function, &sig.into());
          }
        }
        else {
          let any = Type::any();
          let return_type = self.get_type(*return_type).cloned().unwrap_or(any.clone());
          let mut sig = SignatureBuilder::new(return_type.into());
          for &arg in args {
            let arg = self.get_type(arg).cloned().unwrap_or(any.clone());
            sig.append_arg(arg);
          }
          self.update_type(*function, &sig.into());
        }
      }
      StructDef { typename, def_ts } => {
        // Use global def to update the type symbol
        let mut t = self.t.get_type_def_mut(&typename.name).type_tag.clone();
        let def_type_changed = self.update_type_mut(*def_ts, &mut t);
        // Use the type symbol to update the global def
        if def_type_changed {
          let def = self.t.get_type_def_mut(&typename.name);
          def.type_tag = t;
          // Trigger any constraints looking for this name
          if let Some(cs) = self.dependency_map.struct_refs.get(&def.name) {
            for &c in cs.iter() {
              self.next_edge_set.insert(c.id, c);
            }
          }
        }
      }
      StructReference { typename, def_ts } => {
        if let Some(def) = self.t.find_type_def(&typename.name) {
          let t = def.type_tag.clone();
          self.update_type(*def_ts, &t);
        }
      }
      Struct { def_ts, fields } => {
        if let Some(t) = self.resolved.get(def_ts) {
          if let Def(_, _) = &t.content {
            let mut children = vec![];
            for ts in fields {
              children.push(self.resolved.get(ts).cloned().unwrap_or(Type::any()));
            }
            let mut t = Type::new(t.content.clone(), children);
            if self.update_type_mut(*def_ts, &mut t) {
              for (c, ts) in t.children.iter().zip(fields) {
                self.update_type(*ts, c);
              }
            }
          }
        }
      }
      Convert { val, into_type_ts } => {
        let t = self.get_type(*val);
        let into = self.get_type(*into_type_ts);
        if let [Some(t), Some(into)] = &[t, into] {
          if t.is_concrete() && into.is_concrete() {
            fn abstract_contains(t : &Type, into_type : &Type) -> bool {
              if let Abstract(abs_t) = &t.content {
                return abs_t.contains_type(into_type);
              }
              false
            }
            fn union_contains(union : &Type, t : &Type) -> bool {
              if let Union = &union.content {
                if let Abstract(_) = &t.content {
                  return true;
                }
                for ut in union.children() {
                  if t == ut {
                    return true;
                  }
                }
              }
              return false;
            }
            let valid =
              abstract_contains(t, into) ||
              union_contains(t, into) ||
              union_contains(into, t) ||
              (t.pointer() && into.pointer()) ||
              (t.number() && into.number()) ||
              (t.pointer() && into.unsigned_int()) ||
              (t.unsigned_int() && into.pointer());
            if !valid {
              let s = format!("type conversion from {} into {} not supported", t, into);
              self.errors.push(error_raw(self.loc(*val), s));
            }
          }
        }
      }
      SymbolDef{ symbol_id, type_symbol } => {
        // Use global def to update the type symbol
        let mut t = self.t.get_symbol_mut(*symbol_id).type_tag.clone();
        let def_type_changed = self.update_type_mut(*type_symbol, &mut t);
        // Use the type symbol to update the global def
        if def_type_changed {
          let def = self.t.get_symbol_mut(*symbol_id);
          def.type_tag = t;
          // Trigger any constraints looking for this name
          if let Some(cs) = self.dependency_map.symbol_refs.get(&def.name) {
            for &c in cs.iter() {
              self.next_edge_set.insert(c.id, c);
            }
          }
        }
      }
      SymbolReference { node, name, result } => {
        let any = Type::any();
        let t = self.get_type(*result).cloned().unwrap_or(any);
        match self.t.find_symbol(&name, &t) {
          [rs] => {
            let resolved_type = rs.resolved_type.clone();
            let id = rs.symbol_id;
            self.register_def(*node, id);
            self.update_type(*result, &resolved_type);
          }
          [] => {
            // Global will never be resolved, but if an error is generated
            // here it may be recorded several times.
          }
          _ => (), // Multiple matches. Global can't be resolved yet.
        }
      }
      FieldAccess{ container, field, result } => {
        let container_type = self.resolved.get(container);
        if let Some(def_t) = container_type {
          let mut def_t = def_t.clone();
          // Dereference any pointers
          let changed_def = recursive_mut_deref(&mut def_t, |t| {
            if let Def(name, unit_id) = &t.content {
              let def = self.t.get_type_def(name, *unit_id);
              let i = def.fields.iter().position(|s| &s.name == &field.name);
              if let Some(i) = i {
                if self.update_type_mut(*result, &mut t.children[i]) {
                  return true;
                }
              }
              else {
                let s = format!("type '{}' has no field '{}'", name, field.name);
                self.errors.push(error_raw(field.loc, s));
              }
            }
            false
          });
          if changed_def {
            self.update_type(*container, &def_t);
          }
        }
      }
      Array{ array, element } => {
        if let Some(element_type) = self.get_type(*element) {
          let et = element_type.clone();
          self.update_type(*array, &et.array_of());
        }
        else if let Some(array_type) = self.get_type(*array) {
          if let Some(element_type) = array_type.array() {
            let et = element_type.clone();
            self.update_type(*element, &et);
          }
        }
      }
      SizeOf { node, ts } => {
        if let Some(t) = self.get_type(*ts) {
          if t.is_concrete() {
            let t = t.clone().into();
            self.mapping.sizeof_info.insert(*node, t);
          }
        }
      }
    }
  }

  /// Tries to harden a type symbol into a concrete type
  fn try_harden_type_symbol(&mut self, ts : TypeSymbol) {
    if let Some(default) = self.resolved.get(&ts).unwrap().try_harden_literal() {
      self.update_type(ts, &default);
    }
  }

  fn infer(mut self) {
    println!("To resolve: {}", self.c.symbols.len());
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
    while (self.next_edge_set.len() > 0 || literals.len() > 0) && self.errors.len() == 0 {
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

    // Generate errors if program has unresolved symbols
    let mut unresolved = 0;
    active_edge_set.clear();
    if self.errors.is_empty() {
      for (ts, _) in self.c.symbols.iter() {
        if !self.resolved.get(ts).map(|t| t.is_concrete()).unwrap_or(false) {
          unresolved += 1;
          if let Some(cs) = self.dependency_map.ts_map.get(ts) {
            for c in cs { active_edge_set.insert(c.id, c); }
          }
          // Generate errors for unresolved constraints
          let error_count = self.errors.len();
          for (_, c) in active_edge_set.drain() {
            self.unresolved_constraint_error(c);
          }
          if error_count == self.errors.len() {
            self.errors.push(error_raw(self.loc(*ts), "unresolved type"));
          }
        }
      }
    }

    if self.errors.is_empty() && unresolved > 0 {
      panic!("Unresolved types found, but no errors generated!");
    }

    // Assign types to all of the nodes
    if self.errors.is_empty() {
      for (n, ts) in self.c.node_symbols.iter() {
        let t = self.get_type(*ts).unwrap().clone();
        // Make sure the type isn't abstract
        if t.is_concrete() {
          self.mapping.node_type.insert(*n, t);
        }
        else {
          panic!("abstract type but no error");
        }
      }
    }

    // Find polymorphic definitions
    if self.errors.is_empty() {
      for (node_id, symbol_id) in self.mapping.symbol_references.iter() {
        let def = self.t.find_type_info(symbol_id.uid).symbols.get(symbol_id).unwrap().clone();
        if def.is_polymorphic() {
          if let SymbolInfo::Function(_) = def.info {
            let t = self.mapping.node_type.get(node_id).unwrap();
            self.mapping.polymorphic_references.insert((*symbol_id, t.clone()));
          }
        }
      }
    }
  }
}

struct ConstraintDependencyMap<'a> {
  symbol_refs : HashMap<RefStr, Vec<&'a Constraint>>,
  struct_refs : HashMap<RefStr, Vec<&'a Constraint>>,
  ts_map : HashMap<TypeSymbol, Vec<&'a Constraint>>,
}

impl <'a> ConstraintDependencyMap<'a> {

  fn new() -> Self {
    ConstraintDependencyMap {
      symbol_refs: HashMap::new(),
      struct_refs: HashMap::new(),
      ts_map: HashMap::new() }
  }

  fn ts(&mut self, ts : &TypeSymbol, c : &'a Constraint) {
    self.ts_map.entry(*ts).or_insert(vec![]).push(c);
  }

  fn symbol_ref(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.symbol_refs.get_mut(name) { cs.push(c); }
    else { self.symbol_refs.insert(name.clone(), vec![c]); }
  }

  // Checks for duplicates on insertion
  fn new_struct_ref(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.struct_refs.get_mut(name) {
      if cs.iter().find(|con| con.id == c.id).is_none() {
        cs.push(c);
      }
    }
    else { self.struct_refs.insert(name.clone(), vec![c]); }
  }

  fn struct_ref(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.struct_refs.get_mut(name) { cs.push(c); }
    else { self.struct_refs.insert(name.clone(), vec![c]); }
  }

  fn find_struct_refs(&mut self, t : &Type, c : &'a Constraint) {
    if let Def(name, _) = &t.content {
      self.struct_ref(name, c);
    }
    for t in t.children.iter() {
      self.find_struct_refs(t, c);
    }
  }

  fn populate_dependency_map(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content {
      Assert(_, t) => {
        self.find_struct_refs(t, c);
      }
      Equalivalent(a, b) => {
        self.ts(a, c);
        self.ts(b, c);
      }
      Array{ array, element } => {
        self.ts(array, c);
        self.ts(element, c);
      }
      Convert{ val, into_type_ts } => {
        self.ts(val, c);
        self.ts(into_type_ts, c);
      }
      FieldAccess { container, field:_, result } => {
        self.ts(container, c);
        self.ts(result, c);
      }
      Struct { def_ts, fields } => {
        self.ts(def_ts, c);
        for ts in fields { self.ts(ts, c) }
      }
      Function { function, args, return_type } => {
        self.ts(function, c);
        for ts in args { self.ts(ts, c) }
        self.ts(return_type, c);
      }
      SymbolDef { symbol_id:_, type_symbol } => self.ts(type_symbol, c),
      StructDef { typename:_, def_ts } => self.ts(def_ts, c),
      SymbolReference { node:_, name, result } => {
        self.symbol_ref(name, c);
        self.ts(result, c);
      }
      StructReference { typename, def_ts } => {
        self.struct_ref(&typename.name, c);
        self.ts(def_ts, c);
      }
      SizeOf { node:_, ts } => {
        self.ts(ts, c);
      }
    }
  }
}
