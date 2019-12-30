
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment the error reporting for incorrect
/// programs is nondeterministic due to iteration over Rust's secure, randomised
/// HashMaps. This should be fixed at some point so that the most useful error
/// messages are reliably shown to users.

use itertools::Itertools;

use crate::error::{Error, error_raw, TextLocation};
use crate::expr::{UIDGenerator, RefStr, StringCache};
use crate::structure::{
  NodeId, TypeKind, Nodes,
};
use crate::types::{
  Type, TypeContent, TypeInfo, TypeDirectory, GlobalId,
  SignatureBuilder, incremental_unify_monomorphic,
  incremental_unify_polymorphic, UnifyResult,
  MonoType, ModuleId,
};
use crate::inference_constraints::{
  gather_constraints, Constraint, ConstraintContent,
  Constraints, TypeSymbol,
};
use crate::modules::TypedModule;
use crate::codegen::CodegenInfo;

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

struct TypeUnify<'a> {
  errors : &'a mut Vec<Error>,
  resolved : HashMap<TypeSymbol, MonoType>,
}

struct Inference<'a> {
  nodes : &'a Nodes,
  t : &'a mut TypeDirectory<'a>,
  cg : &'a mut CodegenInfo,
  c : &'a Constraints,
  cache : &'a StringCache,
  gen : &'a mut UIDGenerator,
  errors : &'a mut Vec<Error>,
  symbol_references : HashMap<NodeId, (ModuleId, GlobalId)>,
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
      symbol_references: HashMap::new(),
      dependency_map: ConstraintDependencyMap::new(),
      next_edge_set: HashMap::new(),
      resolved: HashMap::new(),
    }
  }

  fn get_type(&self, ts : TypeSymbol) -> Option<&MonoType> {
    self.resolved.get(&ts)
  }

  fn type_updated(&mut self, ts : TypeSymbol) {
    if let Some(cs) = self.dependency_map.ts_map.get(&ts) {
      for &c in cs.iter() {
        self.next_edge_set.insert(c.id, c);
      }
    }
  }

  fn unify_mut_internal(&mut self, ts : TypeSymbol, new_type : &mut MonoType) -> UnifyResult {
    if let Some(prev_t) = self.resolved.get(&ts) {
      let r = incremental_unify_monomorphic(prev_t, new_type);
      if !r.fully_unified {
        let e = error_raw(self.loc(ts), format!("conflicting types inferred; {} and {}.", new_type, prev_t));
        self.errors.push(e);
      }
      r
    }
    else {
      UnifyResult { fully_unified: true, old_type_changed: true, new_type_changed: false }
    }
  }

  fn update_type(&mut self, ts : TypeSymbol, mut t : MonoType) {
    if self.unify_mut_internal(ts, &mut t).old_type_changed {
      self.resolved.insert(ts, t);
      self.type_updated(ts);
    }
  }

  fn update_type_mut(&mut self, ts : TypeSymbol, t : &mut MonoType) -> UnifyResult {
    let r = self.unify_mut_internal(ts, t);
    if r.old_type_changed {
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
      Constructor { def_ts:_ , fields:_ } => return,
      Convert { val:_, into_type_ts:_ } => return,
      TypeDefField { .. } => return,
      GlobalDef { global_id, type_symbol:_ } => {
        let def = self.t.get_global(*global_id);
        error_raw(def.loc,
          format!("Global definition '{}' not resolved. Inferred type {}.", def.name, def.type_tag))
      }
      GlobalReference { node:_, name, result } => {
        let any = MonoType::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols = self.t.find_global(&name, t);
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
      SizeOf { node:_, ts } => {
        error_raw(self.loc(*ts), "sizeof type not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, module_id : ModuleId, global_id : GlobalId) {
    self.symbol_references.insert(node, (module_id, global_id));
  }

  fn process_constraint(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content  {
      Assert(ts, t) => {
        match self.t.resolve_abstract_defs(t) {
          Ok(t) =>
            self.update_type(*ts, t),
          Err(def_name) => {
            let e = error_raw(self.loc(*ts),
              format!("type definition '{}' was not found", def_name));
            self.errors.push(e);
          }
        }
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
      Constructor { def_ts, fields } => {
        if let Some(t) = self.resolved.get(def_ts) {
          if let Def(name, module_id) = &t.as_type().content {
            self.dependency_map.register_typedef(name, c);
            let def = self.t.get_type_def(name, *module_id);
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
                    arg_types.push(expected_type.to_monotype());
                  }
                  for(i, t) in arg_types.into_iter().enumerate() {
                    self.update_type(fields[i].1, t);
                  }
                }
                else{
                  let e = error_raw(self.loc(*def_ts), "incorrect number of field arguments for struct");
                  self.errors.push(e);
                }
              }
              TypeKind::Union => {
                if let [(Some(sym), ts)] = fields.as_slice() {
                  if let Some((_, t)) = def.fields.iter().find(|(n, _)| n.name == sym.name) {
                    let t = t.to_monotype();
                    self.update_type(*ts, t);
                  }
                  else {
                    self.errors.push(error_raw(sym.loc, "field does not exist in this union"));
                  }
                }
                else {
                  let s = format!("incorrect number of field arguments for union '{}'", def.name);
                  let e = error_raw(self.loc(*def_ts), s);
                  self.errors.push(e);
                }
              }
            }
          }
        }
      }
      Convert { val, into_type_ts } => {
        let t = self.get_type(*val);
        let into = self.get_type(*into_type_ts);
        if let [Some(t), Some(into)] = &[t, into] {
          if t.as_type().is_concrete() && into.as_type().is_concrete() {
            let (t, into) = (t.as_type(), into.as_type());
            fn abstract_contains(t : &Type, into_type : &Type) -> bool {
              if let Abstract(abs_t) = &t.content {
                return abs_t.contains_type(into_type);
              }
              false
            }
            let valid =
              abstract_contains(t, into) ||
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
      TypeDefField { container, field_index, field_type } => {
        if let Some(ctype) = self.resolved.get(container) {
          if let Def(name, _) = &ctype.as_type().content {
            let def = self.t.get_type_def_mut(name);
            if let Some(inferred_type) = self.resolved.get(field_type) {
              let t = &mut def.fields[*field_index].1;
              let r = incremental_unify_polymorphic(inferred_type, t);
              if r.new_type_changed {
                // Trigger any constraints looking for this def
                if let Some(cs) = self.dependency_map.typedef_map.get(name) {
                  for &c in cs.values() {
                    self.next_edge_set.insert(c.id, c);
                  }
                }
              }
            }
          }
        }
      }
      GlobalDef{ global_id, type_symbol } => {
        if let Some(t) = self.resolved.get(type_symbol) {
          let def = self.t.get_global(*global_id);
          if !def.polymorphic {
            let r = incremental_unify_polymorphic(t, &mut def.type_tag);
            if r.fully_unified {
              if r.new_type_changed {
                // Trigger any constraints looking for this name
                if let Some(cs) = self.dependency_map.global_map.get(&def.name) {
                  for &c in cs.iter() {
                    self.next_edge_set.insert(c.id, c);
                  }
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
        match self.t.find_global(&name, &t) {
          [g] => {
            let resolved_type = g.resolved_type.clone();
            let (mid, gid) = (g.def.module_id, g.def.id);
            self.register_def(*node, mid, gid);
            self.update_type(*result, resolved_type);
          }
          [] => {
            let s = format!("no global '{}' matches type '{}'", name, t);
            self.errors.push(error_raw(self.loc(*result), s));          
          }
          _ => (), // Multiple matches. Global can't be resolved yet.
        }
      }
      FieldAccess{ container, field, result } => {
        let container_type = self.resolved.get(container);
        if let Some(ct) = container_type {
          let mut t = ct.as_type();
          // Dereference any pointers
          while let Some(inner) = t.ptr() {
            t = inner;
          }
          if let Def(name, module_id) = &t.content {
            self.dependency_map.register_typedef(name, c);
            let def = self.t.get_type_def(&name, *module_id);
            let f = def.fields.iter().find(|(n, _)| n.name == field.name);
            if let Some((_, t)) = f {
              let mt = t.to_monotype();
              self.update_type(*result, mt);
            }
            else {
              let s = format!("type '{}' has no field '{}'", def.name, field.name);
              self.errors.push(error_raw(field.loc, s));
            }
          }
        }
      }
      Array{ array, element } => {
        if let Some(element_type) = self.get_type(*element) {
          let et = element_type.clone();
          self.update_type(*array, et.array_of());
        }
        else if let Some(array_type) = self.get_type(*array) {
          if let Some(element_type) = array_type.as_type().array() {
            let et = element_type.to_monotype();
            self.update_type(*element, et);
          }
        }
      }
      SizeOf { node, ts } => {
        if let Some(t) = self.get_type(*ts) {
          if t.as_type().is_concrete() {
            let t = t.clone().into();
            self.cg.sizeof_info.insert(*node, t);
          }
        }
      }
    }
  }

  /// Tries to harden a type symbol into a concrete type
  fn try_harden_type_symbol(&mut self, ts : TypeSymbol) {
    if let Some(default) = self.resolved.get(&ts).unwrap().try_harden_literal() {
      self.update_type(ts, default);
    }
  }

  fn infer(&mut self) {
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

    // Generate errors if program has unresolved symbols
    let mut unresolved = 0;
    if self.errors.is_empty() {
      for (ts, _) in self.c.symbols.iter() {
        if !self.resolved.get(ts).map(|t| t.as_type().is_concrete()).unwrap_or(false) {
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

    // Assign types to all of the nodes
    if self.errors.is_empty() {
      for (n, ts) in self.c.node_symbols.iter() {
        let t = self.get_type(*ts).unwrap().as_type().clone();
        // Make sure the type isn't abstract
        if t.is_concrete() {
          self.cg.node_type.insert(*n, t);
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
    // Assign global definitions
    else {
      let aaa = (); // TODO: this is slow and stupid and wastes memory
      for (nid, (mid, gid)) in self.symbol_references.drain() {
        let def = self.t.find_module(mid).globals.get(&gid).unwrap().clone();
        if def.polymorphic {
          let t = self.cg.node_type.get(&nid).unwrap();
          println!("polymorphic def '{}', {} - {}", def.name, def.type_tag, t);
        }
        self.cg.symbol_references.insert(nid, def);
      }
    }
  }
}

struct ConstraintDependencyMap<'a> {
  global_map : HashMap<RefStr, Vec<&'a Constraint>>,
  typedef_map : HashMap<RefStr, HashMap<u64, &'a Constraint>>,
  ts_map : HashMap<TypeSymbol, Vec<&'a Constraint>>,
}

impl <'a> ConstraintDependencyMap<'a> {

  fn new() -> Self {
    ConstraintDependencyMap {
      global_map: HashMap::new(),
      typedef_map: HashMap::new(),
      ts_map: HashMap::new() }
  }

  fn ts(&mut self, ts : &TypeSymbol, c : &'a Constraint) {
    self.ts_map.entry(*ts).or_insert(vec![]).push(c);
  }

  fn global(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.global_map.get_mut(name) { cs.push(c); }
    else { self.global_map.insert(name.clone(), vec![c]); }
  }

  fn register_typedef(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.typedef_map.get_mut(name) {
      cs.insert(c.id, c);
    }
    else {
      let mut cs = HashMap::new();
      cs.insert(c.id, c);
      self.typedef_map.insert(name.clone(), cs);
    }
  }

  fn populate_dependency_map(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content {
      Assert(_ts, _t) => {
        // asserts only need to run once, so there's no point
        // in registering them to be triggered again.
      }
      Equalivalent(a, b) => {
        self.ts(a, c);
        self.ts(b, c);
      }
      Array{ array, element } => {
        self.ts(array, c);
        self.ts(element, c);
      },
      Convert{ val, into_type_ts } => {
        self.ts(val, c);
        self.ts(into_type_ts, c);
      }
      FieldAccess { container, field:_, result } => {
        self.ts(container, c);
        self.ts(result, c);
      },
      Constructor { def_ts, fields } => {
        self.ts(def_ts, c);
        for (_, ts) in fields { self.ts(ts, c) }
      },
      Function { function, args, return_type } => {
        self.ts(function, c);
        for ts in args { self.ts(ts, c) }
        self.ts(return_type, c);
      },
      TypeDefField { container, field_index:_, field_type } => {
        self.ts(container, c);
        self.ts(field_type, c);
      }
      GlobalDef { global_id:_, type_symbol } => self.ts(type_symbol, c),
      GlobalReference { node:_, name, result } => {
        self.global(name, c);
        self.ts(result, c);
      }
      SizeOf { node:_, ts } => {
        self.ts(ts, c);
      }
    }
  }
}
