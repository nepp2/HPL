
use crate::{common, error, structure, code_store, compiler};
use crate::types::{types, constraints};

use common::*;
use error::{Error, error, error_raw, TextLocation, ErrorContent};
use structure::{
  NodeId, TypeKind, Nodes,
};

use types::{
  Type, PType, TypeContent, TypeInfo, SymbolId, incremental_unify,
  TypeMapping, UnifyResult, AbstractType, SymbolInit, SymbolDefinition,
};
use constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSlot, Assertion,
  Errors, TypeDirectory,
};

use code_store::CodeStore;
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;

use std::collections::{HashMap, HashSet, VecDeque};

use TypeContent::*;

#[derive(Default)]
pub struct Slots<'a> {
  symbol_map : HashMap<RefStr, Vec<&'a Constraint>>,
  typedef_map : HashMap<RefStr, HashMap<Uid, &'a Constraint>>,
  slot_map : HashMap<TypeSlot, Vec<&'a Constraint>>,
  dirty_slots : HashSet<TypeSlot>,
  dirty_symbols : HashSet<RefStr>,
  types : HashMap<TypeSlot, Type>,

  concrete_errors : Vec<Error>,
  failed_constraint_ids : HashSet<Uid>,
}
  
impl <'a> Slots<'a> {

  pub fn new() -> Self { Default::default() }

  pub fn get(&self, slot : TypeSlot) -> Option<&Type> {
    self.types.get(&slot)
  }

  pub fn get_or_any(&self, slot : TypeSlot) -> &Type {
    static ANY : Type = Type::any();
    self.types.get(&slot).unwrap_or(&ANY)
  }

  fn type_updated(&mut self, slot : TypeSlot) {
    self.dirty_slots.insert(slot);
  }

  pub fn update_type(&mut self, slot : TypeSlot, t : &Type) -> UnifyResult {
    let slot_type = if let Some(t) = self.types.get_mut(&slot) {
      t
    }
    else {
      self.types.entry(slot).or_insert(Type::any())
    };
    let r = incremental_unify(t, slot_type);
    if !r.unify_success {
      let s = format!("conflicting types inferred; {} and {}.", t, slot_type);
      let e = error_raw(self.loc(slot), s);
      self.errors.push(e);
    }
    if r.mutable_type_changed {
      self.type_updated(slot);
    }
    r
  }

  /// returns true if the input type `t` was mutated
  pub fn update_type_mut(&mut self, slot : TypeSlot, t : &mut Type) -> bool {
    let r = self.update_type(slot, t);
    if r.immutable_type_changed && r.unify_success {
      let r = incremental_unify(self.types.get(&slot).unwrap(), t);
      if !r.unify_success { panic!("unification is not commutable!") }
      true
    }
    else {
      false
    }
  }

  fn slot(&mut self, slot : &TypeSlot, c : &'a Constraint) {
    self.slot_map.entry(*slot).or_insert(vec![]).push(c);
  }

  fn symbol(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.symbol_map.get_mut(name) { cs.push(c); }
    else { self.symbol_map.insert(name.clone(), vec![c]); }
  }

  pub fn find_boundary_constraints(&mut self, edge_set : &mut HashMap<Uid, &'a Constraint>) {
    for name in self.dirty_symbols.drain() {
      if let Some(cs) = self.symbol_map.get(&name) {
        for &c in cs.iter() { edge_set.insert(c.id, c); }
      }
    }
    for slot in self.dirty_slots.drain() {
      if let Some(cs) = self.slot_map.get(&slot) {
        for &c in cs.iter() { edge_set.insert(c.id, c); }
      }
    }
  }

  pub fn symbol_updated(&mut self, def : &SymbolDefinition) {
    self.dirty_symbols.insert(def.name.clone());
  }

  pub fn register_typedef(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.typedef_map.get_mut(name) {
      cs.insert(c.id, c);
    }
    else {
      let mut cs = HashMap::new();
      cs.insert(c.id, c);
      self.typedef_map.insert(name.clone(), cs);
    }
  }

  pub fn populate_dependency_map(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content {
      Equalivalent(a, b) => {
        self.slot(a, c);
        self.slot(b, c);
      }
      Branch{ output, cases } => {
        self.slot(output, c);
        for slot in cases {
          self.slot(slot, c);
        }
      }
      TypeParameter{ parent, parameter } => {
        self.slot(parent, c);
        self.slot(parameter, c);
      },
      Convert{ val, into_type_slot } => {
        self.slot(val, c);
        self.slot(into_type_slot, c);
      }
      FieldAccess { container, field:_, result } => {
        self.slot(container, c);
        self.slot(result, c);
      },
      Constructor { def_slot, fields } => {
        self.slot(def_slot, c);
        for (_, slot) in fields { self.slot(slot, c) }
      },
      Function { function, args, return_type } => {
        self.slot(function, c);
        for slot in args { self.slot(slot, c) }
        self.slot(return_type, c);
      },
      SymbolDef { symbol_id:_, slot } => self.slot(slot, c),
      SymbolReference { node:_, name, result } => {
        self.symbol(name, c);
        self.slot(result, c);
      }
      SizeOf { node:_, slot } => {
        self.slot(slot, c);
      }
    }
  }
}
  