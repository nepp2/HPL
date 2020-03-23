
use crate::common::*;
use crate::types::{types, constraints};

use types::SymbolDefinition;
use constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSlot,
};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub struct TypeGraph<'a> {
  symbol_map : HashMap<RefStr, Vec<&'a Constraint>>,
  typedef_map : HashMap<RefStr, HashMap<Uid, &'a Constraint>>,
  slot_map : HashMap<TypeSlot, Vec<&'a Constraint>>,
  dirty_slots : HashSet<TypeSlot>,
  dirty_symbols : HashSet<RefStr>,
}

impl <'a> TypeGraph<'a> {

  pub fn new(c : &'a Constraints) -> Self {
    let mut g : TypeGraph = Default::default();
    for c in c.constraints.iter() {
      g.populate_dependency_map(c);
    }
    g
  }

  pub fn slot_constraints(&self, slot : TypeSlot) -> &[&'a Constraint] {
    if let Some(cs) = self.slot_map.get(&slot) {
      cs.as_slice()
    }
    else { &[] }
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

  /// Find the constraints associated with recently updated slots
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

  pub fn type_updated(&mut self, slot : TypeSlot) {
    self.dirty_slots.insert(slot);
  }

  fn slot(&mut self, slot : &TypeSlot, c : &'a Constraint) {
    self.slot_map.entry(*slot).or_insert(vec![]).push(c);
  }

  fn symbol(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.symbol_map.get_mut(name) { cs.push(c); }
    else { self.symbol_map.insert(name.clone(), vec![c]); }
  }

  fn populate_dependency_map(&mut self, c : &'a Constraint) {
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