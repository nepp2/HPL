
use crate::{common, error};
use crate::types::{types, constraints, type_graph, type_errors};

use common::*;
use error::error_raw;

use types::{Type, incremental_unify, UnifyResult};
use constraints::{Constraint, Constraints, TypeSlot};
use type_errors::TypeErrors;
use type_graph::TypeGraph;

use std::collections::HashMap;

pub struct Slots<'a> {
  c : &'a Constraints,
  types : HashMap<TypeSlot, Type>,
  any : Type,
}
  
impl <'a> Slots<'a> {

  pub fn new(c : &'a Constraints) -> Self {
    Slots {
      c,
      types : Default::default(),
      any: Type::any(),
    }
  }

  pub fn get(&self, slot : TypeSlot) -> Option<&Type> {
    self.types.get(&slot)
  }

  pub fn get_or_any(&self, slot : TypeSlot) -> &Type {
    self.types.get(&slot).unwrap_or(&self.any)
  }

  pub fn update_type(
    &mut self,
    g : &mut TypeGraph,
    errors : &mut TypeErrors,
    slot : TypeSlot,
    t : &Type
  )
    -> UnifyResult
  {
    let slot_type = if let Some(t) = self.types.get_mut(&slot) {
      t
    }
    else {
      self.types.entry(slot).or_insert(Type::any())
    };
    let r = incremental_unify(t, slot_type);
    if !r.unify_success {
      let s = format!("conflicting types inferred; {} and {}.", t, slot_type);
      errors.push(error_raw(self.c.loc(slot), s));
    }
    if r.mutable_type_changed {
      g.type_updated(slot);
    }
    r
  }

  /// returns true if the input type `t` was mutated
  pub fn update_type_mut(
    &mut self,
    g : &mut TypeGraph,
    errors : &mut TypeErrors,
    slot : TypeSlot,
    t : &mut Type
  )
    -> bool
  {
    let r = self.update_type(g, errors, slot, t);
    if r.immutable_type_changed && r.unify_success {
      let r = incremental_unify(self.types.get(&slot).unwrap(), t);
      if !r.unify_success { panic!("unification is not commutable!") }
      true
    }
    else {
      false
    }
  }

  /// Find the constraints associated with unresolved slots
  pub fn find_all_unresolved_constraints(&mut self, g : &TypeGraph<'a>, edge_set : &mut HashMap<Uid, &'a Constraint>) {
    for (slot, _) in self.types.iter() {
      if !self.get(*slot).map(|t| t.is_concrete()).unwrap_or(false) {
        for c in g.slot_constraints(*slot) {
          edge_set.insert(c.id, c);
        }
      }
    }
  }
}
