
use crate::{common, error};
use common::*;
use error::Error;
use std::collections::HashSet;

#[derive(Default)]
pub struct TypeErrors {
  pub concrete_errors : Vec<Error>,

  /// to avoid duplicate errors
  pub failed_constraint_ids : HashSet<Uid>,
}

impl TypeErrors {
  pub fn new() -> Self { Default::default() }

  pub fn push(&mut self, e : Error) {
    self.concrete_errors.push(e);
  }

  pub fn is_empty(&self) -> bool {
    self.concrete_errors.is_empty()
  }
}