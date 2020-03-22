
mod types;
mod constraints;
mod solver;

pub use types::*;
pub use solver::{
  typecheck_module,
  typecheck_polymorphic_function_instance
};