
mod types;
mod constraints;
mod solver;
mod slots;

pub use types::*;
pub use solver::{
  typecheck_module,
  typecheck_polymorphic_function_instance
};