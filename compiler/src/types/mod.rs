
mod types;
mod constraints;
mod solver;
mod slots;
mod type_graph;
mod type_errors;
mod references;

pub use types::*;
pub use solver::{
  typecheck_module,
  typecheck_polymorphic_function_instance
};