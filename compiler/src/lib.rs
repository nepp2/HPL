
#![allow(dead_code)]

#[cfg(test)]
#[macro_use] extern crate rusty_fork;

#[macro_use] extern crate lazy_static;
// #[macro_use] extern crate maplit;

pub mod error;
pub mod lexer;
pub mod parser;
pub mod value;
pub mod watcher;
pub mod typecheck;
pub mod codegen;
pub mod jit;
pub mod repl;
pub mod c_interface;

#[cfg(test)]
mod test;
