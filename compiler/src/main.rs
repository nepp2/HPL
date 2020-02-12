
//#![allow(dead_code)]

#[cfg(test)]
#[macro_use] extern crate rusty_fork;

mod error;
mod lexer;
mod parser;
mod expr;
mod watcher;
mod structure;
mod types;
mod intrinsics;
mod code_store;
mod inference_constraints;
mod inference_solver;
mod llvm_codegen;
mod llvm_compile;
mod compiler;
mod interpret;
mod repl;
mod graph;
pub mod c_interface;

#[cfg(test)]
mod test;

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::env;

use crate::interpret::interpreter;
use crate::compiler::Val;
use crate::error::Error;

pub fn print_result(r : Result<Val, Error>) -> String {
  match r {
    Ok(v) => format!("{:?}", v),
    Err(e) => format!( "{}", e),
  }
}

fn load(path : &str) -> String {
  let path = PathBuf::from(path);
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  code
}

fn load_and_run(path : &str) {
  let code = load(path);
  let mut i = interpreter();
  let result = i.run_module(&code, path);
  println!("{}", print_result(result));
}

fn main(){
  let args: Vec<String> = env::args().collect();
  let args: Vec<&str> = args.iter().map(|s| s.as_ref()).collect();
  match args[1..] {
    ["watch", f] => {
      let path = format!("code/{}.code", f);
      watcher::watch(path.as_ref())
    }
    ["watch"] => watcher::watch("code/scratchpad.code"),
    ["repl"] => repl::run_repl(),
    ["run", f] => load_and_run(f),
    ["infer"] => {
      let code = load("code/prelude.code");
      compiler::run_program(&code).expect("infer failed");
    }
    _ => load_and_run("code/scratchpad.code"),
  }
}