
#![allow(dead_code)]

#[cfg(test)]
#[macro_use] extern crate rusty_fork;

// #[macro_use] extern crate lazy_static;
// #[macro_use] extern crate maplit;

pub mod error;
pub mod lexer;
pub mod parser;
pub mod expr;
pub mod watcher;
pub mod structure;
pub mod typecheck;
pub mod inference;
pub mod codegen;
//pub mod codegen2;
pub mod jit;
pub mod repl;
pub mod c_interface;

#[cfg(test)]
mod test;

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::env;

use crate::jit::interpreter;
use crate::typecheck::Val;
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
  let result = i.run(&code);
  println!("{}", print_result(result));
}

fn test_inference(path : &str) {
  use expr::{ StringCache, UIDGenerator};
  let code = load(path);
  let cache = StringCache::new();
  let mut gen = UIDGenerator::new();
  let mut c_symbols = c_interface::CSymbols::new();
  c_symbols.populate();
  let tokens =
    lexer::lex(&code, &cache)
    .map_err(|mut es| es.remove(0)).unwrap();
  let expr = parser::parse(tokens, &cache).expect("parse errors");
  let nodes = structure::to_nodes(&mut gen, &c_symbols.local_symbol_table, &cache, &expr).expect("node errors");
  let m = inference::base_module(&mut gen, &cache);
  inference::infer_types(&m, &mut gen, &cache, &code, &nodes).expect("type errors");
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
    ["infer"] => test_inference("code/infer.code"),
    _ => watcher::watch("code/scratchpad.code"),
  }
}