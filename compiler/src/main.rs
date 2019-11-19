
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
pub mod types;
pub mod inference;
pub mod codegen2;
pub mod compile;
pub mod interpret;
pub mod repl;
pub mod c_interface;

#[cfg(test)]
mod test;

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::env;

use crate::interpret::interpreter;
use crate::structure::Val;
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
      compile::run_program(&code);
    }
    _ => watcher::watch("code/scratchpad.code"),
  }
}