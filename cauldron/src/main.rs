
#![allow(dead_code)]

#[cfg(test)]
#[macro_use] extern crate rusty_fork;

// #[macro_use] extern crate lazy_static;
// #[macro_use] extern crate maplit;

/*
mod error;
mod lexer;
mod parser;
mod value;
mod watcher;
mod typecheck;
mod codegen;
mod jit;
mod repl;
mod c_interface;
*/

#[cfg(test)]
mod test;

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::env;

use compiler as cc;

use cc::jit::Interpreter;
use cc::typecheck::Val;
use cc::error::Error;
use cc::typecheck;
use cc::watcher;
use cc::repl;

pub fn print_result(r : Result<Val, Error>) -> String {
  match r {
    Ok(v) => format!("{:?}", v),
    Err(e) => format!( "{}", e),
  }
}

fn load_and_run(path : &str) {
  let path = PathBuf::from(path);
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let mut i = Interpreter::new();
  let result = i.run(&code);
  println!("{}", print_result(result));
}

fn main(){
  let args: Vec<String> = env::args().collect();
  let args: Vec<&str> = args.iter().map(|s| s.as_ref()).collect();
  println!("ScriptString size: {}", std::mem::size_of::<typecheck::ScriptString>());
  match args[1..] {
    ["watch", f] => {
      let path = format!("code/{}.code", f);
      watcher::watch(path.as_ref())
    }
    ["watch"] => watcher::watch("code/scratchpad.code"),
    ["run", f] => load_and_run(f),
    _ => repl::run_repl(),
  }
}