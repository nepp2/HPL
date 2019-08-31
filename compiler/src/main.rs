
#![allow(dead_code)]

#[cfg(test)]
#[macro_use] extern crate rusty_fork;

#[macro_use] extern crate lazy_static;
// #[macro_use] extern crate maplit;

pub mod error;
pub mod lexer;
pub mod parser2;
pub mod parser;
pub mod expr;
pub mod watcher;
pub mod typecheck;
pub mod codegen;
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

fn load_and_run(path : &str) {
  let path = PathBuf::from(path);
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let c = expr::StringCache::new();
  let tokens = lexer::lex(&code, &c).unwrap();
  let r = parser2::parse(tokens, &c);
  match r {
    Ok(e) => println!("{}", e),
    Err(e) => println!("{}", e),
  }
}

use libloading as lib;
use llvm_sys::execution_engine::LLVMExecutionEngineRef;
use libc::c_char;

type Sig = unsafe extern fn(LLVMExecutionEngineRef, *const c_char) -> u64;

fn call_dynamic() {
  let lib = lib::Library::new("target/debug/deps/compiler.dll").unwrap();
  unsafe {
    let f = lib.get::<Sig>(b"LLVMGetFunctionAddress");
    println!("Loaded: {:?}", f);
    //Ok(func())
  }
}

fn main(){
  // call_dynamic();
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
    ["parser2", f] => load_and_run(f),
    _ => watcher::watch("code/scratchpad.code"),
  }
}