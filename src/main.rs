
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate maplit;

mod error;
mod lexer;
mod parser;
mod eval;
mod interpreter;
mod value;
mod library;
mod watcher;
mod tests;

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

fn load_and_run(path : &str) {
  let path = PathBuf::from(path);
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let result = interpreter::interpret(&code);
  println!("{}", watcher::print_result(result));
}

fn main(){
  load_and_run("code/scratchpad.code");
  //watcher::watch("code/scratchpad.code");
}