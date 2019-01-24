
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

fn main(){
  watcher::watch("code/scratchpad.code");
}