

extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;
extern crate rand;
extern crate rustyline;
extern crate notify;

#[macro_use]
extern crate lazy_static;

mod error;
mod lexer;
mod parser;
mod value;
mod utils;
mod typecheck;
mod interpreter;
mod bytecode_vm;
mod repl;
mod watcher;

fn main(){
  watcher::watch("bytecode_test.txt");
  //repl::repl();
}