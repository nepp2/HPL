

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

#[macro_use]
mod error;

mod lexer;
mod parser;
mod value;
mod typecheck;
mod bytecode_vm;
mod repl;
mod watcher;

fn main(){
  watcher::watch("bytecode_test.txt");
  //repl::repl();
}