

extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;
extern crate rand;
extern crate rustyline;
extern crate notify;
extern crate itertools;

#[macro_use]
extern crate lazy_static;

mod error;
mod lexer;
mod parser;
mod interpreter;
mod value;
mod intrinsics;
mod sdl_live;
mod watcher;
mod tests;

fn main(){
  //watcher::watch("bytecode_test.txt");
  watcher::watch("new_interpreter.txt");
  //repl::repl();
}