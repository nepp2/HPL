

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

mod lexer;
mod parser;
mod interpreter;
mod bytecode_vm;
mod repl;
mod watcher;

fn main(){
  watcher::watch("code.txt");
  //repl::repl();
}