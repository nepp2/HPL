
#[macro_use]
extern crate lazy_static;

mod error;
mod lexer;
mod parser;
mod interpreter;
mod value;
mod library;
mod sdl_simple;
mod watcher;
mod tests;

fn main(){
  //watcher::watch("bytecode_test.txt");
  watcher::watch("new_interpreter.txt");
  //repl::repl();
  //sdl_simple::run();
}