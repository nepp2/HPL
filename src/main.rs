
extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;
extern crate rand;
extern crate rustyline;

mod font_render;
mod text_edit;
mod lexer;
mod parser;
mod interpreter;
mod visual_edit;
mod repl;

fn main(){
  repl::repl();
  //visual_edit::run_sdl2_app();
  //parser::test_parse();
  //interpreter::test_interpret();
}