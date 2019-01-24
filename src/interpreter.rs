
use crate::parser;
use crate::parser::NO_TYPE;
use crate::lexer;
use crate::value::*;
use crate::error::Error;
use crate::library::load_library;
use crate::eval::{Environment, eval};

use std::fs::File;
use std::io::Read;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

// TODO: this should store the expression id counter for the parser. At the moment, ids will be reused!
pub struct Interpreter {
  pub env : Environment
}

impl Interpreter {
  pub fn simple() -> Interpreter {
    Interpreter::new(Arc::new(AtomicBool::new(false)))
  }

  pub fn new(interrupt_flag : Arc<AtomicBool>) -> Interpreter {
    let mut i = Interpreter { env: Environment::new(interrupt_flag) };
    load_library(&mut i);
    // TODO: this is slow and dumb
    let mut f = File::open("code/prelude.code").expect("file not found");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    i.interpret(&code).unwrap();
    i
  }

  pub fn parse(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex_with_cache(code, &mut self.env.symbol_cache)
      .map_err(|mut es| es.remove(0))?;
    parser::parse_with_cache(tokens, &mut self.env.symbol_cache)
  }

  pub fn interpret_ast(&mut self, ast : &Expr) -> Result<Value, Error> {
    // TODO debug thingy: println!("{}", ast);
    eval(ast, &mut self.env)
  }

  pub fn interpret(&mut self, code : &str) -> Result<Value, Error> {
    let ast = self.parse(code)?;
    self.interpret_ast(&ast)
  }
}

pub fn interpret_with_interrupt(code : &str, interrupt_flag : Arc<AtomicBool>) -> Result<Value, Error> {
  let mut i = Interpreter::new(interrupt_flag);
  i.interpret(code)
}

pub fn interpret(code : &str) -> Result<Value, Error> {
  interpret_with_interrupt(code, Arc::new(AtomicBool::new(false)))
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let result = interpret(code);
  println!("{:?}", result);
}

