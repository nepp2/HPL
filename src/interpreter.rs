
use crate::value::*;
use crate::error::Error;
use crate::library::load_library;
use crate::eval::{
  Environment, eval_string, Module,
  BlockScope, add_module};

use std::mem;
use std::fs::File;
use std::io::Read;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::collections::HashMap;

// TODO: this should store the expression id counter for the parser. At the moment, ids will be reused!

pub struct Interpreter {
  pub symbols : SymbolTable,
  pub loaded_modules : Vec<Module>,
  pub top_level_scope : Option<BlockScope>,
  pub top_level_module : ModuleId,

  /// used to halt the interpreter from another thread
  pub interrupt_flag : Arc<AtomicBool>,
}

impl Interpreter {

  pub fn new(mut interrupt_flag : Arc<AtomicBool>) -> Interpreter {
    let mut symbols = SymbolTable::new();
    let mut loaded_modules = vec!();

    // load prelude
    let prelude = add_module(&mut loaded_modules, Module::new("prelude".into()));
    {
      let mut f = File::open("code/prelude.code").expect("file not found");
      let mut code = String::new();
      f.read_to_string(&mut code).unwrap();
      let mut env = Environment::new(
        &mut symbols,
        &mut loaded_modules,
        prelude, &mut interrupt_flag,
        BlockScope {
          variables: hashmap![],
          modules: vec![prelude],
        });
      load_library(&mut env);
      eval_string(&code, &mut env).unwrap();
    }

    // load top level module
    let top_level_module =
      add_module(&mut loaded_modules, Module::new("top_level".into()));

    Interpreter {
      symbols,
      loaded_modules,
      top_level_scope: Some(BlockScope {
        variables: HashMap::new(),
        modules: vec![prelude, top_level_module],
      }),
      top_level_module,
      interrupt_flag,
    }
  }

  pub fn simple() -> Interpreter {
    Interpreter::new(Arc::new(AtomicBool::new(false)))
  }

  pub fn interpret(&mut self, code : &str) -> Result<Value, Error> {
    let scope = mem::replace(&mut self.top_level_scope, None).unwrap();
    let mut env = Environment::new(
      &mut self.symbols,
      &mut self.loaded_modules,
      self.top_level_module,
      &mut self.interrupt_flag,
      scope);
    let r = eval_string(code, &mut env);
    assert!(env.scope.len()==1);
    self.top_level_scope = env.scope.pop();
    r
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

