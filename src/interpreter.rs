
use crate::parser;
use crate::parser::NO_TYPE;
use crate::lexer;
use crate::value::*;
use crate::error::Error;
use crate::library::load_library;
use crate::eval::{Environment, eval, Module, BlockScope};

use std::fs::File;
use std::io::Read;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::collections::HashMap;

// TODO: this should store the expression id counter for the parser. At the moment, ids will be reused!

pub struct Interpreter {
  pub symbol_cache : SymbolCache,
  pub loaded_modules : HashMap<RefStr, Module>,
  pub top_level_module : Module,
  pub top_level_scope : BlockScope,

  /// used to halt the interpreter from another thread
  pub interrupt_flag : Arc<AtomicBool>,
}

impl Interpreter {
  pub fn new(interrupt_flag : Arc<AtomicBool>) -> Interpreter {
    let top_level_module : Module = Default::default();
    let loaded_modules = hashmap!("top_level".into() => top_level_module);
    let i = Interpreter {
      symbol_cache: SymbolCache::new(),
      loaded_modules,
      top_level_module,
      top_level_scope: BlockScope {
        variables: HashMap::new(),
        modules: vec![top_level_module],
      },
      interrupt_flag,
    };
    load_library(&mut i);
    // TODO: this is slow and dumb
    let mut f = File::open("code/prelude.code").expect("file not found");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    i.interpret(&code).unwrap();
    i
  }

  pub fn load_module(&mut self, module_name: &str) {
    let file_name = format!("code/{}.code", module_name);
    let mut f = File::open(file_name).expect("file not found");
    let module : Module = Default::default();
    let initial_scope = BlockScope {
      variables: hashmap![],
      modules: vec![self.loaded_modules.get("prelude").unwrap().clone()],
    };
    let mut env = Environment::new(&mut self.symbol_cache, &mut self.loaded_modules, &mut module, &mut self.interrupt_flag, initial_scope);
  }

  pub fn simple() -> Interpreter {
    Interpreter::new(Arc::new(AtomicBool::new(false)))
  }

  pub fn parse(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex_with_cache(code, &mut self.symbol_cache)
      .map_err(|mut es| es.remove(0))?;
    parser::parse_with_cache(tokens, &mut self.symbol_cache)
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

