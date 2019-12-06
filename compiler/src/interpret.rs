
use crate::error::Error;
use crate::compile::Val;
use crate::types::ModuleId;
use crate::compile::Compiler;
use crate::expr::Expr;

use std::fs::File;
use std::io::Read;

// TODO: fix this gross hack
#[cfg(not(test))]
static PRELUDE_PATH : &'static str = "code/prelude.code";
#[cfg(test)]
static PRELUDE_PATH : &'static str = "../code/prelude.code";

pub struct Interpreter {
  pub c : Box<Compiler>,
  module_container : Vec<ModuleId>,
}

pub fn interpreter() -> Interpreter {
  let c = Compiler::new();
  let mut i = Interpreter { c, module_container: vec![] };
  
  // load prelude
  if let Err(e) = i.load_prelude() {
    println!("error loading prelude, {}", e);
  }
  
  return i;
}

impl Interpreter {

  pub fn run_expression(&mut self, expr : &Expr) -> Result<(ModuleId, Val), Error> {
    self.module_container.clear();
    self.module_container.extend(self.c.compiled_modules.keys().cloned());
    self.c.load_module(self.module_container.as_slice(), expr)
  }

  fn run(&mut self, code : &str) -> Result<(ModuleId, Val), Error> {
    let expr = self.c.parse(code)?;
    self.run_expression(&expr)
  }

  pub fn eval(&mut self, code : &str) -> Result<Val, Error> {
    Ok(self.run(code)?.1)
  }

  fn load_module(&mut self, code : &str) -> Result<ModuleId, Error> {
    let (id, _val) = self.run(code)?;
    Ok(id)
  }

  fn load_prelude(&mut self) -> Result<(), Error> {
    let mut f = File::open(PRELUDE_PATH).expect("failed to load prelude");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    self.load_module(&code)?;
    Ok(())
  }

  // Calls a function that accepts an OUT pointer as an argument, in C style.
  pub fn run_with_pointer_return<A>(
    &mut self, code : &str, function_name: &str)
      -> Result<A, Error>
  {
    let mut arg : A = unsafe { std::mem::zeroed() };
    self.run_named_function_with_arg(code, function_name, &mut arg)?;
    Ok(arg)
  }

  pub fn run_named_function_with_arg<T, A>(
    &mut self, code : &str, function_name: &str, arg: A)
      -> Result<T, Error>
  {
    let module_id = self.load_module(code)?;
    let m = self.c.compiled_modules.get(&module_id).unwrap();
    let function_name = m.t.globals.iter()
      .find(|def| def.name.as_ref() == function_name)
      .and_then(|def| def.codegen_name());
    if let Some(function_name) = function_name {
      let f = unsafe {
        m.llvm_unit.ee.get_function::<unsafe extern "C" fn(A) -> T>(function_name)
      };
      if let Ok(f) = f {
        let v = unsafe { f.call(arg) };
        return Ok(v);
      }
    }
    panic!("function not found in compiled units");
  }
}