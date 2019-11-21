
use crate::error::Error;
use crate::structure::Val;
use crate::modules::CompiledModule;
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
  pub compiled_modules : Vec<CompiledModule>,
}

pub fn interpreter() -> Interpreter {
  let c = Compiler::new();
  let mut i = Interpreter { c, compiled_modules: vec![] };
  
  // load prelude
  if let Err(e) = i.load_prelude() {
    println!("error loading prelude, {}", e);
  }
  
  return i;
}

impl Interpreter {

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    let imports : Vec<_> = self.compiled_modules.iter().collect();
    let (m, val) = self.c.load_module(imports.as_slice(), expr)?;
    self.compiled_modules.push(m);
    Ok(val)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {
    let expr = self.c.parse(code)?;
    self.run_expression(&expr)
  }

  pub fn load_module(&mut self, code : &str) -> Result<(), Error> {
    self.run(code)?;
    Ok(())
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
    self.load_module(code)?;
    let m = self.compiled_modules.last().unwrap();
    let function_name = m.t.functions.values()
      .find(|def| def.name_in_code.as_ref() == function_name)
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

  // /// Load expression as a module and return the value of its top-level function
  // pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
  //   let (v, _) = self.compile_and_initialise_module(expr)?;
  //   Ok(v)
  // }

  // /// Compile and initialise a new module
  // pub fn build_module(&mut self, expr : &Expr) -> Result<&CompiledModule, Error> {
  //   let (_, c) = self.compile_and_initialise_module(expr)?;
  //   Ok(c)
  // }
}