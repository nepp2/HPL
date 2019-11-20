
use crate::error::Error;
use crate::structure::Val;
use crate::inference;
use crate::types::TypeInfo;
use crate::codegen2::CompiledUnit;
use crate::compile::Compiler;
use crate::expr::Expr;

use owning_ref::BoxRef;
use std::fs::File;
use std::io::Read;

// TODO: fix this gross hack
#[cfg(not(test))]
static PRELUDE_PATH : &'static str = "code/prelude.code";
#[cfg(test)]
static PRELUDE_PATH : &'static str = "../code/prelude.code";

pub struct IModule { cu: CompiledUnit, info : TypeInfo }

pub struct Interpreter {
  pub c : Box<Compiler>,
  pub compiled_units : Vec<CompiledUnit>,
  pub type_info : TypeInfo,
}

pub fn interpreter() -> Interpreter {
  let mut c = Compiler::new();
  let type_info = inference::base_module(&mut c.gen);
  let mut i = Interpreter { c, type_info, compiled_units: vec![] };
  
  // load prelude
  if let Err(e) = i.load_prelude() {
    println!("error loading prelude, {}", e);
  }
  
  return i;
}

impl Interpreter {

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    let (cu, module_info, val) = self.c.load_module(&self.type_info, self.compiled_units.as_slice(), expr)?;
    self.compiled_units.push(cu);
    self.type_info = module_info;
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
    let r =
      self.type_info.functions.values()
      .find(|def| def.name_in_code.as_ref() == function_name)
      .and_then(|def| def.codegen_name().map(|n| (n, def)));
    if let Some((function_name, def)) = r {
      let f =
        self.compiled_units.iter().rev().filter(|cu| cu.module_id == def.module_id)
        .flat_map(|cu| unsafe {
          cu.ee.get_function::<unsafe extern "C" fn(A) -> T>(function_name)
        })
        .next();
      if let Some(f) = f {
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