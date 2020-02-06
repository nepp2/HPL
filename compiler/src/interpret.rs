
use crate::error::Error;
use crate::compiler::{Val, Compiler};
use crate::types::UnitId;

use std::fs::File;
use std::io::Read;

// TODO: fix this gross hack
#[cfg(not(test))]
static PRELUDE_PATH : &'static str = "code/prelude.code";
#[cfg(test)]
static PRELUDE_PATH : &'static str = "../code/prelude.code";

pub struct Interpreter {
  pub c : Box<Compiler>,
  imports : Vec<UnitId>,
}

pub fn interpreter() -> Interpreter {
  let c = Compiler::new();
  let mut i = Interpreter { c, imports: vec![] };
  
  // load prelude
  if let Err(e) = i.load_prelude() {
    println!("error loading prelude, {}", e);
  }
  
  return i;
}

impl Interpreter {
  
  pub fn eval(&mut self, code : &str) -> Result<Val, Error> {
    Ok(self.load_module(code, None)?.1)
  }

  fn load_module(&mut self, code : &str, name : Option<&str>) -> Result<(UnitId, Val), Error> {
    let (unit_id, val) = self.c.load_module(code, name, &self.imports)?;
    self.imports.push(unit_id);
    Ok((unit_id, val))
  }

  fn load_prelude(&mut self) -> Result<(), Error> {
    let mut f = File::open(PRELUDE_PATH).expect("failed to load prelude");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    self.load_module(&code, Some("prelude"))?;
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
    let (unit_id, _) = self.load_module(code, None)?;
    let types = self.c.code_store.types(unit_id);
    let function_name = types.symbols.values()
      .find(|def| def.name.as_ref() == function_name)
      .and_then(|def| def.codegen_name());
    let lu = self.c.code_store.llvm_unit(unit_id);
    if let Some(function_name) = function_name {
      let f = unsafe {
        lu.ee.get_function::<unsafe extern "C" fn(A) -> T>(function_name)
      };
      if let Ok(f) = f {
        let v = unsafe { f.call(arg) };
        return Ok(v);
      }
    }
    panic!("function not found in compiled units");
  }
}