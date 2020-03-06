
use crate::error::Error;
use crate::compiler::{Val, Compiler};
use crate::types::UnitId;

use std::fs::File;
use std::io::Read;

// TODO: fix this gross hack
#[cfg(not(test))]
const CODE_PATH : &'static str = "code/";
#[cfg(test)]
const CODE_PATH : &'static str = "../code/";

pub struct Interpreter {
  pub c : Box<Compiler>,
  imports : Vec<UnitId>,
}

pub fn interpreter() -> Interpreter {
  let c = Compiler::new();
  let mut i = Interpreter { c, imports: vec![] };
  
  // loading core modules
  if let Err(e) = i.load_core_modules() {
    println!("error loading code modules, {}", e);
  }
  
  return i;
}

impl Interpreter {
  
  pub fn eval(&mut self, code : &str) -> Result<Val, Error> {
    Ok(self.load_module(code, None)?.1)
  }

  pub fn run_module(&mut self, code : &str, name : &str) -> Result<Val, Error> {
    Ok(self.load_module(code, Some(name))?.1)
  }

  fn load_module(&mut self, code : &str, name : Option<&str>) -> Result<(UnitId, Val), Error> {
    let (unit_id, val) = self.c.load_module(code, name, &self.imports)?;
    self.imports.push(unit_id);
    Ok((unit_id, val))
  }

  fn load_core_modules(&mut self) -> Result<(), Error> {
    for module_name in &["prelude", "list", "compiler"] {
      let path = format!("{}core/{}.code", CODE_PATH, module_name);
      let mut f = File::open(&path).expect("failed to load prelude");
      let mut code = String::new();
      f.read_to_string(&mut code).unwrap();
      self.load_module(&code, Some(&path))?;
    }
    Ok(())
  }

  /// Calls a function that accepts an OUT pointer as an argument, in C style.
  #[allow(dead_code)]
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