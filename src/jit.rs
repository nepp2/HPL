
use crate::error::{Error, error, error_raw};
use crate::value::{SymbolTable, display_expr, RefStr, Expr};
use crate::lexer;
use crate::parser;
use crate::typecheck::{
  Type, Val, StructDefinition, FunctionDefinition, TypeChecker };
use crate::codegen::{dump_module, Gen};

use std::rc::Rc;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;

use inkwell::context::{Context};
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;

use llvm_sys::support::LLVMLoadLibraryPermanently;
use dlltest;

static mut loaded_symbols : bool = false;

#[no_mangle]
pub extern "C" fn function_from_executable(a : i64, b : i64) -> i64 {
  a + b
}

/*
// Adding the functions above to a global array,
// so Rust compiler won't remove them.
#[used]
static EXTERNAL_FNS: [extern fn(i64, i64) -> i64; 1] = [blah];
*/

pub struct Interpreter {
  pub sym : SymbolTable,
  pub context : Context,
  pub modules : Vec<(Module, ExecutionEngine)>,
  pub functions : HashMap<RefStr, Rc<FunctionDefinition>>,
  pub compiled_functions : HashMap<RefStr, FunctionValue>,
  pub struct_types : HashMap<RefStr, Rc<StructDefinition>>,
  pub global_var_types: HashMap<RefStr, Type>,
}

impl Interpreter {
  pub fn new() -> Interpreter {

    unsafe {
      if !loaded_symbols {
        dlltest::function_from_dll(4, 5);
        function_from_executable(4, 5);
        // This makes sure that any symbols in the main executable can be
        // linked to the code we generate with the JIT. This includes any
        // DLLs used by the main exe.
        LLVMLoadLibraryPermanently(std::ptr::null());
        loaded_symbols = true;
      }
    }

    let sym = SymbolTable::new();
    let context = Context::create();
    let functions = HashMap::new();
    let compiled_functions = HashMap::new();
    let struct_types = HashMap::new();
    let global_var_types = HashMap::new();

    let modules = vec!();

    let mut i = 
      Interpreter {
        sym, context, modules, functions,
        compiled_functions, struct_types,
        global_var_types };
    
    // load prelude
    if let Err(e) = i.load_prelude() {
      println!("error loading prelude, {}", e);
    }
    
    return i;
  }

  fn load_module(&mut self, code : &str) -> Result<(), Error> {
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)?;
    Ok(())
  }

  fn load_prelude(&mut self) -> Result<(), Error> {
    let mut f = File::open("code/prelude_llvm.code").expect("file not found");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    self.load_module(&code)?;
    Ok(())
  }

  fn parse_string(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex(code, &mut self.sym)
      .map_err(|mut es| es.remove(0))?;
    parser::parse(tokens, &mut self.sym)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {;
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)
  }

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    let mut type_checker =
      TypeChecker::new(
        true, HashMap::new(), &mut self.functions, &mut self.struct_types,
        &mut self.global_var_types, &mut self.sym);
    let ast = type_checker.to_ast(expr)?;
    let module_name = format!("module_{}", self.modules.len());
    let mut module = self.context.create_module(&module_name);

    let pm = PassManager::create(&module);
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.add_gvn_pass();
    pm.add_cfg_simplification_pass();
    pm.add_basic_alias_analysis_pass();
    pm.add_promote_memory_to_register_pass();
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();  
    pm.initialize();

    let mut external_globals : HashMap<RefStr, GlobalValue> = HashMap::new();
    let mut external_functions : HashMap<RefStr, FunctionValue> = HashMap::new();
    let f = {
      let jit =
        Gen::new(
          &mut self.context, &mut module, &mut self.compiled_functions, &self.functions,
          &mut external_globals, &mut external_functions, &self.global_var_types, &pm);
      jit.codegen_module(&ast)?
    };
    println!("{}", display_expr(expr));
    dump_module(&module);

    fn execute<T>(expr : &Expr, f : FunctionValue, ee : &ExecutionEngine) -> Result<T, Error> {
      let function_name = f.get_name().to_str().unwrap();
      let v = unsafe {
        // ERROR_MAY_BE_HERE; 
        // TODO: i'm not sure that "get_function" actually calls "FinalizeObject"
        // see: https://llvm.org/doxygen/ExecutionEngineBindings_8cpp_source.html
        let jit_function =
          ee.get_function::<unsafe extern "C" fn() -> T>(function_name)
          .map_err(|e| error_raw(expr, format!("{:?}", e)))?;
        jit_function.call()
      };
      Ok(v)
    }
    let ee =
      module.create_jit_execution_engine(OptimizationLevel::None)
      .map_err(|e| error_raw(expr, e.to_string()))?;

    // Link global variables
    for (global_name, global_value) in external_globals.iter() {
      for (m, eee) in self.modules.iter() {
        if let Some(g) = m.get_global(global_name) {
          if g.get_linkage() == Linkage::Internal {
            unsafe {
              let address = eee.get_global_address(global_name).unwrap();
              ee.add_global_mapping(global_value, address as usize);
              break;
            }
          }
        }
      }
    }

    // Link external functions
    for (function_name, function_value) in external_functions.iter() {
      for (m, eee) in self.modules.iter() {
        if let Some(f) = m.get_function(function_name) {
          if f.count_basic_blocks() > 0 {
            unsafe {
              let address = eee.get_function_address(function_name).unwrap();
              ee.add_global_mapping(function_value, address as usize);
              break;
            }
          }
        }
      }
    }

    ee.run_static_constructors(); // TODO: this might not do anything :(
    let result = match ast.type_tag {
      Type::Bool => execute::<bool>(expr, f, &ee).map(Val::Bool),
      Type::F64 => execute::<f64>(expr, f, &ee).map(Val::F64),
      Type::F32 => execute::<f32>(expr, f, &ee).map(Val::F32),
      Type::I64 => execute::<i64>(expr, f, &ee).map(Val::I64),
      Type::I32 => execute::<i32>(expr, f, &ee).map(Val::I32),
      Type::U64 => execute::<u64>(expr, f, &ee).map(Val::U64),
      Type::U32 => execute::<u32>(expr, f, &ee).map(Val::U32),
      Type::Void => execute::<()>(expr, f, &ee).map(|_| Val::Void),
      Type::Array(_, _) => 
        error(expr, "can't return an array from a top-level function"),
      Type::Ptr(_) => 
        error(expr, "can't return a pointer from a top-level function"),
      Type::Struct(_) =>
        error(expr, "can't return a struct from a top-level function"),
    };
    // unsafe { f.delete(); }
    // TODO: ee.remove_module(&i.module).unwrap();
    self.modules.push((module, ee));
    result
  }
}
