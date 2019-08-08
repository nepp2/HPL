
use crate::error::{Error, error, error_raw};
use crate::expr::{StringCache, RefStr, Expr};
use crate::lexer;
use crate::parser;
use crate::typecheck;
use crate::typecheck::{
  Type, Val, TypedModule, TOP_LEVEL_FUNCTION_NAME };
use crate::codegen::Gen; // TODO {dump_module}
use crate::c_interface::CSymbols;

use std::collections::HashMap;
use std::fs::File;
use std::io::Read;

use inkwell::context::{Context};
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::targets::{InitializationConfig, Target };

use llvm_sys::support::LLVMLoadLibraryPermanently;

static mut LOADED_SYMBOLS : bool = false;

// TODO: fix this gross hack
#[cfg(not(test))]
static PRELUDE_PATH : &'static str = "code/prelude.code";
#[cfg(test)]
static PRELUDE_PATH : &'static str = "../code/prelude.code";

fn execute<T>(function_name : &str, ee : &ExecutionEngine) -> T {
  unsafe {
    let jit_function =
      ee.get_function::<unsafe extern "C" fn() -> T>(function_name)
      .expect("could not find function in JIT-compiled module");
    jit_function.call()
  }
}

pub struct CompiledExpression {
  pub ee : ExecutionEngine,
  pub m : Module,
  pub typed_module : TypedModule,
}

pub struct InterpreterInner {
  pub cache : StringCache,
  pub context : Context,
  pub expressions : Vec<CompiledExpression>,
  pub c_symbols : CSymbols,
  pub global_module : TypedModule,
}

pub type Interpreter = Box<InterpreterInner>;

pub fn interpreter() -> Interpreter {
  unsafe {
    if !LOADED_SYMBOLS {
      // TODO: delete?
      Target::initialize_native(&InitializationConfig::default()).expect("Failed to initialize native target");

      // This makes sure that any symbols in the main executable can be
      // linked to the code we generate with the JIT. This includes any
      // DLLs used by the main exe.
      LLVMLoadLibraryPermanently(std::ptr::null());

      LOADED_SYMBOLS = true;
    }
  }

  let cache = StringCache::new();
  let context = Context::create();
  let expressions = vec!();
  let c_symbols = CSymbols::new();
  let global_module = TypedModule::new();
  
  let mut i = Box::new(InterpreterInner { cache, context, expressions, c_symbols, global_module });

  let i_raw = (&mut *i) as *mut InterpreterInner;

  i.c_symbols.populate(i_raw);
  
  // load prelude
  if let Err(e) = i.load_prelude() {
    println!("error loading prelude, {}", e);
  }
  
  return i;
}

impl InterpreterInner {

  fn load_module(&mut self, code : &str) -> Result<(), Error> {
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)?;
    Ok(())
  }

  fn load_prelude(&mut self) -> Result<(), Error> {
    let mut f = File::open(PRELUDE_PATH).expect("failed to load prelude");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    self.load_module(&code)?;
    Ok(())
  }

  fn parse_string(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex(code, &self.cache)
      .map_err(|mut es| es.remove(0))?;
    parser::parse(tokens, &self.cache)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {;
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)
  }

  pub fn compile_expression(&mut self, expr : &Expr) -> Result<&CompiledExpression, Error> {
    // TODO: provide an option for this?
    // println!("{}", display_expr(expr));

    let typed_module = typecheck::to_typed_module(&self.c_symbols.local_symbol_table, &[self.global_module.clone()], &self.cache, expr)?;

    // add module contents to the global interpreter module
    self.global_module.functions = self.global_module.functions.clone().union(typed_module.functions.clone());
    self.global_module.types = self.global_module.types.clone().union(typed_module.types.clone());
    self.global_module.globals = self.global_module.globals.clone().union(typed_module.globals.clone());

    let module_name = format!("expression_{}", self.expressions.len());
    let mut module = self.context.create_module(&module_name);

    let ee =
      module.create_jit_execution_engine(OptimizationLevel::None)
      .map_err(|e| error_raw(expr, e.to_string()))?;

    // TODO module.set_target(target: &Target);

    // TODO: enable passes again (and figure out what to include)
    let pm = PassManager::create(&module);
    // pm.add_instruction_combining_pass();
    // pm.add_reassociate_pass();
    // pm.add_gvn_pass();
    // pm.add_cfg_simplification_pass();
    // pm.add_basic_alias_analysis_pass();
    // pm.add_promote_memory_to_register_pass();
    // pm.add_instruction_combining_pass();
    // pm.add_reassociate_pass();  
    pm.initialize();

    let mut external_globals : HashMap<RefStr, GlobalValue> = HashMap::new();
    let mut external_functions : HashMap<RefStr, FunctionValue> = HashMap::new();
    let mut c_functions : HashMap<RefStr, (FunctionValue, usize)> = HashMap::new();
    {
      let jit =
        Gen::new(
          &mut self.context, &mut module, &mut ee.get_target_data(), &mut self.global_module, &mut external_globals,
          &mut external_functions, &mut c_functions, &pm);
      jit.codegen_module(&typed_module)?
    };
    
    // TODO: provide an option for this?
    // dump_module(&module);

    // Link c functions
    for (function_value, address) in c_functions.values() {
      ee.add_global_mapping(function_value, *address);
    }

    // Link global variables
    for (global_name, global_value) in external_globals.iter() {
      for c in self.expressions.iter() {
        if let Some(g) = c.m.get_global(global_name) {
          if g.get_linkage() == Linkage::Internal {
            unsafe {
              let address = c.ee.get_global_address(global_name).unwrap();
              ee.add_global_mapping(global_value, address as usize);
              break;
            }
          }
        }
      }
    }

    // Link external functions
    for (function_name, function_value) in external_functions.iter() {
      for c in self.expressions.iter() {
        if let Some(f) = c.m.get_function(function_name) {
          if f.count_basic_blocks() > 0 {
            unsafe {
              let address = c.ee.get_function_address(function_name).unwrap();
              ee.add_global_mapping(function_value, address as usize);
              break;
            }
          }
        }
      }
    }

    // TODO: is this needed?
    ee.run_static_constructors();

    self.expressions.push(CompiledExpression { ee, m: module, typed_module });
    Ok(self.expressions.last().unwrap())
  }

  pub fn run_unwrapped<T>(&mut self, code : &str) -> Result<T, Error> {
    let expr = self.parse_string(code)?;
    let c = self.compile_expression(&expr)?;
    let v : T = execute(TOP_LEVEL_FUNCTION_NAME, &c.ee);
    Ok(v)
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
    let expr = self.parse_string(code)?;
    let c = self.compile_expression(&expr)?;
    let v = unsafe {
      let jit_function =
        c.ee.get_function::<unsafe extern "C" fn(A) -> T>(function_name)
        .expect("could not find function in JIT-compiled module");
      jit_function.call(arg)
    };
    Ok(v)
  }

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    let c = self.compile_expression(expr)?;
    let f = TOP_LEVEL_FUNCTION_NAME;
    let def = c.typed_module.functions.get(TOP_LEVEL_FUNCTION_NAME).unwrap();
    let result = match &def.signature.return_type {
      Type::Bool => Val::Bool(execute::<bool>(f, &c.ee)),
      Type::F64 => Val::F64(execute::<f64>(f, &c.ee)),
      Type::F32 => Val::F32(execute::<f32>(f, &c.ee)),
      Type::I64 => Val::I64(execute::<i64>(f, &c.ee)),
      Type::I32 => Val::I32(execute::<i32>(f, &c.ee)),
      Type::U64 => Val::U64(execute::<u64>(f, &c.ee)),
      Type::U32 => Val::U32(execute::<u32>(f, &c.ee)),
      Type::U16 => Val::U16(execute::<u16>(f, &c.ee)),
      Type::U8 => Val::U8(execute::<u8>(f, &c.ee)),
      Type::Void => {
        execute::<()>(f, &c.ee);
        Val::Void
      }
      Type::Fun(_) => {
        return error(expr, "can't return a function from a top-level function");
      }
      Type::Ptr(_) => {
        return error(expr, "can't return a pointer from a top-level function");
      }
      Type::Def(_def) => {
        return error(expr, "can't return a struct or union from a top-level function");
      }
    };
    // unsafe { f.delete(); }
    // TODO: ee.remove_module(&i.module).unwrap();
    //self.modules.push((module, ee));
    Ok(result)
  }
}
