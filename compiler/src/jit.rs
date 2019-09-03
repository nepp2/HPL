
use crate::error::{Error, error, error_raw};
use crate::expr::{StringCache, RefStr, Expr};
use crate::lexer;
use crate::parser2;
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

  pub fn parse_string(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex(code, &self.cache)
      .map_err(|mut es| es.remove(0))?;
    let expr = parser2::parse(tokens, &self.cache)?;
    println!("{}", expr);
    Ok(expr)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {;
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)
  }

  pub fn compile_expression(&mut self, expr : &Expr) -> Result<&CompiledExpression, Error> {
    let modules : Vec<_> = self.expressions.iter().collect();
    let ce = compile_expression(expr, modules.as_slice(), &self.c_symbols, &mut self.context, &self.cache)?;
    self.expressions.push(ce);
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
      t => {
        return error(expr, format!("can't return value of type {:?} from a top-level function", t));
      }
    };
    // unsafe { f.delete(); }
    // TODO: ee.remove_module(&i.module).unwrap();
    //self.modules.push((module, ee));
    Ok(result)
  }
}

pub fn compile_expression(expr : &Expr, external_modules : &[&CompiledExpression], c_symbols : &CSymbols, context : &mut Context, cache : &StringCache) -> Result<CompiledExpression, Error> {
  // TODO: provide an option for this?
  // println!("{}", expr);

  let mut modules : Vec<_> = external_modules.iter().map(|c| &c.typed_module).collect();

  let typed_module = typecheck::to_typed_module(&c_symbols.local_symbol_table, modules.as_slice(), cache, expr)?;

  modules.push(&typed_module);

  let module_name = format!("module_{}", modules.len());
  let mut module = context.create_module(&module_name);

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
  let mut c_globals : HashMap<RefStr, (GlobalValue, usize)> = HashMap::new();
  {
    let jit =
      Gen::new(
        context, &mut module, &mut ee.get_target_data(), modules.as_slice(), &mut external_globals,
        &mut external_functions, &mut c_functions, &mut c_globals, &pm);
    jit.codegen_module(&typed_module)?
  };

  // TODO: provide an option for this?
  // dump_module(&module);

  // Link c functions
  for (_name, (function_value, address)) in c_functions.iter() {
    // println!("c function '{}' - {}", name, address);
    ee.add_global_mapping(function_value, *address);
  }

  // Link c globals
  for (_name, (global_value, address)) in c_globals.iter() {
    // println!("c global '{}' - {}", name, address);
    ee.add_global_mapping(global_value, *address);
  }

  // Link global variables
  for (global_name, global_value) in external_globals.iter() {
    let c = 
      external_modules.iter()
      .filter(|c| {
        c.m.get_global(global_name)
        .filter(|g| g.get_linkage() == Linkage::Internal)
        .is_some()
      })
      .nth(0);
    if let Some(c) = c {
      unsafe {
        let address = c.ee.get_global_address(global_name).unwrap();
        ee.add_global_mapping(global_value, address as usize);
        break;
      }
    }
    else {
      panic!("compile error: external global '{}' not found", global_name);
    }
  }

  // Link external functions
  for (function_name, function_value) in external_functions.iter() {
    let c = 
      external_modules.iter()
      .filter(|c| {
        c.m.get_function(function_name)
        .filter(|f| f.count_basic_blocks() > 0)
        .is_some()
      })
      .nth(0);
    if let Some(c) = c {
      unsafe {
        let address = c.ee.get_function_address(function_name).unwrap();
        ee.add_global_mapping(function_value, address as usize);
      }
    }
    else {
      panic!("compile error: external function '{}' not found", function_name);
    }
  }

  // TODO: is this needed?
  ee.run_static_constructors();

  Ok(CompiledExpression { ee, m: module, typed_module })
}
