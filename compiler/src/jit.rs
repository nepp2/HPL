
use crate::error::{Error, error, error_raw};
use crate::value::{StringCache, display_expr, RefStr, Expr};
use crate::lexer;
use crate::parser;
use crate::typecheck::{
  Type, Val, StructDefinition, FunctionDefinition,
  TypeChecker, AstNode };
use crate::codegen::{dump_module, Gen};
use crate::c_interface::CLibraries;

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
use inkwell::targets::{InitializationConfig, Target};

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
  pub f : FunctionValue,
  pub ee : ExecutionEngine,
  pub m : Module,
  pub ast : AstNode,
}

pub struct Interpreter {
  pub cache : StringCache,
  pub context : Context,
  pub modules : Vec<CompiledExpression>,
  pub c_libs : CLibraries,
  pub functions : HashMap<RefStr, Rc<FunctionDefinition>>,
  pub struct_types : HashMap<RefStr, Rc<StructDefinition>>,
  pub global_var_types: HashMap<RefStr, Type>,
}

impl Interpreter {
  pub fn new() -> Interpreter {

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
    let modules = vec!();
    let c_libs = CLibraries::new();
    let functions = HashMap::new();
    let struct_types = HashMap::new();
    let global_var_types = HashMap::new();

    let mut i = 
      Interpreter {
        cache, context, modules, c_libs,
        functions, struct_types,
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
    let mut f = File::open(PRELUDE_PATH).expect("failed to load prelude");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    self.load_module(&code)?;
    Ok(())
  }

  fn parse_string(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex(code, &mut self.cache)
      .map_err(|mut es| es.remove(0))?;
    parser::parse(tokens, &mut self.cache)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {;
    let expr = self.parse_string(code)?;
    self.run_expression(&expr)
  }

  pub fn compile_expression(&mut self, expr : &Expr) -> Result<&CompiledExpression, Error> {
    let mut type_checker =
      TypeChecker::new(
        true, HashMap::new(), &mut self.functions, &mut self.struct_types,
        &mut self.global_var_types, &self.c_libs.local_symbol_table, &mut self.cache);
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
    let mut c_functions : HashMap<RefStr, (FunctionValue, usize)> = HashMap::new();
    let f = {
      let jit =
        Gen::new(
          &mut self.context, &mut module, &self.functions, &mut external_globals,
          &mut external_functions, &mut c_functions, &self.global_var_types,
          &self.struct_types, &pm);
      jit.codegen_module(&ast)?
    };

    // TODO: provide an option for this?
    println!("{}", display_expr(expr));
    dump_module(&module);

    let ee =
      module.create_jit_execution_engine(OptimizationLevel::None)
      .map_err(|e| error_raw(expr, e.to_string()))?;

    // Link c functions
    for (function_value, address) in c_functions.values() {
      ee.add_global_mapping(function_value, *address);
    }

    // Link global variables
    for (global_name, global_value) in external_globals.iter() {
      for c in self.modules.iter() {
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
      for c in self.modules.iter() {
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

    self.modules.push(CompiledExpression { f, ee, m: module, ast });
    Ok(self.modules.last().unwrap())
  }

  pub fn run_unwrapped<T>(&mut self, code : &str) -> Result<T, Error> {
    let expr = self.parse_string(code)?;
    let c = self.compile_expression(&expr)?;
    let f = c.f.get_name().to_str().unwrap();
    let v : T = execute(f, &c.ee);
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
    let f = c.f.get_name().to_str().unwrap();
    let result = match &c.ast.type_tag {
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
      Type::Ptr(_) => {
        return error(expr, "can't return a pointer from a top-level function");
      }
      Type::Struct(_def) => {
        return error(expr, "can't return a struct from a top-level function");
      }
    };
    // unsafe { f.delete(); }
    // TODO: ee.remove_module(&i.module).unwrap();
    //self.modules.push((module, ee));
    Ok(result)
  }
}
