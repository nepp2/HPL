
use crate::error::{Error, error, error_raw};
use crate::value::{SymbolTable, display_expr, RefStr, Expr};
use crate::lexer;
use crate::parser;
use crate::typecheck::{
  Type, Val, StructDefinition, FunctionDefinition,
  TypeChecker, ScriptString, AstNode };
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
use inkwell::data_layout::DataLayout;
use inkwell::targets::{InitializationConfig, Target, TargetData}; // TODO: DELETE?

use llvm_sys::support::LLVMLoadLibraryPermanently;
use dlltest;

static mut LOADED_SYMBOLS : bool = false;

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
  pub sym : SymbolTable,
  pub context : Context,
  pub modules : Vec<CompiledExpression>,
  pub functions : HashMap<RefStr, Rc<FunctionDefinition>>,
  pub compiled_functions : HashMap<RefStr, FunctionValue>,
  pub struct_types : HashMap<RefStr, Rc<StructDefinition>>,
  pub global_var_types: HashMap<RefStr, Type>,
}

impl Interpreter {
  pub fn new() -> Interpreter {

    unsafe {
      if !LOADED_SYMBOLS {
        // TODO: DELETE?
        Target::initialize_native(&InitializationConfig::default()).expect("Failed to initialize native target");

        dlltest::function_from_dll(4, 5); // DELETE?
        function_from_executable(4, 5); // DELETE?
        // This makes sure that any symbols in the main executable can be
        // linked to the code we generate with the JIT. This includes any
        // DLLs used by the main exe.
        LLVMLoadLibraryPermanently(std::ptr::null());
        LOADED_SYMBOLS = true;
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

  pub fn compile_expression(&mut self, expr : &Expr) -> Result<&CompiledExpression, Error> {
    let mut type_checker =
      TypeChecker::new(
        true, HashMap::new(), &mut self.functions, &mut self.struct_types,
        &mut self.global_var_types, &mut self.sym);
    let ast = type_checker.to_ast(expr)?;
    let module_name = format!("module_{}", self.modules.len());
    let mut module = self.context.create_module(&module_name);

    // TODO: remove?
    let target = TargetData::create("e-m:e-i64:64-f80:128-n8:16:32:64-S128");
    module.set_data_layout(&target.get_data_layout());

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

    let ee =
      module.create_jit_execution_engine(OptimizationLevel::None)
      .map_err(|e| error_raw(expr, e.to_string()))?;

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
      Type::Ptr(t) => {
        if let Type::U8 = t.as_ref() {
          unsafe{
            let ptr = execute::<*mut u8>(f, &c.ee);
            let slice = std::slice::from_raw_parts(ptr, 10);
            let s = std::str::from_utf8(slice).expect("wasn't a valid utf8 string!");
            println!("transmuted string: {}", s);
          }          
        }
        else if let Type::Struct(def) = t.as_ref() {
          if def.name.as_ref() == "string" {
            unsafe{
              let ptr = execute::<*mut ScriptString>(f, &c.ee);
              let ss = &*ptr;
              let temp : [ u64 ; 2 ] = std::mem::transmute_copy(&ss);
              println!("transmuted string: [{}, {}]", temp[0], temp[1]);
            }
          }
        }
        return error(expr, "can't return a pointer from a top-level function");
      }
      Type::Struct(def) => {
        if def.name.as_ref() == "string" {
          let ss = execute::<ScriptString>(f, &c.ee);
          //Ok(Val::String(ss.to_string()))
          let temp : [ u64 ; 2 ] = unsafe { std::mem::transmute_copy(&ss) };
          println!("transmuted string: [{:#b}, {:#b}]", temp[0], temp[1]);
          Val::U64(ss.length)
        }
        else {
          return error(expr, "can't return a struct from a top-level function");
        }
      }
    };
    // unsafe { f.delete(); }
    // TODO: ee.remove_module(&i.module).unwrap();
    //self.modules.push((module, ee));
    Ok(result)
  }
}
