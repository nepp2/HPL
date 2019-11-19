
use crate::error::{Error, error, error_raw};
use crate::expr::{StringCache, Expr, UIDGenerator};
use crate::lexer;
use crate::parser;
use crate::c_interface::CSymbols;
use crate::structure;
use crate::structure::{Val, TOP_LEVEL_FUNCTION_NAME};
use crate::inference;
use crate::inference::{ Type, ModuleInfo, FunctionImplementation };
use crate::codegen2::{Gen, CompiledUnit, dump_module, CompileInfo};

use inkwell::context::{Context};
// use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::targets::{InitializationConfig, Target };

use llvm_sys::support::LLVMLoadLibraryPermanently;

// TODO: Get rid of this static mut?
static mut LOADED_SYMBOLS : bool = false;

// TODO: Put these options somewhere more sensible
static DEBUG_PRINTING_EXPRS : bool = false;
static DEBUG_PRINTING_IR : bool = false;
static ENABLE_IR_OPTIMISATION : bool = false;

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

pub fn test_inference(code : &str) {
  let cache = StringCache::new();
  let mut gen = UIDGenerator::new();
  let mut c_symbols = CSymbols::new();
  c_symbols.populate();
  let tokens =
    lexer::lex(&code, &cache)
    .map_err(|mut es| es.remove(0)).unwrap();
  let expr = parser::parse(tokens, &cache).expect("parse errors");
  let nodes = structure::to_nodes(&mut gen, &cache, &expr).expect("node errors");
  let m = inference::base_module(&mut gen, &cache);
  let (info, cg) = inference::infer_types(&m, &mut gen, &cache, &nodes).unwrap();

}

// pub struct InterpreterInner {
//   pub cache : StringCache,
//   pub context : Context,
//   pub modules : Vec<CompiledModule>,
//   pub c_symbols : CSymbols,
//   pub uid_generator : UIDGenerator,
// }

// pub type Interpreter = Box<InterpreterInner>;

// pub fn interpreter() -> Interpreter {
//   unsafe {
//     if !LOADED_SYMBOLS {
//       // TODO: delete?
//       Target::initialize_native(&InitializationConfig::default()).expect("Failed to initialize native target");

//       // This makes sure that any symbols in the main executable can be
//       // linked to the code we generate with the JIT. This includes any
//       // DLLs used by the main exe.
//       LLVMLoadLibraryPermanently(std::ptr::null());

//       LOADED_SYMBOLS = true;
//     }
//   }

//   let cache = StringCache::new();
//   let context = Context::create();
//   let modules = vec!();
//   let mut c_symbols = CSymbols::new();
//   c_symbols.populate();
  
//   let mut i = Box::new(InterpreterInner { cache, context, modules, c_symbols, uid_generator: UIDGenerator::new() });
//   let i_raw = (&mut *i) as *mut InterpreterInner;
//   i.c_symbols.add_symbol("compiler", i_raw);
  
//   // load prelude
//   if let Err(e) = i.load_prelude() {
//     println!("error loading prelude, {}", e);
//   }
  
//   return i;
// }

// impl InterpreterInner {

//   fn load_module(&mut self, code : &str) -> Result<(), Error> {
//     let expr = self.parse_string(code)?;
//     self.run_expression(&expr)?;
//     Ok(())
//   }

//   fn load_prelude(&mut self) -> Result<(), Error> {
//     let mut f = File::open(PRELUDE_PATH).expect("failed to load prelude");
//     let mut code = String::new();
//     f.read_to_string(&mut code).unwrap();
//     self.load_module(&code)?;
//     Ok(())
//   }

//   pub fn parse_string(&mut self, code : &str) -> Result<Expr, Error> {
//     let tokens =
//       lexer::lex(code, &self.cache)
//       .map_err(|mut es| es.remove(0))?;
//     let expr = parser::parse(tokens, &self.cache)?;
//     Ok(expr)
//   }

//   pub fn run(&mut self, code : &str) -> Result<Val, Error> {;
//     let expr = self.parse_string(code)?;
//     self.run_expression(&expr)
//   }

//   pub fn get_function_address(&self, module_id : u64, name : &str) -> Option<u64> {
//     // TODO: panics if there is more than one overload, because no argument types
//     // are provided to narrow the search, and it would be very unsafe to return
//     // the wrong one.
//     self.modules.iter().find(|cm| cm.info.id == module_id)
//     .and_then(|cm| {
//       let mut i = cm.info.functions.iter()
//         .filter(|def| def.name_in_code.as_ref() == name);
//       let address =
//         i.next().and_then(|def|
//           unsafe { cm.ee.get_function_address(&def.name_for_codegen) });
//       if i.next().is_some() {
//         panic!("two matching overloads for '{}' in get_function_address", name)
//       }
//       address
//     })
//   }

//   // Calls a function that accepts an OUT pointer as an argument, in C style.
//   pub fn run_with_pointer_return<A>(
//     &mut self, code : &str, function_name: &str)
//       -> Result<A, Error>
//   {
//     let mut arg : A = unsafe { std::mem::zeroed() };
//     self.run_named_function_with_arg(code, function_name, &mut arg)?;
//     Ok(arg)
//   }

//   pub fn run_named_function_with_arg<T, A>(
//     &mut self, code : &str, function_name: &str, arg: A)
//       -> Result<T, Error>
//   {
//     let expr = self.parse_string(code)?;
//     let c = self.build_module(&expr)?;
//     let function_name =
//       c.info.functions.iter()
//       .find(|def| def.name_in_code.as_ref() == function_name)
//       .unwrap().name_for_codegen.as_ref();
//     let v = unsafe {
//       let jit_function =
//         c.ee.get_function::<unsafe extern "C" fn(A) -> T>(function_name)
//         .expect("could not find function in JIT-compiled module");
//       jit_function.call(arg)
//     };
//     Ok(v)
//   }

//   fn compile_and_initialise_module(&mut self, expr : &Expr) -> Result<(Val, &CompiledModule), Error> {
//     let c = {
//       let cm = compile_module(&mut self.uid_generator, expr, self.modules.as_slice(), &self.c_symbols, &mut self.context, &self.cache)?;
//       self.modules.push(cm);
//       self.modules.last().unwrap()
//     };
//     let f = TOP_LEVEL_FUNCTION_NAME;
//     let def = c.info.functions.iter().find(|def| def.name_in_code.as_ref() == TOP_LEVEL_FUNCTION_NAME).unwrap();
//     let value = match &def.signature.return_type {
//       Type::Bool => Val::Bool(execute::<bool>(f, &c.ee)),
//       Type::F64 => Val::F64(execute::<f64>(f, &c.ee)),
//       Type::F32 => Val::F32(execute::<f32>(f, &c.ee)),
//       Type::I64 => Val::I64(execute::<i64>(f, &c.ee)),
//       Type::I32 => Val::I32(execute::<i32>(f, &c.ee)),
//       Type::U64 => Val::U64(execute::<u64>(f, &c.ee)),
//       Type::U32 => Val::U32(execute::<u32>(f, &c.ee)),
//       Type::U16 => Val::U16(execute::<u16>(f, &c.ee)),
//       Type::U8 => Val::U8(execute::<u8>(f, &c.ee)),
//       Type::Void => {
//         execute::<()>(f, &c.ee);
//         Val::Void
//       }
//       t => {
//         return error(expr, format!("can't return value of type {:?} from a top-level function", t));
//       }
//     };
//     // unsafe { f.delete(); }
//     // TODO: ee.remove_module(&i.module).unwrap();
//     //self.modules.push((module, ee));
//     Ok((value, c))
//   }

//   /// Load expression as a module and return the value of its top-level function
//   pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
//     let (v, _) = self.compile_and_initialise_module(expr)?;
//     Ok(v)
//   }

//   /// Compile and initialise a new module
//   pub fn build_module(&mut self, expr : &Expr) -> Result<&CompiledModule, Error> {
//     let (_, c) = self.compile_and_initialise_module(expr)?;
//     Ok(c)
//   }
// }

pub struct Compiler {
  context : Context,
  gen : UIDGenerator,
  cache : StringCache,
  c_symbols : CSymbols,
}

pub fn run_program(code : &str) {
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

  let context = Context::create();
  let gen = UIDGenerator::new();
  let cache = StringCache::new();
  let mut c_symbols = CSymbols::new();
  c_symbols.populate();

  let mut c = Box::new(Compiler { context, gen, cache, c_symbols });
  let cptr = (&mut *c) as *mut Compiler;
  c.c_symbols.add_symbol("compiler", cptr);

  let tokens =
    lexer::lex(&code, &c.cache)
    .map_err(|mut es| es.remove(0)).unwrap();

  let expr = parser::parse(tokens, &c.cache).expect("parse errors");

  let m = inference::base_module(&mut c.gen, &c.cache);

  let (cu, m) = compile_module(&mut *c, &m, &[], &expr).expect("codegen errors");
  run_top_level(&m, &cu).unwrap();
}

pub fn compile_module(c : &mut Compiler, m : &ModuleInfo, compiled_units : &[CompiledUnit], expr : &Expr)
  -> Result<(CompiledUnit, ModuleInfo), Error>
{
  if DEBUG_PRINTING_EXPRS {
    println!("{}", expr);
  }

  let nodes = structure::to_nodes(&mut c.gen, &c.cache, &expr)?;
  let (m, cg) = inference::infer_types(&m, &mut c.gen, &c.cache, &nodes).unwrap();

  let module_name = format!("{:?}", m.id);
  let mut llvm_module = c.context.create_module(&module_name);

  let ee =
    llvm_module.create_jit_execution_engine(OptimizationLevel::None)
    .map_err(|e| error_raw(expr, e.to_string()))?;

  let pm = PassManager::create(&llvm_module);
  if ENABLE_IR_OPTIMISATION {
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.add_gvn_pass();
    pm.add_cfg_simplification_pass();
    pm.add_basic_alias_analysis_pass();
    pm.add_promote_memory_to_register_pass();
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
  }
  pm.initialize();

  let mut globals_to_link : Vec<(GlobalValue, usize)> = vec![];
  let mut functions_to_link : Vec<(FunctionValue, usize)> = vec![];
  {
    let gen = Gen::new(
        &mut c.context, &mut llvm_module, &mut ee.get_target_data(),
        &c.c_symbols.local_symbol_table, &mut globals_to_link, &mut functions_to_link, &pm);
    let info = CompileInfo::new(compiled_units, &m, &cg, &nodes);
    gen.codegen_module(&info)?
  };

  if DEBUG_PRINTING_IR {
    dump_module(&llvm_module);
  }

  // Link c globals
  for (global_value, address) in globals_to_link.iter() {
    // println!("c global '{}' - {}", name, address);
    ee.add_global_mapping(global_value, *address);
  }

  // Link c functions
  for (function_value, address) in functions_to_link.iter() {
    // println!("c function '{}' - {}", name, address);
    ee.add_global_mapping(function_value, *address);
  }

  // TODO: is this needed?
  ee.run_static_constructors();

  let cu = CompiledUnit { module_id: m.id, ee, llvm_module };
  Ok((cu, m))
}

fn run_top_level(m : &ModuleInfo, cu : &CompiledUnit) -> Result<Val, Error> {
  let f = TOP_LEVEL_FUNCTION_NAME;
  let def = m.functions.values().find(|def| def.name_in_code.as_ref() == f).unwrap();
  let f = if let FunctionImplementation::Normal{ name_for_codegen, .. } = &def.implementation {
    name_for_codegen.as_ref()
  }
  else {
    f
  };
  let sig = m.types.signature(def.signature);
  let value = match sig.return_type {
    Type::Bool => Val::Bool(execute::<bool>(f, &cu.ee)),
    Type::F64 => Val::F64(execute::<f64>(f, &cu.ee)),
    Type::F32 => Val::F32(execute::<f32>(f, &cu.ee)),
    Type::I64 => Val::I64(execute::<i64>(f, &cu.ee)),
    Type::I32 => Val::I32(execute::<i32>(f, &cu.ee)),
    Type::U64 => Val::U64(execute::<u64>(f, &cu.ee)),
    Type::U32 => Val::U32(execute::<u32>(f, &cu.ee)),
    Type::U16 => Val::U16(execute::<u16>(f, &cu.ee)),
    Type::U8 => Val::U8(execute::<u8>(f, &cu.ee)),
    Type::Void => {
      execute::<()>(f, &cu.ee);
      Val::Void
    }
    t => {
      return error(def.loc, format!("can't return value of type {:?} from a top-level function", t));
    }
  };
  Ok(value)
}
