
use crate::error::{Error, error, error_raw};
use crate::expr::{StringCache, Expr, UIDGenerator};
use crate::lexer;
use crate::parser;
use crate::c_interface::CSymbols;
use crate::structure;
use crate::structure::{Val, TOP_LEVEL_FUNCTION_NAME};
use crate::inference;
use crate::types::{ Type, ModuleInfo, FunctionImplementation };
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

fn execute<T>(function_name : &str, ee : &ExecutionEngine) -> T {
  unsafe {
    let jit_function =
      ee.get_function::<unsafe extern "C" fn() -> T>(function_name)
      .expect("could not find function in JIT-compiled module");
    jit_function.call()
  }
}

pub fn run_program(code : &str) -> Result<Val, Error> {
  let mut c = Compiler::new();

  let expr = c.parse(code)?;

  let m = inference::base_module(&mut c.gen, &c.cache);

  let (cu, m) = c.compile_module(&m, &[], &expr)?;
  run_top_level(&m, &cu)
}

pub struct Compiler {
  pub context : Context,
  pub gen : UIDGenerator,
  pub cache : StringCache,
  pub c_symbols : CSymbols,
}

impl Compiler {
  pub fn new() -> Box<Compiler> {
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
    c
  }

  pub fn load_module(&mut self, m : &ModuleInfo, compiled_units : &[CompiledUnit], expr : &Expr)
    -> Result<(CompiledUnit, ModuleInfo, Val), Error>
  {
    let (cu, m) = self.compile_module(&m, compiled_units, &expr)?;
    let val = run_top_level(&m, &cu)?;
    Ok((cu, m, val))
  }

  pub fn parse(&mut self, code : &str) -> Result<Expr, Error> {
    let tokens =
      lexer::lex(&code, &self.cache)
      .map_err(|mut es| es.remove(0))?;
  
    parser::parse(tokens, &self.cache)
  }

  pub fn compile_module(&mut self, m : &ModuleInfo, compiled_units : &[CompiledUnit], expr : &Expr)
    -> Result<(CompiledUnit, ModuleInfo), Error>
  {
    if DEBUG_PRINTING_EXPRS {
      println!("{}", expr);
    }

    let nodes = structure::to_nodes(&mut self.gen, &self.cache, &expr)?;
    let (m, cg) = inference::infer_types(&m, &mut self.gen, &self.cache, &nodes).unwrap();

    let module_name = format!("{:?}", m.id);
    let mut llvm_module = self.context.create_module(&module_name);

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
          &mut self.context, &mut llvm_module, &mut ee.get_target_data(),
          &self.c_symbols.local_symbol_table, &mut globals_to_link, &mut functions_to_link, &pm);
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
