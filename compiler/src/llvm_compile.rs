
use crate::{
  error, expr, c_interface, types, llvm_codegen, code_store,
};

use error::{Error, error_raw};
use expr::{StringCache, UIDGenerator};
use c_interface::CSymbols;
use types::UnitId;
use code_store::CodeStore;
use llvm_codegen::{Gen, LlvmUnit, dump_module, CompileInfo };

use inkwell::context::{Context};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::targets::{InitializationConfig, Target };

use llvm_sys::support::LLVMLoadLibraryPermanently;

// TODO: Get rid of this static mut?
static mut LOADED_SYMBOLS : bool = false;

// TODO: Put these options somewhere more sensible
static DEBUG_PRINTING_EXPRS : bool = false;
static DEBUG_PRINTING_IR : bool = false;
static ENABLE_IR_OPTIMISATION : bool = false;

pub fn execute_function<T>(function_name : &str, llvm_unit : &LlvmUnit) -> T {
  unsafe {
    let jit_function =
    llvm_unit.ee.get_function::<unsafe extern "C" fn() -> T>(function_name)
      .expect("could not find function in JIT-compiled module");
    jit_function.call()
  }
}

pub struct LlvmCompiler {
  pub context : Context,
  pub c_symbols : CSymbols,
}

impl LlvmCompiler {
  pub fn new() -> LlvmCompiler {
    unsafe {
      if !LOADED_SYMBOLS {
        // TODO: delete?
        Target::initialize_native(&InitializationConfig::default())
          .expect("Failed to initialize native target");
  
        // This makes sure that any symbols in the main executable can be
        // linked to the code we generate with the JIT. This includes any
        // DLLs used by the main exe.
        LLVMLoadLibraryPermanently(std::ptr::null());
  
        LOADED_SYMBOLS = true;
      }
    }
  
    let context = Context::create();
    let mut c_symbols = CSymbols::new();
    c_symbols.populate();

    LlvmCompiler { context, c_symbols }
  }

  pub fn compile_unit(
    &mut self,
    unit_id : UnitId,
    code_store : &CodeStore,
    gen : &mut UIDGenerator,
    cache : &StringCache,
  ) -> Result<LlvmUnit, Error>
  {
    let name = code_store.name(unit_id);
    let nodes = code_store.nodes(unit_id);
    let types = code_store.types(unit_id);
    let mapping = code_store.type_mapping(unit_id);

    let mut llvm_module = self.context.create_module(name);

    let ee =
      llvm_module.create_jit_execution_engine(OptimizationLevel::None)
      .map_err(|e| error_raw(nodes.root().loc, e.to_string()))?;

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
      //let type_directory
      let gen = Gen::new(
        &mut self.context, &mut llvm_module, &mut ee.get_target_data(),
        &self.c_symbols.local_symbol_table, &mut globals_to_link,
        &mut functions_to_link, &pm);
      let info = CompileInfo::new(code_store, types, nodes, mapping);
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

    let lu = LlvmUnit { unit_id, ee, llvm_module };
    Ok(lu)
  }
}
