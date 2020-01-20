
use crate::{
  error, c_interface, types, llvm_codegen, code_store,
};

use error::{Error, error_raw};
use c_interface::CSymbols;
use types::UnitId;
use code_store::CodeStore;
use llvm_codegen::{Gen, dump_module, CompileInfo };

use inkwell::context::{Context};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;

// TODO: Get rid of this static mut?
static mut LOADED_SYMBOLS : bool = false;

// TODO: Put these options somewhere more sensible
static DEBUG_PRINTING_EXPRS : bool = false;
static DEBUG_PRINTING_IR : bool = false;
static ENABLE_IR_OPTIMISATION : bool = false;

pub struct LlvmUnit {
  pub unit_id : UnitId,
  pub ee : ExecutionEngine,
  pub llvm_module : Module,
}

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
}

impl LlvmCompiler {
  pub fn new() -> LlvmCompiler {
    LlvmCompiler { context: Context::create() }
  }

  pub fn compile_unit(
    &self,
    unit_id : UnitId,
    code_store : &CodeStore,
    c_symbols : &CSymbols
  ) -> Result<LlvmUnit, Error>
  {
    let name = code_store.name(unit_id);
    let nodes = code_store.nodes(unit_id);
    let types = code_store.types(unit_id);
    let mapping = code_store.type_mapping(unit_id);

    let mut llvm_module = self.context.create_module(&name);

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
        &self.context, &mut llvm_module, &mut ee.get_target_data(),
        &c_symbols.local_symbol_table, &mut globals_to_link,
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
