
use crate::{
  common, error, c_interface, types, llvm_codegen, code_store, compiler
};

use common::*;
use error::Error;
use c_interface::CSymbols;
use types::{SymbolId, SymbolInit};
use code_store::{CodeStore, CodegenId};
use llvm_codegen::{Gen, dump_module};

use inkwell::context::{Context};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;

pub enum SymbolLocation {
  CBind(RefStr),
  Function(UnitId, SymbolId),
  Global(UnitId, SymbolId),
}

pub struct LlvmUnit {
  pub codegen_id : CodegenId,
  pub ee : ExecutionEngine,
  pub llvm_module : Module,
  pub globals_to_link : Vec<(GlobalValue, SymbolLocation)>,
  pub functions_to_link : Vec<(FunctionValue, SymbolLocation)>,
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

  pub fn compile_unit_group(
    &self,
    codegen_id : CodegenId,
    unit_group : &[UnitId],
    code_store : &CodeStore,
  ) -> Result<LlvmUnit, Error>
  {
    let name = code_store.name(unit_group[0]);
    let mut llvm_module = self.context.create_module(&name);

    let ee =
      llvm_module.create_jit_execution_engine(OptimizationLevel::None)
      .expect("could not create execution engine");

    let pm = PassManager::create(&llvm_module);
    if compiler::ENABLE_IR_OPTIMISATION {
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

    let mut globals_to_link = vec![];
    let mut functions_to_link = vec![];
    {
      let gen = Gen::new(
        &self.context, &mut llvm_module, &mut ee.get_target_data(),
        &mut globals_to_link, &mut functions_to_link, &pm);
      gen.codegen_module(unit_group, code_store)?
    };

    if compiler::DEBUG_PRINTING_IR {
      dump_module(&llvm_module);
    }

    let lu = LlvmUnit { codegen_id, ee, llvm_module, globals_to_link, functions_to_link };
    Ok(lu)
  }
}

fn find_symbol_address(code_store : &CodeStore, c_symbols : &CSymbols, loc : &SymbolLocation) -> usize {
  match loc {
    SymbolLocation::CBind(name) => {
      if let Some(address) = c_symbols.local_symbol_table.get(name) {
        *address
      }
      else {
        panic!("c symbol '{}' could not be found.", name)
      }
    }
    SymbolLocation::Function(unit_id, symbol_id) => {
      let def = code_store.types(*unit_id).symbols.get(&symbol_id).unwrap();
      let init = match &def.initialiser {
        SymbolInit::Function(init) => init, _ => panic!("expected function initialiser") 
      };
      let lu = code_store.llvm_unit(*unit_id);
      unsafe {
        lu.ee.get_function_address(&init.name_for_codegen)
          .expect("function pointer was null") as usize
      }
    }
    SymbolLocation::Global(unit_id, symbol_id) => {
      let def = code_store.types(*unit_id).symbols.get(&symbol_id).unwrap();
      let lu = code_store.llvm_unit(*unit_id);
      unsafe {
        lu.ee.get_global_address(&def.name)
          .expect("global pointer was null") as usize
      }
    }
  }
}

pub fn link_unit(
  codegen_id : CodegenId,
  code_store : &CodeStore,
  c_symbols : &CSymbols,
)
{
  let lu = code_store.llvm_units.get(&codegen_id).unwrap();
  // Link globals
  for (global_value, loc) in lu.globals_to_link.iter() {
    let address = find_symbol_address(code_store, c_symbols, loc);
    lu.ee.add_global_mapping(global_value, address);
  }
  // Link functions
  for (function_value, loc) in lu.functions_to_link.iter() {
    let address = find_symbol_address(code_store, c_symbols, loc);
    lu.ee.add_global_mapping(function_value, address);
  }
  // Finalize unit
  lu.ee.run_static_constructors();
}
