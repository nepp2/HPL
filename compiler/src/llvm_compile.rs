
use crate::{
  error, c_interface, types, llvm_codegen, code_store, compiler, expr
};

use error::{Error, error_raw};
use c_interface::CSymbols;
use types::{UnitId, SymbolId, SymbolInit};
use code_store::CodeStore;
use llvm_codegen::{Gen, dump_module, CompileInfo };
use expr::RefStr;

use inkwell::context::{Context};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::module::Module;

// TODO: Get rid of this static mut?
static mut LOADED_SYMBOLS : bool = false;

pub enum SymbolLocation {
  CBind(RefStr),
  Function(UnitId, SymbolId),
  Global(UnitId, SymbolId),
}

pub struct LlvmUnit {
  pub unit_id : UnitId,
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

  pub fn compile_unit(
    &self,
    unit_id : UnitId,
    code_store : &CodeStore,
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
      //let type_directory
      let gen = Gen::new(
        &self.context, &mut llvm_module, &mut ee.get_target_data(),
        &mut globals_to_link, &mut functions_to_link, &pm);
      let info = CompileInfo::new(code_store, types, nodes, mapping);
      gen.codegen_module(&info)?
    };

    if compiler::DEBUG_PRINTING_IR {
      dump_module(&llvm_module);
    }

    let lu = LlvmUnit { unit_id, ee, llvm_module, globals_to_link, functions_to_link };
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
  unit_id : UnitId,
  code_store : &CodeStore,
  c_symbols : &CSymbols,
)
{
  let lu = code_store.llvm_unit(unit_id);
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

pub fn link_group(
  units : &[UnitId],
  code_store : &CodeStore,
  c_symbols : &CSymbols,
)
{
  let mut globs = vec![];
  let mut funs = vec![];
  println!("Getting all addresses");
  for &unit_id in units {
    let lu = code_store.llvm_unit(unit_id);
    // Link globals
    for (global_value, loc) in lu.globals_to_link.iter() {
      let address = find_symbol_address(code_store, c_symbols, loc);
      globs.push((lu, global_value, address));
    }
    // Link functions
    for (function_value, loc) in lu.functions_to_link.iter() {
      let address = find_symbol_address(code_store, c_symbols, loc);
      funs.push((lu, function_value, address));
    }
  }
  println!("Linking globals");
  for (lu, global_value, address) in globs {
    lu.ee.add_global_mapping(global_value, address);
  }
  println!("Linking functions");
  for (lu, function_value, address) in funs {
    lu.ee.add_global_mapping(function_value, address);
  }
  // for &unit_id in units {
  //   let lu = code_store.llvm_unit(unit_id);
  //   println!("   LINKING GLOBALS {:?}", unit_id);
  //   // Link globals
  //   for (global_value, loc) in lu.globals_to_link.iter() {
  //     println!("      LINKING GLOBAL {:?}", global_value.print_to_string());
  //     let address = find_symbol_address(code_store, c_symbols, loc);
  //     lu.ee.add_global_mapping(global_value, address);
  //   }
  //   println!("   GLOBALS ALL LINKED");
  //   println!("   LINKING FUNCTIONS {:?}", unit_id);
  //   // Link functions
  //   for (function_value, loc) in lu.functions_to_link.iter() {
  //     println!("      LINKING FUNCTION {:?}", function_value.print_to_string());
  //     let address = find_symbol_address(code_store, c_symbols, loc);
  //     lu.ee.add_global_mapping(function_value, address);
  //   }
  //   println!("   FUNCTIONS ALL LINKED");
  // }
  println!("Running static constructors");
  let aaa = (); // TODO: Why does this sometimes cause a crash?
  for &unit_id in units {
    let lu = code_store.llvm_unit(unit_id);
    lu.ee.run_static_constructors();
  }
}