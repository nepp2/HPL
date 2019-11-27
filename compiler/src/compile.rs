
use crate::error::{
  Error, ErrorContent, error, error_raw, TextLocation};
use crate::expr::{StringCache, Expr, UIDGenerator};
use crate::lexer;
use crate::parser;
use crate::c_interface::CSymbols;
use crate::structure;
use crate::structure::{Val, TOP_LEVEL_FUNCTION_NAME};
use crate::inference;
use crate::inference::CodegenInfo;
use crate::types::{
  Type, PType, TypeInfo, FunctionImplementation, ModuleId,
  FunctionSignature, FunctionDefinition, GenericId };
use crate::codegen2::{Gen, LlvmUnit, dump_module, CompileInfo};
use crate::modules::{ CompiledModule, TypedModule };
use crate::arena::{ Arena };

use inkwell::context::{Context};
use inkwell::passes::PassManager;
use inkwell::values::{FunctionValue, GlobalValue};
use inkwell::OptimizationLevel;
use inkwell::execution_engine::ExecutionEngine;
use inkwell::targets::{InitializationConfig, Target };

use llvm_sys::support::LLVMLoadLibraryPermanently;

// TODO: Get rid of this static mut?
static mut LOADED_SYMBOLS : bool = false;

// TODO: Put these options somewhere more sensible
static DEBUG_PRINTING_EXPRS : bool = true;
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
  let m = c.compile_module(&[], &expr, false)?;
  run_top_level(&m)
}

pub struct Compiler {
  pub context : Context,
  pub gen : UIDGenerator,
  pub cache : StringCache,
  pub c_symbols : CSymbols,
  pub intrinsics : TypedModule,
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
    let mut gen = UIDGenerator::new();
    let cache = StringCache::new();
    let mut c_symbols = CSymbols::new();
    c_symbols.populate();

    let intrinsics = get_intrinsics(&mut gen, &cache);
  
    let mut c = Box::new(Compiler { context, gen, cache, c_symbols, intrinsics });
    let cptr = (&mut *c) as *mut Compiler;
    c.c_symbols.add_symbol("compiler", cptr);
    c
  }

  pub fn parse(&self, code : &str) -> Result<Expr, Error> {
    parse(&self.cache, code)
  }

  pub fn load_module<'a>(&mut self, imports : &[&CompiledModule], expr : &Expr)
    -> Result<(CompiledModule, Val), Error>
  {
    let m = self.compile_module(imports, &expr, false)?;
    let val = run_top_level(&m)?;
    Ok((m, val))
  }

  pub fn interpret_expression<'a>(&mut self, imports : &[&CompiledModule], expr : &Expr)
    -> Result<(CompiledModule, Val), Error>
  {
    let m = self.compile_module(imports, &expr, true)?;
    let val = run_top_level(&m)?;
    Ok((m, val))
  }

  fn compile_module(&mut self, imports : &[&CompiledModule], expr : &Expr, repl_enabled : bool)
    -> Result<CompiledModule, Error>
  {
    if DEBUG_PRINTING_EXPRS {
      println!("{}", expr);
    }
    let nodes = structure::to_nodes(&mut self.gen, &self.cache, &expr, repl_enabled)?;

    let mut import_types = vec![&self.intrinsics.t];
    import_types.extend(imports.iter().map(|m| &m.t));

    let typed_module =
      inference::infer_types(nodes, import_types.as_slice(), &mut self.gen)
      .map_err(|es| error_raw(expr,
        ErrorContent::InnerErrors("type errors".into(), es)))?;

    let module_name = format!("{:?}", typed_module.id);
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
      //let type_directory
      let gen = Gen::new(
          &mut self.context, &mut llvm_module, &mut ee.get_target_data(),
          &self.c_symbols.local_symbol_table, &mut globals_to_link, &mut functions_to_link, &pm);
      
      let info = CompileInfo::new(imports, &typed_module.t, &typed_module.nodes, &typed_module.cg);
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

    let lu = LlvmUnit { module_id: typed_module.id, ee, llvm_module };
    Ok(typed_module.to_compiled(lu))
  }
}

fn parse(cache : &StringCache, code : &str) -> Result<Expr, Error> {
  let tokens =
    lexer::lex(&code, &cache)
    .map_err(|mut es| es.remove(0))?;

  parser::parse(tokens, &cache)
}

fn get_intrinsics(gen : &mut UIDGenerator, cache : &StringCache) -> TypedModule {
  use Type::*;
  use PType::*;

  fn add_intrinsic(
    arena : &Arena, gen : &mut UIDGenerator,
    id : ModuleId, t : &mut TypeInfo, name : &str,
    args : &[Type], return_type : Type)
  {
    add_generic_intrinsic(arena, gen, id, t, name, args, return_type, vec![])
  }
  
  fn add_generic_intrinsic(
    arena : &Arena, gen : &mut UIDGenerator,
    id : ModuleId, t : &mut TypeInfo, name : &str,
    args : &[Type], return_type : Type,
    generics : Vec<GenericId>)
  {
    let sig = FunctionSignature{
      return_type,
      args: arena.alloc_slice(args),
    };
    let f = FunctionDefinition {
      id: gen.next().into(),
      module_id: id,
      name_in_code: arena.alloc_str(name),
      signature: arena.alloc(sig),
      generics,
      implementation: FunctionImplementation::Intrinsic,
      loc: TextLocation::zero(),
    };
    t.functions.push(arena.alloc(f));
  }

  let expr = parse(cache, "").unwrap();
  let nodes = structure::to_nodes(gen, cache, &expr, false).unwrap();

  let arena = Arena::new();
  let id = gen.next().into();
  let mut ti = TypeInfo::new(id);
  let prim_number_types =
    &[Prim(I64), Prim(I32), Prim(F32), Prim(F64),
      Prim(U64), Prim(U32), Prim(U16), Prim(U8) ];
  for &t in prim_number_types {
    for &n in &["-"] {
      add_intrinsic(&arena, gen, id, &mut ti, n, &[t], t);
    }
    for &n in &["+", "-", "*", "/"] {
      add_intrinsic(&arena, gen, id, &mut ti, n, &[t, t], t);
    }
    for &n in &["==", ">", "<", ">=", "<=", "!="] {
      add_intrinsic(&arena, gen, id, &mut ti, n, &[t, t], Prim(Bool));
    }
  }
  for &n in &["&&", "||"] {
    add_intrinsic(&arena, gen, id, &mut ti, n, &[Prim(Bool), Prim(Bool)], Prim(Bool));
  }
  {
    let gid = gen.next().into();
    let gt = Type::Generic(gid);
    let gptr = Type::Ptr(arena.alloc(gt));
    add_generic_intrinsic(&arena, gen, id, &mut ti, "Index", &[gptr], gt, vec![gid]);
  }
  {
    let gid = gen.next().into();
    let gt = Type::Generic(gid);
    let gptr = Type::Ptr(arena.alloc(gt));
    add_generic_intrinsic(&arena, gen, id, &mut ti, "*", &[gptr], gt, vec![gid]);
  }
  {
    let gid = gen.next().into();
    let gt = Type::Generic(gid);
    let gptr = Type::Ptr(arena.alloc(gt));
    add_generic_intrinsic(&arena, gen, id, &mut ti, "&", &[gt], gptr, vec![gid]);
  }
  TypedModule::new(arena, id, nodes, ti, CodegenInfo::new())
}

fn run_top_level(m : &CompiledModule) -> Result<Val, Error> {
  let f = TOP_LEVEL_FUNCTION_NAME;
  let def = m.t.functions.iter().find(|def| def.name_in_code.as_ref() == f).unwrap();
  let f = if let FunctionImplementation::Normal{ name_for_codegen, .. } = &def.implementation {
    name_for_codegen.as_ref()
  }
  else {
    f
  };
  use Type::*;
  use PType::*;
  let sig = def.signature;
  let lu = &m.llvm_unit;
  let value = match sig.return_type {
    Prim(Bool) => Val::Bool(execute::<bool>(f, &lu.ee)),
    Prim(F64) => Val::F64(execute::<f64>(f, &lu.ee)),
    Prim(F32) => Val::F32(execute::<f32>(f, &lu.ee)),
    Prim(I64) => Val::I64(execute::<i64>(f, &lu.ee)),
    Prim(I32) => Val::I32(execute::<i32>(f, &lu.ee)),
    Prim(U64) => Val::U64(execute::<u64>(f, &lu.ee)),
    Prim(U32) => Val::U32(execute::<u32>(f, &lu.ee)),
    Prim(U16) => Val::U16(execute::<u16>(f, &lu.ee)),
    Prim(U8) => Val::U8(execute::<u8>(f, &lu.ee)),
    Prim(Void) => {
      execute::<()>(f, &lu.ee);
      Val::Void
    }
    t => {
      return error(def.loc, format!("can't return value of type {:?} from a top-level function", t));
    }
  };
  Ok(value)
}
