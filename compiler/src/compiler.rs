
use crate::error::{
  Error, ErrorContent, error, error_raw, TextLocation};
use crate::expr::{StringCache, Expr, UIDGenerator};
use crate::lexer;
use crate::parser;
use crate::c_interface::CSymbols;
use crate::structure;
use crate::structure::TOP_LEVEL_FUNCTION_NAME;
use crate::inference_solver;
use crate::types::{
  Type, TypeContent, PType, TypeInfo,
  UnitId, SignatureBuilder, SymbolDefinition,
  PolyTypeId, SymbolInit, TypeMapping,
};
use crate::llvm_codegen::{Gen, LlvmUnit, dump_module, CompileInfo };
use crate::modules::{ CompiledModule, TypedModule };

use std::collections::HashMap;

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
  let (_, val) = c.load_module(&[], &expr)?;
  Ok(val)
}

pub struct Compiler {
  pub context : Context,
  pub gen : UIDGenerator,
  pub cache : StringCache,
  pub c_symbols : CSymbols,
  pub intrinsics : TypedModule,
  pub compiled_modules : HashMap<UnitId, CompiledModule>,
}

impl Compiler {
  pub fn new() -> Box<Compiler> {
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
    let mut gen = UIDGenerator::new();
    let cache = StringCache::new();
    let mut c_symbols = CSymbols::new();
    c_symbols.populate();

    let intrinsics = get_intrinsics(&mut gen, &cache);
  
    let mut c = Box::new(Compiler { 
      context, gen, cache, c_symbols, intrinsics,
      compiled_modules: HashMap::new(),
    });
    let cptr = (&mut *c) as *mut Compiler;
    c.c_symbols.add_symbol("compiler", cptr);
    c
  }

  pub fn parse(&self, code : &str) -> Result<Expr, Error> {
    parse(&self.cache, code)
  }

  pub fn load_module(&mut self, imports : &[UnitId], expr : &Expr)
    -> Result<(UnitId, Val), Error>
  {
    let id = self.compile_module(imports, &expr)?;
    let val = run_top_level(self.compiled_modules.get(&id).unwrap())?;
    Ok((id, val))
  }

  fn compile_module(&mut self, import_ids : &[UnitId], expr : &Expr)
    -> Result<UnitId, Error>
  {
    if DEBUG_PRINTING_EXPRS {
      println!("{}", expr);
    }
    let nodes = structure::to_nodes(&mut self.gen, &self.cache, &expr)?;

    let mut imports = Vec::with_capacity(import_ids.len());
    for id in import_ids.iter() {
      imports.push(self.compiled_modules.get(id).unwrap());
    }

    let mut import_types = vec![&self.intrinsics.t];
    import_types.extend(imports.iter().map(|m| &m.t));

    let typed_module =
      inference_solver::infer_types(nodes, import_types.as_slice(), &self.cache, &mut self.gen)
      .map_err(|es| error_raw(expr, ErrorContent::InnerErrors("type errors".into(), es)))?;

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
        &self.c_symbols.local_symbol_table, &mut globals_to_link,
        &mut functions_to_link, &pm);
      let info = CompileInfo::new(
        imports.as_slice(), &typed_module.t, &typed_module.nodes, &typed_module.cg);
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

    let lu = LlvmUnit { unit_id: typed_module.id, ee, llvm_module };
    let cm = typed_module.to_compiled(lu);
    let unit_id = cm.id;
    self.compiled_modules.insert(unit_id, cm);
    Ok(unit_id)
  }
}

fn parse(cache : &StringCache, code : &str) -> Result<Expr, Error> {
  let tokens =
    lexer::lex(&code, &cache)
    .map_err(|mut es| es.remove(0))?;

  parser::parse(tokens, &cache)
}

fn get_intrinsics(gen : &mut UIDGenerator, cache : &StringCache) -> TypedModule {
  use PType::*;

  fn create_definition(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, name : &str,
    args : &[&Type], return_type : &Type, polymorphic : bool)
      -> SymbolDefinition
  {
    let mut sig = SignatureBuilder::new(return_type.clone());
    for &a in args {
      sig.append_arg(a.clone());
    }
    SymbolDefinition {
      id: gen.next().into(), unit_id,
      name: cache.get(name),
      type_tag: sig.into(),
      initialiser: SymbolInit::Intrinsic,
      polymorphic,
      loc: TextLocation::zero(),
    }
  }

  fn add_intrinsic(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
    name : &str, args : &[&Type], return_type : &Type)
  {
    let g = create_definition(cache, gen, unit_id, name, args, return_type, false);
    t.symbols.insert(g.id, g);
  }
  
  fn add_polymorphic_intrinsic(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
    name : &str, args : &[&Type], return_type : &Type)
  {
    let g = create_definition(cache, gen, unit_id, name, args, return_type, true);
    t.symbols.insert(g.id, g);
  }

  let expr = parse(cache, "").unwrap();
  let nodes = structure::to_nodes(gen, cache, &expr).unwrap();

  let unit_id = gen.next().into();
  let mut ti = TypeInfo::new(unit_id);
  let prim_number_types : &[Type] =
    &[I64.into(), I32.into(), F32.into(), F64.into(),
      U64.into(), U32.into(), U16.into(), U8.into() ];
  let boolean : &Type = &Bool.into();
  for t in prim_number_types {
    add_intrinsic(cache, gen, unit_id, &mut ti, "-", &[t], t);
    for &n in &["+", "-", "*", "/"] {
      add_intrinsic(cache, gen, unit_id, &mut ti, n, &[t, t], t);
    }
    for &n in &["==", ">", "<", ">=", "<=", "!="] {
      add_intrinsic(cache, gen, unit_id, &mut ti, n, &[t, t], boolean);
    }
  }
  for &n in &["&&", "||"] {
    add_intrinsic(cache, gen, unit_id, &mut ti, n, &[boolean, boolean], boolean);
  }
  add_intrinsic(cache, gen, unit_id, &mut ti, "!", &[boolean], boolean);

  for prim in &[I64.into(), I32.into(), U64.into(), U32.into()] {
    for container in &[Type::ptr_to, Type::array_of] {
      let gid : PolyTypeId = gen.next().into();
      let gt : Type = gid.into();
      let gcontainer = container(gt.clone());
      let args = &[&gcontainer, prim];
      add_polymorphic_intrinsic(cache, gen, unit_id, &mut ti, "Index", args, &gt);
    }
  }
  {
    let gid : PolyTypeId = gen.next().into();
    let gt : Type = gid.into();
    let gptr = Type::ptr_to(gt.clone());
    add_polymorphic_intrinsic(cache, gen, unit_id, &mut ti, "*", &[&gptr], &gt);
  }
  {
    let gid : PolyTypeId = gen.next().into();
    let gt : Type = gid.into();
    let gptr = Type::ptr_to(gt.clone());
    add_polymorphic_intrinsic(cache, gen, unit_id, &mut ti, "&", &[&gt], &gptr);
  }
  TypedModule::new(unit_id, nodes, ti, TypeMapping::new())
}

#[derive(Clone, PartialEq, Debug)]
pub enum Val {
  Void,
  F64(f64),
  F32(f32),
  I64(i64),
  U64(u64),
  I32(i32),
  U32(u32),
  U16(u16),
  U8(u8),
  String(String),
  Bool(bool),
}

fn run_top_level(m : &CompiledModule) -> Result<Val, Error> {
  use TypeContent::*;
  use PType::*;
  let f = TOP_LEVEL_FUNCTION_NAME;
  let def = m.t.symbols.values().find(|def| def.name.as_ref() == f).unwrap();
  let f = def.codegen_name().unwrap();
  let sig = if let Some(sig) = def.type_tag.sig() {sig} else {panic!()};
  let lu = &m.llvm_unit;
  let value = match &sig.return_type.content {
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
