
use crate::{
  error, expr, c_interface, llvm_compile, types, code_store,
};
use error::Error;
use expr::{StringCache, Expr, UIDGenerator};
use c_interface::CSymbols;
use types::UnitId;
use llvm_compile::LlvmCompiler;
use code_store::CodeStore;

// TODO: Put these options somewhere more sensible
static DEBUG_PRINTING_EXPRS : bool = false;
static DEBUG_PRINTING_IR : bool = false;
static ENABLE_IR_OPTIMISATION : bool = false;

pub fn run_program(code : &str) -> Result<Val, Error> {
  let mut c = Compiler::new();
  let (_, val) = c.code_store.load_module(&c.llvm_compiler, code.into(), &mut c.gen, &c.cache, &c.c_symbols)?;
  Ok(val)
}

pub struct Compiler {
  pub code_store : CodeStore,
  pub llvm_compiler : LlvmCompiler,
  pub gen : UIDGenerator,
  pub cache : StringCache,
  pub c_symbols : CSymbols,
}

impl Compiler {
  pub fn new() -> Box<Compiler> {
    let mut gen = UIDGenerator::new();
    let cache = StringCache::new();
    let code_store  = CodeStore::new_with_intrinsics(&mut gen, &cache);
    let llvm_compiler = LlvmCompiler::new();
    let c_symbols = CSymbols::new_populated();
    let mut c = Box::new(Compiler { 
      code_store, llvm_compiler, gen, cache, c_symbols
    });
    let cptr = (&mut *c) as *mut Compiler;
    c.c_symbols.add_symbol("compiler", cptr);
    c
  }

  pub fn load_expr_as_module(&mut self, expr : &Expr)
    -> Result<(UnitId, Val), Error>
  {
    self.code_store.load_expr(&self.llvm_compiler, expr.clone(), &mut self.gen, &self.cache, &self.c_symbols)
  }

  pub fn load_module(&mut self, code : &str)
    -> Result<(UnitId, Val), Error>
  {
    self.code_store.load_module(&self.llvm_compiler, code.into(), &mut self.gen, &self.cache, &self.c_symbols)
  }
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
