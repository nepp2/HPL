
use crate::{
  error, expr, c_interface, llvm_compile, types, code_store,
  structure, lexer, parser, inference_solver
};
use expr::{StringCache, Expr, UIDGenerator};
use c_interface::CSymbols;
use code_store::{CodeStore, SourceId, PolyFunction};
use types::{TypeContent, PType, UnitId};
use llvm_compile::{LlvmCompiler, execute_function};
use error::{Error, error, ErrorContent, error_raw};
use structure::TOP_LEVEL_FUNCTION_NAME;

use std::collections::HashMap;

// TODO: Put these options somewhere more sensible
pub static DEBUG_PRINTING_EXPRS : bool = false;
pub static DEBUG_PRINTING_IR : bool = false;
pub static ENABLE_IR_OPTIMISATION : bool = false;

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
    let unit_id = self.gen.next().into();
    self.code_store.exprs.insert(unit_id, expr.clone());
    self.load_module_from_expr_internal(unit_id)?;
    let val = self.code_store.vals.get(&unit_id).unwrap().clone();
    Ok((unit_id, val))
  }

  pub fn load_module(&mut self, code : &str)
    -> Result<(UnitId, Val), Error>
  {
    let source_id = self.gen.next().into();
    self.code_store.code.insert(source_id, code.into());
    let unit_id = self.gen.next().into();
    self.parse(source_id, unit_id)?;
    self.load_module_from_expr_internal(unit_id)?;
    let val = self.code_store.vals.get(&unit_id).unwrap().clone();
    Ok((unit_id, val))
  }

  fn parse(&mut self, source_id : SourceId, unit_id : UnitId) -> Result<(), Error> {
    let code = self.code_store.code.get(&source_id).unwrap();
    let tokens =
      lexer::lex(&code, &self.cache)
      .map_err(|mut es| es.remove(0))?;
    let expr = parser::parse(tokens, &self.cache)?;
    self.code_store.exprs.insert(unit_id, expr);
    Ok(())
  }

  fn load_module_from_expr_internal(&mut self, unit_id : UnitId) -> Result<(), Error> {
    self.structure(unit_id)?;
    self.typecheck(unit_id)?;
    let mapping = self.code_store.type_mapping(unit_id);
    for (unit_id, symbol_id, type_tag) in mapping.polymorphic_references.iter() {
      if let Some(pf) = self.code_store.poly_functions.get(symbol_id) {
        if !pf.instances.contains_key(type_tag) {
          // Do something here to create a new instance and typecheck it
        }
      }
    }

    self.codegen(unit_id, &[])?;
    self.initialise(unit_id)?;
    Ok(())
  }

  fn structure(&mut self, unit_id : UnitId) -> Result<(), Error> {
    let expr = self.code_store.exprs.get(&unit_id).unwrap();
    let nodes = structure::to_nodes(&mut self.gen, &self.cache, &expr)?;
    self.code_store.nodes.insert(unit_id, nodes);
    Ok(())
  }

  fn typecheck(&mut self, unit_id : UnitId) -> Result<(), Error> {
    let (types, mapping) =
      inference_solver::infer_types(
        unit_id, &self.code_store, &self.cache, &mut self.gen)
      .map_err(|es| {
        let c = ErrorContent::InnerErrors("type errors".into(), es);
        let nodes = self.code_store.nodes(unit_id);
        error_raw(nodes.root().loc, c)
      })?;
    for def in types.symbols.values() {
      if def.polymorphic {
        let pf = PolyFunction {
          source_unit: def.unit_id,
          source_node: *mapping.symbol_def_nodes.get(&def.id).unwrap(),
          instances: HashMap::new(),
        };
        self.code_store.poly_functions.insert(def.id, pf);
      }
    }
    self.code_store.types.insert(unit_id, types);
    self.code_store.type_mappings.insert(unit_id, mapping);
    Ok(())
  }

  fn codegen(&mut self, unit_id : UnitId, subunits : &[UnitId]) -> Result<(), Error> {
    let llvm_unit = self.llvm_compiler.compile_unit(unit_id, subunits, &self.code_store, &self.c_symbols)?;
    self.code_store.llvm_units.insert(unit_id, llvm_unit);
    for &subunit_id in subunits {
      self.code_store.subunit_parent.insert(subunit_id, unit_id);
    }
    Ok(())
  }

  fn initialise(&mut self, unit_id : UnitId) -> Result<(), Error> {
    let val = self.run_top_level(unit_id)?;
    self.code_store.vals.insert(unit_id, val);
    Ok(())
  }

  fn run_top_level(&self, unit_id : UnitId) -> Result<Val, Error> {
    use TypeContent::*;
    use PType::*;
    let f = TOP_LEVEL_FUNCTION_NAME;
    let types = self.code_store.types(unit_id);
    let def = types.symbols.values().find(|def| def.name.as_ref() == f).unwrap();
    let f = def.codegen_name().unwrap();
    let sig = if let Some(sig) = def.type_tag.sig() {sig} else {panic!()};
    let lu = self.code_store.llvm_unit(unit_id);
    let value = match &sig.return_type.content {
      Prim(Bool) => Val::Bool(execute_function(f, lu)),
      Prim(F64) => Val::F64(execute_function(f, lu)),
      Prim(F32) => Val::F32(execute_function(f, lu)),
      Prim(I64) => Val::I64(execute_function(f, lu)),
      Prim(I32) => Val::I32(execute_function(f, lu)),
      Prim(U64) => Val::U64(execute_function(f, lu)),
      Prim(U32) => Val::U32(execute_function(f, lu)),
      Prim(U16) => Val::U16(execute_function(f, lu)),
      Prim(U8) => Val::U8(execute_function(f, lu)),
      Prim(Void) => {
        execute_function::<()>(f, lu);
        Val::Void
      }
      t => {
        let loc = self.code_store.nodes(unit_id).root().loc;
        return error(loc, format!("can't return value of type {:?} from a top-level function", t));
      }
    };
    Ok(value)
  }

}

pub fn run_program(code : &str) -> Result<Val, Error> {
  let mut c = Compiler::new();
  let (_, val) = c.load_module(code)?;
  Ok(val)
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
