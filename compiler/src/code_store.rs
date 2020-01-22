
use crate::{
  expr, structure,
  llvm_compile, types,
  compiler, intrinsics,
};
use expr::{StringCache, Expr, UIDGenerator, RefStr};
use types::{UnitId, TypeInfo, SymbolId, Type, TypeMapping};
use llvm_compile::LlvmUnit;
use compiler::Val;
use structure::Nodes;

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SourceId(u64);

impl From<u64> for SourceId { fn from(v : u64) -> Self { SourceId(v) } }

pub struct PolyFunction {
  pub source_unit : UnitId,
  pub instances : HashMap<Type, (UnitId, SymbolId)>,
}

#[derive(Default)]
pub struct CodeStore {
  pub code : HashMap<SourceId, RefStr>,
  pub exprs : HashMap<UnitId, Expr>,
  pub nodes : HashMap<UnitId, Nodes>,
  pub types : HashMap<UnitId, TypeInfo>,
  pub type_mappings : HashMap<UnitId, TypeMapping>,
  pub subunit_parent : HashMap<UnitId, UnitId>,
  pub llvm_units : HashMap<UnitId, LlvmUnit>,
  pub vals : HashMap<UnitId, Val>,
  pub poly_functions : HashMap<SymbolId, PolyFunction>,
}

impl CodeStore {

  pub fn new_with_intrinsics(gen : &mut UIDGenerator, cache : &StringCache) -> Self {
    let mut cs : Self = Default::default();
    let i_types = intrinsics::get_intrinsics(gen, cache);
    cs.types.insert(i_types.unit_id, i_types);
    cs
  }

  pub fn name(&self, unit_id : UnitId) -> RefStr {
    let aaa = (); // TODO store names based on files (or something)
    format!("module_{:?}", unit_id).into()
  }

  pub fn nodes(&self, unit_id : UnitId) -> &Nodes {
    self.nodes.get(&unit_id).unwrap()
  }

  pub fn llvm_unit(&self, unit_id : UnitId) -> &LlvmUnit {
    self.llvm_units.get(&unit_id).unwrap()
  }  

  pub fn types(&self, unit_id : UnitId) -> &TypeInfo {
    self.types.get(&unit_id).unwrap()
  }

  pub fn type_mapping(&self, unit_id : UnitId) -> &TypeMapping {
    self.type_mappings.get(&unit_id).unwrap()
  }
}
