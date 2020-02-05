
use crate::{
  expr, structure,
  llvm_compile, types,
  compiler,
};
use expr::{Expr, Uid, RefStr};
use types::{
  UnitId, TypeInfo, SymbolId, Type, TypeMapping,
  SymbolDefinition, TypeDefinition,
};
use llvm_compile::LlvmUnit;
use compiler::Val;
use structure::Nodes;

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SourceId(Uid);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct CodegenId(Uid);

impl From<Uid> for SourceId { fn from(v : Uid) -> Self { SourceId(v) } }

impl From<Uid> for CodegenId { fn from(v : Uid) -> Self { CodegenId(v) } }

#[derive(Default)]
pub struct CodeStore {
  pub code : HashMap<SourceId, RefStr>,
  pub names : Vec<(UnitId, RefStr)>,
  pub dependencies : HashMap<UnitId, Vec<UnitId>>,
  pub exprs : HashMap<UnitId, Expr>,
  pub nodes : HashMap<UnitId, Nodes>,
  pub types : HashMap<UnitId, TypeInfo>,
  pub type_mappings : HashMap<UnitId, TypeMapping>,
  pub codegen_mapping : HashMap<UnitId, CodegenId>,
  pub llvm_units : HashMap<CodegenId, LlvmUnit>,
  pub vals : HashMap<UnitId, Val>,

  /// Map from the id of a polymorphic symbol to its various instances,
  /// and their instanced types.
  pub poly_instances : HashMap<SymbolId, HashMap<Type, SymbolId>>,

  /// Map from unit_id of a polymorphic instance to the definition
  /// that it is an instance of.
  pub poly_parents : HashMap<UnitId, SymbolId>,
}

impl CodeStore {

  pub fn new() -> Self {
    Default::default()
  }

  pub fn name(&self, unit_id : UnitId) -> RefStr {
    if let Some(x) = self.names.iter().find(|x| x.0 == unit_id) {
      x.1.clone()
    }
    else {
      format!("module_{:?}", unit_id).into()
    }
  }

  pub fn named_unit(&self, name : &str) -> Option<UnitId> {
    self.names.iter().find(|x| x.1.as_ref() == name).map(|x| x.0)
  }

  pub fn nodes(&self, unit_id : UnitId) -> &Nodes {
    if let Some(parent_id) = self.poly_parents.get(&unit_id) {
      return self.nodes(parent_id.uid);
    }
    self.nodes.get(&unit_id).unwrap()

  }

  pub fn llvm_unit(&self, unit_id : UnitId) -> &LlvmUnit {
    let codegen_id = self.codegen_mapping.get(&unit_id).unwrap();
    self.llvm_units.get(codegen_id).unwrap()
  }  

  pub fn types(&self, unit_id : UnitId) -> &TypeInfo {
    self.types.get(&unit_id).unwrap()
  }

  pub fn symbol_def(&self, symbol_id : SymbolId) -> &SymbolDefinition {
    self.types(symbol_id.uid).symbols.get(&symbol_id).unwrap()
  }

  pub fn type_def(&self, name : &str, unit_id : UnitId) -> &TypeDefinition {
    self.types(unit_id).type_defs.get(name).unwrap()
  }

  pub fn type_mapping(&self, unit_id : UnitId) -> &TypeMapping {
    self.type_mappings.get(&unit_id).unwrap()
  }

  pub fn poly_instance(&self, poly_symbol_id : SymbolId, instance_type : &Type)
    -> Option<SymbolId>
  {
    self.poly_instances.get(&poly_symbol_id)
      .and_then(|m| m.get(instance_type)).cloned()
  }
}
