
use crate::{
  common, expr, structure,
  llvm_compile, types,
  compiler,
};
use common::*;
use expr::Expr;
use types::{
  TypeInfo, SymbolId, Type, TypeMapping,
  SymbolDefinition, TypeDefinition,
};
use llvm_compile::LlvmUnit;
use compiler::Val;
use structure::Nodes;

use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct CodegenId(Uid);

impl From<Uid> for CodegenId { fn from(v : Uid) -> Self { CodegenId(v) } }

#[derive(Default)]
pub struct CodeStore {
  pub code : HashMap<UnitId, RefStr>,
  pub names : HashMap<UnitId, RefStr>,
  pub dependencies : HashMap<UnitId, HashSet<UnitId>>,
  pub exprs : HashMap<UnitId, Expr>,
  pub nodes : HashMap<UnitId, Nodes>,
  pub types : HashMap<UnitId, TypeInfo>,
  pub type_mappings : HashMap<UnitId, TypeMapping>,
  pub codegen_mapping : HashMap<UnitId, CodegenId>,
  pub llvm_units : HashMap<CodegenId, LlvmUnit>,
  pub vals : HashMap<UnitId, Val>,
  pub tombstones : HashSet<UnitId>,

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

  pub fn create_unit(&mut self, uid : Uid, name : Option<RefStr>) -> UnitId {
    let id = create_unit(uid);
    let name =  name.unwrap_or_else(|| format!("unit_{:?}", uid).into());
    if self.named_unit(&name).is_some() {
      panic!("tried to load two modules called '{}'", name);
    }
    self.names.insert(id, name);
    id
  }

  pub fn remove_unit(&mut self, uid : UnitId) {
    let aaa = (); // TODO: remove the source. I'm not sure if the source ID is stored anywhere yet. It's supposed to be stored in TextLocations.
    self.names.remove(&uid);
    self.exprs.remove(&uid);
    self.nodes.remove(&uid);
    self.types.remove(&uid);
    self.type_mappings.remove(&uid);
    if let Some(codegen_id) = self.codegen_mapping.remove(&uid) {
      let aaa = (); // TODO: I'm not convinced that this is sufficient to clean up the llvm module & its jitted binary code
      self.llvm_units.remove(&codegen_id);
    }
    self.vals.remove(&uid);
    if let Some(sid) = self.poly_parents.remove(&uid) {
      let map = self.poly_instances.get_mut(&sid).unwrap();
      map.retain(|_, sid| sid.uid != uid);
    }
  }

  pub fn name(&self, unit_id : UnitId) -> RefStr {
    self.names.get(&unit_id).unwrap().clone()
  }

  pub fn named_unit(&self, name : &str) -> Option<UnitId> {
    self.names.iter().find(|x| x.1.as_ref() == name).map(|x| *x.0)
  }

  pub fn nodes(&self, unit_id : UnitId) -> &Nodes {
    if let Some(parent_id) = self.poly_parents.get(&unit_id) {
      return self.nodes(parent_id.uid);
    }
    self.nodes.get(&unit_id).unwrap()

  }

  pub fn add_dependency(&mut self, unit : UnitId, depends_on : UnitId) {
    self.dependencies.entry(unit).or_default().insert(depends_on);
  }

  pub fn llvm_unit(&self, unit_id : UnitId) -> &LlvmUnit {
    let codegen_id = self.codegen_mapping.get(&unit_id).unwrap();
    self.llvm_units.get(codegen_id).unwrap()
  }

  pub fn types(&self, unit_id : UnitId) -> &TypeInfo {
    self.types.get(&unit_id).unwrap()
  }

  pub fn dependencies(&self, unit_id : UnitId) -> &HashSet<UnitId> {
    self.dependencies.get(&unit_id).unwrap()
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