
use crate::types::{TypeInfo, ModuleId, TypeMapping};
use crate::codegen::LlvmUnit;
use crate::structure::Nodes;

pub struct TypedModule {
  pub id : ModuleId,
  pub nodes : Nodes,
  pub t : TypeInfo,
  pub cg : TypeMapping,
}

impl TypedModule {
  pub fn new(
    id : ModuleId,
    nodes : Nodes,
    t : TypeInfo,
    cg : TypeMapping,
  ) -> Self 
  {
    TypedModule { id, nodes, t, cg }
  }

  pub fn to_compiled(self, llvm_unit : LlvmUnit) -> CompiledModule {
    CompiledModule {
      id: self.id,
      nodes: self.nodes,
      t: self.t,
      llvm_unit,
    }
  }
}

pub struct CompiledModule {
  pub id : ModuleId,
  pub nodes : Nodes,
  pub t : TypeInfo,
  pub llvm_unit : LlvmUnit,
}
