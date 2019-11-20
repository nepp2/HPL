
use crate::types::{TypeInfo, ModuleId};
use crate::codegen2::LlvmUnit;
use crate::inference::CodegenInfo;
use crate::arena::Arena;
use crate::structure::Nodes;

pub struct TypedModule {
  arena : Arena,
  pub id : ModuleId,
  pub nodes : Nodes,
  pub t : TypeInfo,
  pub cg : CodegenInfo,
}

impl TypedModule {
  pub fn new(
    arena : Arena,
    id : ModuleId,
    nodes : Nodes,
    t : TypeInfo,
    cg : CodegenInfo,
  ) -> Self 
  {
    TypedModule { arena, id, nodes, t, cg }
  }

  pub fn to_compiled(self, llvm_unit : LlvmUnit) -> CompiledModule {
    CompiledModule {
      arena: self.arena,
      id: self.id,
      nodes: self.nodes,
      t: self.t,
      llvm_unit,
    }
  }
}

pub struct CompiledModule {
  arena : Arena,
  pub id : ModuleId,
  pub nodes : Nodes,
  pub t : TypeInfo,
  pub llvm_unit : LlvmUnit,
}
