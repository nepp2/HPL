
use crate::types::{TypeInfo, SymbolId, Type};
use crate::codegen::{LlvmUnit};
use crate::structure::Nodes;
use crate::expr::Expr;

use std::collections::HashMap;

/*

Modules:

- module_id
- dependencies (module id list)
- code string
- expr tree
- node tree
- type data
- llvm code

Separate maps or rows in a table?

Polymorphic functions

- function_id
- code/expr/nodes
- implementations (sig, types, code)

*/

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct UnitId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SourceId(u64);

enum CompileJob {
  Lex,
  Parse,
  Structure,
  Typecheck,
  Codegen,
}

struct CodeUnit {
  dependencies : Vec<UnitId>,
  expr : Expr,
  nodes : Nodes,
  info : TypeInfo,
  llvm : LlvmUnit,
}

struct CodeStore {
  code : HashMap<SourceId, String>,
  units : HashMap<UnitId, CodeUnit>,
  poly_functions : HashMap<SymbolId, Vec<(Type, UnitId)>>,
}
