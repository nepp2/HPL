
use crate::types::{TypeInfo, SymbolId, Type};
use crate::codegen::{LlvmUnit};
use crate::expr::{Expr, RefStr, UIDGenerator, StringCache};
use crate::lexer;
use crate::parser;
use crate::structure;
use crate::error::Error;

use structure::{NodeId, Nodes};

use std::collections::{HashMap, VecDeque};

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

enum Job {
  Parse(SourceId, RefStr),
  Structure(UnitId),
  Typecheck(UnitId),
  Codegen,
}

struct PolyFunction {
  symbol : SymbolId,
  source_unit : UnitId,
  source_node : NodeId,
}

struct CodeStore {
  gen : UIDGenerator,
  cache : StringCache,
  code : HashMap<SourceId, RefStr>,
  exprs : HashMap<UnitId, Expr>,
  nodes : HashMap<UnitId, Nodes>,
  types : HashMap<UnitId, TypeInfo>,
  dependencies : HashMap<UnitId, Vec<UnitId>>,
  llvm : HashMap<UnitId, LlvmUnit>,
  poly_functions : HashMap<SymbolId, PolyFunction>,
  poly_variations : HashMap<UnitId, (Type, SymbolId)>,
}

impl CodeStore {

  fn process_job_queue(&mut self, job_queue : &mut VecDeque<Job>) -> Result<(), Error> {
    while let Some(job) = job_queue.pop_front() {
      match job {
        Job::Parse(id, code) => {
          self.code.insert(id, code.clone());
          let tokens =
            lexer::lex(&code, &self.cache)
            .map_err(|mut es| es.remove(0))?;
          let expr = parser::parse(tokens, &self.cache)?;
          job_queue.push_back(Job::Structure(expr));
        }
        Job::Structure(expr) => {
          let nodes = structure::to_nodes(&mut self.gen, &self.cache, &expr)?;
          job_queue.push_back(Job::Typecheck(expr, nodes));
        }
        Job::Typecheck(expr, nodes) => {
          // TODO: typecheck
        }
        _ => panic!("doesn't work"),
      }
    }
    Ok(())
  }

  pub fn load(&mut self, code : RefStr) {
    let mut job_queue = VecDeque::new();
    let id = SourceId(self.gen.next());
    job_queue.push_back(Job::Parse(id, code));
  }
}
