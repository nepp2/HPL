
use crate::types::{TypeInfo, SymbolId, Type, TypeMapping, UnitId};
use crate::llvm_codegen::LlvmUnit;
use crate::llvm_compile::LlvmCompiler;
use crate::expr::{Expr, RefStr, UIDGenerator, StringCache};
use crate::{lexer, parser, structure, inference_solver, intrinsics};
use crate::error::{Error, ErrorContent, error_raw};

use structure::{NodeId, Nodes};

use std::collections::{HashMap, VecDeque};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SourceId(u64);

enum Job {
  Parse(SourceId, UnitId, RefStr),
  Structure(UnitId),
  Typecheck(UnitId),
  Codegen(UnitId),
}

struct PolyFunction {
  symbol : SymbolId,
  source_unit : UnitId,
  source_node : NodeId,
}

#[derive(Default)]
pub struct CodeStore {
  code : HashMap<SourceId, RefStr>,
  exprs : HashMap<UnitId, Expr>,
  nodes : HashMap<UnitId, Nodes>,
  types : HashMap<UnitId, TypeInfo>,
  type_mappings : HashMap<UnitId, TypeMapping>,
  dependencies : HashMap<UnitId, Vec<UnitId>>,
  llvm : HashMap<UnitId, LlvmUnit>,
  poly_functions : HashMap<SymbolId, PolyFunction>,
  poly_variations : HashMap<UnitId, (Type, SymbolId)>,
}

impl CodeStore {

  pub fn new_with_intrinsics(gen : &mut UIDGenerator, cache : &StringCache) -> Self {
    let mut cs : Self = Default::default();
    let i_types = intrinsics::get_intrinsics(gen, cache);
    let unit_id = gen.next().into();
    cs.types.insert(unit_id, i_types);
    cs
  }

  pub fn name(&self, unit_id : UnitId) -> &str {
    panic!()
  }

  pub fn nodes(&self, unit_id : UnitId) -> &Nodes {
    panic!()
  }  

  pub fn types(&self, unit_id : UnitId) -> &TypeInfo {
    panic!()
  }

  pub fn type_mapping(&self, unit_id : UnitId) -> &TypeMapping {
    panic!()
  }

  fn process_job_queue(
    &mut self,
    job_queue : &mut VecDeque<Job>,
    llvm_compiler : &LlvmCompiler,
    gen : &mut UIDGenerator, cache : &StringCache,
  ) -> Result<(), Error>
  {
    while let Some(job) = job_queue.pop_front() {
      match job {
        Job::Parse(id, unit_id, code) => {
          self.code.insert(id, code.clone());
          let tokens =
            lexer::lex(&code, &cache)
            .map_err(|mut es| es.remove(0))?;
          let expr = parser::parse(tokens, cache)?;
          self.exprs.insert(unit_id, expr);
          job_queue.push_back(Job::Structure(unit_id));
        }
        Job::Structure(unit_id) => {
          let expr = self.exprs.get(&unit_id).unwrap();
          let nodes = structure::to_nodes(gen, cache, &expr)?;
          self.nodes.insert(unit_id, nodes);
          job_queue.push_back(Job::Typecheck(unit_id));
        }
        Job::Typecheck(unit_id) => {
          // TODO: typecheck
          let nodes = self.nodes.get(&unit_id).unwrap();
          let import_types : Vec<_> = self.types.values().collect();
          let (types, mapping) =
            inference_solver::infer_types2(
              nodes, import_types.as_slice(), cache, gen)
            .map_err(|es| {
              let c = ErrorContent::InnerErrors("type errors".into(), es);
              let root = nodes.node(nodes.root);
              error_raw(root.loc, c)
            })?;
          self.types.insert(unit_id, types);
          self.type_mappings.insert(unit_id, mapping);
        }
        Job::Codegen(unit_id) => {
          let llvm_unit = llvm_compiler.compile_unit(unit_id, self, gen, cache)?;
          // TODO: CALL INITIALISER FUNCTIO AND ADD LLVM UNIT TO SELF
        }
      }
    }
    Ok(())
  }

  pub fn load(
    &mut self,
    llvm_compiler : &LlvmCompiler,
    code : RefStr,
    gen : &mut UIDGenerator, cache : &StringCache
  ) -> Result<UnitId, Error>
  {
    let mut job_queue = VecDeque::new();
    let source_id = SourceId(gen.next());
    let unit_id = gen.next().into();
    job_queue.push_back(Job::Parse(source_id, unit_id, code));
    self.process_job_queue(&mut job_queue, llvm_compiler, gen, cache)?;
    Ok(unit_id)
  }
}
