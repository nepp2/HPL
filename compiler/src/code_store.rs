
use crate::{
  error, expr, c_interface, structure,
  lexer, parser, llvm_compile, types,
  compiler, intrinsics, inference_solver,
};
use error::{Error, error, ErrorContent, error_raw};
use expr::{StringCache, Expr, UIDGenerator, RefStr};
use c_interface::CSymbols;
use types::{TypeContent, PType, UnitId, TypeInfo, SymbolId, Type, TypeMapping};
use llvm_compile::{LlvmCompiler, execute_function, LlvmUnit};
use compiler::Val;
use structure::{NodeId, Nodes, TOP_LEVEL_FUNCTION_NAME};

use std::collections::{HashMap, VecDeque};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SourceId(u64);

enum Job {
  Parse(SourceId, UnitId),
  Structure(UnitId),
  Typecheck(UnitId),
  Codegen(UnitId),
}

pub struct PolyFunction {
  symbol : SymbolId,
  source_unit : UnitId,
  source_node : NodeId,
}

#[derive(Default)]
pub struct CodeStore {
  pub code : HashMap<SourceId, RefStr>,
  pub exprs : HashMap<UnitId, Expr>,
  pub nodes : HashMap<UnitId, Nodes>,
  pub types : HashMap<UnitId, TypeInfo>,
  pub type_mappings : HashMap<UnitId, TypeMapping>,
  pub dependencies : HashMap<UnitId, Vec<UnitId>>,
  pub llvm_units : HashMap<UnitId, LlvmUnit>,
  pub vals : HashMap<UnitId, Val>,
  pub poly_functions : HashMap<SymbolId, PolyFunction>,
  pub poly_variations : HashMap<UnitId, (Type, SymbolId)>,
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
    println!("Getting types for {:?}", unit_id);
    self.types.get(&unit_id).unwrap()
  }

  pub fn type_mapping(&self, unit_id : UnitId) -> &TypeMapping {
    self.type_mappings.get(&unit_id).unwrap()
  }

  fn process_job_queue(
    &mut self,
    job_queue : &mut VecDeque<Job>,
    llvm_compiler : &LlvmCompiler,
    gen : &mut UIDGenerator, cache : &StringCache,
    c_symbols : &CSymbols,
  ) -> Result<(), Error>
  {
    while let Some(job) = job_queue.pop_front() {
      match job {
        Job::Parse(source_id, unit_id) => {
          println!("Parsing {:?}", unit_id);
          let code = self.code.get(&source_id).unwrap();
          let tokens =
            lexer::lex(&code, &cache)
            .map_err(|mut es| es.remove(0))?;
          let expr = parser::parse(tokens, cache)?;
          self.exprs.insert(unit_id, expr);
          job_queue.push_back(Job::Structure(unit_id));
        }
        Job::Structure(unit_id) => {
          println!("Structuring {:?}", unit_id);
          let expr = self.exprs.get(&unit_id).unwrap();
          let nodes = structure::to_nodes(gen, cache, &expr)?;
          self.nodes.insert(unit_id, nodes);
          job_queue.push_back(Job::Typecheck(unit_id));
        }
        Job::Typecheck(unit_id) => {
          println!("Type checking {:?}", unit_id);
          let (types, mapping) =
            inference_solver::infer_types(
              unit_id, self, cache, gen)
            .map_err(|es| {
              let c = ErrorContent::InnerErrors("type errors".into(), es);
              let nodes = self.nodes(unit_id);
              error_raw(nodes.root().loc, c)
            })?;
          self.types.insert(unit_id, types);
          self.type_mappings.insert(unit_id, mapping);
          job_queue.push_back(Job::Codegen(unit_id));
        }
        Job::Codegen(unit_id) => {
          println!("Code generating {:?}", unit_id);
          let llvm_unit = llvm_compiler.compile_unit(unit_id, self, c_symbols)?;
          self.llvm_units.insert(unit_id, llvm_unit);
          let val = self.run_top_level(unit_id)?;
          self.vals.insert(unit_id, val);
        }
      }
    }
    Ok(())
  }

  pub fn load_expr(
    &mut self,
    llvm_compiler : &LlvmCompiler,
    expr : Expr,
    gen : &mut UIDGenerator, cache : &StringCache,
    c_symbols : &CSymbols,
  ) -> Result<(UnitId, Val), Error>
  {
    let mut job_queue = VecDeque::new();
    let unit_id = gen.next().into();
    self.exprs.insert(unit_id, expr);
    job_queue.push_back(Job::Structure(unit_id));
    self.process_job_queue(&mut job_queue, llvm_compiler, gen, cache, c_symbols)?;
    let val = self.vals.get(&unit_id).unwrap().clone();
    Ok((unit_id, val))
  }

  pub fn load_module(
    &mut self,
    llvm_compiler : &LlvmCompiler,
    code : RefStr,
    gen : &mut UIDGenerator, cache : &StringCache,
    c_symbols : &CSymbols,
  ) -> Result<(UnitId, Val), Error>
  {
    let mut job_queue = VecDeque::new();
    let source_id = SourceId(gen.next());
    self.code.insert(source_id, code);
    let unit_id = gen.next().into();
    job_queue.push_back(Job::Parse(source_id, unit_id));
    self.process_job_queue(&mut job_queue, llvm_compiler, gen, cache, c_symbols)?;
    let val = self.vals.get(&unit_id).unwrap().clone();
    Ok((unit_id, val))
  }
  
  fn run_top_level(&self, unit_id : UnitId) -> Result<Val, Error> {
    use TypeContent::*;
    use PType::*;
    let f = TOP_LEVEL_FUNCTION_NAME;
    let types = self.types(unit_id);
    let def = types.symbols.values().find(|def| def.name.as_ref() == f).unwrap();
    let f = def.codegen_name().unwrap();
    let sig = if let Some(sig) = def.type_tag.sig() {sig} else {panic!()};
    let lu = self.llvm_unit(unit_id);
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
        return error(def.loc, format!("can't return value of type {:?} from a top-level function", t));
      }
    };
    Ok(value)
  }
}
