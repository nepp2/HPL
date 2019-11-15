
use std::fmt;
use itertools::Itertools;
use std::hash::Hash;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, UIDGenerator};
use crate::structure::{
  Node, NodeId, Nodes, Symbol, SymbolId, Content,
  Val, LabelId, TypeKind, FunctionNode, VarScope
};

use std::collections::HashMap;
use bimap::BiMap;

pub fn infer_types(
  parent_module : &ModuleInfo,
  gen : &mut UIDGenerator, cache : &StringCache,
  code : &str, nodes : &Nodes)
    -> Result<(ModuleInfo, CodegenInfo), Vec<Error>>
{
  let mut c = Constraints::new();
  let mut module = parent_module.child(gen);
  let mut cg = CodegenInfo::new();
  let mut errors = vec![];
  let core = CoreTypes::new(&mut module.types, gen, cache);
  let mut gather = GatherConstraints::new(
    &core, &mut module, &mut cg, gen, cache, &mut c, &mut errors);
  gather.gather_constraints(nodes);
  let mut i = Inference::new(code, nodes, &mut module, &mut cg, &c, gen, cache, &mut errors);
  i.infer();
  if errors.len() > 0 {
    Err(errors)
  }
  else {
    Ok((module, cg))
  }
}

pub fn base_module(gen : &mut UIDGenerator, cache : &StringCache) -> ModuleInfo {
  let mut m = ModuleInfo::new(gen);
  let bool_tag = m.types.type_id(gen, Type::Bool);
  for &t in &[Type::I64, Type::I32] {
    for &n in &["+", "-", "*", "/"] {
      add_intrinsic(gen, cache, &mut m, n, &[t, t], t);
    }
    for &n in &["==", ">", "<", ">=", "<=", "!="] {
      add_intrinsic(gen, cache, &mut m, n, &[t, t], Type::Bool);
    }
  }
  m
}

fn add_intrinsic(
  gen : &mut UIDGenerator, cache : &StringCache,
  m : &mut ModuleInfo, name : &str,
  args : &[Type], return_type : Type)
{
  let signature = m.types.signature_id(gen, FunctionSignature{
    return_type,
    args: args.iter().cloned().collect(),
  });
  let args = args.iter().enumerate().map(
    |(i, _)| format!("a{}", i).into()).collect();
  let f = FunctionDefinition {
    id: FunctionId(gen.next()),
    module_id: m.id,
    name_in_code: cache.get(name),
    args, signature,
    implementation: FunctionImplementation::Intrinsic,
    definition_location: TextLocation::zero(),
  };
  m.functions.insert(f.id, f);
}

pub struct ModuleInfo {
  pub id : ModuleId,
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub functions : HashMap<FunctionId, FunctionDefinition>,
  pub globals : HashMap<RefStr, GlobalDefinition>,
  pub types : Types,
}

pub struct CodegenInfo {
  pub node_type : HashMap<NodeId, Type>,
  pub sizeof_info : HashMap<NodeId, Type>,
  pub function_references : HashMap<NodeId, FunctionId>,
  pub global_references : HashMap<NodeId, RefStr>,
}

impl CodegenInfo {
  fn new() -> Self {
    CodegenInfo {
      node_type: HashMap::new(),
      sizeof_info: HashMap::new(),
      function_references: HashMap::new(),
      global_references: HashMap::new(),
    }
  }
}

impl ModuleInfo {
  fn new(gen : &mut UIDGenerator) -> ModuleInfo {
    ModuleInfo{
      id: ModuleId(gen.next()),
      type_defs: HashMap::new(),
      functions: HashMap::new(),
      globals: HashMap::new(),
      types: Types::new(),
    }
  }

  // TODO: This is really inefficient. Can maybe be improved using immutable collections:
  // use im_rc::hashmap::HashMap as ImMap;
  // use im_rc::vector::Vector as ImVec;
  pub fn child(&self, gen : &mut UIDGenerator) -> ModuleInfo {
    ModuleInfo {
      id: ModuleId(gen.next()),
      type_defs: self.type_defs.clone(),
      functions: self.functions.clone(),
      globals: self.globals.clone(),
      types: self.types.clone(),
    }
  }

  pub fn find_global(&self, name : &str) -> Option<&GlobalDefinition> {
    self.globals.get(name)
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
    self.type_defs.get(name)
  }

  pub fn find_function(&self, name : &str, args : &[Type]) -> Option<&FunctionDefinition> {
    self.functions.values().find(|def| {
      let sig = self.types.signature(def.signature);
      def.name_in_code.as_ref() == name &&
        sig.args.as_slice() == args
    })
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct FunctionId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SigId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct DefId(u64);

impl From<u64> for TypeId { fn from(v : u64) -> Self { TypeId(v) } }
impl From<u64> for SigId { fn from(v : u64) -> Self { SigId(v) } }
impl From<u64> for DefId { fn from(v : u64) -> Self { DefId(v) } }

#[derive(Clone)]
pub struct Types {
  types : BiMap<TypeId, Type>,

  signatures : BiMap<SigId, FunctionSignature>,

  type_definition_names : BiMap<DefId, RefStr>,
}

fn get_id<Id, V>(map : &mut BiMap<Id, V>, gen : &mut UIDGenerator, v : V) -> Id
  where Id: Eq + Hash + Copy + From<u64>, V: Eq + Hash
{
  if let Some(id) = map.get_by_right(&v) {
    *id
  }
  else {
    let id = gen.next().into();
    map.insert(id, v);
    id
  }
}

impl Types {

  pub fn new() -> Self {
    Types { 
      types: BiMap::new(),
      signatures: BiMap::new(),
      type_definition_names: BiMap::new(),
    }
  }

  pub fn get(&self, id : TypeId) -> Type {
    *self.types.get_by_left(&id).unwrap()
  }

  pub fn type_definition_id(&mut self, gen : &mut UIDGenerator, name : RefStr) -> DefId {
    let aaa = (); // TODO: lookup types from other modules
    get_id(&mut self.type_definition_names, gen, name)
  }

  pub fn signature_id(&mut self, gen : &mut UIDGenerator, sig : FunctionSignature) -> SigId {
    let aaa = (); // TODO: lookup types from other modules
    get_id(&mut self.signatures, gen, sig)
  }

  pub fn type_id(&mut self, gen : &mut UIDGenerator, t : Type) -> TypeId {
    let aaa = (); // TODO: lookup types from other modules
    get_id(&mut self.types, gen, t)
  }

  pub fn signature(&self, id : SigId) -> &FunctionSignature {
    self.signatures.get_by_left(&id).unwrap()
  }

  pub fn type_definition_name(&self, id : DefId) -> &RefStr {
    self.type_definition_names.get_by_left(&id).unwrap()
  }

  pub fn type_ref(&self, t : Type) -> TypeRef {
    TypeRef{ t, types: self }
  }

  pub fn type_ref_id(&self, id : TypeId) -> TypeRef {
    TypeRef{ t: self.get(id), types: self }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Type {
  Void,
  F64,
  F32,
  I64,
  U64,
  I32,
  U32,
  U16,
  U8,
  Bool,
  Dynamic,
  Fun(SigId),
  Def(DefId),
  Array(TypeId),
  Ptr(TypeId),
}

pub struct TypeRef<'l>{
  t : Type,
  types: &'l Types,
}

impl <'l> fmt::Display for TypeRef<'l> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let types = self.types;
    match self.t {
      Type::Fun(sig) => {
        let sig = self.types.signature(sig);
        write!(f, "fun({}) => {}", 
          sig.args.iter()
            .map(|a| types.type_ref(*a))
            .join(", "),
          types.type_ref(sig.return_type))
      }
      Type::Def(s) => {
        let name =
          self.types.type_definition_name(s);
        write!(f, "{}", name)
      }
      Type::Array(t) => write!(f, "array({})", types.type_ref_id(t)),
      Type::Ptr(t) => write!(f, "ptr({})", types.type_ref_id(t)),
      t => write!(f, "{:?}", t),
    }
  }
}

impl Type {
  pub fn from_string(s : &str) -> Option<Type> {
    match s {
      "f64" => Some(Type::F64),
      "f32" => Some(Type::F32),
      "bool" => Some(Type::Bool),
      "i64" => Some(Type::I64),
      "u64" => Some(Type::U64),
      "i32" => Some(Type::I32),
      "u32" => Some(Type::U32),
      "u16" => Some(Type::U16),
      "u8" => Some(Type::U8),
      "any" => Some(Type::Dynamic),
      "()" => Some(Type::Void),
      "" => Some(Type::Dynamic),
      _ => None,
    }
  }

  pub fn float(&self) -> bool {
    match self { Type::F32 | Type::F64 => true, _ => false }
  }

  pub fn unsigned_int(&self) -> bool {
    match self { Type::U64 | Type::U32 | Type::U16 | Type::U8 => true, _ => false }
  }

  pub fn signed_int(&self) -> bool {
    match self { Type::I64 | Type::I32 => true, _ => false }
  }

  pub fn int(&self) -> bool {
    self.signed_int() || self.unsigned_int()
  }

  pub fn number(&self) -> bool {
    self.int() || self.float()
  }

  pub fn pointer(&self) -> bool {
    match self { Type::Ptr(_) | Type::Fun(_) => true, _ => false }
  }
}

#[derive(Clone, Debug)]
pub struct TypeDefinition {
  pub name : RefStr,
  pub fields : Vec<(Symbol, Type)>,
  pub kind : TypeKind,
  pub drop_function : Option<FunctionId>,
  pub clone_function : Option<FunctionId>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone)]
pub enum FunctionImplementation {
  Normal{body: NodeId, name_for_codegen: RefStr },
  CFunction,
  Intrinsic,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
  pub id : FunctionId,
  pub module_id : ModuleId,
  pub name_in_code : RefStr,
  pub args : Vec<Symbol>,
  pub signature : SigId,
  pub implementation : FunctionImplementation,
  pub definition_location : TextLocation,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Vec<Type>,
}

impl PartialEq for TypeDefinition {
  fn eq(&self, rhs : &Self) -> bool {
    self.name == rhs.name
  }
}

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "top_level";

use Content::*;

#[derive(Clone)]
pub struct GlobalDefinition {
  pub module_id : ModuleId,
  pub name : RefStr,
  pub type_tag : Type,
  pub c_bind : bool,
}

fn literal_to_type(string_def : DefId, v : &Val) -> Type {
  use Type::*;
  match v {
    Val::F64(_) => F64,
    Val::F32(_) => F32,
    Val::I64(_) => I64,
    Val::I32(_) => I32,
    Val::Bool(_) => Bool,
    Val::U64(_) => U64,
    Val::U32(_) => U32,
    Val::U16(_) => U16,
    Val::U8(_) => U8,
    Val::Void => Void,
    Val::String(_) => {
      Def(string_def)
    }
  }
}

struct Inference<'l> {
  code : &'l str,
  nodes : &'l Nodes,
  m : &'l mut ModuleInfo,
  cg : &'l mut CodegenInfo,
  c : &'l Constraints,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  errors : &'l mut Vec<Error>,
  resolved : HashMap<TypeSymbol, Type>,
  globals : Vec<(GlobalDefinition, TextLocation)>,
}

impl <'l> Inference<'l> {

  fn new(
    code : &'l str,
    nodes : &'l Nodes,
    m : &'l mut ModuleInfo,
    cg : &'l mut CodegenInfo,
    c : &'l Constraints,
    gen : &'l mut UIDGenerator,
    cache : &'l StringCache,
    errors : &'l mut Vec<Error>)
      -> Self
  {
    Inference {
      code, nodes, m, cg, c, gen, cache, errors,
      resolved: HashMap::new(), globals: vec![],
    }
  }

  fn ts_code_slice(&self, c : &Constraints, ts : TypeSymbol) -> &str {
    let loc = c.symbols.get(&ts).unwrap();
    let (start_line, end_line) = (loc.start.line - 1, loc.end.line - 1);
    let mut it =
      // Chain the zero offset for the first line
      [0].iter().cloned().chain(
        // find the newline positions
        self.code.char_indices().filter(|&(_, c)| c == '\n')
        // offset past the \n char
        .map(|(b, _)| b + 1)
      )
      // get the start offsets of the lines we care about
      .enumerate().filter(|&(i, _)| i == start_line || i == end_line)
      .map(|(_, b)| b);
    let l1_start = it.next().unwrap();
    let l2_start = it.next().unwrap_or(l1_start);
    &self.code[l1_start + loc.start.col.. l2_start + loc.end.col]
  }

  fn set_type_id(&mut self, ts : TypeSymbol, t : TypeId) {
    let t = self.m.types.get(t);
    self.set_type(ts, t);
  }

  fn set_type(&mut self, ts : TypeSymbol, t : Type) {
    let aaa = (); // TODO: unify!
    let code = self.ts_code_slice(&self.c, ts);
    if !self.resolved.contains_key(&ts) {
      println!("     Inferred type {} for '{}'", self.m.types.type_ref(t), code);
      self.resolved.insert(ts, t);
    }
  }

  fn get(&self, ts : TypeSymbol) -> Option<Type> {
    self.resolved.get(&ts).cloned()
  }

  // fn unresolved_constraint(&mut self, c : &Constraint) -> Error {
  //   match c  {
  //     Constraint::Assert(ts, t) => panic!(),
  //     Constraint::Equalivalent(a, b) => {
  //       let loc = self.c.loc(*a).merge(self.c.loc(*b));
  //       error_raw(loc, "equivalence could not be resolved")
  //     }
  //     Constraint::FunctionDef{ loc, .. } =>
  //       error_raw(loc, "function definition not resolved"),
  //     Constraint::FunctionCall{ function, args, result } => (),
  //     Constraint::Constructor { type_name, fields, result } => (),
  //     Constraint::Convert { val, into_type } => (),
  //     Constraint::GlobalDef(name, ts, loc) => (),
  //     Constraint::GlobalReference { name, result } => (),
  //     Constraint::FieldAccess{ container, field, result } => (),
  //     Constraint::Array{ array, element } => (),
  //   }
  // }

  fn process_constraint(&mut self, c : &Constraint) -> bool {
    match c  {
      Constraint::Assert(ts, t) => {
        println!("Asserting type... ");
        self.set_type_id(*ts, *t);
        return true;
      }
      Constraint::Equalivalent(a, b) => {
        println!("Equivalence between '{}' and '{}' ... ",
          self.ts_code_slice(&self.c, *a).lines().next().unwrap(),
          self.ts_code_slice(&self.c, *b).lines().next().unwrap());
        if let Some(&t) = self.resolved.get(a) {
          self.set_type(*b, t);
          return true;
        }
        if let Some(&t) = self.resolved.get(b) {
          self.set_type(*a, t);
          return true;
        }
      }
      Constraint::FunctionDef{ name, return_type, args, body, loc } => {
        println!("Function def... ");
        println!("   Args: ");
        for (_, ts) in args.iter() {
          let code = self.ts_code_slice(&self.c, *ts);
          if let Some(t) = self.resolved.get(ts) {
            println!("      {}, {}", code, self.m.types.type_ref(*t));
          }
          else {
            println!("      {}, unresolved, ", code);
          }
        }
        let resolved_args_count = args.iter().flat_map(|(_, ts)| self.resolved.get(ts)).count();
        let return_type = self.resolved.get(return_type);
        if resolved_args_count == args.len() && return_type.is_some() {
          let mut arg_names = vec!();
          let mut arg_types = vec!();
          for (arg, arg_ts) in args.iter() {
            arg_names.push(arg.clone());
            arg_types.push(*self.resolved.get(arg_ts).unwrap());
          }
          if self.m.find_function(&name, arg_types.as_slice()).is_some() {
            let e = error_raw(loc, "function with that name and signature already defined");
            self.errors.push(e);
          }
          else {
            let signature = FunctionSignature {
              return_type: *return_type.unwrap(),
              args: arg_types,
            };
            let implementation = FunctionImplementation::Normal {
              body: *body,
              name_for_codegen: format!("{}.{}", name, self.gen.next()).into(),
            };
            let f = FunctionDefinition {
              id: FunctionId(self.gen.next()),
              module_id: self.m.id,
              name_in_code: name.clone(),
              args: arg_names,
              signature: self.m.types.signature_id(self.gen, signature),
              implementation,
              definition_location: *loc,
            };
            self.m.functions.insert(f.id, f);
            println!("Function {} inferred.", name);
            return true;
          }
        }
        println!();
      }
      Constraint::FunctionCall{ node, function, args, result } => {
        println!("Function call... ");
        let arg_types : Vec<_> =
          args.iter().flat_map(|(_, ts)| self.resolved.get(ts).cloned()).collect();
        if arg_types.len() == args.len() {
          match function {
            Function::Name(sym) => {
              if let Some(def) = self.m.find_function(&sym.name, arg_types.as_slice()) {
                self.cg.function_references.insert(*node, def.id);
                let return_type = self.m.types.signature(def.signature).return_type;
                self.set_type(*result, return_type);
                return true;
              }
            }
            Function::Value(ts) => {
              let aaa = (); // TODO: support first class functions
              panic!();
            }
          }
        }
      }
      Constraint::Constructor { type_name, fields, result } => {
        println!("Constructor... ");
        if let Some(def) = self.m.find_type_def(type_name) {
          if def.fields.len() == fields.len() {
            let it = fields.iter().zip(def.fields.iter());
            let mut arg_types = vec![];
            for ((field_name, _), (expected_name, expected_type)) in it {
              if let Some(field_name) = field_name {
                if field_name.name != expected_name.name {
                  self.errors.push(error_raw(field_name.loc, "incorrect field name"));
                }
              }
              arg_types.push(*expected_type);
            }
            for((_, ts), t) in fields.iter().zip(arg_types.iter()) {
              self.set_type(*ts, *t);
            }
          }
          else {
            self.errors.push(
              error_raw(self.c.symbols.get(result).unwrap(), "incorrect number of arguments"));
          }
          let def_id = self.m.types.type_definition_id(self.gen, type_name.clone());
          self.set_type(*result, Type::Def(def_id));
          return true;
        }
      }
      Constraint::Convert { val, into_type } => {
        if let Some(&t) = self.resolved.get(val) {
          if t.pointer() && into_type.pointer() {}
          else if t.number() && into_type.number() {}
          else if t.pointer() && into_type.unsigned_int() {}
          else if t.unsigned_int() && into_type.pointer() {}
          else {
            let e = error_raw(*self.c.symbols.get(val).unwrap(), "type conversion not supported");
            self.errors.push(e);
          }
          return true;
        }
      }
      Constraint::GlobalDef{ name, type_symbol, loc, c_bind } => {
        if let Some(&t) = self.resolved.get(type_symbol) {
          let g = GlobalDefinition {
            module_id: self.m.id,
            name: name.clone(),
            type_tag: t,
            c_bind: *c_bind,
          };
          self.globals.push((g, *loc));
          return true;
        }
      }
      Constraint::GlobalReference { node, name, result } => {
        if let Some(def) = self.m.find_global(&name) {
          if def.module_id != self.m.id {
            let t = def.type_tag;
            self.set_type(*result, t);
            self.cg.global_references.insert(*node, name.clone());
            return true;
          }
        }
        if let Some(Type::Fun(sig)) = self.resolved.get(result).cloned() {
          let sig = self.m.types.signature(sig);
          if let Some(def) = self.m.find_function(&name, sig.args.as_slice()) {
            self.cg.function_references.insert(*node, def.id);
            return true;
          }
        }
      }
      Constraint::Index{ node, container, index, result } => {
        let c = self.resolved.get(container).cloned();
        let i = self.resolved.get(index).cloned();
        if let [Some(c), Some(i)] = [c, i] {
          if i.int() {
            match c {
              Type::Ptr(element) => {
                self.set_type_id(*result, element);
                return true;
              }
              _ => (),
            }
          }
          if let Some(def) = self.m.find_function("Index", &[c, i]) {
            self.cg.function_references.insert(*node, def.id);
            let return_type = self.m.types.signature(def.signature).return_type;
            self.set_type(*result, return_type);
            return true;
          }
        }
      }
      Constraint::FieldAccess{ container, field, result } => {
        println!("Field access '{}'... ", field.name);
        let t = self.resolved.get(container);
        if let Some(t) = t {
          if let Type::Def(id) = *t { 
            let n = self.m.types.type_definition_name(id);
            if let Some(def) = self.m.find_type_def(n) {
              let f = def.fields.iter().find(|(n, _)| n.name == field.name);
              if let Some((_, t)) = f.cloned() {
                self.set_type(*result, t);
              }
              else {
                self.errors.push(error_raw(field.loc, "type has no field with this name"));
              }
              return true;
            }
          }
          else {
            self.errors.push(error_raw(field.loc, "type has no field with this name"));
            return true;
          }
        }
      }
      Constraint::Array{ array, element } => {
        if let Some(array_type) = self.resolved.get(array) {
          if let Type::Array(element_type) = *array_type {
            self.set_type_id(*element, element_type);
          }
        }
        if let Some(element_type) = self.resolved.get(element) {
          let element_type = self.m.types.type_id(self.gen, *element_type);
          self.set_type(*array, Type::Array(element_type));
        }
      }
    }
    false
  }

  fn infer(&mut self) {
    println!("To resolve: {}", self.c.symbols.len());
    let mut unused_constraints = vec![];
    for c in self.c.constraints.iter() {
      if !self.process_constraint(c) {
        unused_constraints.push(c);
      }
    }
    println!("\n####### Inference pass complete #######\n");
    while unused_constraints.len() > 0 {
      let remaining_before_pass = unused_constraints.len();
      unused_constraints.retain(|c| !self.process_constraint(c));
      println!("\n####### Inference pass complete #######\n");
      // Exit if no constraints were resolved in the last pass
      if remaining_before_pass == unused_constraints.len() {
        break;
      }
    }
    // Add the globals (this must be delayed because globals follow lexical scoping rules within modules)
    for (g, loc) in self.globals.drain(..) {
      if self.m.find_global(&g.name).is_some() {
        let e = error_raw(loc, "function with that name and signature already defined");
        self.errors.push(e);
      }
      else {
        self.m.globals.insert(g.name.clone(), g);
      }
    }
    // Generate errors for unresolved types
    if self.c.symbols.len() > self.resolved.len() {
      for ts in self.c.symbols.keys() {
        if !self.resolved.contains_key(ts) {
          let e = error_raw(self.c.loc(*ts), "type could not be resolved");
          self.errors.push(e);
        }
      }
    }
    // Sanity check to make sure that programs with unresolved constraints contain errors
    if unused_constraints.len() > 0 && self.errors.len() == 0 {
      panic!("Constraint unused! Some kind of error should be generated!");
    }
    if self.errors.len() > 0 {
      println!("\nErrors:");
      for e in self.errors.iter() {
        println!("         {}", e);
      }
      println!();
    }
    else {
      for (n, ts) in self.c.node_symbols.iter() {
        let t = self.resolved.get(ts).unwrap();
        self.cg.node_type.insert(*n, *t);
      }
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(u64);

pub enum Function {
  Value(TypeSymbol),
  Name(Symbol),
}

pub enum Constraint {
  Assert(TypeSymbol, TypeId),
  Equalivalent(TypeSymbol, TypeSymbol),
  Array{ array : TypeSymbol, element : TypeSymbol },
  Convert{ val : TypeSymbol, into_type : Type },
  FieldAccess {
    container : TypeSymbol,
    field : Symbol,
    result : TypeSymbol,
  },
  Constructor {
    type_name : RefStr,
    fields : Vec<(Option<Symbol>, TypeSymbol)>,
    result : TypeSymbol,
  },
  FunctionDef {
    name : RefStr,
    return_type : TypeSymbol,
    args : Vec<(Symbol, TypeSymbol)>,
    body : NodeId,
    loc : TextLocation,
  },
  FunctionCall {
    node : NodeId,
    function : Function,
    args : Vec<(Option<SymbolId>, TypeSymbol)>,
    result : TypeSymbol,
  },
  Index {
    node : NodeId,
    container : TypeSymbol,
    index : TypeSymbol,
    result : TypeSymbol,
  },
  GlobalDef {
    name: RefStr,
    type_symbol: TypeSymbol,
    loc: TextLocation,
    c_bind : bool,
  },
  GlobalReference {
    node : NodeId,
    name : RefStr,
    result : TypeSymbol,
  },
}

struct CoreTypes {
  string : DefId,
}

impl CoreTypes {
  fn new(types : &mut Types, gen : &mut UIDGenerator, cache : &StringCache) -> Self {
    CoreTypes {
      string: types.type_definition_id(gen, cache.get("string")),
    }
  }
}

struct Constraints {
  symbols : HashMap<TypeSymbol, TextLocation>,
  node_symbols : HashMap<NodeId, TypeSymbol>,
  variable_symbols : HashMap<SymbolId, TypeSymbol>,
  constraints : Vec<Constraint>,
}

impl Constraints {
  fn new() -> Self {
    Constraints {
      symbols: HashMap::new(),
      node_symbols: HashMap::new(),
      variable_symbols: HashMap::new(),
      constraints: vec![],
    }
  }

  fn loc(&self, ts : TypeSymbol) -> TextLocation {
    *self.symbols.get(&ts).unwrap()
  }
}

struct GatherConstraints<'l> {
  labels : HashMap<LabelId, TypeSymbol>,
  type_def_refs : Vec<(RefStr, TextLocation)>,
  core : &'l CoreTypes,
  m : &'l mut ModuleInfo,
  cg : &'l mut CodegenInfo,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  c : &'l mut Constraints,
  errors : &'l mut Vec<Error>,
}

impl <'l> GatherConstraints<'l> {

  fn new(
    core : &'l CoreTypes,
    m : &'l mut ModuleInfo,
    cg : &'l mut CodegenInfo,
    gen : &'l mut UIDGenerator,
    cache : &'l StringCache,
    c : &'l mut Constraints,
    errors : &'l mut Vec<Error>,
  ) -> GatherConstraints<'l>
  {
    GatherConstraints {
      labels: HashMap::new(),
      type_def_refs: vec![],
      core, m, cg, gen, cache, c, errors,
    }
  }

  fn gather_constraints(&mut self, n : &Nodes) {
    self.process_node(n, n.root);
    for (name, loc) in self.type_def_refs.iter() {
      if self.m.find_type_def(name).is_none() {
        let e = error_raw(loc, "No type definition with this name found.");
        self.errors.push(e);
      }
    }
  }

  fn log_error<V>(&mut self, r : Result<V, Error>) -> Option<V> {
    match r {
      Ok(v) => Some(v),
      Err(e) => { self.errors.push(e); None } 
    }
  }

  fn type_symbol(&mut self, loc : TextLocation) -> TypeSymbol {
    let ts = TypeSymbol(self.gen.next().into());
    self.c.symbols.insert(ts, loc);
    ts
  }

  fn node_to_symbol(&mut self, n : &Node) -> TypeSymbol {
    if let Some(ts) = self.c.node_symbols.get(&n.id) { *ts }
    else {
      let ts = self.type_symbol(n.loc);
      self.c.node_symbols.insert(n.id, ts);
      ts
    }
  }

  fn variable_to_type_symbol(&mut self, v : &Symbol) -> TypeSymbol {
    if let Some(ts) = self.c.variable_symbols.get(&v.id) { *ts }
    else {
      let ts = self.type_symbol(v.loc);
      self.c.variable_symbols.insert(v.id, ts);
      ts
    }
  }

  fn constraint(&mut self, c : Constraint) {
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.constraint(Constraint::Equalivalent(a, b));
  }

  fn assert(&mut self, ts : TypeSymbol, t : Type) {
    let t = self.m.types.type_id(self.gen, t);
    self.constraint(Constraint::Assert(ts, t));
  }

  fn tagged_symbol(&mut self, ts : TypeSymbol, type_expr : &Option<Box<Expr>>) {
    if let Some(type_expr) = type_expr {
      if let Some(t) = self.try_expr_to_type(type_expr) {
        self.assert(ts, t);
      }
    }
  }

  fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
    let node = n.node(id);
    let ts = self.node_to_symbol(node);
    match &node.content {
      Literal(val) => {
        let t = literal_to_type(self.core.string, val);
        self.assert(ts, t);
      }
      VariableInitialise{ name, type_tag, value, var_scope } => {
        self.assert(ts, Type::Void);
        let var_type_symbol = self.variable_to_type_symbol(name);
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
        match var_scope {
          VarScope::Local => (),
          VarScope::Global => {
            self.constraint(Constraint::GlobalDef{
              name: name.name.clone(),
              type_symbol: var_type_symbol,
              loc: node.loc,
              c_bind: false,
            });
          }
        }
      }
      Assignment{ assignee , value } => {
        self.assert(ts, Type::Void);
        let a = self.process_node(n, *assignee);
        let b = self.process_node(n, *value);
        self.equalivalent(a, b);
      }
      IfThen{ condition, then_branch } => {
        self.assert(ts, Type::Void);
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        self.assert(cond, Type::Bool);
        self.assert(then_br, Type::Void);
      }
      IfThenElse{ condition, then_branch, else_branch } => {
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        let else_br = self.process_node(n, *else_branch);
        self.equalivalent(ts, then_br);
        self.assert(cond, Type::Bool);
        self.equalivalent(then_br, else_br);
      }
      Block(ns) => {
        let len = ns.len();
        if len > 0 {
          for child in &ns[0..(len-1)] {
            self.process_node(n, *child);
          }
          let c = self.process_node(n, ns[len-1]);
          self.equalivalent(ts, c);
        }
        else {
          self.assert(ts, Type::Void);
        }
      }
      Quote(_e) => {
        let expr_def = self.type_definition_id(node.loc, self.cache.get("expr"));
        let t = self.m.types.type_id(self.gen, Type::Def(expr_def));
        self.assert(ts, Type::Ptr(t));
      }
      Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_type_symbol(n.symbol(*refers_to));
          self.equalivalent(ts, var_type);
        }
        else {
          self.constraint(Constraint::GlobalReference{ node: id, name: name.clone(), result: ts });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, body } => {
        self.assert(ts, Type::Void);
        let mut ts_args : Vec<(Symbol, TypeSymbol)> = vec![];
        for (arg, type_tag) in args.iter() {
          let arg_type_symbol = self.variable_to_type_symbol(arg);
          self.tagged_symbol(arg_type_symbol, type_tag);
          ts_args.push((arg.clone(), arg_type_symbol));
        }
        let body_ts = {
          // Need new scope stack for new function
          let mut gc = GatherConstraints::new(
            self.core, self.m, self.cg, self.gen, self.cache, self.c, self.errors);
          gc.process_node(n, *body)
        };
        self.tagged_symbol(body_ts, return_tag);
        let f = Constraint::FunctionDef { 
          name: name.clone(), args: ts_args,
          return_type: body_ts, body: *body, loc: node.loc };
        self.constraint(f);
      }
      CBind { name, type_tag } => {
        self.assert(ts, Type::Void);
        let cbind_ts = self.type_symbol(node.loc);
        if let Some(t) = self.try_expr_to_type(type_tag) {
          self.assert(cbind_ts, t);
        }
        self.constraint(Constraint::GlobalDef{
          name: name.clone(),
          type_symbol: cbind_ts,
          loc: node.loc,
          c_bind: true,
        });
      }
      Content::TypeDefinition{ name, kind, fields } => {
        self.assert(ts, Type::Void);
        if self.m.type_defs.get(name).is_some() {
          let e = error_raw(node.loc, "type with this name already defined");
          self.errors.push(e)
        }
        else {
          // TODO: check for duplicates?
          let mut typed_fields = vec![];
          for (field, type_tag) in fields.iter() {
            if let Some(t) = self.try_expr_to_type(type_tag.as_ref().unwrap()) {
              typed_fields.push((field.clone(), t));
            }
          }
          // TODO: Generics?
          let def = TypeDefinition {
            name: name.clone(),
            fields: typed_fields,
            kind: *kind,
            drop_function: None, clone_function: None,
            definition_location: node.loc,
          };
          self.m.type_defs.insert(name.clone(), def);
        }
      }
      TypeConstructor{ name, field_values } => {
        let mut fields = vec![];
        for (field, value) in field_values.iter() {
          let field_type_symbol = self.process_node(n, *value);
          fields.push((field.clone(), field_type_symbol));
        }
        let tc = Constraint::Constructor{ type_name: name.clone(), fields, result: ts };
        self.constraint(tc);
      }
      FieldAccess{ container, field } => {
        let fa = Constraint::FieldAccess {
          container: self.process_node(n, *container),
          field: field.clone(),
          result: ts,
        };
        self.constraint(fa);
      }
      Index{ container, index } => {
        // TODO: How do we link the index type here to the index type in the array?
        // I suppose through the definition of a generic index function, which needs to exist
        // somewhere...
        let container = self.process_node(n, *container);
        let index = self.process_node(n, *index);
        let i = Constraint::Index {
          node: id, container, index, result: ts,
        };
        self.constraint(i);
      }
      ArrayLiteral(ns) => {
        let element_ts = self.type_symbol(node.loc);
        for element in ns.iter() {
          let el = self.process_node(n, *element);
          self.equalivalent(el, element_ts);
        }
        self.constraint(Constraint::Array{ array: ts, element: element_ts });
      }
      FunctionCall{ function, args } => {
        let function = match function {
          FunctionNode::Name(name) => Function::Name(name.clone()),
          FunctionNode::Value(val) => {
            let val = self.process_node(n, *val);
            Function::Value(val)
          }
        };
        let fc = Constraint::FunctionCall {
          node: id,
          function,
          args: args.iter().map(|id| (None, self.process_node(n, *id))).collect(),
          result: ts,
        };
        self.constraint(fc);
      }
      While{ condition, body } => {
        self.assert(ts, Type::Void);
        let cond = self.process_node(n, *condition);
        let body = self.process_node(n, *body);
        self.assert(cond, Type::Bool);
        self.assert(body, Type::Void);
      }
      Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        if let Some(t) = self.try_expr_to_type(into_type) {
          self.assert(ts, t);
          let c = Constraint::Convert { val: v, into_type: t };
          self.constraint(c);
        }
      }
      SizeOf{ type_tag } => {
        if let Some(tid) = self.try_expr_to_type(type_tag) {
          self.cg.sizeof_info.insert(node.id, tid);
        }
        self.assert(ts, Type::U64);
      }
      Label{ label, body } => {
        self.labels.insert(*label, ts);
        let body = self.process_node(n, *body);
        self.equalivalent(ts, body);
      }
      BreakToLabel{ label, return_value } => {
        self.assert(ts, Type::Void);
        let label_ts = *self.labels.get(label).unwrap();
        if let Some(v) = return_value {
          let v = self.process_node(n, *v);
          self.equalivalent(label_ts, v);
        }
        else {
          self.assert(label_ts, Type::Void);
        }
      }
    }
    ts
  }

  fn try_expr_to_type(&mut self, e : &Expr) -> Option<Type> {
    let r = self.expr_to_type(e);
    self.log_error(r)
  }

  fn try_expr_to_type_id(&mut self, e : &Expr) -> Option<TypeId> {
    let r = self.expr_to_type_id(e);
    self.log_error(r)
  }

  fn type_definition_id(&mut self, loc : TextLocation, name : RefStr) -> DefId {
    self.type_def_refs.push((name.clone(), loc));
    self.m.types.type_definition_id(self.gen, name)
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn expr_to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      let name = self.cache.get(name);
      let id = self.type_definition_id(expr.loc, name);
      return Ok(Type::Def(id));
    }
    match expr.try_construct() {
      Some(("fun", es)) => {
        if let Some(args) = es.get(0) {
          let args =
            args.children().iter()
            .map(|e| {
              let e = if let Some((":", [_name, tag])) = e.try_construct() {tag} else {e};
              self.expr_to_type(e)
            })
            .collect::<Result<Vec<Type>, Error>>()?;
          let return_type = if let Some(t) = es.get(1) {
            self.expr_to_type(t)?
          }
          else {
            Type::Void
          };
          let id = self.m.types.signature_id(self.gen, FunctionSignature{ args, return_type});
          return Ok(Type::Fun(id));
        }
      }
      Some(("call", [name, t])) => {
        match name.unwrap_symbol()? {
          "ptr" => {
            let t = self.expr_to_type_id(t)?;
            return Ok(Type::Ptr(t))
          }
          "array" => {
            let t = self.expr_to_type_id(t)?;
            return Ok(Type::Array(t))
          }
          _ => (),
        }
      }
      _ => ()
    }
    error(expr, "invalid type expression")
  }

  fn expr_to_type_id(&mut self, expr : &Expr) -> Result<TypeId, Error> {
    let t = self.expr_to_type(expr)?;
    return Ok(self.m.types.type_id(self.gen, t));
  }

}
