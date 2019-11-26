
use std::fmt;
use itertools::Itertools;

use crate::error::TextLocation;
use crate::expr::UIDGenerator;
use crate::structure::{
  NodeId, Symbol, TypeKind, GlobalType,
};
use crate::arena::{ Arena, Ap };

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct FunctionId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GenericId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for FunctionId { fn from(v : u64) -> Self { FunctionId(v) } }
impl From<u64> for GenericId { fn from(v : u64) -> Self { GenericId(v) } }

pub struct TypeInfo {
  pub type_defs : HashMap<Ap<str>, Ap<TypeDefinition>>,
  pub functions : HashMap<FunctionId, Ap<FunctionDefinition>>,
  pub globals : HashMap<Ap<str>, Ap<GlobalDefinition>>,
  pub module_id : ModuleId,
}

/// Primitive type
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PType {
  Void,
  F64, F32,
  I64, I32,
  U64, U32, U16, U8,
  Bool,
}

impl  Into<Type> for PType {
  fn into(self) -> Type {
    Type::Prim(self)
  }
}

use PType::*;

#[derive(Clone, Copy, Debug)]
pub enum Type {
  /// Primitive type (e.g. int, float, bool, etc)
  Prim(PType),
  Fun(Ap<FunctionSignature>),
  Def(Ap<str>),
  Array(Ap<Type>),
  Ptr(Ap<Type>),
  Generic(GenericId),
  Unknown,
}

#[derive(Clone, Debug)]
pub struct TypeDefinition {
  pub name : Ap<str>,
  pub fields : Vec<(Symbol, Type)>,
  pub kind : TypeKind,
  pub drop_function : Option<Ap<FunctionDefinition>>,
  pub clone_function : Option<Ap<FunctionDefinition>>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone)]
pub enum FunctionImplementation {
  Normal{body: NodeId, name_for_codegen: Ap<str>, args : Vec<Symbol> },
  CFunction,
  Intrinsic,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
  pub id : FunctionId,
  pub module_id : ModuleId,
  pub name_in_code : Ap<str>,
  pub signature : Ap<FunctionSignature>,
  pub generics : Vec<GenericId>,
  pub implementation : FunctionImplementation,
  pub loc : TextLocation,
}

impl  FunctionDefinition {
  pub fn codegen_name(&self) -> Option<&str> {
    match &self.implementation {
      FunctionImplementation::Normal{ name_for_codegen, .. } => Some(name_for_codegen),
      FunctionImplementation::CFunction => Some(&self.name_in_code),
      FunctionImplementation::Intrinsic => None,
    }
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Ap<[Type]>,
}

#[derive(Clone)]
pub struct GlobalDefinition {
  pub module_id : ModuleId,
  pub name : Ap<str>,
  pub type_tag : Type,
  pub global_type : GlobalType,
  pub loc : TextLocation,
}

impl  PartialEq for Type {
  fn eq(&self, other: &Self) -> bool {
    use Type::*;
    match (*self, *other) {
      (Fun(a), Fun(b)) => a == b,
      (Def(a), Def(b)) => a == b,
      (Array(a), Array(b)) => a == b,
      (Ptr(a), Ptr(b)) => a == b,
      (Prim(a), Prim(b)) => a == b,
      (Generic(a), Generic(b)) => a == b,
      _ => false,
    }
  }
}

impl  fmt::Display for GenericId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let GenericId(id) = *self;
    write!(f, "{:X}", id)
  }
}

impl  fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::Fun(sig) => {
        write!(f, "fun({}) => {}", 
          sig.args.iter().join(", "),
          sig.return_type)
      }
      Type::Def(name) => {
        write!(f, "{}", name)
      }
      Type::Array(t) => write!(f, "array({})", t),
      Type::Ptr(t) => write!(f, "ptr({})", t),
      Type::Prim(t) => write!(f, "{:?}", t),
      Type::Generic(id) => write!(f, "@Generic({})", id),
      Type::Unknown => write!(f, "@Unknown"),
    }
  }
}

impl  Type {
  pub fn from_string(s : &str) -> Option<Type> {
    let pt = match s {
      "f64" => F64,
      "f32" => F32,
      "bool" => Bool,
      "i64" => I64,
      "u64" => U64,
      "i32" => I32,
      "u32" => U32,
      "u16" => U16,
      "u8" => U8,
      // "any" => Dynamic,
      "()" => Void,
      // "" => Dynamic,
      _ => return None,
    };
    Some(Type::Prim(pt))
  }

  pub fn float(&self) -> bool {
    match self { Type::Prim(F32) | Type::Prim(F64) => true, _ => false }
  }

  pub fn unsigned_int(&self) -> bool {
    match self { Type::Prim(U64) | Type::Prim(U32) | Type::Prim(U16) | Type::Prim(U8) => true, _ => false }
  }

  pub fn signed_int(&self) -> bool {
    match self { Type::Prim(I64) | Type::Prim(I32) => true, _ => false }
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

impl TypeInfo {
  pub fn new(module_id : ModuleId) -> TypeInfo {
    TypeInfo {
      type_defs: HashMap::new(),
      functions: HashMap::new(),
      globals: HashMap::new(),
      module_id,
    }
  }

  pub fn find_global(&self, name : &str, skip_repl_globals : bool, results : &mut Vec<SymbolDef>) {
    if let Some(g) = self.globals.get(name) {
      if !(skip_repl_globals && g.global_type == GlobalType::Repl) {
        results.push(SymbolDef::Glob(*g));
      }
    }
    for f in self.functions.values() {
      if f.name_in_code.as_ref() == name {
        results.push(SymbolDef::Fun(*f));
      }
    }
  }

  pub fn find_type_def(&self, name : &str) -> Option<Ap<TypeDefinition>> {
    self.type_defs.get(name).cloned()
  }

  pub fn get_function(&self, fid : FunctionId) -> Ap<FunctionDefinition> {
    *self.functions.get(&fid).unwrap()
  }

  pub fn find_function(
    &self,
    name : &str,
    args : &[Type],
    skip_repl_globals : bool,
    arena : &Arena,
    gen : &mut UIDGenerator, 
    generics : &mut HashMap<GenericId, Type>,
    results : &mut Vec<ConcreteFunction>,
  )
  {
    if let Some(def) = self.globals.get(name) {
      if !(skip_repl_globals && def.global_type == GlobalType::Repl) {
        if let Type::Fun(sig) = def.type_tag {
          if args == sig.args.as_ref() {
            let def = SymbolDef::Glob(*def);
            results.push(ConcreteFunction { def, concrete_signature: sig });
          }
        }
      }
    }
    let r = self.functions.values().find(|def| {
      def.generics.is_empty() && def.name_in_code.as_ref() == name && {
        args == def.signature.args.as_ref()
      }
    });
    if let Some(def) = r {
      let concrete_signature = def.signature;
      let def = SymbolDef::Fun(*def);
      results.push(ConcreteFunction { def, concrete_signature });
    }
    else {
      let r = self.functions.values().find(|def| {
        (!def.generics.is_empty()) && def.name_in_code.as_ref() == name && {
          let matched = generic_match_sig(generics, args, def, &def.signature);
          if !matched {
            generics.clear();
          }
          matched
        }
      });
      if let Some(def) = r {
        let concrete_signature = concrete_signature(arena, gen, def, generics);
        let def = SymbolDef::Fun(*def);
        results.push(ConcreteFunction { def, concrete_signature });
      }
    }
  }
}


fn concrete_signature(arena : &Arena, gen : &mut UIDGenerator, def : &FunctionDefinition, generic_map : &mut HashMap<GenericId, Type>) -> Ap<FunctionSignature> {
  let sig = def.signature;
  let mut args = arena.alloc_slice_mut(sig.args.as_ref());
  for t in args.iter_mut() {
    *t = generic_replace(arena, generic_map, gen, *t);
  }
  let return_type = generic_replace(arena, generic_map, gen, sig.return_type);
  let sig = FunctionSignature { args: args.into_ap(), return_type };
  arena.alloc(sig)
}

fn generic_replace(arena : &Arena, generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, t : Type)
  -> Type
{
  match t {
    Type::Ptr(t) => {
      let t = arena.alloc(generic_replace(arena, generics, gen, *t));
      Type::Ptr(t)
    }
    Type::Array(t) => {
      let t = arena.alloc(generic_replace(arena, generics, gen, *t));
      Type::Array(t)
    }
    Type::Generic(gid) => {
      *generics.get(&gid).unwrap()
    }
    _ => return t,
  }
}

fn generic_match_sig(
  generics : &mut HashMap<GenericId, Type>, args : &[Type],
  def : &FunctionDefinition, sig : &FunctionSignature)
    -> bool
{
  args.len() == sig.args.len() && {
    for (t, gt) in args.iter().zip(sig.args.iter()) {
      if !generic_match(generics, *t, *gt) {
        return false;
      }
    }
    generics.len() == def.generics.len()
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, t : Type, gt : Type) -> bool {
  let (t, gt) = match (t, gt) {
    (Type::Ptr(t), Type::Ptr(gt)) => (t, gt),
    (Type::Array(t), Type::Array(gt)) => (t, gt),
    (t, Type::Generic(gid)) => {
      if let Some(bound_type) = generics.get(&gid) {
        return t == *bound_type;
      }
      else {
        generics.insert(gid, t);
        return true;
      }
    }
    _ => return t == gt,
  };
  generic_match(generics, *t, *gt)
}

#[derive(Copy, Clone)]
pub enum SymbolDef {
  Fun(Ap<FunctionDefinition>),
  Glob(Ap<GlobalDefinition>),
}

#[derive(Copy, Clone)]
pub struct ConcreteFunction {
  pub def : SymbolDef,
  pub concrete_signature : Ap<FunctionSignature>,
}

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  new_module_id : ModuleId,
  import_types : &'a [&'a TypeInfo],
  new_module : &'a mut TypeInfo,
  generic_bindings : HashMap<GenericId, Type>,
  function_results : Vec<ConcreteFunction>,
  global_results : Vec<SymbolDef>,
}

impl <'a> TypeDirectory<'a> {
  pub fn new(
    new_module_id : ModuleId,
    import_types : &'a [&'a TypeInfo],
    new_module : &'a mut TypeInfo) -> Self
  {
    TypeDirectory{
      new_module_id, import_types, new_module,
      generic_bindings: HashMap::new(),
      function_results: vec![],
      global_results: vec![],
    }
  }

  pub fn create_type_def(&mut self, def : Ap<TypeDefinition>) {
    self.new_module.type_defs.insert(def.name, def);
  }

  pub fn create_global(&mut self, def : Ap<GlobalDefinition>) {
    self.new_module.globals.insert(def.name, def);
  }

  pub fn create_function(&mut self, def : Ap<FunctionDefinition>) {
    self.new_module.functions.insert(def.id, def);
  }

  pub fn find_global_local(&mut self, name : &str) -> &[SymbolDef]
  {
    self.global_results.clear();
    self.new_module.find_global(name, true, &mut self.global_results);
    self.global_results.as_slice()
  }

  pub fn find_global(&mut self, name : &str) -> &[SymbolDef]
  {
    self.global_results.clear();
    self.new_module.find_global(name, true, &mut self.global_results);
    for m in self.import_types.iter().rev() {
      m.find_global(name, false, &mut self.global_results);
    }
    self.global_results.as_slice()
  }

  pub fn find_type_def(&self, name : &str) -> Option<Ap<TypeDefinition>> {
    self.new_module.find_type_def(name).or_else(||
      self.import_types.iter().rev().flat_map(|m| m.find_type_def(name)).next())
  }

  /// Return true if a local symbol already has this name and a matching argument list
  pub fn find_function_local(
    &mut self,
    name : &str, args : &[Type],
    arena : &Arena, gen : &mut UIDGenerator, 
  ) -> &[ConcreteFunction]
  {
    self.generic_bindings.clear();
    self.function_results.clear();
    self.new_module.find_function(name, args, true, arena, gen, &mut self.generic_bindings, &mut self.function_results);
    self.function_results.as_slice()
  }

  /// Returns a slice of all matching definitions.
  pub fn find_function(
    &mut self,
    name : &str, args : &[Type],
    arena : &Arena, gen : &mut UIDGenerator, 
  ) -> &[ConcreteFunction]
  {
    self.generic_bindings.clear();
    self.function_results.clear();
    self.new_module.find_function(name, args, true, arena, gen, &mut self.generic_bindings, &mut self.function_results);
    for m in self.import_types.iter().rev() {
      m.find_function(name, args, false, arena, gen, &mut self.generic_bindings, &mut self.function_results);
    }
    self.function_results.as_slice()
  }

  pub fn new_module_id(&self) -> ModuleId {
    self.new_module.module_id
  }

  pub fn find_module(&self, module_id : ModuleId) -> &TypeInfo {
    [&*self.new_module].iter()
      .chain(self.import_types.iter().rev())
      .find(|t| t.module_id == module_id)
      .expect("module not found")
  }

  pub fn get_function(&self, module_id : ModuleId, fid : FunctionId) -> Ap<FunctionDefinition> {
    self.find_module(module_id).get_function(fid)
  }
}


