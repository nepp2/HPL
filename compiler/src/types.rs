
use std::fmt;
use itertools::Itertools;

use crate::error::TextLocation;
use crate::expr::UIDGenerator;
use crate::structure::{
  NodeId, SymbolId, TypeKind,
};
use crate::arena::{ Arena, Ap };

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GenericId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for GenericId { fn from(v : u64) -> Self { GenericId(v) } }

pub struct TypeInfo {
  pub type_defs : HashMap<Ap<str>, Ap<TypeDefinition>>,
  pub globals : Vec<Ap<GlobalDefinition>>,
  pub poly_functions : Vec<Ap<PolyFunctionDef>>,
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

#[derive(Clone, Copy, Debug, PartialEq)]
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

impl Type {
  pub fn signature(self) -> Option<Ap<FunctionSignature>> {
    match self {
      Type::Fun(sig) => Some(sig),
      _ => None,
    }
  }
}

#[derive(Copy, Clone, Debug)]
pub struct Symbol {
  pub id : SymbolId,
  pub name : Ap<str>,
  pub loc : TextLocation,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDefinition {
  pub name : Ap<str>,
  pub fields : Ap<[(Symbol, Type)]>,
  pub kind : TypeKind,
  pub drop_function : Option<Ap<ConcreteGlobal>>,
  pub clone_function : Option<Ap<ConcreteGlobal>>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone)]
pub enum FunctionImplementation {
  Normal{body: NodeId, name_for_codegen: Ap<str>, args : Vec<Symbol> },
  CFunction,
  Intrinsic,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Ap<[Type]>,
}

/// The initialiser for the global
#[derive(Debug, Clone, Copy)]
pub enum GlobalInit {
  Function(Ap<FunctionInit>),
  Expression(NodeId),
  Intrinsic,
  CBind,
}

#[derive(Debug, Clone, Copy)]
pub struct FunctionInit {
  pub body: NodeId,
  pub name_for_codegen: Ap<str>,
  pub args : Ap<[Symbol]>,
}

#[derive(Clone, Copy, Debug)]
pub struct GlobalDefinition {
  pub module_id : ModuleId,
  pub name : Ap<str>,
  pub type_tag : Type,
  pub initialiser : GlobalInit,
  pub loc : TextLocation,
}

impl GlobalDefinition {
  pub fn codegen_name(&self) -> Option<&str> {
    match &self.initialiser {
      GlobalInit::Function(f) => Some(&f.name_for_codegen),
      GlobalInit::CBind | GlobalInit::Expression(_) => Some(&self.name),
      _ => None,
    }
  }
}

#[derive(Copy, Clone)]
pub struct PolyFunctionDef {
  pub global : Ap<GlobalDefinition>,
  pub poly_signature : Ap<FunctionSignature>,
  pub generics : Ap<[GenericId]>,
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
      globals: vec![],
      poly_functions: vec![],
      module_id,
    }
  }

  pub fn find_global(
    &self,
    name : &str,
    t : Type,
    arena : &Arena,
    gen : &mut UIDGenerator, 
    generics : &mut HashMap<GenericId, Type>,
    results : &mut Vec<ConcreteGlobal>) {
    for g in self.globals.iter() {
      if g.name.as_ref() == name && unknown_match(t, g.type_tag) {
        results.push(ConcreteGlobal { def: *g, concrete_type: g.type_tag });
      }
    }
    for def in self.poly_functions.iter() {
      if def.global.name.as_ref() == name {
        generics.clear();
        let matched = generic_match(generics, t, Type::Fun(def.poly_signature));
        if matched && generics.len() == def.generics.len() {
          let sig = concrete_signature(arena, gen, def, generics);
          let def = def.global;
          results.push(ConcreteGlobal { def, concrete_type: Type::Fun(sig) });
        }
      }
    }
  }

  pub fn find_type_def(&self, name : &str) -> Option<Ap<TypeDefinition>> {
    self.type_defs.get(name).cloned()
  }
}

fn unknown_match(u : Type, t : Type) -> bool {
  match (u, t) {
    (Type::Unknown, _) => true,
    (Type::Ptr(u), Type::Ptr(t)) => unknown_match(*u, *t),
    (Type::Array(u), Type::Array(t)) => unknown_match(*u, *t),
    (Type::Fun(u_sig), Type::Fun(t_sig)) => {
      if u_sig.args.len() != t_sig.args.len() { return false }
      for (u, t) in u_sig.args.iter().zip(t_sig.args.iter()) {
        if !unknown_match(*u, *t) {
          return false;
        }
      }
      unknown_match(u_sig.return_type, t_sig.return_type)
    }
    // enumerate all the options so the compiler complains if a new Type is added
    (Type::Generic(_), _) => panic!("unexpected generic type"),
    (Type::Def(_), _) | (Type::Prim(_), _) => u == t,
    (Type::Ptr(_), _) | (Type::Array(_), _) | (Type::Fun(_), _) => false,
  }
}


fn concrete_signature(arena : &Arena, gen : &mut UIDGenerator, def : &PolyFunctionDef, generic_map : &mut HashMap<GenericId, Type>) -> Ap<FunctionSignature> {
  let sig = def.poly_signature;
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
    Type::Fun(sig) => {
      let mut args = arena.alloc_slice_mut(&sig.args);
      for t in args.iter_mut() {
        *t = generic_replace(arena, generics, gen, *t);
      }
      let args = args.into_ap();
      let return_type = generic_replace(arena, generics, gen, sig.return_type);
      let sig = FunctionSignature{ args, return_type };
      Type::Fun(arena.alloc(sig))
    }
    Type::Generic(gid) => {
      *generics.get(&gid).unwrap()
    }
    Type::Def(_) | Type::Prim(_) => t,
    Type::Unknown => panic!("unexpected unknown"),
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, t : Type, gt : Type) -> bool {
  match (t, gt) {
    (Type::Unknown, _) => true,
    (Type::Ptr(t), Type::Ptr(gt)) => generic_match(generics, *t, *gt),
    (Type::Array(t), Type::Array(gt)) => generic_match(generics, *t, *gt),
    (Type::Fun(t_sig), Type::Fun(gt_sig)) => {
      if t_sig.args.len() != gt_sig.args.len() { return false }
      for (t, gt) in t_sig.args.iter().zip(gt_sig.args.iter()) {
        if !generic_match(generics, *t, *gt) {
          return false;
        }
      }
      generic_match(generics, t_sig.return_type, gt_sig.return_type)
    },
    (t, Type::Generic(gid)) => {
      if let Some(bound_type) = generics.get(&gid) {
        t == *bound_type
      }
      else {
        generics.insert(gid, t);
        true
      }
    }
      // enumerate all the options so the compiler complains if a new Type is added
    (Type::Generic(_), _) => panic!("unexpected generic type"),
    (Type::Def(_), _) | (Type::Prim(_), _) => t == gt,
    (Type::Ptr(_), _) | (Type::Array(_), _) | (Type::Fun(_), _) => false,
  }
}

#[derive(Copy, Clone, Debug)]
pub struct ConcreteGlobal {
  pub def : Ap<GlobalDefinition>,
  pub concrete_type : Type,
}

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  new_module_id : ModuleId,
  import_types : &'a [&'a TypeInfo],
  new_module : &'a mut TypeInfo,
  generic_bindings : HashMap<GenericId, Type>,
  global_results : Vec<ConcreteGlobal>,
}

// TODO: A lot of these functions are slow because they iterate through everything.
// This could probably be improved with some caching, although any caching needs to
// be wary of new symbols being added.
impl <'a> TypeDirectory<'a> {
  pub fn new(
    new_module_id : ModuleId,
    import_types : &'a [&'a TypeInfo],
    new_module : &'a mut TypeInfo) -> Self
  {
    TypeDirectory{
      new_module_id, import_types, new_module,
      generic_bindings: HashMap::new(),
      global_results: vec![],
    }
  }

  pub fn create_type_def(&mut self, def : Ap<TypeDefinition>) {
    self.new_module.type_defs.insert(def.name, def);
  }

  pub fn create_global(&mut self, def : Ap<GlobalDefinition>) {
    self.new_module.globals.push(def);
  }

  /// Returns a slice of all matching definitions
  pub fn find_global(
    &mut self,
    name : &str,
    t : Type,
    arena : &Arena,
    gen : &mut UIDGenerator
  )
      -> &[ConcreteGlobal]
  {
    self.generic_bindings.clear();
    self.global_results.clear();
    self.new_module.find_global(name, t, arena, gen, &mut self.generic_bindings, &mut self.global_results);
    for m in self.import_types.iter().rev() {
      m.find_global(name, t, arena, gen, &mut self.generic_bindings, &mut self.global_results);
    }
    self.global_results.as_slice()
  }

  pub fn find_type_def(&self, name : &str) -> Option<Ap<TypeDefinition>> {
    self.new_module.find_type_def(name).or_else(||
      self.import_types.iter().rev().flat_map(|m| m.find_type_def(name)).next())
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
}


