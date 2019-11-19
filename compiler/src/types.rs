
use std::fmt;
use itertools::Itertools;
use std::hash::Hash;

use crate::error::TextLocation;
use crate::expr::{ RefStr, UIDGenerator};
use crate::structure::{
  NodeId, Symbol, TypeKind, GlobalType,
};

use std::collections::HashMap;
use bimap::BiMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct FunctionId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GenericId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SigId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct DefId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for FunctionId { fn from(v : u64) -> Self { FunctionId(v) } }
impl From<u64> for GenericId { fn from(v : u64) -> Self { GenericId(v) } }
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
    get_id(&mut self.type_definition_names, gen, name)
  }

  pub fn signature_id(&mut self, gen : &mut UIDGenerator, sig : FunctionSignature) -> SigId {
    get_id(&mut self.signatures, gen, sig)
  }

  pub fn type_id(&mut self, gen : &mut UIDGenerator, t : Type) -> TypeId {
    get_id(&mut self.types, gen, t)
  }

  pub fn ptr_to_type(&mut self, gen : &mut UIDGenerator, t : Type) -> Type {
    Type::Ptr(self.type_id(gen, t))
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
  F64, F32,
  I64, I32,
  U64, U32, U16, U8,
  Bool,
  Generic(GenericId),
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
      // "any" => Some(Type::Dynamic),
      "()" => Some(Type::Void),
      // "" => Some(Type::Dynamic),
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


pub struct ModuleInfo {
  pub id : ModuleId,
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub functions : HashMap<FunctionId, FunctionDefinition>,
  pub globals : HashMap<RefStr, GlobalDefinition>,
  pub types : Types,
}

pub enum FindFunctionResult {
  ConcreteFunction(FunctionId),
  GenericInstance(FunctionId, HashMap<GenericId, Type>),
}

impl ModuleInfo {
  pub fn new(gen : &mut UIDGenerator) -> ModuleInfo {
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

  pub fn get_function(&self, fid : FunctionId) -> &FunctionDefinition {
    self.functions.get(&fid).unwrap()
  }

  pub fn find_function(&self, name : &str, args : &[Type]) -> Option<FindFunctionResult> {
    let r = self.functions.values().find(|def| {
      def.generics.is_empty() && def.name_in_code.as_ref() == name && {
        let sig = self.types.signature(def.signature);
        args == sig.args.as_slice()
      }
    });
    if let Some(def) = r {
      return Some(FindFunctionResult::ConcreteFunction(def.id));
    }
    let mut generics = HashMap::new();
    let r = self.functions.values().find(|def| {
      (!def.generics.is_empty()) && def.name_in_code.as_ref() == name && {
        let sig = self.types.signature(def.signature);
        let matched = generic_match_sig(&mut generics, &self.types, args, def, sig);
        if !matched {
          generics.clear();
        }
        matched
      }
    });
    if let Some(def) = r {
      Some(FindFunctionResult::GenericInstance(def.id, generics))
    }
    else {
      None
    }
  }

  pub fn concrete_function(&mut self, gen : &mut UIDGenerator, r : FindFunctionResult) -> FunctionId {
    match r {
      FindFunctionResult::ConcreteFunction(fid) => fid,
      FindFunctionResult::GenericInstance(fid, generics) => {
        let mut sig = self.types.signature(self.get_function(fid).signature).clone();
        for t in sig.args.iter_mut() {
          *t = generic_replace(&generics, gen, &mut self.types, *t);
        }
        sig.return_type = generic_replace(&generics, gen, &mut self.types, sig.return_type);
        let signature = self.types.signature_id(gen, sig);
        let def = self.get_function(fid);
        let def = FunctionDefinition {
          id: FunctionId(gen.next()),
          module_id: self.id,
          name_in_code: def.name_in_code.clone(),
          signature,
          generics: vec![],
          implementation: def.implementation.clone(),
          loc: def.loc,
        };
        let fid = def.id;
        self.functions.insert(fid, def);
        fid
      },
    }
  }
}

fn generic_replace(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, types : &mut Types, t : Type) -> Type {
  fn generic_replace_id(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, types : &mut Types, t : TypeId) -> TypeId {
    let t = types.get(t);
    let t = generic_replace(generics, gen, types, t);
    types.type_id(gen, t)
  }
  match t {
    Type::Ptr(t) => Type::Ptr(generic_replace_id(generics, gen, types, t)),
    Type::Array(t) => Type::Array(generic_replace_id(generics, gen, types, t)),
    Type::Generic(gid) => *generics.get(&gid).unwrap(),
    _ => return t,
  }
}

fn generic_match_sig(
  generics : &mut HashMap<GenericId, Type>, types : &Types,
  args : &[Type], def : &FunctionDefinition, sig : &FunctionSignature)
    -> bool
{
  args.len() == sig.args.len() && {
    for (t, gt) in args.iter().zip(sig.args.iter()) {
      if !generic_match(generics, types, *t, *gt) {
        return false;
      }
    }
    generics.len() == def.generics.len()
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, types : &Types, t : Type, gt : Type) -> bool {
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
  generic_match(generics, types, types.get(t), types.get(gt))
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
  Normal{body: NodeId, name_for_codegen: RefStr, args : Vec<Symbol> },
  CFunction,
  Intrinsic,
}

#[derive(Debug, Clone)]
pub struct FunctionDefinition {
  pub id : FunctionId,
  pub module_id : ModuleId,
  pub name_in_code : RefStr,
  pub signature : SigId,
  pub generics : Vec<GenericId>,
  pub implementation : FunctionImplementation,
  pub loc : TextLocation,
}

impl FunctionDefinition {
  pub fn codegen_name(&self) -> Option<&str> {
    match &self.implementation {
      FunctionImplementation::Normal{ name_for_codegen, .. } => Some(name_for_codegen),
      FunctionImplementation::CFunction => Some(&self.name_in_code),
      FunctionImplementation::Intrinsic => None,
    }
  }
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

#[derive(Clone)]
pub struct GlobalDefinition {
  pub module_id : ModuleId,
  pub name : RefStr,
  pub type_tag : Type,
  pub global_type : GlobalType,
  pub loc : TextLocation,
}
