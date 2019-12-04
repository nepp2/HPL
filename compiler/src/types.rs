
use std::fmt;
use itertools::Itertools;

use crate::error::TextLocation;
use crate::expr::{UIDGenerator, RefStr};
use crate::structure::{
  NodeId, TypeKind, Symbol
};

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GenericId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for GenericId { fn from(v : u64) -> Self { GenericId(v) } }

pub struct TypeInfo {
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub globals : Vec<GlobalDefinition>,
  pub poly_functions : Vec<PolyFunctionDef>,
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

use PType::*;

// #[derive(Clone, Debug, PartialEq)]
// pub enum Type {
//   /// Primitive type (e.g. int, float, bool, etc)
//   Prim(PType),
//   Fun(Box<FunctionSignature>),
//   Def(RefStr),
//   Array(Vec<Type>),
//   Ptr(Vec<Type>),
//   Abstract(AbstractType),
//   Generic(GenericId),
// }

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
  content : TypeContent,
  children : Vec<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeContent {
  /// Primitive type (e.g. int, float, bool, etc)
  Prim(PType),
  Fun,
  Def(RefStr),
  Array,
  Ptr,
  Abstract(AbstractType),
  Generic(GenericId),
}

use TypeContent::*;

impl Into<Type> for PType {
  fn into(self) -> Type {
    Type::new(Prim(self), vec![])
  }
}

impl Into<Type> for AbstractType {
  fn into(self) -> Type {
    Type::new(Abstract(self), vec![])
  }
}

impl Into<Type> for GenericId {
  fn into(self) -> Type {
    Type::new(Generic(self), vec![])
  }
}
impl Type {

  fn new(content : TypeContent, children : Vec<Type>) -> Self {
    Type { content, children }
  }

  pub fn sig(&self) -> Option<(&[Type], &Type)> {
    if self.content == Fun {
      return Some((&self.children[1..], &self.children[0]));
    }
    None
  }

  pub fn def(s : RefStr) -> Type {
    Type::new(Def(s), vec![])
  }

  pub fn ptr_to(t : Type) -> Self {
    Type::new(Ptr, vec![t])
  }

  pub fn ptr(&self) -> Option<&Type> {
    if self.content == Ptr {
      if let [t] = self.children.as_slice() {
        return Some(t);
      }
    }
    None
  }

  pub fn array(&self) -> Option<&Type> {
    if self.content == Array {
      if let [t] = self.children.as_slice() {
        return Some(t);
      }
    }
    None
  }

  pub fn array_of(t : Type) -> Self {
    Type { content: Ptr, children: vec![t]}
  }

  pub fn children(&self) -> &[Type] {
    self.children.as_slice()
  }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AbstractType {
  Float,
  Integer,
  Any,
}

impl AbstractType {
  pub fn contains_type(self, t : &Type) -> bool {
    match self {
      AbstractType::Float => t.float(),
      AbstractType::Integer => t.int(),
      AbstractType::Any => true,
    }
  }

  pub fn matches_type(self, t : &Type) -> bool {
    if let Abstract(a) = &t.content {
      self == *a
    }
    else {
      self.contains_type(t)
    }
  }

  pub fn default_type(self) -> Option<Type> {
    match self {
      AbstractType::Float => Some(PType::F64.into()),
      AbstractType::Integer => Some(PType::I64.into()),
      AbstractType::Any => None,
    }
  }
}

#[derive(Clone, Debug)]
pub struct TypeDefinition {
  pub name : RefStr,
  pub fields : Vec<(Symbol, Type)>,
  pub kind : TypeKind,
  pub drop_function : Option<ConcreteGlobal>,
  pub clone_function : Option<ConcreteGlobal>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone)]
pub enum FunctionImplementation {
  Normal{body: NodeId, name_for_codegen: RefStr, args : Vec<Symbol> },
  CFunction,
  Intrinsic,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Vec<Type>,
}

/// The initialiser for the global
#[derive(Debug, Clone)]
pub enum GlobalInit {
  Function(FunctionInit),
  Expression(NodeId),
  Intrinsic,
  CBind,
}

#[derive(Debug, Clone)]
pub struct FunctionInit {
  pub body: NodeId,
  pub name_for_codegen: RefStr,
  pub args : Vec<Symbol>,
}

#[derive(Clone, Debug)]
pub struct GlobalDefinition {
  pub module_id : ModuleId,
  pub name : RefStr,
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

#[derive(Clone)]
pub struct PolyFunctionDef {
  pub global : GlobalDefinition,
  pub generics : Vec<GenericId>,
}

impl  fmt::Display for GenericId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let GenericId(id) = *self;
    write!(f, "{:X}", id)
  }
}

impl  fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.content {
      Fun => {
        let (args, return_type) = self.sig().unwrap();
        write!(f, "fun({}) => {}", 
          args.iter().join(", "), return_type)
      }
      Def(name) => write!(f, "{}", name),
      Array => write!(f, "array({})", self.ptr().unwrap()),
      Ptr => write!(f, "ptr({})", self.array().unwrap()),
      Prim(t) => write!(f, "{:?}", t),
      Generic(id) => write!(f, "@Generic({})", id),
      Abstract(tc) => write!(f, "{:?}", tc),
    }
  }
}

impl  Type {

  pub fn is_concrete(&self) -> bool {
    match self.content {
      Abstract(_) => return false,
      Generic(_) => return false,
      _ => (),
    }
    for t in self.children.iter() {
      if !t.is_concrete() { return false }
    }
    true
  }

  pub fn to_concrete(&mut self) -> Result<(), ()> {
    match self.content {
      Abstract(at) => {
        if let Some(t) = at.default_type() {
          *self = t;
        }
        else {
          return Err(());
        }
      }
      Generic(_) => return Err(()),
      _ => (),
    };
    for t in self.children.iter() {
      t.to_concrete()?;
    }
    Ok(())
  }

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
      "()" => Void,
      _ => return None,
    };
    Some(pt.into())
  }

  pub fn float(&self) -> bool {
    match self.content { Prim(F32) | Prim(F64) => true, _ => false }
  }

  pub fn unsigned_int(&self) -> bool {
    match self.content { Prim(U64) | Prim(U32) | Prim(U16) | Prim(U8) => true, _ => false }
  }

  pub fn signed_int(&self) -> bool {
    match self.content { Prim(I64) | Prim(I32) => true, _ => false }
  }

  pub fn int(&self) -> bool {
    self.signed_int() || self.unsigned_int()
  }

  pub fn number(&self) -> bool {
    self.int() || self.float()
  }

  pub fn pointer(&self) -> bool {
    match self.content { Ptr | Fun => true, _ => false }
  }
}

pub fn unify_types(a : &Type, b : &mut Type) -> Option<Type> {
  if let Abstract(abs_a) = &a.content {
    if abs_a.matches_type(b) { Some(b.clone()) } else { None }
  }
  else if let Abstract(abs_b) = &b.content {
    if abs_b.matches_type(a) { Some(a.clone()) } else { None }
  }
  else {
    match &a.content {
      Ptr | Array | Fun | Def(_) | Prim(_) => {
        if a.content != b.content {
          return None;
        }
      }
      Abstract(_) => panic!("impossible state"),
      Generic(_) => panic!("unexpected generic type"),
    }
    if a.children.len() != b.children.len() { return None }
    let mut children = vec![];
    for (o, t) in a.children.iter().zip(b.children.iter_mut()) {
      children.push(unify_types(o, t)?);
    }
    Some(Type::new(a.content.clone(), children))
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

  pub fn find_global<'a>(
    &'a self,
    name : &str,
    t : &Type,
    gen : &mut UIDGenerator, 
    generics : &mut HashMap<GenericId, Type>,
    results : &mut Vec<ConcreteGlobal>) {
    for g in self.globals.iter() {
      if g.name.as_ref() == name && abstract_match(t, &g.type_tag) {
        results.push(ConcreteGlobal { def: g.clone(), concrete_type: g.type_tag.clone() });
      }
    }
    'outer: for def in self.poly_functions.iter() {
      if def.global.name.as_ref() == name {
        generics.clear();
        let matched = generic_match(generics, t, &def.global.type_tag);
        if matched && generics.len() == def.generics.len() {
          for t in generics.values_mut() {
            if let Err(()) = t.to_concrete() {
              continue 'outer;
            }
          }
          let mut concrete_type = def.global.type_tag.clone();
          generic_replace(generics, gen, &mut concrete_type);
          let def = def.global.clone();
          results.push(ConcreteGlobal { def, concrete_type });
        }
      }
    }
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
    self.type_defs.get(name)
  }
}

fn abstract_match(u : &Type, t : &Type) -> bool {
  if let Abstract(au) = &u.content {
    return au.matches_type(t);
  }
  if let Abstract(at) = &t.content {
    return at.matches_type(u);
  }
  if u.content != t.content {
    return false;
  }
  if u.children.len() != t.children.len() { return false }
  for (u, t) in u.children.iter().zip(t.children.iter()) {
    if !abstract_match(u, t) {
      return false;
    }
  }
  true
}

fn generic_replace(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, t : &mut Type) {
  if let Generic(gid) = &t.content {
    *t = generics.get(&gid).unwrap().clone();
  }
  for t in t.children.iter_mut() {
    generic_replace(generics, gen, t);
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, t : &Type, gt : &Type) -> bool {
  match (&t.content, &gt.content) {
    (Generic(_), _) => panic!("unexpected generic type"),
    (t, Generic(gid)) => {
      if let Some(bound_type) = generics.get(&gid) {
        if let Some(unified_t) = unify_types(&t, bound_type) {
          generics.insert(*gid, unified_t);
          true
        }
        else {
          false
        }
      }
      else {
        generics.insert(*gid, t.clone());
        true
      }
    }
    (Abstract(at), gt) => at.contains_type(gt),
    (Ptr(t), Ptr(gt)) => generic_match(generics, t, gt),
    (Array(t), Array(gt)) => generic_match(generics, t, gt),
    (Fun(t_sig), Fun(gt_sig)) => {
      if t_sig.args.len() != gt_sig.args.len() { return false }
      for (t, gt) in t_sig.args.iter().zip(gt_sig.args.iter()) {
        if !generic_match(generics, t, gt) {
          return false;
        }
      }
      generic_match(generics, &t_sig.return_type, &gt_sig.return_type)
    },
      // enumerate all the options so the compiler complains if a new Type is added
    (Def(_), _) | (Prim(_), _) => t == gt,
    (Ptr(_), _) | (Array(_), _) | (Fun(_), _) => false,
  }
}

#[derive(Clone, Debug)]
pub struct ConcreteGlobal {
  /// TODO: this is very inefficient, because these are searched for and returned repeatedly
  pub def : GlobalDefinition,
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

  pub fn create_type_def(&mut self, def : TypeDefinition) {
    self.new_module.type_defs.insert(def.name.clone(), def);
  }

  pub fn create_global(&mut self, def : GlobalDefinition) {
    self.new_module.globals.push(def);
  }

  /// Returns a slice of all matching definitions
  pub fn find_global(
    &mut self,
    name : &str,
    t : &Type,
    gen : &mut UIDGenerator
  )
      -> &[ConcreteGlobal]
  {
    self.generic_bindings.clear();
    self.global_results.clear();
    self.new_module.find_global(name, t, gen, &mut self.generic_bindings, &mut self.global_results);
    for m in self.import_types.iter().rev() {
      m.find_global(name, t, gen, &mut self.generic_bindings, &mut self.global_results);
    }
    self.global_results.as_slice()
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
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


