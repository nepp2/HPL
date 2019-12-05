
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GlobalId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for GenericId { fn from(v : u64) -> Self { GenericId(v) } }
impl From<u64> for GlobalId { fn from(v : u64) -> Self { GlobalId(v) } }

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

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
  pub content : TypeContent,
  pub children : Vec<Type>,
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

pub struct SignatureBuilder {
  types : Vec<Type>,
}

impl SignatureBuilder {
  pub fn new(return_type : Type) -> Self {
    SignatureBuilder { types: vec![return_type] }
  }

  pub fn append_arg(&mut self, arg : Type) {
    self.types.push(arg);
  }

  pub fn set_arg(&mut self, i : usize, t : Type) {
    self.types[1 + i] = t;
  }

  pub fn set_return(&mut self, t : Type) {
    self.types[0] = t;
  }

  pub fn args(&mut self) -> &mut [Type] {
    &mut self.types[1..]
  }

  pub fn return_type(&mut self) -> &mut Type {
    &mut self.types[0]
  }
}

impl Into<Type> for SignatureBuilder {
  fn into(self) -> Type {
    Type::new(Fun, self.types)
  }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct FunctionSignature<'a> {
  pub return_type : &'a Type,
  pub args : &'a [Type],
}

impl Type {
  
  fn new(content : TypeContent, children : Vec<Type>) -> Self {
    Type { content, children }
  }
  
  pub fn any() -> Self {
    Type::new(Abstract(AbstractType::Any), vec![])
  }

  pub fn sig(&self) -> Option<FunctionSignature> {
    if self.content == Fun {
      Some(FunctionSignature{return_type: &self.children[0], args: &self.children[1..]})
    }
    else { None }
  }

  pub fn sig_builder(&self) -> Option<SignatureBuilder> {
    if self.content == Fun {
      Some(SignatureBuilder{types: self.children.clone()})
    }
    else { None }
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
    Type { content: Array, children: vec![t]}
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
  pub id : GlobalId,
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

impl  fmt::Display for AbstractType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      AbstractType::Any => write!(f, "@Unknown"),
      _ => write!(f, "{:?}", self),
    }
  }
}

impl  fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.content {
      Fun => {
        let sig = self.sig().unwrap();
        write!(f, "fun({}) => {}", 
          sig.args.iter().join(", "), sig.return_type)
      }
      Def(name) => write!(f, "{}", name),
      Array => write!(f, "array({})", self.array().unwrap()),
      Ptr => write!(f, "ptr({})", self.ptr().unwrap()),
      Prim(t) => write!(f, "{:?}", t),
      Generic(id) => write!(f, "@Generic({})", id),
      Abstract(abs) => write!(f, "{}", abs),
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
    for t in self.children.iter_mut() {
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

#[derive(PartialEq)]
pub enum IncrementalUnifyResult {
  ChangedOld,
  EqualOrSubsumedByOld,
  Failure,
}

pub fn incremental_unify(old : &Type, new : &mut Type) -> IncrementalUnifyResult {
  use IncrementalUnifyResult::*;
  if let Generic(_) = &old.content { return Failure }
  if old.content != new.content {
    if let Abstract(abs_old) = &old.content {
      if abs_old.contains_type(new) { return ChangedOld }
    }
    if let Abstract(abs_new) = &new.content {
      if abs_new.contains_type(old) {
        *new = old.clone();
        return EqualOrSubsumedByOld;
      }
    }
    return Failure;
  }
  if old.children.len() != new.children.len() { return Failure }
  let mut changed_old_type = false;
  for (i, old) in old.children.iter().enumerate() {
    match incremental_unify(old, &mut new.children[i]) {
      ChangedOld => changed_old_type = true,
      EqualOrSubsumedByOld => (),
      Failure => return Failure,
    }
  }
  if changed_old_type { ChangedOld } else { EqualOrSubsumedByOld }
}

pub fn unify_types(a : &Type, b : &Type) -> Option<Type> {
  match can_unify_types(a, b) {
    CanUnifyResult::CanUnify => {
      let mut t = b.clone();
      if incremental_unify(a, &mut t) == IncrementalUnifyResult::Failure {panic!("bug in unify_types")}
      Some(t)
    }
    CanUnifyResult::AlreadyEqual => Some(a.clone()),
    CanUnifyResult::CannotUnify => None,
  }
}

#[derive(Clone, Copy, PartialEq)]
pub enum CanUnifyResult {
  CanUnify, AlreadyEqual, CannotUnify
}

impl CanUnifyResult {
  pub fn success(self) -> bool { self != CanUnifyResult::CannotUnify }
}

pub fn can_unify_types(u : &Type, t : &Type) -> CanUnifyResult {
  use CanUnifyResult::*;
  if let Generic(_) = &u.content { return CannotUnify }
  if u.content != t.content {
    if let Abstract(au) = &u.content {
      if au.contains_type(t) { return CanUnify }
    }
    if let Abstract(at) = &t.content {
      if at.contains_type(u) { return CanUnify }
    }
    return CannotUnify;
  }
  if u.children.len() != t.children.len() { return CannotUnify }
  let mut unification_required = false;
  for (u, t) in u.children.iter().zip(t.children.iter()) {
    match can_unify_types(u, t) {
      CanUnify => unification_required = true,
      CannotUnify => return CannotUnify,
      AlreadyEqual => (),
    }
  }
  if unification_required { CanUnify } else { AlreadyEqual }
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
      if g.name.as_ref() == name {
        if let Some(t) = unify_types(t, &g.type_tag) {
          results.push(ConcreteGlobal { def: g.clone(), concrete_type: t });
        }
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

fn generic_replace(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, t : &mut Type) {
  if let Generic(gid) = &t.content {
    *t = generics.get(&gid).unwrap().clone();
  }
  for t in t.children.iter_mut() {
    generic_replace(generics, gen, t);
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, t : &Type, gt : &Type) -> bool {
  if let Generic(_) = &t.content { panic!("unexpected generic type") }
  if let Abstract(_) = &gt.content { panic!("unexpected abstract type") }
  if let Generic(gid) = &gt.content {
    if let Some(bound_type) = generics.get(&gid) {
      if let Some(t) = unify_types(&t, bound_type) {
        generics.insert(*gid, t);
        true
      }
      else { false }
    }
    else {
      generics.insert(*gid, t.clone());
      true
    }    
  }
  else if let Abstract(at) = &t.content { at.contains_type(gt) }
  else {
    if t.content != gt.content { return false }
    if t.children.len() != gt.children.len() { return false }
    for (t, gt) in t.children.iter().zip(gt.children.iter()) {
      if !generic_match(generics, t, gt) {
        return false;
      }
    }
    true
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

  pub fn get_global(&mut self, id : GlobalId) -> &mut GlobalDefinition {
    self.new_module.globals.iter_mut().find(|def| def.id == id).unwrap()
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


