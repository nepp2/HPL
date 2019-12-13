
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

static AAA : () = (); // TODO: Rename GenericId and Generic to PolyTypeId and Poly

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
  Def(RefStr, ModuleId),
  Array,
  Ptr,
  Abstract(AbstractType),
  Generic(GenericId),
}

/// This wrapper indicates that the type is monomorphic (not polymorphic), and may be unified.
/// The type may be abstract. Unresolved polymorphic elements should be converted
/// into abstract types before resolution.
#[derive(Clone, Debug, PartialEq)]
pub struct MonoType {
  inner : Type
}

pub enum MonoTypeError {
  WrongNumberOfTypeParameters,
  DefDoesNotExist(String),
}

impl MonoType {
  pub fn any() -> Self {
    MonoType { inner: Type::any() }
  }

  pub fn as_type(&self) -> &Type {
    &self.inner
  }

  pub fn sig_builder(&self) -> Option<SignatureBuilder<MonoType>> {
    if self.inner.content == Fun {
      Some(SignatureBuilder{types: self.inner.children.iter().cloned().map(|t| MonoType{ inner: t }).collect()})
    }
    else { None }
  }
}

impl Into<Type> for MonoType {
  fn into(self) -> Type {
    self.inner
  }
}

impl fmt::Display for MonoType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.inner)
  }
}

fn generic_replace(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, t : &mut Type) {
  if let Generic(gid) = &t.content {
    *t = generics.get(&gid).cloned().unwrap_or_else(||Type::any());
  }
  for t in t.children.iter_mut() {
    generic_replace(generics, gen, t);
  }
}

fn replace_polytypes(t : &Type, poly_map : &HashMap<GenericId, Type>) -> MonoType {
  if let Generic(gid) = &t.content {
    let t = poly_map.get(&gid).cloned().unwrap_or_else(||Type::any());
    return MonoType { inner: t };
  }
  let content = t.content.clone();
  let mut children = vec![];
  for c in t.children.iter() {
    children.push(replace_polytypes(c, poly_map).inner);
  }
  MonoType { inner: Type::new(content, children) }
}
  
fn generic_match(generics : &mut HashMap<GenericId, Type>, t : &Type, gt : &Type) -> bool {
  if let Generic(_) = &t.content { panic!("unexpected generic type") }
  if let Generic(gid) = &gt.content {
    if let Some(bound_type) = generics.get(&gid) {
      if let Some(t) = unify_types_internal(&t, bound_type) {
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
  else if let Abstract(at) = &gt.content { at.contains_type(t) }
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

pub struct SignatureBuilder<T> {
  types : Vec<T>,
}

impl <T : Into<Type>> SignatureBuilder<T> {
  pub fn new(return_type : T) -> Self {
    SignatureBuilder { types: vec![return_type] }
  }

  pub fn append_arg(&mut self, arg : T) {
    self.types.push(arg);
  }

  pub fn set_arg(&mut self, i : usize, t : T) {
    self.types[1 + i] = t;
  }

  pub fn set_return(&mut self, t : T) {
    self.types[0] = t;
  }

  pub fn args(&mut self) -> &mut [T] {
    &mut self.types[1..]
  }

  pub fn return_type(&mut self) -> &mut T {
    &mut self.types[0]
  }
}

impl Into<MonoType> for SignatureBuilder<MonoType> {
  fn into(self) -> MonoType {
    MonoType { inner: Type::new(Fun, self.types.into_iter().map(|t| t.into()).collect()) }
  }
}

impl Into<Type> for SignatureBuilder<Type> {
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
  
  pub fn new(content : TypeContent, children : Vec<Type>) -> Self {
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

  pub fn def(s : RefStr) -> Type {
    Type::new(Abstract(AbstractType::Def(s)), vec![])
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

  pub fn to_monotype(&self) -> MonoType {
    let content = match &self.content {
      Generic(gid) => Abstract(AbstractType::Any),
      _ => self.content.clone(),
    };
    let mut children = vec![];
    for c in self.children.iter() {
      children.push(c.to_monotype().inner);
    }
    MonoType { inner: Type::new(content, children) }
  }
}

#[derive(Clone, PartialEq, Debug)]
pub enum AbstractType {
  Float,
  Integer,
  Any,
  Def(RefStr),
}

impl AbstractType {
  pub fn contains_type(self, t : &Type) -> bool {
    match self {
      AbstractType::Float => t.float(),
      AbstractType::Integer => t.int(),
      AbstractType::Any => true,
      AbstractType::Def(_) => panic!(),
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
  pub polytypes : Vec<GenericId>,
  pub drop_function : Option<ResolvedGlobal>,
  pub clone_function : Option<ResolvedGlobal>,
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
  pub polymorphic : bool,
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
      Def(name, _) => write!(f, "{}", name),
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

pub fn incremental_unify(old : &MonoType, new : &mut MonoType) -> IncrementalUnifyResult {
  incremental_unify_internal(&old.inner, &mut new.inner)
}

fn incremental_unify_internal(old : &Type, new : &mut Type) -> IncrementalUnifyResult {
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
    match incremental_unify_internal(old, &mut new.children[i]) {
      ChangedOld => changed_old_type = true,
      EqualOrSubsumedByOld => (),
      Failure => return Failure,
    }
  }
  if changed_old_type { ChangedOld } else { EqualOrSubsumedByOld }
}

pub fn unify_types(a : &MonoType, b : &MonoType) -> Option<MonoType> {
  unify_types_internal(&a.inner, &b.inner).map(|inner| MonoType { inner })
}

fn unify_types_internal(a : &Type, b : &Type) -> Option<Type> {
  match can_unify_types_internal(a, b) {
    CanUnifyResult::CanUnify => {
      let mut t = b.clone();
      if incremental_unify_internal(a, &mut t) == IncrementalUnifyResult::Failure {panic!("bug in unify_types")}
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

pub fn can_unify_types(a : &MonoType, b : &MonoType) -> CanUnifyResult {
  can_unify_types_internal(&a.inner, &b.inner)
}

fn can_unify_types_internal(u : &Type, t : &Type) -> CanUnifyResult {
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
    match can_unify_types_internal(u, t) {
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
      module_id,
    }
  }

  pub fn find_global<'a>(
    &'a self,
    name : &str,
    results : &mut Vec<GlobalDefinition>) {
    for g in self.globals.iter() {
      if g.name.as_ref() == name {
        results.push(g.clone());
      }
    }
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
    self.type_defs.get(name)
  }
}

#[derive(Clone, Debug)]
pub struct ResolvedGlobal {
  /// TODO: this is very inefficient, because these are searched for and returned repeatedly
  pub def : GlobalDefinition,
  pub resolved_type : MonoType,
}

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  new_module_id : ModuleId,
  import_types : &'a [&'a TypeInfo],
  new_module : &'a mut TypeInfo,
  generic_bindings : HashMap<GenericId, Type>,
  global_results : Vec<GlobalDefinition>,
  resolved_results : Vec<ResolvedGlobal>,
  globals_cache : HashMap<RefStr, Vec<(GlobalDefinition, MonoType)>>,
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
      resolved_results: vec![],
      globals_cache: HashMap::new(),
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

  fn resolve_global(
    &mut self,
    name : &str,
    t : &MonoType,
    gen : &mut UIDGenerator,
    globals : &[(GlobalDefinition, MonoType)],
  )
      -> Result<&[ResolvedGlobal], MonoTypeError>
  {
    self.resolved_results.clear();
    for (g, monotype) in globals {
      if g.polymorphic {
        self.generic_bindings.clear();
        if generic_match(&mut self.generic_bindings, &t.inner, &g.type_tag) {
          let resolved_type = replace_polytypes(&g.type_tag, &self.generic_bindings);
          self.resolved_results.push(ResolvedGlobal { def: g.clone(), resolved_type });
        }
      }
      else {
        if let Some(t) = unify_types_internal(&t.inner, &g.type_tag) {
          self.resolved_results.push(ResolvedGlobal { def: g.clone(), resolved_type: monotype.clone() });
        }
      }
    }
    Ok(self.resolved_results.as_slice())
  }

  /// Returns a slice of all matching definitions
  pub fn find_global(
    &mut self,
    name : &str,
    t : &MonoType,
    gen : &mut UIDGenerator
  )
    -> Result<&[ResolvedGlobal], MonoTypeError>
  {
    if let Some(globals) = self.globals_cache.get(name) {
      self.resolve_global(name, t, gen, globals.as_slice())
    }
    else {
      self.global_results.clear();
      self.new_module.find_global(name, &mut self.global_results);
      for m in self.import_types.iter().rev() {
        m.find_global(name, &mut self.global_results);
      }
      let globals_cache = vec![];
      for g in self.global_results.drain(..) {
        globals_cache.push((g.clone(), g.type_tag.to_monotype()));
        self.globals_cache.insert(name.into(), globals_cache);
      }
      self.resolve_global(name, t, gen, self.globals_cache.get(name).unwrap().as_slice())
    }
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


