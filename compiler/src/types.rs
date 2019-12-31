
use std::fmt;
use itertools::Itertools;

use crate::error::TextLocation;
use crate::expr::RefStr;
use crate::structure::{
  NodeId, TypeKind, Symbol
};

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct PolyTypeId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct GlobalId(u64);

impl From<u64> for ModuleId { fn from(v : u64) -> Self { ModuleId(v) } }
impl From<u64> for PolyTypeId { fn from(v : u64) -> Self { PolyTypeId(v) } }
impl From<u64> for GlobalId { fn from(v : u64) -> Self { GlobalId(v) } }

pub struct TypeInfo {
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub globals : HashMap<GlobalId, GlobalDefinition>,
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

impl PType {
  pub fn from_string(s : &str) -> Option<PType> {
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
    Some(pt)
  }
}

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
  Polytype(PolyTypeId),
}

/// This wrapper indicates that the type is monomorphic (not polymorphic), and may be unified.
/// The type may be abstract. Unresolved polymorphic elements should be converted
/// into abstract types before resolution.
#[derive(Clone, Debug, PartialEq)]
pub struct MonoType {
  inner : Type
}

impl MonoType {
  fn new(inner : Type) -> Self {
    MonoType { inner }
  }

  pub fn any() -> Self {
    MonoType::new(Type::any())
  }

  pub fn as_type(&self) -> &Type {
    &self.inner
  }

  pub fn try_harden_literal(&self) -> Option<MonoType> {
    if let Abstract(ab) = &self.inner.content {
      if let Some(default) = ab.default_type() {
        return Some(MonoType::new(default));
      }
    }
    None
  }

  pub fn array_of(self) -> Self {
    MonoType::new(self.inner.array_of())
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

fn polytype_replace(polytypes : &HashMap<PolyTypeId, MonoType>, pt : &Type) -> MonoType {
  fn polytype_replace_internal(polytypes : &HashMap<PolyTypeId, MonoType>, t : &mut Type) {
    if let Polytype(gid) = &t.content {
      *t = polytypes.get(&gid).cloned().unwrap_or_else(||MonoType::any()).inner;
    }
    for t in t.children.iter_mut() {
      polytype_replace_internal(polytypes, t);
    }
  }
  let mut pt = pt.clone();
  polytype_replace_internal(polytypes, &mut pt);
  MonoType{ inner: pt }
}

/// `pt` may be a polytype. It will be treated like `Abstract(Any)`.
fn polytype_match(polytypes : &mut HashMap<PolyTypeId, MonoType>, mt : &MonoType, pt : &Type) -> bool {
  fn polytype_match_internal(polytypes : &mut HashMap<PolyTypeId, MonoType>, mt : &Type, pt : &Type) -> bool {
    if let Polytype(_) = &mt.content { panic!("unexpected generic type") }
    if let Polytype(gid) = &pt.content {
      if let Some(bound_type) = polytypes.get(&gid) {
        if let Some(mt) = unify_types_internal(bound_type, &mt) {
          polytypes.insert(*gid, mt);
          true
        }
        else { false }
      }
      else {
        polytypes.insert(*gid, mt.clone().to_monotype());
        true
      }    
    }
    else if let Abstract(at) = &mt.content { at.contains_type(pt) }
    else if let Abstract(at) = &pt.content { at.contains_type(mt) }
    else {
      if mt.content != pt.content { return false }
      if mt.children.len() != pt.children.len() { return false }
      for (mt, pt) in mt.children.iter().zip(pt.children.iter()) {
        if !polytype_match_internal(polytypes, mt, pt) {
          return false;
        }
      }
      true
    }
  }
  polytype_match_internal(polytypes, &mt.inner, pt)
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

impl Into<Type> for PolyTypeId {
  fn into(self) -> Type {
    Type::new(Polytype(self), vec![])
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

  pub fn unresolved_def(s : RefStr) -> Type {
    Type::new(Abstract(AbstractType::Def(s)), vec![])
  }

  pub fn ptr_to(self) -> Self {
    Type::new(Ptr, vec![self])
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

  pub fn array_of(self) -> Self {
    Type { content: Array, children: vec![self]}
  }

  pub fn children(&self) -> &[Type] {
    self.children.as_slice()
  }

  pub fn to_monotype(mut self) -> MonoType {
    self.strip_polytypes();
    MonoType { inner: self }
  }

  fn strip_polytypes(&mut self) {
    match &self.content {
      Polytype(_) => self.content = Abstract(AbstractType::Any),
      _ => (),
    };
    for c in self.children.iter_mut() {
      c.strip_polytypes();
    }
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
  pub fn contains_type(&self, t : &Type) -> bool {
    match self {
      AbstractType::Float => t.float(),
      AbstractType::Integer => t.int(),
      AbstractType::Any => true,
      AbstractType::Def(name) => {
        if let Def(resolved_name, _) = &t.content {
          return resolved_name == name;
        }
        false
      }
    }
  }

  pub fn default_type(&self) -> Option<Type> {
    match self {
      AbstractType::Float => Some(PType::F64.into()),
      AbstractType::Integer => Some(PType::I64.into()),
      AbstractType::Any => None,
      AbstractType::Def(_) => None,
    }
  }
}

#[derive(Clone, Debug)]
pub struct TypeDefinition {
  pub name : RefStr,
  pub module_id : ModuleId,
  pub fields : Vec<(Symbol, Type)>,
  pub kind : TypeKind,
  pub polytypes : Vec<PolyTypeId>,
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

impl  fmt::Display for PolyTypeId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let PolyTypeId(id) = *self;
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
      Polytype(id) => write!(f, "@Polytype({})", id),
      Abstract(abs) => write!(f, "{}", abs),
    }
  }
}

impl  Type {

  pub fn is_concrete(&self) -> bool {
    match self.content {
      Abstract(_) => return false,
      Polytype(_) => return false,
      _ => (),
    }
    for t in self.children.iter() {
      if !t.is_concrete() { return false }
    }
    true
  }

  pub fn to_concrete(&mut self) -> Result<(), ()> {
    match &self.content {
      Abstract(at) => {
        if let Some(t) = at.default_type() {
          *self = t;
        }
        else {
          return Err(());
        }
      }
      Polytype(_) => return Err(()),
      _ => (),
    };
    for t in self.children.iter_mut() {
      t.to_concrete()?;
    }
    Ok(())
  }

  pub fn from_string(s : &str) -> Option<Type> {
    PType::from_string(s).map(|pt| pt.into())
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

//#[derive(PartialEq)]
pub struct UnifyResult {
  pub fully_unified : bool,
  pub old_type_changed : bool,
  pub new_type_changed : bool,
}

impl UnifyResult {
  fn new() -> Self {
    UnifyResult { fully_unified: false, old_type_changed: false, new_type_changed: false }
  }
}

pub fn incremental_unify_monomorphic(old : &MonoType, new : &mut MonoType) -> UnifyResult {
  incremental_unify_polymorphic(old, &mut new.inner)
}

pub fn incremental_unify_polymorphic(old : &MonoType, new : &mut Type) -> UnifyResult {
  let mut result = UnifyResult::new();
  match incremental_unify_internal(old.as_type(), new, &mut result) {
    Ok(()) => result.fully_unified = true,
    Err(()) => (),
  }
  result
}

fn incremental_unify_internal(old_mono : &Type, new : &mut Type, result : &mut UnifyResult)
  -> Result<(), ()>
{
  if let Polytype(_) = &new.content { return Ok(()) }
  if let Polytype(_) = &old_mono.content { panic!("unexpected polytype") }
  if old_mono.content != new.content {
    if let Abstract(abs_old) = &old_mono.content {
      if abs_old.contains_type(new) {
        result.old_type_changed = true;
        return Ok(());
      }
    }
    if let Abstract(abs_new) = &new.content {
      if abs_new.contains_type(old_mono) {
        *new = old_mono.clone().to_monotype().inner;
        result.new_type_changed = true;
        return Ok(());
      }
    }
    return Err(());
  }
  if old_mono.children.len() != new.children.len() { return Err(()) }
  for (i, old_mono) in old_mono.children.iter().enumerate() {
    incremental_unify_internal(old_mono, &mut new.children[i], result)?;
  }
  Ok(())
}

pub fn unify_types(a : &MonoType, b : &MonoType) -> Option<MonoType> {
  unify_types_internal(a, &b.inner)
}

/// Will explicitly convert b to a monotype if the types match
fn unify_types_internal(mt : &MonoType, pt : &Type) -> Option<MonoType> {
  match can_unify_types_internal(&mt.inner, pt) {
    CanUnifyResult::CanUnify => {
      let mut t = pt.clone().to_monotype();
      if !incremental_unify_polymorphic(mt, &mut t.inner).fully_unified {
        panic!("bug in unify_types")
      }
      Some(t)
    }
    CanUnifyResult::AlreadyEqual => Some(mt.clone()),
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
  // Polytypes are assumed to behave like the Any type, but they must be explicitly
  // converted to MonoTypes before unification actually happens!
  if let Polytype(_) = &u.content { return CanUnify }
  if let Polytype(_) = &t.content { return CanUnify }
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
      globals: HashMap::new(),
      module_id,
    }
  }

  pub fn find_global<'a>(
    &'a self,
    name : &str,
    t : &MonoType,
    polytypes : &mut HashMap<PolyTypeId, MonoType>,
    results : &mut Vec<ResolvedGlobal>) {
    for g in self.globals.values() {
      if g.name.as_ref() == name {
        if g.polymorphic {
          polytypes.clear();
          if polytype_match(polytypes, t, &g.type_tag) {
            let resolved_type = polytype_replace(polytypes, &g.type_tag);
            results.push(ResolvedGlobal { def: g.clone(), resolved_type });
          }
        }
        else {
          if let Some(resolved_type) = unify_types_internal(&t, &g.type_tag) {
            results.push(ResolvedGlobal { def: g.clone(), resolved_type });
          }
        }
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
  polytype_bindings : HashMap<PolyTypeId, MonoType>,
  global_results : Vec<ResolvedGlobal>,
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
      polytype_bindings: HashMap::new(),
      global_results: vec![],
    }
  }

  pub fn get_global_mut(&mut self, id : GlobalId) -> &mut GlobalDefinition {
    self.new_module.globals.get_mut(&id).unwrap()
  }

  pub fn get_type_def(&self, name : &str, module_id : ModuleId) -> &TypeDefinition {
    self.find_module(module_id).find_type_def(name).unwrap()
  }

  pub fn get_type_def_mut(&mut self, name : &str) -> &mut TypeDefinition {
    self.new_module.type_defs.get_mut(name).unwrap()
  }

  pub fn create_type_def(&mut self, def : TypeDefinition) {
    self.new_module.type_defs.insert(def.name.clone(), def);
  }

  pub fn create_global(&mut self, def : GlobalDefinition) {
    self.new_module.globals.insert(def.id, def);
  }

  /// Returns a slice of all matching definitions
  pub fn find_global(
    &mut self,
    name : &str,
    t : &MonoType,
  )
    -> &[ResolvedGlobal]
  {
    self.polytype_bindings.clear();
    self.global_results.clear();
    self.new_module.find_global(name, t, &mut self.polytype_bindings, &mut self.global_results);
    for m in self.import_types.iter().rev() {
      m.find_global(name, t, &mut self.polytype_bindings, &mut self.global_results);
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


