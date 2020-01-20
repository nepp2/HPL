
use std::fmt;
use itertools::Itertools;

use crate::error::TextLocation;
use crate::expr::RefStr;
use crate::structure::{
  NodeId, TypeKind, Reference
};

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct UnitId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct PolyTypeId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SymbolId(u64);

impl From<u64> for UnitId { fn from(v : u64) -> Self { UnitId(v) } }
impl From<u64> for PolyTypeId { fn from(v : u64) -> Self { PolyTypeId(v) } }
impl From<u64> for SymbolId { fn from(v : u64) -> Self { SymbolId(v) } }

/// Provides all the type definitions for a particular unit
pub struct TypeInfo {
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub symbols : HashMap<SymbolId, SymbolDefinition>,
  pub unit_id : UnitId,
}

/// Provides type information about nodes
pub struct TypeMapping {
  pub node_type : HashMap<NodeId, Type>,
  pub sizeof_info : HashMap<NodeId, Type>,
  pub symbol_references : HashMap<NodeId, (UnitId, SymbolId)>,
}

impl TypeMapping {
  pub fn new() -> Self {
    TypeMapping {
      node_type: HashMap::new(),
      sizeof_info: HashMap::new(),
      symbol_references: HashMap::new(),
    }
  }
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
  Def(RefStr, UnitId),
  Array,
  Ptr,
  Abstract(AbstractType),
  Polytype(PolyTypeId),
}

fn polytype_replace(polytypes : &HashMap<PolyTypeId, Type>, polytype : &Type) -> Type {
  fn polytype_replace_internal(polytypes : &HashMap<PolyTypeId, Type>, t : &mut Type) {
    if let Polytype(gid) = &t.content {
      *t = polytypes.get(&gid).cloned().unwrap_or_else(||Type::any());
    }
    for t in t.children.iter_mut() {
      polytype_replace_internal(polytypes, t);
    }
  }
  let mut t = polytype.clone();
  polytype_replace_internal(polytypes, &mut t);
  t
}

/// `polytype` may be a polymorphic type. It will be treated like `Abstract(Any)`.
fn polytype_match(polytypes : &mut HashMap<PolyTypeId, Type>, t : &Type, polytype : &Type) -> bool {
  fn polytype_match_internal(polytypes : &mut HashMap<PolyTypeId, Type>, t : &Type, polytype : &Type) -> bool {
    if let Polytype(_) = &t.content { panic!("unexpected generic type") }
    if let Polytype(gid) = &polytype.content {
      if let Some(bound_type) = polytypes.get(&gid) {
        if let Some(t) = unify_types(bound_type, &t) {
          polytypes.insert(*gid, t);
          true
        }
        else { false }
      }
      else {
        polytypes.insert(*gid, t.clone());
        true
      }    
    }
    else if let Abstract(at) = &t.content { at.contains_type(polytype) }
    else if let Abstract(at) = &polytype.content { at.contains_type(t) }
    else {
      if t.content != polytype.content { return false }
      if t.children.len() != polytype.children.len() { return false }
      for (t, polytype) in t.children.iter().zip(polytype.children.iter()) {
        if !polytype_match_internal(polytypes, t, polytype) {
          return false;
        }
      }
      true
    }
  }
  polytype_match_internal(polytypes, t, polytype)
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

  pub fn try_harden_literal(&self) -> Option<Type> {
    if let Abstract(ab) = &self.content {
      return ab.default_type();
    }
    None
  }

  pub fn sig_builder(&self) -> Option<SignatureBuilder> {
    if self.content == Fun {
      Some(SignatureBuilder{types: self.children.iter().cloned().collect()})
    }
    else { None }
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
  pub unit_id : UnitId,
  pub fields : Vec<(Reference, Type)>,
  pub kind : TypeKind,
  pub polytypes : Vec<PolyTypeId>,
  pub drop_function : Option<ResolvedSymbol>,
  pub clone_function : Option<ResolvedSymbol>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone)]
pub enum FunctionImplementation {
  Normal{body: NodeId, name_for_codegen: RefStr, args : Vec<Reference> },
  CFunction,
  Intrinsic,
}

/// The initialiser for the symbol
#[derive(Debug, Clone)]
pub enum SymbolInit {
  Function(FunctionInit),
  Expression(NodeId),
  Intrinsic,
  CBind,
}

#[derive(Debug, Clone)]
pub struct FunctionInit {
  pub body: NodeId,
  pub name_for_codegen: RefStr,
  pub args : Vec<Reference>,
}

#[derive(Clone, Debug)]
pub struct SymbolDefinition {
  pub id : SymbolId,
  pub unit_id : UnitId,
  pub name : RefStr,
  pub type_tag : Type,
  pub initialiser : SymbolInit,
  pub polymorphic : bool,
  pub loc : TextLocation,
}

impl SymbolDefinition {
  pub fn codegen_name(&self) -> Option<&str> {
    match &self.initialiser {
      SymbolInit::Function(f) => Some(&f.name_for_codegen),
      SymbolInit::CBind | SymbolInit::Expression(_) => Some(&self.name),
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
      AbstractType::Any => write!(f, "Any"),
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
      Def(name, _) => {
        write!(f, "{}", name)?;
        if self.children.len() > 0 {
          write!(f, "({}", self.children[0])?;
          for t in &self.children[1..] {
            write!(f, ", {}", t)?;
          }
          write!(f, ")")?;
        }
        Ok(())
      },
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
  pub unify_success : bool,
  pub immutable_type_changed : bool,
  pub mutable_type_changed : bool,
}

impl UnifyResult {
  fn new() -> Self {
    UnifyResult { unify_success: false, immutable_type_changed: false, mutable_type_changed: false }
  }
}

pub fn incremental_unify(old : &Type, new : &mut Type) -> UnifyResult {
  let mut result = UnifyResult::new();
  match incremental_unify_internal(old, new, &mut result) {
    Ok(()) => result.unify_success = true,
    Err(()) => (),
  }
  result
}

fn incremental_unify_internal(old_mono : &Type, new : &mut Type, result : &mut UnifyResult)
  -> Result<(), ()>
{
  if let Polytype(_) = &new.content { return Ok(()) }
  if let Polytype(_) = &old_mono.content { return Ok(()) }
  if old_mono.content != new.content {
    if let Abstract(abs_old) = &old_mono.content {
      if abs_old.contains_type(new) {
        result.immutable_type_changed = true;
        return Ok(());
      }
    }
    if let Abstract(abs_new) = &new.content {
      if abs_new.contains_type(old_mono) {
        *new = old_mono.clone();
        result.mutable_type_changed = true;
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

pub fn unify_types(a : &Type, b : &Type) -> Option<Type> {
  #[derive(Clone, Copy, PartialEq)]
  enum CanUnifyResult {
    CanUnify, AlreadyEqual, CannotUnify
  }

  fn can_unify_types_internal(u : &Type, t : &Type) -> CanUnifyResult {
    use CanUnifyResult::*;
    // Polytypes are assumed to behave like the Any type
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
  match can_unify_types_internal(a, b) {
    CanUnifyResult::CanUnify => {
      let mut b = b.clone();
      if !incremental_unify(a, &mut b).unify_success {
        panic!("bug in unify_types")
      }
      Some(b)
    }
    CanUnifyResult::AlreadyEqual => Some(a.clone()),
    CanUnifyResult::CannotUnify => None,
  }
}

impl TypeInfo {
  pub fn new(unit_id : UnitId) -> TypeInfo {
    TypeInfo {
      type_defs: HashMap::new(),
      symbols: HashMap::new(),
      unit_id,
    }
  }

  pub fn find_symbol<'a>(
    &'a self,
    name : &str,
    t : &Type,
    polytypes : &mut HashMap<PolyTypeId, Type>,
    results : &mut Vec<ResolvedSymbol>) {
    for g in self.symbols.values() {
      if g.name.as_ref() == name {
        if g.polymorphic {
          polytypes.clear();
          if polytype_match(polytypes, t, &g.type_tag) {
            let resolved_type = polytype_replace(polytypes, &g.type_tag);
            results.push(ResolvedSymbol { def: g.clone(), resolved_type });
          }
        }
        else {
          if let Some(resolved_type) = unify_types(&t, &g.type_tag) {
            results.push(ResolvedSymbol { def: g.clone(), resolved_type });
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
pub struct ResolvedSymbol {
  /// TODO: this is very inefficient, because these are searched for and returned repeatedly
  pub def : SymbolDefinition,
  pub resolved_type : Type,
}

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  new_module_id : UnitId,
  import_types : &'a [&'a TypeInfo],
  new_module : &'a mut TypeInfo,
  polytype_bindings : HashMap<PolyTypeId, Type>,
  symbol_results : Vec<ResolvedSymbol>,
}

// TODO: A lot of these functions are slow because they iterate through everything.
// This could probably be improved with some caching, although any caching needs to
// be wary of new symbols being added.
impl <'a> TypeDirectory<'a> {
  pub fn new(
    new_module_id : UnitId,
    import_types : &'a [&'a TypeInfo],
    new_module : &'a mut TypeInfo) -> Self
  {
    TypeDirectory{
      new_module_id, import_types, new_module,
      polytype_bindings: HashMap::new(),
      symbol_results: vec![],
    }
  }

  pub fn get_global_mut(&mut self, id : SymbolId) -> &mut SymbolDefinition {
    self.new_module.symbols.get_mut(&id).unwrap()
  }

  pub fn get_type_def(&self, name : &str, unit_id : UnitId) -> &TypeDefinition {
    self.find_module(unit_id).find_type_def(name).unwrap()
  }

  pub fn get_type_def_mut(&mut self, name : &str) -> &mut TypeDefinition {
    self.new_module.type_defs.get_mut(name).unwrap()
  }

  pub fn create_type_def(&mut self, def : TypeDefinition) {
    self.new_module.type_defs.insert(def.name.clone(), def);
  }

  pub fn create_global(&mut self, def : SymbolDefinition) {
    self.new_module.symbols.insert(def.id, def);
  }

  /// Returns a slice of all matching definitions
  pub fn find_symbol(
    &mut self,
    name : &str,
    t : &Type,
  )
    -> &[ResolvedSymbol]
  {
    self.polytype_bindings.clear();
    self.symbol_results.clear();
    self.new_module.find_symbol(name, t, &mut self.polytype_bindings, &mut self.symbol_results);
    for m in self.import_types.iter().rev() {
      m.find_symbol(name, t, &mut self.polytype_bindings, &mut self.symbol_results);
    }
    self.symbol_results.as_slice()
  }

  pub fn find_type_def(&self, name : &str) -> Option<&TypeDefinition> {
    self.new_module.find_type_def(name).or_else(||
      self.import_types.iter().rev().flat_map(|m| m.find_type_def(name)).next())
  }

  pub fn new_module_id(&self) -> UnitId {
    self.new_module.unit_id
  }

  pub fn find_module(&self, unit_id : UnitId) -> &TypeInfo {
    [&*self.new_module].iter()
      .chain(self.import_types.iter().rev())
      .find(|t| t.unit_id == unit_id)
      .expect("module not found")
  }
}


