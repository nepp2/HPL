
use std::fmt;
use itertools::Itertools;

use crate::expr::{RefStr, UIDGenerator, Uid};
use crate::structure::{
  NodeId, TypeKind, Reference
};

use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct UnitId(Uid);

impl From<Uid> for UnitId { fn from(v : Uid) -> Self { UnitId(v) } }

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SymbolId {
  pub sid : Uid,
  pub uid : UnitId,
}

impl UnitId {
  pub fn new_symbol_id(self, gen : &mut UIDGenerator) -> SymbolId {
    SymbolId { sid: gen.next(), uid: self }
  }
}

impl From<(Uid, UnitId)> for SymbolId {
  fn from(v : (Uid, UnitId)) -> Self {
    SymbolId{sid: v.0, uid: v.1}
  }
}

/// Provides all the type definitions for a particular unit
pub struct TypeInfo {
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub symbols : HashMap<SymbolId, SymbolDefinition>,
  pub unit_id : UnitId,
}

/// Provides type information about nodes
#[derive(Default)]
pub struct TypeMapping {
  pub node_type : HashMap<NodeId, Type>,
  pub sizeof_info : HashMap<NodeId, Type>,
  pub symbol_references : HashMap<NodeId, SymbolId>,
  pub polymorphic_references : HashSet<(SymbolId, Type)>,
  pub symbol_def_nodes : HashMap<SymbolId, NodeId>,
  pub type_def_nodes : HashMap<RefStr, NodeId>,
}

impl TypeMapping {
  pub fn new() -> Self { Default::default() }
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Type {
  pub content : TypeContent,
  pub children : Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeContent {
  /// Primitive type (e.g. int, float, bool, etc)
  Prim(PType),
  Fun,
  Def(RefStr, UnitId),
  Array,
  Ptr,
  Abstract(AbstractType),
  Polytype(RefStr),
}

fn polytype_replace(polytypes : &HashMap<RefStr, Type>, polytype : &Type) -> Type {
  fn polytype_replace_internal(polytypes : &HashMap<RefStr, Type>, t : &mut Type) {
    if let Polytype(gid) = &t.content {
      *t = polytypes.get(gid).cloned().unwrap_or_else(||Type::any());
    }
    for t in t.children.iter_mut() {
      polytype_replace_internal(polytypes, t);
    }
  }
  let mut t = .clone();
  polytype_replace_internal(polytypes, &mut t);
  t
}

trait PolyTypes {
  fn get<'l>(&'l self, name : &str) -> Option<&'l Type>;
  fn insert(&mut self, name : RefStr, t : Type);
}

/// `` may be a polymorphic type. It will be treated like `Abstract(Any)`.
fn polytype_match(polytypes : &mut HashMap<RefStr, Type>, t : &Type, polytype : &Type) -> bool {
  fn polytype_match_internal(polytypes : &mut HashMap<RefStr, Type>, t : &Type, polytype : &Type) -> bool {
    if let Polytype(_) = &t.content { panic!("unexpected generic type {}", t) }
    if let Polytype(gid) = &polytype.content {
      if let Some(bound_type) = polytypes.get(gid) {
        if let Some(t) = unify_types(bound_type, &t) {
          polytypes.insert(gid.clone(), t);
          true
        }
        else { false }
      }
      else {
        polytypes.insert(gid.clone(), t.clone());
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

impl Into<Type> for TypeContent {
  fn into(self) -> Type {
    Type::new(self, vec![])
  }
}

impl Into<Type> for AbstractType {
  fn into(self) -> Type {
    Type::new(Abstract(self), vec![])
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

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
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
  pub type_vars : Vec<RefStr>,
  pub drop_function : Option<ResolvedSymbol>,
  pub clone_function : Option<ResolvedSymbol>,
}

impl TypeDefinition {

  pub fn is_polymorphic(&self) -> bool {
    self.type_vars.len() > 0
  }

  pub fn instanced_field_type(&self, name : &str, type_var_instances : &[Type]) -> Option<Type> {
    for (r, t) in self.fields.iter() {
      if r.name.as_ref() == name {
        let mut t = t.clone();
        self.instance_type(&mut t, type_var_instances);
        return Some(t);
      }
    }
    None
  }

  pub fn instance_type(&self, t : &mut Type, type_var_instances : &[Type]) {
    if let TypeContent::Polytype(name) = &t.content {
      let i = self.type_vars.iter().position(|tv| tv == name).unwrap();
      *t = type_var_instances[i].clone();
    }
    for c in t.children.iter_mut() {
      self.instance_type(c, type_var_instances);
    }
  }
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
  pub type_vars : Vec<RefStr>,
}

impl SymbolDefinition {
  pub fn codegen_name(&self) -> Option<&str> {
    match &self.initialiser {
      SymbolInit::Function(f) => Some(&f.name_for_codegen),
      SymbolInit::CBind | SymbolInit::Expression(_) => Some(&self.name),
      _ => None,
    }
  }

  pub fn is_polymorphic(&self) -> bool {
    self.type_vars.len() > 0
  }

  pub fn instanced_type_vars(&self, instanced_signature : &Type) -> Vec<Type> {
    let mut polytype_map = HashMap::new();
    let success = polytype_match(&mut polytype_map, instanced_signature, &self.type_tag);
    if !success {
      panic!("instanced signature did not match polymorphic function signature");
    }
    self.type_vars.iter().map(|v| polytype_map.remove(v).unwrap()).collect()
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

impl fmt::Debug for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self)
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
    polytypes : &mut HashMap<RefStr, Type>,
    results : &mut Vec<ResolvedSymbol>) {
    for sym in self.symbols.values() {
      if sym.name.as_ref() == name {
        if sym.is_polymorphic() {
          polytypes.clear();
          if polytype_match(polytypes, t, &sym.type_tag) {
            let resolved_type = polytype_replace(polytypes, &sym.type_tag);
            results.push(ResolvedSymbol { symbol_id: sym.id, resolved_type });
          }
        }
        else {
          if let Some(resolved_type) = unify_types(&t, &sym.type_tag) {
            results.push(ResolvedSymbol { symbol_id: sym.id, resolved_type });
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
  pub symbol_id : SymbolId,
  pub resolved_type : Type,
}

/// Utility type for finding definitions either in the module being constructed,
/// or in the other modules in scope.
pub struct TypeDirectory<'a> {
  new_unit_id : UnitId,
  import_types : &'a [&'a TypeInfo],
  new_module : &'a mut TypeInfo,
  polytype_bindings : HashMap<RefStr, Type>,
  symbol_results : Vec<ResolvedSymbol>,
}

// TODO: A lot of these functions are slow because they iterate through everything.
// This could probably be improved with some caching, although any caching needs to
// be wary of new symbols being added.
impl <'a> TypeDirectory<'a> {
  pub fn new(
    new_unit_id : UnitId,
    import_types : &'a [&'a TypeInfo],
    new_module : &'a mut TypeInfo) -> Self
  {
    TypeDirectory{
      new_unit_id, import_types, new_module,
      polytype_bindings: HashMap::new(),
      symbol_results: vec![],
    }
  }

  pub fn get_symbol_mut(&mut self, id : SymbolId) -> &mut SymbolDefinition {
    self.new_module.symbols.get_mut(&id).unwrap()
  }

  pub fn get_type_def(&self, name : &str, unit_id : UnitId) -> &TypeDefinition {
    self.find_type_info(unit_id).find_type_def(name).unwrap()
  }

  pub fn get_type_def_mut(&mut self, name : &str) -> &mut TypeDefinition {
    self.new_module.type_defs.get_mut(name).unwrap()
  }

  pub fn create_type_def(&mut self, def : TypeDefinition) {
    self.new_module.type_defs.insert(def.name.clone(), def);
  }

  pub fn create_symbol(&mut self, def : SymbolDefinition) {
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

  pub fn new_unit_id(&self) -> UnitId {
    self.new_module.unit_id
  }

  pub fn find_type_info(&self, unit_id : UnitId) -> &TypeInfo {
    [&*self.new_module].iter()
      .chain(self.import_types.iter().rev())
      .find(|t| t.unit_id == unit_id)
      .expect("module not found")
  }
}


