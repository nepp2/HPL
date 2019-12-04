
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

impl  Into<Type> for PType {
  fn into(self) -> Type {
    Type::Prim(self)
  }
}

use PType::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  /// Primitive type (e.g. int, float, bool, etc)
  Prim(PType),
  Fun(Box<FunctionSignature>),
  Def(RefStr),
  Array(Box<Type>),
  Ptr(Box<Type>),
  Abstract(AbstractType),
  Generic(GenericId),
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

  pub fn default_type(self) -> Option<Type> {
    match self {
      AbstractType::Float => Some(Type::Prim(PType::F64)),
      AbstractType::Integer => Some(Type::Prim(PType::I64)),
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
      Type::Abstract(tc) => write!(f, "{:?}", tc),
    }
  }
}

impl  Type {

  pub fn is_concrete(&self) -> bool {
    match self {
      Type::Abstract(_) => false,
      Type::Fun(sig) => {
        for t in sig.args.iter() {
          if !t.is_concrete() { return false }
        }
        sig.return_type.is_concrete()
      },
      Type::Array(t) => t.is_concrete(),
      Type::Ptr(t) => t.is_concrete(),
      Type::Prim(_) => true,
      Type::Def(_) => true,
      Type::Generic(_) => false,
    }
  }

  pub fn to_concrete(&mut self) -> Result<(), ()> {
    match self {
      Type::Abstract(at) => {
        if let Some(t) = at.default_type() {
          *self = t;
        }
        else {
          return Err(());
        }
      }
      Type::Fun(sig) => {
        for t in sig.args.iter_mut() {
          t.to_concrete()?;
        }
        sig.return_type.to_concrete()?;
      },
      Type::Array(t) => t.to_concrete()?,
      Type::Ptr(t) => t.to_concrete()?,
      Type::Prim(_) => (),
      Type::Def(_) => (),
      Type::Generic(_) => return Err(()),
    };
    Ok(())
  }

  pub fn signature_mut(&mut self) -> Option<&mut FunctionSignature> {
    match self {
      Type::Fun(sig) => Some(sig),
      _ => None,
    }
  }

  pub fn signature(&self) -> Option<&FunctionSignature> {
    match self {
      Type::Fun(sig) => Some(sig),
      _ => None,
    }
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

pub fn unify_types_mut<'l>(old : &'l Type, new : &'l mut Type) -> Result<bool, ()> {
  use Type::*;
  let aaa = (); // make this recursive
  if let Abstract(abs_old) = old {
    if old == new { Ok(false) }
    else if abs_old.contains_type(new) { Ok(true) }
    else { Err(()) }
  }
  else if let Abstract(abs_new) = new {
    if abs_new.contains_type(old) { Ok(false) } else { Err(()) }
  }
  else {
    match old {
      Ptr(old) =>
        if let Ptr(new) = new { unify_types_mut(old, new) }
        else { Err(()) }
      Array(old) =>
        if let Array(new) = new { unify_types_mut(old, new) }
        else { Err(()) }
      Fun(old_sig) => {
        if let Fun(new_sig) = new {
          if old_sig.args.len() != new_sig.args.len() { return Err(()) }
          let mut changed = 0;
          for (o, t) in old_sig.args.iter().zip(new_sig.args.iter_mut()) {
            if unify_types_mut(o, t)? {
              changed += 1;
            }
          }
          if unify_types_mut(&old_sig.return_type, &mut new_sig.return_type)? {
            changed += 1;
          }
          Ok(changed > 0)
        }
        else { Err(()) }
      }
      Abstract(_) => panic!("impossible state"),
      Generic(_) => panic!("unexpected generic type"),
      // enumerate all the options so the compiler complains if a new Type is added
      Def(_) | Prim(_) => if old == new { Ok(false) } else { Err(()) },
    }
  }
}

// pub fn unify_abstract<'l>(a : &'l Type, b : &'l Type) -> Option<&'l Type> {
//   use Type::*;
//   let aaa = (); // make this recursive
//   match (a, b) {
//     (Abstract(abs_a), Abstract(abs_b)) => {
//       if abs_a == abs_b { return Some(a) } else { None }
//     }
//     (Abstract(abs_a), b) => {
//       if abs_a.contains_type(b) { Some(b) } else { None }
//     }
//     (a, Abstract(abs_b)) => {
//       if abs_b.contains_type(a) { Some(a) } else { None }
//     }
//     (a, b) => {
//       if a == b { Some(a) } else { None }
//     }
//   }
// }

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
  match (u, t) {
    (Type::Abstract(bt), _) => bt.contains_type(t),
    (Type::Ptr(u), Type::Ptr(t)) => abstract_match(u, t),
    (Type::Array(u), Type::Array(t)) => abstract_match(u, t),
    (Type::Fun(u_sig), Type::Fun(t_sig)) => {
      if u_sig.args.len() != t_sig.args.len() { return false }
      for (u, t) in u_sig.args.iter().zip(t_sig.args.iter()) {
        if !abstract_match(u, t) {
          return false;
        }
      }
      abstract_match(&u_sig.return_type, &t_sig.return_type)
    }
    // enumerate all the options so the compiler complains if a new Type is added
    (Type::Generic(_), _) => panic!("unexpected generic type"),
    (Type::Def(_), _) | (Type::Prim(_), _) => u == t,
    (Type::Ptr(_), _) | (Type::Array(_), _) | (Type::Fun(_), _) => false,
  }
}

fn generic_replace(generics : &HashMap<GenericId, Type>, gen : &mut UIDGenerator, t : &mut Type) {
  match t {
    Type::Ptr(t) => generic_replace(generics, gen, t),
    Type::Array(t) => generic_replace(generics, gen, t),
    Type::Fun(sig) => {
      for t in sig.args.iter_mut() {
        generic_replace(generics, gen, t);
      }
      generic_replace(generics, gen, &mut sig.return_type);
    }
    Type::Generic(gid) => {
      *t = generics.get(&gid).unwrap().clone();
    }
    Type::Def(_) | Type::Prim(_) => (),
    Type::Abstract(_) => panic!("unexpected abstract type"),
  }
}

fn generic_match(generics : &mut HashMap<GenericId, Type>, t : &Type, gt : &Type) -> bool {
  match (t, gt) {
    (Type::Generic(_), _) => panic!("unexpected generic type"),
    (t, Type::Generic(gid)) => {
      if let Some(bound_type) = generics.get(&gid) {
        if let Some(unified_t) = unify_abstract(&t, bound_type) {
          let ut = unified_t.clone();
          generics.insert(*gid, ut);
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
    (Type::Abstract(at), gt) => at.contains_type(gt),
    (Type::Ptr(t), Type::Ptr(gt)) => generic_match(generics, t, gt),
    (Type::Array(t), Type::Array(gt)) => generic_match(generics, t, gt),
    (Type::Fun(t_sig), Type::Fun(gt_sig)) => {
      if t_sig.args.len() != gt_sig.args.len() { return false }
      for (t, gt) in t_sig.args.iter().zip(gt_sig.args.iter()) {
        if !generic_match(generics, t, gt) {
          return false;
        }
      }
      generic_match(generics, &t_sig.return_type, &gt_sig.return_type)
    },
      // enumerate all the options so the compiler complains if a new Type is added
    (Type::Def(_), _) | (Type::Prim(_), _) => t == gt,
    (Type::Ptr(_), _) | (Type::Array(_), _) | (Type::Fun(_), _) => false,
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


