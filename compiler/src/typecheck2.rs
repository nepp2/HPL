
use std::rc::Rc;
use std::fmt::Write;
use std::fmt;
use itertools::Itertools;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};
use crate::structure::{Node, NodeId, Nodes, Content, Val, LabelId};

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeId {
  id : u64
}

pub struct Types {
  types : HashMap<TypeId, Type>,
}

impl Types {

  pub fn new() -> Self {
    Types { types: HashMap::new() }
  }

  pub fn get(&self, id : TypeId) -> &Type {
    self.types.get(&id).unwrap()
  }

  pub fn display(&self, id : TypeId) -> TypeDisplay {
    TypeDisplay{ t: self.get(id), types: self }
  }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Type {
  Void,
  F64,
  F32,
  I64,
  U64,
  I32,
  U32,
  U16,
  U8,
  Bool,
  Dynamic,
  Fun(Rc<FunctionSignature>),
  Def(RefStr),
  Array(TypeId),
  Ptr(TypeId),
}

pub struct TypeDisplay<'l>{
  t : &'l Type,
  types: &'l Types,
}

impl <'l> fmt::Display for TypeDisplay<'l> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let types = self.types;
    match self.t {
      Type::Fun(sig) =>
        write!(f, "fun({}) => {}", 
          sig.args.iter()
            .map(|a| types.display(*a))
            .join(", "),
          types.display(sig.return_type)),
      Type::Def(s) => write!(f, "{}", s),
      Type::Array(t) => write!(f, "array({})", types.display(*t)),
      Type::Ptr(t) => write!(f, "ptr({})", types.display(*t)),
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
      "any" => Some(Type::Dynamic),
      "()" => Some(Type::Void),
      "" => Some(Type::Dynamic),
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

  pub fn pointer(&self) -> bool {
    match self { Type::Ptr(_) | Type::Fun(_) => true, _ => false }
  }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TypeKind {
  Struct, Union
}

#[derive(Clone, Debug)]
pub struct TypeDefinition {
  pub name : RefStr,
  pub fields : Vec<(RefStr, Type)>,
  pub kind : TypeKind,
  pub drop_function : Option<FunctionReference>,
  pub clone_function : Option<FunctionReference>,
  pub definition_location : TextLocation,
}

#[derive(Debug)]
pub enum FunctionImplementation {
  Normal(TypedNode),
  CFunction(Option<usize>),
  Intrinsic,
}

#[derive(Debug)]
pub struct FunctionDefinition {
  pub module_id : u64,
  pub name_in_code : RefStr,
  pub name_for_codegen : RefStr,
  pub args : Vec<RefStr>,
  pub signature : Rc<FunctionSignature>,
  pub implementation : FunctionImplementation,
  pub definition_location : TextLocation,
}

impl FunctionDefinition {
  fn function_reference(&self) -> FunctionReference {
    FunctionReference {
      name_in_code: self.name_in_code.clone(),
      name_for_codegen: self.name_for_codegen.clone(),
      module_id: self.module_id,
    }
  }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct FunctionSignature {
  pub return_type : TypeId,
  pub args : Vec<TypeId>,
}

impl PartialEq for TypeDefinition {
  fn eq(&self, rhs : &Self) -> bool {
    self.name == rhs.name
  }
}

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "top_level";

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global }

/// Identifies a specific function from a specific module with a specific argument list
#[derive(Debug, Clone)]
pub struct FunctionReference {
  pub name_in_code : RefStr,
  pub name_for_codegen : RefStr,
  pub module_id : u64,
}

use Content::*;

/// This indicates whether the type is a full value, or just a reference to one.
/// When an expression is evaluated to a full value, it may need to be dropped later.
/// When a reference turns into a value, it may need to be cloned.
#[derive(Debug, PartialEq)]
pub enum NodeValueType {
  Owned,
  Ref,
  Mut,
  Nil,
}

#[derive(Debug)]
pub struct TypedNode {
  pub type_tag : Type,
  pub content : Content,
  pub loc : TextLocation,
}

impl TypedNode {

  pub fn node_value_type(&self) -> NodeValueType {
    match &self.content {
      FieldAccess{..} | Reference{..} |
      Index{..} | Literal(_) | Quote(_)
        => NodeValueType::Ref,
      Block(_) | FunctionCall{..} |
      IfThenElse{..} | TypeConstructor{..}
        => NodeValueType::Owned,
      _ => NodeValueType::Nil,
    }
  }

  fn assert_type(&self, expected : Type) -> Result<(), Error> {
    if self.type_tag == expected {
      Ok(())
    }
    else {
      error(self.loc, format!("expected type {:?}, found type {:?}", expected, self.type_tag))
    }
  }
}

pub struct GlobalDefinition {
  pub name : RefStr,
  pub type_tag : Type,
  pub c_address : Option<usize>,
}

//#[derive(Clone)]
pub struct TypedModule {
  pub id : u64,
  pub type_defs : HashMap<RefStr, TypeDefinition>,
  pub functions : Vec<FunctionDefinition>,
  pub globals : HashMap<RefStr, GlobalDefinition>,
  pub types : Types,
}

impl TypedModule {
  pub fn new(id : u64) -> TypedModule {
    TypedModule{
      id, type_defs: HashMap::new(),
      functions: vec![], globals: HashMap::new(),
      types: Types::new(),
    }
  }
}

struct SymbolReference {
  symbol_name : RefStr,
  reference_location : TextLocation,
}

pub struct TypeChecker<'l> {
  uid_generator : &'l mut UIDGenerator,
  module : &'l mut TypedModule,
  modules : &'l [&'l TypedModule],
  local_symbol_table : &'l HashMap<RefStr, usize>,

  type_definition_references : Vec<SymbolReference>,

  cache: &'l StringCache,
}

pub struct FunctionChecker<'l, 'lt> {
  t : &'l mut TypeChecker<'lt>,

  is_top_level : bool,
  variables: HashMap<RefStr, Type>,

  labels_in_scope : Vec<LabelId>,

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  scope_map: Vec<HashMap<RefStr, RefStr>>,
}

