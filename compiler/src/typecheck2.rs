
use std::rc::Rc;
use std::fmt::Write;
use std::fmt;
use itertools::Itertools;
use std::hash::Hash;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};
use crate::structure::{Node, NodeId, Nodes, NodeRef, Content, Val, LabelId};

use std::collections::{HashMap, HashSet};
use bimap::BiMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeId(u64);

pub struct Types {
  types : BiMap<TypeId, Type>,

  signatures : BiMap<TypeId, FunctionSignature>,

  definition_names : BiMap<TypeId, RefStr>,
}

fn get_id<V: Eq + Hash>(map : &mut BiMap<TypeId, V>, gen : &mut UIDGenerator, v : V) -> TypeId {
  if let Some(id) = map.get_by_right(&v) {
    *id
  }
  else {
    let id = TypeId(gen.next());
    map.insert(id, v);
    id
  }
}

impl Types {

  pub fn new() -> Self {
    Types { 
      types: BiMap::new(),
      signatures: BiMap::new(),
      definition_names: BiMap::new(),
    }
  }

  pub fn get(&self, id : TypeId) -> &Type {
    self.types.get_by_left(&id).unwrap()
  }

  pub fn definition_id(&mut self, gen : &mut UIDGenerator, name : RefStr) -> TypeId {
    get_id(&mut self.definition_names, gen, name)
  }

  pub fn definition_name(&self, id : TypeId) -> &RefStr {
    self.definition_names.get_by_left(&id).unwrap()
  }

  pub fn signature_id(&mut self, gen : &mut UIDGenerator, sig : FunctionSignature) -> TypeId {
    get_id(&mut self.signatures, gen, sig)
  }

  pub fn signature(&self, id : TypeId) -> &FunctionSignature {
    self.signatures.get_by_left(&id).unwrap()
  }

  pub fn type_id(&mut self, gen : &mut UIDGenerator, t : Type) -> TypeId {
    get_id(&mut self.types, gen, t)
  }

  pub fn display(&self, id : TypeId) -> TypeDisplay {
    TypeDisplay{ t: self.get(id), types: self }
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn expr_to_type(&mut self, cache : &mut StringCache, gen : &mut UIDGenerator, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      let name = cache.get(name);
      let id = self.definition_id(gen, name);
      return Ok(Type::Def(id));
    }
    match expr.try_construct() {
      Some(("fun", es)) => {
        if let Some(args) = es.get(0) {
          let args =
            args.children().iter()
            .map(|e| {
              let e = if let Some((":", [_name, tag])) = e.try_construct() {tag} else {e};
              self.expr_to_type_id(cache, gen, e)
            })
            .collect::<Result<Vec<TypeId>, Error>>()?;
          let return_type = if let Some(t) = es.get(1) {
            self.expr_to_type_id(cache, gen, t)?
          }
          else {
            self.type_id(gen, Type::Void)
          };
          let id = self.signature_id(gen, FunctionSignature{ args, return_type});
          return Ok(Type::Fun(id));
        }
      }
      Some(("call", [name, t])) => {
        match name.unwrap_symbol()? {
          "ptr" => {
            let t = self.expr_to_type_id(cache, gen, t)?;
            return Ok(Type::Ptr(t))
          }
          "array" => {
            let t = self.expr_to_type_id(cache, gen, t)?;
            return Ok(Type::Array(t))
          }
          _ => (),
        }
      }
      _ => ()
    }
    error(expr, "invalid type expression")
  }

  fn expr_to_type_id(&mut self, cache : &mut StringCache, gen : &mut UIDGenerator, expr : &Expr) -> Result<TypeId, Error> {
    let t = self.expr_to_type(cache, gen, expr)?;
    return Ok(self.type_id(gen, t));
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
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
  Fun(TypeId),
  Def(TypeId),
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
      Type::Fun(sig) => {
        let sig = self.types.signature(*sig);
        write!(f, "fun({}) => {}", 
          sig.args.iter()
            .map(|a| types.display(*a))
            .join(", "),
          types.display(sig.return_type))
      }
      Type::Def(s) => write!(f, "{}", self.types.definition_name(*s)),
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
  scope_map: Vec<HashMap<RefStr, TypeId>>,
}

use Content::*;
use Type::*;

enum TypeConstraint {
  Literal(Val),
  RefersToVariable(NodeId),
  RefersTo(NodeId),
}

struct Inference<'l> {
  nodes : &'l Nodes,
  unresolved : HashSet<NodeId>,
  types : HashMap<NodeId, Type>,
  constraints : Constraints,
}

fn set_type(types : &mut HashMap<NodeId, Type>, id : NodeId, t : Type) {
  // TODO: unify!
  types.insert(id, t);
}

impl <'l> Inference<'l> {

  fn infer(&mut self) {
    // Asserts
    for (id, t) in self.constraints.assert.drain(..) {
      set_type(&mut self.types, id, t);
    }

    // Equivalence
    let mut equiv = HashMap::new();
    for (n, t) in self.constraints.equalivalent_to.iter() {
      if let Some(t) = self.types.get(t) {
        self.constraints.assert.push((*n, t.clone()));
      }
      else {
        equiv.insert(*n, *t);
      }
    }
    self.constraints.equalivalent_to = equiv;
  }
}

struct Constraints {
  literals : HashMap<NodeId, Val>,
  tagged : HashMap<NodeId, Type>,
  assigned : HashMap<NodeId, NodeId>,
  equalivalent_to : HashMap<NodeId, NodeId>,
  assert : Vec<(NodeId, Type)>,
}

fn infer_constraints(c : &mut Constraints, n : NodeRef) {
  match &n.content() {
    Literal(val) => {
      c.literals.insert(n.id(), val.clone());
    }
    VariableInitialise{ name, type_tag, value } => {
      c.assert.push((n.id(), Type::Void));
      // Register & parse the type
      // Register the variable and it's type
      infer_constraints(c, n.get(*value));
    }
    Assignment{ assignee , value } => {
      c.assert.push((n.id(), Type::Void));
      c.assigned.insert(*assignee, *value);
      infer_constraints(c, n.get(*assignee));
      infer_constraints(c, n.get(*value));
    }
    IfThen{ condition, then_branch } => {
      c.assert.push((n.id(), Type::Void));
      c.assert.push((*condition, Type::Bool));
      c.assert.push((*then_branch, Type::Void));
      infer_constraints(c, n.get(*condition));
      infer_constraints(c, n.get(*then_branch));
    }
    IfThenElse{ condition, then_branch, else_branch } => {
      c.equalivalent_to.insert(n.id(), *then_branch);
      c.assert.push((*condition, Type::Bool));
      c.equalivalent_to.insert(*then_branch, *else_branch);
      infer_constraints(c, n.get(*condition));
      infer_constraints(c, n.get(*then_branch));
      infer_constraints(c, n.get(*else_branch));
    }
    Block(ns) => {
      let len = ns.len();
      if len > 0 {
        for n in &ns[0..(len-1)] {
          c.assert.push((*n, Type::Void));
        }
        c.equalivalent_to.insert(n.id(), ns[len-1]);
      }
      else {
        c.assert.push((n.id(), Type::Void));
      }
      for child in ns.iter() {
        infer_constraints(c, n.get(*child));
      }
    }
    Quote(e) => {
      //let t : Type = ptr(expr);
      //c.assert.push((n.id(), t));
    }
    Reference(name) => {
      // TODO: Figure out wtf this is referencing!
    }
    Content::FunctionDefinition{ name, args, return_tag, body } => {
      c.assert.push((n.id(), Type::Void));
      // TODO: register a function somehow
    }
    CBind { name, type_tag  } => {
      // TODO: Figure out wtf this is referencing!
    }
    StructDefinition{ name, fields } => {
      c.assert.push((n.id(), Type::Void));
      // TODO: register a struct somehow
    }
    UnionDefinition{ name, fields } => {
      c.assert.push((n.id(), Type::Void));
      // TODO: register a union somehow
    }
    TypeConstructor{ name, field_values } => {
      // TODO: figure out what kind of type is being constructed!
    }
    FieldAccess{ container, field } => {

    }
    Index{ container, index } => {

    }
    ArrayLiteral(ns) => {

    }
    FunctionCall{ function, args } => {

    }
    While{ condition, body } => {

    }
    Convert{ from_value, into_type } => {

    }
    SizeOf{ type_tag } => {

    }
    Label{ label, body } => {

    }
    BreakToLabel{ label, return_value } => {

    }
  }
}
