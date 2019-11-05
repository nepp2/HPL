
use std::rc::Rc;
use std::fmt::Write;
use std::fmt;
use itertools::Itertools;
use std::hash::Hash;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};
use crate::structure::{Node, NodeId, Nodes, NodeRef, Content, Val, LabelId, TypeKind};

use std::collections::{HashMap, HashSet};
use bimap::BiMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SigId(u64);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct DefId(u64);

impl From<u64> for TypeId { fn from(v : u64) -> Self { TypeId(v) } }
impl From<u64> for SigId { fn from(v : u64) -> Self { SigId(v) } }
impl From<u64> for DefId { fn from(v : u64) -> Self { DefId(v) } }

pub struct Types {
  types : BiMap<TypeId, Type>,

  signatures : BiMap<SigId, FunctionSignature>,

  type_definition_ids : HashMap<RefStr, DefId>,

  type_definitions : HashMap<DefId, TypeDefinition>,
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
      type_definition_ids: HashMap::new(),
      type_definitions: HashMap::new(),
    }
  }

  pub fn get(&self, id : TypeId) -> &Type {
    self.types.get_by_left(&id).unwrap()
  }

  pub fn type_definition_id(&mut self, gen : &mut UIDGenerator, name : RefStr) -> DefId {
    let a = (); // TODO: lookup types from other modules
    *self.type_definition_ids.entry(name).or_insert_with(||gen.next().into())
  }

  pub fn signature_id(&mut self, gen : &mut UIDGenerator, sig : FunctionSignature) -> SigId {
    let a = (); // TODO: lookup types from other modules
    get_id(&mut self.signatures, gen, sig)
  }

  pub fn type_id(&mut self, gen : &mut UIDGenerator, t : Type) -> TypeId {
    let a = (); // TODO: lookup types from other modules
    get_id(&mut self.types, gen, t)
  }

  pub fn type_definition(&self, id : DefId) -> Option<&TypeDefinition> {
    self.type_definitions.get(&id)
  }

  pub fn signature(&self, id : SigId) -> &FunctionSignature {
    self.signatures.get_by_left(&id).unwrap()
  }

  pub fn display(&self, id : TypeId) -> TypeDisplay {
    TypeDisplay{ t: self.get(id), types: self }
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn expr_to_type(&mut self, cache : &StringCache, gen : &mut UIDGenerator, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      let name = cache.get(name);
      let id = self.type_definition_id(gen, name);
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

  fn expr_to_type_id(&mut self, cache : &StringCache, gen : &mut UIDGenerator, expr : &Expr) -> Result<TypeId, Error> {
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
  Fun(SigId),
  Def(DefId),
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
      Type::Def(s) => {
        let name =
          self.types.type_definition(*s)
          .map(|td| td.name.as_ref()).unwrap_or("@unresolved");
        write!(f, "{}", name)
      }
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

use Type::*;

fn literal_to_type(string_def : DefId, v : &Val) -> Type {
  match v {
    Val::F64(_) => F64,
    Val::F32(_) => F32,
    Val::I64(_) => I64,
    Val::I32(_) => I32,
    Val::Bool(_) => Bool,
    Val::U64(_) => U64,
    Val::U32(_) => U32,
    Val::U16(_) => U16,
    Val::U8(_) => U8,
    Val::Void => Void,
    Val::String(_) => {
      Def(string_def)
    }
  }
}

struct Inference<'l> {
  nodes : &'l Nodes,
  types : &'l mut Types,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  resolved : HashMap<TypeSymbol, TypeId>,
}


impl <'l> Inference<'l> {
  
  fn set_type(&mut self, ts : TypeSymbol, t : TypeId) {
    let a = (); // TODO: unify!
    self.resolved.insert(ts, t);
  }

  fn infer(&mut self, mut constraints : Constraints) -> Result<(), Error> {

    let type_symbol_count = constraints.symbols.len();

    // Literals
    let string_def = self.types.type_definition_id(self.gen, self.cache.get("string"));
    for (n, v) in constraints.literals.iter() {
      let t = literal_to_type(string_def, v);
      let t = self.types.type_id(self.gen, t);
      constraints.assert.push((*n, t));
    }
    constraints.literals.clear();

    loop {
      let mut progress = false;

      // Asserts
      for (ts, t) in constraints.assert.drain(..) {
        self.set_type(ts, t);
        progress = true;
      }

      // Equivalence
      let mut equiv = Vec::new();
      for (a, b) in constraints.equalivalent.iter() {
        if let Some(t) = self.resolved.get(b) {
          constraints.assert.push((*a, *t));
          progress = true;
        }
        else if let Some(t) = self.resolved.get(a) {
          constraints.assert.push((*b, *t));
          progress = true;
        }
        else {
          equiv.push((*a, *b));
        }
      }
      constraints.equalivalent = equiv;

      if !progress {
        if self.resolved.len() == type_symbol_count {
          break;
        }
        else {
          let loc = self.nodes.get(self.nodes.root).loc;
          return error(loc, "Couldn't infer types for some nodes");
        }
      }
    }

    Ok(())
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(u64);

struct FunctionDefConstraints {
  name : RefStr,
  return_type : TypeSymbol,
  args : Vec<(RefStr, TypeSymbol)>,
}

struct TypeDefConstraints {
  name : RefStr,
  kind : TypeKind,
  fields : Vec<(RefStr, TypeSymbol)>,
}

struct FieldAccessConstraints {
  container : TypeSymbol,
  field : RefStr,
  result : TypeSymbol,
}

struct ConstructorConstraints {
  type_name : RefStr,
  fields : Vec<(Option<RefStr>, TypeSymbol)>,
  result : TypeSymbol,
}

struct FunctionCallConstraints {
  function : TypeSymbol,
  args : Vec<(Option<RefStr>, TypeSymbol)>,
  result : TypeSymbol,
}

struct GlobalReference {
  name : RefStr,
  result : TypeSymbol,
}

struct CoreTypes {
  string : DefId,
}

impl CoreTypes {
  fn new(types : &mut Types, gen : &mut UIDGenerator, cache : &StringCache) -> Self {
    CoreTypes {
      string: types.type_definition_id(gen, cache.get("string")),
    }
  }
}

struct Constraints {
  symbols : Vec<TypeSymbol>,
  node_symbols : HashMap<NodeId, TypeSymbol>,
  literals : Vec<(TypeSymbol, Val)>,
  assert : Vec<(TypeSymbol, TypeId)>,
  array : HashMap<TypeSymbol, TypeSymbol>,
  equalivalent : Vec<(TypeSymbol, TypeSymbol)>,
  field_access : Vec<FieldAccessConstraints>,
  constructors : Vec<ConstructorConstraints>,
  function_def : Vec<FunctionDefConstraints>,
  function_call : Vec<FunctionCallConstraints>,
  type_def : Vec<TypeDefConstraints>,
  global_def : HashMap<RefStr, TypeSymbol>,
  global_reference : Vec<GlobalReference>,
}

struct GatherConstraints<'l> {
  var_scope : Vec<Vec<(RefStr, TypeSymbol)>>,
  core : &'l CoreTypes,
  types : &'l mut Types,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  c : &'l mut Constraints,
  errors : &'l mut Vec<Error>,
}

impl <'l> GatherConstraints<'l> {

  fn new(
    core : &'l CoreTypes,
    types : &'l mut Types,
    gen : &'l mut UIDGenerator,
    cache : &'l StringCache,
    c : &'l mut Constraints,
    errors : &'l mut Vec<Error>,
  ) -> GatherConstraints<'l> {
    GatherConstraints {
      var_scope: vec![],
      core, types, gen, cache, c, errors,
    }
  }

  fn log_error<V>(&mut self, r : Result<V, Error>) -> Option<V> {
    match r {
      Ok(v) => Some(v),
      Err(e) => { self.errors.push(e); None } 
    }
  }

  fn expr_to_type(&mut self, e : &Expr) -> Option<Type> {
    let r = self.types.expr_to_type(self.cache, self.gen, e);
    self.log_error(r)
  }

  fn expr_to_type_id(&mut self, e : &Expr) -> Option<TypeId> {
    let r = self.types.expr_to_type_id(self.cache, self.gen, e);
    self.log_error(r)
  }

  fn type_symbol(&mut self) -> TypeSymbol {
    let ts = TypeSymbol(self.gen.next().into());
    self.c.symbols.push(ts);
    ts
  }

  fn node_id_to_symbol(&mut self, n : NodeId) -> TypeSymbol {
    if let Some(ts) = self.c.node_symbols.get(&n) { *ts }
    else {
      let ts = self.type_symbol();
      self.c.node_symbols.insert(n, ts);
      ts
    }
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.c.equalivalent.push((a, b));
  }

  fn assert(&mut self, ts : TypeSymbol, t : Type) {
    let t = self.types.type_id(self.gen, t);
    self.c.assert.push((ts, t));
  }

  fn tagged_symbol(&mut self, ts : TypeSymbol, type_expr : &Option<Box<Expr>>) {
    if let Some(type_expr) = type_expr {
      if let Some(t) = self.expr_to_type(type_expr) {
        self.assert(ts, t);
      }
    }
  }

  fn add_var_to_scope(&mut self, name : RefStr) -> TypeSymbol {
    let ts = self.type_symbol();
    let scope = self.var_scope.last_mut().unwrap();
    scope.push((name.clone(), ts));
    ts
  }

  fn type_definition(&mut self, td : TypeDefConstraints) {
    let a = (); // TODO: check duplicates
    self.c.type_def.push(td);
  }

  fn function_call(&mut self, f : FunctionCallConstraints) {
    self.c.function_call.push(f);
  }

  fn function_definition(&mut self, f : FunctionDefConstraints) {
    let a = (); // TODO: check duplicates
    self.c.function_def.push(f);
  }

  fn global_definition(&mut self, name : RefStr, ts : TypeSymbol) {
    let a = (); // TODO: check duplicates
    self.c.global_def.insert(name, ts);
  }

  fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
    let ts = self.node_id_to_symbol(id);
    match &n.get(id).content {
      Literal(val) => {
        let t = literal_to_type(self.core.string, val);
        self.assert(ts, t);
        self.c.literals.push((ts, val.clone()));
      }
      VariableInitialise{ name, type_tag, value } => {
        self.assert(ts, Type::Void);
        let var_type_symbol = self.add_var_to_scope(name.clone());
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
      }
      Assignment{ assignee , value } => {
        self.assert(ts, Type::Void);
        let a = self.process_node(n, *assignee);
        let b = self.process_node(n, *value);
        self.equalivalent(a, b);
      }
      IfThen{ condition, then_branch } => {
        self.assert(ts, Type::Void);
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        self.assert(cond, Type::Bool);
        self.assert(then_br, Type::Void);
      }
      IfThenElse{ condition, then_branch, else_branch } => {
        let cond = self.process_node(n, *condition);
        let then_br = self.process_node(n, *then_branch);
        let else_br = self.process_node(n, *else_branch);
        self.equalivalent(ts, then_br);
        self.assert(cond, Type::Bool);
        self.equalivalent(then_br, else_br);
      }
      Block(ns) => {
        let len = ns.len();
        if len > 0 {
          for child in &ns[0..(len-1)] {
            let c = self.process_node(n, *child);
            self.assert(c, Type::Void);
          }
          let c = self.process_node(n, ns[len-1]);
          self.equalivalent(ts, c);
        }
        else {
          self.assert(ts, Type::Void);
        }
      }
      Quote(_e) => {
        let expr_def = self.types.type_definition_id(self.gen, self.cache.get("expr"));
        let t = self.types.type_id(self.gen, Type::Def(expr_def));
        self.assert(ts, Ptr(t));
      }
      Reference(name) => {
        let a = (); // TODO: Figure out wtf this is referencing!
      }
      Content::FunctionDefinition{ name, args, return_tag, body } => {
        self.assert(ts, Type::Void);
        let mut ts_args : Vec<(RefStr, TypeSymbol)> = vec![];
        for (arg_name, type_tag) in args.iter() {
          let arg_type_symbol = self.add_var_to_scope(arg_name.clone());
          self.tagged_symbol(arg_type_symbol, type_tag);
          ts_args.push((arg_name.clone(), arg_type_symbol));
        }
        let return_type = self.type_symbol();
        self.tagged_symbol(return_type, return_tag);
        let body_ts = self.process_node(n, *body);
        self.equalivalent(return_type, body_ts);
        let f = FunctionDefConstraints { name: name.clone(), args: ts_args, return_type, };
        self.function_definition(f);
        // Need new scope stack for new function
        let mut gc = GatherConstraints::new(self.core, self.types, self.gen, self.cache, self.c, self.errors);
        gc.process_node(n, *body);
      }
      CBind { name, type_tag } => {
        self.assert(ts, Type::Void);
        let cbind_ts = self.type_symbol();
        if let Some(t) = self.expr_to_type(type_tag) {
          self.assert(cbind_ts, t);
        }
        self.global_definition(name.clone(), cbind_ts);
      }
      Content::TypeDefinition{ name, kind, fields } => {
        self.assert(ts, Type::Void);
        let mut ts_fields : Vec<(RefStr, TypeSymbol)> = vec![];
        for (field_name, type_tag) in fields.iter() {
          let field_type_symbol = self.type_symbol();
          self.tagged_symbol(field_type_symbol, type_tag);
          ts_fields.push((field_name.clone(), field_type_symbol));
        }
        let td = TypeDefConstraints { name: name.clone(), kind: *kind, fields: ts_fields };
        self.type_definition(td);
      }
      TypeConstructor{ name, field_values } => {
        let mut fields : Vec<(Option<RefStr>, TypeSymbol)> = vec![];
        for (field_name, value) in field_values.iter() {
          let field_type_symbol = self.process_node(n, *value);
          fields.push((field_name.clone(), field_type_symbol));
        }
        let tc = ConstructorConstraints{ type_name: name.clone(), fields, result: ts };
        self.c.constructors.push(tc);
      }
      FieldAccess{ container, field } => {
        let fa = FieldAccessConstraints {
          container: self.process_node(n, *container),
          field: field.clone(),
          result: ts,
        };
        self.c.field_access.push(fa);
      }
      Index{ container, index } => {
        let index_reference = GlobalReference {
          name : self.cache.get("Index"),
          result: self.type_symbol(),
        };
        let fc = FunctionCallConstraints {
          function: index_reference.result,
          args: [container, index].iter().map(|id| (None, self.process_node(n, **id))).collect(),
          result: ts,
        };
        self.c.global_reference.push(index_reference);
        self.function_call(fc);
      }
      ArrayLiteral(ns) => {
        let element_ts = self.type_symbol();
        for element in ns.iter() {
          let el = self.process_node(n, *element);
          self.equalivalent(el, element_ts);
        }
        self.c.array.insert(ts, element_ts);
      }
      FunctionCall{ function, args } => {
        let fc = FunctionCallConstraints {
          function: self.process_node(n, *function),
          args: args.iter().map(|id| (None, self.process_node(n, *id))).collect(),
          result: ts,
        };
        self.function_call(fc);
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
    ts
  }
}
