
use std::rc::Rc;
use std::fmt::Write;
use std::fmt;
use itertools::Itertools;
use std::hash::Hash;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};
use crate::structure::{
  Node, NodeId, Nodes, Symbol, SymbolId, Content, Val, LabelId, TypeKind, FunctionNode
};

use std::collections::{HashMap, HashSet};
use bimap::BiMap;

pub fn infer_types(gen : &mut UIDGenerator, cache : &StringCache, code : &str, nodes : &Nodes) -> Result<TypedModule, Vec<Error>> {
  let mut c = Constraints::new();
  let mut module = TypedModule::new(gen.next());
  let mut errors = vec![];
  let core = CoreTypes::new(&mut module.types, gen, cache);
  let mut gather = GatherConstraints::new(&core, &mut module, gen, cache, &mut c, &mut errors);
  gather.process_node(nodes, nodes.root);
  let mut i = Inference::new(code, nodes, &mut module, &c, gen, cache, &mut errors);
  i.infer();
  if errors.len() > 0 {
    Err(errors)
  }
  else {
    Ok(module)
  }
}

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

  pub fn get(&self, id : TypeId) -> Type {
    *self.types.get_by_left(&id).unwrap()
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
  t : Type,
  types: &'l Types,
}

impl <'l> fmt::Display for TypeDisplay<'l> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let types = self.types;
    match self.t {
      Type::Fun(sig) => {
        let sig = self.types.signature(sig);
        write!(f, "fun({}) => {}", 
          sig.args.iter()
            .map(|a| types.display(*a))
            .join(", "),
          types.display(sig.return_type))
      }
      Type::Def(s) => {
        let name =
          self.types.type_definition(s)
          .map(|td| td.name.as_ref()).unwrap_or("@unresolved");
        write!(f, "{}", name)
      }
      Type::Array(t) => write!(f, "array({})", types.display(t)),
      Type::Ptr(t) => write!(f, "ptr({})", types.display(t)),
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
  pub fields : Vec<(SymbolId, TypeId)>,
  pub kind : TypeKind,
  pub drop_function : Option<FunctionReference>,
  pub clone_function : Option<FunctionReference>,
  pub definition_location : TextLocation,
}

#[derive(Debug, Clone, Copy)]
pub enum FunctionImplementation {
  Normal(NodeId),
  CFunction(Option<usize>),
  Intrinsic,
}

#[derive(Debug)]
pub struct FunctionDefinition {
  pub module_id : u64,
  pub name_in_code : RefStr,
  pub name_for_codegen : RefStr,
  pub args : Vec<RefStr>,
  pub signature : SigId,
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

// pub fn node_value_type(&self) -> NodeValueType {
//   match &self.content {
//     FieldAccess{..} | Reference{..} |
//     Index{..} | Literal(_) | Quote(_)
//       => NodeValueType::Ref,
//     Block(_) | FunctionCall{..} |
//     IfThenElse{..} | TypeConstructor{..}
//       => NodeValueType::Owned,
//     _ => NodeValueType::Nil,
//   }
// }

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
      functions: vec![],
      globals: HashMap::new(),
      types: Types::new(),
    }
  }

  pub fn find_function(&self, name : &str, args : &[TypeId]) -> Option<&FunctionDefinition> {
    self.functions.iter().find(|def| {
      let sig = self.types.signature(def.signature);
      def.name_in_code.as_ref() == name &&
        sig.args.as_slice() == args
    })
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
  code : &'l str,
  nodes : &'l Nodes,
  m : &'l mut TypedModule,
  c : &'l Constraints,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  errors : &'l mut Vec<Error>,
  resolved : HashMap<TypeSymbol, TypeId>,
}


impl <'l> Inference<'l> {

  fn new(
    code : &'l str,
    nodes : &'l Nodes,
    m : &'l mut TypedModule,
    c : &'l Constraints,
    gen : &'l mut UIDGenerator,
    cache : &'l StringCache,
    errors : &'l mut Vec<Error>)
      -> Self
  {
    Inference {
      code, nodes, m, c, gen, cache, errors,
      resolved: HashMap::new(),
    }
  }

  fn ts_code_slice(&self, c : &Constraints, ts : TypeSymbol) -> &str {
    let loc = c.symbols.get(&ts).unwrap();
    let (start_line, end_line) = (loc.start.line - 1, loc.end.line - 1);
    let mut it =
      // Chain the zero offset for the first line
      [0].iter().cloned().chain(
        // find the newline positions
        self.code.char_indices().filter(|&(_, c)| c == '\n')
        // offset past the \n char
        .map(|(b, _)| b + 1)
      )
      // get the start offsets of the lines we care about
      .enumerate().filter(|&(i, _)| i == start_line || i == end_line)
      .map(|(_, b)| b);
    let l1_start = it.next().unwrap();
    let l2_start = it.next().unwrap_or(l1_start);
    &self.code[l1_start + loc.start.col.. l2_start + loc.end.col]
  }
  
  fn set_type_id(&mut self, ts : TypeSymbol, t : TypeId) {
    let a = (); // TODO: unify!
    let code = self.ts_code_slice(&self.c, ts);
    if !self.resolved.contains_key(&ts) {
      println!("     Inferred type {} for '{}'", self.m.types.display(t), code);
      self.resolved.insert(ts, t);
    }
  }

  fn set_type(&mut self, ts : TypeSymbol, t : Type) {
    let t = self.m.types.type_id(self.gen, t);
    self.set_type_id(ts, t);
  }

  fn get(&self, ts : TypeSymbol) -> Option<TypeId> {
    self.resolved.get(&ts).cloned()
  }

  fn process_constraint(&mut self, c : &Constraint) {
    match c  {
      Constraint::Assert(ts, t) => {
        println!("Asserting type... ");
        self.set_type_id(*ts, *t);
      }
      Constraint::Equalivalent(a, b) => {
        println!("Equivalence... ");
        if let Some(&t) = self.resolved.get(a) {
          self.set_type_id(*b, t);
        }
        else if let Some(&t) = self.resolved.get(b) {
          self.set_type_id(*a, t);
        }
      }
      Constraint::FunctionDef{ name, return_type, args, body, loc } => {
        println!("Function def... ");
        println!("   Args: ");
        for (_, ts) in args.iter() {
          let code = self.ts_code_slice(&self.c, *ts);
          if let Some(t) = self.resolved.get(ts) {
            println!("      {}, {}", code, self.m.types.display(*t));
          }
          else {
            println!("      {}, unresolved, ", code);
          }
        }
        let resolved_args_count = args.iter().flat_map(|(_, ts)| self.resolved.get(ts)).count();
        let return_type = self.resolved.get(return_type);
        if resolved_args_count == args.len() && return_type.is_some() {
          let mut arg_names = vec!();
          let mut arg_types = vec!();
          for (arg, arg_ts) in args.iter() {
            arg_names.push(self.nodes.symbol(*arg).name.clone());
            arg_types.push(*self.resolved.get(arg_ts).unwrap());
          }
          if self.m.find_function(&name, arg_types.as_slice()).is_some() {
            let e = error_raw(loc, "function with that name and signature already defined");
            self.errors.push(e);
            return;
          }
          let signature = FunctionSignature {
            return_type: *return_type.unwrap(),
            args: arg_types,
          };
          let f = FunctionDefinition {
            module_id: self.m.id,
            name_in_code: name.clone(),
            name_for_codegen: format!("{}.{}", name, self.gen.next()).into(),
            args: arg_names,
            signature: self.m.types.signature_id(self.gen, signature),
            implementation: FunctionImplementation::Normal(*body),
            definition_location: *loc,
          };
          self.m.functions.push(f);
          println!("Function {} inferred.", name);
        }
        println!();
      }
      Constraint::FunctionCall{ function, args, result } => {
        let arg_types : Vec<TypeId> =
          args.iter().flat_map(|(_, ts)| self.resolved.get(ts).cloned()).collect();
        match function {
          Function::Name(sym) => {
            let sym = self.nodes.symbol(*sym);
            if let Some(def) = self.m.find_function(&sym.name, arg_types.as_slice()) {
              let return_type = self.m.types.signature(def.signature).return_type;
              self.set_type_id(*result, return_type);
            }
          }
          Function::Value(ts) => {
            panic!();
          }
        }
      }
      Constraint::FieldAccess{ container, field, result } => {
        let def =
          self.resolved.get(container)
          .map(|&id| self.m.types.get(id))
          .and_then(|t| match t { 
            Type::Def(d) => self.m.types.type_definition(d),
            _ => None,
          });
        if let Some(def) = def {
          let field = self.nodes.symbol(*field);
          // TODO: I should probably make SymbolId a MEMBER of Symbol, and
          // get rid of the symbol map on the Types struct. It's just a lot of
          // faff for no reason. I only need symbol ids for mapping to type symbols.
          let f = def.fields.iter().find(|(n, _)| n == &field.name);
          if let Some((_, t)) = f.cloned() {
            self.set_type_id(*result, t);
          }
        }
      }
      Constraint::Array{ array, element } => {
        if let Some(array_type) = self.get(*array) {
          if let Type::Array(element_type) = self.m.types.get(array_type) {
            self.set_type_id(*element, element_type);
          }
        }
        if let Some(element_type) = self.get(*element) {
          self.set_type(*array, Type::Array(element_type));
        }
      }
      _ => (),
    }
  }

  fn infer(&mut self) {
    println!("To resolve: {}", self.c.symbols.len());
    for i in 0..2 {
      for c in self.c.constraints.iter() {
        self.process_constraint(c);
      }
      println!("Resolved after step {}: {}", i, self.resolved.len());
      println!();
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct TypeSymbol(u64);

pub enum Function {
  Value(TypeSymbol),
  Name(SymbolId),
}

pub enum Constraint {
  Assert(TypeSymbol, TypeId),
  Equalivalent(TypeSymbol, TypeSymbol),
  Array{ array : TypeSymbol, element : TypeSymbol },
  Convert{ val : TypeSymbol, into_type : TypeSymbol },
  FieldAccess {
    container : TypeSymbol,
    field : SymbolId,
    result : TypeSymbol,
  },
  Constructor {
    type_name : RefStr,
    fields : Vec<(Option<SymbolId>, TypeSymbol)>,
    result : TypeSymbol,
  },
  FunctionDef {
    name : RefStr,
    return_type : TypeSymbol,
    args : Vec<(SymbolId, TypeSymbol)>,
    body : NodeId,
    loc : TextLocation,
  },
  FunctionCall {
    function : Function,
    args : Vec<(Option<SymbolId>, TypeSymbol)>,
    result : TypeSymbol,
  },
  GlobalDef(RefStr, TypeSymbol),
  GlobalReference {
    name : RefStr,
    result : TypeSymbol,
  }
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
  symbols : HashMap<TypeSymbol, TextLocation>,
  node_symbols : HashMap<NodeId, TypeSymbol>,
  variable_symbols : HashMap<SymbolId, TypeSymbol>,
  constraints : Vec<Constraint>,
}

impl Constraints {
  fn new() -> Self {
    Constraints {
      symbols: HashMap::new(),
      node_symbols: HashMap::new(),
      variable_symbols: HashMap::new(),
      constraints: vec![],
    }
  }
}

struct GatherConstraints<'l> {
  labels : HashMap<LabelId, TypeSymbol>,
  core : &'l CoreTypes,
  m : &'l mut TypedModule,
  gen : &'l mut UIDGenerator,
  cache : &'l StringCache,
  c : &'l mut Constraints,
  errors : &'l mut Vec<Error>,
}

impl <'l> GatherConstraints<'l> {

  fn new(
    core : &'l CoreTypes,
    m : &'l mut TypedModule,
    gen : &'l mut UIDGenerator,
    cache : &'l StringCache,
    c : &'l mut Constraints,
    errors : &'l mut Vec<Error>,
  ) -> GatherConstraints<'l> {
    GatherConstraints {
      labels: HashMap::new(),
      core, m, gen, cache, c, errors,
    }
  }

  fn log_error<V>(&mut self, r : Result<V, Error>) -> Option<V> {
    match r {
      Ok(v) => Some(v),
      Err(e) => { self.errors.push(e); None } 
    }
  }

  fn expr_to_type(&mut self, e : &Expr) -> Option<Type> {
    let r = self.m.types.expr_to_type(self.cache, self.gen, e);
    self.log_error(r)
  }

  fn expr_to_type_id(&mut self, e : &Expr) -> Option<TypeId> {
    let r = self.m.types.expr_to_type_id(self.cache, self.gen, e);
    self.log_error(r)
  }

  fn type_symbol(&mut self, loc : TextLocation) -> TypeSymbol {
    let ts = TypeSymbol(self.gen.next().into());
    self.c.symbols.insert(ts, loc);
    ts
  }

  fn node_to_symbol(&mut self, n : &Node) -> TypeSymbol {
    if let Some(ts) = self.c.node_symbols.get(&n.id) { *ts }
    else {
      let ts = self.type_symbol(n.loc);
      self.c.node_symbols.insert(n.id, ts);
      ts
    }
  }

  fn variable_to_symbol(&mut self, v : &Symbol) -> TypeSymbol {
    if let Some(ts) = self.c.variable_symbols.get(&v.id) { *ts }
    else {
      let ts = self.type_symbol(v.loc);
      self.c.variable_symbols.insert(v.id, ts);
      ts
    }
  }

  fn constraint(&mut self, c : Constraint) {
    self.c.constraints.push(c);
  }

  fn equalivalent(&mut self, a : TypeSymbol, b : TypeSymbol) {
    self.constraint(Constraint::Equalivalent(a, b));
  }

  fn assert(&mut self, ts : TypeSymbol, t : Type) {
    let t = self.m.types.type_id(self.gen, t);
    self.constraint(Constraint::Assert(ts, t));
  }

  fn tagged_symbol(&mut self, ts : TypeSymbol, type_expr : &Option<Box<Expr>>) {
    if let Some(type_expr) = type_expr {
      if let Some(t) = self.expr_to_type(type_expr) {
        self.assert(ts, t);
      }
    }
  }

  fn process_node(&mut self, n : &Nodes, id : NodeId)-> TypeSymbol {
    let node = n.node(id);
    let ts = self.node_to_symbol(node);
    match &node.content {
      Literal(val) => {
        let t = literal_to_type(self.core.string, val);
        self.assert(ts, t);
      }
      LocalInitialise{ name, type_tag, value } => {
        self.assert(ts, Type::Void);
        let var_type_symbol = self.variable_to_symbol(n.symbol(*name));
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
      }
      GlobalInitialise{ name, type_tag, value } => {
        self.assert(ts, Type::Void);
        let name = n.symbol(*name);
        let var_type_symbol = self.variable_to_symbol(name);
        self.tagged_symbol(var_type_symbol, type_tag);
        let vid = self.process_node(n, *value);
        self.equalivalent(var_type_symbol, vid);
        let a = (); // TODO: check duplicates
        self.constraint(Constraint::GlobalDef(name.name.clone(), var_type_symbol));
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
            self.process_node(n, *child);
          }
          let c = self.process_node(n, ns[len-1]);
          self.equalivalent(ts, c);
        }
        else {
          self.assert(ts, Type::Void);
        }
      }
      Quote(_e) => {
        let expr_def = self.m.types.type_definition_id(self.gen, self.cache.get("expr"));
        let t = self.m.types.type_id(self.gen, Type::Def(expr_def));
        self.assert(ts, Ptr(t));
      }
      Reference{ name, refers_to } => {
        if let Some(refers_to) = refers_to {
          let var_type = self.variable_to_symbol(n.symbol(*refers_to));
          self.equalivalent(ts, var_type);
        }
        else {
          self.constraint(Constraint::GlobalReference{ name: name.clone(), result: ts });
        }
      }
      Content::FunctionDefinition{ name, args, return_tag, body } => {
        self.assert(ts, Type::Void);
        let mut ts_args : Vec<(SymbolId, TypeSymbol)> = vec![];
        for (arg, type_tag) in args.iter() {
          let arg_type_symbol = self.variable_to_symbol(n.symbol(*arg));
          self.tagged_symbol(arg_type_symbol, type_tag);
          ts_args.push((*arg, arg_type_symbol));
        }
        let return_type = self.process_node(n, *body);
        self.tagged_symbol(return_type, return_tag);
        let a = (); // TODO: check duplicates
        let f = Constraint::FunctionDef { 
          name: name.clone(), args: ts_args,
          return_type, body: *body, loc: node.loc };
        self.constraint(f);
        // Need new scope stack for new function
        let mut gc = GatherConstraints::new(self.core, self.m, self.gen, self.cache, self.c, self.errors);
        gc.process_node(n, *body);
      }
      CBind { name, type_tag } => {
        self.assert(ts, Type::Void);
        let cbind_ts = self.type_symbol(node.loc);
        if let Some(t) = self.expr_to_type(type_tag) {
          self.assert(cbind_ts, t);
        }
        let a = (); // TODO: check duplicates
        self.constraint(Constraint::GlobalDef(name.clone(), cbind_ts));
      }
      Content::TypeDefinition{ name, kind, fields } => {
        self.assert(ts, Type::Void);
        if self.m.type_defs.get(name).is_some() {
          let e = error_raw(node.loc, "type with this name already defined");
          self.errors.push(e)
        }
        else {
          // TODO: check for duplicates?
          let mut typed_fields = vec![];
          for (field, type_tag) in fields.iter() {
            if let Some(t) = self.expr_to_type_id(&type_tag.unwrap()) {
              typed_fields.push((*field, t));
            }
          }
          // TODO: Generics?
          let def = TypeDefinition {
            name: name.clone(),
            fields: typed_fields,
            kind: *kind,
            drop_function: None, clone_function: None,
            definition_location: node.loc,
          };
          self.m.type_defs.insert(name.clone(), def);
        }
      }
      TypeConstructor{ name, field_values } => {
        let mut fields : Vec<(Option<SymbolId>, TypeSymbol)> = vec![];
        for (field, value) in field_values.iter() {
          let field_type_symbol = self.process_node(n, *value);
          fields.push((*field, field_type_symbol));
        }
        let tc = Constraint::Constructor{ type_name: name.clone(), fields, result: ts };
        self.constraint(tc);
      }
      FieldAccess{ container, field } => {
        let fa = Constraint::FieldAccess {
          container: self.process_node(n, *container),
          field: field.clone(),
          result: ts,
        };
        self.constraint(fa);
      }
      Index{ container, index } => {
        // TODO: How do we link the index type here to the index type in the array?
        // I suppose through the definition of a generic index function, which needs to exist
        // somewhere...
        let a = ();
        let index_tc = self.type_symbol(node.loc);
        let index_reference = Constraint::GlobalReference {
          name : self.cache.get("Index"),
          result: index_tc,
        };
        let fc = Constraint::FunctionCall {
          function: Function::Value(index_tc),
          args: vec![
            (None, self.process_node(n, *container)),
            (None, self.process_node(n, *index)),
          ],
          result: ts,
        };
        self.constraint(index_reference);
        self.constraint(fc);
      }
      ArrayLiteral(ns) => {
        let element_ts = self.type_symbol(node.loc);
        for element in ns.iter() {
          let el = self.process_node(n, *element);
          self.equalivalent(el, element_ts);
        }
        self.constraint(Constraint::Array{ array: ts, element: element_ts });
      }
      FunctionCall{ function, args } => {
        let function = match function {
          FunctionNode::Name(name) => Function::Name(*name),
          FunctionNode::Value(val) => {
            let val = self.process_node(n, *val);
            Function::Value(val)
          }
        };
        let fc = Constraint::FunctionCall {
          function,
          args: args.iter().map(|id| (None, self.process_node(n, *id))).collect(),
          result: ts,
        };
        self.constraint(fc);
      }
      While{ condition, body } => {
        self.assert(ts, Type::Void);
        let cond = self.process_node(n, *condition);
        let body = self.process_node(n, *body);
        self.assert(cond, Type::Bool);
        self.assert(body, Type::Void);
      }
      Convert{ from_value, into_type } => {
        let v = self.process_node(n, *from_value);
        if let Some(t) = self.expr_to_type(into_type) {
          self.assert(ts, t);
          let convert_ts = self.type_symbol(node.loc);
          let convert_reference = Constraint::GlobalReference {
            name : self.cache.get("Convert"),
            result: convert_ts,
          };
          let fc = Constraint::FunctionCall {
            function: Function::Value(convert_ts),
            args: vec![(None, v)],
            result: ts,
          };
          self.constraint(convert_reference);
          self.constraint(fc);
        }
      }
      SizeOf{ type_tag } => {
        let a = (); // TODO: there is no way of accessing the type during codegen
        self.expr_to_type(type_tag);
        self.assert(ts, Type::U64);
      }
      Label{ label, body } => {
        self.labels.insert(*label, ts);
        let body = self.process_node(n, *body);
        self.equalivalent(ts, body);
      }
      BreakToLabel{ label, return_value } => {
        self.assert(ts, Type::Void);
        let label_ts = *self.labels.get(label).unwrap();
        if let Some(v) = return_value {
          let v = self.process_node(n, *v);
          self.equalivalent(label_ts, v);
        }
        else {
          self.assert(label_ts, Type::Void);
        }
      }
    }
    ts
  }
}
