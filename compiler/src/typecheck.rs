
use std::rc::Rc;
use std::fmt::Write;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

use std::collections::HashMap;

use std::hash::Hash;

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
  Array(Box<Type>),
  Ptr(Box<Type>),
  Tuple(Vec<Type>),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Val {
  Void,
  F64(f64),
  F32(f32),
  I64(i64),
  U64(u64),
  I32(i32),
  U32(u32),
  U16(u16),
  U8(u8),
  String(String),
  Bool(bool),
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
  pub return_type : Type,
  pub args : Vec<Type>,
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
#[derive(Debug)]
pub struct FunctionReference {
  pub name_in_code : RefStr,
  pub name_for_codegen : RefStr,
  pub module_id : u64,
}

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableReference(RefStr),
  VariableInitialise(RefStr, Box<TypedNode>, VarScope),
  Assignment(Box<(TypedNode, TypedNode)>),
  IfThen(Box<(TypedNode, TypedNode)>),
  IfThenElse(Box<(TypedNode, TypedNode, TypedNode)>),
  Block(Vec<TypedNode>),
  Quote(Box<Expr>),
  FunctionReference(FunctionReference),
  FunctionDefinition(RefStr),
  CBind(RefStr),
  TypeDefinition(RefStr),
  StructInstantiate(RefStr, Vec<TypedNode>),
  UnionInstantiate(RefStr, Box<(RefStr, TypedNode)>),
  FieldAccess(Box<(TypedNode, RefStr)>),
  Index(Box<(TypedNode, TypedNode)>),
  ArrayLiteral(Vec<TypedNode>),
  FunctionCall(Box<TypedNode>, Vec<TypedNode>),
  IntrinsicCall(RefStr, Vec<TypedNode>),
  While(Box<(TypedNode, TypedNode)>),
  ExplicitReturn(Option<Box<TypedNode>>),
  Convert(Box<TypedNode>),
  SizeOf(Box<Type>),
  Break,
}

#[derive(Debug)]
pub struct TypedNode {
  pub type_tag : Type,
  pub content : Content,
  pub loc : TextLocation,
}

impl TypedNode {
  fn assert_type(&self, expected : Type) -> Result<(), Error> {
    if self.type_tag == expected {
      Ok(())
    }
    else {
      error(self.loc, format!("expected type {:?}, found type {:?}", expected, self.type_tag))
    }
  }
}

fn node(expr : &Expr, type_tag : Type, content : Content) -> TypedNode {
  TypedNode {
    type_tag,
    content,
    loc: expr.loc,
  }
}

pub struct GlobalDefinition {
  pub name : RefStr,
  pub type_tag : Type,
  pub c_address : Option<usize>,
}

#[derive(PartialEq, Eq, Hash)]
pub struct FunctionIdentity {
  name : RefStr,
  args : Vec<Type>,
}

type FunctionKey = Rc<FunctionIdentity>;

// TODO: REMOVE
// pub struct CachedHash<T : std::hash::Hash> {
//   hash : u64,
//   t : T,
// }

// impl <T : std::hash::Hash> CachedHash<T> {
//   pub fn new(t : T) -> Self {
//     t.hash(state: &mut H)
//   }
// }

#[derive(Clone)]
pub struct TypedModule {
  pub id : u64,
  pub types : HashMap<RefStr, Rc<TypeDefinition>>,
  pub functions : Vec<Rc<FunctionDefinition>>,
  pub globals : HashMap<RefStr, Rc<GlobalDefinition>>,
}

impl TypedModule {
  pub fn new(id : u64) -> TypedModule {
    TypedModule{ id, types: HashMap::new(), functions: vec![], globals: HashMap::new() }
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

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  scope_map: Vec<HashMap<RefStr, RefStr>>,
}

impl <'l> TypeChecker<'l> {

  pub fn new(
    uid_generator : &'l mut UIDGenerator,
    module : &'l mut TypedModule,
    modules : &'l [&'l TypedModule],
    local_symbol_table : &'l HashMap<RefStr, usize>,
    cache : &'l StringCache)
      -> TypeChecker<'l>
  {
    TypeChecker {
      uid_generator,
      module,
      modules,
      local_symbol_table,
      type_definition_references: vec!(),
      cache,
    }
  }

  fn iter_modules(&self) -> impl Iterator<Item=&TypedModule> {
    std::iter::once(self.module as &TypedModule).chain(self.modules.iter().cloned())
  }

  fn find_in_modules<RV>(&'l self, find : impl Fn(&'l TypedModule) -> Option<RV>) -> Option<RV> {
    if let Some(v) = find(&self.module) { return Some(v); }
    for m in self.modules {
      if let Some(v) = find(m) { return Some(v); }
    }
    None
  }

  fn find_f<T>(&self, name : &str, f : fn(&TypedModule) -> &HashMap<RefStr, T>) -> Option<&T> {
    self.iter_modules().flat_map(|m| f(m).get(name)).nth(0)
  }

  fn find_global(&self, name : &str) -> Option<&Rc<GlobalDefinition>> {
    self.find_f(name, |m| &m.globals)
  }

  fn find_function(&self, name : &str, args : &[Type]) -> Option<&Rc<FunctionDefinition>> {
    self.iter_modules().flat_map(|m|
      m.functions.iter().find(|def|
        def.name_in_code.as_ref() == name &&
        def.signature.args.as_slice() == args))
    .next()
  }

  fn find_functions<'f>(&'f self, name : &'f str) -> impl Iterator<Item=&'f Rc<FunctionDefinition>> {
    self.iter_modules().flat_map(move |m| m.functions.iter().filter(move |def| def.name_in_code.as_ref() == name))
  }

  fn find_type_def(&self, name : &str) -> Option<&Rc<TypeDefinition>> {
    self.find_f(name, |m| &m.types)
  }

  fn add_global(&mut self, name : RefStr, def : GlobalDefinition) {
    self.module.globals.insert(name, Rc::new(def));
  }

  fn add_function(&mut self, def : FunctionDefinition) {
    self.module.functions.push(Rc::new(def));
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    if let Some(name) = expr.try_symbol() {
      if let Some(t) = Type::from_string(name) {
        return Ok(t);
      }
      let name = self.cache.get(name);
      self.type_definition_references.push(SymbolReference{ symbol_name: name.clone(), reference_location: expr.loc });
      return Ok(Type::Def(name));
    }
    match expr.try_construct() {
      Some(("fun", es)) => {
        if let Some(args) = es.get(0) {
          let args =
            args.children().iter()
            .map(|e| {
              let e = if let Some((":", [_name, tag])) = e.try_construct() {tag} else {e};
              self.to_type(e)
            })
            .collect::<Result<Vec<Type>, Error>>()?;
          let return_type = if let Some(t) = es.get(1) {
            self.to_type(t)?
          }
          else {
            Type::Void
          };
          return Ok(Type::Fun(Rc::new(FunctionSignature{ args, return_type})));
        }
      }
      Some(("call", [name, t])) => {
        match name.unwrap_symbol()? {
          "ptr" => {
            let t = self.to_type(t)?;
            return Ok(Type::Ptr(Box::new(t)))
          }
          "array" => {
            let t = self.to_type(t)?;
            return Ok(Type::Array(Box::new(t)))
          }
          _ => (),
        }
      }
      _ => ()
    }
    error(expr, "invalid type expression")
  }

  fn add_type_definition(&mut self, expr : &Expr) -> Result<(), Error> {
    let (kind, children) = expr.unwrap_construct()?;
    let kind = match kind {
      "union" => TypeKind::Union,
      "struct" => TypeKind::Struct,
      _ => panic!(),
    };
    if let [name_expr, fields_expr] = children {
      let name = name_expr.unwrap_symbol()?;
      if self.find_type_def(name).is_some() {
        return error(expr, "type with this name already defined");
      }
      // TODO: check for duplicates?
      let field_exprs = fields_expr.children();
      let mut fields = vec![];
      for f in field_exprs {
        fields.push(self.typed_symbol(f)?);
      }
      // TODO: Generics?
      let name = self.cache.get(name);
      let def = TypeDefinition { name: name.clone(), fields, kind };
      self.module.types.insert(name, Rc::new(def));
      return Ok(());
    }
    return error(expr, "malformed type definition");
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(RefStr, Type), Error> {
    if let Some((":", [s, t])) = e.try_construct() {
      let name = self.cache.get(s.unwrap_symbol()?);
      let type_tag = self.to_type(t)?;
      Ok((name, type_tag))
    }
    else if let Ok(s) = e.unwrap_symbol() {
      let name = self.cache.get(s);
      Ok((name, Type::Dynamic))
    }
    else {
      error(e, "invalid typed symbol construct")
    }
  }
}

impl <'l, 'lt> FunctionChecker<'l, 'lt> {

  pub fn new(
    t : &'l mut TypeChecker<'lt>,
    is_top_level : bool,
    variables : HashMap<RefStr, Type>)
      -> FunctionChecker<'l, 'lt>
  {
    let global_map = t.module.globals.keys().map(|n| (n.clone(), n.clone())).collect();
    FunctionChecker {
      t,
      is_top_level,
      variables,
      scope_map: vec!(global_map),
    }
  }

  fn cached(&self, s : &str) -> RefStr {
    self.t.cache.get(s)
  }

  fn get_scoped_variable_name(&self, name : &RefStr) -> RefStr {
    for m in self.scope_map.iter().rev() {
      if let Some(n) = m.get(name) {
        return n.clone();
      }
    }
    return name.clone();
  }

  fn create_scoped_variable_name(&mut self, name : RefStr) -> RefStr {
    let mut unique_name = name.to_string();
    let mut i = 0;
    while self.t.find_global(unique_name.as_str()).is_some() ||
      self.variables.contains_key(unique_name.as_str())
    {
      unique_name.clear();
      i += 1;
      write!(&mut unique_name, "{}#{}", name, i).unwrap();
    }
    let unique_name : RefStr = unique_name.into();
    self.scope_map.last_mut().unwrap().insert(name, unique_name.clone());
    unique_name.clone()
  }

  // TODO: this coerces empty arrays into whatever type they're supposed to have.
  // It's probably broken though, because it's using the pointer type instead of the array type.Clone
  // No idea. Decide what to do with it!
  //
  // fn coerce_to_type(&mut self, mut node : TypedNode, t : &Type) -> Result<TypedNode, Error> {
  //   if &node.type_tag == t {
  //     return Ok(node);
  //   }
  //   match (&node.content, t) {
  //     (Content::ArrayLiteral(ns), Type::Ptr(_)) => {
  //       if ns.len() == 0 {
  //         node.type_tag = t.clone();
  //         return Ok(node);
  //       }
  //     }
  //     _ => (),
  //   }
  //   error(node.loc, format!("expected type {:?}, found {:?}", t, node.type_tag))
  // }

  fn to_type_literal(&mut self, expr : &Expr, exprs : &[Expr]) -> Result<TypedNode, Error> {
    if exprs.len() < 1 {
      return error(expr, format!("malformed type instantiation"));
    }
    let name_expr = &exprs[0];
    let field_exprs = &exprs[1..];
    let name = name_expr.unwrap_symbol()?;
    let fields =
      field_exprs.iter().map(|e| {
        if let Some((":", [name, value])) = e.try_construct() {
          Ok((Some(name), self.to_ast(value)?))
        }
        else {
          Ok((None, self.to_ast(e)?))
        }
      })
      .collect::<Result<Vec<(Option<&Expr>, TypedNode)>, Error>>()?;
    let def =
      self.t.find_type_def(name)
      .ok_or_else(|| error_raw(name_expr, "no type with this name exists"))?;
    match &def.kind {
      TypeKind::Struct => {
        if fields.len() != def.fields.len() {
          return error(expr, "wrong number of fields");
        }
        let field_iter = fields.iter().zip(def.fields.iter());
        for ((field, value), (expected_name, expected_type)) in field_iter {
          if let Some(field) = field {
            if field.unwrap_symbol()? != expected_name.as_ref() {
              return error(*field, "incorrect field name");
            }
          }
          if &value.type_tag != expected_type {
            return error(value.loc, format!("type mismatch. expected {:?}, found {:?}", expected_type, value.type_tag));
          }
        }
        let c = Content::StructInstantiate(self.cached(name), fields.into_iter().map(|v| v.1).collect());
        Ok(node(expr, Type::Def(def.name.clone()), c))
      }
      TypeKind::Union => {
        if fields.len() != 1 {
          return error(expr, "must instantiate exactly one field");
        }
        let (field, value) = fields.into_iter().nth(0).unwrap();
        if field.is_none() {
          return error(expr, "the union field to initialise must be specified");
        }
        let field = field.unwrap();
        let field_name = self.cached(field.unwrap_symbol()?);
        if def.fields.iter().find(|(n, _)| n == &field_name).is_none() {
          return error(field, "field does not exist in this union");
        }
        let c = Content::UnionInstantiate(self.cached(name), Box::new((field_name, value)));
        Ok(node(expr, Type::Def(def.name.clone()), c))
      }
    }
  }

  fn construct_to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let (instr, children) = expr.unwrap_construct()?;
    match (instr, children) {
      ("break", []) => {
        return Ok(node(expr, Type::Void, Content::Break));
      }
      ("call", exprs) => {
        let function_expr = &exprs[0];
        match function_expr.try_symbol() {
          Some("new") => return self.to_type_literal(expr, &exprs[1..]),
          Some("sizeof") => {
            if exprs.len() == 2 {
              let type_tag = self.t.to_type(&exprs[1])?;
              return Ok(node(expr, Type::U64, Content::SizeOf(Box::new(type_tag))));
            }
          }
          _ => (),
        }
        let args =
          exprs[1..].iter().map(|e| self.to_ast(e))
          .collect::<Result<Vec<TypedNode>, Error>>()?;
        if let Some(function_name) = function_expr.try_symbol() {
          let op_tag = match_intrinsic(function_name, args.as_slice());
          if let Some(op_tag) = op_tag {
            return Ok(node(expr, op_tag, Content::IntrinsicCall(self.cached(function_name), args)))
          }
          for def in self.t.find_functions(function_name) {
            let i = args.iter().map(|n| &n.type_tag);
            if def.signature.args.iter().eq(i) {
              let fr_content = Content::FunctionReference(def.function_reference());
              let fr = node(function_expr, Type::Fun(def.signature.clone()), fr_content);
              let content = Content::FunctionCall(Box::new(fr), args);
              return Ok(node(expr, def.signature.return_type.clone(), content))
            }
          }
        }
        let function_value = self.to_ast(function_expr)?;
        if let Type::Fun(sig) = &function_value.type_tag {
          if sig.args.len() != args.len() {
            return error(expr, "incorrect number of arguments passed");
          }
          let return_type = sig.return_type.clone();
          let content = Content::FunctionCall(Box::new(function_value), args);
          return Ok(node(expr, return_type, content));
        }
        error(&exprs[0], "no function match this name and parameters")
      }
      ("as", [a, b]) => {
        let a = self.to_ast(a)?;
        let t = self.t.to_type(b)?;
        Ok(node(expr, t, Content::Convert(Box::new(a))))
      }
      ("&&", [a, b]) => {
        let a = self.to_ast(a)?;
        let b = self.to_ast(b)?;
        Ok(node(expr, Type::Bool, Content::IntrinsicCall(self.cached(instr), vec!(a, b))))
      }
      ("||", [a, b]) => {
        let a = self.to_ast(a)?;
        let b = self.to_ast(b)?;
        Ok(node(expr, Type::Bool, Content::IntrinsicCall(self.cached(instr), vec!(a, b))))
      }
      ("let", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let v = Box::new(self.to_ast(value_expr)?);
          // The first scope is used for function arguments. The second
          // is the top level of the function.
          let c = if self.is_top_level && self.scope_map.len() == 2 {
            // global variable
            let def = GlobalDefinition { name: name.clone(), type_tag: v.type_tag.clone(), c_address: None };
            self.t.add_global(name.clone(), def);
            Content::VariableInitialise(name, v, VarScope::Global)
          }
          else {
            // local variable
            let scoped_name = self.create_scoped_variable_name(name);
            self.variables.insert(scoped_name.clone(), v.type_tag.clone());
            Content::VariableInitialise(scoped_name, v, VarScope::Local)
          };
          return Ok(node(expr, Type::Void, c));
        }
        error(expr, "malformed let expression")
      }
      // TODO this is a very stupid approach
      ("quote", [e]) => {
        Ok(node(expr, Type::Ptr(Box::new(Type::U8)), Content::Quote(Box::new(e.clone()))))
      }
      ("=", [assign_expr, value_expr]) => {
        let a = self.to_ast(assign_expr)?;
        let b = self.to_ast(value_expr)?;
        Ok(node(expr, Type::Void, Content::Assignment(Box::new((a, b)))))
      }
      ("return", exprs) => {
        if exprs.len() > 1 {
          return error(expr, format!("malformed return expression"));
        }
        let (return_val, type_tag) =
          if exprs.len() == 1 {
            let v = self.to_ast(&exprs[0])?;
            let t = v.type_tag.clone();
            (Some(Box::new(v)), t)
          }
          else {
            (None, Type::Void)
          };
        Ok(node(expr, type_tag, Content::ExplicitReturn(return_val)))
      }
      ("while", [condition_node, body_node]) => {
        let condition = self.to_ast(condition_node)?;
        let body = self.to_ast(body_node)?;
        Ok(node(expr, Type::Void, Content::While(Box::new((condition, body)))))
      }
      ("if", exprs) => {
        if exprs.len() > 3 {
          return error(expr, "malformed if expression");
        }
        let condition = self.to_ast(&exprs[0])?;
        condition.assert_type(Type::Bool)?;
        let then_branch = self.to_ast(&exprs[1])?;
        if exprs.len() == 3 {
          let else_branch = self.to_ast(&exprs[2])?;
          if then_branch.type_tag != else_branch.type_tag {
            return error(expr, "if/else branch type mismatch");
          }
          let t = then_branch.type_tag.clone();
          let c = Content::IfThenElse(Box::new((condition, then_branch, else_branch)));
          Ok(node(expr, t, c))
        }
        else {
          Ok(node(expr, Type::Void, Content::IfThen(Box::new((condition, then_branch)))))
        }
      }
      ("block", exprs) => {
        self.scope_map.push(HashMap::new());
        let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<TypedNode>, Error>>()?;
        self.scope_map.pop();
        let tag = nodes.last().map(|n| n.type_tag.clone()).unwrap_or(Type::Void);
        Ok(node(expr, tag, Content::Block(nodes)))
      }
      ("cbind", [e]) => {
        if let (":", [name_expr, type_expr]) = e.unwrap_construct()? {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let type_tag = self.t.to_type(type_expr)?;
          let address = self.t.local_symbol_table.get(&name).map(|v| *v);
          if address.is_none() {
            // TODO: check the signature of the function too
            println!("Warning: C binding '{}' not linked. LLVM linker may link it instead.", name);
            // return error(expr, "tried to bind non-existing C function")
          }
          // TODO: Why is it necessary to treat function pointers specially? If I treat
          // them as globals the tests stop passing, but I'm not sure why.
          if let Type::Fun(sig) = &type_tag {
            let args =
              sig.args.iter().enumerate().
              map(|(i, _)| ((i + 65) as u8 as char).to_string().into())
              .collect();
            let def = FunctionDefinition {
              name_in_code: name.clone(),
              name_for_codegen: name.clone(),
              args,
              signature: sig.clone(),
              implementation: FunctionImplementation::CFunction(address),
              module_id: self.t.module.id,
            };
            self.t.add_function(def);
          }
          else {
            let def = GlobalDefinition { name: name.clone(), type_tag, c_address: address };
            self.t.add_global(name.clone(), def);
          }
          return Ok(node(expr, Type::Void, Content::CBind(name)))
        }
        error(expr, "invalid cbind expression")
      }
      ("fun", exprs) => {
        if let [name, args_exprs, function_body] = exprs {
          let name = self.cached(name.unwrap_symbol()?);
          let args_exprs = args_exprs.children();
          let mut arg_names = vec!();
          let mut arg_types = vec!();
          for arg in args_exprs.iter() {
            let (name, type_tag) = self.t.typed_symbol(arg)?;
            if type_tag == Type::Void {
              return error(expr, "functions args cannot be void");
            }
            arg_names.push(name);
            arg_types.push(type_tag);
          }
          let args = arg_names.iter().cloned().zip(arg_types.iter().cloned()).collect();
          let mut function_checker = FunctionChecker::new(self.t, false, args);
          let body = function_checker.to_ast(function_body)?;
          if self.t.find_function(&name, arg_types.as_slice()).is_some() {
            return error(expr, "function with that name already defined");
          }
          let signature = Rc::new(FunctionSignature {
            return_type: body.type_tag.clone(),
            args: arg_types,
          });
          let def = FunctionDefinition {
            name_in_code: name.clone(),
            name_for_codegen: format!("{}.{}", name, self.t.uid_generator.next()).into(),
            args: arg_names,
            signature,
            implementation: FunctionImplementation::Normal(body),
            module_id: self.t.module.id,
          };
          self.t.add_function(def);
          return Ok(node(expr, Type::Void, Content::FunctionDefinition(name)))
        }
        error(expr, "malformed function definition")
      }
      ("union", exprs) => {
        let name = self.cached(&exprs[0].unwrap_symbol()?);
        Ok(node(expr, Type::Void, Content::TypeDefinition(name)))
      }
      ("struct", exprs) => {
        let name = self.cached(&exprs[0].unwrap_symbol()?);
        Ok(node(expr, Type::Void, Content::TypeDefinition(name)))
      }
      (".", [container_expr, field_expr]) => {
        let container_val = self.to_ast(container_expr)?;
        let field_name = self.cached(field_expr.unwrap_symbol()?);
        let def = match &container_val.type_tag {
          Type::Def(type_name) => self.t.find_type_def(type_name).unwrap(),
          _ => return error(container_expr, format!("expected struct or union, found {:?}", container_val.type_tag)),
        };
        let (_, field_type) =
          def.fields.iter().find(|(n, _)| n==&field_name)
          .ok_or_else(|| error_raw(field_expr, "type does not have field with this name"))?;
        let field_type = field_type.clone();
        let c = Content::FieldAccess(Box::new((container_val, field_name)));
        Ok(node(expr, field_type, c))
      }
      ("array", exprs) => {
        let mut elements = vec!();
        for e in exprs {
          elements.push(self.to_ast(e)?);
        }
        let t =
          if let Some(a) = elements.first() {
            for b in &elements[1..] {
              if a.type_tag != b.type_tag {
                return error(expr, format!("array initialiser contains more than one type."));
              }
            }
            a.type_tag.clone()
          }
          else {
            // dummy value for an empty array
            Type::U8
          };
        Ok(node(expr, Type::Array(Box::new(t)), Content::ArrayLiteral(elements)))
      }
      ("index", exprs) => {
        let array_expr = &exprs[0];
        if let [index_expr] = &exprs[1..] {
          let array = self.to_ast(array_expr)?;
          let inner_type = match &array.type_tag {
            Type::Array(t) => *(t).clone(),
            _ => return error(array_expr, "expected array"),
          };
          let index = self.to_ast(index_expr)?;
          if index.type_tag != Type::I64 {
            return error(array_expr, "expected integer");
          }
          return Ok(node(expr, inner_type, Content::Index(Box::new((array, index)))));
        }
        error(expr, "malformed array index expression")
      }
      (construct, _) => {
        error(expr, format!("invalid '{}' expression", construct))
      }
    }
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    match &expr.content {
      ExprContent::List(_, _) => {
        return self.construct_to_ast(expr);
      }
      ExprContent::Symbol(s) => {
        // this is just a normal symbol
        let s = self.cached(s.as_str());
        if s.as_ref() == "break" {
          return Ok(node(expr, Type::Void, Content::Break));
        }
        let name = self.get_scoped_variable_name(&s);
        let var_type =
          self.variables.get(name.as_ref())
          .or_else(|| self.t.find_global(name.as_ref()).map(|def| &def.type_tag));
        if let Some(t) = var_type {
          return Ok(node(expr, t.clone(), Content::VariableReference(name)));
        }
        let mut function_iter = self.t.find_functions(&s);
        if let Some(def) = function_iter.next() {
          if function_iter.next().is_some() {
            return error(expr, "can't disambiguate multiple functions with the same name");
          }
          let c = Content::FunctionReference(def.function_reference());
          return Ok(node(expr, Type::Fun(def.signature.clone()), c));
        }
        let i = self.t.modules.iter().flat_map(|m| m.globals.keys()).cloned().collect::<Vec<_>>();
        println!("{:?}", i);
        error(expr, format!("unknown symbol '{}'", s))
      }
      ExprContent::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        let s = self.t.find_type_def("string").unwrap();
        Ok(node(expr, Type::Def(s.name.clone()), Content::Literal(v)))
      }
      ExprContent::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(node(expr, Type::F64, Content::Literal(v)))
      }
      ExprContent::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(node(expr, Type::I64, Content::Literal(v)))
      }
      ExprContent::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(node(expr, Type::Bool, Content::Literal(v)))
      },
      ExprContent::LiteralUnit => {
        Ok(node(expr, Type::Void, Content::Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }
}

fn match_intrinsic(name : &str, args : &[TypedNode]) -> Option<Type> {
  match args {
    [a, b] => match (&a.type_tag, &b.type_tag) {
      (Type::F64, Type::F64) => match name {
        "+" | "-" | "*" | "/" => Some(Type::F64),
        ">" | ">="| "<" | "<=" | "==" => Some(Type::Bool),
        _ => None,
      }
      (Type::I64, Type::I64) => match name {
        "+" | "-" | "*" | "/" => Some(Type::I64),
        ">" | ">="| "<" | "<=" | "==" => Some(Type::Bool),
        _ => None,
      }
      _ => None
    }
    [a] => match (&a.type_tag, name) {
      (Type::F64, "-") => Some(Type::F64),
      (Type::I64, "-") => Some(Type::I64),
      (Type::Bool, "!") => Some(Type::Bool),
      (Type::Ptr(t), "deref") => Some(*t.clone()),
      (t, "ref") => Some(Type::Ptr(Box::new(t.clone()))),
      _ => None,
    }
    _ => None,
  }
}

fn find_type_definitions<'e>(expr : &'e Expr, types : &mut Vec<&'e Expr>) {
  let children = expr.children();
  if children.len() == 0 { return }
  if let ExprContent::List(s, _) = &expr.content {
    match s.as_str() {
      "union" => {
        types.push(expr);
        return;
      }
      "struct" => {
        types.push(expr);
        return;
      }
      "quote" => {
        return
      }
      _ => (),
    }
  }
  for c in children {
    find_type_definitions(c, types);
  }
}


pub fn to_typed_module(uid_generator : &mut UIDGenerator, local_symbol_table : &HashMap<RefStr, usize>, modules : &[&TypedModule], cache : &StringCache, expr : &Expr) -> Result<TypedModule, Error> {
  let mut module = TypedModule::new(uid_generator.next());
  let mut type_checker =
    TypeChecker::new(uid_generator, &mut module, modules, local_symbol_table, cache);
  
  let mut types = vec!();
  find_type_definitions(expr, &mut types);

  // Process the types
  for e in types {
    type_checker.add_type_definition(e)?;
  }

  // Process the rest of the module (adds functions and globals)
  let mut function_checker =
    FunctionChecker::new(&mut type_checker, true, HashMap::new());
  let body = function_checker.to_ast(expr)?;

  // Check any unresolved symbols
  let unresolved_types : Vec<_> = type_checker.type_definition_references.drain(0..).collect();
  for t in unresolved_types {
    if type_checker.find_type_def(&t.symbol_name).is_none() {
      return error(t.reference_location, format!("type definition '{}' not found", t.symbol_name));
    }
  }

  let name = cache.get(TOP_LEVEL_FUNCTION_NAME);
  if type_checker.module.functions.iter().find(|def| def.name_in_code == name).is_some() {
    return error(expr, "top level function already defined!");
  }
  let signature = Rc::new(FunctionSignature {
    return_type: body.type_tag.clone(),
    args: vec!(),
  });
  let def = FunctionDefinition {
    name_in_code: name.clone(),
    name_for_codegen: name,
    args: vec!(),
    signature,
    implementation: FunctionImplementation::Normal(body),
    module_id: type_checker.module.id,
  };
  type_checker.add_function(def);
  Ok(module)
}
