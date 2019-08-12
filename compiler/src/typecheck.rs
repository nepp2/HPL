
use std::rc::Rc;
use std::fmt::Write;

use crate::error;
use crate::error::{Error, error, error_raw, TextLocation, ErrorContent};
use crate::expr::{StringCache, RefStr, Expr, ExprTag};

use std::collections::HashMap;
use itertools::Itertools;

use im_rc::HashMap as ImMap;


#[derive(Clone, PartialEq, Debug)]
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
  Fun(Rc<FunctionSignature>),
  Def(RefStr),
  Ptr(Box<Type>),
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
      "()" => Some(Type::Void),
      "" => Some(Type::I64),
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
  pub name : RefStr,
  pub args : Vec<RefStr>,
  pub signature : Rc<FunctionSignature>,
  pub implementation : FunctionImplementation,
}

#[derive(Debug, PartialEq)]
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
  FunctionReference(RefStr),
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
  Deref(Box<TypedNode>),
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

#[derive(Clone)]
pub struct TypedModule {
  pub types : ImMap<RefStr, Rc<TypeDefinition>>,
  pub functions : ImMap<RefStr, Rc<FunctionDefinition>>,
  pub globals : ImMap<RefStr, Rc<GlobalDefinition>>,
}

impl TypedModule {
  pub fn new() -> TypedModule {
    TypedModule{ types: ImMap::new(), functions: ImMap::new(), globals: ImMap::new() }
  }
}

/*
  Namespacing examples:
    - module + function name
    - module + type
    - module + function + type?
    - varname + function + scope


*/

enum TypeError {
  Error(Error),
  SymbolResolveFailure(RefStr, TextLocation),
}

fn type_error<T, L : Into<TextLocation>, S : Into<ErrorContent>>(loc : L, message : S) -> Result<T, TypeError> {
  Err(error::error_raw(loc, message).into())
}

impl From<Error> for TypeError {
  fn from(e : Error) -> TypeError {
    TypeError::Error(e)
  }
}

struct SymbolResolveFailure {
  symbol_needed : RefStr,
  failure_location : TextLocation,
}

pub struct TypeChecker<'l> {
  module : &'l mut TypedModule,
  modules : &'l [TypedModule],
  local_symbol_table : &'l HashMap<RefStr, usize>,

  unresolved_type_definitions : Vec<SymbolResolveFailure>,

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
    module : &'l mut TypedModule,
    modules : &'l [TypedModule],
    local_symbol_table : &'l HashMap<RefStr, usize>,
    cache : &'l StringCache)
      -> TypeChecker<'l>
  {
    TypeChecker {
      module,
      modules,
      local_symbol_table,
      unresolved_type_definitions: vec!(),
      cache,
    }
  }

  fn find_f<T>(&self, name : &str, f : fn(&TypedModule) -> &ImMap<RefStr, T>) -> Option<&T> {
    f(self.module).get(name).or_else(|| self.modules.iter().flat_map(|m| f(m).get(name)).nth(0))
  }

  fn find_global(&self, name : &str) -> Option<&Rc<GlobalDefinition>> {
    self.find_f(name, |m| &m.globals)
  }

  fn find_function(&self, name : &str) -> Option<&Rc<FunctionDefinition>> {
    self.find_f(name, |m| &m.functions)
  }

  fn find_type_def(&self, name : &str) -> Option<&Rc<TypeDefinition>> {
    self.find_f(name, |m| &m.types)
  }

  fn add_global(&mut self, name : RefStr, def : GlobalDefinition) {
    self.module.globals.insert(name, Rc::new(def));
  }

  fn add_function(&mut self, name : RefStr, def : FunctionDefinition) {
    self.module.functions.insert(name, Rc::new(def));
  }

  /// Converts expression into type. Logs symbol error if definition references a type that hasn't been defined yet
  /// These symbol errors may be resolved later, when the rest of the module has been checked.
  fn to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    let name = expr.symbol_unwrap()?;
    let params = expr.children.as_slice();
    if let Some(t) = Type::from_string(name) {
      if params.len() > 0 {
        return error(expr, "unexpected type parameters").map_err(|e| e.into());
      }
      return Ok(t);
    }
    if name == "fun" {
      let args =
        params[0].children.as_slice()
        .iter().tuples()
        .map(|(_, e)| self.to_type(e))
        .collect::<Result<Vec<Type>, Error>>()?;
      let return_type = self.to_type(&params[1])?;
      return Ok(Type::Fun(Rc::new(FunctionSignature{ args, return_type})));
    }
    match (name, params) {
      ("ptr", [t]) => {
        let t = self.to_type(t)?;
        Ok(Type::Ptr(Box::new(t)))
      }
      (name, params) => {
        if params.len() > 0 {
          return error(expr, "unexpected type parameters").map_err(|e| e.into());
        }
        let name = self.cache.get(name);
        if self.find_type_def(&name).is_none() {
          self.unresolved_type_definitions.push(SymbolResolveFailure{ symbol_needed: name.clone(), failure_location: expr.loc });
        }
        return Ok(Type::Def(name));
      }
    }
  }

  fn add_type_definition(&mut self, expr : &Expr) -> Result<(), Error> {
    let kind = match expr.symbol_unwrap()? {
      "union" => TypeKind::Union,
      "struct" => TypeKind::Struct,
      _ => panic!(),
    };
    let children = expr.children.as_slice();
    if children.len() < 1 {
      return error(expr, "malformed type definition");
    }
    let name_expr = &children[0];
    let name = name_expr.symbol_unwrap()?;
    if self.find_type_def(name).is_some() {
      return error(expr, "struct with this name already defined");
    }
    // TODO: check for duplicates?
    let field_exprs = &children[1..];
    let mut fields = vec![];
    // TODO: record the field types, and check them!
    for (field_name_expr, type_expr) in field_exprs.iter().tuples() {
      let field_name = self.cache.get(field_name_expr.symbol_unwrap()?);
      let type_tag = self.to_type(type_expr)?;
      fields.push((field_name, type_tag));
    }
    let name = self.cache.get(name);
    let def = TypeDefinition { name: name.clone(), fields, kind };
    self.module.types.insert(name, Rc::new(def));
    Ok(())
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

  fn tree_to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let instr = expr.symbol_unwrap()?;
    let children = expr.children.as_slice();
    match (instr, children) {
      ("call", exprs) => {
        let args =
              exprs[1..].iter().map(|e| self.to_ast(e))
              .collect::<Result<Vec<TypedNode>, Error>>()?;
        if let Some(function_name) = exprs[0].symbol_unwrap().ok() {
          let op_tag = match_intrinsic(function_name, args.as_slice());
          if let Some(op_tag) = op_tag {
            return Ok(node(expr, op_tag, Content::IntrinsicCall(self.cached(function_name), args)))
          }
        }
        let function_value = self.to_ast(&exprs[0])?;
        if let Type::Fun(sig) = &function_value.type_tag {
          if sig.args.len() != args.len() {
            return error(expr, "incorrect number of arguments passed");
          }
          let return_type = sig.return_type.clone();
          let content = Content::FunctionCall(Box::new(function_value), args);
          return Ok(node(expr, return_type, content));
        }
        error(&exprs[0], "value is not a function")
      }
      ("sizeof", [t]) => {
        let type_tag = self.t.to_type(t)?;
        return Ok(node(expr, Type::U64, Content::SizeOf(Box::new(type_tag))));
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
      ("let", exprs) => {
        let name = self.cached(exprs[0].symbol_unwrap()?);
        let v = Box::new(self.to_ast(&exprs[1])?);
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
        Ok(node(expr, Type::Void, c))
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
      ("cbind", [name_expr, type_expr]) => {
        let name = self.cached(name_expr.symbol_unwrap()?);
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
            name: name.clone(),
            args,
            signature: sig.clone(),
            implementation: FunctionImplementation::CFunction(address),
          };
          self.t.add_function(name.clone(), def);
        }
        else {
          let def = GlobalDefinition { name: name.clone(), type_tag, c_address: address };
          self.t.add_global(name.clone(), def);
        }
        Ok(node(expr, Type::Void, Content::CBind(name)))
      }
      ("fun", exprs) => {
        let name = self.cached(exprs[0].symbol_unwrap()?);
        let args_exprs = exprs[1].children.as_slice();
        let function_body = &exprs[2];
        let mut arg_names = vec!();
        let mut arg_types = vec!();
        for (name_expr, type_expr) in args_exprs.iter().tuples() {
          let name = self.cached(name_expr.symbol_unwrap()?);
          let type_tag = self.t.to_type(type_expr)?;
          if type_tag == Type::Void {
            return error(expr, "functions args cannot be void");
          }
          arg_names.push(name);
          arg_types.push(type_tag);
        }
        let args = arg_names.iter().cloned().zip(arg_types.iter().cloned()).collect();
        let mut function_checker = FunctionChecker::new(self.t, false, args);
        let body = function_checker.to_ast(function_body)?;
        if self.t.find_function(name.as_ref()).is_some() {
          return error(expr, "function with that name already defined");
        }
        let signature = Rc::new(FunctionSignature {
          return_type: body.type_tag.clone(),
          args: arg_types,
        });
        let def = FunctionDefinition {
          name: name.clone(),
          args: arg_names,
          signature,
          implementation: FunctionImplementation::Normal(body),
        };
        self.t.add_function(name.clone(), def);
        Ok(node(expr, Type::Void, Content::FunctionDefinition(name)))
      }
      ("union", exprs) => {
        let name = self.cached(&exprs[0].symbol_unwrap()?);
        Ok(node(expr, Type::Void, Content::TypeDefinition(name)))
      }
      ("struct", exprs) => {
        let name = self.cached(&exprs[0].symbol_unwrap()?);
        Ok(node(expr, Type::Void, Content::TypeDefinition(name)))
      }
      ("type_instantiate", exprs) => {
        if exprs.len() < 1 || exprs.len() % 2 == 0 {
          return error(expr, format!("malformed type instantiation"));
        }
        let name_expr = &exprs[0];
        let field_exprs = &exprs[1..];
        let name = name_expr.symbol_unwrap()?;
        let fields =
          field_exprs.iter().tuples().map(|(name, value)| {
            let value = self.to_ast(value)?;
            Ok((name, value))
          })
          .collect::<Result<Vec<(&Expr, TypedNode)>, Error>>()?;
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
              let name = field.symbol_unwrap()?;
              if name != "" && name != expected_name.as_ref() {
                return error(*field, "incorrect field name");
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
            let field_name = self.cached(field.symbol_unwrap()?);
            if def.fields.iter().find(|(n, _)| n == &field_name).is_none() {
              return error(field, "field does not exist in this union");
            }
            let c = Content::UnionInstantiate(self.cached(name), Box::new((field_name, value)));
            Ok(node(expr, Type::Def(def.name.clone()), c))
          }
        }
      }
      (".", [container_expr, field_expr]) => {
        let container_val = self.to_ast(container_expr)?;
        let field_name = self.cached(field_expr.symbol_unwrap()?);
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
      ("literal_array", exprs) => {
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
            Type::Void
          };
        Ok(node(expr, Type::Ptr(Box::new(t)), Content::ArrayLiteral(elements)))
      }
      ("index", [array_expr, index_expr]) => {
        let array = self.to_ast(array_expr)?;
        let inner_type = match &array.type_tag {
          Type::Ptr(t) => *(t).clone(),
          _ => return error(array_expr, "expected ptr"),
        };
        let index = self.to_ast(index_expr)?;
        if index.type_tag != Type::I64 {
          return error(array_expr, "expected integer");
        }
        Ok(node(expr, inner_type, Content::Index(Box::new((array, index)))))
      }
      _ => return error(expr, "unsupported expression"),
    }
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    match &expr.tag {
      ExprTag::Symbol(s) => {
        // Is this a tree?
        let children = expr.children.as_slice();
        if children.len() > 0 {
          return self.tree_to_ast(expr);
        }
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
        if let Some(def) = self.t.find_function(&s) {
          return Ok(node(expr, Type::Fun(def.signature.clone()), Content::FunctionReference(s)));
        }
        error(expr, format!("unknown symbol '{}'", s))
      }
      ExprTag::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        let s = self.t.find_type_def("string").unwrap();
        Ok(node(expr, Type::Def(s.name.clone()), Content::Literal(v)))
      }
      ExprTag::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(node(expr, Type::F64, Content::Literal(v)))
      }
      ExprTag::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(node(expr, Type::I64, Content::Literal(v)))
      }
      ExprTag::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(node(expr, Type::Bool, Content::Literal(v)))
      },
      ExprTag::LiteralUnit => {
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
      (Type::F64, "unary_-") => Some(Type::F64),
      (Type::I64, "unary_-") => Some(Type::I64),
      (Type::Bool, "unary_!") => Some(Type::Bool),
      (t, "unary_ref") => Some(Type::Ptr(Box::new(t.clone()))),
      _ => None,
    }
    _ => None,
  }
}

fn find_symbols<'e>(expr : &'e Expr, types : &mut Vec<&'e Expr>, functions : &mut Vec<&'e Expr>) {
  let children = expr.children.as_slice();
  if children.len() == 0 { return }
  if let ExprTag::Symbol(s) = &expr.tag {
    match s.as_str() {
      "union" => {
      types.push(expr);
      return;
      }
      "struct" => {
      types.push(expr);
      return;
      }
      "fun" => {
      functions.push(expr);
      }
      _ => (),
    }
  }
  for c in children {
    find_symbols(c, types, functions);
  }
}

pub fn to_typed_module(local_symbol_table : &HashMap<RefStr, usize>, modules : &[TypedModule], cache : &StringCache, expr : &Expr) -> Result<TypedModule, Error> {
  let mut module = TypedModule::new();
  let mut type_checker =
    TypeChecker::new(&mut module, modules, local_symbol_table, cache);
  
  let mut types = vec!();
  let mut functions = vec!();
  find_symbols(expr, &mut types, &mut functions);

  // Process the types
  for e in types {
    type_checker.add_type_definition(e)?;
  }

  // Process the rest of the module (adds functions and globals)
  let mut function_checker =
    FunctionChecker::new(&mut type_checker, true, HashMap::new());
  let body = function_checker.to_ast(expr)?;

  // Check any unresolved symbols
  let unresolved_types : Vec<_> = type_checker.unresolved_type_definitions.drain(0..).collect();
  for t in unresolved_types {
    if type_checker.find_type_def(&t.symbol_needed).is_none() {
      return error(t.failure_location, format!("type definition '{}' not found", t.symbol_needed));
    }
  }

  let name = cache.get(TOP_LEVEL_FUNCTION_NAME);
  if module.functions.contains_key(name.as_ref()) {
    return error(expr, "function with that name already defined");
  }
  let signature = Rc::new(FunctionSignature {
    return_type: body.type_tag.clone(),
    args: vec!(),
  });
  let def = FunctionDefinition {
    name: name.clone(),
    args: vec!(),
    signature,
    implementation: FunctionImplementation::Normal(body),
  };
  module.functions.insert(name.clone(), Rc::new(def));
  Ok(module)
}
