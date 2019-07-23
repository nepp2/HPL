
use std::rc::Rc;
use std::fmt::Write;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::value::{StringCache, RefStr, Expr, ExprTag};

use std::collections::HashMap;
use itertools::Itertools;

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
  Struct(Rc<TypeDefinition>),
  Union(Rc<TypeDefinition>),
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

#[derive(Clone, Debug, PartialEq)]
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
pub struct FunctionDefinition {
  pub name : RefStr,
  pub args : Vec<RefStr>,
  pub signature : Rc<FunctionSignature>,
  pub c_function_address : Option<usize>,
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

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global }

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableReference(RefStr),
  VariableInitialise(RefStr, Box<AstNode>, VarScope),
  Assignment(Box<(AstNode, AstNode)>),
  IfThen(Box<(AstNode, AstNode)>),
  IfThenElse(Box<(AstNode, AstNode, AstNode)>),
  Block(Vec<AstNode>),
  FunctionReference(RefStr),
  FunctionDefinition(Rc<FunctionDefinition>, Box<AstNode>),
  CFunctionPrototype(Rc<FunctionDefinition>),
  TypeDefinition(Rc<TypeDefinition>),
  StructInstantiate(Rc<TypeDefinition>, Vec<AstNode>),
  UnionInstantiate(Rc<TypeDefinition>, Box<(RefStr, AstNode)>),
  FieldAccess(Box<(AstNode, RefStr)>, usize),
  Index(Box<(AstNode, AstNode)>),
  ArrayLiteral(Vec<AstNode>),
  FunctionCall(Box<AstNode>, Vec<AstNode>),
  IntrinsicCall(RefStr, Vec<AstNode>),
  While(Box<(AstNode, AstNode)>),
  ExplicitReturn(Option<Box<AstNode>>),
  Convert(Box<AstNode>),
  Deref(Box<AstNode>),
  SizeOf(Box<Type>),
  Break,
}

#[derive(Debug)]
pub struct AstNode {
  pub type_tag : Type,
  pub content : Content,
  pub loc : TextLocation,
}

impl AstNode {
  fn assert_type(&self, expected : Type) -> Result<(), Error> {
    if self.type_tag == expected {
      Ok(())
    }
    else {
      error(self.loc, format!("expected type {:?}, found type {:?}", expected, self.type_tag))
    }
  }
}

fn ast(expr : &Expr, type_tag : Type, content : Content) -> AstNode {
  AstNode {
    type_tag,
    content,
    loc: expr.loc,
  }
}

pub struct TypeChecker<'l> {
  is_top_level : bool,
  variables: HashMap<RefStr, Type>,
  functions: &'l mut HashMap<RefStr, Rc<FunctionDefinition>>,
  types : &'l mut HashMap<RefStr, Rc<TypeDefinition>>,
  global_variables : &'l mut HashMap<RefStr, Type>,
  local_symbol_table : &'l HashMap<RefStr, usize>,

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  scope_map: Vec<HashMap<RefStr, RefStr>>,

  cache: &'l mut StringCache,
}

impl <'l> TypeChecker<'l> {

  pub fn new(
    is_top_level : bool,
    variables : HashMap<RefStr, Type>,
    functions : &'l mut HashMap<RefStr, Rc<FunctionDefinition>>,
    types : &'l mut HashMap<RefStr, Rc<TypeDefinition>>,
    global_variables : &'l mut HashMap<RefStr, Type>,
    local_symbol_table : &'l HashMap<RefStr, usize>,
    cache : &'l mut StringCache)
      -> TypeChecker<'l>
  {
    let global_map = global_variables.keys().map(|n| (n.clone(), n.clone())).collect();
    TypeChecker {
      is_top_level,
      variables,
      functions,
      types,
      global_variables,
      local_symbol_table,
      cache,
      scope_map: vec!(global_map),
    }
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
    while self.global_variables.contains_key(unique_name.as_str()) ||
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

  fn to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    let name = expr.tree_symbol_unwrap()?.as_ref();
    let params = expr.children.as_slice();
    if let Some(t) = Type::from_string(name) {
      if params.len() > 0 {
        return error(expr, "unexpected type parameters");
      }
      return Ok(t);
    }
    if name == "fun" {
      let args =
        params[0].children.iter().map(|e| self.to_type(e))
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
        if let Some(t) = self.types.get(name) {
          if params.len() > 0 {
            return error(expr, "unexpected type parameters");
          }
          match t.kind {
            TypeKind::Struct => return Ok(Type::Struct(t.clone())),
            TypeKind::Union => return Ok(Type::Union(t.clone())),
          }
        }
        return error(expr, format!("type '{}' does not exist", name));
      }
    }
  }

  fn match_intrinsic(name : &str, args : &[AstNode]) -> Option<Type> {
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

  fn to_type_definition(&mut self, expr : &Expr, exprs : &[Expr], kind : TypeKind) -> Result<AstNode, Error> {
    if exprs.len() < 1 {
      return error(expr, "malformed type definition");
    }
    let name_expr = &exprs[0];
    let name = name_expr.symbol_unwrap()?;
    if self.types.contains_key(name) {
      return error(expr, "struct with this name already defined");
    }
    // TODO: check for duplicates?
    let field_exprs = &exprs[1..];
    let mut fields = vec![];
    // TODO: record the field types, and check them!
    for (field_name_expr, type_expr) in field_exprs.iter().tuples() {
      let field_name = field_name_expr.symbol_unwrap()?.clone();
      let type_tag = self.to_type(type_expr)?;
      fields.push((field_name, type_tag));
    }
    let def = Rc::new(TypeDefinition { name: name.clone(), fields, kind });
    self.types.insert(name.clone(), def.clone());
    Ok(ast(expr, Type::Void, Content::TypeDefinition(def)))
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<AstNode, Error> {
    match &expr.tag {
      ExprTag::Tree(_) => {
        let instr = expr.tree_symbol_unwrap()?;
        let children = expr.children.as_slice();
        match (instr.as_ref(), children) {
          ("call", exprs) => {
            let args =
                  exprs[1..].iter().map(|e| self.to_ast(e))
                  .collect::<Result<Vec<AstNode>, Error>>()?;
            if let Some(function_name) = exprs[0].symbol_unwrap().ok() {
              let op_tag = TypeChecker::match_intrinsic(
                function_name.as_ref(), args.as_slice());
              if let Some(op_tag) = op_tag {
                return Ok(ast(expr, op_tag, Content::IntrinsicCall(function_name.clone(), args)))
              }
            }
            let function_value = self.to_ast(&exprs[0])?;
            if let Type::Fun(sig) = &function_value.type_tag {
              if sig.args.len() != args.len() {
                return error(expr, "incorrect number of arguments passed");
              }
              let return_type = sig.return_type.clone();
              let content = Content::FunctionCall(Box::new(function_value), args);
              return Ok(ast(expr, return_type, content));
            }
            error(&exprs[0], "value is not a function")
          }
          ("sizeof", [t]) => {
            let type_tag = self.to_type(t)?;
            return Ok(ast(expr, Type::U64, Content::SizeOf(Box::new(type_tag))));
          }
          ("as", [a, b]) => {
            let a = self.to_ast(a)?;
            let t = self.to_type(b)?;
            Ok(ast(expr, t, Content::Convert(Box::new(a))))
          }
          ("&&", [a, b]) => {
            let a = self.to_ast(a)?;
            let b = self.to_ast(b)?;
            Ok(ast(expr, Type::Bool, Content::IntrinsicCall(instr.clone(), vec!(a, b))))
          }
          ("||", [a, b]) => {
            let a = self.to_ast(a)?;
            let b = self.to_ast(b)?;
            Ok(ast(expr, Type::Bool, Content::IntrinsicCall(instr.clone(), vec!(a, b))))
          }
          ("let", exprs) => {
            let name = exprs[0].symbol_unwrap()?;
            let v = Box::new(self.to_ast(&exprs[1])?);
            // The first scope is used for function arguments. The second
            // is the top level of the function.
            let c = if self.is_top_level && self.scope_map.len() == 2 {
              // global variable
              self.global_variables.insert(name.clone(), v.type_tag.clone());
              Content::VariableInitialise(name.clone(), v, VarScope::Global)
            }
            else {
              // local variable
              let scoped_name = self.create_scoped_variable_name(name.clone());
              self.variables.insert(scoped_name.clone(), v.type_tag.clone());
              Content::VariableInitialise(scoped_name, v, VarScope::Local)
            };
            Ok(ast(expr, Type::Void, c))
          }
          ("=", [assign_expr, value_expr]) => {
            let a = self.to_ast(assign_expr)?;
            let b = self.to_ast(value_expr)?;
            Ok(ast(expr, Type::Void, Content::Assignment(Box::new((a, b)))))
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
            Ok(ast(expr, type_tag, Content::ExplicitReturn(return_val)))
          }
          ("while", [condition_node, body_node]) => {
            let condition = self.to_ast(condition_node)?;
            let body = self.to_ast(body_node)?;
            Ok(ast(expr, Type::Void, Content::While(Box::new((condition, body)))))
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
              Ok(ast(expr, t, c))
            }
            else {
              Ok(ast(expr, Type::Void, Content::IfThen(Box::new((condition, then_branch)))))
            }
          }
          ("block", exprs) => {
            self.scope_map.push(HashMap::new());
            let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<AstNode>, Error>>()?;
            self.scope_map.pop();
            let tag = nodes.last().map(|n| n.type_tag.clone()).unwrap_or(Type::Void);
            Ok(ast(expr, tag, Content::Block(nodes)))
          }
          ("cfun", exprs) => {
            let name = exprs[0].symbol_unwrap()?;
            let args_exprs = exprs[1].children.as_slice();
            let return_type_expr = &exprs[2];
            let mut arg_names = vec!();
            let mut arg_types = vec!();
            for (name_expr, type_expr) in args_exprs.iter().tuples() {
              let name = name_expr.symbol_unwrap()?;
              let type_tag = self.to_type(type_expr)?;
              if type_tag == Type::Void {
                return error(expr, "functions args cannot be void");
              }
              arg_names.push(name.clone());
              arg_types.push(type_tag);
            }
            let return_type = self.to_type(return_type_expr)?;
            if self.functions.contains_key(name.as_ref()) {
              return error(expr, "function with that name already defined");
            }
            let signature = Rc::new(FunctionSignature {
              return_type,
              args: arg_types,
            });
            let address = self.local_symbol_table.get(name).map(|v| *v);
            if address.is_none() {
              // TODO: check the signature of the function too
              println!("Warning: C function '{}' not linked. LLVM linker may link it instead.", name);
              // return error(expr, "tried to bind non-existing C function")
            }
            let def = Rc::new(FunctionDefinition {
              name: name.clone(),
              args: arg_names,
              signature,
              c_function_address: address,
            });
            self.functions.insert(name.clone(), def.clone());
            
            Ok(ast(expr, Type::Void, Content::CFunctionPrototype(def)))
          }
          ("fun", exprs) => {
            let name = exprs[0].symbol_unwrap()?;
            let args_exprs = exprs[1].children.as_slice();
            let function_body = &exprs[2];
            let mut arg_names = vec!();
            let mut arg_types = vec!();
            for (name_expr, type_expr) in args_exprs.iter().tuples() {
              let name = name_expr.symbol_unwrap()?;
              let type_tag = self.to_type(type_expr)?;
              if type_tag == Type::Void {
                return error(expr, "functions args cannot be void");
              }
              arg_names.push(name.clone());
              arg_types.push(type_tag);
            }
            let args = arg_names.iter().cloned().zip(arg_types.iter().cloned()).collect();
            let mut empty_global_map = HashMap::new(); // hide globals from child functions
            let mut type_checker =
              TypeChecker::new(false, args, self.functions, self.types, &mut empty_global_map, self.local_symbol_table, self.cache);
            let body = type_checker.to_ast(function_body)?;
            if self.functions.contains_key(name.as_ref()) {
              return error(expr, "function with that name already defined");
            }
            let signature = Rc::new(FunctionSignature {
              return_type: body.type_tag.clone(),
              args: arg_types,
            });
            let def = Rc::new(FunctionDefinition {
              name: name.clone(),
              args: arg_names,
              signature,
              c_function_address: None,
            });
            self.functions.insert(name.clone(), def.clone());
            Ok(ast(expr, Type::Void, Content::FunctionDefinition(def, Box::new(body))))
          }
          ("union", exprs) => {
            self.to_type_definition(expr, exprs, TypeKind::Union)
          }
          ("struct", exprs) => {
            self.to_type_definition(expr, exprs, TypeKind::Struct)
          }
          ("type_instantiate", exprs) => {
            if exprs.len() < 1 || exprs.len() % 2 == 0 {
              return error(expr, format!("malformed type instantiation {:?}", expr));
            }
            let name_expr = &exprs[0];
            let field_exprs = &exprs[1..];
            let name = name_expr.symbol_unwrap()?;
            let fields =
              field_exprs.iter().tuples().map(|(name, value)| {
                let value = self.to_ast(value)?;
                Ok((name, value))
              })
              .collect::<Result<Vec<(&Expr, AstNode)>, Error>>()?;
            let def =
              self.types.get(name)
              .ok_or_else(|| error_raw(name_expr, "no type with this name exists"))?;
            match &def.kind {
              TypeKind::Struct => {
                if fields.len() != def.fields.len() {
                  return error(expr, "wrong number of fields");
                }
                let field_iter = fields.iter().zip(def.fields.iter());
                for ((field, value), (expected_name, expected_type)) in field_iter {
                  let name = field.symbol_unwrap()?;
                  if name.as_ref() != "" && name != expected_name {
                    return error(*field, "incorrect field name");
                  }
                  if &value.type_tag != expected_type {
                    return error(value.loc, format!("type mismatch. expected {:?}, found {:?}", expected_type, value.type_tag));
                  }
                }
                let c = Content::StructInstantiate(def.clone(), fields.into_iter().map(|v| v.1).collect());
                Ok(ast(expr, Type::Struct(def.clone()), c))
              }
              TypeKind::Union => {
                if fields.len() != 1 {
                  return error(expr, "must instantiate exactly one field");
                }
                let (field, value) = fields.into_iter().nth(0).unwrap();
                let name = field.symbol_unwrap()?;
                if def.fields.iter().find(|(n, _)| n == name).is_none() {
                  return error(field, "field does not exist in this union");
                }
                let c = Content::UnionInstantiate(def.clone(), Box::new((name.clone(), value)));
                Ok(ast(expr, Type::Union(def.clone()), c))
              }
            }
          }
          (".", [container_expr, field_expr]) => {
            let container_val = self.to_ast(container_expr)?;
            let field_name = field_expr.symbol_unwrap()?;
            let def = match &container_val.type_tag {
              Type::Struct(def) => def,
              Type::Union(def) => def,
              _ => return error(container_expr, format!("expected struct or union, found {:?}", container_val.type_tag)),
            };
            let (field_index, (_, field_type)) =
              def.fields.iter().enumerate().find(|(_, (n, _))| n==field_name)
              .ok_or_else(|| error_raw(field_expr, "type does not have field with this name"))?;
            let field_type = field_type.clone();
            let c = Content::FieldAccess(Box::new((container_val, field_name.clone())), field_index);
            Ok(ast(expr, field_type, c))
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
            Ok(ast(expr, Type::Ptr(Box::new(t)), Content::ArrayLiteral(elements)))
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
            Ok(ast(expr, inner_type, Content::Index(Box::new((array, index)))))
          }
          _ => return error(expr, "unsupported expression"),
        }
      }
      ExprTag::Symbol(s) => {
        if s.as_ref() == "break" {
          return Ok(ast(expr, Type::Void, Content::Break));
        }
        let name = self.get_scoped_variable_name(s);
        let var_type =
          self.variables.get(name.as_ref())
          .or_else(|| self.global_variables.get(name.as_ref()));
        if let Some(t) = var_type {
          return Ok(ast(expr, t.clone(), Content::VariableReference(name)));
        }
        if let Some(def) = self.functions.get(s.as_ref()) {
          return Ok(ast(expr, Type::Fun(def.signature.clone()), Content::FunctionReference(s.clone())))
        }
        error(expr, "unknown variable name")
      }
      ExprTag::LiteralString(s) => {
        let v = Val::String(s.to_string());
        let s = self.types.get("string").unwrap();
        Ok(ast(expr, Type::Struct(s.clone()), Content::Literal(v)))
      }
      ExprTag::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(ast(expr, Type::F64, Content::Literal(v)))
      }
      ExprTag::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(ast(expr, Type::I64, Content::Literal(v)))
      }
      ExprTag::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(ast(expr, Type::Bool, Content::Literal(v)))
      },
      ExprTag::LiteralUnit => {
        Ok(ast(expr, Type::Void, Content::Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }
}
