
use std::rc::Rc;
use std::fmt::Write;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::value::{SymbolTable, RefStr, Expr, ExprTag};

use std::collections::HashMap;
use itertools::Itertools;

#[no_mangle]
#[derive(PartialEq, Debug, Copy, Clone)]
#[repr(C)]
pub struct ScriptString {
  pub ptr : *mut u8,
  pub length : u64,
}

impl ScriptString {
  /*
  pub fn new(mut s : String) -> ScriptString {
    let v = unsafe { s.as_mut_vec() };
    v.shrink_to_fit();
    let ss = ScriptString { ptr: v.as_mut_ptr(), length: v.capacity() as u64 };
    std::mem::forget(s);
    ss
  }
  */

  pub fn as_str(&self) -> &str {
    let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.length as usize) };
    std::str::from_utf8(slice).expect("wasn't a valid utf8 string!")
  }
}
/*
impl Drop for ScriptString {
  fn drop(&mut self) {
    unsafe {
      Vec::from_raw_parts(self.ptr, self.length as usize, self.length as usize);
    }
  }
}
*/

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
  Struct(Rc<StructDefinition>),
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

  /// returns the minimum number of bits required to store the type inline
  pub fn width(&self) -> u64 {
    match self {
      Type::F64 | Type::U64 | Type::I64 => 64,
      Type::F32 | Type::U32 | Type::I32 => 32,
      Type::U16 => 16,
      Type::U8 => 8,
      Type::Bool => 1,
      Type::Void => 0,
      Type::Struct(def) =>
        def.fields.iter().map(|(_, t)| t.width()).sum(),
      Type::Ptr(_) => 64, // TODO: could be wrong
    }
  }
}

#[derive(Clone, Debug)]
pub struct StructDefinition {
  pub name : RefStr,
  pub fields : Vec<(RefStr, Type)>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
  pub name : RefStr,
  pub args : Vec<RefStr>,
  pub signature : Rc<FunctionSignature>
}

#[derive(Debug)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Vec<Type>,
}

impl PartialEq for StructDefinition {
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
  FunctionDefinition(Rc<FunctionDefinition>, Box<AstNode>),
  CFunctionPrototype(Rc<FunctionDefinition>),
  StructDefinition(Rc<StructDefinition>),
  StructInstantiate(Rc<StructDefinition>, Vec<AstNode>),
  FieldAccess(Box<(AstNode, RefStr)>, usize),
  Index(Box<(AstNode, AstNode)>),
  ArrayLiteral(Vec<AstNode>),
  FunctionCall(RefStr, Vec<AstNode>),
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
  struct_types : &'l mut HashMap<RefStr, Rc<StructDefinition>>,
  global_variables : &'l mut HashMap<RefStr, Type>,

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  scope_map: Vec<HashMap<RefStr, RefStr>>,

  sym: &'l mut SymbolTable,
}

impl <'l> TypeChecker<'l> {

  pub fn new(
    is_top_level : bool,
    variables : HashMap<RefStr, Type>,
    functions : &'l mut HashMap<RefStr, Rc<FunctionDefinition>>,
    struct_types : &'l mut HashMap<RefStr, Rc<StructDefinition>>,
    global_variables : &'l mut HashMap<RefStr, Type>,
    sym : &'l mut SymbolTable)
      -> TypeChecker<'l>
  {
    let global_map = global_variables.keys().map(|n| (n.clone(), n.clone())).collect();
    TypeChecker {
      is_top_level,
      variables,
      functions,
      struct_types,
      global_variables,
      sym,
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
    match (name, params) {
      ("ptr", [t]) => {
        let t = self.to_type(t)?;
        Ok(Type::Ptr(Box::new(t)))
      }
      (name, params) => {
        if let Some(t) = self.struct_types.get(name) {
          if params.len() > 0 {
            return error(expr, "unexpected struct type parameters");
          }
          return Ok(Type::Struct(t.clone()))
        }
        return error(expr, "type does not exist");
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
        _ => None,
      }
      _ => None,
    }
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<AstNode, Error> {
    match &expr.tag {
      ExprTag::Tree(_) => {
        let instr = expr.tree_symbol_unwrap()?;
        let children = expr.children.as_slice();
        match (instr.as_ref(), children) {
          ("call", exprs) => {
            let function_name = exprs[0].symbol_unwrap()?;
            let args =
                  exprs[1..].iter().map(|e| self.to_ast(e))
                  .collect::<Result<Vec<AstNode>, Error>>()?;
            let op_tag = TypeChecker::match_intrinsic(function_name.as_ref(), args.as_slice());
            if let Some(op_tag) = op_tag {
              return Ok(ast(expr, op_tag, Content::IntrinsicCall(function_name.clone(), args)))
            }
            if let Some(def) = self.functions.get(function_name.as_ref()) {
              let return_type = def.signature.return_type.clone();
              return Ok(ast(expr, return_type, Content::FunctionCall(function_name.clone(), args)));
            }
            error(expr, "unknown function")
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
            let def = Rc::new(FunctionDefinition {
              name: name.clone(),
              args: arg_names,
              signature,
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
              TypeChecker::new(false, args, self.functions, self.struct_types, &mut empty_global_map, self.sym);
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
            });
            self.functions.insert(name.clone(), def.clone());
            Ok(ast(expr, Type::Void, Content::FunctionDefinition(def, Box::new(body))))
          }
          ("struct_define", exprs) => {
            if exprs.len() < 1 {
              return error(expr, "malformed struct definition");
            }
            let name_expr = &exprs[0];
            let name = name_expr.symbol_unwrap()?;
            if self.struct_types.contains_key(name) {
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
            let def = Rc::new(StructDefinition { name: name.clone(), fields });
            self.struct_types.insert(name.clone(), def.clone());
            Ok(ast(expr, Type::Void, Content::StructDefinition(def)))
          }
          ("struct_instantiate", exprs) => {
            if exprs.len() < 1 || exprs.len() % 2 == 0 {
              return error(expr, format!("malformed struct instantiation {:?}", expr));
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
              self.struct_types.get(name)
              .ok_or_else(|| error_raw(name_expr, "no struct with this name exists"))?;
            let field_iter = fields.iter().zip(def.fields.iter());
            if fields.len() != def.fields.len() {
              return error(expr, "wrong number of fields");
            }
            for ((field, value), (expected_name, expected_type)) in field_iter {
              let name = field.symbol_unwrap()?;
              if name.as_ref() != "" && name != expected_name {
                return error(*field, "incorrect field name");
              }
              if &value.type_tag != expected_type {
                return error(value.loc, "type mismatch");
              }
            }
            let c = Content::StructInstantiate(def.clone(), fields.into_iter().map(|v| v.1).collect());
            Ok(ast(expr, Type::Struct(def.clone()), c))
          }
          (".", [struct_expr, field_expr]) => {
            let struct_val = self.to_ast(struct_expr)?;
            let field_name = field_expr.symbol_unwrap()?;
            let def = match &struct_val.type_tag {
              Type::Struct(def) => def,
              _ => return error(struct_expr, format!("expected struct, found {:?}", struct_val.type_tag)),
            };
            let (field_index, (_, field_type)) =
              def.fields.iter().enumerate().find(|(_, (n, _))| n==field_name)
              .ok_or_else(|| error_raw(field_expr, "struct does not have field with this name"))?;
            let field_type = field_type.clone();
            let c = Content::FieldAccess(Box::new((struct_val, field_name.clone())), field_index);
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
          Ok(ast(expr, t.clone(), Content::VariableReference(name)))
        }
        else {
          error(expr, "unknown variable name")
        }
      }
      ExprTag::LiteralString(s) => {
        let v = Val::String(s.to_string());
        Ok(ast(expr, Type::Ptr(Box::new(Type::U8)), Content::Literal(v)))
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
      _ => error(expr, "unsupported expression"),
    }
  }
}
