
use std::rc::Rc;
use std::fmt::Write;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::value::{SymbolTable, RefStr, Expr, ExprTag};
use crate::parser;

use std::collections::HashMap;
use itertools::Itertools;

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
  Void,
  Float,
  I64,
  Bool,
  Struct(Rc<StructDefinition>),
  Ptr(Box<Type>),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Val {
  Void,
  Float(f64),
  I64(i64),
  Bool(bool),
}

impl Type {
  fn from_string(s : &str) -> Option<Type> {
    match s {
      "float" => Some(Type::Float),
      "bool" => Some(Type::Bool),
      "ptr" => Some(Type::Ptr(Box::new(Type::Void))),
      "i64" => Some(Type::I64),
      "()" => Some(Type::Void),
      other => {
        if other == parser::NO_TYPE {
          Some(Type::Float)
        }
        else {
          None
        }
      }
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

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableReference(RefStr),
  VariableInitialise(RefStr, Box<AstNode>),
  Assignment(Box<(AstNode, AstNode)>),
  IfThen(Box<(AstNode, AstNode)>),
  IfThenElse(Box<(AstNode, AstNode, AstNode)>),
  Block(Vec<AstNode>),
  FunctionDefinition(Rc<FunctionDefinition>, Box<AstNode>),
  CFunctionPrototype(Rc<FunctionDefinition>),
  StructDefinition(Rc<StructDefinition>),
  StructInstantiate(Rc<StructDefinition>, Vec<AstNode>),
  FieldAccess(Box<(AstNode, RefStr)>, usize),
  FunctionCall(RefStr, Vec<AstNode>),
  IntrinsicCall(RefStr, Vec<AstNode>),
  While(Box<(AstNode, AstNode)>),
  ExplicitReturn(Option<Box<AstNode>>),
  Deref(Box<AstNode>),
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
  variables: HashMap<RefStr, Type>,
  functions: &'l mut HashMap<RefStr, Rc<FunctionDefinition>>,
  struct_types : &'l mut HashMap<RefStr, Rc<StructDefinition>>,

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  scope_map: Vec<HashMap<RefStr, RefStr>>,

  sym: &'l mut SymbolTable,
}

impl <'l> TypeChecker<'l> {

  pub fn new(
    args : HashMap<RefStr, Type>,
    functions : &'l mut HashMap<RefStr, Rc<FunctionDefinition>>,
    struct_types : &'l mut HashMap<RefStr, Rc<StructDefinition>>,
    sym : &'l mut SymbolTable)
      -> TypeChecker<'l>
  {
    TypeChecker {
      variables : args,
      functions,
      struct_types,
      sym,
      scope_map: vec!(HashMap::new())
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
    while self.variables.contains_key(unique_name.as_str()) {
      unique_name.clear();
      i += 1;
      write!(&mut unique_name, "{}#{}", name, i).unwrap();
    }
    let unique_name : RefStr = unique_name.into();
    self.scope_map.last_mut().unwrap().insert(name, unique_name.clone());
    unique_name.clone()
  }

  fn to_type(&mut self, expr : &Expr) -> Result<Type, Error> {
    let s = expr.symbol_unwrap()?;
    if let Some(t) = Type::from_string(s) {
      return Ok(t);
    }
    if let Some(t) = self.struct_types.get(s) {
      return Ok(Type::Struct(t.clone()));
    }
    error(expr, "no type with this name exists")
  }

  fn match_intrinsic(name : &str, args : &[AstNode]) -> Option<Type> {
    match args {
      [a, b] => match (&a.type_tag, &b.type_tag) {
        (Type::Float, Type::Float) => match name {
          "+" | "-" | "*" | "/" => Some(Type::Float),
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
        (Type::Float, "unary_-") => Some(Type::Float),
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
            let scoped_name = self.create_scoped_variable_name(name.clone());
            let v = Box::new(self.to_ast(&exprs[1])?);
            self.variables.insert(scoped_name.clone(), v.type_tag.clone());
            Ok(ast(expr, Type::Void, Content::VariableInitialise(scoped_name, v)))
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
            let mut type_checker =
              TypeChecker::new(args, self.functions, self.struct_types, self.sym);
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
            for ((field, value), (expected_name, expected_type)) in field_iter {
              let name = field.symbol_unwrap()?;
              if name != expected_name {
                return error(*field, "incorrect field name");
              }
              if &value.type_tag != expected_type {
                return error(value.loc, "type mismatch");
              }
            }
            if fields.len() > def.fields.len() {
              let extra_field = fields[def.fields.len()].0;
              return error(extra_field, "too many fields");
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
          _ => return error(expr, "unsupported expression"),
        }
      }
      ExprTag::Symbol(s) => {
        if s.as_ref() == "break" {
          return Ok(ast(expr, Type::Void, Content::Break));
        }
        let name = self.get_scoped_variable_name(s);
        if let Some(t) = self.variables.get(name.as_ref()) {
          Ok(ast(expr, t.clone(), Content::VariableReference(name)))
        }
        else {
          error(expr, "unknown variable name")
        }
      }
      ExprTag::LiteralFloat(f) => {
        let v = Val::Float(*f as f64);
        Ok(ast(expr, Type::Float, Content::Literal(v)))
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
