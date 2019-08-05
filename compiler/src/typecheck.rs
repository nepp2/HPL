
use std::rc::Rc;
use std::fmt::Write;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprTag};

use std::collections::{HashMap, HashSet};
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
  Def(RefStr),
  Ptr(Box<Type>),
  Unresolved,
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
  pub name : Symbol,
  pub fields : Vec<(Symbol, Type)>,
  pub kind : TypeKind,
}

#[derive(Debug)]
pub enum FunctionImplementation {
  Normal(TypedNode),
  CFunction(usize),
  Intrinsic,
}

#[derive(Debug)]
pub struct FunctionDefinition {
  pub name : Symbol,
  pub args : Vec<Symbol>,
  pub signature : Rc<FunctionSignature>,
  pub implementation : FunctionImplementation,
}

#[derive(Debug, PartialEq)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Vec<Type>,
}

// impl PartialEq for TypeDefinition {
//   fn eq(&self, rhs : &Self) -> bool {
//     self.name == rhs.name
//   }
// }

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global }

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  SymbolReference(RefStr),
  LocalVariableReference(RefStr, i32),
  DefineLocalVariable(RefStr, i32, Box<TypedNode>),
  DefineGlobalVariable(RefStr, Box<TypedNode>),
  Assignment(Box<(TypedNode, TypedNode)>),
  IfThen(Box<(TypedNode, TypedNode)>),
  IfThenElse(Box<(TypedNode, TypedNode, TypedNode)>),
  Block(Vec<TypedNode>),
  Quote(Box<Expr>),
  FunctionDefinition(RefStr),
  CFunctionPrototype(RefStr),
  TypeDefinition(RefStr),
  TypeInstantiate(Symbol, Vec<(Symbol, TypedNode)>),
  FieldAccess(Box<(TypedNode, Symbol)>),
  Index(Box<(TypedNode, TypedNode)>),
  ArrayLiteral(Vec<TypedNode>),
  FunctionCall(Box<TypedNode>, Vec<TypedNode>),
  ShortCircuit(RefStr, Vec<TypedNode>),
  While(Box<(TypedNode, TypedNode)>),
  ExplicitReturn(Option<Box<TypedNode>>),
  Convert(Box<(TypedNode, Type)>),
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

/// Creates a node with an unresolved type
fn node(expr : &Expr, content : Content) -> TypedNode {
  TypedNode {
    type_tag: Type::Unresolved,
    content,
    loc: expr.loc,
  }
}

enum SymbolDefinition {
  GlobalDef(Type),
  FunctionDef(FunctionDefinition),
  TypeDef(TypeDefinition),
}

#[derive(Clone, Debug)]
struct Symbol {
  text : RefStr,
  loc : TextLocation,
}

pub struct TypedModule {
  pub symbols : HashMap<RefStr, SymbolDefinition>,
}

/* TODO

  Namespacing examples:
    - module + function name
    - module + type
    - module + function + type?
    - varname + function + scope

*/

#[derive(Copy, Clone)]
pub struct TypeResolver<'l> {
  modules : &'l [TypedModule],
  cache: &'l StringCache,
}

struct ExprConverter<'l> {
  cache: &'l StringCache,
  new_module : &'l mut TypedModule,
  is_top_level : bool,
  unique_variable_ids : i32,

  /// Tracks which variables are available, when.
  /// Used to rename variables with clashing names.
  variable_scope: Vec<HashMap<RefStr, i32>>,
}

fn symbol(text : RefStr, loc : TextLocation) -> Symbol {
  Symbol { text, loc }
}

impl <'l> ExprConverter<'l> {

  pub fn new(
    cache: &'l StringCache,
    new_module : &'l mut TypedModule,
    is_top_level : bool,
    variables : HashSet<RefStr>)
      -> ExprConverter<'l>
  {
    let first_scope : HashMap<RefStr, i32> =
      variables.into_iter().enumerate().map(|(i, v)| (v, i as i32)).collect();
    ExprConverter {
      cache,
      new_module,
      is_top_level,
      unique_variable_ids: first_scope.len() as i32,
      variable_scope: vec!(first_scope),
    }
  }

  fn add_symbol(&mut self, loc : TextLocation, name : RefStr, sym : SymbolDefinition) -> Result<(), Error> {
    if self.new_module.symbols.contains_key(&name) {
      return error(loc, "symbol with this name already defined");
    }
    self.new_module.symbols.insert(name, sym);
    Ok(())
  }

  fn to_type(&self, expr : &Expr) -> Result<Type, Error> {
    let name = expr.symbol_unwrap()?;
    let params = expr.children.as_slice();
    if let Some(t) = Type::from_string(name) {
      if params.len() > 0 {
        return error(expr, "unexpected type parameters");
      }
      return Ok(t);
    }
    if name == "fun" {
      let args =
        params[0].children.as_slice().iter().map(|e| self.to_type(e))
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
          return error(expr, "unexpected type parameters");
        }
        Ok(Type::Def(self.cache.get(name)))
      }
    }
  }

  fn to_type_definition(&mut self, expr : &Expr) -> Result<TypeDefinition, Error> {
    let kind = match expr.symbol_unwrap()? {
      "struct" => TypeKind::Struct,
      "union" => TypeKind::Union,
    };
    let children = expr.children.as_slice();
    if children.len() < 1 {
      return error(expr, "malformed type definition");
    }
    let name_expr = &children[0];
    let name = name_expr.symbol_unwrap()?;
    // TODO: check for duplicates?
    let field_exprs = &children[1..];
    let mut fields = vec![];
    // TODO: record the field types, and check them!
    for (field_name_expr, type_expr) in field_exprs.iter().tuples() {
      let field_name = field_name_expr.symbol_unwrap()?;
      let field_name = symbol(self.cache.get(field_name), field_name_expr.loc);
      let type_tag = self.to_type(type_expr)?;
      fields.push((field_name, type_tag));
    }
    let name = symbol(self.cache.get(name), name_expr.loc);
    Ok(TypeDefinition { name, fields, kind })
  }

  fn convert_top_level_function(&mut self, expr : &Expr) -> Result<FunctionDefinition, Error> {
    let name = self.cache.get("top_level");
    self.convert_function_body(symbol(name, TextLocation::zero()), vec!(), vec!(), expr, true)
  }

  fn convert_function_body(
    &mut self, name : Symbol,
    arg_names : Vec<Symbol>, arg_types : Vec<Type>,
    function_body : &Expr, is_top_level : bool)
      -> Result<FunctionDefinition, Error>
  {
    let args = arg_names.iter().map(|s| &s.text).cloned().collect();
    let mut converter =
      ExprConverter::new(self.cache, self.new_module, is_top_level, args);
    let body = converter.to_ast(function_body)?;
    let signature = Rc::new(FunctionSignature {
      return_type: body.type_tag.clone(),
      args: arg_types,
    });
    let def = FunctionDefinition {
      name: name,
      args: arg_names,
      signature,
      implementation: FunctionImplementation::Normal(body),
    };
    return Ok(def);
  }

  fn get_local_variable_id(&self, name : &RefStr) -> Option<i32> {
    self.variable_scope.iter().rev().flat_map(|m| m.get(name).map(|x| *x)).nth(0)
  }

  fn create_unique_variable_id(&mut self, name : RefStr) -> i32 {
    let i = self.unique_variable_ids;
    self.unique_variable_ids += 1;
    self.variable_scope.last_mut().unwrap().insert(name, i);
    i
  }

  fn tree_to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let instr = expr.symbol_unwrap()?;
    let children = expr.children.as_slice();
    match (instr, children) {
      ("call", exprs) => {
        let args =
          exprs[1..].iter().map(|e| self.to_ast(e))
          .collect::<Result<Vec<TypedNode>, Error>>()?;
        let function_value = self.to_ast(&exprs[0])?;
        let content = Content::FunctionCall(Box::new(function_value), args);
        return Ok(node(expr, content));
      }
      ("sizeof", [t]) => {
        let type_tag = self.to_type(t)?;
        return Ok(node(expr, Content::SizeOf(Box::new(type_tag))));
      }
      ("as", [a, b]) => {
        let a = self.to_ast(a)?;
        let t = self.to_type(b)?;
        Ok(node(expr, Content::Convert(Box::new((a, t)))))
      }
      ("&&", [a, b]) => {
        let a = self.to_ast(a)?;
        let b = self.to_ast(b)?;
        Ok(node(expr, Content::ShortCircuit(self.cache.get(instr), vec!(a, b))))
      }
      ("||", [a, b]) => {
        let a = self.to_ast(a)?;
        let b = self.to_ast(b)?;
        Ok(node(expr, Content::ShortCircuit(self.cache.get(instr), vec!(a, b))))
      }
      ("let", exprs) => {
        let name = self.cache.get(exprs[0].symbol_unwrap()?);
        let v = Box::new(self.to_ast(&exprs[1])?);
        // The first scope is used for function arguments. The second
        // is the top level of the function.
        let c = if self.is_top_level && self.variable_scope.len() == 2 {
          // global variable
          self.add_symbol(expr.loc, name.clone(), SymbolDefinition::GlobalDef(Type::Unresolved))?;
          Content::DefineGlobalVariable(name, v)
        }
        else {
          // local variable
          let variable_id = self.create_unique_variable_id(name.clone());
          Content::DefineLocalVariable(name, variable_id, v)
        };
        Ok(node(expr, c))
      }
      // TODO this is a very stupid approach
      ("quote", [e]) => {
        Ok(node(expr, Content::Quote(Box::new(e.clone()))))
      }
      ("=", [assign_expr, value_expr]) => {
        let a = self.to_ast(assign_expr)?;
        let b = self.to_ast(value_expr)?;
        Ok(node(expr, Content::Assignment(Box::new((a, b)))))
      }
      ("return", exprs) => {
        if exprs.len() > 1 {
          return error(expr, format!("malformed return expression"));
        }
        let return_val =
          if exprs.len() == 1 {
            let v = self.to_ast(&exprs[0])?;
            Some(Box::new(v))
          }
          else {
            None
          };
        Ok(node(expr, Content::ExplicitReturn(return_val)))
      }
      ("while", [condition_node, body_node]) => {
        let condition = self.to_ast(condition_node)?;
        let body = self.to_ast(body_node)?;
        Ok(node(expr, Content::While(Box::new((condition, body)))))
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
          /* TODO: remember
          if then_branch.type_tag != else_branch.type_tag {
            return error(expr, "if/else branch type mismatch");
          }
          let t = then_branch.type_tag.clone();
          */
          let c = Content::IfThenElse(Box::new((condition, then_branch, else_branch)));
          Ok(node(expr, c))
        }
        else {
          Ok(node(expr, Content::IfThen(Box::new((condition, then_branch)))))
        }
      }
      ("block", exprs) => {
        self.variable_scope.push(HashMap::new());
        let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<TypedNode>, Error>>()?;
        self.variable_scope.pop();
        // TODO: remember
        // let tag = nodes.last().map(|n| n.type_tag.clone()).unwrap_or(Type::Void);
        Ok(node(expr, Content::Block(nodes)))
      }
      ("cfun", exprs) => {
        let name_expr = &exprs[0];
        let args_exprs = exprs[1].children.as_slice();
        let return_type_expr = &exprs[2];
        let name = self.cache.get(name_expr.symbol_unwrap()?);
        let mut arg_names = vec!();
        let mut arg_types = vec!();
        for (name_expr, type_expr) in args_exprs.iter().tuples() {
          let name = self.cache.get(name_expr.symbol_unwrap()?);
          let type_tag = self.to_type(type_expr)?;
          if type_tag == Type::Void {
            return error(expr, "functions args cannot be void");
          }
          arg_names.push(symbol(name, name_expr.loc));
          arg_types.push(type_tag);
        }
        let return_type = self.to_type(return_type_expr)?;
        let signature = Rc::new(FunctionSignature {
          return_type,
          args: arg_types,
        });
        println!("Warning: C function '{}' not linked. LLVM linker may link it instead.", name);
        let def = FunctionDefinition {
          name: symbol(name.clone(), name_expr.loc),
          args: arg_names,
          signature,
          implementation: FunctionImplementation::CFunction(0), //TODO: THIS IS BROKEN
        };
        self.add_symbol(expr.loc, name.clone(), SymbolDefinition::FunctionDef(def));
        Ok(node(expr, Content::CFunctionPrototype(name)))
      }
      ("fun", exprs) => {
        let name_expr = &exprs[0];
        let name = self.cache.get(name_expr.symbol_unwrap()?);
        let args_exprs = exprs[1].children.as_slice();
        let function_body = &exprs[2];
        let mut arg_names = vec!();
        let mut arg_types = vec!();
        for (name_expr, type_expr) in args_exprs.iter().tuples() {
          let name = self.cache.get(name_expr.symbol_unwrap()?);
          let type_tag = self.to_type(type_expr)?;
          arg_names.push(symbol(name, name_expr.loc));
          arg_types.push(type_tag);
        }
        let def = self.convert_function_body(symbol(name, name_expr.loc), arg_names, arg_types, function_body, false)?;
        self.add_symbol(expr.loc, name.clone(), SymbolDefinition::FunctionDef(def));
        Ok(node(expr, Content::FunctionDefinition(name)))
      }
      ("union", exprs) => {
        let def = self.to_type_definition(expr)?;
        Ok(node(expr, Content::TypeDefinition(def.name.text.clone())))
      }
      ("struct", exprs) => {
        let def = self.to_type_definition(expr)?;
        Ok(node(expr, Content::TypeDefinition(def.name.text.clone())))
      }
      ("type_instantiate", exprs) => {
        if exprs.len() < 1 || exprs.len() % 2 == 0 {
          return error(expr, format!("malformed type instantiation"));
        }
        let name_expr = &exprs[0];
        let field_exprs = &exprs[1..];
        let name = self.cache.get(name_expr.symbol_unwrap()?);
        let fields =
          field_exprs.iter().tuples().map(|(name_expr, value)| {
            let name = self.cache.get(name_expr.symbol_unwrap()?);
            let value = self.to_ast(value)?;
            Ok((symbol(name, name_expr.loc), value))
          })
          .collect::<Result<Vec<(Symbol, TypedNode)>, Error>>()?;
        let c = Content::TypeInstantiate(symbol(name, name_expr.loc), fields);
        Ok(node(expr, c))
      }
      (".", [container_expr, field_expr]) => {
        let container_val = self.to_ast(container_expr)?;
        let field_name = self.cache.get(field_expr.symbol_unwrap()?);
        // TODO remember:
        // let def = match &container_val.type_tag {
        //   Type::Def(name) => self.get_type_def(name).unwrap(),
        //   _ => return error(container_expr, format!("expected struct or union, found {:?}", container_val.type_tag)),
        // };
        // let (field_index, (_, field_type)) =
        //   def.fields.iter().enumerate().find(|(_, (n, _))| n==&field_name)
        //   .ok_or_else(|| error_raw(field_expr, "type does not have field with this name"))?;
        let c = Content::FieldAccess(Box::new((container_val, symbol(field_name, field_expr.loc))));
        Ok(node(expr, c))
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
        // TODO remember: Ok(node(expr, Type::Ptr(Box::new(t)), Content::ArrayLiteral(elements)))
        Ok(node(expr, Content::ArrayLiteral(elements)))
      }
      ("index", [array_expr, index_expr]) => {
        let array = self.to_ast(array_expr)?;
        // TODO remember:
        // let inner_type = match &array.type_tag {
        //   Type::Ptr(t) => *(t).clone(),
        //   _ => return error(array_expr, "expected ptr"),
        // };
        let index = self.to_ast(index_expr)?;
        // if index.type_tag != Type::I64 {
        //   return error(index_expr, "expected integer");
        // }
        Ok(node(expr, Content::Index(Box::new((array, index)))))
      }
      _ => return error(expr, "unsupported expression"),
    }
  }

  fn to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    match &expr.tag {
      ExprTag::Symbol(s) => {
        // Is this a tree?
        let children = expr.children.as_slice();
        if children.len() > 0 {
          return self.tree_to_ast(expr);
        }
        // this is just a normal symbol
        let s = self.cache.get(s.as_str());
        if s.as_ref() == "break" {
          return Ok(node(expr, Content::Break));
        }
        let local_var_id = self.get_local_variable_id(&s);
        if let Some(id) = local_var_id {
          return Ok(node(expr, Content::LocalVariableReference(s, id)));
        }
        else {
          return Ok(node(expr, Content::SymbolReference(s)));
        }
      }
      ExprTag::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        Ok(node(expr, Content::Literal(v)))
      }
      ExprTag::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(node(expr, Content::Literal(v)))
      }
      ExprTag::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(node(expr, Content::Literal(v)))
      }
      ExprTag::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(node(expr, Content::Literal(v)))
      },
      ExprTag::LiteralUnit => {
        Ok(node(expr, Content::Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }
}

impl <'l> TypeResolver<'l> {

  fn find_symbol(&self, name : &str)-> Option<&SymbolDefinition> {
    self.modules.iter().flat_map(|m| m.symbols.get(name)).nth(0)
  }

  fn symbol(&self, name : &str) -> Result<&SymbolDefinition, Error> {
    panic!()
  }

  fn unwrap_definition(&self, n : &TypedNode) -> Result<&TypeDefinition, Error> {
    match &n.type_tag {
      Type::Def(def) => match self.symbol(def)? {
        SymbolDefinition::TypeDef(def) => return Ok(&def),
        _ => (),
      },
      _ => (),
    }
    error(n.loc, "expected struct or union")
  }

  fn resolve_node(&self, n : &mut TypedNode) -> Result<(), Error> {
    use Content::*;
    if n.type_tag != Type::Unresolved {
      return Ok(());
    }
    let t : Type = match &n.content {
      SymbolReference(name) => {
        match self.symbol(name)? {
          SymbolDefinition::GlobalDef(t) => t.clone(),
          SymbolDefinition::FunctionDef(def) => Type::Fun(def.signature.clone()),
          SymbolDefinition::TypeDef(def) => Type::Def(def.name.text.clone()),
        }
      }
      LocalVariableReference(name, id) => {
        panic!()
      }
      DefineGlobalVariable(name, value) => {
        // resolve the type and assign it to the new module
        Type::Void
      }
      DefineLocalVariable(name, id, value) => {
        // TODO: add a value to some hashmap or something
        Type::Void
      }
      Assignment(ns) => {
        let (assignee, value) = (&mut ns.0, &mut ns.1);
        // TODO: check that the assignee and value are compatible
        Type::Void
      }
      IfThen(ns) => {
        let (condition, then_branch) = (&mut ns.0, &mut ns.1);
        // TODO: check that the condition is a bool
        Type::Void
      }
      IfThenElse(ns) => {
        let (condition, then_branch, else_branch) = (&mut ns.0, &mut &ns.1, &mut &ns.2);
        self.resolve_node(condition)?;
        self.resolve_node(then_branch)?;
        self.resolve_node(else_branch)?;
        // TODO: check that the condition is a bool
        // TODO: check that the two branches have the same return type
        else_branch.type_tag.clone()
      }
      Block(ns) => {
        if let Some(n) = ns.last() {
          n.type_tag.clone()
        }
        else {
          Type::Void
        }
      }
      Quote(n) => {
        Type::Ptr(Box::new(Type::U8))
      }
      FunctionDefinition(name) => {
        Type::Void
      }
      CFunctionPrototype(name) => {
        Type::Void
      }
      TypeDefinition(name) => {
        Type::Void
      }
      TypeInstantiate(name, fields) => {
        let def =
          self.find_symbol(&name.text)
          .and_then(|s| match s { SymbolDefinition::TypeDef(t) => Some(t), _ => None})
          .ok_or_else(|| error_raw(n.loc, "no struct with this name exists"))?;
        match def.kind {
          TypeKind::Struct => {
            if fields.len() != def.fields.len() {
              return error(n.loc, "wrong number of fields");
            }
            for ((field, value), (expected_name, expected_type)) in fields.iter().zip(def.fields.iter()) {
              if field.text.as_ref() != "" && field.text != expected_name.text {
                return error(n.loc, "incorrect field name");
              }
              if &value.type_tag != expected_type {
                return error(value.loc, format!("type mismatch. expected {:?}, found {:?}", expected_type, value.type_tag));
              }
            }
          }
          TypeKind::Union => {
            if fields.len() != 1 {
              return error(n.loc, "must instantiate exactly one field");
            }
            let (field, value) = fields.into_iter().nth(0).unwrap();
            if def.fields.iter().find(|(n, _)| n.text == field.text).is_none() {
              return error(n.loc, "field does not exist in this union");
            }
          }
        }
        Type::Def(name.text.clone())
      }
      FieldAccess(x) => {
        let (container, field_name) = (&mut x.0, &x.1);
        let def = self.unwrap_definition(container)?;
        let (_, field_type) =
          def.fields.iter().find(|(n, _)| n.text==field_name.text)
          .ok_or_else(|| error_raw(field_name.loc, "type does not have field with this name"))?;
        field_type.clone()
      }
      Index(ns) => {
        let (array, index) = (&mut ns.0, &mut ns.1);
        // TODO: check index type
        // TODO: check array type
        match &array.type_tag {
          Type::Ptr(t) => (**t).clone(),
          _ => return error(array.loc, "expected array"),
        }
      }
      ArrayLiteral(ns) => {
        // TODO: check that all the types are the same
        Type::Ptr(Box::new(ns[0].type_tag.clone()))
      }
      FunctionCall(f, args) => {
        // TODO: check function type
        // TODO: check args
        match &f.type_tag {
          Type::Fun(sig) => {
            if args.len() != sig.args.len() {
              return error(n.loc, "incorrect number of arguments")
            }
            for (a, t) in args.iter().zip(sig.args.iter()) {
              if &a.type_tag != t {
                return error(a.loc, "argument type did not match function signature")
              }
            }
            sig.return_type.clone()
          }
          _ => {
            return error(n.loc, "expected function type");
          }
        }
      }
      ShortCircuit(operation, ns) => {
        // TODO: check operand types
        Type::Bool
      }
      While(ns) => {
        let (condition, block) = (&mut ns.0, &mut ns.1);
        // TODO: check condition type
        Type::Void
      }
      ExplicitReturn(n) => {
        if let Some(n) = &*n {
          n.type_tag.clone()
        }
        else {
          Type::Void
        }
      }
      Convert(x) => {
        let (n, t) = (&mut x.0, &mut x.1);
        t.clone()
      }
      Deref(p) => {
        match &p.type_tag {
          Type::Ptr(t) => (**t).clone(),
          _ => return error(n.loc, "expected pointer")
        }
      }
      SizeOf(t) => {
        Type::U64
      }
      Break => Type::Void,
      Literal(val) => {
        match val {
          Val::Bool(_) => Type::Bool,
          Val::F32(_) => Type::F32,
          Val::F64(_) => Type::F64,
          Val::U8(_) => Type::U8,
          Val::U16(_) => Type::U16,
          Val::U32(_) => Type::U32,
          Val::U64(_) => Type::U64,
          Val::I32(_) => Type::I32,
          Val::I64(_) => Type::I64,
          Val::String(s) => Type::Def(self.cache.get("string")), // TODO: this could collide with a local variable!
          Val::Void => Type::Void,
        }
      }
    };
    n.type_tag = t;
    Ok(())
  }

  fn check_type_exists(&self, t : &Type) -> Result<(), Error> {
    match t {
      Type::Fun(sig) => {

      }
      Type::Def(name) => {

      }
      Type::Ptr(t) =>
      Type::Unresolved => return error(loc: L, message: S)
    }
    panic!()
  }

  fn check_type_definition(&self, def : &TypeDefinition) -> Result<(), Error> {
    for (_, t) in def.fields.iter() {
      self.check_type_exists(t)?;
    }
    Ok(())
  }

  fn check_signature(&self, sig : &FunctionSignature) -> Result<(), Error> {
    for t in sig.args.iter() {
      self.check_type_exists(t)?;
    }
    self.check_type_exists(&sig.return_type)
  }

  fn resolve_module(&self, module : &mut TypedModule) -> Result<(), Error> {
    for sym in module.symbols.values_mut() {
      match sym {
        SymbolDefinition::FunctionDef(def) => {
          self.check_signature(&def.signature)?;
          match &mut def.implementation {
            FunctionImplementation::Normal(body) => {
              self.resolve_node(body)?;
            }
            _ => (),
          }
          
        }
        SymbolDefinition::GlobalDef(t) => {
          self.check_type_exists(t)?;
        }
        SymbolDefinition::TypeDef(def) => {
          self.check_type_definition(def)?;
        }
        _ => ()
      }
    }
    Ok(())
  }

  fn convert_to_structured_module(&self, expr: &Expr) -> Result<TypedModule, Error> {
    let mut new_module = TypedModule { symbols: HashMap::new() };
    let mut converter =
      ExprConverter::new(self.cache, &mut new_module, true, HashSet::new());

    let top_level_function = converter.convert_top_level_function(expr)?;

    Ok(new_module)
  }

  pub fn to_typed_module(&self, expr: &Expr) -> Result<TypedModule, Error> {
    self.convert_to_structured_module(expr)
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
