
use crate::error::{Error, error, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

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

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "top_level";

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LabelId {
  id : u64
}

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableInitialise{ name: RefStr, value: Box<TypedNode> },
  Assignment{ assignee: Box<TypedNode> , value: Box<TypedNode> },
  IfThen{ condition: Box<TypedNode>, then_branch: Box<TypedNode> },
  IfThenElse{ condition: Box<TypedNode>, then_branch: Box<TypedNode>, else_branch: Box<TypedNode> },
  Block(Vec<TypedNode>),
  Quote(Box<Expr>),
  Reference(RefStr),
  FunctionDefinition{ name: RefStr, args: Vec<(RefStr, Option<TypedNode>)>, body: Box<TypedNode> },
  CBind { name: RefStr, type_tag : Box<TypedNode> },
  StructDefinition{ name: RefStr, fields: Vec<(RefStr, Option<TypedNode>)> },
  UnionDefinition{ name: RefStr, fields: Vec<(RefStr, Option<TypedNode>)> },
  TypeConstructor{ name: RefStr, field_values: Vec<(Option<RefStr>, TypedNode)> },
  FieldAccess{ container: Box<TypedNode>, field: RefStr },
  Index{ container: Box<TypedNode>, index: Box<TypedNode> },
  ArrayLiteral(Vec<TypedNode>),
  FunctionCall{ function: Box<TypedNode>, args: Vec<TypedNode> },
  While{ condition: Box<TypedNode>, body: Box<TypedNode> },
  Convert{ from_value: Box<TypedNode>, into_type: Box<TypedNode> },
  SizeOf{ type_tag: Box<TypedNode> },

  Label{ label: LabelId, body: Box<TypedNode> },
  BreakToLabel{ label: LabelId, return_value: Option<Box<TypedNode>> },
}

use Content::*;

#[derive(Debug)]
pub struct TypedNode {
  pub content : Content,
  pub loc : TextLocation,
}

fn node(expr : &Expr, content : Content) -> TypedNode {
  TypedNode { content, loc: expr.loc }
}

pub struct GlobalDefinition {
  pub name : RefStr,
  pub c_address : Option<usize>,
}

struct SymbolReference {
  symbol_name : RefStr,
  reference_location : TextLocation,
}

pub struct NodeConverter<'l> {
  uid_generator : &'l mut UIDGenerator,

  cache: &'l StringCache,
}

pub struct FunctionConverter<'l, 'lt> {
  t : &'l mut NodeConverter<'lt>,

  labels_in_scope : Vec<LabelId>,
}

impl <'l> NodeConverter<'l> {

  pub fn new(
    uid_generator : &'l mut UIDGenerator,
    cache : &'l StringCache)
      -> NodeConverter<'l>
  {
    NodeConverter {
      uid_generator,
      cache,
    }
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let mut fc = FunctionConverter::new(self);
    fc.to_ast(expr)
  }
}

impl <'l, 'lt> FunctionConverter<'l, 'lt> {

  pub fn new(t : &'l mut NodeConverter<'lt>) -> FunctionConverter<'l, 'lt> {
    FunctionConverter { t, labels_in_scope : vec![],
    }
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(RefStr, Option<TypedNode>), Error> {
    if let Some((":", [s, t])) = e.try_construct() {
      let name = self.cached(s.unwrap_symbol()?);
      let type_tag = self.to_ast(t)?;
      Ok((name, Some(type_tag)))
    }
    else if let Ok(s) = e.unwrap_symbol() {
      let name = self.cached(s);
      Ok((name, None))
    }
    else {
      error(e, "invalid typed symbol construct")
    }
  }

  fn cached(&self, s : &str) -> RefStr {
    self.t.cache.get(s)
  }

  fn compile_template_arguments(&mut self, e : &Expr, args : &mut Vec<TypedNode>) -> Result<(), Error> {
    match e.try_construct() {
      Some(("$", [e])) => {
        args.push(self.to_ast(e)?);
      }
      Some((_, es)) => {
        for e in es {
          self.compile_template_arguments(e, args)?;
        }
      }
      _ => (),
    }
    Ok(())
  }

  /// Converts a quote to a typed node and handles templating if necessary
  fn quote_to_ast(&mut self, expr : &Expr, quoted_expr : &Expr) -> Result<TypedNode, Error> {
    // TODO: this function is kind of verbose and difficult to read
    let e = quoted_expr;
    let mut template_args = vec![];
    self.compile_template_arguments(e, &mut template_args)?;
    let main_quote = node(expr, Quote(Box::new(e.clone())));
    if template_args.len() > 0 {
      let mut coerced_args = vec![];
      let loc_name = self.cached("text_location");
      let marker_name = self.cached("text_marker");
      for n in template_args.into_iter() {
        let loc = loc_struct(expr, loc_name.clone(), marker_name.clone());
        let expr_val = function_call(expr, self.cached("sym"), vec![n, loc]);
        let arg = function_call(expr, self.cached("&"), vec![expr_val]);
        coerced_args.push(arg);
      }
      let array_literal = array_literal(expr, coerced_args);
      Ok(function_call(expr, self.cached("template_quote"), vec![main_quote, array_literal]))
    }
    else {
      Ok(main_quote)
    }
  }

  fn to_type_constructor(&mut self, expr : &Expr, exprs : &[Expr]) -> Result<TypedNode, Error> {
    if exprs.len() < 1 {
      return error(expr, format!("malformed type instantiation"));
    }
    let name_expr = &exprs[0];
    let field_exprs = &exprs[1..];
    let name = self.cached(name_expr.unwrap_symbol()?);
    let field_values =
      field_exprs.iter().map(|e| {
        if let Some((":", [name, value])) = e.try_construct() {
          let name = self.cached(name.unwrap_symbol()?);
          Ok((Some(name), self.to_ast(value)?))
        }
        else {
          Ok((None, self.to_ast(e)?))
        }
      })
      .collect::<Result<Vec<(Option<RefStr>, TypedNode)>, Error>>()?;
    let c = TypeConstructor{ name, field_values };
    Ok(node(expr, c))
  }

  fn construct_to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let (instr, children) = expr.unwrap_construct()?;
    match (instr, children) {
      ("call", exprs) => {
        let function_expr = &exprs[0];
        match function_expr.try_symbol() {
          Some("new") => return self.to_type_constructor(expr, &exprs[1..]),
          Some("sizeof") => {
            if exprs.len() == 2 {
              let type_tag = Box::new(self.to_ast(&exprs[1])?);
              return Ok(node(expr, SizeOf{ type_tag }));
            }
          }
          _ => (),
        }
        let args =
          exprs[1..].iter().map(|e| self.to_ast(e))
          .collect::<Result<Vec<TypedNode>, Error>>()?;
        let function = Box::new(self.to_ast(function_expr)?);
        let content = FunctionCall{ function, args };
        return Ok(node(expr, content));
      }
      ("as", [from_value, into_type]) => {
        let from_value = Box::new(self.to_ast(from_value)?);
        let into_type = Box::new(self.to_ast(into_type)?);
        Ok(node(expr, Convert{ from_value, into_type }))
      }
      ("let", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let value = Box::new(self.to_ast(value_expr)?);
          let c = VariableInitialise{ name, value };
          return Ok(node(expr, c));
        }
        error(expr, "malformed let expression")
      }
      ("#", [quoted_expr]) => {
        self.quote_to_ast(expr, quoted_expr)
      }
      ("return", exprs) => {
        if exprs.len() > 1 {
          return error(expr, format!("malformed return expression"));
        }
        let return_value = if let [e] = exprs {
          let v = self.to_ast(&e)?;
          Some(Box::new(v))
        }
        else {
          None
        };
        let label = *self.labels_in_scope.first().unwrap();
        let c = BreakToLabel{ label, return_value };
        Ok(node(expr, c))
      }
      ("while", [condition_expr, body_expr]) => {
        let label = LabelId { id: self.t.uid_generator.next() };
        // Add label to scope in case the loop breaks
        self.labels_in_scope.push(label);
        let condition = Box::new(self.to_ast(condition_expr)?);
        let body = Box::new(self.to_ast(body_expr)?);
        let while_node = node(expr, While{ condition, body });
        let labelled_while = node(expr, Label{ label, body: Box::new(while_node) });
        // Remove label
        self.labels_in_scope.pop();
        Ok(labelled_while)
      }
      // ("for", [var_range_expr, body_expr]) => {
      //   if let Some(("in", [var, range])) = var_range_expr.try_construct() {
      //     if let Some(var_name) = var.try_symbol() {
      //       /*
      //         {
      //           let #range = range(0, 10)
      //           let #end = #range.end
      //           let i = #range.start
      //           while i < #end {
      //             $body_expr
      //             i = i + 1
      //           }
      //         }
      //       */
      //       let range_var = self.cached("@range_var");
      //       let end_var = self.cached("@end_var");
      //       let loop_var = self.cached("@loop_var");
      //       let range_node = self.to_ast(range)?;
      //       let for_block = block(expr, vec![
      //         let_var(expr, range_var.clone(), range_node),
      //         let_var(expr, end_var.clone(), field_access(expr, range_var.clone(), "end")),
      //         let_var(expr, loop_var.clone(), field_access(expr, range_var.clone(), "start")),
      //         node(expr, Type::Void, While((
      //           intrinsic("<", vec![loop_var, end_var]),
      //           block(expr, vec![
      //             self.to_ast(body_expr)?,
      //             assignment(loop_var, intrinsic("+", vec![loop_var, literal_int(1)])),
      //           ])
      //         ).into()))
      //       ]);
      //       return Ok(for_block);
      //     }
      //   }
      //   error(expr, "malformed for expression")
      // }
      ("if", exprs) => {
        if exprs.len() > 3 {
          return error(expr, "malformed if expression");
        }
        let condition = Box::new(self.to_ast(&exprs[0])?);
        let then_branch = Box::new(self.to_ast(&exprs[1])?);
        if exprs.len() == 3 {
          let else_branch = Box::new(self.to_ast(&exprs[2])?);
          let c = IfThenElse{ condition, then_branch, else_branch };
          Ok(node(expr, c))
        }
        else {
          Ok(node(expr, IfThen{ condition, then_branch }))
        }
      }
      ("block", exprs) => {
        let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<TypedNode>, Error>>()?;
        Ok(node(expr, Block(nodes)))
      }
      ("cbind", [e]) => {
        if let (":", [name_expr, type_expr]) = e.unwrap_construct()? {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let type_tag = Box::new(self.to_ast(type_expr)?);
          return Ok(node(expr, CBind{ name, type_tag }));
        }
        error(expr, "invalid cbind expression")
      }
      ("fun", exprs) => {
        if let [name, args_expr, function_body] = exprs {
          let name = self.cached(name.unwrap_symbol()?);
          let args =
            args_expr.children().iter()
            .map(|e| self.typed_symbol(e))
            .collect::<Result<Vec<_>, Error>>()?;
          let mut function_checker = FunctionConverter::new(self.t);
          let body = Box::new(function_checker.to_function_body(function_body)?);
          return Ok(node(expr, FunctionDefinition{name, args, body}));
        }
        error(expr, "malformed function definition")
      }
      ("union", [name, fields_expr]) => {
        let name = self.cached(name.unwrap_symbol()?);
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        Ok(node(expr, UnionDefinition{name, fields}))
      }
      ("struct", [name, fields_expr]) => {
        let name = self.cached(name.unwrap_symbol()?);
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        Ok(node(expr, StructDefinition{name, fields}))
      }
      (".", [container_expr, field_expr]) => {
        let container = Box::new(self.to_ast(container_expr)?);
        let field = self.cached(field_expr.unwrap_symbol()?);
        let c = FieldAccess{ container, field };
        Ok(node(expr, c))
      }
      ("array", exprs) => {
        let mut elements = vec!();
        for e in exprs {
          elements.push(self.to_ast(e)?);
        }
        Ok(node(expr, ArrayLiteral(elements)))
      }
      ("index", exprs) => {
        let array_expr = &exprs[0];
        if let [index_expr] = &exprs[1..] {
          let container = self.to_ast(array_expr)?.into();
          let index = self.to_ast(index_expr)?.into();
          return Ok(node(expr, Index{ container, index }));
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
          let label = *self.labels_in_scope.last().unwrap();
          let c = BreakToLabel{ label , return_value: None };
          return Ok(node(expr, c));
        }
        return Ok(node(expr, Reference(s)));
      }
      ExprContent::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        Ok(node(expr, Literal(v)))
      }
      ExprContent::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(node(expr, Literal(v)))
      }
      ExprContent::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(node(expr, Literal(v)))
      }
      ExprContent::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(node(expr, Literal(v)))
      },
      ExprContent::LiteralUnit => {
        Ok(node(expr, Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }

  fn to_function_body(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    if self.labels_in_scope.len() != 0 {
      panic!("labels_in_scope in invalid state");
    }
    let label = LabelId{ id: self.t.uid_generator.next() };
    self.labels_in_scope.push(label);
    let body = self.to_ast(expr)?.into();
    self.labels_in_scope.pop();
    let c = Label{ label, body };
    Ok(node(expr, c))
  }
}

fn loc_struct(expr : &Expr, loc_name : RefStr, marker_name : RefStr) -> TypedNode {
  let start = {
    let col = u64_literal(expr, expr.loc.start.col as u64);
    let line = u64_literal(expr, expr.loc.start.line as u64);
    type_constructor(expr, marker_name.clone(), vec![col, line])
  };
  let end = {
    let col = u64_literal(expr, expr.loc.end.col as u64);
    let line = u64_literal(expr, expr.loc.end.line as u64);
    type_constructor(expr, marker_name, vec![col, line])
  };
  type_constructor(expr, loc_name, vec![start, end])
}

fn let_var(expr : &Expr, name : RefStr, val : TypedNode) -> TypedNode {
  node(expr, VariableInitialise{ name, value: val.into() })
}

fn field_access(expr : &Expr, container : TypedNode, field : RefStr) -> TypedNode {
  node(expr, FieldAccess{ container: container.into(), field })
}

fn block(expr : &Expr, args : Vec<TypedNode>) -> TypedNode {
  node(expr, Block(args))
}

fn u64_literal(expr : &Expr, i : u64) -> TypedNode {
  node(expr, Literal(Val::U64(i)))
}

fn array_literal(expr : &Expr, args : Vec<TypedNode>) -> TypedNode {
  let args = ArrayLiteral(args);
  node(expr, args)
}

fn reference(expr : &Expr, name : RefStr) -> TypedNode {
  node(expr, Content::Reference(name))
}

fn function_call(expr : &Expr, function : RefStr, args : Vec<TypedNode>) -> TypedNode {
  let function = node(expr, Reference(function)).into();
  let function_call = FunctionCall{ function, args };
  node(expr, function_call)
}

fn type_constructor(expr : &Expr, name : RefStr, field_values : Vec<TypedNode>) -> TypedNode {
  let field_values = field_values.into_iter().map(|a| (None, a)).collect();
  node(expr, TypeConstructor{ name, field_values })
}
