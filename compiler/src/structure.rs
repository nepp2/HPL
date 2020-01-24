
use crate::error::{Error, error, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

use std::collections::HashMap;

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "__top_level";

#[derive(Clone, PartialEq, Debug)]
pub enum PrimitiveVal {
  Void,
  Float(f64),
  Int(i64),
  String(String),
  Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LabelId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReferenceId(u64);

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TypeKind {
  Struct, Union
}

#[derive(Debug, Clone)]
pub struct Reference {
  pub id : ReferenceId,
  pub name : RefStr,
  pub loc : TextLocation,
}

/// TODO: This is a messy way of supporting REPL functionality.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum GlobalType { Normal, CBind }

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global(GlobalType) }

#[derive(Debug)]
pub enum Content {
  Literal(PrimitiveVal),
  VariableInitialise{ name: Reference, type_tag: Option<Box<Expr>>, value: NodeId, var_scope : VarScope },
  Assignment{ assignee: NodeId , value: NodeId },
  IfThen{ condition: NodeId, then_branch: NodeId },
  IfThenElse{ condition: NodeId, then_branch: NodeId, else_branch: NodeId },
  Block(Vec<NodeId>),
  Quote(Box<Expr>),
  Reference { name: RefStr, refers_to: Option<ReferenceId> },
  FunctionDefinition{ name: RefStr, args: Vec<(Reference, Option<Box<Expr>>)>, return_tag: Option<Box<Expr>>, type_vars : Vec<RefStr>, body: NodeId },
  CBind { name: RefStr, type_tag : Box<Expr> },
  TypeDefinition{ name: RefStr, kind : TypeKind, fields: Vec<(Reference, Option<Box<Expr>>)>, type_vars : Vec<RefStr> },
  TypeConstructor{ name: Reference, field_values: Vec<(Option<Reference>, NodeId)> },
  FieldAccess{ container: NodeId, field: Reference },
  ArrayLiteral(Vec<NodeId>),
  FunctionCall{ function: NodeId, args: Vec<NodeId> },
  While{ condition: NodeId, body: NodeId },
  Convert{ from_value: NodeId, into_type: Box<Expr> },
  SizeOf{ type_tag: Box<Expr> },

  Label{ label: LabelId, body: NodeId },
  BreakToLabel{ label: LabelId, return_value: Option<NodeId> },
}

impl Content {
  pub fn node_value_type(&self) -> NodeValueType {
    match self {
      FieldAccess{..} | Content::Reference{..} |
      Literal(_) | Quote(_)
        => NodeValueType::Reference,
      Block(_) | FunctionCall{..} |
      IfThenElse{..} | TypeConstructor{..}
        => NodeValueType::Owned,
      _ => NodeValueType::Nil,
    }
  }
}

use Content::*;

/// This indicates whether the type is a full value, or just a reference to one.
/// When an expression is evaluated to a full value, it may need to be dropped later.
/// When a reference turns into a value, it may need to be cloned.
#[derive(Debug, PartialEq)]
pub enum NodeValueType {
  Owned,
  Reference,
  Mut,
  Nil,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(u64);

impl From<u64> for NodeId { fn from(v : u64) -> Self { NodeId(v) } }

#[derive(Debug)]
pub struct Node {
  pub id : NodeId,
  pub content : Content,
  pub loc : TextLocation,
}

pub struct NodeConverter<'l> {
  uid_generator : &'l mut UIDGenerator,

  nodes : HashMap<NodeId, Node>,

  symbols : HashMap<ReferenceId, Reference>,

  cache: &'l StringCache,
}

pub struct FunctionConverter<'l, 'lt> {
  t : &'l mut NodeConverter<'lt>,
  is_top_level : bool,
  labels_in_scope : Vec<LabelId>,
  block_scope : Vec<Vec<Reference>>,
}

pub struct Nodes {
  pub nodes : HashMap<NodeId, Node>,
  pub symbols : HashMap<ReferenceId, Reference>,
  pub root : NodeId,
}

impl Nodes {
  pub fn node(&self, id : NodeId) -> &Node {
    self.nodes.get(&id).unwrap()
  }

  pub fn root(&self) -> &Node {
    self.nodes.get(&self.root).unwrap()
  }

  pub fn symbol(&self, id : ReferenceId) -> &Reference {
    self.symbols.get(&id).unwrap()
  }

  pub fn node_ref(&self, id : NodeId) -> NodeRef {
    NodeRef{ n: self.nodes.get(&id).unwrap(), nodes: self }
  }
}

#[derive(Copy, Clone)]
pub struct NodeRef<'l> {
  pub n : &'l Node,
  pub nodes : &'l Nodes,
}

impl <'l> NodeRef<'l> {
  pub fn get(&self, id : NodeId) -> NodeRef<'l> {
    self.nodes.node_ref(id)
  }

  pub fn content(&self) -> &Content {
    &self.n.content
  }

  pub fn id(&self) -> NodeId {
    self.n.id
  }
}

pub fn to_nodes(
  uid_generator : &mut UIDGenerator,
  cache : &StringCache,
  expr : &Expr)
    -> Result<Nodes, Error>
{
  let mut nc = NodeConverter {
    uid_generator,
    nodes: HashMap::new(),
    symbols: HashMap::new(),
    cache,
  };
  let mut fc = FunctionConverter::new(&mut nc, true, vec![]);
  let top_level = fc.top_level_expression(expr)?;
  Ok(Nodes{ root: top_level, nodes: nc.nodes, symbols: nc.symbols })
}

impl <'l> NodeConverter<'l> {
  fn node<Loc : Into<TextLocation>>(&mut self, loc : Loc, content : Content) -> NodeId {
    let id = self.uid_generator.next().into();
    let n = Node { id, content, loc: loc.into() };
    self.nodes.insert(id, n);
    id
  }

  fn symbol<Loc : Into<TextLocation>>(&mut self, name : &str, loc : Loc) -> Reference {
    let name = self.cache.get(name);
    let id = ReferenceId(self.uid_generator.next());
    let s = Reference { id, name, loc: loc.into() };
    self.symbols.insert(id, s.clone());
    s
  }
}

impl <'l, 'lt> FunctionConverter<'l, 'lt> {

  pub fn new(t : &'l mut NodeConverter<'lt>, is_top_level : bool, args : Vec<Reference>)
   -> FunctionConverter<'l, 'lt>
  {
    FunctionConverter { t, is_top_level, labels_in_scope : vec![], block_scope: vec![args] }
  }

  fn add_var_to_scope(&mut self, var : Reference) {
    let scope = self.block_scope.last_mut().unwrap();
    scope.push(var);
  }

  fn find_var(&self, name : &str) -> Option<&Reference> {
    for var in self.block_scope.iter().flat_map(|i| i.iter()).rev() {
      if name == var.name.as_ref() { return Some(var) }
    }
    None
  }

  fn expr_to_symbol(&mut self, e : &Expr) -> Result<Reference, Error> {
    let name = e.unwrap_symbol()?;
    Ok(self.t.symbol(name, e.loc))
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(Reference, Option<Box<Expr>>), Error> {
    if let Some((":", [s, t])) = e.try_construct() {
      let symbol = self.expr_to_symbol(s)?;
      let type_tag = t.clone().into();
      Ok((symbol, Some(type_tag)))
    }
    else {
      Ok((self.expr_to_symbol(e)?, None))
    }
  }

  fn cached(&self, s : &str) -> RefStr {
    self.t.cache.get(s)
  }

  fn compile_template_arguments(&mut self, e : &Expr, args : &mut Vec<NodeId>) -> Result<(), Error> {
    match e.try_construct() {
      Some(("$", [e])) => {
        args.push(self.to_node(e)?);
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

  fn node(&mut self, expr : &Expr, content : Content) -> NodeId {
    self.t.node(expr, content)
  }

  /// Converts a quote to a typed node and handles templating if necessary
  fn quote_to_node(&mut self, expr : &Expr, quoted_expr : &Expr) -> Result<NodeId, Error> {
    // TODO: this function is kind of verbose and difficult to read
    let e = quoted_expr;
    let mut template_args = vec![];
    self.compile_template_arguments(e, &mut template_args)?;
    let main_quote = self.node(expr, Quote(Box::new(e.clone())));
    if template_args.len() > 0 {
      let mut coerced_args = vec![];
      for n in template_args.into_iter() {
        let loc = self.loc_struct(expr);
        let expr_val = self.function_call(expr, "sym", vec![n, loc]);
        let arg = self.function_call(expr, "&", vec![expr_val]);
        coerced_args.push(arg);
      }
      let array_literal = self.array_literal(expr, coerced_args);
      Ok(self.function_call(expr, "template_quote", vec![main_quote, array_literal]))
    }
    else {
      Ok(main_quote)
    }
  }

  fn to_type_constructor(&mut self, expr : &Expr, exprs : &[Expr]) -> Result<NodeId, Error> {
    if exprs.len() < 1 {
      return error(expr, format!("malformed type instantiation"));
    }
    let name_expr = &exprs[0];
    let field_exprs = &exprs[1..];
    let name = self.expr_to_symbol(name_expr)?;
    let field_values =
      field_exprs.iter().map(|e| {
        if let Some((":", [name, value])) = e.try_construct() {
          let name = self.expr_to_symbol(name)?;
          Ok((Some(name), self.to_node(value)?))
        }
        else {
          Ok((None, self.to_node(e)?))
        }
      })
      .collect::<Result<Vec<(Option<Reference>, NodeId)>, Error>>()?;
    let c = TypeConstructor{ name, field_values };
    Ok(self.node(expr, c))
  }

  fn function_def_to_node(
    &mut self,
    expr : &Expr,
    name : &Expr,
    args : &Expr,
    return_tag : Option<&Expr>,
    polytypes : Option<&Expr>,
    body : &Expr,
  )
    -> Result<NodeId, Error>
  {
    let name = self.cached(name.unwrap_symbol()?);
    let args =
      args.children().iter()
      .map(|e| self.typed_symbol(e))
      .collect::<Result<Vec<_>, Error>>()?;
    let arg_symbols =
      args.iter().map(|(s, _)| s.clone()).collect();
    let return_tag = {
      if let Some(t) = return_tag {
        Some(Box::new(t.clone()))
      }
      else { None }
    };
    let type_vars = {
      if let Some(("polytypes", ts)) = polytypes.and_then(|e| e.try_construct()) {
        let type_vars =
          ts.iter().map(|e| { let s = self.cached(e.unwrap_symbol()?) ; Ok(s) })
          .collect::<Result<Vec<_>, _>>()?;
        type_vars
      }
      else { vec![] }
    };
    let mut function_checker = FunctionConverter::new(self.t, false, arg_symbols);
    let body = function_checker.to_function_body(body)?;
    return Ok(self.node(expr, FunctionDefinition{name, args, type_vars, return_tag, body}));
  }

  fn construct_to_node(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    let (instr, children) = expr.unwrap_construct()?;
    match (instr, children) {
      ("call", exprs) => {
        let function_expr = &exprs[0];
        match function_expr.try_symbol() {
          Some("new") => return self.to_type_constructor(expr, &exprs[1..]),
          Some("sizeof") => {
            if exprs.len() == 2 {
              let type_tag = exprs[1].clone().into();
              return Ok(self.node(expr, SizeOf{ type_tag }));
            }
          }
          _ => (),
        }
        let args =
          exprs[1..].iter().map(|e| self.to_node(e))
          .collect::<Result<Vec<NodeId>, Error>>()?;
        let function = self.to_node(function_expr)?;
        let content = FunctionCall{ function, args };
        return Ok(self.node(expr, content));
      }
      ("as", [from_value, into_type]) => {
        let from_value = self.to_node(from_value)?;
        let into_type = into_type.clone().into();
        Ok(self.node(expr, Convert{ from_value, into_type }))
      }
      ("static", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let (name, type_tag) = self.typed_symbol(name_expr)?;
          let value = self.to_node(value_expr)?;
          let var_scope = VarScope::Global(GlobalType::Normal);
          let c = VariableInitialise { name, type_tag, value, var_scope };
          return Ok(self.node(expr, c));
        }
        error(expr, "malformed let expression")
      }
      ("let", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let (name, type_tag) = self.typed_symbol(name_expr)?;
          let value = self.to_node(value_expr)?;
          self.add_var_to_scope(name.clone());
          let c = VariableInitialise{ name, type_tag, value, var_scope: VarScope::Local };
          return Ok(self.node(expr, c));
        }
        error(expr, "malformed let expression")
      }
      ("#", [quoted_expr]) => {
        self.quote_to_node(expr, quoted_expr)
      }
      ("=", [assign_expr, value_expr]) => {
        let a = self.to_node(assign_expr)?;
        let b = self.to_node(value_expr)?;
        Ok(self.node(expr, Assignment{ assignee: a, value: b }))
      }
      ("return", exprs) => {
        if exprs.len() > 1 {
          return error(expr, format!("malformed return expression"));
        }
        let return_value = if let [e] = exprs {
          let v = self.to_node(&e)?;
          Some(v)
        }
        else {
          None
        };
        let label = *self.labels_in_scope.first().unwrap();
        let c = BreakToLabel{ label, return_value };
        Ok(self.node(expr, c))
      }
      ("while", [condition_expr, body_expr]) => {
        // Add label to scope in case the loop breaks
        self.labelled_node(expr, |fc| {
          let condition = fc.to_node(condition_expr)?;
          let body = fc.to_node(body_expr)?;
          let while_node = fc.node(expr, While{ condition, body });
          Ok(while_node)
        })
      }
      ("for", [range_expr, body_expr]) => {
        self.for_loop(expr, range_expr, body_expr)
      }
      ("if", exprs) => {
        if exprs.len() > 3 {
          return error(expr, "malformed if expression");
        }
        let condition = self.to_node(&exprs[0])?;
        let then_branch = self.to_node(&exprs[1])?;
        if exprs.len() == 3 {
          let else_branch = self.to_node(&exprs[2])?;
          let c = IfThenElse{ condition, then_branch, else_branch };
          Ok(self.node(expr, c))
        }
        else {
          Ok(self.node(expr, IfThen{ condition, then_branch }))
        }
      }
      ("block", exprs) => {
        let nodes = self.new_block_scope(|fc| {
          exprs.iter().map(|e| fc.to_node(e)).collect::<Result<Vec<NodeId>, Error>>()
        })?;
        Ok(self.node(expr, Block(nodes)))
      }
      ("cbind", [e]) => {
        if let (":", [name_expr, type_expr]) = e.unwrap_construct()? {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let type_tag = type_expr.clone().into();
          return Ok(self.node(expr, CBind{ name, type_tag }));
        }
        error(expr, "invalid cbind expression")
      }
      ("fun", exprs) => {
        // slightly ugly hack to work out which subexpression is which.
        // the return type tag is easily mixed up with the polytypes expression.
        match exprs {
          [name, args, body] =>
            self.function_def_to_node(expr, name, args, None, None, body),
          [name, args, return_tag, polytypes, body] =>
            self.function_def_to_node(
              expr, name, args, Some(return_tag), Some(polytypes), body),
          [name, args, unknown, body] => {
            if let Some(("polytypes", _)) = unknown.try_construct() {
              self.function_def_to_node(
                expr, name, args, None, Some(unknown), body)
            }
            else {
              self.function_def_to_node(
                expr, name, args, Some(unknown), None, body)
            }
          }
          _ => {
            error(expr, "malformed function definition")
          }
        }
      }
      ("union", [name, fields_expr]) => {
        let name = self.cached(name.unwrap_symbol()?);
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        let td = TypeDefinition{name, kind: TypeKind::Union, fields, type_vars: vec![] };
        Ok(self.node(expr, td))
      }
      ("struct", [name, fields_expr]) => {
        let (name, type_vars) = {
          if let Some(("call", exprs)) = name.try_construct() {
            let name = self.cached(exprs[0].unwrap_symbol()?);
            let type_vars : Result<Vec<_>, _> =
              exprs[1..].iter().map(|e| { let s = self.cached(e.unwrap_symbol()?) ; Ok(s) }).collect();
            (name, type_vars?)
          }
          else {
            let name = self.cached(name.unwrap_symbol()?);
            (name, vec![])
          }
        };
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        Ok(self.node(expr, TypeDefinition{name, kind: TypeKind::Struct, fields, type_vars }))
      }
      (".", [container_expr, field_expr]) => {
        let container = self.to_node(container_expr)?;
        let field = self.expr_to_symbol(field_expr)?;
        let c = FieldAccess{ container, field };
        Ok(self.node(expr, c))
      }
      ("array", exprs) => {
        let mut elements = vec!();
        for e in exprs {
          elements.push(self.to_node(e)?);
        }
        Ok(self.node(expr, ArrayLiteral(elements)))
      }
      ("index", exprs) => {
        let array_expr = &exprs[0];
        if let [index_expr] = &exprs[1..] {
          let container = self.to_node(array_expr)?;
          let index = self.to_node(index_expr)?;
          return Ok(self.function_call(expr, "Index", vec![container, index]));
        }
        error(expr, "malformed array index expression")
      }
      (construct, _) => {
        error(expr, format!("invalid '{}' expression", construct))
      }
    }
  }

  pub fn to_node(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    match &expr.content {
      ExprContent::List(_, _) => {
        return self.construct_to_node(expr);
      }
      ExprContent::Symbol(s) => {
        // this is just a normal symbol
        let s = s.as_str();
        if s == "break" {
          let label = *self.labels_in_scope.last().unwrap();
          let c = BreakToLabel{ label , return_value: None };
          return Ok(self.node(expr, c));
        }
        let name = self.cached(s);
        if let Some(var) = self.find_var(&s) {
          let id = var.id;
          return Ok(self.node(expr, Content::Reference{ name, refers_to: Some(id) }));
        }
        return Ok(self.node(expr, Content::Reference{ name, refers_to: None}));
      }
      ExprContent::LiteralString(s) => {
        let v = PrimitiveVal::String(s.as_str().to_string());
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralFloat(f) => {
        let v = PrimitiveVal::Float(*f as f64);
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralInt(v) => {
        let v = PrimitiveVal::Int(*v as i64);
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralBool(b) => {
        let v = PrimitiveVal::Bool(*b);
        Ok(self.node(expr, Literal(v)))
      },
      ExprContent::LiteralUnit => {
        Ok(self.node(expr, Literal(PrimitiveVal::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }

  fn top_level_expression(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    let c = Content::FunctionDefinition {
      name: self.cached(TOP_LEVEL_FUNCTION_NAME),
      args: vec![],
      return_tag: None,
      type_vars: vec![],
      body: self.to_function_body(expr)?,
    };
    let f = self.node(expr, c);
    Ok(f)
  }

  fn to_function_body(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    if self.labels_in_scope.len() != 0 {
      panic!("labels_in_scope in invalid state");
    }
    self.labelled_node(expr, |fc| {
      fc.to_node(expr)
    })
  }

  fn labelled_node<Loc, F>(&mut self, loc : Loc, f : F)
    -> Result<NodeId, Error>
    where
      Loc : Into<TextLocation>,
      F : Fn(&mut FunctionConverter) -> Result<NodeId, Error>
  {
    let label = LabelId(self.t.uid_generator.next());
    self.labels_in_scope.push(label);
    let body = f(self);
    self.labels_in_scope.pop();
    Ok(self.t.node(loc, Label{ label, body: body? }))
  }

  fn new_block_scope<T, F>(&mut self, f : F)
    -> Result<T, Error>
    where
      F : Fn(&mut FunctionConverter) -> Result<T, Error>
  {
    self.block_scope.push(vec![]);
    let t = f(self);
    self.block_scope.pop();
    Ok(t?)
  }

  fn loc_struct(&mut self, expr : &Expr) -> NodeId {
    let start = {
      let col = self.int_literal(expr, expr.loc.start.col as i64);
      let line = self.int_literal(expr, expr.loc.start.line as i64);
      let text_marker = self.t.symbol("text_marker", expr);
      self.type_constructor(expr, text_marker, vec![col, line])
    };
    let end = {
      let col = self.int_literal(expr, expr.loc.end.col as i64);
      let line = self.int_literal(expr, expr.loc.end.line as i64);
      let text_marker = self.t.symbol("text_marker", expr);
      self.type_constructor(expr, text_marker, vec![col, line])
    };
    let text_location = self.t.symbol("text_location", expr);
    self.type_constructor(expr, text_location, vec![start, end])
  }

  fn let_var(&mut self, expr : &Expr, name : Reference, val : NodeId) -> NodeId {
    self.node(expr, VariableInitialise{ name, type_tag: None, value: val, var_scope : VarScope::Local })
  }

  fn int_literal(&mut self, expr : &Expr, i : i64) -> NodeId {
    self.node(expr, Literal(PrimitiveVal::Int(i)))
  }

  fn array_literal(&mut self, expr : &Expr, args : Vec<NodeId>) -> NodeId {
    let args = ArrayLiteral(args);
    self.node(expr, args)
  }

  fn function_call(&mut self, expr : &Expr, name: &str, args : Vec<NodeId>) -> NodeId {
    let function = self.node(expr, Content::Reference{ name: self.cached(name), refers_to: None });
    let function_call = FunctionCall{ function, args };
    self.node(expr, function_call)
  }

  fn type_constructor(&mut self, expr : &Expr, name : Reference, field_values : Vec<NodeId>) -> NodeId {
    let field_values = field_values.into_iter().map(|a| (None, a)).collect();
    self.node(expr, TypeConstructor{ name, field_values })
  }

  /// TODO: this is implemented entirely in terms of other constructs. It might be nice
  /// to move it into an earlier part of the pipeline (such as an expression macro) to
  /// limit logic duplication and make the code more maintainable.
  fn for_loop(&mut self, e : &Expr, range : &Expr, body : &Expr) -> Result<NodeId, Error> {
    if let Some(("in", [var, range])) = range.try_construct() {
      let n = self.labelled_node(e.loc, |fc| {
        fc.new_block_scope(|fc| {
          let it_var = fc.t.symbol("@range_var", e);
          let loop_var = fc.expr_to_symbol(var)?;
          let let_it_node = {
            let range = fc.to_node(range)?;
            let iter = fc.function_call(e, "iter", vec![range]);
            let iter_ref = fc.function_call(e, "&", vec![iter]);
            fc.let_var(e, it_var.clone(), iter_ref)
          };
          let let_loop_node = {
            let zero = fc.int_literal(e, 0); // this value will be overwritten
            fc.let_var(e, loop_var.clone(), zero)
          };
          fc.add_var_to_scope(loop_var.clone());
          let while_node = {        
            let condition = {
              let it = fc.node(e, Content::Reference{ name: it_var.name.clone(), refers_to: Some(it_var.id) });
              let var_ref = {
                let var = fc.node(e, Content::Reference{ name: loop_var.name.clone(), refers_to: Some(loop_var.id) });
                fc.function_call(e, "&", vec![var])
              };
              fc.function_call(e, "next", vec![it, var_ref])
            };
            let body = fc.to_node(body)?;
            fc.node(e, While { condition, body })
          };
          let nodes = vec![let_it_node, let_loop_node, while_node];
          Ok(fc.node(e, Block(nodes)))  
        })
      })?;
      return Ok(n);
    }
    error(e, "malformed for expression")
  }

}
