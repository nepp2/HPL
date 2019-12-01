
use crate::error::{Error, error, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

use std::collections::HashMap;

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "__top_level";

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LabelId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(u64);

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TypeKind {
  Struct, Union
}

#[derive(Debug, Clone)]
pub struct Symbol {
  pub id : SymbolId,
  pub name : RefStr,
  pub loc : TextLocation,
}

#[derive(Debug)]
pub enum FunctionNode {
  Value(NodeId),
  Name(Symbol),
}

/// TODO: This is a messy way of supporting REPL functionality.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum GlobalType { Normal, CBind }

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global(GlobalType) }

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableInitialise{ name: Symbol, type_tag: Option<Box<Expr>>, value: NodeId, var_scope : VarScope },
  Assignment{ assignee: NodeId , value: NodeId },
  IfThen{ condition: NodeId, then_branch: NodeId },
  IfThenElse{ condition: NodeId, then_branch: NodeId, else_branch: NodeId },
  Block(Vec<NodeId>),
  Quote(Box<Expr>),
  Reference { name: RefStr, refers_to: Option<SymbolId> },
  FunctionDefinition{ name: RefStr, args: Vec<(Symbol, Option<Box<Expr>>)>, return_tag: Option<Box<Expr>>, body: NodeId },
  CBind { name: RefStr, type_tag : Box<Expr> },
  TypeDefinition{ name: RefStr, kind : TypeKind, fields: Vec<(Symbol, Option<Box<Expr>>)> },
  TypeConstructor{ name: RefStr, field_values: Vec<(Option<Symbol>, NodeId)> },
  FieldAccess{ container: NodeId, field: Symbol },
  ArrayLiteral(Vec<NodeId>),
  FunctionCall{ function: FunctionNode, args: Vec<NodeId> },
  While{ condition: NodeId, body: NodeId },
  Convert{ from_value: NodeId, into_type: Box<Expr> },
  SizeOf{ type_tag: Box<Expr> },

  Label{ label: LabelId, body: NodeId },
  BreakToLabel{ label: LabelId, return_value: Option<NodeId> },
}

impl Content {
  pub fn node_value_type(&self) -> NodeValueType {
    match self {
      FieldAccess{..} | Reference{..} |
      Literal(_) | Quote(_)
        => NodeValueType::Ref,
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
  Ref,
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

  symbols : HashMap<SymbolId, Symbol>,

  cache: &'l StringCache,
}

pub struct FunctionConverter<'l, 'lt> {
  t : &'l mut NodeConverter<'lt>,
  is_top_level : bool,
  labels_in_scope : Vec<LabelId>,
  block_scope : Vec<Vec<Symbol>>,
}

pub struct Nodes {
  pub nodes : HashMap<NodeId, Node>,
  pub symbols : HashMap<SymbolId, Symbol>,
  pub root : NodeId,
}

impl Nodes {
  pub fn node(&self, id : NodeId) -> &Node {
    self.nodes.get(&id).unwrap()
  }

  pub fn symbol(&self, id : SymbolId) -> &Symbol {
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
  fn node(&mut self, expr : &Expr, content : Content) -> NodeId {
    let id = self.uid_generator.next().into();
    let n = Node { id, content, loc: expr.loc };
    self.nodes.insert(id, n);
    id
  }

  fn symbol<Loc : Into<TextLocation>>(&mut self, name : &str, loc : Loc) -> Symbol {
    let name = self.cache.get(name);
    let id = SymbolId(self.uid_generator.next());
    let s = Symbol { id, name, loc: loc.into() };
    self.symbols.insert(id, s.clone());
    s
  }
}

impl <'l, 'lt> FunctionConverter<'l, 'lt> {

  pub fn new(t : &'l mut NodeConverter<'lt>, is_top_level : bool, args : Vec<Symbol>)
   -> FunctionConverter<'l, 'lt>
  {
    FunctionConverter { t, is_top_level, labels_in_scope : vec![], block_scope: vec![args] }
  }

  fn add_var_to_scope(&mut self, var : Symbol) {
    let scope = self.block_scope.last_mut().unwrap();
    scope.push(var);
  }

  fn find_var(&self, name : &str) -> Option<&Symbol> {
    for var in self.block_scope.iter().flat_map(|i| i.iter()).rev() {
      if name == var.name.as_ref() { return Some(var) }
    }
    None
  }

  fn expr_to_symbol(&mut self, e : &Expr) -> Result<Symbol, Error> {
    let name = e.unwrap_symbol()?;
    Ok(self.t.symbol(name, e.loc))
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(Symbol, Option<Box<Expr>>), Error> {
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
      let loc_name = self.cached("text_location");
      let marker_name = self.cached("text_marker");
      for n in template_args.into_iter() {
        let loc = self.loc_struct(expr, loc_name.clone(), marker_name.clone());
        let sym = self.t.symbol("sym", expr);
        let expr_val = self.function_call(expr, sym, vec![n, loc]);
        let to_ref = self.t.symbol("&", expr);
        let arg = self.function_call(expr, to_ref, vec![expr_val]);
        coerced_args.push(arg);
      }
      let array_literal = self.array_literal(expr, coerced_args);
      let template_quote = self.t.symbol("template_quote", expr);
      Ok(self.function_call(expr, template_quote, vec![main_quote, array_literal]))
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
    let name = self.cached(name_expr.unwrap_symbol()?);
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
      .collect::<Result<Vec<(Option<Symbol>, NodeId)>, Error>>()?;
    let c = TypeConstructor{ name, field_values };
    Ok(self.node(expr, c))
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
        let function = if let Some(name) = function_expr.try_symbol() {
          if let Some(var) = self.find_var(name) {
            let name = self.cached(name);
            let id = var.id;
            FunctionNode::Value(self.node(function_expr, Reference{ name, refers_to: Some(id) }))
          }
          else {
            FunctionNode::Name(self.expr_to_symbol(function_expr)?)
          }
        }
        else {
          FunctionNode::Value(self.to_node(function_expr)?)
        };
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
        let label = LabelId(self.t.uid_generator.next());
        // Add label to scope in case the loop breaks
        self.labels_in_scope.push(label);
        let condition = self.to_node(condition_expr)?;
        let body = self.to_node(body_expr)?;
        let while_node = self.node(expr, While{ condition, body });
        let labelled_while = self.node(expr, Label{ label, body: while_node });
        // Remove label
        self.labels_in_scope.pop();
        Ok(labelled_while)
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
        self.block_scope.push(vec![]);
        let nodes = exprs.iter().map(|e| self.to_node(e)).collect::<Result<Vec<NodeId>, Error>>()?;
        self.block_scope.pop();
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
        if let [name, args_expr, function_body] = exprs {
          let name = self.cached(name.unwrap_symbol()?);
          let args =
            args_expr.children().iter()
            .map(|e| self.typed_symbol(e))
            .collect::<Result<Vec<_>, Error>>()?;
          let arg_symbols =
            args.iter().map(|(s, _)| s.clone()).collect();
          let mut function_checker = FunctionConverter::new(self.t, false, arg_symbols);
          let body = function_checker.to_function_body(function_body)?;
          return Ok(self.node(expr, FunctionDefinition{name, args, return_tag: None, body}));
        }
        error(expr, "malformed function definition")
      }
      ("union", [name, fields_expr]) => {
        let name = self.cached(name.unwrap_symbol()?);
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        Ok(self.node(expr, TypeDefinition{name, kind: TypeKind::Union, fields}))
      }
      ("struct", [name, fields_expr]) => {
        let name = self.cached(name.unwrap_symbol()?);
        let fields =
          fields_expr.children().iter()
          .map(|e| self.typed_symbol(e))
          .collect::<Result<Vec<_>, Error>>()?;
        Ok(self.node(expr, TypeDefinition{name, kind: TypeKind::Struct, fields}))
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
          let function = FunctionNode::Name(self.t.symbol("Index", expr));
          let c = Content::FunctionCall{ function, args: vec![container, index] };
          return Ok(self.node(expr, c));
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
          return Ok(self.node(expr, Reference{ name, refers_to: Some(id) }));
        }
        return Ok(self.node(expr, Reference{ name, refers_to: None}));
      }
      ExprContent::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(self.node(expr, Literal(v)))
      }
      ExprContent::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(self.node(expr, Literal(v)))
      },
      ExprContent::LiteralUnit => {
        Ok(self.node(expr, Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }

  fn top_level_expression(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    let c = Content::FunctionDefinition{
      name: self.cached(TOP_LEVEL_FUNCTION_NAME),
      body: self.to_function_body(expr)?,
      args: vec![],
      return_tag: None,
    };
    let f = self.node(expr, c);
    Ok(f)
  }

  fn to_function_body(&mut self, expr : &Expr) -> Result<NodeId, Error> {
    if self.labels_in_scope.len() != 0 {
      panic!("labels_in_scope in invalid state");
    }
    let label = LabelId(self.t.uid_generator.next());
    self.labels_in_scope.push(label);
    let body = self.to_node(expr)?;
    self.labels_in_scope.pop();
    let c = Label{ label, body };
    Ok(self.node(expr, c))
  }

  fn loc_struct(&mut self, expr : &Expr, loc_name : RefStr, marker_name : RefStr) -> NodeId {
    let start = {
      let col = self.u64_literal(expr, expr.loc.start.col as u64);
      let line = self.u64_literal(expr, expr.loc.start.line as u64);
      self.type_constructor(expr, marker_name.clone(), vec![col, line])
    };
    let end = {
      let col = self.u64_literal(expr, expr.loc.end.col as u64);
      let line = self.u64_literal(expr, expr.loc.end.line as u64);
      self.type_constructor(expr, marker_name, vec![col, line])
    };
    self.type_constructor(expr, loc_name, vec![start, end])
  }

  fn let_var(&mut self, expr : &Expr, name : RefStr, val : NodeId) -> NodeId {
    let name = self.t.symbol(&name, expr.loc);
    self.node(expr, VariableInitialise{ name, type_tag: None, value: val, var_scope : VarScope::Local })
  }

  fn block(&mut self, expr : &Expr, args : Vec<NodeId>) -> NodeId {
    self.node(expr, Block(args))
  }

  fn u64_literal(&mut self, expr : &Expr, i : u64) -> NodeId {
    self.node(expr, Literal(Val::U64(i)))
  }

  fn array_literal(&mut self, expr : &Expr, args : Vec<NodeId>) -> NodeId {
    let args = ArrayLiteral(args);
    self.node(expr, args)
  }

  fn function_call(&mut self, expr : &Expr, function : Symbol, args : Vec<NodeId>) -> NodeId {
    let function = FunctionNode::Name(function);
    let function_call = FunctionCall{ function, args };
    self.node(expr, function_call)
  }

  fn type_constructor(&mut self, expr : &Expr, name : RefStr, field_values : Vec<NodeId>) -> NodeId {
    let field_values = field_values.into_iter().map(|a| (None, a)).collect();
    self.node(expr, TypeConstructor{ name, field_values })
  }
}

// TODO: maybe implement for loop:
//
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
//       let range_node = self.to_node(range)?;
//       let for_block = block(expr, vec![
//         let_var(expr, range_var.clone(), range_node),
//         let_var(expr, end_var.clone(), field_access(expr, range_var.clone(), "end")),
//         let_var(expr, loop_var.clone(), field_access(expr, range_var.clone(), "start")),
//         self.node(expr, Type::Void, While((
//           intrinsic("<", vec![loop_var, end_var]),
//           block(expr, vec![
//             self.to_node(body_expr)?,
//             assignment(loop_var, intrinsic("+", vec![loop_var, literal_int(1)])),
//           ])
//         )))
//       ]);
//       return Ok(for_block);
//     }
//   }
//   error(expr, "malformed for expression")
// }
