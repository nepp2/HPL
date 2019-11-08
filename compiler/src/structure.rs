
use crate::error::{Error, error, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

use std::collections::HashMap;

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
pub enum Content {
  Literal(Val),
  LocalInitialise{ name: SymbolId, type_tag: Option<Box<Expr>>, value: NodeId },
  GlobalInitialise{ name: SymbolId, type_tag: Option<Box<Expr>>, value: NodeId },
  Assignment{ assignee: NodeId , value: NodeId },
  IfThen{ condition: NodeId, then_branch: NodeId },
  IfThenElse{ condition: NodeId, then_branch: NodeId, else_branch: NodeId },
  Block(Vec<NodeId>),
  Quote(Box<Expr>),
  Reference { name: RefStr, refers_to: Option<SymbolId> },
  FunctionDefinition{ name: RefStr, args: Vec<(SymbolId, Option<Box<Expr>>)>, return_tag: Option<Box<Expr>>, body: NodeId },
  CBind { name: RefStr, type_tag : Box<Expr> },
  TypeDefinition{ name: RefStr, kind : TypeKind, fields: Vec<(SymbolId, Option<Box<Expr>>)> },
  TypeConstructor{ name: RefStr, field_values: Vec<(Option<SymbolId>, NodeId)> },
  FieldAccess{ container: NodeId, field: RefStr },
  Index{ container: NodeId, index: NodeId },
  ArrayLiteral(Vec<NodeId>),
  FunctionCall{ function: NodeId, args: Vec<NodeId> },
  While{ condition: NodeId, body: NodeId },
  Convert{ from_value: NodeId, into_type: Box<Expr> },
  SizeOf{ type_tag: Box<Expr> },

  Label{ label: LabelId, body: NodeId },
  BreakToLabel{ label: LabelId, return_value: Option<NodeId> },
}

use Content::*;

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
  let mut fc = FunctionConverter::new(&mut nc, true);
  let root = fc.to_node(expr)?;
  Ok(Nodes{ root, nodes: nc.nodes, symbols: nc.symbols })
}

impl <'l> NodeConverter<'l> {
  fn node(&mut self, expr : &Expr, content : Content) -> NodeId {
    let id = self.uid_generator.next().into();
    let n = Node { id, content, loc: expr.loc };
    self.nodes.insert(id, n);
    id
  }
}

impl <'l, 'lt> FunctionConverter<'l, 'lt> {

  pub fn new(t : &'l mut NodeConverter<'lt>, is_top_level : bool) -> FunctionConverter<'l, 'lt> {
    FunctionConverter { t, is_top_level, labels_in_scope : vec![], block_scope: vec![] }
  }

  fn add_var_to_scope(&mut self, var : &Symbol) {
    let scope = self.block_scope.last_mut().unwrap();
    scope.push(var.clone());
  }

  fn find_var(&mut self, name : &str) -> Option<&Symbol> {
    for var in self.block_scope.iter().flat_map(|i| i.iter()).rev() {
      if name == var.name.as_ref() { return Some(var) }
    }
    None
  }

  fn symbol(&mut self, name : &str, loc : TextLocation) -> SymbolId {
    let name = self.cached(name);
    let id = SymbolId(self.t.uid_generator.next());
    self.t.symbols.insert(id, Symbol { id, name, loc });
    id
  }

  fn expr_to_symbol(&mut self, e : &Expr) -> Result<SymbolId, Error> {
    let name = e.unwrap_symbol()?;
    Ok(self.symbol(name, e.loc))
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(SymbolId, Option<Box<Expr>>), Error> {
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
        let expr_val = self.function_call(expr, self.cached("sym"), vec![n, loc]);
        let arg = self.function_call(expr, self.cached("&"), vec![expr_val]);
        coerced_args.push(arg);
      }
      let array_literal = self.array_literal(expr, coerced_args);
      Ok(self.function_call(expr, self.cached("template_quote"), vec![main_quote, array_literal]))
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
      .collect::<Result<Vec<(Option<SymbolId>, NodeId)>, Error>>()?;
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
        let function = self.to_node(function_expr)?;
        let content = FunctionCall{ function, args };
        return Ok(self.node(expr, content));
      }
      ("as", [from_value, into_type]) => {
        let from_value = self.to_node(from_value)?;
        let into_type = into_type.clone().into();
        Ok(self.node(expr, Convert{ from_value, into_type }))
      }
      ("let", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let name = self.expr_to_symbol(name_expr)?;
          let value = self.to_node(value_expr)?;
          let c = if self.is_top_level && self.block_scope.len() == 1 {
            GlobalInitialise{ name, type_tag : None, value }
          }
          else {
            LocalInitialise{ name, type_tag: None, value }
          };
          return Ok(self.node(expr, c));
        }
        error(expr, "malformed let expression")
      }
      ("#", [quoted_expr]) => {
        self.quote_to_node(expr, quoted_expr)
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
          let mut function_checker = FunctionConverter::new(self.t, false);
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
        Ok(self.node(expr, TypeDefinition{name, kind: TypeKind::Union, fields}))
      }
      (".", [container_expr, field_expr]) => {
        let container = self.to_node(container_expr)?;
        let field = self.cached(field_expr.unwrap_symbol()?);
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
          return Ok(self.node(expr, Index{ container, index }));
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
    let name = self.symbol(&name, expr.loc);
    self.node(expr, LocalInitialise{ name, type_tag: None, value: val })
  }

  fn field_access(&mut self, expr : &Expr, container : NodeId, field : RefStr) -> NodeId {
    self.node(expr, FieldAccess{ container: container, field })
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

  fn function_call(&mut self, expr : &Expr, function : RefStr, args : Vec<NodeId>) -> NodeId {
    let function = self.node(expr, Reference{ name: function, refers_to: None });
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
