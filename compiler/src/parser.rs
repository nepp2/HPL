use crate::lexer::{Token, TokenType};
use crate::expr::{StringCache, Expr, ExprContent, RefStr};
use crate::error::{Error, ErrorContent, TextLocation, TextMarker, error};
use std::collections::{HashSet, HashMap};
use std::str::FromStr;

static EXPECTED_TOKEN_ERROR : &str = "Expected token. Found nothing.";

struct ParseConfig {
  next_precedence : i32,
  paren_pairs : HashMap<RefStr, RefStr>,
  paren_terminators : HashSet<RefStr>,
  expression_separators : HashMap<RefStr, i32>,
  prefix_precedence : HashMap<RefStr, i32>,
  infix_precedence : HashMap<RefStr, i32>,
  special_operators : HashSet<RefStr>,
}

impl ParseConfig {
  fn new(special_operators : &[&str], paren_pairs : &[(&str, &str)]) -> Self {
    let mut c = ParseConfig {
      next_precedence: 1,
      paren_pairs: HashMap::new(),
      paren_terminators: HashSet::new(),
      expression_separators: HashMap::new(),
      prefix_precedence: HashMap::new(),
      infix_precedence: HashMap::new(),
      special_operators: special_operators.iter().map(|&s| s.into()).collect(),
    };
    for &(a, b) in paren_pairs {
      c.paren_pairs.insert(a.into(), b.into());
      c.paren_terminators.insert(b.into());
    }
    c
  }

  fn separator(&mut self, sep : &str) {
    self.expression_separators.insert(sep.into(), self.next_precedence);
    self.next_precedence += 1;
  }

  fn infix_prefix(&mut self, infix : &[&str], prefix : &[&str]) {
    for &op in infix {
      self.infix_precedence.insert(op.into(), self.next_precedence);
    }
    for &op in prefix {
      self.prefix_precedence.insert(op.into(), self.next_precedence);
    }
    self.next_precedence += 1;
  }

  fn infix(&mut self, ops : &[&str]) {
    self.infix_prefix(ops, &[]);
  }

  fn prefix(&mut self, ops : &[&str]) {
    self.infix_prefix(&[], ops);
  }
}

/// Precedence level
struct PL { infix : &'static [&'static str], prefix : &'static [&'static str] }

fn parse_config() -> ParseConfig {
  let special_operators = &["=", ".", "||", "&&", "as", ":", "#"];
  let paren_pairs = &[
    ("(", ")"),
    ("{", "}"),
    ("[", "]"),
  ];
  let mut c = ParseConfig::new(special_operators, paren_pairs);
  c.separator(";");
  c.separator(",");
  c.prefix(&["#keyword"]);
  c.infix(&["=", "+="]);
  c.infix(&[":"]);
  c.infix(&["as"]);
  c.infix(&["&&", "||"]);
  c.infix(&[">", "<", ">=", "<=", "==", "!="]);
  c.infix_prefix(&["+", "-"], &["-"]);
  c.infix(&["*", "/", "%"]);
  c.infix_prefix(&["=>"], &["!", "ref", "deref",]);
  c.prefix(&["#", "$"]);
  c.infix(&["(", "["]);
  c.infix(&["."]);
  c
}

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct ParseState<'l> {
  tokens : Vec<Token>,
  pos : usize,
  config : &'l ParseConfig,
  cache : &'l StringCache,
}

use TokenType::*;

impl <'l> ParseState<'l> {

  fn new(tokens : Vec<Token>, config : &'l ParseConfig, cache : &'l StringCache) -> ParseState<'l> {
    ParseState { tokens, pos: 0, config, cache }
  }

  fn has_tokens(&self) -> bool {
    self.pos < self.tokens.len()
  }

  fn peek(&self) -> Result<&Token, Error> {
    if self.has_tokens() {
      Ok(&self.tokens[self.pos])
    }
    else if self.pos > 0 {
      let m = self.tokens[self.pos-1].loc.end;
      error(TextLocation::new(m, m), EXPECTED_TOKEN_ERROR)
    }
    else {
      error(TextLocation::zero(), EXPECTED_TOKEN_ERROR)
    }
  }

  fn peek_marker(&self) -> TextMarker {
    if self.has_tokens() {
      self.tokens[self.pos].loc.start
    }
    else if self.tokens.len() == 0 {
      TextMarker { col: 0, line: 0 }
    }
    else {
      self.tokens[self.pos-1].loc.end
    }
  }

  fn loc(&self, start : TextMarker) -> TextLocation {
    if self.pos > 0 {
      let end = self.tokens[self.pos-1].loc.end;
      TextLocation::new(start, end)
    }
    else {
      TextLocation::zero()
    }
  }

  fn peek_ahead(&self, offset : usize) -> Option<&Token> {
    let i = self.pos + offset;
    if i < self.tokens.len() {
      Some(&self.tokens[i])
    }
    else {
      None
    }
  }

  fn pop_type(&mut self, token_type : TokenType) -> Result<&Token, Error> {
    self.expect_type(token_type)?;
    Ok(&self.tokens[self.pos-1])
  }

  fn skip(&mut self) {
    self.pos += 1;
  }

  fn accept(&mut self, string : &str) -> bool {
    let accept = {
      if let Ok(t) = self.peek() {
        t.symbol.as_ref() == string
      }
      else { false }
    };
    if accept { self.skip() }
    accept
  }

  fn expect(&mut self, string : &str) -> Result<(), Error> {
    let t = self.peek()?;
    if t.symbol.as_ref() != string {
      return error(t.loc, format!("Expected token '{}', found token '{}'", string, t.symbol));
    }
    self.skip();
    Ok(())
  }

  /// Returns marker for start of the token if successful
  fn expect_type(&mut self, token_type : TokenType) -> Result<(), Error> {
    {
      let t = self.peek()?;
      if t.token_type != token_type {
        return error(t.loc, format!("Expected token of type '{:?}', found token type '{:?}'", token_type, t.token_type));
      }
    }
    self.skip();
    Ok(())
  }

  fn add_expr(&mut self, content : ExprContent, loc : TextLocation) -> Expr {
    Expr::new(content, loc)
  }

  fn add_leaf(&mut self, content : ExprContent, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    self.add_expr(content, loc)
  }

  fn add_list<S : Into<String>>(&mut self, s : S, list : Vec<Expr>, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let content = ExprContent::list(s.into(), list);
    self.add_expr(content, loc)
  }

  fn add_symbol<S : Into<String>>(&mut self, s : S, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    let content = ExprContent::symbol(s.into());
    self.add_expr(content, loc)
  }
}

/// This expression parser is vaguely based on some blogs about pratt parsing.
fn pratt_parse(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let mut expr = parse_prefix(ps)?;
  while ps.has_tokens() {
    let t = ps.peek()?;
    // TODO remove: println!("expr parsed: {}, precedence: {}, t: {}", expr, precedence, t.symbol);
    if ps.config.paren_terminators.contains(&t.symbol) {
      // TODO remove: println!("bumped into a {}", t.symbol);
      break;
    }
    // New lines are imlicitly semi-colons (except after an infix operator)
    else if expr.loc.end.line != t.loc.start.line {
      let next_precedence = *ps.config.expression_separators.get(";").unwrap();
      if next_precedence > precedence {
        expr = parse_list(ps, vec![expr], ";", "block".into())?;
      }
      else {
        break;
      }
    }
    // Separators
    else if let Some(&next_precedence) = ps.config.expression_separators.get(&t.symbol) {
      if next_precedence > precedence {
        let separator = t.symbol.clone();
        ps.pop_type(TokenType::Symbol)?;
        let tag = match separator.as_ref() {
          ";" => "block", "," => "tuple", _ => panic!(),
        };
        expr = parse_list(ps, vec![expr], separator.as_ref(), tag.into())?;
      }
      else {
        break;
      }
    }
    // Infix operators
    else if let Some(&next_precedence) = ps.config.infix_precedence.get(&t.symbol) {
      if next_precedence > precedence {
        // Parens
        if ps.config.paren_pairs.contains_key(&t.symbol) {
          expr = parse_paren_infix(ps, expr, None)?;
        }
        // Normal infix
        else {
          expr = parse_infix(ps, expr, next_precedence)?;
        }
      }
      else {
        break;
      }
    }
    else {
      break;
    }
  }
  Ok(expr)
}

fn parse_paren_infix(ps : &mut ParseState, left_expr : Expr, first_arg : Option<Expr>) -> Result<Expr, Error> {
  let start = left_expr.loc.start;
  let t = ps.peek()?;
  let start_paren = t.symbol.clone();
  let end_paren = ps.config.paren_pairs.get(&start_paren).unwrap().clone();
  let operation = match start_paren.as_ref() {
    "(" => "call",
    "[" => "index",
    _ => return error(t.loc, "unexpected syntax"),
  };
  ps.expect(&start_paren)?;
  let mut list = vec![left_expr];
  if let Some(first_arg) = first_arg {
    list.push(first_arg);
  }
  parse_into_list(ps, &mut list, ",")?;
  ps.expect(&end_paren)?;
  Ok(ps.add_list(operation, list, start))
}

fn parse_prefix(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let t = ps.peek()?;
  // if the next token is a prefix operator
  if let Some(new_precedence) = ps.config.prefix_precedence.get(t.symbol.as_ref()) {
    let t = ps.peek()?;
    if ps.config.special_operators.contains(&t.symbol) {
      let operator = t.symbol.as_ref().to_string();
      ps.expect_type(TokenType::Symbol)?;
      let expr = pratt_parse(ps, *new_precedence)?;
      Ok(ps.add_list(operator, vec![expr], start))
    }
    else {
      let operator = parse_simple_string(ps)?;
      let expr = pratt_parse(ps, *new_precedence)?;
      Ok(ps.add_list("call", vec![operator, expr], start))
    }
  }
  // else assume it's an expression term
  else {
    parse_expression_term(ps)
  }
}

fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
  let infix_start = left_expr.loc.start;
  let t = ps.peek()?;
  if t.symbol.as_ref() == "." {
    // special handling for method call syntax
    ps.expect_type(TokenType::Symbol)?;
    let right_expr = pratt_parse(ps, precedence)?;
    if ps.has_tokens() && ps.peek()?.symbol.as_ref() == "(" {
      parse_paren_infix(ps, right_expr, Some(left_expr))
    }
    else {
      Ok(ps.add_list(".", vec![left_expr, right_expr], infix_start))
    }
  }
  else if ps.config.special_operators.contains(&t.symbol) {
    let operator = t.symbol.as_ref().to_string();
    ps.expect_type(TokenType::Symbol)?;
    let list = vec![left_expr, pratt_parse(ps, precedence)?];
    Ok(ps.add_list(operator, list, infix_start))
  }
  else {
    let operator = parse_simple_string(ps)?;
    let list = vec![operator, left_expr, pratt_parse(ps, precedence)?];
    Ok(ps.add_list("call", list, infix_start))
  }
}

fn parse_into_list(ps : &mut ParseState, list : &mut Vec<Expr>, separator : &str) -> Result<(), Error> {
  let &precedence = ps.config.expression_separators.get(separator).unwrap();
  let is_semicolon = separator == ";";
  while ps.has_tokens() {
    let t = ps.peek()?;
    if ps.config.paren_terminators.contains(&t.symbol) {
      break;
    }
    list.push(pratt_parse(ps, precedence)?);
    if !ps.has_tokens() {
      break;
    }
    let t = ps.peek()?;
    let implicit_separator = is_semicolon && {
      let previous_line = list.last().unwrap().loc.end.line;
      let next_line = t.loc.start.line;
      previous_line != next_line
    };
    if !(implicit_separator || ps.accept(separator)) {
      break;
    }
  }
  Ok(())
}

fn parse_list(ps : &mut ParseState, mut list : Vec<Expr>, separator : &str, tag : String) -> Result<Expr, Error> {
  let start = list.first().map(|e| e.loc.start).unwrap_or_else(|| ps.peek_marker());
  parse_into_list(ps, &mut list, separator)?;
  Ok(ps.add_list(tag, list, start))
}

fn parse_block_in_braces(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect("{")?;
  let mut list = vec![];
  parse_into_list(ps, &mut list, ";")?;
  ps.expect("}")?;
  Ok(ps.add_list("block", list, start))
}

fn parse_new_scope(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let e = pratt_parse(ps, precedence)?;
  if let Some(("block", _)) = e.try_construct() {
    Ok(e)
  }
  else {
    Ok(ps.add_list("block", vec![e], start))
  }
}

fn parse_everything(ps : &mut ParseState) -> Result<Expr, Error> {
  pratt_parse(ps, 0)
}

fn parse_literal<T : FromStr>(ps : &mut ParseState) -> Result<T, Error> {
  let t = ps.peek()?;
  if let Ok(v) = T::from_str(&t.symbol) {
    ps.skip();
    Ok(v)
  }
  else {
    error(t.loc, format!("Failed to parse literal from '{}'", t.symbol))
  }
}

fn parse_simple_string(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let s : String = ps.pop_type(Symbol)?.symbol.as_ref().into();
  Ok(ps.add_symbol(s, start))
}

fn try_parse_keyword_term(ps : &mut ParseState) -> Result<Option<Expr>, Error> {
  let t = ps.peek()?;
  let &kp = ps.config.prefix_precedence.get("#keyword").unwrap();
  let start = ps.peek_marker();
  let expr = match t.symbol.as_ref() {
    "if" => {
      ps.pop_type(TokenType::Symbol)?;
      let cond = pratt_parse(ps, kp)?;
      ps.accept("then");
      let then_e = parse_new_scope(ps, kp)?;
      if ps.accept("else") {
        let else_e = parse_new_scope(ps, kp)?;
        ps.add_list("if", vec![cond, then_e, else_e], start)
      }
      else {
        ps.add_list("if", vec![cond, then_e], start)
      }
    }
    "while" => {
      ps.pop_type(TokenType::Symbol)?;
      let cond = pratt_parse(ps, kp)?;
      let body = parse_block_in_braces(ps)?;
      ps.add_list("while", vec![cond, body], start)
    }
    "for" => {
      ps.pop_type(TokenType::Symbol)?;
      let cond = pratt_parse(ps, kp)?;
      let body = parse_block_in_braces(ps)?;
      ps.add_list("for", vec![cond, body], start)
    }
    "struct" => {
      ps.pop_type(TokenType::Symbol)?;
      let name = parse_simple_string(ps)?;
      let fields = parse_block_in_braces(ps)?;
      ps.add_list("struct", vec![name, fields], start)
    }
    "union" => {
      ps.pop_type(TokenType::Symbol)?;
      let name = parse_simple_string(ps)?;
      let fields = parse_block_in_braces(ps)?;
      ps.add_list("union", vec![name, fields], start)
    }
    "cbind" => {
      ps.pop_type(TokenType::Symbol)?;
      let typed_symbol = pratt_parse(ps, kp)?;
      ps.add_list("cbind", vec![typed_symbol], start)
    }
    "fun" => {
      ps.pop_type(TokenType::Symbol)?;
      let mut es = vec![];
      let is_full_definition = ps.peek()?.symbol.as_ref() != "(";
      if is_full_definition {
        // Parse name
        es.push(parse_simple_string(ps)?);
      }
      // arguments
      ps.expect("(")?;
      es.push(parse_list(ps, vec![], ",", "args".into())?);
      ps.expect(")")?;
      // return type
      if ps.accept("=>") {
        es.push(pratt_parse(ps, kp)?);
      }
      if is_full_definition {
        // body
        es.push(parse_block_in_braces(ps)?);
      }
      ps.add_list("fun", es, start)
    }
    "let" => {
      ps.pop_type(TokenType::Symbol)?;
      let definition = pratt_parse(ps, kp)?;
      ps.add_list("let", vec![definition], start)
    }
    "return" => {
      let start = ps.peek_marker();
      ps.expect("return")?;
      let mut list = vec![];
      if ps.has_tokens() {
        let t = ps.peek()?.symbol.as_ref();
        if !ps.config.paren_terminators.contains(t) || !ps.config.expression_separators.contains_key(t) {
          list.push(pratt_parse(ps, kp)?);
        }
      }
      ps.add_list("return", list, start)
    }
    _ => return Ok(None),
  };
  Ok(Some(expr))
}

fn parse_expression_term(ps : &mut ParseState) -> Result<Expr, Error> {
  let t = ps.peek()?;
  match ps.peek()?.token_type {
    Symbol => {
      if let Some(close_paren) = ps.config.paren_pairs.get(&t.symbol) {
        // Parens
        let start = ps.peek_marker();
        let paren : String = t.symbol.as_ref().into();
        ps.expect_type(Symbol)?;
        match paren.as_str() {
          "[" => {
            let e = parse_list(ps, vec![], ",", "array".into())?;
            ps.expect(close_paren)?;
            Ok(e)
          }
          "{" => {
            let e = parse_list(ps, vec![], ";", "block".into())?;
            ps.expect(close_paren)?;
            Ok(e)
          }
          "(" => {
            if ps.accept(close_paren) {
              Ok(ps.add_leaf(ExprContent::LiteralUnit, start))
            }
            else {
              let e = parse_everything(ps)?;
              ps.expect(close_paren)?;
              Ok(e)
            }
          }
          _ => panic!(),
        }
      }
      else {
        // bools
        let bool_val = match t.symbol.as_ref() {
          "true" => Some(true),
          "false" => Some(false),
          _ => None,
        };
        if let Some(b) = bool_val {
          let start = ps.peek_marker();
          ps.pop_type(TokenType::Symbol)?;
          let b = ExprContent::LiteralBool(b);
          Ok(ps.add_leaf(b, start))
        }
          // keyword terms (if, while, etc)
        else if let Some(e) = try_parse_keyword_term(ps)? {
          Ok(e)
        }
        else {
          parse_simple_string(ps)
        }
      }
    }
    StringLiteral => {
      let start = ps.peek_marker();
      let s = {
        let t = ps.pop_type(StringLiteral)?;
        ExprContent::literal_string(t.symbol.as_ref().into())
      };
      Ok(ps.add_leaf(s, start))
    }
    FloatLiteral => {
      let start = ps.peek_marker();
      let f = ExprContent::LiteralFloat(parse_literal(ps)?);
      Ok(ps.add_leaf(f, start))
    }
    IntLiteral => {
      let start = ps.peek_marker();
      let i = ExprContent::LiteralInt(parse_literal(ps)?);
      Ok(ps.add_leaf(i, start))
    }
  }
}

fn parse_top_level(ps : &mut ParseState) -> Result<Expr, Error> {
  parse_list(ps, vec![], ";", "block".into())
}

pub fn parse(tokens : Vec<Token>, symbols : &StringCache) -> Result<Expr, Error> {
  let config = parse_config();
  let mut ps = ParseState::new(tokens, &config, symbols);
  let e = parse_top_level(&mut ps)?;
  if ps.has_tokens() {
    let t = ps.peek()?;
    return error(t.loc, format!("Unexpected token '{}' of type '{:?}'", t.symbol, t.token_type));
  }
  return Ok(e);
}

pub enum ReplParseResult {
  Complete(Expr),
  Incomplete,
}

pub fn repl_parse(tokens : Vec<Token>, symbols : &mut StringCache) -> Result<ReplParseResult, Error> {
  use ReplParseResult::*;
  let config = parse_config();
  let mut ps = ParseState::new(tokens, &config, symbols);
  match parse_top_level(&mut ps) {
    Ok(e) => {
      return Ok(Complete(e));
    }
    Err(e) => {
      if let ErrorContent::Message(m) = &e.message {
        if m.as_str() == EXPECTED_TOKEN_ERROR {
          return Ok(Incomplete);
        }
      }
      return Err(e);
    }
  }
}
