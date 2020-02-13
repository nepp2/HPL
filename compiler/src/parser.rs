use crate::lexer::{Token, TokenType};
use crate::expr::{StringCache, Expr, ExprContent, RefStr};
use crate::error::{Error, TextLocation, TextMarker, error};
use std::collections::{HashSet, HashMap};
use std::str::FromStr;

pub static EXPECTED_TOKEN_ERROR : &str = "Expected token. Found nothing.";

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

fn parse_config() -> ParseConfig {
  let special_operators = &[
    "=", ".", "as", "in", ":", "#", "$"
  ];
  let paren_pairs = &[
    ("(", ")"),
    ("{", "}"),
    ("[", "]"),
  ];
  let mut c = ParseConfig::new(special_operators, paren_pairs);
  c.separator(";");
  c.separator(",");
  c.prefix(&["#keyword"]);
  c.infix(&["=", "+=", "in"]);
  c.infix(&[":"]);
  c.infix(&["as"]);
  c.infix(&["&&", "||"]);
  c.infix(&[">", "<", ">=", "<=", "==", "!="]);
  c.infix(&["%"]);
  c.infix_prefix(&["+", "-"], &["-"]);
  c.infix(&["*", "/", "%"]);
  c.infix_prefix(&["=>"], &["!", "&", "*",]);
  c.infix(&["(", "["]);
  c.infix(&["."]);
  c.prefix(&["#", "$"]);
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

fn match_symbol(t : &Token, s : &str) -> bool {
  t.symbol().map(|sym| sym.as_ref() == s).unwrap_or(false)
}

fn get<'l, V>(m : &'l HashMap<RefStr, V>, k : Option<&RefStr>) -> Option<&'l V> {
  k.and_then(|k| m.get(k))
}

fn contains_key<'l, V>(m : &'l HashMap<RefStr, V>, k : Option<&RefStr>) -> bool {
  k.map(|k| m.contains_key(k)).unwrap_or(false)
}

fn contains<'l>(m : &'l HashSet<RefStr>, k : Option<&RefStr>) -> bool {
  k.map(|k| m.contains(k)).unwrap_or(false)
}

impl <'l> ParseState<'l> {

  fn new(tokens : Vec<Token>, config : &'l ParseConfig, cache : &'l StringCache) -> ParseState<'l> {
    ParseState { tokens, pos: 0, config, cache }
  }

  fn has_tokens(&self) -> bool {
    self.pos < self.tokens.len()
  }

  fn prev(&self) -> Option<&Token> {
    if self.pos > 0 {
      return Some(&self.tokens[self.pos-1]);
    }
    None
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

  fn peek_newline(&self) -> bool {
    if let Some(prev) = self.prev() {
      if let Ok(next) = self.peek() {
        return prev.loc.end.line != next.loc.start.line;
      }
    }
    false
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
        match_symbol(t, string)
      }
      else { false }
    };
    if accept { self.skip() }
    accept
  }

  fn expect(&mut self, string : &str) -> Result<(), Error> {
    let t = self.peek()?;
    if !match_symbol(t, string) {
      return error(t.loc, format!("Expected symbol '{}', found {}", string, t));
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
    if contains(&ps.config.paren_terminators, t.symbol()) {
      break;
    }
    // New lines are imlicitly semi-colons (except after an infix operator)
    else if ps.peek_newline() {
      let next_precedence = *ps.config.expression_separators.get(";").unwrap();
      if next_precedence > precedence {
        expr = parse_list(ps, vec![expr], ";", "block".into())?;
      }
      else {
        break;
      }
    }
    // Separators
    else if let Some(&next_precedence) = get(&ps.config.expression_separators, t.symbol()) {
      if next_precedence > precedence {
        let separator = t.symbol().unwrap().as_ref();
        let (tag, separator) = match separator {
          ";" => ("block", ";"),
          "," => ("tuple", ","),
          _ => panic!(),
        };
        ps.pop_type(TokenType::Symbol)?;
        expr = parse_list(ps, vec![expr], separator, tag.into())?;
      }
      else {
        break;
      }
    }
    // Infix operators
    else if let Some(&next_precedence) = get(&ps.config.infix_precedence, t.symbol()) {
      if next_precedence > precedence {
        // Parens
        if contains_key(&ps.config.paren_pairs, t.symbol()) {
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
  let (operation, start_paren) = match t.symbol().map(|s| s.as_ref()) {
    Some("(") => ("call", "("),
    Some("[") => ("index", "["),
    _ => return error(t.loc, "unexpected token"),
  };
  let end_paren = ps.config.paren_pairs.get(start_paren).unwrap().clone();
  ps.expect(start_paren)?;
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
  if let Some(new_precedence) = get(&ps.config.prefix_precedence, t.symbol()) {
    let t = ps.peek()?;
    if contains(&ps.config.special_operators, t.symbol()) {
      let operator = t.to_string();
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
  if match_symbol(t, ".") {
    // special handling for method call syntax
    ps.expect_type(TokenType::Symbol)?;
    let right_expr = pratt_parse(ps, precedence)?;
    if ps.has_tokens() && match_symbol(ps.peek()?, "(") {
      parse_paren_infix(ps, right_expr, Some(left_expr))
    }
    else {
      Ok(ps.add_list(".", vec![left_expr, right_expr], infix_start))
    }
  }
  else if contains(&ps.config.special_operators, t.symbol()) {
    let operator = t.to_string();
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
    if contains(&ps.config.paren_terminators, t.symbol()) {
      break;
    }
    list.push(pratt_parse(ps, precedence)?);
    if !ps.has_tokens() {
      break;
    }
    let implicit_separator = is_semicolon && ps.peek_newline();
    if !(implicit_separator || ps.accept(separator)) {
      break;
    }
  }
  Ok(())
}

fn peek_statement_terminated(ps : &ParseState) -> bool {
  if let Ok(t) = ps.peek() {
    let symbol = t.symbol();
    contains(&ps.config.paren_terminators, symbol) ||
      contains_key(&ps.config.expression_separators, symbol) ||
      ps.peek_newline()
  }
  else {
    true
  }
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
  let s = t.literal().unwrap().as_ref();
  if let Ok(v) = T::from_str(s) {
    ps.skip();
    Ok(v)
  }
  else {
    error(t.loc, format!("Failed to parse literal from '{}'", s))
  }
}

fn parse_simple_string(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let s = ps.pop_type(Symbol)?.to_string();
  Ok(ps.add_symbol(s, start))
}

fn try_parse_keyword_term(ps : &mut ParseState) -> Result<Option<Expr>, Error> {
  let t = ps.peek()?;
  let &kp = ps.config.prefix_precedence.get("#keyword").unwrap();
  let start = ps.peek_marker();
  let symbol = match t.symbol() {
    Some(s) => s.as_ref(), None => return Ok(None),
  };
  let expr = match symbol {
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
      let var_range = pratt_parse(ps, kp)?;
      let body = parse_block_in_braces(ps)?;
      ps.add_list("for", vec![var_range, body], start)
    }
    "struct" => {
      ps.pop_type(TokenType::Symbol)?;
      let name = pratt_parse(ps, kp)?;
      let fields = parse_block_in_braces(ps)?;
      ps.add_list("struct", vec![name, fields], start)
    }
    "union" => {
      ps.pop_type(TokenType::Symbol)?;
      let name = pratt_parse(ps, kp)?;
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
      let is_full_definition = !match_symbol(ps.peek()?, "(");
      if is_full_definition {
        // Parse name
        es.push(parse_prefix(ps)?);
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
        if ps.accept("with") {
          es.push(parse_list(ps, vec![], ",", "polytypes".into())?);
        }
        // body
        es.push(parse_block_in_braces(ps)?);
      }
      ps.add_list("fun", es, start)
    }
    "static" => {
      ps.pop_type(TokenType::Symbol)?;
      let definition = pratt_parse(ps, kp)?;
      ps.add_list("static", vec![definition], start)
    }
    "let" => {
      ps.pop_type(TokenType::Symbol)?;
      let definition = pratt_parse(ps, kp)?;
      ps.add_list("let", vec![definition], start)
    }
    "type" => {
      ps.pop_type(TokenType::Symbol)?;
      let definition = pratt_parse(ps, kp)?;
      ps.add_list("type", vec![definition], start)
    }
    "return" => {
      let start = ps.peek_marker();
      ps.expect("return")?;
      if peek_statement_terminated(ps) {
        ps.add_list("return", vec![], start)
      }
      else {
        let return_expr = pratt_parse(ps, kp)?;
        ps.add_list("return", vec![return_expr], start)
      }
    }
    _ => return Ok(None),
  };
  Ok(Some(expr))
}

fn parse_expression_term(ps : &mut ParseState) -> Result<Expr, Error> {
  let t = ps.peek()?;
  match ps.peek()?.token_type {
    Symbol => {
      if let Some(close_paren) = get(&ps.config.paren_pairs, t.symbol()) {
        // Parens
        let start = ps.peek_marker();
        let paren : String = t.to_string();
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
        let bool_val = t.symbol().and_then(|s| match s.as_ref() {
          "true" => Some(true),
          "false" => Some(false),
          _ => None,
        });
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
        ExprContent::literal_string(t.to_string())
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

pub fn parse(tokens : Vec<Token>, cache : &StringCache) -> Result<Expr, Error> {
  let config = parse_config();
  let mut ps = ParseState::new(tokens, &config, cache);
  let e = parse_top_level(&mut ps)?;
  if ps.has_tokens() {
    let t = ps.peek()?;
    return error(t.loc, format!("Unexpected token '{}' of type '{:?}'", t.to_string(), t.token_type));
  }
  return Ok(e);
}
