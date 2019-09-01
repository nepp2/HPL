use crate::lexer::{Token, TokenType};
use crate::expr::{StringCache, Expr, ExprTag, RefStr};
use crate::error::{Error, ErrorContent, TextLocation, TextMarker, error};
use std::collections::{HashSet, HashMap};
use std::str::FromStr;

static EXPECTED_TOKEN_ERROR : &str = "Expected token. Found nothing.";

struct ParseConfig {
  paren_pairs : HashMap<RefStr, RefStr>,
  paren_terminators : HashSet<RefStr>,
  expression_separators : HashMap<RefStr, i32>,
  prefix_precedence : HashMap<RefStr, i32>,
  infix_precedence : HashMap<RefStr, i32>,
  special_operators : HashSet<RefStr>,
}

fn parse_config() -> ParseConfig {
  let paren_pairs = vec![
    ("(", ")"),
    ("{", "}"),
    ("[", "]"),
  ];
  ParseConfig {
    expression_separators:
      vec![
        (";", 1),
        (",", 2),
        (":", 3),
      ].into_iter().map(|(s, p)| (s.into(), p)).collect(),
    paren_pairs:
      paren_pairs.iter().cloned().map(|(a, b)| (a.into(), b.into())).collect(),
    paren_terminators: paren_pairs.iter().cloned().map(|(_, b)| b.into()).collect(),
    prefix_precedence:
      vec![
        ("-", 7),
        ("!", 10),
        ("ref", 10),
        ("deref", 10),
        ("$", 13),
      ].into_iter().map(|(s, p)| (s.into(), p)).collect(),
    infix_precedence:
      vec![
        ("=", 4),
        ("+=", 4),
        ("&&", 5),
        ("||", 5),
        (">", 6),
        ("<", 6),
        (">=", 6),
        ("<=", 6),
        ("==", 6),
        ("!=", 6),
        ("+", 7),
        ("-", 7),
        ("*", 8),
        ("/", 8),
        ("%", 8),
        ("as", 9),
        ("(", 11),
        ("[", 11),
        (".", 12),
      ].into_iter().map(|(s, p)| (s.into(), p)).collect(),
    special_operators:
      vec!["=", ".", "+=", "&&", "||", "$"].into_iter().map(|s| s.into()).collect(),
  }
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
    else {
      let m = self.tokens[self.pos-1].loc.end;
      error(TextLocation::new(m, m), EXPECTED_TOKEN_ERROR)
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
    let end = self.tokens[self.pos-1].loc.end;
    TextLocation::new(start, end)
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

  fn accept(&mut self, token_type : TokenType, string : &str) -> bool {
    let accept = {
      if let Ok(t) = self.peek() {
        t.symbol.as_ref() == string &&
        t.token_type == token_type
      }
      else { false }
    };
    if accept { self.skip() }
    accept
  }

  fn expect(&mut self, token_type : TokenType, string : &str) -> Result<(), Error> {
    let t = self.peek()?;
    if t.symbol.as_ref() != string {
      return error(t.loc, format!("Expected token '{}', found token '{}'", string, t.symbol));
    }
    if t.token_type != token_type {
      return error(t.loc, format!("Expected token type '{:?}', found token type '{:?}'", token_type, t.token_type));
    }
    self.skip();
    Ok(())
  }

  /// Returns marker for start of the token if successful
  fn expect_type(&mut self, token_type : TokenType) -> Result<(), Error> {
    {
      let t = self.peek()?;
      if t.token_type != token_type {
        return error(t.loc, format!("Expected token of type '{:?}', found token '{:?}'", token_type, t.token_type));
      }
    }
    self.skip();
    Ok(())
  }

  fn add_expr(&mut self, tag : ExprTag, children : Vec<Expr>, loc : TextLocation) -> Expr {
    Expr::new(tag, children, loc)
  }

  fn add_leaf(&mut self, tag : ExprTag, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    self.add_expr(tag, vec!(), loc)
  }

  fn add_construct<T : Into<String>>
    (&mut self, s : T, children : Vec<Expr>, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let tag = ExprTag::construct(s.into());
    self.add_expr(tag, children, loc)
  }

  fn add_symbol(&mut self, s : String, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    let tag = ExprTag::symbol(s);
    self.add_expr(tag, vec!(), loc)
  }
}

/// This expression parser is vaguely based on some blogs about pratt parsing.
fn pratt_parse(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let mut expr = parse_prefix(ps, precedence)?;
  while ps.has_tokens() {
    let t = ps.peek()?;
    println!("expr parsed: {}, precedence: {}, t: {}", expr, precedence, t.symbol);
    if ps.config.paren_terminators.contains(&t.symbol) {
      println!("bumped into a {}", t.symbol);
      break;
    }
    // New lines are imlicitly semi-colons (except after an infix operator)
    else if expr.loc.end.line != t.loc.start.line {
      let next_precedence = *ps.config.expression_separators.get(";").unwrap();
      if next_precedence > precedence {
        expr = parse_separator(ps, expr, ";".into(), next_precedence)?;
      }
      else {
        break;
      }
    }
    // Separators
    else if let Some(next_precedence) = ps.config.expression_separators.get(&t.symbol) {
      if *next_precedence > precedence {
        let separator = t.symbol.as_ref().into();
        expr = parse_separator(ps, expr, separator, *next_precedence)?;
      }
      else {
        break;
      }
    }
    // Infix operators
    else if let Some(next_precedence) = ps.config.infix_precedence.get(&t.symbol) {
      if *next_precedence > precedence {
        // Parens
        if let Some(close_paren) = ps.config.paren_pairs.get(&t.symbol) {
          let paren_str = match t.symbol.as_ref() {
            "(" => "#paren",
            "{" => "#brace",
            "[" => "#bracket",
            _ => panic!(),
          }.to_string();
          let paren_start = expr.loc.start;
          ps.expect_type(TokenType::Syntax)?;
          let contents = parse_everything(ps)?;
          ps.expect(TokenType::Syntax, close_paren)?;
          expr = ps.add_construct(paren_str, vec![expr, contents], paren_start);
        }
        // Normal infix
        else {
          expr = parse_infix(ps, expr, *next_precedence)?;
        }
      }
      else {
        break;
      }
    }
    else {
      if precedence == 0 {
        //return error(t.loc, format!("unexpected token {}, {}", t.symbol, expr));
      }
      break;
    }
  }
  Ok(expr)
}

fn parse_keyword_expression(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let precedence = std::cmp::max(precedence, 1);
  let t = ps.pop_type(Syntax)?;
  let keyword_expr_start = t.loc.start;
  let keyword_str : String = t.symbol.as_ref().into();
  let line = t.loc.start.line;
  let mut exprs = vec![];
  while ps.has_tokens() {
    let t = ps.peek()?;
    if t.loc.start.line != line {
      break;
    }
    exprs.push(pratt_parse(ps, precedence)?)
  }
  Ok(ps.add_construct(keyword_str, exprs, keyword_expr_start))
}

fn parse_prefix(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let t = ps.peek()?;
  // if the next token is a prefix operator
  if let Some(new_precedence) = ps.config.prefix_precedence.get(t.symbol.as_ref()) {
    let op_string = format!("unary_{}", t.symbol.as_ref());
    ps.expect_type(Syntax)?;
    let operator = ps.add_symbol(op_string, start);
    let expr = pratt_parse(ps, *new_precedence)?;
    let args = vec![operator, expr];
    Ok(ps.add_construct("call", args, start))
  }
  // else assume it's an expression term
  else {
    parse_expression_term(ps, precedence)
  }
}

fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
  let infix_start = left_expr.loc.start;
  let operator_start = ps.peek_marker();
  let operator_str : String = ps.pop_type(Syntax)?.symbol.as_ref().into();
  if ps.config.special_operators.contains(operator_str.as_str()) {
    let right_expr = pratt_parse(ps, precedence)?;
    let args = vec!(left_expr, right_expr);
    Ok(ps.add_construct(operator_str, args, infix_start))
  }
  else {
    let operator = ps.add_symbol(operator_str, operator_start);
    let right_expr = pratt_parse(ps, precedence)?;
    let args = vec!(operator, left_expr, right_expr);
    Ok(ps.add_construct("call", args, infix_start))
  }
}

fn parse_separator(ps : &mut ParseState, left_expr : Expr, separator : String, precedence : i32) -> Result<Expr, Error> {
  let separator_start = left_expr.loc.start;
  let mut args = vec!(left_expr);
  while ps.has_tokens() {
    let t = ps.peek()?;
    if ps.config.paren_terminators.contains(&t.symbol) {
      break;
    }
    let previous_line = args.last().unwrap().loc.end.line;
    let next_line = t.loc.start.line;
    let implicit_separator = previous_line != next_line;
    if !(implicit_separator || ps.accept(Syntax, separator.as_str())) {
      break;
    }
    args.push(pratt_parse(ps, precedence)?);
  }
  Ok(ps.add_construct(separator, args, separator_start))
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

fn parse_simple_string(ps : &mut ParseState, t : TokenType) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let s = ps.pop_type(t)?.symbol.as_ref().into();
  Ok(ps.add_symbol(s, start))
}

fn parse_simple_symbol(ps : &mut ParseState) -> Result<Expr, Error> {
  // TODO: Parse the '$' interpolation operator for quotes
  parse_simple_string(ps, Symbol)
}

fn parse_expression_term(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
  let t = ps.peek()?;
  match t.token_type {
    Symbol => parse_simple_symbol(ps),
    Syntax => {
      // Parens
      if let Some(close_paren) = ps.config.paren_pairs.get(&t.symbol) {
        ps.expect_type(TokenType::Syntax)?;
        let e = parse_everything(ps)?;
        ps.expect(TokenType::Syntax, close_paren)?;
        Ok(e)
      }
      else {
        parse_keyword_expression(ps, precedence)
      }
    }
    StringLiteral => {
      let start = ps.peek_marker();
      let s = {
        let t = ps.pop_type(StringLiteral)?;
        ExprTag::literal_string(t.symbol.as_ref().into())
      };
      Ok(ps.add_leaf(s, start))
    }
    FloatLiteral => {
      let start = ps.peek_marker();
      let f = ExprTag::LiteralFloat(parse_literal(ps)?);
      Ok(ps.add_leaf(f, start))
    }
    IntLiteral => {
      let start = ps.peek_marker();
      let i = ExprTag::LiteralInt(parse_literal(ps)?);
      Ok(ps.add_leaf(i, start))
    }
  }
}

pub fn parse(tokens : Vec<Token>, symbols : &StringCache) -> Result<Expr, Error> {
  let config = parse_config();
  let mut ps = ParseState::new(tokens, &config, symbols);
  let e = parse_everything(&mut ps)?;
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
  match parse_everything(&mut ps) {
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
