use crate::lexer::{Token, TokenType};
use crate::expr::{StringCache, Expr, ExprTag, RefStr};
use crate::error::{Error, ErrorContent, TextLocation, TextMarker, error};
use std::collections::{HashSet, HashMap};
use std::str::FromStr;

static EXPECTED_TOKEN_ERROR : &str = "Expected token. Found nothing.";

struct ParseConfig {
  block_terminators : HashSet<RefStr>,
  expression_terminators : HashSet<RefStr>,
  prefix_precedence : HashMap<RefStr, i32>,
  infix_precedence : HashMap<RefStr, i32>,
  special_operators : HashSet<RefStr>,
}

fn parse_config() -> ParseConfig {
  ParseConfig {
    block_terminators:
      vec!["end", "}", ")", "]", "else", ","].into_iter().map(|s| s.into()).collect(),
    expression_terminators:
      vec!["end", "}", ")", "]", "else", ",", ";"].into_iter().map(|s| s.into()).collect(),
    prefix_precedence:
      vec!["-", "!", "$", "ref", "deref"].into_iter().map(|s| s.into()).collect(),
    infix_precedence:
      vec![
        "=", ".", "==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
        "<", ">", "+", "-", "*", "/", "%", "|", "&", "^", "as"].into_iter().map(|s| s.into()).collect(),
    special_operators:
      vec!["=", ".", "+=", "&&", "||", "$"].into_iter().map(|s| s.into()).collect(),
  }
}

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct ParseState<'l> {
  tokens : Vec<Token>,
  pos : usize,
  cache : &'l StringCache,
  config : &'l ParseConfig,
}

use TokenType::*;

impl <'l> ParseState<'l> {

  fn new(tokens : Vec<Token>, cache : &StringCache,) -> ParseState {
    ParseState { tokens, pos: 0, cache }
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
    TextLocation::new(start, self.peek_marker())
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

// TODO: this might be slow because lazy_static is threadsafe
lazy_static! {
  static ref BLOCK_TERMINATORS : HashSet<&'static str> =
    vec!["end", "}", ")", "]", "else", ","].into_iter().collect();
  static ref EXPRESSION_TERMINATORS : HashSet<&'static str> =
    vec!["end", "}", ")", "]", "else", ",", ";"].into_iter().collect();
  static ref PREFIX_OPERATORS : HashSet<&'static str> =
    vec!["-", "!", "$", "ref", "deref"].into_iter().collect();
  static ref INFIX_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
      "<", ">", "+", "-", "*", "/", "%", "|", "&", "^", "as"].into_iter().collect();
  static ref SPECIAL_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "+=", "&&", "||", "$"].into_iter().collect();
}

fn parse_expression(ps : &mut ParseState) -> Result<Expr, Error> {
  
  fn infix_precedence(t : &Token) -> Result<i32, Error> {
    let p =
      match t.symbol.as_ref() {
        "=" => 1,
        "+=" => 1,
        "&&" => 2,
        "||" => 2,
        ">" => 3,
        "<" => 3,
        ">=" => 3,
        "<=" => 3,
        "==" => 3,
        "!=" => 3,
        "+" => 4,
        "-" => 4,
        "*" => 5,
        "/" => 5,
        "%" => 5,
        "as" => 6,
        "!" => 7,
        "ref" => 7,
        "deref" => 7,
        "(" => 8,
        "[" => 8,
        "." => 9,
        "$" => 10,
        _ => return error(t.loc, format!("Unexpected operator '{}'", t.symbol)),
      };
    Ok(p)
  }

  fn prefix_precedence(t : &Token) -> Result<i32, Error> {
    let p =
      match t.symbol.as_ref() {
        "-" => 4,
        "!" => 7,
        "ref" => 7,
        "deref" => 7,
        "$" => 10,
        _ => return error(t.loc, format!("Unexpected operator '{}'", t.symbol)),
      };
    Ok(p)
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
    let mut expr = parse_prefix(ps)?;
    while ps.has_tokens() {
      let t = ps.peek()?;
      if t.token_type == Syntax && EXPRESSION_TERMINATORS.contains(t.symbol.as_ref()) {
        break;
      }
      else if t.token_type == Syntax && (t.symbol.as_ref() == "(" || t.symbol.as_ref() == "[") {
        let next_precedence = infix_precedence(t)?;
        if next_precedence > precedence {
          if t.symbol.as_ref() == "(" {
            expr = parse_function_call(ps, expr)?;
          }
          else {
            expr = parse_index_expression(ps, expr)?;
          };
        }
        else {
          break;
        }
      }
      else if t.token_type == Syntax && INFIX_OPERATORS.contains(t.symbol.as_ref()) {
        let next_precedence = infix_precedence(t)?;
        if next_precedence > precedence {
          expr = parse_infix(ps, expr, next_precedence)?;
        }
        else {
          break;
        }
      }
      else {
        // Just break, with confidence that the expression is complete. This is a bit crazy, because
        // it would allow a sequence of statements to be placed on the same line without separators.
        break; // TODO: Consider making this throw errors instead
      }
    }
    Ok(expr)
  }

  fn parse_index_expression(ps : &mut ParseState, indexee_expr : Expr) -> Result<Expr, Error> {
    let start = indexee_expr.loc.start;
    ps.expect(Syntax, "[")?;
    let indexing_expr = parse_expression(ps)?;
    ps.expect(Syntax, "]")?;
    let args = vec!(indexee_expr, indexing_expr);
    Ok(ps.add_construct("index", args, start))
  }

  fn parse_function_call(ps : &mut ParseState, function_expr : Expr) -> Result<Expr, Error> {
    let start = function_expr.loc.start;
    ps.expect(Syntax, "(")?;
    let mut exprs = vec!(function_expr);
    if !ps.accept(Syntax, ")") {
      loop {
        exprs.push(parse_expression(ps)?);
        if !ps.accept(Syntax, ",") {
          break;
        }
      }
      ps.expect(Syntax, ")")?;
    }
    Ok(ps.add_construct("call", exprs, start))
  }

  fn parse_prefix(ps : &mut ParseState) -> Result<Expr, Error> {
    let start = ps.peek_marker();
    let t = ps.peek()?;
    // if the next token is a prefix operator
    if t.token_type == Syntax && PREFIX_OPERATORS.contains(t.symbol.as_ref()) {
      let op_string = format!("unary_{}", t.symbol.as_ref());
      ps.expect_type(Syntax)?;
      let operator = ps.add_symbol(op_string, start);
      // TODO: I think this is a bug. It should parse a whole expression, passing in the precedence of the prefix operator.
      // In practise it might never come up, as prefix operators pretty much always have higher precedence than infix
      // operators. I'm not sure if I can think of any counter-examples. This might not work if I double up on prefix
      // operators though, like "--1" or "!!true".
      let expr = parse_expression_term(ps)?;
      let args = vec![operator, expr];
      Ok(ps.add_construct("call", args, start))
    }
    // else assume it's an expression term
    else {
      parse_expression_term(ps)
    }
  }

  fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
    let infix_start = left_expr.loc.start;
    let operator_start = ps.peek_marker();
    let operator_str : String = ps.pop_type(Syntax)?.symbol.as_ref().into();
    if SPECIAL_OPERATORS.contains(operator_str.as_str()) {
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

fn parse_syntax(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  match ps.peek()?.symbol.as_ref() {
    "[" => {
      ps.expect(Syntax, "[")?;
      let mut exprs = vec!();
      loop {
        if ps.peek()?.symbol.as_ref() == "]" {
          break;
        }
        exprs.push(parse_expression(ps)?);
        if ps.peek()?.symbol.as_ref() == "," {
          ps.skip()
        }
        else {
          break;
        }
      }
      ps.expect(Syntax, "]")?;
      Ok(ps.add_construct("literal_array", exprs, start))
    }
    "(" => {
      ps.expect(Syntax, "(")?;
      if ps.accept(Syntax, ")") {
        // "()" denotes the unit value
        let u = ExprTag::LiteralUnit;
        Ok(ps.add_leaf(u, start))
      }
      else {
        let mut exprs = parse_block_exprs(ps)?;
        ps.expect(Syntax, ")")?;
        if exprs.len() == 1 {
          Ok(exprs.pop().unwrap())
        }
        else{
          Ok(ps.add_construct("block", exprs, start))
        }
      }
    }
    _ => error(ps.peek()?.loc, format!("Unexpected syntax '{}'", ps.peek()?.symbol)),
  }
}

fn parse_expression_term(ps : &mut ParseState) -> Result<Expr, Error> {
  match ps.peek()?.token_type {
    Symbol => parse_simple_symbol(ps),
    Syntax => parse_syntax(ps),
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

fn parse_block_exprs(ps : &mut ParseState) -> Result<Vec<Expr>, Error> {
  let mut exprs = vec!();
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || BLOCK_TERMINATORS.contains(ps.peek()?.symbol.as_ref()) {
        break 'outer;
      }
      if ps.peek()?.symbol.as_ref() == ";" {
        ps.skip();
      }
      else {
        break 'inner;
      }
    }
    exprs.push(parse_expression(ps)?);
  }
  if exprs.len() == 0 {
    // There must be at least one expression in a block
    let start = ps.peek_marker();
    exprs.push(ps.add_leaf(ExprTag::LiteralUnit, start));
  }
  Ok(exprs)
}

fn parse_block(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let exprs = parse_block_exprs(ps)?;
  Ok(ps.add_construct("block", exprs, start))
}

pub fn parse(tokens : Vec<Token>, symbols : &StringCache) -> Result<Expr, Error> {
  let mut ps = ParseState::new(tokens, symbols);
  let e = parse_block(&mut ps)?;
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
  let mut ps = ParseState::new(tokens, symbols);
  match parse_block(&mut ps) {
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
