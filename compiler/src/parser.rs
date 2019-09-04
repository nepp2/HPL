use crate::lexer::{Token, TokenType};
use crate::expr::{StringCache, Expr, ExprContent, RefStr};
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

/// Precedence level
struct PL { infix : &'static [&'static str], prefix : &'static [&'static str] }

fn parse_config() -> ParseConfig {
  let mut c = ParseConfig {
    paren_pairs: HashMap::new(),
    paren_terminators: HashSet::new(),
    expression_separators: HashMap::new(),
    prefix_precedence: HashMap::new(),
    infix_precedence: HashMap::new(),
    special_operators:
      vec!["=", ".", "+=", "&&", "||", "$", "else", ":"]
      .into_iter().map(|s| s.into()).collect(),
  };
  let paren_pairs = vec![
    ("(", ")"),
    ("{", "}"),
    ("[", "]"),
  ];
  let expression_separators = &[";", "," ];
  let operators : &[PL] = &[
    PL { infix: &["=", "+="], prefix: &[] },
    PL { infix: &[":"], prefix: &[] },
    PL { infix: &["else"], prefix: &[] },
    PL { infix: &["&&", "||"], prefix: &[] },
    PL { infix: &[">", "<", ">=", "<=", "==", "!="], prefix: &[] },
    PL { infix: &["+", "-"], prefix: &["-"] },
    PL { infix: &["*", "/", "%"], prefix: &[] },
    PL { infix: &["as"], prefix: &[] },
    PL { infix: &[], prefix: &["!", "ref", "deref",] },
    PL { infix: &["(", "["], prefix: &[] },
    PL { infix: &["."], prefix: &[] },
  ];
  let mut precedence = 0;
  for s in expression_separators {
    precedence += 1;
    c.expression_separators.insert((*s).into(), precedence);
  }
  for (a, b) in paren_pairs {
    c.paren_pairs.insert(a.into(), b.into());
    c.paren_terminators.insert(b.into());
  }
  for level in operators {
    precedence += 1;
    for i in level.infix {
      c.infix_precedence.insert((*i).into(), precedence);
    }
    for p in level.prefix {
      c.prefix_precedence.insert((*p).into(), precedence);
    }
  }
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

  fn add_list(&mut self, list : Vec<Expr>, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let content = ExprContent::list(list);
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
  let mut expr = parse_prefix(ps, precedence)?;
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
        if let Some(_close_paren) = ps.config.paren_pairs.get(&t.symbol) {
          let paren_start = expr.loc.start;
          let call = ps.add_symbol("#call", paren_start);
          let contents = parse_expression_term(ps, precedence)?;
          expr = ps.add_list(vec![call, expr, contents], paren_start);
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
  let keyword = parse_simple_string(ps, Syntax)?;
  let keyword_expr_start = keyword.loc.start;
  let line = keyword.loc.start.line;
  let mut exprs = vec![keyword];
  while ps.has_tokens() {
    let t = ps.peek()?;
    if t.loc.start.line != line {
      break;
    }
    exprs.push(pratt_parse(ps, precedence)?)
  }
  Ok(ps.add_list(exprs, keyword_expr_start))
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
    let call = ps.add_symbol("#call", start);
    Ok(ps.add_list(vec![call, operator, expr], start))
  }
  // else assume it's an expression term
  else {
    parse_expression_term(ps, precedence)
  }
}

fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
  let infix_start = left_expr.loc.start;
  let operator_str = ps.peek()?.symbol.as_ref();
  if ps.config.special_operators.contains(operator_str) {
    let operator = parse_simple_string(ps, Syntax)?;
    let right_expr = pratt_parse(ps, precedence)?;
    let args = vec!(operator, left_expr, right_expr);
    Ok(ps.add_list(args, infix_start))
  }
  else {
    let operator = parse_simple_string(ps, Syntax)?;
    let right_expr = pratt_parse(ps, precedence)?;
    let call = ps.add_symbol("#call", infix_start);
    let args = vec!(call, operator, left_expr, right_expr);
    Ok(ps.add_list(args, infix_start))
  }
}

fn parse_separator(ps : &mut ParseState, left_expr : Expr, separator : String, precedence : i32) -> Result<Expr, Error> {
  let separator_start = left_expr.loc.start;
  let is_semicolon = separator.as_str() == ";";
  let separator_expr = ps.add_symbol(separator.as_str(), ps.peek_marker());
  let mut args = vec!(separator_expr, left_expr);
  while ps.has_tokens() {
    let t = ps.peek()?;
    if ps.config.paren_terminators.contains(&t.symbol) {
      break;
    }
    let implicit_separator = is_semicolon && {
      let previous_line = args.last().unwrap().loc.end.line;
      let next_line = t.loc.start.line;
      previous_line != next_line
    };
    if !(implicit_separator || ps.accept(Syntax, separator.as_str())) {
      break;
    }
    args.push(pratt_parse(ps, precedence)?);
  }
  Ok(ps.add_list(args, separator_start))
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
  let s : String = ps.pop_type(t)?.symbol.as_ref().into();
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
        let start = ps.peek_marker();
        let label = format!("#{}{}", t.symbol, close_paren);
        ps.expect_type(TokenType::Syntax)?;
        let label = ps.add_symbol(label, start);
        if ps.accept(TokenType::Syntax, close_paren) {
          Ok(ps.add_list(vec![label], start))
        }
        else {
          let mut e = parse_everything(ps)?;
          ps.expect(TokenType::Syntax, close_paren)?;
          match &mut e.content {
            ExprContent::List(list) => {
              let mut args = vec![label];
              let mut v = list.empty_into_vec();
              args.append(&mut v);
              Ok(ps.add_list(args, start))
            }
            _ => {
              Ok(ps.add_list(vec![label, e], start))
            }
          }
        }
      }
      else {
        parse_keyword_expression(ps, precedence)
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
