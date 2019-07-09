use crate::lexer::{Token, TokenType};
use crate::value::{RefStr, SymbolTable, Expr, ExprTag};
use crate::error::{Error, ErrorContent, TextLocation, TextMarker, error};
use std::collections::HashSet;
use std::str::FromStr;

static EXPECTED_TOKEN_ERROR : &str = "Expected token. Found nothing.";

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct ParseState<'l> {
  tokens : Vec<Token>,
  pos : usize,
  sym : &'l mut SymbolTable,
}

use TokenType::*;

impl <'l> ParseState<'l> {

  fn new(tokens : Vec<Token>, sym : &mut SymbolTable,) -> ParseState {
    ParseState { tokens, pos: 0, sym }
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
    Expr { tag, children, loc }
  }

  fn add_leaf(&mut self, tag : ExprTag, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    self.add_expr(tag, vec!(), loc)
  }

  fn add_tree<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, children : Vec<Expr>, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let tag = ExprTag::Tree(self.sym.get(s));
    self.add_expr(tag, children, loc)
  }

  fn add_symbol<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let tag = ExprTag::Symbol(self.sym.get(s));
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
    vec!["-", "!", "$"].into_iter().collect();
  static ref INFIX_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
      "<", ">", "+", "-", "*", "/", "%", "|", "&", "^", "as"].into_iter().collect();
  static ref SPECIAL_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "+=", "&&", "||", "$"].into_iter().collect();
}

fn parse_expression(ps : &mut ParseState) -> Result<Expr, Error> {
  
  fn operator_precedence(t : &Token) -> Result<i32, Error> {
    // TODO: can't distinguish precedence of unary operator from binary operator.
    // This matters for the '-' operator, for example.
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
        "(" => 8,
        "[" => 8,
        "." => 9,
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
        let next_precedence = operator_precedence(t)?;
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
        let next_precedence = operator_precedence(t)?;
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
    Ok(ps.add_tree("index", args, start))
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
    Ok(ps.add_tree("call", exprs, start))
  }

  fn parse_prefix(ps : &mut ParseState) -> Result<Expr, Error> {
    let start = ps.peek_marker();
    let t = ps.peek()?;
    // if the next token is a prefix operator
    if t.token_type == Syntax && PREFIX_OPERATORS.contains(t.symbol.as_ref()) {
      let mut op_string = String::new();
      op_string.push_str("unary_");
      op_string.push_str(t.symbol.as_ref());
      ps.expect_type(Syntax)?;
      let operator = ps.add_symbol(op_string, start);
      let expr = parse_expression_term(ps)?;
      let args = vec![operator, expr];
      Ok(ps.add_tree("call", args, start))
    }
    // else assume it's an expression term
    else {
      parse_expression_term(ps)
    }
  }

  fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
    let infix_start = left_expr.loc.start;
    let operator_start = ps.peek_marker();
    let operator_str = ps.pop_type(Syntax)?.symbol.clone();
    if operator_str.as_ref() == "as" {
      let right_expr = parse_type(ps)?;
      let args = vec!(left_expr, right_expr);
      Ok(ps.add_tree("as", args, infix_start))
    }
    else if SPECIAL_OPERATORS.contains(operator_str.as_ref()) {
      let right_expr = pratt_parse(ps, precedence)?;
      let args = vec!(left_expr, right_expr);
      Ok(ps.add_tree(operator_str, args, infix_start))
    }
    else {
      let operator = ps.add_symbol(operator_str, operator_start);
      let right_expr = pratt_parse(ps, precedence)?;
      let args = vec!(operator, left_expr, right_expr);
      Ok(ps.add_tree("call", args, infix_start))
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
  let s = ps.pop_type(t)?.symbol.clone();
  Ok(ps.add_symbol(s, start))
}

fn parse_simple_symbol(ps : &mut ParseState) -> Result<Expr, Error> {
  // TODO: Parse the '$' interpolation operator for quotes
  parse_simple_string(ps, Symbol)
}

fn parse_type(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let type_name = ps.pop_type(Symbol)?.symbol.clone();
  let mut params = vec!();
  if ps.accept(Syntax, "(") {
    loop {
      if ps.peek()?.token_type != Symbol {
        break;
      }
      params.push(parse_type(ps)?);
      if !ps.accept(Syntax, ",") {
        break;
      }
    }
    ps.expect(Syntax, ")")?;
  }
  let type_expr = ps.add_tree(type_name, params, start);
  Ok(type_expr)
}

fn parse_function(ps : &mut ParseState, keyword : &str) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, keyword)?;
  let fun_name = parse_simple_symbol(ps)?;
  let mut arguments = vec!();
  let args_start = ps.peek_marker();
  ps.expect(Syntax, "(")?;
  loop {
    if ps.peek()?.token_type != Symbol {
      break;
    }
    arguments.push(parse_simple_symbol(ps)?);
    if ps.accept(Syntax, ":") {
      arguments.push(parse_type(ps)?);
    }
    else {
      let start = ps.peek_marker();
      arguments.push(ps.add_symbol("", start));
    }
    if !ps.accept(Syntax, ",") {
      break;
    }
  }
  ps.expect(Syntax, ")")?;
  let args_expr = ps.add_tree("args", arguments, args_start);
  let function_block = parse_block(ps)?;
  ps.expect(Syntax, "end")?;
  let fun_expr = ps.add_tree("fun", vec![fun_name, args_expr, function_block], start);
  Ok(fun_expr)
}

fn parse_fun(ps : &mut ParseState) -> Result<Expr, Error> {
  parse_function(ps, "fun")
}

fn parse_cfun(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "cfun")?;
  let fun_name = parse_simple_symbol(ps)?;
  let mut arguments = vec!();
  let args_start = ps.peek_marker();
  ps.expect(Syntax, "(")?;
  loop {
    if ps.peek()?.token_type != Symbol {
      break;
    }
    arguments.push(parse_simple_symbol(ps)?);
    ps.expect(Syntax, ":")?;
    arguments.push(parse_type(ps)?);
    if !ps.accept(Syntax, ",") {
      break;
    }
  }
  ps.expect(Syntax, ")")?;
  let args_expr = ps.add_tree("args", arguments, args_start);
  let return_type = if ps.accept(Syntax, ":") {
    parse_type(ps)?
  }
  else {
    ps.add_symbol("", start)
  };
  let cfun_expr = ps.add_tree("cfun", vec![fun_name, args_expr, return_type], start);
  Ok(cfun_expr)
}

fn parse_macro(ps : &mut ParseState) -> Result<Expr, Error> {
  parse_function(ps, "macro")
}

fn parse_let(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "let")?;
  let var_name = parse_simple_symbol(ps)?;
  ps.expect(Syntax, "=")?;
  let initialiser = parse_expression(ps)?;
  Ok(ps.add_tree("let", vec!(var_name, initialiser), start))
}

fn parse_if(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "if")?;
  let conditional = parse_expression(ps)?;
  ps.accept(Syntax, "then");
  let then_block = parse_block(ps)?;
  let mut args = vec!(conditional, then_block);
  if ps.accept(Syntax, "else") {
    if ps.peek()?.symbol.as_ref() == "if" {
      let else_if = parse_if(ps)?;
      args.push(else_if);
    }
    else {
      let else_block = parse_block(ps)?;
      ps.expect(Syntax, "end")?;
      args.push(else_block);
    }
  }
  else {
    ps.expect(Syntax, "end")?;
  }
  Ok(ps.add_tree("if", args, start))
}

fn parse_while(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "while")?;
  let conditional = parse_expression(ps)?;
  let loop_block = parse_block(ps)?;
  ps.expect(Syntax, "end")?;
  let args = vec!(conditional, loop_block);
  Ok(ps.add_tree("while", args, start))
}

fn parse_for(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "for")?;
  let loop_var = parse_simple_symbol(ps)?;
  ps.expect(Syntax, "in")?;
  let iterator = parse_expression(ps)?;
  let loop_block = parse_block(ps)?;
  ps.expect(Syntax, "end")?;
  let args = vec!(loop_var, iterator, loop_block);
  Ok(ps.add_tree("for", args, start))
}

fn parse_struct_definition(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "struct")?;
  let struct_name = parse_simple_symbol(ps)?;
  let mut args = vec!(struct_name);
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.symbol.as_ref() == "end" {
        break 'outer;
      }
      if !ps.accept(Syntax, ",") {
        break 'inner;
      }
    }
    let arg_name = parse_simple_symbol(ps)?;
    args.push(arg_name);
    if ps.accept(Syntax, ":") {
      let type_expr = parse_type(ps)?;
      args.push(type_expr);
    }
    else {
      let start = ps.peek_marker();
      args.push(ps.add_symbol("", start));
    }
  }
  ps.expect(Syntax, "end")?;
  Ok(ps.add_tree("struct_define", args, start))
}

fn parse_struct_instantiate(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let struct_name = parse_simple_symbol(ps)?;
  ps.expect(Syntax, "{")?;
  let mut args = vec!(struct_name);
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.symbol.as_ref() == "}" {
        break 'outer;
      }
      if ps.peek()?.symbol.as_ref() == "," {
        ps.skip();
      }
      else {
        break 'inner;
      }
    }
    let named =
      ps.peek_ahead(0).map_or(false, |t| t.token_type == Symbol)
      && ps.peek_ahead(1).map_or(false, |t| t.symbol.as_ref() == ":");
    if named {
      args.push(parse_simple_symbol(ps)?);
      ps.expect(Syntax, ":")?;
      args.push(parse_expression(ps)?);
    }
    else {
      let start = ps.peek_marker();
      args.push(ps.add_symbol("", start));
      args.push(parse_expression(ps)?);
    }
  }
  ps.expect(Syntax, "}")?;
  Ok(ps.add_tree("struct_instantiate", args, start))
}

fn parse_sizeof(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "sizeof")?;
  ps.expect(Syntax, "(")?;
  let e = parse_type(ps)?;
  ps.expect(Syntax, ")")?;
  Ok(ps.add_tree("sizeof", vec![e], start))
}

fn parse_quote(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "quote")?;
  let e = parse_expression(ps)?;
  Ok(ps.add_tree("quote", vec![e], start))
}

fn parse_return(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect(Syntax, "return")?;
  if ps.has_tokens() {
    let t = ps.peek()?;
    if !EXPRESSION_TERMINATORS.contains(t.symbol.as_ref()) {
      let e = parse_expression(ps)?;
      return Ok(ps.add_tree("return", vec![e], start));
    }
  }
  Ok(ps.add_tree("return", vec![], start))
}

fn parse_syntax(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  match ps.peek()?.symbol.as_ref() {
    "sizeof" => parse_sizeof(ps),
    "quote" => parse_quote(ps),
    "let" => parse_let(ps),
    "fun" => parse_fun(ps),
    "cfun" => parse_cfun(ps),
    "macro" => parse_macro(ps),
    "if" => parse_if(ps),
    "for" => parse_for(ps),
    "break" => {
      Ok(parse_simple_string(ps, Syntax)?)
    }
    "return" => parse_return(ps),
    "while" => parse_while(ps),
    "struct" => parse_struct_definition(ps),
    "true" => {
      let start = ps.peek_marker();
      ps.expect(Syntax, "true")?;
      Ok(ps.add_leaf(ExprTag::LiteralBool(true), start))
    }
    "false" => {
      let start = ps.peek_marker();
      ps.expect(Syntax, "false")?;
      Ok(ps.add_leaf(ExprTag::LiteralBool(false), start))
    }
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
      Ok(ps.add_tree("literal_array", exprs, start))
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
          Ok(ps.add_tree("block", exprs, start))
        }
      }
    }
    "do" => {
      ps.expect(Syntax, "do")?;
      let block = parse_block(ps)?;
      ps.expect(Syntax, "end")?;
      Ok(block)
    }
    _ => error(ps.peek()?.loc, format!("Unexpected syntax '{}'", ps.peek()?.symbol)),
  }
}

fn parse_symbol_term(ps : &mut ParseState) -> Result<Expr, Error> {
  let is_struct =
    ps.peek_ahead(1).map_or(false, |t| t.symbol.as_ref() == "{");
  if is_struct {
    parse_struct_instantiate(ps)
  }
  else{
    // else assume it's just a symbol reference
    parse_simple_symbol(ps)
  }
}

fn parse_expression_term(ps : &mut ParseState) -> Result<Expr, Error> {
  match ps.peek()?.token_type {
    Symbol => parse_symbol_term(ps),
    Syntax => parse_syntax(ps),
    StringLiteral => {
      let start = ps.peek_marker();
      let s = {
        let t = ps.pop_type(StringLiteral)?;
        ExprTag::LiteralString(t.symbol.clone())
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
  Ok(exprs)
}

fn parse_block(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let exprs = parse_block_exprs(ps)?;
  Ok(ps.add_tree("block", exprs, start))
}

pub fn parse(tokens : Vec<Token>, symbols : &mut SymbolTable) -> Result<Expr, Error> {
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

pub fn repl_parse(tokens : Vec<Token>, symbols : &mut SymbolTable) -> Result<ReplParseResult, Error> {
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
