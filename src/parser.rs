use crate::lexer;
use crate::lexer::{Token, TokenType};
use crate::value::{RefStr, SymbolCache, Expr, ExprTag, ExprId, Type};
use crate::error::{Error, TextLocation, TextMarker, error};
use std::collections::HashSet;
use std::f32;
use std::str::FromStr;

static CALL : &str = "call";
static INDEX : &str = "index";
static LITERAL_ARRAY : &str = "literal_array";
static ARGS : &str = "args";
static FUN : &str = "fun";
static LET : &str = "let";
static IF : &str = "if";
static WHILE : &str = "while";
static FOR : &str = "for";
static STRUCT_DEFINE : &str = "struct_define";
static STRUCT_INSTANTIATE : &str = "struct_instantiate";
static BREAK : &str = "break";
static BLOCK : &str = "block";
static REGION : &str = "region";
pub static NO_TYPE : &str = "[NO_TYPE]";

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct ParseState<'l> {
  tokens : Vec<Token>,
  pos : usize,
  symbol_cache : &'l mut SymbolCache,
  expr_id_gen : ExprId, // TODO: this should be cached in the interpreter. At the moment, ids will be reused!
}

impl <'l> ParseState<'l> {

  fn new(tokens : Vec<Token>, symbol_cache : &mut SymbolCache,) -> ParseState {
    ParseState { tokens, pos: 0, symbol_cache, expr_id_gen: 0 }
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
      error(TextLocation::new(m, m), "Expected token. Found nothing.")
    }
  }

  fn peek_marker(&self) -> TextMarker {
    if self.has_tokens() {
      self.tokens[self.pos].loc.start
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

  fn accept_string(&mut self, string : &str) -> bool {
    let accept = {
      if let Ok(t) = self.peek() {
        t.string.as_ref() == string
      }
      else { false }
    };
    if accept { self.skip() }
    accept
  }

  fn expect_string(&mut self, string : &str) -> Result<(), Error> {
    {
      let t = self.peek()?;
      if t.string.as_ref() != string {
        return error(t.loc, format!("Expected token '{}', found token '{}'", string, t.string));
      }
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
    let id = self.expr_id_gen;
    self.expr_id_gen += 1;
    Expr { id, tag, children, loc, type_info: Type::Unresolved }
  }

  fn add_leaf(&mut self, tag : ExprTag, start : TextMarker) -> Expr {
    let loc = self.loc(start);
    self.add_expr(tag, vec!(), loc)
  }

  fn add_tree<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, children : Vec<Expr>, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let tag = ExprTag::Tree(self.symbol_cache.symbol(s));
    self.add_expr(tag, children, loc)
  }

  fn add_symbol<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, start : TextMarker) -> Expr
  {
    let loc = self.loc(start);
    let tag = ExprTag::Symbol(self.symbol_cache.symbol(s));
    self.add_expr(tag, vec!(), loc)
  }
}

// TODO: this might be slow because lazy_static is threadsafe
lazy_static! {
  static ref TERMINATING_SYNTAX : HashSet<&'static str> =
    vec!["}", ")", "]", ";", ","].into_iter().collect();
  static ref PREFIX_OPERATORS : HashSet<&'static str> =
    vec!["-", "!"].into_iter().collect();
  static ref INFIX_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
      "<", ">", "+", "-", "*", "/", "|", "&", "^"].into_iter().collect();
  static ref SPECIAL_OPERATORS : HashSet<&'static str> =
    vec!["=", ".", "+="].into_iter().collect();
}

fn parse_expression(ps : &mut ParseState) -> Result<Expr, Error> {
  
  fn operator_precedence(t : &Token) -> Result<i32, Error> {
    let p =
      match t.string.as_ref() {
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
        "!" => 6,
        "(" => 7,
        "[" => 7,
        "." => 8,
        _ => return error(t.loc, format!("Unexpected operator '{}'", t.string)),
      };
    Ok(p)
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ps : &mut ParseState, precedence : i32) -> Result<Expr, Error> {
    let mut expr = parse_prefix(ps)?;
    while ps.has_tokens() {
      let t = ps.peek()?;
      if t.token_type == TokenType::Syntax && TERMINATING_SYNTAX.contains(t.string.as_ref()) {
        break;
      }
      else if t.token_type == TokenType::Syntax && (t.string.as_ref() == "(" || t.string.as_ref() == "[") {
        let next_precedence = operator_precedence(t)?;
        if next_precedence > precedence {
          if t.string.as_ref() == "(" {
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
      else if t.token_type == TokenType::Syntax && INFIX_OPERATORS.contains(t.string.as_ref()) {
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
    ps.expect_string("[")?;
    let indexing_expr = parse_expression(ps)?;
    ps.expect_string("]")?;
    let args = vec!(indexee_expr, indexing_expr);
    Ok(ps.add_tree(INDEX, args, start))
  }

  fn parse_function_call(ps : &mut ParseState, function_expr : Expr) -> Result<Expr, Error> {
    let start = function_expr.loc.start;
    ps.expect_string("(")?;
    let mut exprs = vec!(function_expr);
    if !ps.accept_string(")") {
      loop {
        exprs.push(parse_expression(ps)?);
        if !ps.accept_string(",") {
          break;
        }
      }
      ps.expect_string(")")?;
    }
    Ok(ps.add_tree(CALL, exprs, start))
  }

  fn parse_prefix(ps : &mut ParseState) -> Result<Expr, Error> {
    let start = ps.peek_marker();
    let t = ps.peek()?;
    // if the next token is a prefix operator
    if t.token_type == TokenType::Syntax && PREFIX_OPERATORS.contains(t.string.as_ref()) {
      let operator = ps.add_symbol(t.string.clone(), start);
      ps.expect_type(TokenType::Syntax)?;
      let expr = parse_expression_term(ps)?;
      let args = vec![operator, expr];
      Ok(ps.add_tree(CALL, args, start))
    }
    // else assume it's an expression term
    else {
      parse_expression_term(ps)
    }
  }

  fn parse_infix(ps : &mut ParseState, left_expr : Expr, precedence : i32) -> Result<Expr, Error> {
    let infix_start = left_expr.loc.start;
    let operator_start = ps.peek_marker();
    let operator_str = ps.pop_type(TokenType::Syntax)?.string.clone();
    if SPECIAL_OPERATORS.contains(operator_str.as_ref()) {
      let right_expr = pratt_parse(ps, precedence)?;
      let args = vec!(left_expr, right_expr);
      Ok(ps.add_tree(operator_str, args, infix_start))
    }
    else {
      let operator = ps.add_symbol(operator_str, operator_start);
      let right_expr = pratt_parse(ps, precedence)?;
      let args = vec!(operator, left_expr, right_expr);
      Ok(ps.add_tree(CALL, args, infix_start))
    }
  }

  pratt_parse(ps, 0)
}

fn parse_float(ps : &mut ParseState) -> Result<f32, Error> {
  let t = ps.pop_type(TokenType::FloatLiteral)?;
  if let Ok(f) = f32::from_str(&t.string) {
    Ok(f)
  }
  else {
    error(t.loc, format!("Failed to parse float from '{}'", t.string))
  }
}

fn parse_syntax(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  match ps.peek()?.string.as_ref() {
    "[" => {
      ps.expect_string("[")?;
      let mut exprs = vec!();
      loop {
        if ps.peek()?.string.as_ref() == "]" {
          break;
        }
        exprs.push(parse_expression(ps)?);
        if ps.peek()?.string.as_ref() == "," {
          ps.skip()
        }
        else {
          break;
        }
      }
      ps.expect_string("]")?;
      Ok(ps.add_tree(LITERAL_ARRAY, exprs, start))
    }
    "(" => {
      ps.expect_string("(")?;
      if ps.accept_string(")") {
        // "()" denotes the unit value
        let u = ExprTag::LiteralUnit;
        Ok(ps.add_leaf(u, start))
      }
      else {
        let a = parse_expression(ps)?;
        ps.expect_string(")")?;
        Ok(a)
      }
    }
    _ => error(ps.peek()?.loc, format!("Unexpected syntax '{}'", ps.peek()?.string)),
  }
}

fn parse_simple_string(ps : &mut ParseState, t : TokenType) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let s = ps.pop_type(t)?.string.clone();
  Ok(ps.add_symbol(s, start))
}

fn parse_simple_symbol(ps : &mut ParseState) -> Result<Expr, Error> {
  parse_simple_string(ps, TokenType::Symbol)
}

fn parse_type(ps : &mut ParseState) -> Result<Expr, Error> {
  parse_simple_symbol(ps)
}

fn parse_fun(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string("fun")?;
  let fun_name = parse_simple_symbol(ps)?;
  let mut arguments = vec!();
  let args_start = ps.peek_marker();
  ps.expect_string("(")?;
  loop {
    if ps.peek()?.token_type != TokenType::Symbol {
      break;
    }
    arguments.push(parse_simple_symbol(ps)?);
    if ps.accept_string(":") {
      arguments.push(parse_type(ps)?);
    }
    else {
      let start = ps.peek_marker();
      arguments.push(ps.add_symbol(NO_TYPE, start));
    }
    if !ps.accept_string(",") {
      break;
    }
  }
  ps.expect_string(")")?;
  let args_expr = ps.add_tree(ARGS, arguments, args_start);
  ps.expect_string("{")?;
  let function_block = parse_block(ps)?;
  ps.expect_string("}")?;
  let fun_expr = ps.add_tree(FUN, vec![fun_name, args_expr, function_block], start);
  Ok(fun_expr)
}

fn parse_let(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string("let")?;
  let var_name = parse_simple_symbol(ps)?;
  ps.expect_string("=")?;
  let initialiser = parse_expression(ps)?;
  Ok(ps.add_tree(LET, vec!(var_name, initialiser), start))
}

fn parse_if(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string("if")?;
  let conditional = parse_expression(ps)?;
  ps.expect_string("{")?;
  let then_block = parse_block(ps)?;
  ps.expect_string("}")?;
  let mut args = vec!(conditional, then_block);
  if ps.accept_string("else") {
    ps.expect_string("{")?;
    let else_block = parse_block(ps)?;
    ps.expect_string("}")?;
    args.push(else_block);
  }
  Ok(ps.add_tree(IF, args, start))
}

fn parse_while(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string(WHILE)?;
  let conditional = parse_expression(ps)?;
  ps.expect_string("{")?;
  let loop_block = parse_block(ps)?;
  ps.expect_string("}")?;
  let args = vec!(conditional, loop_block);
  Ok(ps.add_tree(WHILE, args, start))
}

fn parse_for(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string(FOR)?;
  let loop_var = parse_simple_symbol(ps)?;
  ps.expect_string("in")?;
  let iterator = parse_expression(ps)?;
  ps.expect_string("{")?;
  let loop_block = parse_block(ps)?;
  ps.expect_string("}")?;
  let args = vec!(loop_var, iterator, loop_block);
  Ok(ps.add_tree(FOR, args, start))
}

fn parse_struct_definition(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string("struct")?;
  let struct_name = parse_simple_symbol(ps)?;
  ps.expect_string("{")?;
  let mut args = vec!(struct_name);
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.string.as_ref() == "}" {
        break 'outer;
      }
      if !ps.accept_string(",") {
        break 'inner;
      }
    }
    let arg_name = parse_simple_symbol(ps)?;
    args.push(arg_name);
    if ps.accept_string(":") {
      let type_name = parse_simple_symbol(ps)?;
      args.push(type_name);
    }
    else {
      let start = ps.peek_marker();
      args.push(ps.add_symbol(NO_TYPE, start));
    }
  }
  ps.expect_string("}")?;
  Ok(ps.add_tree(STRUCT_DEFINE, args, start))
}

fn parse_struct_instantiate(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  let struct_name = parse_simple_symbol(ps)?;
  ps.expect_string("(")?;
  let mut args = vec!(struct_name);
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.string.as_ref() == ")" {
        break 'outer;
      }
      if ps.peek()?.string.as_ref() == "," {
        ps.skip();
      }
      else {
        break 'inner;
      }
    }
    let arg_name = parse_simple_symbol(ps)?;
    args.push(arg_name);
    ps.expect_string(":")?;
    args.push(parse_expression(ps)?);
  }
  ps.expect_string(")")?;
  Ok(ps.add_tree(STRUCT_INSTANTIATE, args, start))
}

fn parse_region(ps : &mut ParseState) -> Result<Expr, Error> {
  let start = ps.peek_marker();
  ps.expect_string("region")?;
  ps.expect_string("{")?;
  let exprs = parse_block_exprs(ps)?;
  ps.expect_string("}")?;
  Ok(ps.add_tree(BLOCK, exprs, start))
}

fn parse_keyword_term(ps : &mut ParseState) -> Result<Expr, Error> {
  match ps.peek()?.string.as_ref() {
    "region" => parse_region(ps),
    "let" => parse_let(ps),
    "fun" => parse_fun(ps),
    "if" => parse_if(ps),
    "for" => parse_for(ps),
    "break" => {
      Ok(parse_simple_string(ps, TokenType::Keyword)?)
    }
    "while" => parse_while(ps),
    "struct" => parse_struct_definition(ps),
    "true" => {
      let start = ps.peek_marker();
      ps.expect_string("true")?;
      Ok(ps.add_leaf(ExprTag::LiteralBool(true), start))
    }
    "false" => {
      let start = ps.peek_marker();
      ps.expect_string("false")?;
      Ok(ps.add_leaf(ExprTag::LiteralBool(false), start))
    }
    _ => {
      let t = ps.peek()?;
      error(t.loc, format!("Encountered unexpected keyword '{}'. This keyword is not supported here.", t.string))
    }
  }
}

fn parse_symbol_term(ps : &mut ParseState) -> Result<Expr, Error> {
  let is_struct =
    ps.peek_ahead(1).map_or(false, |t| t.string.as_ref() == "(")
    && ps.peek_ahead(2).map_or(false, |t| t.token_type == TokenType::Symbol)
    && ps.peek_ahead(3).map_or(false, |t| t.string.as_ref() == ":");
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
    TokenType::Symbol => parse_symbol_term(ps),
    TokenType::Keyword => parse_keyword_term(ps),
    TokenType::Syntax => parse_syntax(ps),
    TokenType::StringLiteral => {
      let start = ps.peek_marker();
      let s = {
        let t = ps.pop_type(TokenType::StringLiteral)?;
        ExprTag::LiteralString(t.string.clone())
      };
      Ok(ps.add_leaf(s, start))
    }
    TokenType::FloatLiteral => {
      let start = ps.peek_marker();
      let f = ExprTag::LiteralFloat(parse_float(ps)?);
      Ok(ps.add_leaf(f, start))
    }
  }
}

fn parse_block_exprs(ps : &mut ParseState) -> Result<Vec<Expr>, Error> {
  let mut exprs = vec!();
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.string.as_ref() == "}" {
        break 'outer;
      }
      if ps.peek()?.string.as_ref() == ";" {
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
  Ok(ps.add_tree(BLOCK, exprs, start))
}

pub fn parse_with_cache(tokens : Vec<Token>, symbol_cache : &mut SymbolCache,) -> Result<Expr, Error> {
  let mut ps = ParseState::new(tokens, symbol_cache);
  let e = parse_block(&mut ps)?;
  if ps.has_tokens() {
    let t = ps.peek()?;
    return error(t.loc, format!("Unexpected token '{}' of type '{:?}'", t.string, t.token_type));
  }
  return Ok(e);
}

pub fn parse(tokens : Vec<Token>) -> Result<Expr, Error> {
  parse_with_cache(tokens, &mut SymbolCache::new())
}

#[test]
fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parse(tokens);
  println!("{:?}", ast);
}
