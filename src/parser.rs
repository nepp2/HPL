use lexer;
use lexer::{Token, TokenType};
use value::{RefStr, SymbolCache};
use error::{Error, TextLocation, TextMarker};
use std::collections::HashSet;
use std::f32;
use std::str::FromStr;

/*

TODO: there should be a symbol table to get rid of all the string duplication.

TODO: a lot of string copying happens in this file, which isn't great.
I guess garbage collection is actually pretty good for strings. A lot of
them could be static, but I'd have to fiddle the types a lot to do something
about that. I could also consume the tokens way more efficiency, but I'd
have to change a lot of code.

TODO: Question. does creating a new string from a static string actually allocate?
*/

// TODO: this might be slow because lazy_static is threadsafe

static CALL : &str = "call";
static INDEX : &str = "index";
static LITERAL_ARRAY : &str = "literal_array";
static ARGS : &str = "args";
static FUN : &str = "fun";
static LET : &str = "let";
static IF : &str = "if";
static WHILE : &str = "while";
static STRUCT_DEFINE : &str = "struct_define";
static STRUCT_INSTANTIATE : &str = "struct_instantiate";
static BREAK : &str = "break";
static BLOCK : &str = "block";
pub static NO_TYPE : &str = "[NO_TYPE]";

#[derive(PartialEq, Debug, Clone)]
pub enum ExprTag {
  Tree(RefStr),
  Symbol(RefStr),
  LiteralFloat(f32),
  LiteralBool(bool),
}

/// Used to look up expressions in the abstract syntax tree
pub type ExprId = usize;

/// Expression
#[derive(Debug)]
pub struct Expr {
  pub tag : ExprTag,
  pub children : Vec<ExprId>,
  pub loc : TextLocation,
}

impl Expr {
  pub fn tree_symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Tree(s) = &self.tag {
      Ok(&s)
    }
    else {
      error_expr!(self, "expected a tree, found {:?}", self)
    }
  }

  pub fn symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(&s)
    }
    else {
      error_expr!(self, "expected a symbol, found {:?}", self)
    }
  }

  pub fn symbol_to_refstr(&self) -> Result<RefStr, Error> {
    self.symbol_unwrap().map(|s| s.clone())
  }
}

/// Abstract syntax tree
#[derive(Debug)]
pub struct Ast {
  pub root_id : ExprId,
  pub exprs : Vec<Expr>,
}

impl Ast {
  pub fn expr(&self, id : ExprId) -> &Expr {
    &self.exprs[id]
  }

  pub fn tag(&self, id : ExprId) -> &ExprTag {
    &self.exprs[id].tag
  }

  pub fn children(&self, id : ExprId) -> Result<&[ExprId], Error> {
    let e = &self.exprs[id];
    match e.tag {
      ExprTag::Tree(_) => Ok(&self.exprs[id].children),
      _ => error_result!(e, "expected tree, found {:?}", e)
    }
    
  }

  pub fn loc(&self, id : ExprId) -> &TextLocation {
    &self.exprs[id].loc
  }
}

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct ParseState {
  tokens : Vec<Token>,
  pos : usize,
  symbol_cache : SymbolCache,
  exprs : Vec<Expr>,
}

impl ParseState {

  fn new(tokens : Vec<Token>) -> ParseState {
    ParseState { tokens, pos: 0, symbol_cache: SymbolCache::new(), exprs: vec!() }
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
      error!(TextLocation::new(m, m), "Expected token. Found nothing.")
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
        return error!(t.loc, "Expected token '{}', found token '{}'", string, t.string);
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
        return error!(t.loc, "Expected token of type '{:?}', found token '{:?}'", token_type, t.token_type);
      }
    }
    self.skip();
    Ok(())
  }

  fn add_expr(&mut self, e : Expr) -> ExprId {
    let id = self.exprs.len();
    self.exprs.push(e);
    id
  }

  fn add_leaf(&mut self, tag : ExprTag, start : TextMarker) -> ExprId {
    let loc = self.loc(start);
    self.add_expr(Expr { tag, children: vec!(), loc })
  }

  fn add_tree<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, children : Vec<ExprId>, start : TextMarker) -> ExprId
  {
    let loc = self.loc(start);
    let tag = ExprTag::Tree(self.symbol_cache.symbol(s));
    self.add_expr(Expr { tag, children, loc })
  }

  fn add_symbol<T : AsRef<str> + Into<RefStr>>
    (&mut self, s : T, start : TextMarker) -> ExprId
  {
    let loc = self.loc(start);
    let tag = ExprTag::Symbol(self.symbol_cache.symbol(s));
    self.add_expr(Expr { tag, children: vec!(), loc })
  }

  pub fn get_loc(&self, id : ExprId) -> &TextLocation {
    &self.exprs[id].loc
  }
}

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

fn parse_expression(ps : &mut ParseState) -> Result<ExprId, Error> {
  
  fn operator_precedence(t : &Token) -> Result<i32, Error> {
    let p =
      match t.string.as_ref() {
        "=" => 1,
        "+=" => 1,
        ">" => 2,
        "<" => 2,
        ">=" => 2,
        "<=" => 2,
        "==" => 2,
        "&&" => 3,
        "||" => 3,
        "+" => 4,
        "-" => 4,
        "*" => 5,
        "/" => 5,
        "!" => 6,
        "(" => 7,
        "[" => 7,
        "." => 8,
        _ => return error!(t.loc, "Unexpected operator '{}'", s),
      };
    Ok(p)
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ps : &mut ParseState, precedence : i32) -> Result<ExprId, Error> {
    // TODO: this is currently implemented with an enum in a dumb way to handle limitation of Rust's
    // lifetime inference. Once these limitations are fixed (non-lexical lifetimes) I can fix this.
    enum Action { FunctionCall, IndexExpression, Infix(i32) }
    let mut expr = parse_prefix(ps)?;
    while ps.has_tokens() {
      let action;
      { // open scope to scope-limit lifetime of token
        let t = ps.peek()?;
        if t.token_type == TokenType::Syntax && TERMINATING_SYNTAX.contains(t.string.as_ref()) {
          break;
        }
        else if t.token_type == TokenType::Syntax && (t.string.as_ref() == "(" || t.string.as_ref() == "[") {
          let next_precedence = operator_precedence(&t.string)?;
          if next_precedence > precedence {
            action = if t.string.as_ref() == "(" {
              Action::FunctionCall
            }
            else {
              Action::IndexExpression
            };
          }
          else {
            break;
          }
        }
        else if t.token_type == TokenType::Syntax && INFIX_OPERATORS.contains(t.string.as_ref()) {
          let next_precedence = operator_precedence(&t.string)?;
          if next_precedence > precedence {
            action = Action::Infix(next_precedence);
          }
          else {
            break;
          }
        }
        else {
          // TODO: this seems crazy
          //return Err(format!("Unexpected token '{}' of type '{:?}' (PRATT)", t.string, t.token_type));
          break;
        }
      };
      match action {
        Action::FunctionCall => expr = parse_function_call(ps, expr)?,
        Action::IndexExpression => expr = parse_index_expression(ps, expr)?,
        Action::Infix(next_precedence) => expr = parse_infix(ps, expr, next_precedence)?,
      }
    }
    Ok(expr)
  }

  fn parse_index_expression(ps : &mut ParseState, indexee_expr : ExprId) -> Result<ExprId, Error> {
    let start = ps.get_loc(indexee_expr).start;
    ps.expect_string("[")?;
    let indexing_expr = parse_expression(ps)?;
    ps.expect_string("]")?;
    let args = vec!(indexee_expr, indexing_expr);
    Ok(ps.add_tree(INDEX, args, start))
  }

  fn parse_function_call(ps : &mut ParseState, function_expr : ExprId) -> Result<ExprId, Error> {
    let start = ps.get_loc(function_expr).start;
    ps.expect_string("(")?;
    let mut exprs = vec!(function_expr);
    loop {
      exprs.push(parse_expression(ps)?);
      if !ps.accept_string(",") {
        break;
      }
    }
    ps.expect_string(")")?;
    Ok(ps.add_tree(CALL, exprs, start))
  }

  fn parse_prefix(ps : &mut ParseState) -> Result<ExprId, Error> {
    let start = ps.peek_marker();
    // if the next token is a prefix operator
    let prefix_operator = {
      // TODO: fix this with non-lexical lifetimes at some point
      let t = ps.peek()?;
      if t.token_type == TokenType::Syntax && PREFIX_OPERATORS.contains(t.string.as_ref()) {
        Some(t.string.clone())
      }
      else { None }
    };
    // then parse a prefix pattern
    if let Some(operator) = prefix_operator {
      ps.expect_type(TokenType::Syntax)?;
      let expr = parse_expression_term(ps)?;
      let args = vec![ps.add_symbol(operator, start), expr];
      Ok(ps.add_tree(CALL, args, start))
    }
    // else assume it's an expression term
    else {
      parse_expression_term(ps)
    }
  }

  fn parse_infix(ps : &mut ParseState, left_expr : ExprId, precedence : i32) -> Result<ExprId, Error> {
    let infix_start = ps.get_loc(left_expr).start;
    let operator_start = ps.peek_marker();
    let operator_str = ps.pop_type(TokenType::Syntax)?.string.clone();
    let operator = ps.add_symbol(operator_str.clone(), operator_start);
    let right_expr = pratt_parse(ps, precedence)?;
    let args = vec!(operator, left_expr, right_expr);
    if SPECIAL_OPERATORS.contains(operator_str.as_ref()) {
      Ok(ps.add_tree(operator_str, args, infix_start))
    }
    else {
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
    error!(t.loc, "Failed to parse float from '{}'", t.string)
  }
}

fn parse_syntax(ps : &mut ParseState) -> Result<ExprId, Error> {
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
      let a = parse_expression(ps)?;
      ps.expect_string(")")?;
      Ok(a)
    }
    _ => error!(ps.peek()?.loc, "Unexpected syntax '{}'", ps.peek()?.string),
  }
}

fn parse_simple_string(ps : &mut ParseState, t : TokenType) -> Result<ExprId, Error> {
  let start = ps.peek_marker();
  let s = ps.pop_type(t)?.string.clone();
  Ok(ps.add_symbol(s, start))
}

fn parse_simple_symbol(ps : &mut ParseState) -> Result<ExprId, Error> {
  parse_simple_string(ps, TokenType::Symbol)
}

fn parse_type(ps : &mut ParseState) -> Result<ExprId, Error> {
  parse_simple_symbol(ps)
}

fn parse_fun(ps : &mut ParseState) -> Result<ExprId, Error> {
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

fn parse_let(ps : &mut ParseState) -> Result<ExprId, Error> {
  let start = ps.peek_marker();
  ps.expect_string("let")?;
  let var_name = parse_simple_symbol(ps)?;
  ps.expect_string("=")?;
  let initialiser = parse_expression(ps)?;
  Ok(ps.add_tree(LET, vec!(var_name, initialiser), start))
}

fn parse_if(ps : &mut ParseState) -> Result<ExprId, Error> {
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

fn parse_while(ps : &mut ParseState) -> Result<ExprId, Error> {
  let start = ps.peek_marker();
  ps.expect_string("while")?;
  let conditional = parse_expression(ps)?;
  ps.expect_string("{")?;
  let loop_block = parse_block(ps)?;
  ps.expect_string("}")?;
  let args = vec!(conditional, loop_block);
  Ok(ps.add_tree(WHILE, args, start))
}

fn parse_struct_definition(ps : &mut ParseState) -> Result<ExprId, Error> {
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

fn parse_struct_instantiate(ps : &mut ParseState) -> Result<ExprId, Error> {
  let start = ps.peek_marker();
  let struct_name = parse_simple_symbol(ps)?;
  ps.expect_string("{")?;
  let mut args = vec!(struct_name);
  'outer: loop {
    'inner: loop {
      if !ps.has_tokens() || ps.peek()?.string.as_ref() == "}" {
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
  ps.expect_string("}")?;
  Ok(ps.add_tree(STRUCT_INSTANTIATE, args, start))
}

fn parse_keyword_term(ps : &mut ParseState) -> Result<ExprId, Error> {
  match ps.peek()?.string.as_ref() {
    "let" => parse_let(ps),
    "fun" => parse_fun(ps),
    "if" => parse_if(ps),
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
      error!(t.loc, "Encountered unexpected keyword '{}'. This keyword is not supported here.", t.string)
    }
  }
}

fn parse_symbol_term(ps : &mut ParseState) -> Result<ExprId, Error> {
  let is_struct =
    if let Ok(t) = ps.peek_ahead(1) { t.string.as_ref() == "{" } else { false };
  if is_struct {
    parse_struct_instantiate(ps)
  }
  else{
    // else assume it's just a symbol reference
    parse_simple_symbol(ps)
  }
}

fn parse_expression_term(ps : &mut ParseState) -> Result<ExprId, Error> {
  match ps.peek()?.token_type {
    TokenType::Symbol => parse_symbol_term(ps),
    TokenType::Keyword => parse_keyword_term(ps),
    TokenType::Syntax => parse_syntax(ps),
    TokenType::FloatLiteral => {
      let start = ps.peek_marker();
      let f = ExprTag::LiteralFloat(parse_float(ps)?);
      Ok(ps.add_leaf(f, start))
    }
  }
}

fn parse_block(ps : &mut ParseState) -> Result<ExprId, Error> {
  let start = ps.peek_marker();
  let mut exprs = vec!();
  'outer: loop {
    exprs.push(parse_expression(ps)?);
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
  }
  Ok(ps.add_tree(BLOCK, exprs, start))
}

pub fn parse(tokens : Vec<Token>) -> Result<Ast, Error> {
  let mut ps = ParseState::new(tokens);
  let e = parse_block(&mut ps)?;
  if ps.has_tokens() {
    let t = ps.peek()?;
    return error!(t.loc, "Unexpected token '{}' of type '{:?}'", t.string, t.token_type);
  }
  let ast = Ast { root_id: e, exprs: ps.exprs };
  return Ok(ast);
}

#[test]
fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parse(tokens);
  println!("{:?}", ast);
}
