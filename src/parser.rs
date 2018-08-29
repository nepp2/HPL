
use lexer;
use lexer::{Token, TokenType};
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

#[derive(PartialEq, Debug, Clone)]
pub enum Expr {
  Expr { symbol : String, args : Vec<Expr> },
  Symbol(String),
  LiteralFloat(f32),
  LiteralBool(bool),
}

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct TokenStream {
  tokens : Vec<Token>,
  pos : usize,
  // TODO: these can be globals I think, with the help of some macro
  terminating_syntax : HashSet<&'static str>,
  infix_operators : HashSet<&'static str>,
  prefix_operators : HashSet<&'static str>,
}

impl TokenStream {

  fn new(tokens : Vec<Token>) -> TokenStream {
    fn to_hashset(syntax : &[&'static str]) -> HashSet<&'static str> {
      let mut set = HashSet::new();
      for &s in syntax {
        set.insert(s);
      }
      set
    }

    TokenStream {
      tokens,
      pos: 0,
      terminating_syntax: to_hashset(TERMINATING_SYNTAX),
      infix_operators: to_hashset(INFIX_SYNTAX),
      prefix_operators: to_hashset(PREFIX_SYNTAX),
    }
  }

  fn has_tokens(&self) -> bool {
    self.pos < self.tokens.len()
  }

  fn peek(&self) -> Result<&Token, String> {
    if self.has_tokens() {
      Ok(&self.tokens[self.pos])
    }
    else {
      Err("Expected token. Found nothing.".to_string())
    }
  }

  fn pop_type(&mut self, token_type : TokenType) -> Result<&Token, String> {
    self.expect_type(token_type)?;
    Ok(&self.tokens[self.pos-1])
  }

  fn skip(&mut self) {
    self.pos += 1;
  }

  fn accept_string(&mut self, string : &str) -> bool {
    let accept = {
      if let Ok(t) = self.peek() {
        t.string == string
      }
      else { false }
    };
    if accept { self.skip() }
    accept
  }

  fn expect_string(&mut self, string : &str) -> Result<(), String> {
    {
      let t = self.peek();
      if let Ok(t) = t {
        if t.string != string {
          return Err(format!("Expected token '{}', found token '{}'", string, t.string));
        }
      }
      else {
        return Err(format!("Expected token '{}', found nothing.", string));
      }
    }
    self.skip();
    Ok(())
  }

  fn expect_type(&mut self, token_type : TokenType) -> Result<(), String> {
    {
      let t = self.peek();
      if let Ok(t) = t {
        if t.token_type != token_type {
          return Err(format!("Expected token of type '{:?}', found token '{:?}'", token_type, t.token_type));
        }
      }
      else {
        return Err(format!("Expected token of type '{:?}', found nothing.", token_type));
      }
    }
    self.skip();
    Ok(())
  }
}

const TERMINATING_SYNTAX : &'static [&'static str] = &["}", ")", "]", ";", ","];
const PREFIX_SYNTAX : &'static [&'static str] = &["-", "!"];
const INFIX_SYNTAX : &'static [&'static str] =
  &["==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
    "<", ">", "=", "+", "-", "*", "/", "|", "&", "^"];

fn parse_expression(ts : &mut TokenStream) -> Result<Expr, String> {
  
  fn operator_precedence(s : &str) -> Result<i32, String> {
    let p =
      match s {
        "=" => 1,
        "+=" => 1,
        ">" => 2,
        "<" => 2,
        "==" => 2,
        "&&" => 3,
        "||" => 3,
        "+" => 4,
        "-" => 4,
        "*" => 5,
        "/" => 5,
        "(" => 6,
        "[" => 6,
        _ => return Err(format!("Unexpected operator '{}'", s)),
      };
    Ok(p)
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ts : &mut TokenStream, precedence : i32) -> Result<Expr, String> {
    // TODO: this is currently implemented with an enum in a dumb way to handle limitation of Rust's
    // lifetime inference. Once these limitations are fixed (non-lexical lifetimes) I can fix this.
    enum Action { FunctionCall, IndexExpression, Infix(i32) }
    let mut expr = parse_prefix(ts)?;
    while ts.has_tokens() {
      let action;
      { // open scope to scope-limit lifetime of token
        let t = ts.peek()?;
        if t.token_type == TokenType::Syntax && ts.terminating_syntax.contains(t.string.as_str()) {
          break;
        }
        else if t.token_type == TokenType::Syntax && (t.string == "(" || t.string == "[") {
          let next_precedence = operator_precedence(&t.string)?;
          if next_precedence > precedence {
            action = if t.string == "(" {
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
        else if t.token_type == TokenType::Syntax && ts.infix_operators.contains(t.string.as_str()) {
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
        Action::FunctionCall => expr = parse_function_call(ts, expr)?,
        Action::IndexExpression => expr = parse_index_expression(ts, expr)?,
        Action::Infix(next_precedence) => expr = parse_infix(ts, expr, next_precedence)?,
      }
    }
    Ok(expr)
  }

  fn parse_index_expression(ts : &mut TokenStream, indexee_expr : Expr) -> Result<Expr, String> {
    ts.expect_string("[")?;
    let indexing_expr = parse_expression(ts)?;
    ts.expect_string("]")?;
    let args = vec!(indexee_expr, indexing_expr);
    Ok(Expr::Expr { symbol: "index".to_string(), args } )
  }

  fn parse_function_call(ts : &mut TokenStream, function_expr : Expr) -> Result<Expr, String> {
    ts.expect_string("(")?;
    let mut exprs = vec!(function_expr);
    loop {
      exprs.push(parse_expression(ts)?);
      if !ts.accept_string(",") {
        break;
      }
    }
    ts.expect_string(")")?;
    Ok(Expr::Expr { symbol: "call".to_string(), args: exprs } )
  }

  fn parse_prefix(ts : &mut TokenStream) -> Result<Expr, String> {
    // TODO: fix this with non-lexical lifetimes at some point
    let (is_prefix, operator) = {
      let t = ts.peek()?;
      let b = t.token_type == TokenType::Syntax && ts.prefix_operators.contains(t.string.as_str());
      (b, if b { t.string.clone()} else { String::new() })
    };
    if is_prefix {
      ts.expect_type(TokenType::Syntax)?;
      let expr = parse_expression_term(ts)?;
      Ok(Expr::Expr{ symbol: "call".to_string(), args: vec!(Expr::Symbol(operator), expr) })
    }
    else {
      parse_expression_term(ts)
    }
  }

  fn parse_infix(ts : &mut TokenStream, left_expr : Expr, precedence : i32) -> Result<Expr, String> {
    let operator = ts.pop_type(TokenType::Syntax)?.string.clone();
    let right_expr = pratt_parse(ts, precedence)?;
    if operator.as_str() == "=" {
      let args = vec!(left_expr, right_expr);
      Ok(Expr::Expr { symbol: "assign".to_string(), args })
    }
    else if operator.as_str() == "+=" {
      let args = vec!(left_expr, right_expr, Expr::Symbol("+".to_string()));
      Ok(Expr::Expr { symbol: "assign_modify".to_string(), args })
    }
    else {
      let args = vec!(Expr::Symbol(operator), left_expr, right_expr);
      Ok(Expr::Expr { symbol: "call".to_string(), args })
    }
  }

  pratt_parse(ts, 0)
}

fn parse_float(ts : &mut TokenStream) -> Result<f32, String> {
  let t = ts.pop_type(TokenType::FloatLiteral)?;
  if let Ok(f) = f32::from_str(&t.string) {
    Ok(f)
  }
  else {
    Err(format!("Failed to parse float from '{}'", t.string))
  }
}

fn parse_syntax(ts : &mut TokenStream) -> Result<Expr, String> {
  match ts.peek()?.string.as_str() {
    "[" => {
      ts.expect_string("[")?;
      let mut exprs = vec!();
      loop {
        if ts.peek()?.string == "]" {
          break;
        }
        exprs.push(parse_expression(ts)?);
        if ts.peek()?.string == "," {
          ts.skip()
        }
        else {
          break;
        }
      }
      ts.expect_string("]")?;
      Ok(Expr::Expr { symbol: "literal_array".to_string(), args: exprs })
    }
    "(" => {
      ts.expect_string("(")?;
      let a = parse_expression(ts)?;
      ts.expect_string(")")?;
      Ok(a)
    }
    _ => Err(format!("Unexpected syntax '{}' at position '{:?}'", ts.peek()?.string, ts.peek()?.loc)),
  }
}

fn parse_fun(ts : &mut TokenStream) -> Result<Expr, String> {
  ts.expect_string("fun")?;
  let fun_name = ts.pop_type(TokenType::Symbol)?.string.clone();
  let mut arg_names = vec!();
  ts.expect_string("(")?;
  loop {
    if ts.peek()?.token_type != TokenType::Symbol {
      break;
    }
    let arg_name = ts.pop_type(TokenType::Symbol)?.string.to_string();
    arg_names.push(Expr::Symbol(arg_name));
    if ts.peek()?.string == "," {
      ts.skip();
    }
    else {
      break;
    }
  }
  ts.expect_string(")")?;
  ts.expect_string("{")?;
  let function_block = parse_block(ts)?;
  ts.expect_string("}")?;
  let fun_symbol = Expr::Symbol(fun_name);
  let args_expr =
    Expr::Expr {
      symbol: "args".to_string(),
      args: arg_names,
    };
  let fun_expr =
    Expr::Expr{
      symbol: "fun".to_string(),
      args: vec!(fun_symbol, args_expr, function_block),
    };
  Ok(fun_expr)
}

fn parse_let(ts : &mut TokenStream) -> Result<Expr, String> {
  ts.expect_string("let")?;
  let var_name = ts.pop_type(TokenType::Symbol)?.string.clone();
  ts.expect_string("=")?;
  let initialiser = parse_expression(ts)?;
  let var_symbol = Expr::Symbol(var_name);
  Ok(Expr::Expr{ symbol: "let".to_string(), args: vec!(var_symbol, initialiser)})
}

fn parse_if(ts : &mut TokenStream) -> Result<Expr, String> {
  ts.expect_string("if")?;
  let conditional = parse_expression(ts)?;
  ts.expect_string("{")?;
  let then_block = parse_block(ts)?;
  ts.expect_string("}")?;
  let mut args = vec!(conditional, then_block);
  if ts.accept_string("else") {
    ts.expect_string("{")?;
    let else_block = parse_block(ts)?;
    ts.expect_string("}")?;
    args.push(else_block);
  }
  Ok(Expr::Expr{ symbol: "if".to_string(), args })
}

fn parse_while(ts : &mut TokenStream) -> Result<Expr, String> {
  ts.expect_string("while")?;
  let conditional = parse_expression(ts)?;
  ts.expect_string("{")?;
  let loop_block = parse_block(ts)?;
  ts.expect_string("}")?;
  let args = vec!(conditional, loop_block);
  Ok(Expr::Expr{ symbol: "while".to_string(), args })
}

fn parse_keyword_term(ts : &mut TokenStream) -> Result<Expr, String> {
  match ts.peek()?.string.as_str() {
    "let" => parse_let(ts),
    "fun" => parse_fun(ts),
    "if" => parse_if(ts),
    "break" => {
      ts.expect_string("break")?;
      Ok(Expr::Symbol("break".to_string()))
    }
    "while" => parse_while(ts),
    "true" => {
      ts.expect_string("true")?;
      Ok(Expr::LiteralBool(true))
    }
    "false" => {
      ts.expect_string("false")?;
      Ok(Expr::LiteralBool(false))
    }
    _ => Err(format!("Encountered unexpected keyword '{}'. This keyword is not supported here.", ts.peek()?.string)),
  }
}

fn parse_symbol(ts : &mut TokenStream) -> Result<Expr, String> {
  let symbol = Expr::Symbol(ts.pop_type(TokenType::Symbol)?.string.clone());
  // TODO
  if ts.has_tokens() {
    let mut symbols = vec!();
    while ts.peek()?.string.as_str() == "." {
      ts.skip();
      symbols.push(Expr::Symbol(ts.pop_type(TokenType::Symbol)?.string.clone()));
    }
    if symbols.len() > 0 {
      symbols.insert(0, symbol);
      return Ok(Expr::Expr { symbol: "symbol_chain".to_string(), args: symbols });
    }
  }
  return Ok(symbol);
}

fn parse_expression_term(ts : &mut TokenStream) -> Result<Expr, String> {
  match ts.peek()?.token_type {
    TokenType::Symbol => parse_symbol(ts),
    TokenType::Keyword => parse_keyword_term(ts),
    TokenType::Syntax => parse_syntax(ts),
    TokenType::FloatLiteral => Ok(Expr::LiteralFloat(parse_float(ts)?)),
  }
}

fn parse_block(ts : &mut TokenStream) -> Result<Expr, String> {
  let mut exprs = vec!();
  'outer: loop {
    exprs.push(parse_expression(ts)?);
    'inner: loop {
      if !ts.has_tokens() || ts.peek()?.string == "}" {
        break 'outer;
      }
      if ts.peek()?.string != ";" {
        break 'inner;
      }
      ts.skip(); // skip the semicolon
    }
  }
  if exprs.len() == 1 {
    Ok(exprs.pop().unwrap())
  }
  else {
    Ok(Expr::Expr { symbol: "block".to_string(), args: exprs })
  }
}

pub fn parse(tokens : Vec<Token>) -> Result<Expr, String> {
  let mut ts = TokenStream::new(tokens);
  let e = parse_block(&mut ts)?;
  if ts.has_tokens() {
    let t = ts.peek()?;
    return Err(format!("Unexpected token '{}' of type '{:?}'", t.string, t.token_type));
  }
  return Ok(e);
}

#[test]
fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parse(tokens);
  println!("{:?}", ast);
}
