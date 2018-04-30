
use lexer::{Token, TokenType};
use std::collections::HashSet;
use std::f32;
use std::str::FromStr;

/*

TODO: a lot of string copying happens in this file, which isn't great.
I guess garbage collection is actually pretty good for strings. A lot of
them could be static, but I'd have to fiddle the types a lot to do something
about that. I could also consume the tokens for way more efficiency, but I'd
have to change a lot of code.

TODO: Question. does creating a new string from a static string actually allocate?
*/


#[derive(Debug)]
pub enum Expr {
  InfixOp(Box<Expr>, String, Box<Expr>),
  PrefixOp(String, Box<Expr>),
  LiteralFloat(f32),
  FunctionCall { func : Box<Expr>, args : Vec<Expr> }
}

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct TokenStream {
  tokens : Vec<Token>,
  pos : usize,
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
        ">" => 1,
        "<" => 1,
        "+" => 2,
        "-" => 2,
        "*" => 3,
        "/" => 3,
        "(" => 4,
        _ => return Err(format!("Unexpected operator '{}'", s)),
      };
    Ok(p)
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ts : &mut TokenStream, precedence : i32) -> Result<Expr, String> {
    // TODO: this is currently implemented with an enum in a dumb way to handle limitation of Rust's
    // lifetime inference. Once these limitations are fixed (non-lexical lifetimes) I can fix this.
    enum Action { FunctionCall, Infix(i32), Break }
    let mut expr = parse_prefix(ts)?;
    while ts.has_tokens() {
      let mut action = Action::Break;
      { // open scope to scope-limit lifetime of token
        let t = ts.peek()?;
        if t.token_type == TokenType::Syntax && ts.terminating_syntax.contains(t.string.as_str()) {
          // this case should break
        }
        else if t.token_type == TokenType::Syntax && t.string == "(" {
          let next_precedence = operator_precedence(&t.string)?;
          if next_precedence > precedence {
            action = Action::FunctionCall;
          }
        }
        else if t.token_type == TokenType::Syntax && ts.infix_operators.contains(t.string.as_str()) {
          let next_precedence = operator_precedence(&t.string)?;
          if next_precedence > precedence {
            action = Action::Infix(next_precedence);
          }
        }
      };
      match action {
        Action::Break => break,
        Action::FunctionCall => expr = parse_function_call(ts, expr)?,
        Action::Infix(next_precedence) => expr = parse_infix(ts, expr, next_precedence)?,
      }
    }
    Ok(expr)
  }

  fn parse_function_call(ts : &mut TokenStream, function_expr : Expr) -> Result<Expr, String> {
    ts.expect_string("(")?;
    let mut exprs = vec!();
    loop {
      exprs.push(parse_expression(ts)?);
      if !ts.accept_string(",") {
        break;
      }
    }
    ts.expect_string(")")?;
    Ok(Expr::FunctionCall{ func: Box::new(function_expr), args: exprs })
  }

  fn parse_prefix(ts : &mut TokenStream) -> Result<Expr, String> {
    // TODO: fix this with non-lexical lifetimes at some point
    let (is_prefix, s) = {
      let t = ts.peek()?;
      let b = t.token_type == TokenType::Syntax && ts.prefix_operators.contains(t.string.as_str());
      (b, if b { t.string.clone()} else { String::new() })
    };
    if is_prefix {
      ts.expect_type(TokenType::Syntax)?;
      let expr = parse_expression_term(ts)?;
      Ok(Expr::PrefixOp(s, Box::new(expr)))
    }
    else {
      parse_expression_term(ts)
    }
  }

  fn parse_infix(ts : &mut TokenStream, left_expr : Expr, precedence : i32) -> Result<Expr, String> {
    let string = ts.pop_type(TokenType::Syntax)?.string.clone();
    let right_expr = pratt_parse(ts, precedence)?;
    Ok(Expr::InfixOp(Box::new(left_expr), string, Box::new(right_expr)))
  }

  pratt_parse(ts, 0)
}

fn parse_float(ts : &mut TokenStream) -> Result<Expr, String> {
  let t = ts.pop_type(TokenType::FloatLiteral)?;
  if let Ok(f) = f32::from_str(&t.string) {
    Ok(Expr::LiteralFloat(f))
  }
  else {
    Err(format!("Failed to parse float from '{}'", t.string))
  }
}

fn parse_syntax(ts : &mut TokenStream) -> Result<Expr, String> {
  let paren = ts.peek()?.string == "(";
  if paren {
    ts.expect_string("(")?;
    let e = parse_expression(ts)?;
    ts.expect_string(")")?;
    Ok(e)
  }
  else {
    Err(format!("Unexpected syntax '{}'", ts.peek()?.string))
  }
}

fn parse_expression_term(ts : &mut TokenStream) -> Result<Expr, String> {
  let token_type = ts.peek()?.token_type;
  match token_type {
    TokenType::Symbol => Err("Tried to parse symbol. Symbols are not yet supported.".to_string()),
    TokenType::Keyword => Err("Tried to parse keyword. Keywords are not yet supported.".to_string()),
    TokenType::Syntax => parse_syntax(ts),
    TokenType::FloatLiteral => parse_float(ts),
  }
}

pub fn parse(tokens : Vec<Token>) -> Result<Expr, String> {
  let mut ts = TokenStream::new(tokens);
  parse_expression(&mut ts)
}

#[test]
fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parse(tokens);
  println!("{:?}", ast);
}
