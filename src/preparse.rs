
use lexer;
use lexer::{Token, TokenType};

// TODO: this might be better implemented with a ring buffer (or just a backwards vec)
struct TokenStream {
  tokens : Vec<Token>,
  pos : usize,
}

impl TokenStream {

  fn new(tokens : Vec<Token>) -> TokenStream {
    TokenStream {
      tokens,
      pos: 0,
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

#[derive(PartialEq, Debug)]
pub enum Arg {
  Expr(Expr),
  Symbol(String),
  Literal(f32),
}

#[derive(PartialEq, Debug)]
pub struct Expr {
  symbol : String,
  args : Vec<Arg>,
}

const TERMINATING_SYNTAX : &'static [&'static str] = &["}", ")", "]", ";", ","];


#[derive(Debug)]
pub enum PreparseError {
  Incomplete, Error(String)
}

fn parse_expr(ts : &mut TokenStream) -> Result<Expr, PreparseError> {
  // if open syntax
  //
  panic!();
}

fn wrap_err<T>(r : Result<T, String>) -> Result<T, PreparseError> {
  match r {
    Ok(x) => Ok(x),
    Err(s) => Err(PreparseError::Error(s)),
  }
}

fn err<T>(s : String) -> Result<T, PreparseError> {
  Err(PreparseError::Error(s))
}

pub fn preparse(tokens : Vec<Token>) -> Result<Expr, PreparseError> {
  let mut ts = TokenStream::new(tokens);
  let e = parse_expr(&mut ts)?;
  if ts.has_tokens() {
    let t = wrap_err(ts.peek())?;
    return err(format!("Unexpected token '{}' of type '{:?}'", t.string, t.token_type));
  }
  return Ok(e);
}

fn expr(s : &str, args : Vec<Arg>) -> Expr {
  Expr { symbol: s.to_string(), args }
}

#[test]
fn test_preparse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = preparse(tokens).unwrap();

  use self::Arg::*;

  let three_plus_4 = expr("+", vec!(Literal(3.0), Literal(4.0)));
  let expected_ast = expr("*", vec!(Expr(three_plus_4), Literal(10.0)));

  assert_eq!(ast, expected_ast);
}

