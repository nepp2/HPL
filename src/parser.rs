
use lexer;
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

  fn peek(&self) -> &Token {
    &self.tokens[self.pos]
  }

  fn pop_type(&mut self, token_type : TokenType) -> &Token {
    self.expect_type(token_type);
    &self.tokens[self.pos-1]
  }

  fn skip(&mut self) {
    self.pos += 1;
  }

  fn accept_string(&mut self, string : &str) -> bool {
    let accept = {
      let t = self.peek();
      t.string == string
    };
    if accept { self.skip() }
    accept
  }

  fn expect_string(&mut self, string : &str) {
    {
      let t = self.peek();
      if t.string != string {
        panic!("Expected token '{}', found token '{}'", string, t.string);
      }
    }
    self.skip();
  }

  fn expect_type(&mut self, token_type : TokenType) {
    {
      let t = self.peek();
      if t.token_type != token_type {
        panic!("Expected token of type '{:?}', found token '{:?}'", token_type, t.token_type);
      }
    }
    self.skip();
  }
}

const TERMINATING_SYNTAX : &'static [&'static str] = &["}", ")", "]", ";", ","];
const PREFIX_SYNTAX : &'static [&'static str] = &["-", "!"];
const INFIX_SYNTAX : &'static [&'static str] =
  &["==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||", "&&",
    "<", ">", "=", "+", "-", "*", "/", "|", "&", "^"];

fn parse_expression(ts : &mut TokenStream) -> Expr {
  
  fn operator_precedence(s : &str) -> i32 {
    match s {
      ">" => 1,
      "<" => 1,
      "+" => 2,
      "-" => 2,
      "*" => 3,
      "/" => 3,
      "(" => 4,
      _ => panic!("Unexpected operator"),
    }
  }

  /// This expression parser is vaguely based on some blogs about pratt parsing.
  fn pratt_parse(ts : &mut TokenStream, precedence : i32) -> Expr {
    // TODO: this is currently implemented with an enum in a dumb way to handle limitation of Rust's
    // lifetime inference. Once these limitations are fixed (non-lexical lifetimes) I can fix this.
    enum Action { FunctionCall, Infix(i32), Break }
    let mut expr = parse_prefix(ts);
    while ts.has_tokens() {
      let mut action = Action::Break;
      { // open scope to scope-limit lifetime of token
        let t = ts.peek();
        if t.token_type == TokenType::Syntax && ts.terminating_syntax.contains(t.string.as_str()) {
          // this case should break
        }
        else if t.token_type == TokenType::Syntax && t.string == "(" {
          let next_precedence = operator_precedence(&t.string);
          if next_precedence > precedence {
            action = Action::FunctionCall;
          }
        }
        else if t.token_type == TokenType::Syntax && ts.infix_operators.contains(t.string.as_str()) {
          let next_precedence = operator_precedence(&t.string);
          if next_precedence > precedence {
            action = Action::Infix(next_precedence);
          }
        }
      };
      match action {
        Action::Break => break,
        Action::FunctionCall => expr = parse_function_call(ts, expr),
        Action::Infix(next_precedence) => expr = parse_infix(ts, expr, next_precedence),
      }
    }
    expr
  }

  fn parse_function_call(ts : &mut TokenStream, function_expr : Expr) -> Expr {
    ts.expect_string("(");
    let mut exprs = vec!();
    loop {
      exprs.push(parse_expression(ts));
      if !ts.accept_string(",") {
        break;
      }
    }
    ts.expect_string(")");
    Expr::FunctionCall{ func: Box::new(function_expr), args: exprs }
  }

  fn parse_prefix(ts : &mut TokenStream) -> Expr {
    // TODO: fix this with non-lexical lifetimes at some point
    let (is_prefix, s) = {
      let t = ts.peek();
      let b = t.token_type == TokenType::Syntax && ts.prefix_operators.contains(t.string.as_str());
      (b, if b { t.string.clone()} else { String::new() })
    };
    if is_prefix {
      ts.expect_type(TokenType::Syntax);
      let expr = parse_expression_term(ts);
      Expr::PrefixOp(s, Box::new(expr))
    }
    else {
      parse_expression_term(ts)
    }
  }

  fn parse_infix(ts : &mut TokenStream, left_expr : Expr, precedence : i32) -> Expr {
    let string = ts.pop_type(TokenType::Syntax).string.clone();
    let right_expr = pratt_parse(ts, precedence);
    Expr::InfixOp(Box::new(left_expr), string, Box::new(right_expr))
  }

  pratt_parse(ts, 0)
}

fn parse_float(ts : &mut TokenStream) -> Expr {
  let t = ts.pop_type(TokenType::FloatLiteral);
  Expr::LiteralFloat(f32::from_str(&t.string).unwrap())
}

fn parse_syntax(ts : &mut TokenStream) -> Expr {
  let paren = ts.peek().string == "(";
  if paren {
    ts.expect_string("(");
    let e = parse_expression(ts);
    ts.expect_string(")");
    e
  }
  else {
    panic!("Unexpected syntax '{}'", ts.peek().string)
  }
}

fn parse_expression_term(ts : &mut TokenStream) -> Expr {
  let token_type = ts.peek().token_type;
  match token_type {
    TokenType::Symbol => panic!(),
    TokenType::Syntax => parse_syntax(ts),
    TokenType::FloatLiteral => parse_float(ts),
  }
}

pub fn parse(tokens : Vec<Token>) -> Expr {
  let mut ts = TokenStream::new(tokens);
  parse_expression(&mut ts)
}

pub fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code);
  let ast = parse(tokens);
  println!("{:?}", ast);
}
