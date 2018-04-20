
use std::str::Chars;
use std::i32;

enum TokenType {
  Symbol, Syntax, FloatLiteral
}

struct TextLocation {
  start : i32,
  length : i32,
  line : i32,
}

struct Token {
  s : String,
  tkn_type : TokenType,
  loc : TextLocation,
}

struct CStream <'l> {
  chars : Chars<'l>,
  pos : i32,
  line : i32,
  tokens : Vec<Token>,
}

fn lex(code : &str) -> i32 {
  let a = code.chars().zip(0..i32::MAX);
  let mut cs = CStream {
    chars: code.chars().zip(0, i32::MAX),
    pos: 0, line : 0,
    tokens: vec!(),
  };
  0
}

#[test]
fn test () {
  let code = "3 + 4 * 10";
  let ts = lex(code);
  println!("{:?}", ts);
}