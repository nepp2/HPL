
use std::str::Chars;
use std::i32;

#[derive(Debug)]
enum TokenType {
  Symbol, Syntax, FloatLiteral
}

#[derive(Debug)]
struct TextLocation {
  start : u32,
  length : u32,
  line : u32,
}

#[derive(Debug)]
pub struct Token {
  string : String,
  token_type : TokenType,
  loc : TextLocation,
}

struct CStream {
  chars : Vec<char>,
  loc : StreamLocation,
  tokens : Vec<Token>,
}

#[derive(Clone, Copy)]
struct StreamLocation {
  pos : usize,
  line : usize,
}

impl CStream {
  fn has_chars(&self) -> bool {
    self.loc.pos < self.chars.len()
  }

  fn peek(&self) -> char { self.chars[self.loc.pos] }

  fn skip_char(&mut self){
    self.loc.pos += 1;
  }

  fn complete_token(&mut self, start_loc : StreamLocation, string : String, token_type : TokenType) {
    let len = self.loc.pos - start_loc.pos;
    let loc = TextLocation {
      start: start_loc.pos as u32,
      length: len as u32,
      line: start_loc.line as u32,
    };
    let t = Token {
      string,
      token_type: token_type,
      loc : loc,
    };
    self.tokens.push(t);
  }

  fn handle_newline(&mut self, operation : &Fn(&mut CStream)) -> bool {
    if self.peek() == '\n' {
      operation(self);
      self.loc.line += 1;
      true
    }
    else { false }
  }

  fn is_symbol_number(&self) -> bool {
    let c = self.peek();
    c >= '0' && c <= '9'
  }

  fn iter_char_while(&mut self, condition : &Fn(&CStream) -> bool, operation : &mut FnMut(&mut CStream)) {
    while self.loc.pos < self.chars.len() {
      if condition(self) {
        operation(self);
      }
      else{
        break;
      }
    }
  }

  fn skip_char_while (&mut self, condition : &Fn(&CStream) -> bool) {
    self.iter_char_while(condition, &mut CStream::skip_char);
  }

  fn append_char(&mut self, string : &mut String) {
    let c = self.peek();
    string.push(c);
    self.skip_char();
  }

  fn append_char_while(&mut self, string : &mut String, condition : &Fn(&CStream) -> bool) {
    self.iter_char_while(condition, &mut |cs : &mut CStream| { cs.append_char(string) });
  }

  fn parse_number(&mut self) -> bool {
    if self.is_symbol_number() {
      let start_loc = self.loc;
      let mut string = String::new();
      self.append_char_while(&mut string, &CStream::is_symbol_number);
      if self.has_chars() && self.peek() == '.' {
        self.append_char(&mut string);
        self.append_char_while(&mut string, &CStream::is_symbol_number);
      }
      self.complete_token(start_loc, string, TokenType::FloatLiteral);
      true
    }
    else { false }
  }

  fn is_space_char(&self) -> bool {
    let c = self.peek();
    c.is_whitespace()
  }

  fn skip_space(&mut self) -> bool {
    if self.is_space_char() {
      self.skip_char_while(&CStream::is_space_char);
      true
    }
    else { false }
  }

  fn peek_string(&self, s : &str) -> bool {
    let mut i = 0;
    for c in s.chars() {
      let index = self.loc.pos + i;
      if index >= self.chars.len() || self.chars[index] != c {
        return false;
      }
      i += 1;
    }
    return true;
  }

  fn parse_string(&mut self, s : &str, token_type : TokenType) -> bool {
    if self.peek_string(s) {
      let start_loc = self.loc;
      for _ in s.chars() {
        self.skip_char();
      }
      self.complete_token(start_loc, s.to_string(), token_type);
      return true;
    }
    return false;
  }

  const SYNTAX : &'static [&'static str] =
    &["==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||",
      "&&", "{", "}", "(", ")", "[", "]", "<", ">", ";", ":", ",",
      ".", "=", "+", "-", "*", "/", "?", "|", "&", "^", "!"];

  fn parse_syntax(&mut self) -> bool {
    for s in CStream::SYNTAX {
      if self.parse_string(s, TokenType::Syntax) {
        return true;
      }
    }
    return false;
  }
}

pub fn lex(code : &str) -> Vec<Token> {
  let mut cs = CStream {
    chars: code.chars().collect(),
    loc : StreamLocation { pos: 0, line : 0 },
    tokens: vec!(),
  };

  while cs.has_chars() {
    if cs.handle_newline(&CStream::skip_char) {}
    else if cs.parse_number() {}
    else if cs.skip_space() {}
    else if cs.parse_syntax() {}
    else {
      let s : String = cs.chars[cs.loc.pos..].into_iter().collect();
      panic!("Unexpected characters: \"{}\"", s);
    }
  }

  cs.tokens
}

pub fn test_lex() {
  let code = "(3 + 4) * 10";
  let ts = lex(code);
  for t in ts {
    println!("{:?}", t.string);
  }
  //println!("{:?}", ts);
}

#[test]
fn test () {
  test_lex();
}