
use std::collections::HashSet;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TokenType {
  Symbol, Syntax, FloatLiteral, Keyword
}

#[derive(Debug)]
pub struct TextLocation {
  start : u32,
  length : u32,
  line : u32,
}

#[derive(Debug)]
pub struct Token {
  pub string : String,
  pub token_type : TokenType,
  pub loc : TextLocation,
}

#[derive(Debug)]
pub struct LexError {
  message : String,
  loc : TextLocation,
}

struct CStream {
  chars : Vec<char>,
  loc : StreamLocation,
  tokens : Vec<Token>,
  errors : Vec<LexError>,
  keywords : HashSet<&'static str>,
}

#[derive(Clone, Copy)]
struct StreamLocation {
  pos : usize,
  line : usize,
}

impl CStream {

  const KEYWORDS : &'static [&'static str] = &["fun", "if", "else", "type", "while", "break", "return", "let"];

  fn new(chars : Vec<char>) -> CStream {
    let mut keywords = HashSet::new();
    for &s in CStream::KEYWORDS { keywords.insert(s); }
    CStream {
      chars,
      loc : StreamLocation { pos: 0, line : 0 },
      tokens: vec!(),
      errors: vec!(),
      keywords,
    }
  }

  fn has_chars(&self) -> bool {
    self.loc.pos < self.chars.len()
  }

  fn peek(&self) -> char { self.chars[self.loc.pos] }

  fn skip_char(&mut self){
    self.loc.pos += 1;
  }

  fn pop(&mut self) -> char {
    let c = self.peek();
    self.skip_char();
    c
  }

  fn get_text_location(&mut self, start_loc : StreamLocation) -> TextLocation {
    let len = self.loc.pos - start_loc.pos;
    TextLocation {
      start: start_loc.pos as u32,
      length: len as u32,
      line: start_loc.line as u32,
    }
  }

  fn complete_token(&mut self, start_loc : StreamLocation, string : String, token_type : TokenType) {
    let loc = self.get_text_location(start_loc);
    let t = Token {
      string,
      token_type: token_type,
      loc : loc,
    };
    self.tokens.push(t);
  }

  fn error(&mut self, start_loc : StreamLocation, message : String) {
    let loc = self.get_text_location(start_loc);
    self.errors.push(LexError{ message, loc });
  }

  fn handle_newline(&mut self, operation : &Fn(&mut CStream)) -> bool {
    if self.peek() == '\n' {
      operation(self);
      self.loc.line += 1;
      true
    }
    else { false }
  }

  fn is_number(&self) -> bool {
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
    if self.is_number() {
      let start_loc = self.loc;
      let mut string = String::new();
      self.append_char_while(&mut string, &CStream::is_number);
      if self.has_chars() && self.peek() == '.' {
        self.append_char(&mut string);
        self.append_char_while(&mut string, &CStream::is_number);
      }
      if self.has_chars() && self.is_symbol_start_char() {
        self.append_char_while(&mut string, &CStream::is_symbol_middle_char);
        self.error(start_loc, "Malformed floating point literal".to_string());
      }
      else{
        self.complete_token(start_loc, string, TokenType::FloatLiteral);
      }
      true
    }
    else { false }
  }

  fn is_symbol_start_char(&self) -> bool {
    let c = self.peek();
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
  }

  fn is_symbol_middle_char(&self) -> bool {
    self.is_symbol_start_char() || {
      let c = self.peek();
      c >= '0' && c <= '9'
    }
  }

  fn parse_symbol_or_keyword(&mut self) -> bool {
    if self.is_symbol_start_char() {
      let start_loc = self.loc;
      let mut string = String::new();
      self.append_char(&mut string);
      self.append_char_while (&mut string, &CStream::is_symbol_middle_char);
      if self.keywords.contains(string.as_str()) {
        self.complete_token(start_loc, string, TokenType::Keyword);
      }
      else {
        self.complete_token(start_loc, string, TokenType::Symbol);
      }
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

  fn unknown_token(&mut self) {
    let start_loc = self.loc;
    let _ = self.pop(); 
    self.error(start_loc, "Unknown token".to_string());
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

pub fn lex(code : &str) -> Result<Vec<Token>, Vec<LexError>> {
  let mut cs = CStream::new(code.chars().collect());
  while cs.has_chars() {
    if cs.handle_newline(&CStream::skip_char) {}
    else if cs.parse_symbol_or_keyword() {}
    else if cs.parse_number() {}
    else if cs.skip_space() {}
    else if cs.parse_syntax() {}
    else {
      cs.unknown_token();
    }
  }
  if cs.errors.is_empty() {
    Ok(cs.tokens)
  }
  else {
    Err(cs.errors)
  }
}

#[test]
fn test_lex() {
  let code = "(3 + 4) * 10";
  let ts = lex(code).unwrap();
  for t in ts {
    println!("{:?}", t.string);
  }
  //println!("{:?}", ts);
}
