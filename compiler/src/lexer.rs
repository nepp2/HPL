
use crate::expr::{StringCache, RefStr};
use crate::error::{Error, TextLocation, TextMarker, error_raw};

const SYNTAX : &'static [&'static str] =
  &["==", "!=", "<=", ">=", "=>", "+=", "-=", "*=", "/=", "||",
    "&&", "{", "}", "(", ")", "[", "]", "<", ">", ";", ":", ",",
    ".", "=", "+", "-", "*", "/", "%", "?", "|", "&", "^", "!", "$"];

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum TokenType {
  Symbol, FloatLiteral, IntLiteral, StringLiteral
}

#[derive(Clone)]
pub struct Token {
  pub symbol : RefStr,
  pub token_type : TokenType,
  pub loc : TextLocation,
}

struct CStream<'l> {
  chars : Vec<char>,
  loc : StreamLocation,
  tokens : Vec<Token>,
  errors : Vec<Error>,
  symbols : &'l StringCache,
  current_token : String,
}

#[derive(Clone, Copy)]
struct StreamLocation {
  pos : usize,
  line : usize,
  line_start : usize,
}

impl From<StreamLocation> for TextMarker {
  fn from(v : StreamLocation) -> TextMarker {
    TextMarker { line : v.line, col: v.pos - v.line_start }
  }
}

impl <'l> CStream<'l> {

  fn new(chars : Vec<char>, symbols : &StringCache) -> CStream {
    CStream {
      chars,
      loc : StreamLocation { pos: 0, line: 1, line_start: 0 },
      tokens: vec!(),
      errors: vec!(),
      symbols,
      current_token: String::new(),
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
    TextLocation::new(start_loc, self.loc)
  }

  fn complete_token(&mut self, start_loc : StreamLocation, token_type : TokenType) {
    let loc = self.get_text_location(start_loc);
    let symbol = self.symbols.get(self.current_token.as_ref());
    self.current_token.clear();
    let t = Token {
      symbol,
      token_type: token_type,
      loc : loc,
    };
    self.tokens.push(t);
  }

  fn raise_error(&mut self, start_loc : StreamLocation, message : String) -> Error {
    let location = self.get_text_location(start_loc);
    self.current_token.clear();
    error_raw(location, message)
  }

  fn advance_line(&mut self) {
    self.loc.line += 1;
    self.loc.line_start = self.loc.pos;
  }

  fn handle_newline(&mut self) -> bool {
    if self.peek() == '\n' {
      self.skip_char();
      self.advance_line();
      true
    }
    else if self.skip_string("\r\n") {
      self.advance_line();
      true
    }
    else { false }
  }

  fn is_number(&self) -> bool {
    let c = self.peek();
    c >= '0' && c <= '9'
  }

  fn iter_char_while<C, O>(&mut self, condition : C, mut operation : O)
    where C : Fn(&CStream<'l>) -> bool, O : FnMut(&mut CStream<'l>)
  {
    while self.loc.pos < self.chars.len() {
      if condition(self) {
        operation(self);
      }
      else{
        break;
      }
    }
  }

  fn skip_char_while<C>(&mut self, condition : C)
    where C : Fn(&CStream<'l>) -> bool
  {
    self.iter_char_while(condition, &mut CStream::skip_char);
  }

  fn append_char(&mut self) {
    let c = self.peek();
    self.current_token.push(c);
    self.skip_char();
  }

  fn append_char_while<C>(&mut self, condition : C)
    where C : Fn(&CStream<'l>) -> bool
  {
    self.iter_char_while(condition, &mut |cs : &mut CStream| { cs.append_char() });
  }

  fn lex_number(&mut self) -> Result<bool, Error> {
    if self.is_number() {
      let start_loc = self.loc;
      self.append_char_while(&CStream::is_number);
      let literal_type =
        if self.has_chars() && self.peek() == '.' {
          self.append_char();
          self.append_char_while(&CStream::is_number);
          TokenType::FloatLiteral
        }
        else {
          TokenType::IntLiteral
        };
      if self.has_chars() && self.is_symbol_start_char() {
        self.append_char_while(&CStream::is_symbol_middle_char);
        return Err(self.raise_error(start_loc, "Malformed literal".to_string()));
      }
      else{
        self.complete_token(start_loc, literal_type);
      }
      Ok(true)
    }
    else { Ok(false) }
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

  fn lex_symbol(&mut self) -> bool {
    if self.is_symbol_start_char() {
      let start_loc = self.loc;
      self.append_char();
      self.append_char_while (&CStream::is_symbol_middle_char);
      self.complete_token(start_loc, TokenType::Symbol);
      true
    }
    else { false }
  }

  /// returns true for a single space or tab (not for newline characters)
  fn is_space_char(&self) -> bool {
    let c = self.peek();
    c == '\t' || c == ' '
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

  fn skip_string(&mut self, s : &str) -> bool {
    if self.peek_string(s) {
      for _ in s.chars() {
        self.skip_char();
      }
      return true;
    }
    return false;
  }

  fn lex_string(&mut self, s : &str) -> bool {
    let start_loc = self.loc;
    if self.skip_string(s) {
      self.current_token.push_str(s);
      self.complete_token(start_loc, TokenType::Symbol);
      return true;
    }
    return false;
  }

  fn unknown_token(&mut self) -> Error {
    let start_loc = self.loc;
    let _ = self.pop(); 
    self.raise_error(start_loc, "Unknown token".to_string())
  }

  fn lex_comment(&mut self) -> bool {
    // TODO: this doesn't handle newlines properly, so the error locations will be wrong
    if self.peek_string("/*") {
      self.skip_char();
      self.skip_char();
      self.skip_char_while(&|cs : &CStream| { !cs.peek_string("*/") });
      self.skip_char();
      self.skip_char();
      return true;
    }
    else if self.peek_string("//") {
      self.skip_char_while(&|cs : &CStream| {
        let c = cs.peek();
        c != '\n'
      });
      return true;
    }
    return false;
  }

  fn lex_syntax(&mut self) -> bool {
    // TODO: this is slow
    for s in SYNTAX {
      if self.lex_string(s) {
        return true;
      }
    }
    return false;
  }

  fn lex_string_literal(&mut self) -> Result<bool, Error> {
    if self.peek() != '"' {
      return Ok(false);
    }
    self.skip_char();
    let start_loc = self.loc;
    while self.has_chars() {
      let c = self.peek();
      if c == '\\' {
        // slash pattern, e.g. \n for newline
        self.skip_char();
        let c = self.peek();
        match c {
          '\\' => self.current_token.push('\\'),
          'n' => self.current_token.push('\n'),
          't' => self.current_token.push('\t'),
          '"' => self.current_token.push('"'),
          _ => return Err(self.raise_error(start_loc, format!("unexpected pattern '\\{}' in string literal", c))),
        }
        self.skip_char();
      }
      else {
        if c == '"' { break; }
        if c == '\n' { self.advance_line() }
        self.append_char();
      }
    }
    if self.has_chars() {
      self.skip_char();
      self.complete_token(start_loc, TokenType::StringLiteral);
      return Ok(true);
    }
    else {
      return Err(self.raise_error(start_loc, "malformed string literal".to_string()));
    }
  }
}

pub fn lex(code : &str, symbols : &StringCache) -> Result<Vec<Token>, Vec<Error>> {

  fn lex_with_errors(cs : &mut CStream) -> Result<(), Error> {
    while cs.has_chars() {
      if cs.handle_newline() {}
      else if cs.skip_space() {}
      else if cs.lex_symbol() {}
      else if cs.lex_string_literal()? {}
      else if cs.lex_number()? {}
      else if cs.lex_comment() {}
      else if cs.lex_syntax() {}
      else {
        return Err(cs.unknown_token());
      }
    }
    Ok(())
  }

  let mut cs = CStream::new(code.chars().collect(), symbols);
  while cs.has_chars() {
    match lex_with_errors(&mut cs) {
      Ok(_) => (),
      Err(e) => cs.errors.push(e),
    }
  }
  if cs.errors.is_empty() {
    Ok(cs.tokens)
  }
  else {
    Err(cs.errors)
  }
}
