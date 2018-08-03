
enum ExpTree {
  Token(Token),
  Tree(Vec<ExpTree>, TreeType)
}

enum TreeType {
  Brace, Paren, Bracket
}

const TERMINATING_SYNTAX : &'static [&'static str] = &["}", ")", "]", ";", ","];

// succeeds and returns a thing
// fails and returns an error
// fails as incomplete

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




enum PreparseError {
  Incomplete, Error(String)
}

fn parse_expression_tree(ts : &mut TokenStream) -> Result<ExpTree, PreparseError> {
  // if open syntax
  // 
}

pub fn preparse(tokens : Vec<Token>) -> Result<ExpTree, PreparseError> {
  let mut ts = TokenStream::new(tokens);



  let e = parse_expression(&mut ts)?;
  if ts.has_tokens() {
    let t = ts.peek()?;
    return Err(format!("Unexpected token '{}' of type '{:?}'", t.string, t.token_type));
  }
  return Ok(e);
}
