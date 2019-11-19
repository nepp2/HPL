
use std::fmt;

/// Returns an error that isn't wrapped in Result::Err
pub fn error_raw<L : Into<TextLocation>, S : Into<ErrorContent>>(loc : L, message : S) -> Error {
  Error { message: message.into(), location: loc.into() }
}

/// Returns an error wrapped in Result::Err
pub fn error<T, L : Into<TextLocation>, S : Into<ErrorContent>>(loc : L, message : S) -> Result<T, Error> {
  Err(Error { message: message.into(), location: loc.into() })
}

/// Returns an error content wrapped
pub fn error_content<S : Into<ErrorContent>>(message : S) -> ErrorContent {
  message.into()
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TextMarker {
  pub line : usize,
  pub col : usize,
}

impl TextMarker {
  fn order(a : Self, b : Self) -> (Self, Self) {
    if a.line < b.line { (a, b) }
    else if b.line < a.line { (b, a) }
    else if a.col < b.col { (a, b) }
    else { (b, a) }
  }
}

impl From<(usize, usize)> for TextMarker {
  fn from(v : (usize, usize)) -> TextMarker {
    TextMarker { line : v.0, col: v.1 }
  }
}

impl <'l> Into<TextLocation> for &'l TextLocation {
  fn into(self) -> TextLocation {
    *self
  }
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TextLocation {
  pub start : TextMarker,
  pub end : TextMarker,
}

impl TextLocation {
  
  pub fn new<T : Into<TextMarker>>(start : T, end : T) -> TextLocation {
    TextLocation {
      start: start.into(),
      end: end.into(),
    }
  }
  
  pub fn zero() -> TextLocation {
    let z = TextMarker{ line: 0, col: 0 };
    TextLocation::new(z, z)
  }

  pub fn merge(self, x : Self) -> Self {
    let (start, _) = TextMarker::order(self.start, x.start);
    let (_, end) = TextMarker::order(self.end, x.end);
    TextLocation { start, end }
  }

  /// TODO: move this somewhere else?
  pub fn slice_text(self, code : &str) -> &str {
    let loc = self;
    let (start_line, end_line) = (loc.start.line - 1, loc.end.line - 1);
    let mut it =
      // Chain the zero offset for the first line
      [0].iter().cloned().chain(
        // find the newline positions
        code.char_indices().filter(|&(_, c)| c == '\n')
        // offset past the \n char
        .map(|(b, _)| b + 1)
      )
      // get the start offsets of the lines we care about
      .enumerate().filter(|&(i, _)| i == start_line || i == end_line)
      .map(|(_, b)| b);
    let l1_start = it.next().unwrap();
    let l2_start = it.next().unwrap_or(l1_start);
    &code[l1_start + loc.start.col.. l2_start + loc.end.col]
  }
}

impl <S : Into<String>> From<S> for ErrorContent {
  fn from(s : S) -> ErrorContent {
    let s : String = s.into();
    ErrorContent::Message(s)
  }
}

#[derive(Debug, PartialEq)]
pub enum ErrorContent {
  Message(String),
  InnerError(String, Box<Error>),
}

#[derive(Debug, PartialEq)]
pub struct Error {
  pub message : ErrorContent,
  pub location : TextLocation,
}


impl fmt::Display for TextMarker {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "line: {}, column: {}", self.line, self.col)
  }
}

impl fmt::Display for TextLocation {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if self.start.line == self.end.line {
      write!(f, "(line: {}, column: {} to {})",
        self.start.line, self.start.col, self.end.col)
    }
    else {
      write!(f, "({}) to ({})", self.start, self.end)
    }
  }
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.location)?;
    match &self.message {
      ErrorContent::Message(m) => {
        write!(f, ", message: {}", m)
      },
      ErrorContent::InnerError(m, e) => {
        writeln!(f, ", message: {}", m)?;
        writeln!(f, "  inner error:")?;
        write!(f, "    {}", e)
      },
    }
  }
}

