
use std::fmt;
use crate::common::*;

/// Returns an error that isn't wrapped in Result::Err
pub fn error_raw<L : Into<TextLocation>, S : Into<ErrorContent>>(loc : L, message : S) -> Error {
  Error { message: message.into(), location: loc.into() }
}

/// Returns an error wrapped in Result::Err
pub fn error<T, L : Into<TextLocation>, S : Into<ErrorContent>>(loc : L, message : S) -> Result<T, Error> {
  Err(Error { message: message.into(), location: loc.into() })
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TextMarker {
  pub line : usize,
  pub col : usize,
}

impl TextMarker {
  fn order(a : Self, b : Self) -> (Self, Self) {
    if b < a { (b, a) } else { (a, b) }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct TextLocation {
  pub source : SourceId,
  pub start : TextMarker,
  pub end : TextMarker,
}

impl TextLocation {
  
  pub fn new<T : Into<TextMarker>>(source : SourceId, start : T, end : T) -> TextLocation {
    TextLocation {
      source,
      start: start.into(),
      end: end.into(),
    }
  }
  
  pub fn zero() -> TextLocation {
    let z = TextMarker{ line: 0, col: 0 };
    TextLocation { source: no_source(), start: z, end: z }
  }

  pub fn merge(self, x : Self) -> Self {
    if self.source != x.source {
      panic!("tried to merge text locations from different sources")
    }
    let (start, _) = TextMarker::order(self.start, x.start);
    let (_, end) = TextMarker::order(self.end, x.end);
    TextLocation { source: self.source, start, end }
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
  InnerErrors(String, Vec<Error>),
}

#[derive(Debug, PartialEq)]
pub struct Error {
  pub message : ErrorContent,
  pub location : TextLocation,
}

impl Error {
  pub fn display(&self) -> UnsourcedError {
    UnsourcedError{ e: self }
  }
}

pub struct UnsourcedError<'l> {
  e : &'l Error,
}

impl <'l> fmt::Display for UnsourcedError<'l> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.e.location)?;
    match &self.e.message {
      ErrorContent::Message(m) => {
        write!(f, ", message: {}", m)
      },
      ErrorContent::InnerErrors(m, es) => {
        writeln!(f, ", message: {}", m)?;
        writeln!(f, "  inner errors:")?;
        for e in es.iter() {
          writeln!(f, "    {}", e.display())?
        }
        Ok(())
      },
    }
  }
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
