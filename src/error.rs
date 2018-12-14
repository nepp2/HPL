
/// Returns an error that isn't wrapped in Result::Err
pub fn error_raw<L : Into<TextLocation>, S : Into<String>>(loc : L, message : S) -> Error {
  Error { message: message.into(), location: loc.into() }
}

/// Returns an error wrapped in Result::Err
pub fn error<T, L : Into<TextLocation>, S : Into<String>>(loc : L, message : S) -> Result<T, Error> {
  Err(Error { message: message.into(), location: loc.into() })
}

pub fn error_no_loc<S : Into<String>>(message : S) -> Error {
  Error { message: message.into(), location: TextLocation::new((0,0), (0,0)) }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TextMarker {
  pub line : usize,
  pub col : usize,
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
}

#[derive(Debug, PartialEq)]
pub struct Error {
  pub message : String,
  pub location : TextLocation,
}
