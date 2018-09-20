
#[macro_export]
macro_rules! error(
  ( $loc:expr, $($args:tt)* ) => (
    {
      let loc = $loc;
      Err(Error {
        message: format!($($args)*),
        location: loc,
      })
    }
  )
);

#[macro_export]
macro_rules! error_expr(
  ( $expr:expr, $($args:tt)* ) => (
    {
      let loc = ($expr).loc;
      Err(error!(($expr).loc, $($args)*))
    }
  )
);

#[macro_export]
macro_rules! error_result(
  ( $($args:tt)* ) => ( Err(error!($($args)*)) )
);

#[derive(Debug, Clone, Copy)]
pub struct TextMarker {
  pub line : usize,
  pub col : usize,
}

impl From<(usize, usize)> for TextMarker {
  fn from(v : (usize, usize)) -> TextMarker {
    TextMarker { line : v.0, col: v.1 }
  }
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug)]
pub struct Error {
  pub message : String,
  pub location : TextLocation,
}
