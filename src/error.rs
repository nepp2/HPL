
#[macro_export]
macro_rules! error(
  ( $($args:tt)* ) => (
    Error {
      message: format!($($args)*),
      location: TextLocation { line: 0, start: 0, length: 0 },
    }
  )
);

#[macro_export]
macro_rules! error_result(
  ( $($args:tt)* ) => ( Err(error!($($args)*)) )
);

#[derive(Debug)]
pub struct TextLocation {
  pub line : u32,
  pub start : u32,
  pub length : u32,
}

#[derive(Debug)]
pub struct Error {
  pub message : String,
  pub location : TextLocation,
}

fn error(){
  let e = error!("blah blah {} {}", 3, 6);
  let a = error!("blah blah {} {}", 4, 5);
}
