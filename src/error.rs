
#[macro_export]
macro_rules! error(
  ( $fmt:expr, $($args:tt)* ) => (
    Error {
      message: format!($fmt, $($args)*),
      location: TextLocation { line: 0, start: 0, length: 0 },
    }
    //vec!( $($args)* )
  )
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
  let e = error!("blah blah {} {}", 4, 5);
  let a = error!("blah blah {} {}", 4, 5);
}
