
use error::{Error, TextLocation};
use value::RefStr;
use parser::Expr;

pub fn symbol_unwrap(e : &Expr) -> Result<&RefStr, Error> {
  if let Expr::Symbol(s) = e {
    Ok(s)
  }
  else {
    error_result!("expected a symbol, found {:?}", e)
  }
}

pub fn symbol_to_refstr(e : &Expr) -> Result<RefStr, Error> {
  symbol_unwrap(e).map(|s| s.clone())
}