
use value::RefStr;
use parser::Expr;

pub fn symbol_unwrap(e : &Expr) -> Result<&RefStr, String> {
if let Expr::Symbol(s) = e {
    Ok(s)
}
else {
    Err(format!("expected a symbol, found {:?}", e))
}
}

pub fn symbol_to_refstr(e : &Expr) -> Result<RefStr, String> {
symbol_unwrap(e).map(|s| s.clone())
}