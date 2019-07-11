
use std::fmt;
use std::rc::Rc;
use std::collections::HashSet;

use crate::error::{Error, TextLocation, error };

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

#[derive(PartialEq, Debug, Clone)]
pub enum ExprTag {
  Tree(RefStr),
  Symbol(RefStr),
  LiteralString(RefStr),
  LiteralFloat(f64),
  LiteralInt(i64),
  LiteralBool(bool),
  LiteralUnit,
}

/// Expression
#[derive(Debug, Clone)]
pub struct Expr {
  pub tag : ExprTag,
  pub children : Vec<Expr>,
  pub loc : TextLocation,
}

pub fn display_expr(e: &Expr) -> String {
  pub fn display_inner(e: &Expr, w: &mut fmt::Write, indent : usize) -> fmt::Result {
    match &e.tag {
      ExprTag::Tree(s) => {
        write!(w, "({}", s)?;
        if s.as_ref() == "block" {
          let indent = indent + 2;
          for c in e.children.iter() {
            writeln!(w)?;
            write!(w, "{:indent$}", "", indent=indent)?;
            display_inner(c, w, indent)?
          }
        }
        else {
          for c in e.children.iter() {
            write!(w, " ")?;
            display_inner(c, w, indent)?
          }
        }
        write!(w, ")")
      }
      ExprTag::Symbol(x) => write!(w, "{}", x),
      ExprTag::LiteralString(x) => write!(w, "{}", x),
      ExprTag::LiteralFloat(x) => write!(w, "{}", x),
      ExprTag::LiteralInt(x) => write!(w, "{}", x),
      ExprTag::LiteralBool(x) => write!(w, "{}", x),
      ExprTag::LiteralUnit => write!(w, "()"),
    }
  }
  let mut buf = String::new();
  display_inner(e, &mut buf, 0).unwrap();
  buf
}

impl Expr {
  pub fn tree_symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Tree(s) = &self.tag {
      Ok(s)
    }
    else {
      error(self, format!("expected a tree, found {:?}", self))
    }
  }

  pub fn symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(s)
    }
    else {
      error(self, format!("expected a symbol, found {:?}", self))
    }
  }
}

impl <'l> Into<TextLocation> for &'l Expr {
  fn into(self) -> TextLocation {
    self.loc
  }
}

#[derive(Default)]
pub struct StringCache {
  symbols : HashSet<RefStr>,
}

impl StringCache {
  pub fn new() -> StringCache {
    Default::default()
  }

  pub fn get<T : AsRef<str> + Into<RefStr>>(&mut self, s : T) -> RefStr {
    if let Some(symbol) = self.symbols.get(s.as_ref()) {
      symbol.clone()
    }
    else{
      let string : RefStr = s.into();
      self.symbols.insert(string.clone());
      string
    }
  }
}
