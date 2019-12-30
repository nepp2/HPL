
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashSet;

use crate::error::{Error, TextLocation, error_raw };
use crate::c_interface::SStr;

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

pub struct UIDGenerator {
  gen : u64,
}

impl UIDGenerator {
  pub fn new() -> Self {
    UIDGenerator { gen : 0 }
  }

  pub fn next(&mut self) -> u64 {
    let uid = self.gen;
    self.gen += 1;
    uid
  }
}

#[repr(u64)]
#[derive(Debug)]
pub enum ExprContent {
  List(SStr, SArray<Expr>),
  Symbol(SStr),
  LiteralString(SStr),
  LiteralFloat(f64),
  LiteralInt(i64),
  LiteralBool(bool),
  LiteralUnit,
}

impl Clone for ExprContent {
  fn clone(&self) -> Self {
    fn clone(s : SStr) -> SStr {
      let v : String = s.as_str().into();
      let s = SStr::from_str(s.as_str());
      std::mem::forget(v);
      s
    }
    use self::ExprContent::*;
    match self {
      List(s, children) => List(clone(*s), children.clone()),
      Symbol(s) => Symbol(clone(*s)),
      LiteralString(s) => LiteralString(clone(*s)),
      LiteralFloat(f) => LiteralFloat(*f),
      LiteralInt(i) => LiteralInt(*i),
      LiteralBool(b) => LiteralBool(*b),
      LiteralUnit => LiteralUnit,
    }
  }
}

impl ExprContent {
  pub fn literal_string(s : String) -> ExprContent {
    let content = ExprContent::LiteralString(SStr::from_str(s.as_str()));
    std::mem::forget(s);
    content
  }
  pub fn symbol(s : String) -> ExprContent {
    let content = ExprContent::Symbol(SStr::from_str(s.as_str()));
    std::mem::forget(s);
    content
  }
  pub fn list(s : String, children : Vec<Expr>) -> ExprContent {
    let content = ExprContent::List(SStr::from_str(s.as_str()), SArray::new(children));
    std::mem::forget(s);
    content
  }
}

/// Owned array, compatible with Cauldron's array implementation
#[repr(C)]
pub struct SArray<T> {
  pub data : *mut T,
  pub length : u64,
}

impl <T> SArray<T> {
  fn new(mut v : Vec<T>) -> SArray<T> {
    let a = SArray { length: v.len() as u64, data: v.as_mut_ptr() };
    std::mem::forget(v);
    a
  }

  pub fn as_slice(&self) -> &[T] {
    unsafe { std::slice::from_raw_parts(self.data, self.length as usize) }
  }
}

impl <T : fmt::Debug> fmt::Debug for SArray<T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", self.as_slice())
  }
}

impl <T> Drop for SArray<T> {
  fn drop(&mut self) {
    unsafe {
      Vec::from_raw_parts(self.data, self.length as usize, self.length as usize)
    };
  }
}

impl <T : Clone> Clone for SArray<T> {
  fn clone(&self) -> Self {
    let v = unsafe {
      Vec::from_raw_parts(self.data, self.length as usize, self.length as usize)
    };
    let a = SArray::new(v.clone());
    std::mem::forget(v);
    a
  }
}

#[repr(C)]
#[derive(Clone)]
pub struct Expr {
  pub loc : TextLocation,
  pub content : ExprContent,
}

impl Expr {
  pub fn new(content : ExprContent, loc : TextLocation) -> Expr {
    Expr { loc, content }
  }
}

impl Drop for Expr {
  fn drop(&mut self) {
    // TODO: strings should be cleared somehow. this leaks memory badly.
  }
}

impl <'l> Into<TextLocation> for &'l Expr {
  fn into(self) -> TextLocation {
    self.loc
  }
}

impl Expr {

  pub fn try_construct(&self) -> Option<(&str, &[Expr])> {
    match &self.content {
      ExprContent::List(s, children) => Some((s.as_str(), children.as_slice())),
      _ => None,
    }
  }

  pub fn unwrap_construct(&self) -> Result<(&str, &[Expr]), Error> {
    self.try_construct().ok_or_else(||
      error_raw(self, format!("expected a construct, found {:?}", self.content)))
  }

  pub fn try_symbol(&self) -> Option<&str> {
    match &self.content {
      ExprContent::Symbol(s) => Some(s.as_str()),
      _ => None,
    }
  }

  pub fn unwrap_symbol(&self) -> Result<&str, Error> {
    self.try_symbol().ok_or_else(||
      error_raw(self, format!("expected a symbol, found {:?}", self.content)))
  }

  pub fn children(&self) -> &[Expr] {
    match &self.content {
      ExprContent::List(_, c) => c.as_slice(),
      _ => &[],
    }
  }
}

impl fmt::Debug for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self)
  }
}

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fn display_inner(e: &Expr, f: &mut fmt::Formatter<'_>, indent : usize) -> fmt::Result {
      if let Some((s, children)) = e.try_construct() {
        write!(f, "({}", s)?;
        if s == "block" || s == "{" || s == ";" {
          let indent = indent + 2;
          for c in children {
            writeln!(f)?;
            write!(f, "{:indent$}", "", indent=indent)?;
            display_inner(c, f, indent)?;
          }
        }
        else {
          for c in children {
            write!(f, " ")?;
            display_inner(c, f, indent)?;
          }
        }
        write!(f, ")")?;
        return Ok(());
      }
      match &e.content {
        ExprContent::Symbol(s) => write!(f, "{}", s.as_str()),
        ExprContent::List(s, children) => {
          let children = children.as_slice();
          write!(f, "({}", s.as_str())?;
          if s.as_str() == "block" {
            let indent = indent + 2;
            for c in children {
              writeln!(f)?;
              write!(f, "{:indent$}", "", indent=indent)?;
              display_inner(c, f, indent)?;
            }
          }
          else {
            for c in children {
              write!(f, " ")?;
              display_inner(c, f, indent)?;
            }
          }
          write!(f, ")")?;
          Ok(())
        }
        ExprContent::LiteralString(s) => write!(f, "\"{}\"", s.as_str()),
        ExprContent::LiteralFloat(v) => write!(f, "{}", v),
        ExprContent::LiteralInt(v) => write!(f, "{}", v),
        ExprContent::LiteralBool(v) => write!(f, "{}", v),
        ExprContent::LiteralUnit => write!(f, "()"),
      }
    }
    display_inner(&self, f, 0)
  }
}

/// This cache uses internal mutability to cache strings. It should be safe,
/// because the strings themselves are immutable.
#[derive(Default, Clone)]
pub struct StringCache {
  symbols : RefCell<HashSet<RefStr>>,
}

impl StringCache {
  pub fn new() -> StringCache {
    Default::default()
  }

  pub fn get<T : AsRef<str> + Into<RefStr>>(&self, s : T) -> RefStr {
    let mut symbols = self.symbols.borrow_mut();
    if let Some(symbol) = symbols.get(s.as_ref()) {
      symbol.clone()
    }
    else{
      let string : RefStr = s.into();
      symbols.insert(string.clone());
      string
    }
  }
}
