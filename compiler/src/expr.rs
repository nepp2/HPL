
use std::fmt;
use std::rc::Rc;
use std::collections::HashSet;

use crate::error::{Error, TextLocation, error };
use crate::c_interface::SStr;

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

#[repr(C, u8)]
#[derive(Debug)]
pub enum ExprTag {
  Symbol(SStr),
  LiteralString(SStr),
  LiteralFloat(f64),
  LiteralInt(i64),
  LiteralBool(bool),
  LiteralUnit,
}

impl ExprTag {
  pub fn literal_string(s : String) -> ExprTag {
    let tag = ExprTag::LiteralString(SStr::from_str(s.as_str()));
    std::mem::forget(s);
    tag
  }
  pub fn symbol(s : String) -> ExprTag {
    let tag = ExprTag::Symbol(SStr::from_str(s.as_str()));
    std::mem::forget(s);
    tag
  }
}

#[repr(C)]
pub struct SArray<T> {
  pub len : u64,
  pub data : *mut T,
}

impl <T> SArray<T> {
  fn new(mut v : Vec<T>) -> SArray<T> {
    let a = SArray { len: v.len() as u64, data: v.as_mut_ptr() };
    std::mem::forget(v);
    a
  }

  pub fn as_slice(&self) -> &[T] {
    unsafe { std::slice::from_raw_parts(self.data, self.len as usize) }
  }
}

impl <T> Drop for SArray<T> {
  fn drop(&mut self) {
    unsafe {
      Vec::from_raw_parts(self.data, self.len as usize, self.len as usize)
    };
  }
}

#[repr(C)]
pub struct Expr {
  pub children : SArray<Expr>,
  pub loc : TextLocation,
  pub tag : ExprTag,
}

impl Expr {

  pub fn new(tag : ExprTag, children : Vec<Expr>, loc : TextLocation) -> Expr {
    Expr { children: SArray::new(children), loc, tag }
  }
  
  // TODO: are these needed?
  // pub fn get_symbol(&self) -> SStr {
  //   if self.tag == ExprTag::Symbol { unsafe { self.data.s } } else { panic!() }
  // }
  // pub fn get_string(&self) -> SStr {
  //   if self.tag == ExprTag::LiteralString { unsafe { self.data.s } } else { panic!() }
  // }
  // pub fn get_float(&self) -> f64 {
  //   if self.tag == ExprTag::LiteralFloat { unsafe { self.data.f } } else { panic!() }
  // }
  // pub fn get_int(&self) -> i64 {
  //   if self.tag == ExprTag::LiteralInt { unsafe { self.data.i } } else { panic!() }
  // }
  // pub fn get_bool(&self) -> bool {
  //   if self.tag == ExprTag::LiteralBool { unsafe { self.data.b } } else { panic!() }
  // }
}

impl Drop for Expr {
  fn drop(&mut self) {
    match self.tag {
      ExprTag::Symbol(s) => {
        unsafe {
          String::from_raw_parts(s.ptr, s.length as usize, s.length as usize);
        }
      }
      _ => ()
    }
  }
}

impl <'l> Into<TextLocation> for &'l Expr {
  fn into(self) -> TextLocation {
    self.loc
  }
}

impl Expr {
  pub fn symbol_unwrap(&self) -> Result<&str, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(s.as_str())
    }
    else{
      error(self, format!("expected a symbol, found {:?}", self.tag))
    }
  }
}


impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fn display_inner(e: &Expr, f: &mut fmt::Formatter<'_>, indent : usize) -> fmt::Result {
      if e.children.len > 0 {
        let s = e.symbol_unwrap().unwrap();
        write!(f, "({}", s)?;
        if s == "block" {
          let indent = indent + 2;
          for c in e.children.as_slice() {
            writeln!(f)?;
            write!(f, "{:indent$}", "", indent=indent)?;
            display_inner(c, f, indent)?;
          }
        }
        else {
          for c in e.children.as_slice() {
            write!(f, " ")?;
            display_inner(c, f, indent)?;
          }
        }
        write!(f, ")")?;
        return Ok(());
      }
      match (&e.tag, e.children.as_slice()) {
        (ExprTag::Symbol(s), []) => write!(f, "{}", s.as_str()),
        (ExprTag::Symbol(s), children) => {
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
        (ExprTag::LiteralString(s), _) => write!(f, "{}", s.as_str()),
        (ExprTag::LiteralFloat(v), _) => write!(f, "{}", v),
        (ExprTag::LiteralInt(v), _) => write!(f, "{}", v),
        (ExprTag::LiteralBool(v), _) => write!(f, "{}", v),
        (ExprTag::LiteralUnit, _) => write!(f, "()"),
      }
    }
    display_inner(&self, f, 0)
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
