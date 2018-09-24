
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashSet;

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

pub struct SymbolCache {
  symbols : HashSet<RefStr>
}

impl SymbolCache {
  pub fn new() -> SymbolCache {
    SymbolCache{ symbols: HashSet::new() }
  }

  pub fn symbol<T : AsRef<str> + Into<RefStr>>(&mut self, s : T) -> RefStr {
    if self.symbols.contains(s.as_ref()) {
      self.symbols.get(s.as_ref()).unwrap().clone()
    }
    else {
      let s : RefStr = s.into();
      self.symbols.insert(s.clone());
      s
    }
  }
}

#[derive(Debug, PartialEq)]
pub struct StructDef {
  pub name : RefStr,
  pub fields : Vec<RefStr>,
}

#[derive(Debug, PartialEq)]
pub struct Struct {
  pub def : Rc<StructDef>,
  pub fields : Vec<Value>,
}

pub type StructVal = Rc<RefCell<Struct>>;

pub type Array = Rc<RefCell<Vec<Value>>>;

/// Represents a value in the interpreted language.
/// Currently uses 16 bytes. I think this is because there are 8 byte
/// RC pointers in the union, and the discriminating value is being
/// padded to word size (also 8 bytes). Could probably be optimised
/// down to 8 bytes total, with some ugly pointer hacks.
#[derive(Clone, PartialEq)]
pub enum Value {
  Float(f32),
  Array(Array),
  Bool(bool),
  Function(usize),
  Struct(StructVal),
  Unit,
}


impl fmt::Debug for Value {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Value::Float(x) => write!(f, "{}", x),
      Value::Array(a) => write!(f, "{:?}", &*a.borrow()),
      Value::Bool(b) => write!(f, "{}", b),
      Value::Function(id) => write!(f, "function[{}]", id),
      Value::Struct(s) => {
        let Struct { def, fields } = &*s.borrow();
        let name = &def.name;
        write!(f, "{} {{ ", name)?;
        let end = fields.len() - 1;
        for (i, (n, v)) in def.fields.iter().zip(fields.iter()).enumerate() {
          let sep = if i == end {""} else {","};
          write!(f, "{}: {:?}{} ", n, v, sep)?;
        }
        write!(f, "}}")
      }
      Value::Unit => write!(f, "Unit"),
    }
  }
}
