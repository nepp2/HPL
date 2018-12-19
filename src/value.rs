
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashSet;

use crate::error::{Error, TextLocation, error};

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

#[derive(Clone, PartialEq, Debug)]
pub struct FunctionSignature {
  pub return_type : Type,
  pub args : Vec<Type>,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
  Unit,
  Float,
  String,
  Bool,
  Array,
  Function,
  Struct(RefStr),
  Any,
  Unresolved
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprTag {
  Tree(RefStr),
  Symbol(RefStr),
  LiteralString(RefStr),
  LiteralFloat(f32),
  LiteralBool(bool),
}

/// Used to look up expressions in the abstract syntax tree
pub type ExprId = usize;

/// Expression
#[derive(Debug, Clone)]
pub struct Expr {
  pub id : ExprId,
  pub tag : ExprTag,
  pub children : Vec<Expr>,
  pub loc : TextLocation,
  pub type_info : Type,
}

fn pretty_print(e: &Expr, f: &mut fmt::Formatter, indent : usize) -> fmt::Result {
  match &e.tag {
    ExprTag::Tree(s) => {
      write!(f, "({}", s)?;
      if s.as_ref() == "block" {
        let indent = indent + 2;
        for c in e.children.iter() {
          writeln!(f)?;
          write!(f, "{:indent$}", "", indent=indent)?;
          pretty_print(c, f, indent)?
        }
      }
      else {
        for c in e.children.iter() {
          write!(f, " ")?;
          pretty_print(c, f, indent)?
        }
      }
      write!(f, ")")
    }
    ExprTag::Symbol(x) => write!(f, "{}", x),
    ExprTag::LiteralString(x) => write!(f, "{}", x),
    ExprTag::LiteralFloat(x) => write!(f, "{}", x),
    ExprTag::LiteralBool(x) => write!(f, "{}", x),
  }
}

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    pretty_print(self, f, 0)
  }
}

impl Expr {
  pub fn tree_symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Tree(s) = &self.tag {
      Ok(&s)
    }
    else {
      error(self, format!("expected a tree, found {:?}", self))
    }
  }

  pub fn symbol_unwrap(&self) -> Result<&RefStr, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(&s)
    }
    else {
      error(self, format!("expected a symbol, found {:?}", self))
    }
  }

  pub fn symbol_to_refstr(&self) -> Result<RefStr, Error> {
    self.symbol_unwrap().map(|s| s.clone())
  }
}

impl <'l> Into<TextLocation> for &'l Expr {
  fn into(self) -> TextLocation {
    self.loc
  }
}

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

#[derive(Clone, PartialEq)]
pub struct FunctionRef {
  pub name : RefStr
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
  String(RefStr),
  Function(FunctionRef),
  Struct(StructVal),
  Unit,
}

impl Value {
  pub fn to_type(&self) -> Type {
    use self::Value::*;
    match self {
      Float(_) => Type::Float,
      Array(_) => Type::Array,
      Bool(_) => Type::Bool,
      String(_) => Type::String,
      Function(_) => Type::Function,
      Struct(s) => Type::Struct(s.borrow().def.name.clone()),
      Unit => Type::Unit,
    }
  }
}

impl fmt::Debug for Value {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Value::Float(x) => write!(f, "{}", x),
      Value::Array(a) => write!(f, "{:?}", &*a.borrow()),
      Value::Bool(b) => write!(f, "{}", b),
      Value::String(s) => write!(f, "{}", s),
      Value::Function(fr) => write!(f, "{}[..]", fr.name),
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

impl From<bool> for Value {
  fn from(v : bool) -> Value {
    Value::Bool(v)
  }
}
impl From<f32> for Value {
  fn from(v : f32) -> Value {
    Value::Float(v)
  }
}
impl From<Array> for Value {
  fn from(v : Array) -> Value {
    Value::Array(v)
  }
}

impl Into<Result<f32, String>> for Value {
  fn into(self) -> Result<f32, String> {
    match self {
      Value::Float(f) => Ok(f), 
      x => Err(format!("Expected float, found {:?}.", x))
    }
  }
}
impl Into<Result<bool, String>> for Value {
  fn into(self) -> Result<bool, String> {
    match self {
      Value::Bool(b) => Ok(b),
      x => Err(format!("Expected bool, found {:?}.", x))
    }
  }
}
impl Into<Result<FunctionRef, String>> for Value {
  fn into(self) -> Result<FunctionRef, String> {
    match self {
      Value::Function(f) => Ok(f),
      x => Err(format!("Expected function, found {:?}.", x))
    }
  }
}
impl Into<Result<Array, String>> for Value {
  fn into(self) -> Result<Array, String> {
    match self {
      Value::Array(a) => Ok(a),
      x => Err(format!("Expected array, found {:?}.", x))
    }
  }
}
impl Into<Result<StructVal, String>> for Value {
  fn into(self) -> Result<StructVal, String> {
    match self {
      Value::Struct(s) => Ok(s),
      x => Err(format!("Expected struct, found {:?}.", x))
    }
  }
}
