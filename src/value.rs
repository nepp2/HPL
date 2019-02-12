
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashSet;
use std::collections::HashMap;
use std::any::Any;

use crate::error::{Error, TextLocation, error, ErrorContent};

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
  Struct{ module: RefStr, name: RefStr },
  Any,
  External(RefStr),
}

impl Type {
  pub fn name(&self) -> RefStr {
    use self::Type::*;
    match self {
      Float => "float".into(),
      Any => "any".into(),
      Array => "array".into(),
      Bool => "bool".into(),
      String => "string".into(),
      Function => "function".into(),
      Struct{ name, .. } => name.clone(),
      External(e) => e.clone(),
      Unit => "unit".into(),
    }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprTag {
  Tree(Symbol),
  Symbol(Symbol),
  LiteralString(Symbol),
  LiteralFloat(f32),
  LiteralBool(bool),
  LiteralUnit,
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
    ExprTag::LiteralUnit => write!(f, "()"),
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

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Symbol { id : u64 }

pub struct Keywords {
  
}

pub struct SymbolTable {
  symbol_map : HashMap<RefStr, Symbol>,
  symbols : Vec<RefStr>,
  keywords : Keywords,
}

impl SymbolTable {
  pub fn new() -> SymbolTable {
    SymbolTable {
      symbol_map: Default::default(),
      symbols: Default::default(),
      keywords: Keywords{},
    }
  }

  pub fn get<S : AsRef<str> + Into<RefStr>>(&mut self, s : S) -> Symbol {
    if let Some(symbol) = self.symbol_map.get(s.as_ref()) {
      *symbol
    }
    else{
      let symbol = Symbol { id : self.symbols.len() as u64 };
      let string : RefStr = s.into();
      self.symbols.push(string.clone());
      self.symbol_map.insert(string, symbol);
      symbol
    }
  }

  pub fn refstr(&self, symbol : Symbol) -> RefStr {
    self.symbols[symbol.id as usize].clone()
  }

  pub fn str(&self, symbol : Symbol) -> &str {
    self.symbols[symbol.id as usize].as_ref()
  }
}

#[derive(Debug, PartialEq)]
pub struct StructDef {
  pub name : RefStr,
  pub module : RefStr,
  pub fields : Vec<RefStr>,
}

#[derive(Debug, PartialEq)]
pub struct Struct {
  pub def : Rc<StructDef>,
  pub fields : Vec<Value>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ModuleId {
  pub i : usize
}

#[derive(Clone, PartialEq)]
pub struct FunctionRef {
  pub name : RefStr,
  pub visible_modules : Vec<ModuleId>,
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
  External(ExternalVal),
  Unit,
}

#[derive(Clone)]
pub struct ExternalVal {
  pub type_name : RefStr,
  pub val : Rc<RefCell<Any>>,
}

impl PartialEq for ExternalVal {
  fn eq(&self, rhs : &ExternalVal) -> bool {
    Rc::ptr_eq(&self.val, &rhs.val)
  }
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
      Struct(s) => Type::Struct{
        module: s.borrow().def.module.clone(),
        name: s.borrow().def.name.clone(),
      },
      External(e) => Type::External(e.type_name.clone()),
      Unit => Type::Unit,
    }
  }

  pub fn type_name(&self) -> RefStr {
    use self::Value::*;
    match self {
      Float(_) => "float".into(),
      Array(_) => "array".into(),
      Bool(_) => "bool".into(),
      String(_) => "string".into(),
      Function(_) => "function".into(),
      Struct(s) => s.borrow().def.name.clone(),
      External(e) => e.type_name.clone(),
      Unit => "unit".into(),
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
      Value::Function(fr) => write!(f, "{}(..)", fr.name),
      Value::External(e) => write!(f, "external({})", e.type_name),
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
impl From<Vec<Value>> for Value {
  fn from(v : Vec<Value>) -> Value {
    Value::Array(Rc::new(RefCell::new(v)))
  }
}
impl From<&str> for Value {
  fn from(v : &str) -> Value {
    Value::String(v.into())
  }
}
impl From<String> for Value {
  fn from(v : String) -> Value {
    Value::String(v.into())
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
impl Into<Result<RefStr, String>> for Value {
  fn into(self) -> Result<RefStr, String> {
    match self {
      Value::String(s) => Ok(s),
      x => Err(format!("Expected string, found {:?}.", x))
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

impl Into<Result<ExternalVal, String>> for Value {
  fn into(self) -> Result<ExternalVal, String> {
    match self {
      Value::External(v) => Ok(v),
      x => Err(format!("Expected struct, found {:?}.", x))
    }
  }
}

// ### VALUE 2 ###

#[derive(Clone, PartialEq)]
pub enum ValInternal {
  Small(u64),
  Big(Rc<RefCell<Vec<u8>>>),
}

#[derive(Clone, PartialEq)]
pub struct Value2 {
  tag : Type,
  value : ValInternal,
}

impl Value2 {
  pub fn to_type(&self) -> Type {
    self.tag.clone()
  }

  pub fn type_name(&self) -> RefStr {
    self.tag.name()
  }
}

const BOOL_TRUE : u64 = 1;
const BOOL_FALSE : u64 = 0;

use self::ValInternal::*;

impl From<bool> for Value2 {
  fn from(b : bool) -> Value2 {
    let v = if b { BOOL_TRUE } else { BOOL_FALSE };
    Value2 { tag: Type::Bool, value: Small(v)}
  }
}
impl From<f32> for Value2 {
  fn from(f : f32) -> Value2 {
    let v = f.to_bits() as u64;
    Value2 { tag: Type::Float, value: Small(v)}
  }
}

/*
impl From<Vec<Value2>> for Value2 {
  fn from(v : Vec<Value2>) -> Value2 {
    Value2::Array(Rc::new(RefCell::new(v)))
  }
}
impl From<&str> for Value2 {
  fn from(v : &str) -> Value2 {
    Value2::String(v.into())
  }
}
impl From<String> for Value2 {
  fn from(v : String) -> Value2 {
    Value2::String(v.into())
  }
}

impl Into<Result<f32, String>> for Value2 {
  fn into(self) -> Result<f32, String> {
    match self {
      Value2::Float(f) => Ok(f), 
      x => Err(format!("Expected float, found {:?}.", x))
    }
  }
}
impl Into<Result<RefStr, String>> for Value2 {
  fn into(self) -> Result<RefStr, String> {
    match self {
      Value2::String(s) => Ok(s),
      x => Err(format!("Expected string, found {:?}.", x))
    }
  }
}
impl Into<Result<bool, String>> for Value2 {
  fn into(self) -> Result<bool, String> {
    match self {
      Value2::Bool(b) => Ok(b),
      x => Err(format!("Expected bool, found {:?}.", x))
    }
  }
}
impl Into<Result<FunctionRef, String>> for Value2 {
  fn into(self) -> Result<FunctionRef, String> {
    match self {
      Value2::Function(f) => Ok(f),
      x => Err(format!("Expected function, found {:?}.", x))
    }
  }
}
impl Into<Result<Array, String>> for Value2 {
  fn into(self) -> Result<Array, String> {
    match self {
      Value2::Array(a) => Ok(a),
      x => Err(format!("Expected array, found {:?}.", x))
    }
  }
}
impl Into<Result<StructVal, String>> for Value2 {
  fn into(self) -> Result<StructVal, String> {
    match self {
      Value2::Struct(s) => Ok(s),
      x => Err(format!("Expected struct, found {:?}.", x))
    }
  }
}

impl Into<Result<ExternalVal, String>> for Value2 {
  fn into(self) -> Result<ExternalVal, String> {
    match self {
      Value2::External(v) => Ok(v),
      x => Err(format!("Expected struct, found {:?}.", x))
    }
  }
}
*/