
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

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum Type {
  Unit,
  Float,
  String,
  Bool,
  Array,
  Function,
  Struct{ module: Symbol, name: Symbol },
  Any,
  External(Symbol),
}

impl Type {
  pub fn name(&self, sym : &mut SymbolTable) -> Symbol {
    use self::Type::*;
    match self {
      Float => sym.get("float"),
      Any => sym.get("any"),
      Array => sym.get("array"),
      Bool => sym.get("bool"),
      String => sym.get("string"),
      Function => sym.get("function"),
      Struct{ name, .. } => *name,
      External(e) => *e,
      Unit => sym.get("unit"),
    }
  }

  pub fn str(&self) -> &'static str {
    use self::Type::*;
    match self {
      Float => "float",
      Any => "any",
      Array => "array",
      Bool => "bool",
      String => "string",
      Function => "function",
      Struct { .. } => "struct",
      External(_) => "external",
      Unit => "unit",
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

pub fn display_expr(e: &Expr, sym : &mut SymbolTable) -> String {
  pub fn display_inner(e: &Expr, sym : &mut SymbolTable, w: &mut fmt::Write, indent : usize) -> fmt::Result {
    match &e.tag {
      ExprTag::Tree(symbol) => {
        let s = sym.str(*symbol);
        write!(w, "({}", s)?;
        if s == "block" {
          let indent = indent + 2;
          for c in e.children.iter() {
            writeln!(w)?;
            write!(w, "{:indent$}", "", indent=indent)?;
            display_inner(c, sym, w, indent)?
          }
        }
        else {
          for c in e.children.iter() {
            write!(w, " ")?;
            display_inner(c, sym, w, indent)?
          }
        }
        write!(w, ")")
      }
      ExprTag::Symbol(x) => write!(w, "{}", sym.str(*x)),
      ExprTag::LiteralString(x) => write!(w, "{}", sym.str(*x)),
      ExprTag::LiteralFloat(x) => write!(w, "{}", x),
      ExprTag::LiteralBool(x) => write!(w, "{}", x),
      ExprTag::LiteralUnit => write!(w, "()"),
    }
  }
  let mut buf = String::new();
  display_inner(e, sym, &mut buf, 0).unwrap();
  buf
}

impl Expr {
  pub fn tree_symbol_unwrap(&self) -> Result<Symbol, Error> {
    if let ExprTag::Tree(s) = &self.tag {
      Ok(*s)
    }
    else {
      error(self, format!("expected a tree, found {:?}", self))
    }
  }

  pub fn symbol_unwrap(&self) -> Result<Symbol, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(*s)
    }
    else {
      error(self, format!("expected a symbol, found {:?}", self))
    }
  }

  /* TODO: remove?
  pub fn symbol_to_refstr(&self) -> Result<RefStr, Error> {
    self.symbol_unwrap().map(|s| s.clone())
  }
  */
}

impl <'l> Into<TextLocation> for &'l Expr {
  fn into(self) -> TextLocation {
    self.loc
  }
}

#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub struct Symbol { id : u64 }

#[derive(Default)]
pub struct SymbolTable {
  symbol_map : HashMap<RefStr, Symbol>,
  symbols : Vec<RefStr>,  
}

impl SymbolTable {
  pub fn new() -> SymbolTable {
    Default::default()
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
  pub name : Symbol,
  pub module : Symbol,
  pub fields : Vec<Symbol>,
}

#[derive(PartialEq)]
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
  pub name : Symbol,
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
  String(Symbol),
  Function(FunctionRef),
  Struct(StructVal),
  External(ExternalVal),
  Unit,
}

#[derive(Clone)]
pub struct ExternalVal {
  pub type_name : Symbol,
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
        module: s.borrow().def.module,
        name: s.borrow().def.name,
      },
      External(e) => Type::External(e.type_name),
      Unit => Type::Unit,
    }
  }

  fn write(&self, w: &mut fmt::Write, sym : &mut SymbolTable) -> fmt::Result {
    match self {
      Value::Float(x) => write!(w, "{}", x),
      Value::Array(a) => {
        write!(w, "[")?;
        let a = a.borrow();
        let mut i = a.iter();
        if let Some(v) = i.next() { v.write(w, sym)? }
        for v in i {
          write!(w, ", ")?;
          v.write(w, sym)?;
        }
        write!(w, "]")
      }
      Value::Bool(b) => write!(w, "{}", b),
      Value::String(s) => write!(w, "{}", sym.str(*s)),
      Value::Function(fr) => write!(w, "{}(..)", sym.str(fr.name)),
      Value::External(e) => write!(w, "external({})", sym.str(e.type_name)),
      Value::Struct(s) => {
        let Struct { def, fields } = &*s.borrow();
        let name = def.name;
        write!(w, "{} {{ ", sym.str(name))?;
        let end = fields.len() - 1;
        for (i, (n, v)) in def.fields.iter().zip(fields.iter()).enumerate() {
          write!(w, "{}: ", sym.str(*n))?;
          v.write(w, sym)?;
          write!(w, "{} ", if i == end {""} else {","})?;
        }
        write!(w, "}}")
      }
      Value::Unit => write!(w, "Unit"),
    }
  }

  pub fn to_string(&self, sym : &mut SymbolTable) -> String {
    let mut s = String::new();
    self.write(&mut s, sym).unwrap();
    s
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
impl From<Symbol> for Value {
  fn from(v : Symbol) -> Value {
    Value::String(v)
  }
}

impl Into<Result<f32, String>> for Value {
  fn into(self) -> Result<f32, String> {
    match self {
      Value::Float(f) => Ok(f), 
      x => Err(format!("Expected float, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<Symbol, String>> for Value {
  fn into(self) -> Result<Symbol, String> {
    match self {
      Value::String(s) => Ok(s),
      x => Err(format!("Expected string, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<bool, String>> for Value {
  fn into(self) -> Result<bool, String> {
    match self {
      Value::Bool(b) => Ok(b),
      x => Err(format!("Expected bool, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<FunctionRef, String>> for Value {
  fn into(self) -> Result<FunctionRef, String> {
    match self {
      Value::Function(f) => Ok(f),
      x => Err(format!("Expected function, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<Array, String>> for Value {
  fn into(self) -> Result<Array, String> {
    match self {
      Value::Array(a) => Ok(a),
      x => Err(format!("Expected array, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<StructVal, String>> for Value {
  fn into(self) -> Result<StructVal, String> {
    match self {
      Value::Struct(s) => Ok(s),
      x => Err(format!("Expected struct, found {:?}.", x.to_type().str()))
    }
  }
}

impl Into<Result<ExternalVal, String>> for Value {
  fn into(self) -> Result<ExternalVal, String> {
    match self {
      Value::External(v) => Ok(v),
      x => Err(format!("Expected struct, found {:?}.", x.to_type().str()))
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

  /*
  pub fn type_name(&self, sym : &mut SymbolTable) -> RefStr {
    self.tag.name(sym)
  }
  */
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