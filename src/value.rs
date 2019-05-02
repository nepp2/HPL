
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::any::Any;
use std::mem;

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
  Map,
  Any,
  External(RefStr),
}

impl Type {
  pub fn name(&self, sym : &mut SymbolTable) -> RefStr {
    use self::Type::*;
    match self {
      Float => sym.get("float"),
      Any => sym.get("any"),
      Array => sym.get("array"),
      Bool => sym.get("bool"),
      String => sym.get("string"),
      Function => sym.get("function"),
      Map => sym.get("map"),
      External(e) => e.clone(),
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
      Map => "map",
      External(_) => "external",
      Unit => "unit",
    }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ExprTag {
  Tree(RefStr),
  Symbol(RefStr),
  LiteralString(RefStr),
  LiteralFloat(f32),
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
      ExprTag::LiteralBool(x) => write!(w, "{}", x),
      ExprTag::LiteralUnit => write!(w, "()"),
    }
  }
  let mut buf = String::new();
  display_inner(e, &mut buf, 0).unwrap();
  buf
}

impl Expr {
  pub fn tree_symbol_unwrap(&self) -> Result<RefStr, Error> {
    if let ExprTag::Tree(s) = &self.tag {
      Ok(s.clone())
    }
    else {
      error(self, format!("expected a tree, found {:?}", self))
    }
  }

  pub fn symbol_unwrap(&self) -> Result<RefStr, Error> {
    if let ExprTag::Symbol(s) = &self.tag {
      Ok(s.clone())
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

#[derive(Default)]
pub struct SymbolTable {
  symbols : HashSet<RefStr>,
}

impl SymbolTable {
  pub fn new() -> SymbolTable {
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

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ModuleId {
  pub i : usize
}

#[derive(Clone, PartialEq)]
pub struct FunctionRef {
  pub module : ModuleId,
  pub name : RefStr,
}

pub type MapVal = Rc<RefCell<HashMap<RefStr, Value>>>;

pub type Array = Rc<RefCell<Vec<Value>>>;

/// Represents a value in the interpreted language.
/// Currently uses 16 bytes. I think this is because there are 8 byte
/// RC pointers in the union, and the discriminating value is being
/// padded to word size (also 8 bytes). Could probably be optimised
/// down to 8 bytes total, with some ugly pointer hacks.
#[derive(Clone, PartialEq)]
pub enum Value {
  Float(u64),
  Array(Array),
  Bool(u64),
  String(RefStr),
  Function(FunctionRef),
  Map(MapVal),
  External(ExternalVal),
  Unit,
}

pub fn expr_to_value(e : &Expr, sym : &mut SymbolTable) -> Value {
  use self::ExprTag::*;
  let mut m = HashMap::new();
  match &e.tag {
    Tree(s) => {
      m.insert(sym.get("tag"), Value::from(sym.get("expr")));
      m.insert(sym.get("value"), Value::from(s.clone()));
    }
    Symbol(s) => {
      m.insert(sym.get("tag"), Value::from(sym.get("symbol")));
      m.insert(sym.get("value"), Value::from(s.clone()));
    }
    LiteralString(s) => {
      m.insert(sym.get("tag"), Value::from(sym.get("literal_string")));
      m.insert(sym.get("value"), Value::from(s.clone()));
    }
    LiteralFloat(f) => {
      m.insert(sym.get("tag"), Value::from(sym.get("literal_float")));
      m.insert(sym.get("value"), Value::from(f.clone()));
    }
    LiteralBool(b) => {
      m.insert(sym.get("tag"), Value::from(sym.get("literal_bool")));
      m.insert(sym.get("value"), Value::from(b.clone()));
    }
    LiteralUnit => {
      m.insert(sym.get("tag"), Value::from(sym.get("literal_unit")));
    }
  }
  if e.children.len() > 0 {
    let children : Vec<Value> = e.children.iter().map(|e| expr_to_value(e, sym)).collect();
    m.insert(sym.get("children"), Value::from(children));
  }
  m.insert(sym.get("start_line"), Value::from(e.loc.start.line as f32));
  m.insert(sym.get("start_col"), Value::from(e.loc.start.col as f32));
  m.insert(sym.get("end_line"), Value::from(e.loc.end.line as f32));
  m.insert(sym.get("end_col"), Value::from(e.loc.end.col as f32));
  Value::Map(Rc::new(RefCell::new(m)))
}

pub fn value_to_expr(v : Value, sym : &mut SymbolTable) -> Result<Expr, ErrorContent> {
  fn get(m : &HashMap<RefStr, Value>, s : &str, sym : &mut SymbolTable) -> Result<Value, ErrorContent> {
    m.get(&sym.get(s)).map(|v| v.clone()).ok_or_else(|| format!("expected key '{}' in map", s).into())
  }

  let m = v.convert::<MapVal>()?;
  let m = m.borrow();
  let tag = get(&m, "tag", sym)?.convert::<RefStr>()?;
  let start_line = get(&m, "start_line", sym)?.convert::<f32>()? as usize;
  let start_col = get(&m, "start_col", sym)?.convert::<f32>()? as usize;
  let end_line = get(&m, "end_line", sym)?.convert::<f32>()? as usize;
  let end_col = get(&m, "end_col", sym)?.convert::<f32>()? as usize;
  let expr_tag = match tag.as_ref() {
    "expr" => {
      let s = get(&m, "value", sym)?.convert::<RefStr>()?;
      ExprTag::Tree(s)
    },
    "symbol" => {
      let s = get(&m, "value", sym)?.convert::<RefStr>()?;
      ExprTag::Symbol(s)
    },
    "literal_string" => {
      let s = get(&m, "value", sym)?.convert::<RefStr>()?;
      ExprTag::LiteralString(s)
    },
    "literal_float" => {
      let f = get(&m, "value", sym)?.convert::<f32>()?;
      ExprTag::LiteralFloat(f)
    },
    "literal_bool" => {
      let b = get(&m, "end_col", sym)?.convert::<bool>()?;
      ExprTag::LiteralBool(b)
    },
    "literal_unit" => {
      ExprTag::LiteralUnit
    },
    _ => return Err(format!("found unexpected expr tag '{}'", tag).into()),
  };
  let mut children = vec![];
  if let Some(c) = m.get(&sym.get("children")) {
    let a = c.clone().convert::<Array>()?;
    for v in a.borrow().iter() {
      children.push(value_to_expr(v.clone(), sym)?);
    }
  }
  let e = Expr {
    tag: expr_tag, children, loc: TextLocation::new((start_line, start_col), (end_line, end_col))
  };
  Ok(e)
}

fn bits_to_f32(b : u64) -> f32 {
  f32::from_bits(b as u32)
}

fn bits_to_bool(b : u64) -> bool {
  b != 0
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
      Function{..} => Type::Function,
      Map(_) => Type::Map,
      External(e) => Type::External(e.type_name.clone()),
      Unit => Type::Unit,
    }
  }

  fn write(&self, w: &mut fmt::Write, sym : &mut SymbolTable) -> fmt::Result {
    match self {
      Value::Float(x) => {
        write!(w, "{}", bits_to_f32(*x))
      }
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
      Value::Bool(b) => write!(w, "{}", bits_to_bool(*b)),
      Value::String(s) => write!(w, "{}", s),
      Value::Function(f) => write!(w, "{}(..)", f.name),
      Value::External(e) => write!(w, "external({})", e.type_name),
      Value::Map(m) => {
        let map = &*m.borrow();
        // TODO
        //let name = def.name;
        //write!(w, "{} {{ ", sym.str(name))?;
        write!(w, "{{ ")?;
        let end = map.len() - 1;
        for (i, (n, v)) in map.iter().enumerate() {
          write!(w, "{}: ", *n)?;
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

  pub fn convert<T>(self) -> Result<T, String>
    where Value: Into<Result<T, String>>
  {
    let r : Result<T, String> = self.into();
    return r;
  }

  /// Return the borrowed value and replace it in-place with Unit
  pub fn get(&mut self) -> Value {
    mem::replace(self, Value::Unit)
  }
}

impl From<bool> for Value {
  fn from(v : bool) -> Value {
    Value::Bool(if v { 1 } else { 0 })
  }
}
impl From<f32> for Value {
  fn from(v : f32) -> Value {
    Value::Float(v.to_bits() as u64)
  }
}
impl From<Vec<Value>> for Value {
  fn from(v : Vec<Value>) -> Value {
    Value::Array(Rc::new(RefCell::new(v)))
  }
}
impl From<RefStr> for Value {
  fn from(v : RefStr) -> Value {
    Value::String(v)
  }
}

impl Into<Result<f32, String>> for Value {
  fn into(self) -> Result<f32, String> {
    match self {
      Value::Float(f) => Ok(bits_to_f32(f)),
      x => Err(format!("Expected float, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<RefStr, String>> for Value {
  fn into(self) -> Result<RefStr, String> {
    match self {
      Value::String(s) => Ok(s),
      x => Err(format!("Expected string, found {:?}.", x.to_type().str()))
    }
  }
}
impl Into<Result<bool, String>> for Value {
  fn into(self) -> Result<bool, String> {
    match self {
      Value::Bool(b) => Ok(bits_to_bool(b)),
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
impl Into<Result<MapVal, String>> for Value {
  fn into(self) -> Result<MapVal, String> {
    match self {
      Value::Map(s) => Ok(s),
      x => Err(format!("Expected map, found {:?}.", x.to_type().str()))
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
