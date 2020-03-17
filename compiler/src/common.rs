
use std::fmt;
use std::rc::Rc;
use std::collections::HashSet;
use std::cell::RefCell;

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Ord, PartialOrd)]
pub struct Uid(u64);

impl Uid {
  pub fn null() -> Uid {
    Uid(0)
  }

  pub fn inner(self) -> u64 {
    self.0
  }
}

impl  fmt::Display for Uid {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:X}", self.0)
  }
}

pub struct UIDGenerator {
  gen : u64,
}

impl UIDGenerator {
  pub fn new() -> Self {
    UIDGenerator { gen : 1 }
  }

  pub fn next(&mut self) -> Uid {
    let uid = self.gen;
    self.gen += 1;
    Uid(uid)
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Ord, PartialOrd)]
pub struct UnitId(Uid);

impl UnitId {
  pub fn inner(self) -> Uid {
    self.0
  }
}

pub type SourceId = UnitId;

pub fn no_source() -> SourceId {
  create_unit(Uid::null())
}

pub fn create_unit(uid : Uid) -> UnitId {
  UnitId(uid)
}

/// This cache uses internal mutability to cache strings. It should be safe,
/// because the strings themselves are immutable.
/// It's not threadsafe, but I think RefCell should prevent it from being
/// passed to multiple threads.
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
