
use std::fmt;
use std::rc::Rc;
use std::collections::HashSet;
use std::cell::RefCell;

/// An immutable, reference counted string
pub type RefStr = Rc<str>;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Ord, PartialOrd)]
pub struct Uid(u64);

impl  fmt::Display for Uid {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let Uid(id) = *self;
    write!(f, "{:X}", id)
  }
}

pub struct UIDGenerator {
  gen : u64,
}

impl UIDGenerator {
  pub fn new() -> Self {
    UIDGenerator { gen : 0 }
  }

  pub fn next(&mut self) -> Uid {
    let uid = self.gen;
    self.gen += 1;
    Uid(uid)
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Ord, PartialOrd)]
pub struct UnitId(Uid);

pub type SourceId = Option<UnitId>;

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
