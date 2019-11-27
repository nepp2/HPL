
use bumpalo::Bump;
use std::ops::{Deref, DerefMut};
use std::fmt;
use std::borrow;
use core::hash::{Hash, Hasher};

const ARENA_SLOTS : usize = 4064;

static mut ARENA_IDS : [u64; ARENA_SLOTS] = [0; ARENA_SLOTS];
static mut NEXT_ARENA_ID : u64 = 1;
static mut NEXT_ARENA_SLOT : usize = 0;

unsafe fn next_id() -> u64 {
  NEXT_ARENA_ID += 1;
  NEXT_ARENA_ID
}

unsafe fn check_validity(id : u64, slot : usize) {
  if ARENA_IDS[slot] != id {
    panic!("Arena pointer used after arena was freed!");
  }
}

/// A user-friendly but slightly unsafe Arena type.
/// It should panic if an arena pointer is dereferenced after its arena is freed.
/// It is not thread-safe.
pub struct Arena {
  id : u64,
  slot : usize,
  bump : Bump,
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      check_validity(self.id, self.slot);
      ARENA_IDS[self.slot] = 0;
    }
  }
}

impl Arena {

  pub fn new() -> Self {
    unsafe {
      let id = next_id();
      for slot in 0..ARENA_SLOTS {
        let slot = (slot + NEXT_ARENA_SLOT) % ARENA_SLOTS;
        if ARENA_IDS[slot] == 0 {
          ARENA_IDS[slot] = id;
          NEXT_ARENA_SLOT = slot + 1;
          return Arena { id, slot, bump : Bump::new() };
        }
      }
    }
    panic!("no free arena slots!");
  }

  fn alloc_ap<T : ?Sized>(&self, t : &mut T) -> Ap<T> {
    Ap {
      arena_id: self.id,
      arena_slot: self.slot,
      ptr: t as *mut T,
    }
  }

  pub fn alloc<T : Copy>(&self, val : T) -> Ap<T> {
    self.alloc_ap(self.bump.alloc(val))
  }

  pub fn alloc_slice<T : Copy>(&self, vs : &[T]) -> Ap<[T]> {
    self.alloc_ap(self.bump.alloc_slice_copy(vs))
  }

  pub fn alloc_str(&self, s : &str) -> Ap<str> {
    let bytes = self.bump.alloc_slice_copy(s.as_bytes());
    let s = unsafe { std::str::from_utf8_unchecked_mut(bytes) };
    self.alloc_ap(s)
  }

  fn alloc_ap_mut<T : ?Sized>(&self, ap : Ap<T>) -> ApMut<T> {
    ApMut { ap }
  }

  pub fn alloc_mut<T : Copy>(&self, val : T) -> ApMut<T> {
    self.alloc_ap_mut(self.alloc(val))
  }

  pub fn alloc_slice_mut<T : Copy>(&self, vs : &[T]) -> ApMut<[T]> {
    self.alloc_ap_mut(self.alloc_slice(vs))
  }
}

/// An arena pointer. The safety of this is not checked by the compiler.
/// It is checked at runtime in debug mode.
/// This reference type also allows mutable multi-aliasing, which may be
/// a terrible idea. It's normally unsafe in Rust, but I'm not sure if it
/// really needs to be in a single-threaded context.
/// TODO: remove the safety checks in release mode
pub struct Ap<T : ?Sized>
{
  arena_id : u64,
  arena_slot : usize,
  ptr : *mut T,
}

impl<T : ?Sized> Copy for Ap<T> {}

impl<T : ?Sized> Clone for Ap<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl <T : ?Sized> Ap<T> {
  fn check_validity(&self) {
    unsafe { check_validity(self.arena_id, self.arena_slot); }
  }
}

impl <T : ?Sized + PartialEq> PartialEq for Ap<T> {
  fn eq(&self, other: &Self) -> bool {
      (&**self) == (&**other)
  }
}
impl <T : ?Sized + Eq + PartialEq> Eq for Ap<T> {}

impl<T : ?Sized> Deref for Ap<T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    self.check_validity();
    unsafe { &*self.ptr }
  }
}

// impl<T : ?Sized> DerefMut for Ap<T> {
//   fn deref_mut(&mut self) -> &mut Self::Target {
//     self.check_validity();
//     unsafe { &mut *self.ptr }
//   }
// }

impl<T: ?Sized + Hash> Hash for Ap<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Ap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Ap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Ap<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Ap<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

pub struct ApMut<T : ?Sized>
{
  ap : Ap<T>
}

impl <T : ?Sized> ApMut<T> {
  pub fn into_ap(self) -> Ap<T> {
    self.ap
  }
}

impl<T : ?Sized> Deref for ApMut<T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    self.ap.check_validity();
    unsafe { &*self.ap.ptr }
  }
}

impl<T : ?Sized> DerefMut for ApMut<T> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.ap.check_validity();
    unsafe { &mut *self.ap.ptr }
  }
}
