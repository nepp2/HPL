
use bumpalo::Bump;

pub struct Arena {
  bump : Bump,
}

impl Arena {

  pub fn new() -> Self {
    Arena { bump : Bump::new() }
  }

  pub fn alloc<T>(&self, val : T) -> &mut T {
    self.bump.alloc(val)
  }

  pub fn alloc_slice_copy<T : Copy>(&self, vs : &[T]) -> &mut [T] {
    self.bump.alloc_slice_copy(vs)
  }

  pub fn alloc_str(&self, s : &str) -> &str {
    let bytes = self.alloc_slice_copy(s.as_bytes());
    std::str::from_utf8_unchecked(bytes)
  }
}
