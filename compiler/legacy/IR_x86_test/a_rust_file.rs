
#[no_mangle]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct ScriptString {
  pub ptr : *mut u8,
  pub length : u64,
}

impl ScriptString {
  pub fn as_str(&self) -> &str {
    let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.length as usize) };
    std::str::from_utf8(slice).expect("wasn't a valid utf8 string!")
  }
}

#[no_mangle]
pub extern "C" fn print(s : ScriptString) {
  println!("{}", s.as_str());
}
