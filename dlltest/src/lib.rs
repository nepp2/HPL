
#[no_mangle]
pub extern "C" fn function_from_dll(a : i64, b : i64) -> i64 {
  println!("Calling function from dll!");
  a + b
}

#[no_mangle]
pub extern "C" fn another_function_from_dll(a : i64, b : i64) -> i64 {
  println!("Calling another function from dll!");
  a + b
}

/*
#[no_mangle]
#[derive(PartialEq, Debug, Copy, Clone)]
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
*/

#[no_mangle]
pub extern "C" fn print(ptr : *mut u8, length : u64) {
  let slice = unsafe { std::slice::from_raw_parts(ptr, length as usize) };
  let s = std::str::from_utf8(slice).expect("wasn't a valid utf8 string!");
  println!("{}", s);
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(crate::function_from_dll(2, 2), 4);
    }
}
