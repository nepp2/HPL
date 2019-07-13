// external C interface for the compiler (so that the language can use it)

use crate::jit::Interpreter;
use crate::lexer;
use crate::value::RefStr;

use std::ffi::CStr;
use std::os::raw::c_char;
use std::collections::HashMap;

use libloading::Library;

#[no_mangle]
pub extern fn create_interpreter() -> *mut Interpreter {
  Box::into_raw(Box::new(Interpreter::new()))
}

#[no_mangle]
pub extern fn drop_interpreter(i : *mut Interpreter) {
  unsafe { Box::from_raw(i) };
}

#[no_mangle]
pub extern fn lex_string(i : *mut Interpreter, code : *mut c_char) {
  let i = unsafe { &mut *i };
  let code = unsafe { CStr::from_ptr(code) };
  let _tokens =
    lexer::lex(code.to_str().unwrap(), &mut i.cache)
    .map_err(|mut es| es.remove(0)).unwrap();
  
}

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

type VoidPtr = *mut ();

#[cfg(not(debug_assertions))]
static MODE : &'static str = "release";
#[cfg(debug_assertions)]
static MODE : &'static str = "debug";

#[cfg(not(test))]
static ROOT : &'static str = "";
#[cfg(test)]
static ROOT : &'static str = "../";

extern {
  pub fn malloc(size: usize) -> *mut u8;
}

#[no_mangle]
pub extern "C" fn hello_world() {
  println!("Hello world");
}

#[no_mangle]
pub extern "C" fn load_library_c(file_name : ScriptString) -> usize {
  println!("calling the load library function");
  500
  /*
  match load_library(file_name.as_str()) {
    Some(v) => v,
    None => 0,
  }
  */
}

static mut SHARED_LIBRARIES : Option<HashMap<usize, (RefStr, Library)>> = None;
static mut SHARED_LIB_HANDLE_COUNTER : usize = 0;

/// TODO: This is not thread-safe!
pub fn load_library(file_name : &str) -> Option<usize> {
  let path = format!("{}target/{}/deps/{}", ROOT, MODE, file_name);
  let r = Library::new(path);
  if r.is_err() {
    return None;
  }
  let lib = r.unwrap();
  unsafe {
    if SHARED_LIBRARIES.is_none() {
      SHARED_LIBRARIES = Some(HashMap::new());
    }
    SHARED_LIB_HANDLE_COUNTER += 1;
    let handle = SHARED_LIB_HANDLE_COUNTER;
    SHARED_LIBRARIES.as_mut().unwrap().insert(handle, (file_name.into(), lib));
    Some(handle)
  }
}

pub struct CLibraries {
  pub local_symbol_table : HashMap<RefStr, usize>,
  pub shared_libraries : HashMap<usize, (RefStr, Library)>,
  pub lib_handle_counter : usize,
}

impl CLibraries {
  pub fn new() -> CLibraries {
    let mut cache = HashMap::new();
    cache.insert("load_library".into(), (load_library_c as *const()) as usize);
    cache.insert("malloc".into(), (malloc as *const()) as usize);
    cache.insert("hello".into(), (hello_world as *const()) as usize);

    CLibraries {
      local_symbol_table: cache,
      shared_libraries: HashMap::new(),
      lib_handle_counter: 0,
    }
  }
}
