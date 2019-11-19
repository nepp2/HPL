// external C interface for the compiler (so that the language can use it)

use crate::compile::Compiler;
use crate::expr::{RefStr, Expr, ExprContent};

use std::fs::File;
use std::io::Read;
use std::ffi::CString;
use std::collections::HashMap;
use std::path::Path;
use std::fmt;

use libloading::{Library, Symbol};

use std::{thread, time};

/// A handle to a module
#[no_mangle]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct SModuleHandle {
  pub id : u64,
}

/// A borrowed slice that is compatible with the Cauldron's array representation
#[no_mangle]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct SSlice<T> {
  pub data : *mut T,
  pub length : u64,
}

impl <T> SSlice<T> {
  pub fn from_slice(s : &[T]) -> Self {
    let data = s.as_ptr() as *mut T;
    SSlice { data, length: s.len() as u64 }
  }

  pub fn as_slice(&self) -> &[T] {
    unsafe {
      std::slice::from_raw_parts(self.data, self.length as usize)
    }
  }
}

/// A sized string that is compatible with the Cauldron's string representation
pub type SStr = SSlice<u8>;

impl SStr {
  pub fn from_str(s : &str) -> Self {
    let data = (s as *const str) as *mut u8;
    SStr { data, length: s.len() as u64 }
  }

  pub fn as_str(&self) -> &str {
    unsafe {
      let slice = std::slice::from_raw_parts(self.data, self.length as usize);
      std::str::from_utf8_unchecked(slice)
    }
  }
}

impl fmt::Debug for SStr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.as_str())
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

#[no_mangle]
static TEST_GLOBAL : i64 = 47;

extern {
  pub fn malloc(size: usize) -> *mut u8;
  pub fn free(ptr: *mut u8);
  pub fn memcpy(dest : *mut u8, src: *const u8, count : usize) -> *mut u8;
}

#[no_mangle]
pub extern "C" fn load_quote(c : *mut Compiler, s : SStr) -> *mut u8 {
  let code_path = format!("{}code/{}.code", ROOT, s.as_str());
  let mut f = File::open(code_path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let c = unsafe { &mut *c };
  let expr = Box::new(c.parse(&code).unwrap());
  Box::into_raw(expr) as *mut u8
}

#[no_mangle]
pub extern "C" fn build_module(c : *mut Compiler, e : &Expr) -> SModuleHandle {
  // let c = unsafe { &mut *c };
  // let cm = c.load_module(e).expect("failed to build the module");
  // SModuleHandle { id: cm.info.id }
  loop {}
}

#[no_mangle]
pub extern "C" fn get_function(
  c : *mut Compiler, h : SModuleHandle, name : SStr)
    -> *mut u8
{
  // let c = unsafe { &mut *c };
  // let address =
  //   c.get_function_address(h.id, name.as_str())
  //   .expect("no matching function found");
  // address as *mut u8
  loop {}
}

#[no_mangle]
pub extern "C" fn template_quote(e : &Expr, args : SSlice<&Expr>) -> Box<Expr> {
  fn template(e : &Expr, args : &[&Expr], next_arg : &mut usize) -> Expr {
    if let Some((name, es)) = e.try_construct() {
      match name {
        "$" => {
          let new_e = args[*next_arg].clone();
          *next_arg += 1;
          new_e
        }
        _ => {
          let mut children = vec![];
          for expr in es {
            children.push(template(expr, args, next_arg));
          }
          let loc = e.loc;
          let content = ExprContent::list(name.into(), children);
          Expr { loc, content }
        }
      }
    }
    else {
      e.clone()
    }
  }
  Box::new(template(e, args.as_slice(), &mut 0))
}

#[no_mangle]
pub extern "C" fn print_string(s : SStr) {
  print!("{}", s.as_str());
}

pub extern "C" fn print_type<T : std::fmt::Display>(t : T) {
  print!("{}", t);
}

#[no_mangle]
pub extern "C" fn print_expr(e : &Expr) {
  println!("{}", e);
}

#[no_mangle]
pub extern "C" fn expr_to_string(out : &mut SStr, e : &Expr) {
  let string = format!("{}", e);
  let s = SStr::from_str(string.as_str());
  std::mem::forget(string);
  *out = s;
}

/// defined for the test suite only
#[no_mangle]
pub extern "C" fn test_add(a : i64, b : i64) -> i64 {
  a + b
}

#[no_mangle]
pub extern "C" fn thread_sleep(millis : u64) {
  let t = time::Duration::from_millis(millis);
  thread::sleep(t);
}

#[no_mangle]
pub extern "C" fn load_library_c(lib_name : SStr) -> usize {
  let lib = lib_name.as_str();
  let deps_path = format!("{}target/{}/deps/{}.dll", ROOT, MODE, lib);
  let local_path = format!("{}.dll", lib);
  let paths = [deps_path.as_str(), local_path.as_str()];
  paths.iter().cloned().flat_map(load_library).nth(0).unwrap_or(0)
}

static mut SHARED_LIBRARIES : Option<HashMap<usize, (RefStr, Library)>> = None;
static mut SHARED_LIB_HANDLE_COUNTER : usize = 0;

/// TODO: This is not thread-safe!
pub fn load_library(path : &str) -> Option<usize> {
  let path = Path::new(path);
  let file_name = path.file_name().unwrap().to_str().unwrap();
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

/// TODO: This is not thread-safe!
#[no_mangle]
pub extern "C" fn load_symbol(lib_handle : usize, symbol_name : SStr) -> usize {
  let s = CString::new(symbol_name.as_str()).unwrap();
  unsafe {
    if SHARED_LIBRARIES.is_none() {
      panic!();
    }
    let (_, lib) = SHARED_LIBRARIES.as_ref().unwrap().get(&lib_handle).unwrap();
    let symbol: Option<Symbol<*const ()>> =
      lib.get(s.as_bytes_with_nul()).ok();
    symbol.map(|sym| sym.into_raw().into_raw() as usize).unwrap_or(0)
  }
}

pub struct CSymbols {
  pub local_symbol_table : HashMap<RefStr, usize>,
  pub shared_libraries : HashMap<usize, (RefStr, Library)>,
  pub lib_handle_counter : usize,
}

impl CSymbols {
  pub fn new() -> CSymbols {
    CSymbols {
      local_symbol_table: HashMap::new(),
      shared_libraries: HashMap::new(),
      lib_handle_counter: 0,
    }
  }

  pub fn populate(&mut self) {
    let sym = &mut self.local_symbol_table;
    sym.insert("load_library".into(), (load_library_c as *const()) as usize);
    sym.insert("load_symbol".into(), (load_symbol as *const()) as usize);
    sym.insert("malloc".into(), (malloc as *const()) as usize);
    sym.insert("free".into(), (free as *const()) as usize);
    sym.insert("memcpy".into(), (memcpy as *const()) as usize);
    

    sym.insert("print_string".into(), (print_string as *const()) as usize);
    sym.insert("print_expr".into(), (print_expr as *const()) as usize);
    sym.insert("print_i64".into(), (print_type::<i64> as *const()) as usize);
    sym.insert("print_u64".into(), (print_type::<u64> as *const()) as usize);
    sym.insert("print_f64".into(), (print_type::<f64> as *const()) as usize);
    sym.insert("print_bool".into(), (print_type::<bool> as *const()) as usize);

    sym.insert("template_quote".into(),  (template_quote as *const()) as usize);
    sym.insert("thread_sleep".into(), (thread_sleep as *const()) as usize);
    sym.insert("load_quote".into(),  (load_quote as *const()) as usize);
    sym.insert("build_module".into(),  (build_module as *const()) as usize);
    sym.insert("get_function".into(),  (get_function as *const()) as usize);
    sym.insert("expr_to_string".into(),  (expr_to_string as *const()) as usize);

    sym.insert("test_add".into(), (test_add as *const()) as usize);
    sym.insert("test_global".into(), (&TEST_GLOBAL as *const i64) as usize);
  }

  pub fn add_symbol<T>(&mut self, name : &str, p : *mut T) {
    // This is a bit confusing. When we link to a global we do it by passing a
    // pointer. Since this global *is* a pointer, we have to pass a pointer to
    // a pointer, which requires another permanent heap allocation for indirection.
    // TODO: can this be improved?
    let p = Box::into_raw(Box::new(p));
    self.local_symbol_table.insert(name.into(), p as usize);
  }
}
