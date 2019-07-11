// external C interface for the compiler (so that the language can use it)

use crate::jit::Interpreter;
use crate::lexer;

use std::ffi::CStr;
use std::os::raw::c_char;

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
    lexer::lex(code.to_str().unwrap(), &mut i.sym)
    .map_err(|mut es| es.remove(0)).unwrap();
  
}
/*
fn load_and_run(path : &str) {
  let path = PathBuf::from(path);
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let mut i = Interpreter::new();
  let result = i.run(&code);
  println!("{}", print_result(result));
}
*/
