
#[no_mangle]
pub extern "C" fn function_from_dll2(a : i64, b : i64) -> i64 {
  a - b
}
