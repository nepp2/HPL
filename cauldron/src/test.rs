
use compiler as cc;
use cc::error::Error;
use cc::jit::Interpreter;
use cc::typecheck::Val;
use dlltest::function_from_dll;
use llvm_sys::support::LLVMLoadLibraryPermanently;

fn result_string(r : Result<Val, Error>) -> String {
  match r {
    Ok(v) => format!("{:?}", v),
    Err(e) => format!("{}", e),
  }
}

fn assert_result_with_interpreter(i : &mut Interpreter, code : &str, expected_result : Val){
  let expected = Ok(expected_result);
  let result = i.run(code);
  assert!(
    result == expected,
    "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
    code, result_string(expected), result_string(result));
}

fn assert_result(code : &str, expected_result : Val){
  let mut i = Interpreter::new();
  assert_result_with_interpreter(&mut i, code, expected_result)
}

/*
TODO: Fairly sure there's some undefined behaviour in at least one of these tests, causing it to
crash unpredictably. Haven't found a test that crashes reliably though. Also, I'm not sure the
crash happens at all without interaction between tests, now that they run in separate processes.

UPDATE: The test failure _may_ could have been caused by Rust running tests in parallel. I'm not
sure if I'm using LLVM in a way that can be multithreaded.
*/

// Runs the tests in isolated processes, because they do unsafe things and could pollute each other.
rusty_fork_test! {
  #[test]
  fn test_dll_function_linking() {
    function_from_dll(4, 4);
    // This makes sure that any symbols in the main executable can be
    // linked to the code we generate with the JIT. This includes any
    // DLLs used by the main exe.
    unsafe { LLVMLoadLibraryPermanently(std::ptr::null()) };
    let code = "
      cfun function_from_dll(a : i64, b : i64) : i64
      function_from_dll(17, 7)
    ";
    assert_result(code, Val::I64(24));
  }

  /* TODO: FIX THIS
  #[test]
  fn test_executable_function_linking() {
    let code = "
      cfun function_from_executable(a : i64, b : i64) : i64
      function_from_executable(17, 7)
    ";
    assert_result(code, Val::I64(24));
  }
  */

}
