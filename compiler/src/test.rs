
use crate::error::Error;
use crate::jit::Interpreter;
use crate::typecheck::Val;
use crate::c_interface::ScriptString;

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
  fn test_basics() {
    let cases = vec![
      ("", Val::Void),
      ("()", Val::Void),
      ("4 + 5", Val::I64(9)),
      ("4. + 5.5", Val::F64(9.5)),
      ("4 - 5", Val::I64(-1)),
      ("4 * 5", Val::I64(20)),
      ("20 > 5", Val::Bool(true)),
      ("20 < 5", Val::Bool(false)),
      ("5 <= 5", Val::Bool(true)),
      ("5 >= 5", Val::Bool(true)),
      ("5 == 5", Val::Bool(true)),
      ("-(4 - 5)", Val::I64(1)),
      ("4 + (let a = 5; let b = 4; a)", Val::I64(9)),
      ("if true then 3 else 4 end", Val::I64(3)),
      ("if false then 3 else 4 end", Val::I64(4)),
      ("let a = 5; a", Val::I64(5)),
    ];
    for (code, expected_result) in cases {
      assert_result(code, expected_result);
    }
  }

  #[test]
  fn test_conversions() {
    let cases = vec![
      ("4.5 as i32", Val::I32(4)),
      ("4 as u32", Val::U32(4)),
      ("4 as f64", Val::F64(4.0)),
      ("4 as f32", Val::F32(4.0)),
      ("(4 as u32) as i64", Val::I64(4)),
      ("(4 as u32) as u64", Val::U64(4)),
      ("(-4 as i32) as u64", Val::U64((-4 as i32) as u64)),
      ("-4 as u32", Val::U32((-4 as i32) as u32)),
    ];
    for (code, expected_result) in cases {
      assert_result(code, expected_result);
    }
  }

  #[test]
  fn test_and_or() {
    assert_result("true && false", Val::Bool(false));
    assert_result("true || false", Val::Bool(true));
    // Make sure they terminate early
    let and = "
      let a = 0
      false && (a = 1; true)
      a
    ";
    let or = "
      let a = 0
      true || (a = 1; true)
      a
    ";
    assert_result(and, Val::I64(0));
    assert_result(or, Val::I64(0));
  }

  #[test]
  fn test_scope(){
    let code = "
      let a = 4
      let b = if true
        let a = 5
        a
      else
        10
      end
      a + b
    ";
    assert_result(code, Val::I64(9));
  }

  #[test]
  fn test_assignment(){
    let a = "
      let a = 4
      a = a + 5
      a
    ";
    let b = "
      struct point
        x : i64
        y : i64
      end
      let a = point{x: 5, y: 50}
      a.x = a.x + 10
      a.y = 500
      a.x + a.y
    ";
    assert_result(a, Val::I64(9));
    assert_result(b, Val::I64(515));
  }

  #[test]
  fn test_struct() {
    let code = "
      struct point
        x : i64
        y : i64
      end
      fun foo(a : point, b : point)
        point{x: a.x + b.x, y: a.y + b.y}
      end
      let a = point{x: 10, y: 1}
      let b = point{2, 20}
      let c = foo(a, b)
      c.y
    ";
    assert_result(code, Val::I64(21));
  }

  #[test]
  fn test_return(){
    let code = "
      fun foo(v : bool)
        if v
          return 10
        end
        20
      end
      foo(true) + foo(false)
    ";
    assert_result(code, Val::I64(30));
  }

  #[test]
  fn test_while() {
    let a = "
      let x = 10
      while true
        x = x - 1
        if x <= 5
          break
        end
      end
      x
    ";
    assert_result(a, Val::I64(5));
    let b = "
      let x = 1
      while x < 10
        x = x + 6
      end
      x
    ";
    assert_result(b, Val::I64(13));
  }

  #[test]
  fn test_jit_module_variable_linking() {
    let mut i = Interpreter::new();
    let a = "let foo = 5";
    let b = "foo";
    assert_result_with_interpreter(&mut i, a, Val::Void);
    assert_result_with_interpreter(&mut i, b, Val::I64(5));
  }

  #[test]
  fn test_jit_module_function_linking() {
    let mut i = Interpreter::new();
    let a = "
      fun foobar()
        843
      end";
    let b = "foobar()";
    assert_result_with_interpreter(&mut i, a, Val::Void);
    assert_result_with_interpreter(&mut i, b, Val::I64(843));
  }

  #[test]
  fn test_arrays() {
    let code = "
      let a = [0, 1, 2, 3, 6]
      a[1] = 50
      a[1] + a[4]
    ";
    assert_result(code, Val::I64(56));
  }

  #[test]
  fn test_struct_format() {
    let mut i = Interpreter::new();
    #[repr(C)]
    struct Blah {
      x : i32,
      p : *mut i64,
      y : u64,
      z : f32,
    }
    let code = r#"
      struct blah
        x : i32
        p : ptr(i64)
        y : u64
        z : f32
      end
      fun main(a : ptr(blah))
        a[0] = blah { 50 as i32, [40, 50, 60], 5390 as u64, 45640.5 as f32 }
      end
    "#;
    let b : Blah = i.run_with_pointer_return(code, "main").unwrap();
    assert_eq!(b.x, 50);
    assert_eq!(b.y, 5390);
    assert_eq!(b.z, 45640.5);
  }

  #[test]
  fn test_struct_abi() {
    // TODO test that structs are passed into C functions corrected
    panic!("test not implemented");
  }

  // TODO: this test isn't very good
  #[test]
  fn test_string() {
    let mut i = Interpreter::new();
    let code = r#"
      fun main(a : ptr(string))
        a[0] = "Hello world"
      end
    "#;
    let s : ScriptString = i.run_with_pointer_return(code, "main").unwrap();
    let expected = "Hello world";
    assert_eq!(s.as_str(), expected);
  }

  #[test]
  fn test_dll_function_linking() {
    // Seems to cause the symbols to be linked
    #[allow(unused_imports)]
    use dlltest::*;
    
    let a = "
      cfun function_from_dll(a : i64, b : i64) : i64
      function_from_dll(17, 7)
    ";
    let b = "
      cfun another_function_from_dll(a : i64, b : i64) : i64
      another_function_from_dll(17, 7)
    ";
    assert_result(a, Val::I64(24));
    assert_result(b, Val::I64(24));
  }

}

/*

Features to add:

  * non-native types (can fold strings and arrays into this?)
  * consider making new-lines significant in some cases (relating to semi-colons)

#[test]
fn test_first_class_function() {
  let code = "
    let a = [1, 2, 3, 4]
    fun foo(a, b) {
      a + b
    }
    fun fold(a, v, f) {
      let i = 0
      while i < len(a) {
        v = f(v, a[i])
        i = i + 1
      }
      v
    }
    fold(a, 0, foo)
  ";
  assert_result(code, Val::I64(10));
}

#[test]
fn test_for_loop() {
  let range_code = "
    let t = 0
    let r = range(0, 5)
    for x in range(0, 2) {
      for v in r {
        t = t + 1
      }
    }
    t
  ";
  assert_result(range_code, Val::I64(10));
}

#[test]
fn test_brace_syntax_quirks(){
  // This test demonstrates a problem with the struct initialisation syntax
  let code = "
    struct a { }
    let b = a()
  ";
  // TODO: fix this problem
  assert_result(code, Val::Void);
}

// TODO: unclear if multiple dispatch will be supported again
#[test]
fn test_dispatch(){
  let fundef_code = "
    fun add(a : float, b : float) {
      a + b
    }

    fun add(a : bool, b : bool) {
      a == b
    }
  ";
  let cases = vec![
    ("add(-3, 5)", Val::I64(2)),
    ("add(true, false)", Val::Bool(false)),
    ("add(false, false)", Val::Bool(true)),
  ];
  for (code, expected_result) in cases {
    let mut i = Interpreter::new();
    let def_result = i.run(fundef_code);
    assert!(def_result.is_ok(), "Error: {:?}", result_string(def_result));
    let expected = Ok(expected_result);
    let result = i.run(code);
    assert!(
      result == expected,
      "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
      code, result_string(expected), result_string(result));
  }
}

*/
