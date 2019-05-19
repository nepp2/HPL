
use crate::error::Error;
use crate::llvm::Interpreter;
use crate::typecheck::Val;


#[test]
fn test_basics() {
  let cases = vec![
    ("", Val::Void),
    ("()", Val::Void),
    ("4 + 5", Val::I64(9)),
    ("4. + 5.5", Val::Float(9.5)),
    ("4 - 5", Val::I64(-1)),
    ("4 * 5", Val::I64(20)),
    ("20 > 5", Val::Bool(true)),
    ("20 < 5", Val::Bool(false)),
    ("5 <= 5", Val::Bool(true)),
    ("5 >= 5", Val::Bool(true)),
    ("5 == 5", Val::Bool(true)),
    ("-(4 - 5)", Val::I64(1)),
    ("4 + {let a = 5; let b = 4; a}", Val::I64(9)),
    ("if true { 3 } else { 4 }", Val::I64(3)),
    ("if false { 3 } else { 4 }", Val::I64(4)),
    ("let a = 5; a", Val::I64(5)),
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
    false && {a = 1; true}
    a
  ";
  let or = "
    let a = 0
    true || {a = 1; true}
    a
  ";
  assert_result(and, Val::I64(0));
  assert_result(or, Val::I64(0));
}

fn result_string(r : Result<Val, Error>) -> String {
  match r {
    Ok(v) => format!("{:?}", v),
    Err(e) => format!("{}", e),
  }
}

fn assert_result_with_interpreter(code : &str, expected_result : Val, i : &mut Interpreter){
  let expected = Ok(expected_result);
  let result = i.run(code);
  assert!(
    result == expected,
    "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
    code, result_string(expected), result_string(result));
}

fn assert_result(code : &str, expected_result : Val){
  let mut i = Interpreter::new();
  assert_result_with_interpreter(code, expected_result, &mut i)
}

// TODO: multiple dispatch currently not supported
//#[test]
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

#[test]
fn test_scope(){
  let code = "
    let a = 4
    let b = if true {
      let a = 5
      a
    }
    else {
      10
    }
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
    struct point {
      x : i64
      y : i64
    }
    let a = point(x: 5, y: 50)
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
    struct point {
      x : i64
      y : i64
    }
    fun foo(a : point, b : point) {
      point(x: a.x + b.x, y: a.y + b.y)
    }
    let a = point(x: 10, y: 1)
    let b = point(x: 2, y: 20)
    let c = foo(a, b)
    c.y
  ";
  assert_result(code, Val::I64(21));
}

#[test]
fn test_return(){
  let code = "
    fun foo(v : bool) {
      if v {
        return 10
      }
      20
    }
    foo(true) + foo(false)
  ";
  assert_result(code, Val::I64(30));
}

#[test]
fn test_while() {
  let a = "
    let x = 10
    while true {
      x = x - 1;
      if x <= 5 {
        break;
      }
    }
    x
  ";
  assert_result(a, Val::I64(5));
  let b = "
    let x = 1
    while x < 10 {
      x = x + 6;
    }
    x
  ";
  assert_result(b, Val::I64(13));
}

/*
fn test_global() {
  let mut i = Interpreter::new();
  let a = "let foo = 5";
  let b = "foo";
  assert_result_with_interpreter(&mut i, a, Val::Void);
  assert_result_with_interpreter(&mut i, b, Val::I64(5));
}


Features to add:

  * non-native types (can fold strings and arrays into this?)
  * consider making new-lines significant in some cases (relating to semi-colons)

#[test]
fn test_arrays() {
  let code = "
    let a = [0, [1, 2, 3], 6]
    a[1][1] = 50
    a[1][1] + a[2]
  ";
  assert_result(code, Val::I64(56));
}

#[test]
fn test_string() {
  let mut i = Interpreter::new();
  let code = r#""Hello world""#;
  // TODO let expected = Val::from(i.sym.get("Hello world"));
  let expected = Val::Void;
  assert_result_with_interpreter(code, expected, &mut i);
}

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

*/
