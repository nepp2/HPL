
use crate::interpreter;
use crate::interpreter::Interpreter;
use crate::value::*;

#[test]
fn test_basics() {
  let cases = vec![
    ("", Value::Unit),
    ("()", Value::Unit),
    ("4 + 5", Value::from(9.0)),
    ("4 - 5", Value::from(-1.0)),
    ("4 * 5", Value::from(20.0)),
    ("20 > 5", Value::from(true)),
    ("20 < 5", Value::from(false)),
    ("5 <= 5", Value::from(true)),
    ("5 >= 5", Value::from(true)),
    ("5 == 5", Value::from(true)),
    ("-(4 - 5)", Value::from(1.0)),
    ("4 + {let a = 5; let b = 4; a}", Value::from(9.0)),
    ("if true { 3 } else { 4 }", Value::from(3.0)),
    ("if false { 3 } else { 4 }", Value::from(4.0)),
    ("let a = 5; a", Value::from(5.0)),
    (r#""Hello world""#, Value::from("Hello world")),
  ];
  for (code, expected_result) in cases {
    assert_result(code, expected_result);
  }
}

#[test]
fn test_and_or() {
  assert_result("true && false", Value::from(false));
  assert_result("true || false", Value::from(true));
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
  assert_result(and, Value::from(0.0));
  assert_result(or, Value::from(0.0));
}

fn assert_result(code : &str, expected_result : Value){
  let expected = Ok(expected_result);
  let result = interpreter::interpret(code);
  assert!(
    result == expected,
    "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
    code, expected, result);
}

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
    ("add(-3, 5)", Value::from(2.0)),
    ("add(true, false)", Value::from(false)),
    ("add(false, false)", Value::from(true)),
  ];
  for (code, expected_result) in cases {
    let mut i = Interpreter::simple();
    let def_result = i.interpret(fundef_code);
    assert!(def_result.is_ok(), "Error: {:?}", def_result);
    let expected = Ok(expected_result);
    let result = i.interpret(code);
    assert!(
      result == expected,
      "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
      code, expected, result);
  }
}

#[test]
fn test_scope(){
  let code = "
    let a = 4
    let b = 0
    if true {
      let a = 5
      b = b + a
    }
    b = b + a
    b
  ";
  assert_result(code, Value::from(9.0));
}

#[test]
fn test_struct() {
  let code = "
    struct vec2 {
      x : float
      y : float
    }
    fun add(a : vec2, b : vec2) {
      vec2(x: a.x + b.x, y: a.y + b.y)
    }
    let a = vec2(x: 10, y: 1)
    let b = vec2(x: 2, y: 20)
    let c = add(a, b)
    c.y
  ";
  assert_result(code, Value::from(21.0));
}

#[test]
fn test_arrays() {
  let code = "
    let a = [0, [1, 2, 3], 6]
    a[1][1] = 50
    a[1][1] + a[2]
  ";
  assert_result(code, Value::from(56.0));
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
  assert_result(a, Value::from(5.0));
  let b = "
    let x = 1
    while x < 10 {
      x = x + 6;
    }
    x
  ";
  assert_result(b, Value::from(13.0));
}

#[test]
fn test_first_class_function() {
  let code = "
    let a = [1, 2, 3, 4]
    fun add(a, b) {
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
    fold(a, 0, add)
  ";
  assert_result(code, Value::from(10.0));
}

#[test]
fn test_for_loop() {
  let array_code = "
    let t = 0
    for v in [1, 2, 3, 4] {
      t = t + v
    }
    t
  ";
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
  assert_result(array_code, Value::from(10.0));
  assert_result(range_code, Value::from(10.0));
}

#[test]
fn test_brace_syntax_quirks(){
  // This test demonstrates a problem with the struct initialisation syntax
  let code = "
    struct a { }
    let b = a()
  ";
  // TODO: fix this problem
  // assert_result(code, Value::Unit);
}

#[test]
fn test_return(){
  let code = "
    fun foo(v) {
      if v {
        return 10
      }
      20
    }
    foo(true) + foo(false)
  ";
  assert_result(code, Value::from(30.0));
}

/*

Features to add:

  * non-native types (can fold strings and arrays into this?)
  * explicit returns (not sure what to do about semi-colons)
  * consider making new-lines significant in some cases (relating to semi-colons)

*/
