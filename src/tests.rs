
use interpreter_old;
use interpreter_old::Interpreter;
use value::*;

#[test]
fn test_maths() {
  let cases = vec![
    ("4 + 5", Value::from(9.0)),
    ("4 - 5", Value::from(-1.0)),
    ("4 * 5", Value::from(20.0)),
    ("20 > 5", Value::from(true)),
    ("20 < 5", Value::from(false)),
    ("5 <= 5", Value::from(true)),
    ("5 >= 5", Value::from(true)),
    ("5 == 5", Value::from(true)),
    ("true && false", Value::from(false)),
    ("true || false", Value::from(true)),
    ("-(4 - 5)", Value::from(1.0)),
  ];
  for (code, expected_result) in cases {
    let er = Ok(expected_result);
    let result = interpreter_old::interpret(code);
    assert!(
      result == er,
      "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
      code, er, result);
  }
}

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
    let mut i = Interpreter::new();
    assert!(i.interpret(fundef_code).is_ok());
    let er = Ok(expected_result);
    let result = i.interpret(code);
    assert!(
      result == er,
      "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
      code, er, result);
  }
}