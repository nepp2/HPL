
use interpreter_old;
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
    let result = interpreter_old::interpret_string(code);
    assert!(
      result == er,
      "error in code '{}'. Expected result '{:?}'. Actual result was '{:?}'",
      code, er, result);
  }
}