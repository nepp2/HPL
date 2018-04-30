
use parser::Expr;

fn infix(a : Expr, op : &str, b : Expr) -> Result<f32, String> {
  let v1 = interpret(a)?;
  let v2 = interpret(b)?;
  let r =
    match op {
      "+" => v1 + v2,
      "-" => v1 - v2,
      "*" => v1 * v2,
      "/" => v1 / v2,
      _ => return Err(format!("unsupported operator '{}'", op)),
    };
  Ok(r)
}

fn prefix(op : &str, a : Expr) -> Result<f32, String> {
  let v = interpret(a)?;
  match op {
    "-" => Ok(-v),
    _ => Err(format!("unsupported operator '{}'", op)),
  }
}

pub fn interpret(ast : Expr) -> Result<f32, String> {
  match ast {
    Expr::FunctionCall{ func: _, args: _ } => Err(format!("function calls not supported")),
    Expr::InfixOp(a, op, b) => infix(*a, &op, *b),
    Expr::PrefixOp(op, a) => prefix(&op, *a),
    Expr::LiteralFloat(f) => Ok(f),
  }
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parser::parse(tokens).unwrap();
  let result = interpret(ast);
  println!("{:?}", result);
}

