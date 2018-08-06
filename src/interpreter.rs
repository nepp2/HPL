
use parser;
use lexer;
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

fn interpret_instr(instr : &str, args : Vec<Expr>) -> Result<f32, String> {
  match (instr, args.as_slice()) {
    ("call", [Expr::Symbol(s), args..]) => {
      match (s.as_str(), args) {
        ("+", [a, b]) => Ok(interpret(a)? + interpret(b)?),
        _ => Ok(0.0),
      }
    }
    _ => Err(format!("not implemented")),
  }
}

pub fn interpret(ast : &Expr) -> Result<f32, String> {
  match ast {
    Expr::Expr{ symbol, args } => Err(format!("symbols not supported")),
    Expr::Symbol(_) => Err(format!("symbols not supported")),
    Expr::Literal(f) => Ok(*f),
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

