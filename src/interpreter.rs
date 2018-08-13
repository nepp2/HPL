
use parser;
use lexer;
use parser::Expr;

fn interpret_instr(instr : &str, args : &Vec<Expr>) -> Result<f32, String> {
  match (instr, args.as_slice()) {
    ("call", [Expr::Symbol(s), a, b]) => {
      let av = interpret(a)?;
      let bv = interpret(b)?;
      match s.as_str() {
        "+" => Ok(av + bv),
        "-" => Ok(av - bv),
        "*" => Ok(av * bv),
        "/" => Ok(av / bv),
        _ => Err(format!("unsupported operation '{}'", s)),
      }
    }
    ("call", [Expr::Symbol(s), a]) => {
      let v = interpret(a)?;
      match s.as_str() {
        "-" => Ok(-v),
        _ => Err(format!("unsupported operation '{}'", s)),
      }
    }
    ("block", exprs) => {
      let expr_count = exprs.len();
      if expr_count > 1 {
        for i in 0..expr_count {
          let _ = interpret(&exprs[i])?;
        }
      }
      interpret(&exprs[expr_count-1])
    }
    _ => Err(format!("not implemented")),
  }
}

pub fn interpret(ast : &Expr) -> Result<f32, String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      interpret_instr(symbol, args)
    }
    Expr::Symbol(_) => Err(format!("symbols not supported")),
    Expr::Literal(f) => Ok(*f),
  }
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parser::parse(tokens).unwrap();
  let result = interpret(&ast);
  println!("{:?}", result);
}

