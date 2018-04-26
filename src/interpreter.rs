
use lexer;
use parser;

use parser::Expr;

fn infix(a : Expr, op : &str, b : Expr) -> f32 {
  let v1 = interpret(a);
  let v2 = interpret(b);
  match op {
    "+" => v1 + v2,
    "-" => v1 - v2,
    "*" => v1 * v2,
    "/" => v1 / v2,
    _ => panic!("unsupported operator '{}'", op),
  }
}

fn prefix(op : &str, a : Expr) -> f32 {
  let v = interpret(a);
  match op {
    "-" => -v,
    _ => panic!("unsupported operator '{}'", op),
  }
}

pub fn interpret(ast : Expr) -> f32 {
  match ast {
    Expr::FunctionCall{ func, args } => panic!("function calls not supported"),
    Expr::InfixOp(a, op, b) => infix(*a, &op, *b),
    Expr::PrefixOp(op, a) => prefix(&op, *a),
    Expr::LiteralFloat(f) => f,
  }
}

pub fn test_interpret() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code);
  let ast = parser::parse(tokens);
  let result = interpret(ast);
  println!("{:?}", result);
}

