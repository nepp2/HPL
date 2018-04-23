
use lexer;
use lexer::Token;

#[derive(Debug)]
enum Expr {
  InfixOp(Box<Expr>, String, Box<Expr>),
  LiteralFloat(f32),
}

fn parse(tokens : Vec<Token>) -> Expr {

  panic!();
}

pub fn test_parse() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code);
  let ast = parse(tokens);
  println!("{:?}", ast);
}
