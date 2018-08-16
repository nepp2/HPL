
use parser;
use lexer;
use parser::Expr;
use std::collections::HashMap;
use std::rc::Rc;

enum Value {
  Float(f32),
  String(String)
}

struct Environment<'l> {
  map : HashMap<String, f32>,
  functions : &'l mut HashMap<String, FunctionDef>,
}

struct FunctionDef {
  args : Vec<String>,
  expr : Rc<Expr>,
}

fn interpret_function_call(function_name: &str, args: &[Expr], env : &mut Environment)
  -> Result<f32, String>
{
  let mut arg_values = vec!();
  for i in 0..args.len() {
    let v = interpret_with_env(&args[i], env)?;
    arg_values.push(v);
  }
  let (map, expr) = {
    let fun = match env.functions.get(function_name) {
      Some(fd) => fd,
      None => return Err(format!("Found no function called '{}'", function_name)),
    };
    let mut m = HashMap::new();
    for i in 0..arg_values.len() {
      m.insert(fun.args[i].to_string(), arg_values[i]);
    }
    (m, fun.expr.clone())
  };
  let mut new_env = Environment{ map, functions: env.functions };
  interpret_with_env(&expr, &mut new_env)
}

fn interpret_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment) -> Result<f32, String> {
  match (instr, args.as_slice()) {
    ("call", exprs) => {
      let symbol = match &exprs[0] {
        Expr::Symbol(s) => s,
        _ => return Err(format!("expected symbol")),
      };
      let params = &exprs[1..];
      match (symbol.as_str(), params) {
        ("+", [a, b]) => Ok(interpret_with_env(a, env)? + interpret_with_env(b, env)?),
        ("-", [a, b]) => Ok(interpret_with_env(a, env)? - interpret_with_env(b, env)?),
        ("*", [a, b]) => Ok(interpret_with_env(a, env)? * interpret_with_env(b, env)?),
        ("/", [a, b]) => Ok(interpret_with_env(a, env)? / interpret_with_env(b, env)?),
        ("-", [v]) => Ok(-interpret_with_env(v, env)?),
        _ => interpret_function_call(symbol.as_str(), params, env),
      }
    }
    ("block", exprs) => {
      let expr_count = exprs.len();
      if expr_count > 1 {
        for i in 0..expr_count {
          let _ = interpret_with_env(&exprs[i], env)?;
        }
      }
      interpret_with_env(&exprs[expr_count-1], env)
    }
    ("let", exprs) => {
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      let v = interpret_with_env(&exprs[1], env)?;
      env.map.insert(name.to_string(), v);
      //println!("Assign value '{}' to variable '{}'", v, name);
      Ok(0.0)
    }
    ("fun", exprs) => {
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      let args_exprs = match &exprs[1] { Expr::Expr{ args, .. } => args, _ => { return Err(format!("expected an expression")); }};
      let function_body = Rc::new(exprs[2].clone());
      let mut args = vec!();
      for e in args_exprs {
        if let Expr::Symbol(s) = e {
          args.push(s.to_string());
        }
        else {
          return Err(format!("expected a symbol"));
        }
      }
      env.functions.insert(name.to_string(), FunctionDef { args, expr: function_body });
      Ok(0.0)
    }
    _ => Err(format!("instruction '{}' is not supported by the interpreter.", instr)),
  }
}

fn interpret_with_env(ast : &Expr, env : &mut Environment) -> Result<f32, String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      interpret_instr(symbol, args, env)
    }
    Expr::Symbol(s) => {
      let v = env.map.get(s);
      match v {
        Some(f) => Ok(*f),
        None => Err(format!("symbols '{}' was not defined", s)),
      }
    }
    Expr::LiteralFloat(f) => Ok(*f)
  }
}

pub fn interpret(ast : &Expr) -> Result<f32, String> {
  let mut functions = HashMap::new();
  let mut env = Environment { map: HashMap::new(), functions: &mut functions };
  interpret_with_env(ast, &mut env)
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let tokens = lexer::lex(code).unwrap();
  let ast = parser::parse(tokens).unwrap();
  let result = interpret(&ast);
  println!("{:?}", result);
}

