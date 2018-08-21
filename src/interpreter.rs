
use parser;
use lexer;
use parser::Expr;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;

/* TODO
#[derive(Debug)]
struct Array {
  step : u32,
  data : Vec<u32>
}
*/

type Array = Rc<RefCell<Vec<Value>>>;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
  Float(f32),
  Array(Array),
  Bool(bool),
  Unit,
}

/*

struct ScopeStack<T> {
  map : HashMap<String, T>,
  parent : Option<Rc<ScopeStack<T>>>,
}

impl<T> ScopeStack<T> {
  fn get(&self, s : &str) -> Result<&T, String> {
    match self.map.get(s) {
      Some(t) => Ok(t),
      None => Err(format!("")),
    }
  }
}

struct Environment {
  map : ScopeStack<Value>,
  functions : ScopeStack<FunctionDef>,
}

*/

struct Environment<'l> {
  map : HashMap<String, Value>,
  functions : &'l mut HashMap<String, FunctionDef>,
}

struct FunctionDef {
  args : Vec<String>,
  expr : Rc<Expr>,
}

fn interpret_function_call(function_name: &str, args: &[Expr], env : &mut Environment)
  -> Result<Value, String>
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
    for (v, n) in arg_values.into_iter().zip(&fun.args) {
      m.insert(n.to_string(), v);
    }
    (m, fun.expr.clone())
  };
  let mut new_env = Environment{ map, functions: env.functions };
  interpret_with_env(&expr, &mut new_env)
}

fn interpret_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment) -> Result<Value, String> {

  fn to_f(v : &Expr, env : &mut Environment) -> Result<f32, String> {
    match interpret_with_env(v, env)? {
      Value::Float(f) => Ok(f),
      x => Err(format!("Expected float, found {:?}.", x))
    }
  }
  fn to_b(v : &Expr, env : &mut Environment) -> Result<bool, String> {
    match interpret_with_env(v, env)? {
      Value::Bool(b) => Ok(b),
      x => Err(format!("Expected boolean, found {:?}.", x))
    }
  }
  fn to_array(v : &Expr, env : &mut Environment) -> Result<Array, String> {
    match interpret_with_env(v, env)? {
      Value::Array(a) => Ok(a),
      x => Err(format!("Expected array, found {:?}.", x))
    }
  }
  fn f_to_val(f : f32) -> Result<Value, String> {
    Ok(Value::Float(f))
  }
  fn b_to_val(b : bool) -> Result<Value, String> {
    Ok(Value::Bool(b))
  }

  match (instr, args.as_slice()) {
    ("call", exprs) => {
      let symbol = match &exprs[0] {
        Expr::Symbol(s) => s,
        _ => return Err(format!("expected symbol")),
      };
      let params = &exprs[1..];
      match (symbol.as_str(), params) {
        ("+", [a, b]) => f_to_val(to_f(a, env)? + to_f(b, env)?),
        ("-", [a, b]) => f_to_val(to_f(a, env)? - to_f(b, env)?),
        ("*", [a, b]) => f_to_val(to_f(a, env)? * to_f(b, env)?),
        ("/", [a, b]) => f_to_val(to_f(a, env)? / to_f(b, env)?),
        (">", [a, b]) => b_to_val(to_f(a, env)? > to_f(b, env)?),
        ("<", [a, b]) => b_to_val(to_f(a, env)? < to_f(b, env)?),
        ("==", [a, b]) => b_to_val(interpret_with_env(a, env)? == interpret_with_env(b, env)?),
        ("&&", [a, b]) => b_to_val(to_b(a, env)? && to_b(b, env)?),
        ("||", [a, b]) => b_to_val(to_b(a, env)? || to_b(b, env)?),
        ("-", [v]) => f_to_val(-to_f(v, env)?),
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
      Ok(Value::Unit)
    }
    ("if", exprs) => {
      if exprs.len() < 2 {
        return Err(format!("malformed if expression"));
      }
      let condition = to_b(&exprs[0], env)?;
      if condition {
        interpret_with_env(&exprs[1], env)
      }
      else if exprs.len() > 2 {
        interpret_with_env(&exprs[2], env)
      }
      else {
        Ok(Value::Unit)
      }
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
      Ok(Value::Unit)
    }
    ("literal_array", exprs) => {
      let mut array_contents = Rc::new(RefCell::new(vec!()));
      for e in exprs {
        let v = interpret_with_env(e, env)?;
        array_contents.borrow_mut().push(v);
      }
      Ok(Value::Array(array_contents))
    }
    ("index", exprs) => {
      if let [array_expr, index_expr] = exprs {
        let array_rc = to_array(array_expr, env)?;
        let array = array_rc.borrow();
        let f = to_f(index_expr, env)?;
        let i = f as usize;
        if f >= 0.0 && i < array.len() {
          let v = array[i].clone();
          Ok(v)
        }
        else {
          Err(format!("Index out of bounds error. Array of {} elements given index {}.", exprs.len(), f))
        }
      }
      else {
        Err(format!("index instruction expected 2 arguments. Found {}.", exprs.len()))
      }
    }
    _ => Err(format!("instruction '{}' is not supported by the interpreter.", instr)),
  }
}

fn interpret_with_env(ast : &Expr, env : &mut Environment) -> Result<Value, String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      interpret_instr(symbol, args, env)
    }
    Expr::Symbol(s) => {
      match env.map.get(s) {
        Some(v) => Ok(v.clone()),
        None => Err(format!("symbols '{}' was not defined", s)),
      }
    }
    Expr::LiteralFloat(f) => Ok(Value::Float(*f)),
    Expr::LiteralBool(b) => Ok(Value::Bool(*b)),
  }
}

pub fn interpret(ast : &Expr) -> Result<Value, String> {
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

