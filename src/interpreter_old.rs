
use parser;
use lexer;
use value::*;
use error::{Error, TextLocation, error, error_raw, error_no_loc};
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;
use std::cell::RefCell;

/// Insert the value in the last hashmap in the vector, which represents the local scope.
fn scoped_insert<T>(stack : &mut Vec<HashMap<RefStr, T>>, s : RefStr, t : T) {
  let i = stack.len()-1;
  stack[i].insert(s, t);
}

/// Retrieve the value closest to the end of the vector of hashmaps (the most local scope)
/// in the environment
fn scoped_get<'l, T>(stack : &'l mut Vec<HashMap<RefStr, T>>, s : &str) -> Option<&'l mut T> {
  for map in stack.iter_mut().rev() {
    if map.contains_key(s) {
      return Some(map.get_mut(s).unwrap());
    }
  }
  return None;
}

#[derive(PartialEq)]
enum BreakState {
  Breaking,
  NotBreaking,
}

#[derive(Debug)]
pub struct FunctionInfo {
  pub name : RefStr,
  pub arguments : Vec<RefStr>,
}

struct FunctionDef<'l> {
  info : FunctionInfo,
  handle : FunctionHandle<'l>,
}

enum FunctionHandle<'l> {
  Ast(&'l Expr),
  Intrinsic(fn(&[Value]) -> Result<Value, Error>),
}

struct Environment<'l> {
  values : &'l mut Vec<HashMap<RefStr, Value>>,
  functions : &'l mut Vec<HashMap<RefStr, FunctionDef>>,
  structs : &'l mut HashMap<RefStr, Rc<StructDef>>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_depth : i32,

  /// indicates whether the program is currently breaking out of a loop
  break_state : BreakState,
}

impl <'l> Environment<'l> {
  fn new(
    values : &'l mut Vec<HashMap<RefStr, Value>>,
    functions : &'l mut Vec<HashMap<RefStr, FunctionDef>>,
    structs : &'l mut HashMap<RefStr, Rc<StructDef>>,
  ) -> Environment<'l> {
    Environment{
      values, functions, structs,
      loop_depth: 0,
      break_state: BreakState::NotBreaking
    }
  }
}

fn interpret_function_call(function_name_expr: &Expr, args: &[Expr], env : &mut Environment)
  -> Result<Value, Error>
{
  let function_name = function_name_expr.symbol_unwrap()?;
  let mut arg_values = vec!();
  for i in 0..args.len() {
    let v = interpret_with_env(&args[i], env)?;
    arg_values.push(v);
  }
  let mut args = HashMap::new();
  let expr = {
    let fun = match scoped_get(&mut env.functions, function_name) {
      Some(fd) => fd,
      None => return error(function_name_expr, format!("Found no function called '{}'", function_name)),
    };
    for (v, n) in arg_values.into_iter().zip(&fun.args) {
      args.insert(n.clone(), v);
    }
    fun.expr.clone()
  };
  let mut vs = vec!(args);
  let mut new_env = Environment::new(&mut vs, env.functions, env.structs);
  interpret_with_env(&expr, &mut new_env)
}

fn to_f(v : &Expr, env : &mut Environment) -> Result<f32, Error> {
  match interpret_with_env(v, env)? {
    Value::Float(f) => Ok(f),
    x => error(v, format!("Expected float, found {:?}.", x))
  }
}
fn to_b(v : &Expr, env : &mut Environment) -> Result<bool, Error> {
  match interpret_with_env(v, env)? {
    Value::Bool(b) => Ok(b),
    x => error(v, format!("Expected boolean, found {:?}.", x))
  }
}
fn to_array(v : &Expr, env : &mut Environment) -> Result<Array, Error> {
  match interpret_with_env(v, env)? {
    Value::Array(a) => Ok(a),
    x => error(v, format!("Expected array, found {:?}.", x))
  }
}
fn to_struct(v : &Expr, env : &mut Environment) -> Result<StructVal, Error> {
  match interpret_with_env(v, env)? {
    Value::Struct(s) => Ok(s),
    x => error(v, format!("Expected struct, found {:?}.", x))
  }
}
fn to_function(v : &Expr, env : &mut Environment) -> Result<(FunctionType, usize), Error> {
  match interpret_with_env(v, env)? {
    Value::Function(f, s) => Ok((f, s)),
    x => error(v, format!("Expected function, found {:?}.", x))
  }
}
/*
fn to_f(v : Value) -> Result<f32, Error> {
  match v {
    Value::Float(f) => Ok(f),
    x => Err(error_no_loc(format!("Expected float, found {:?}.", x)))
  }
}
fn to_b(v : Value) -> Result<bool, Error> {
  match v {
    Value::Bool(b) => Ok(b),
    x => Err(error_no_loc(format!("Expected boolean, found {:?}.", x)))
  }
}
fn to_function(v : Value) -> Result<(FunctionType, usize), Error> {
  match v {
    Value::Function(t, h) => Ok((t, h)),
    x => Err(error_no_loc(format!("Expected function, found {:?}.", x)))
  }
}
fn to_array(v : Value) -> Result<Array, Error> {
  match v {
    Value::Array(a) => Ok(a),
    x => Err(error_no_loc(format!("Expected array, found {:?}.", x)))
  }
}
fn to_struct(v : &Value) -> Result<&StructVal, Error> {
  match v {
    Value::Struct(s) => Ok(s),
    x => Err(error_no_loc(format!("Expected struct, found {:?}.", x)))
  }
}
*/

fn array_index(array : &Vec<Value>, index : f32) -> Result<usize, Error> {
  let i = index as usize;
  if index >= 0.0 && i < array.len() {
    Ok(i)
  }
  else {
    Err(error_no_loc(format!("Index out of bounds error. Array of {} elements given index {}.", array.len(), index)))
  }
}

fn struct_field_index(def : &StructDef, field_expr : &Expr) -> Result<usize, Error> {
  let field_name : &str = field_expr.symbol_unwrap()?;
  def.fields.iter().position(|s| s.as_ref() == field_name)
  .ok_or_else(||error_raw(field_expr, format!("field {} does not exist on struct {:?}.", field_name, def)))
}
fn f_to_val(f : f32) -> Result<Value, String> {
  Ok(Value::Float(f))
}
fn b_to_val(b : bool) -> Result<Value, String> {
  Ok(Value::Bool(b))
}

fn interpret_instr(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  let instr = expr.tree_symbol_unwrap()?.as_ref();
  let children = expr.children.as_slice();
  match (instr, children) {
    ("call", exprs) => {
      let function_name_expr = &exprs[0];
      let params = &exprs[1..];
      interpret_function_call(function_name_expr, params, env)
      /*
      match (symbol.as_ref(), params) {
        ("+", [a, b]) => f_to_val(to_f(a, env)? + to_f(b, env)?),
        ("-", [a, b]) => f_to_val(to_f(a, env)? - to_f(b, env)?),
        ("*", [a, b]) => f_to_val(to_f(a, env)? * to_f(b, env)?),
        ("/", [a, b]) => f_to_val(to_f(a, env)? / to_f(b, env)?),
        (">", [a, b]) => b_to_val(to_f(a, env)? > to_f(b, env)?),
        ("<", [a, b]) => b_to_val(to_f(a, env)? < to_f(b, env)?),
        ("<=", [a, b]) => b_to_val(to_f(a, env)? <= to_f(b, env)?),
        (">=", [a, b]) => b_to_val(to_f(a, env)? >= to_f(b, env)?),
        ("==", [a, b]) => b_to_val(interpret_with_env(a, env)? == interpret_with_env(b, env)?),
        ("&&", [a, b]) => b_to_val(to_b(a, env)? && to_b(b, env)?),
        ("||", [a, b]) => b_to_val(to_b(a, env)? || to_b(b, env)?),
        ("-", [v]) => f_to_val(-to_f(v, env)?),
        _ => interpret_function_call(symbol, params, env),
      }
      */
    }
    ("block", exprs) => {
      env.values.push(HashMap::new());
      let last_val = {
        let expr_count = exprs.len();
        if expr_count > 1 {
          for i in 0..expr_count {
            let _ = interpret_with_env(&exprs[i], env)?;
          }
        }
        interpret_with_env(&exprs[expr_count-1], env)
      };
      env.values.pop();
      last_val
    }
    ("let", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let v = interpret_with_env(&exprs[1], env)?;
      scoped_insert(&mut env.values, name.clone(), v);
      Ok(Value::Unit)
    }
    ("=", [_, assign_expr, value_expr]) => {
      match &assign_expr.tag {
        ExprTag::Symbol(var_symbol) => {
          let v = interpret_with_env(&value_expr, env)?;
          match scoped_get(&mut env.values, var_symbol) {
            Some(variable) => {
              *variable = v;
              return Ok(Value::Unit)
            }
            None => return error(assign_expr, format!("symbol '{}' was not defined", var_symbol)),
          }
        }
        ExprTag::Tree(symbol) => {
          match (symbol.as_ref(), assign_expr.children.as_slice()) {
            ("index", [array_expr, index_expr]) => {
              let v = interpret_with_env(&value_expr, env)?;
              let array_rc = to_array(array_expr, env)?;
              let mut array = array_rc.borrow_mut();
              let f = to_f(index_expr, env)?;
              let i = array_index(&array, f)?;
              array[i] = v;
              return Ok(Value::Unit)
            }
            (".", [struct_expr, field_expr]) => {
              let v = interpret_with_env(&value_expr, env)?;
              let structure = to_struct(struct_expr, env)?;
              let index = struct_field_index(&structure.borrow().def, field_expr)?;
              structure.borrow_mut().fields[index] = v;
              return Ok(Value::Unit)
            }
            _ => return error(assign_expr, format!("can't assign to {:?}", assign_expr)),
          }
        }
        _ => (),
      }
      error(assign_expr, format!("can't assign to {:?}", assign_expr))
    }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return error(expr, format!("malformed if expression"));
      }
      let condition = to_b(&exprs[0], env)?;
      if condition {
        interpret_with_env(&exprs[1], env)
      }
      else if arg_count == 3 {
        interpret_with_env(&exprs[2], env)
      }
      else {
        Ok(Value::Unit)
      }
    }
    ("struct_define", exprs) => {
      if exprs.len() < 1 {
        return error(expr, format!("malformed struct definition"));
      }
      let name_expr = &exprs[0];
      let name = name_expr.symbol_to_refstr()?;
      if env.structs.contains_key(&name) {
        return error(name_expr, format!("A struct called {} has already been defined.", name));
      }
      // TODO: check for duplicates?
      let struct_def =
        exprs[1..].iter().map(|e| e.symbol_to_refstr())
        .collect::<Result<Vec<RefStr>, Error>>()
        .map(|fields| Rc::new(StructDef { name: name.clone(), fields}))?;
      env.structs.insert(name, struct_def);
      Ok(Value::Unit)
    }
    ("struct_instantiate", exprs) => {
      if exprs.len() < 1 || exprs.len() % 2 == 0 {
        return error(expr, format!("malformed struct instantiation {:?}", expr));
      }
      let name_expr = &exprs[0];
      let name = name_expr.symbol_to_refstr()?;
      let def =
        env.structs.get(name.as_ref())
        .ok_or_else(|| error_raw(name_expr, format!("struct {} does not exist", name)))?.clone();
      let mut fields = vec![Value::Unit ; def.fields.len()];
      {
        let mut field_index_map =
          def.fields.iter().enumerate()
          .map(|(i, s)| (s.as_ref(), i)).collect::<HashMap<&str, usize>>();
        for i in (1..exprs.len()).step_by(2) {
          let field_name_expr = &exprs[i];
          let field_name = field_name_expr.symbol_to_refstr()?;
          let field_value = interpret_with_env(&exprs[i+1], env)?;
          let index = field_index_map.remove(field_name.as_ref())
            .ok_or_else(|| error_raw(field_name_expr, format!("field {} does not exist", field_name)))?;
          fields[index] = field_value;
        }
        if field_index_map.len() > 0 {
          return error(expr, format!("Some fields not initialised"));
        }
      }
      let s = Rc::new(RefCell::new(Struct { def, fields }));
      Ok(Value::Struct(s))
    }
    (".", [expr, name_expr]) => {
      let s = to_struct(expr, env)?;
      let index = struct_field_index(&s.borrow().def, name_expr)?;
      let v = s.borrow().fields[index].clone();
      Ok(v)
    }
    ("while", exprs) => {
      if exprs.len() != 2 {
        return error(expr, format!("malformed while block"));
      }
      env.loop_depth += 1;
      while env.break_state != BreakState::Breaking && to_b(&exprs[0], env)? {
        interpret_with_env(&exprs[1], env)?;
      }
      env.loop_depth -= 1;
      env.break_state = BreakState::NotBreaking;
      Ok(Value::Unit)
    }
    ("fun", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let args_exprs = exprs[1].children.as_slice();
      let function_body = Rc::new(exprs[2].clone());
      let mut args = vec!();
      for e in args_exprs {
        if let Expr::Symbol(s) = e {
          args.push(s.clone());
        }
        else {
          return Err(format!("expected a symbol"));
        }
      }
      scoped_insert(&mut env.functions, name.clone(), FunctionDef { args, expr: function_body });
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
        let i = array_index(&array, f)?;
        Ok(array[i].clone())
      }
      else {
        Err(format!("index instruction expected 2 arguments. Found {}.", exprs.len()))
      }
    }
    _ => Err(format!("instruction '{}' with args {:?} is not supported by the interpreter.", instr, args)),
  }
}

fn interpret_with_env(ast : &Expr, env : &mut Environment) -> Result<Value, Error> {
  if env.break_state == BreakState::Breaking {
    // this basically skips all evaluations until we backtrack to the loop,
    // which will spot the break state and stop iterating.
    return Ok(Value::Unit);
  }
  match ast {
    Expr::Expr{ symbol, args } => {
      interpret_instr(symbol, args, env)
    }
    Expr::Symbol(s) => {
      if s.as_ref() == "break" {
        if env.loop_depth > 0 {
          env.break_state = BreakState::Breaking;
          Ok(Value::Unit)
        }
        else {
          Err(format!("can't break outside a loop"))
        }
      }
      else {
        match scoped_get(&mut env.values, s) {
          Some(v) => Ok(v.clone()),
          None => Err(format!("symbol '{}' was not defined", s)),
        }
      }
    }
    Expr::LiteralFloat(f) => Ok(Value::Float(*f)),
    Expr::LiteralBool(b) => Ok(Value::Bool(*b)),
  }
}

pub fn interpret(ast : &Expr) -> Result<Value, String> {
  let mut vs = vec!(HashMap::new());
  let mut fs = vec!(HashMap::new());
  let mut structs = HashMap::new();
  let mut env = Environment::new(&mut vs, &mut fs, &mut structs);
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

