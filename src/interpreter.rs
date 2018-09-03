
use parser;
use lexer;
use lexer::{RefStr, AsStr};
use parser::Expr;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug, PartialEq)]
pub struct Struct {
  name : RefStr,
  fields : HashMap<RefStr, Value>,
}

pub type StructVal = Rc<RefCell<Struct>>;

pub type Array = Rc<RefCell<Vec<Value>>>;

/// Represents a value in the interpreted language.
/// Currently uses 16 bytes. I think this is because there are 8 byte
/// RC pointers in the union, and the discriminating value is being
/// padded to word size (also 8 bytes). Could probably be optimised
/// down to 8 bytes total, with some ugly pointer hacks.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
  Float(f32),
  Array(Array),
  Bool(bool),
  Struct(StructVal),
  Unit,
}

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

struct FunctionDef {
  args : Vec<RefStr>,
  expr : Rc<Expr>,
}

type StructDef = HashSet<RefStr>;

struct Environment<'l> {
  values : &'l mut Vec<HashMap<RefStr, Value>>,
  functions : &'l mut Vec<HashMap<RefStr, FunctionDef>>,
  structs : &'l mut HashMap<RefStr, StructDef>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_depth : i32,

  /// indicates whether the program is currently breaking out of a loop
  break_state : BreakState,
}

impl <'l> Environment<'l> {
  fn new(
    values : &'l mut Vec<HashMap<RefStr, Value>>,
    functions : &'l mut Vec<HashMap<RefStr, FunctionDef>>,
    structs : &'l mut HashMap<RefStr, StructDef>,
  ) -> Environment<'l> {
    Environment{
      values, functions, structs,
      loop_depth: 0,
      break_state: BreakState::NotBreaking
    }
  }
}

fn interpret_function_call(function_name: &str, args: &[Expr], env : &mut Environment)
  -> Result<Value, String>
{
  let mut arg_values = vec!();
  for i in 0..args.len() {
    let v = interpret_with_env(&args[i], env)?;
    arg_values.push(v);
  }
  let mut args = HashMap::new();
  let expr = {
    let fun = match scoped_get(&mut env.functions, function_name) {
      Some(fd) => fd,
      None => return Err(format!("Found no function called '{}'", function_name)),
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
  fn to_struct(v : &Expr, env : &mut Environment) -> Result<StructVal, String> {
    match interpret_with_env(v, env)? {
      Value::Struct(s) => Ok(s),
      x => Err(format!("Expected struct, found {:?}.", x))
    }
  }
  fn f_to_val(f : f32) -> Result<Value, String> {
    Ok(Value::Float(f))
  }
  fn b_to_val(b : bool) -> Result<Value, String> {
    Ok(Value::Bool(b))
  }
  fn symbol_unwrap(e : &Expr) -> Result<&RefStr, String> {
    if let Expr::Symbol(s) = e {
      Ok(s)
    }
    else {
      Err(format!("expected a symbol, found {:?}", e))
    }
  }
  fn symbol_to_refstr(e : &Expr) -> Result<RefStr, String> {
    symbol_unwrap(e).map(|s| s.clone())
  }

  fn array_index(array : &Vec<Value>, index : f32) -> Result<usize, String> {
    let i = index as usize;
    if index >= 0.0 && i < array.len() {
      Ok(i)
    }
    else {
      Err(format!("Index out of bounds error. Array of {} elements given index {}.", array.len(), index))
    }
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
        ("<=", [a, b]) => b_to_val(to_f(a, env)? <= to_f(b, env)?),
        (">=", [a, b]) => b_to_val(to_f(a, env)? >= to_f(b, env)?),
        ("==", [a, b]) => b_to_val(interpret_with_env(a, env)? == interpret_with_env(b, env)?),
        ("&&", [a, b]) => b_to_val(to_b(a, env)? && to_b(b, env)?),
        ("||", [a, b]) => b_to_val(to_b(a, env)? || to_b(b, env)?),
        ("-", [v]) => f_to_val(-to_f(v, env)?),
        _ => interpret_function_call(symbol, params, env),
      }
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
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      let v = interpret_with_env(&exprs[1], env)?;
      scoped_insert(&mut env.values, name.clone(), v);
      //println!("Assign value '{}' to variable '{}'", v, name);
      Ok(Value::Unit)
    }
    ("=", [Expr::Symbol(var_symbol), value_expr]) => {
      let v = interpret_with_env(&value_expr, env)?;
      match scoped_get(&mut env.values, var_symbol) {
        Some(variable) => {
          *variable = v;
          Ok(Value::Unit)
        }
        None => Err(format!("symbol '{}' was not defined", var_symbol)),
      }
    }
    ("=", [Expr::Expr { symbol, args }, value_expr]) => {
      match (symbol.as_str(), args.as_slice()) {
        ("index", [array_expr, index_expr]) => {
          let v = interpret_with_env(&value_expr, env)?;
          let array_rc = to_array(array_expr, env)?;
          let mut array = array_rc.borrow_mut();
          let f = to_f(index_expr, env)?;
          let i = array_index(&array, f)?;
          array[i] = v;
          Ok(Value::Unit)
        }
        (".", [struct_expr, field_expr]) => {
          let v = interpret_with_env(&value_expr, env)?;
          let structure = to_struct(struct_expr, env)?;
          let field_name : &str = symbol_unwrap(field_expr)?;
          structure.borrow().fields.get(field_name)
            .ok_or_else(||format!("field {} does not exist on struct {:?}.", field_name, structure))?;
          *structure.borrow_mut().fields.get_mut(field_name).unwrap() = v;
          Ok(Value::Unit)
        }
        _ => Err(format!("can't assign to {:?}", (symbol, args))),
      }
    }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return Err(format!("malformed if expression"));
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
        return Err(format!("malformed struct definition"));
      }
      let struct_name = symbol_to_refstr(&exprs[0])?;
      if env.structs.contains_key(&struct_name) {
        return Err(format!("A struct called {} has already been defined.", struct_name));
      }
      let field_names =
        exprs[1..].iter().map(symbol_to_refstr)
        .collect::<Result<HashSet<RefStr>, String>>()?;
      env.structs.insert(struct_name, field_names);
      Ok(Value::Unit)
    }
    ("struct_instantiate", exprs) => {
      if exprs.len() < 1 || exprs.len() % 2 == 0 {
        return Err(format!("malformed struct instantiation {:?}", exprs));
      }
      let name = symbol_to_refstr(&exprs[0])?;
      {
        let struct_def =
          env.structs.get(name.as_str())
          .ok_or_else(|| format!("struct {} does not exist", name))?;
        for i in (1..exprs.len()).step_by(2) {
          let field_name = symbol_unwrap(&exprs[i])?;
          struct_def.get(field_name)
            .ok_or_else(|| format!("unexpected field '{}'", field_name))?;
        }
      };
      let mut fields = HashMap::new();
      for i in (1..exprs.len()).step_by(2) {
        let field_name = symbol_to_refstr(&exprs[i])?;
        let field_value = interpret_with_env(&exprs[i+1], env)?;
        fields.insert(field_name, field_value);
      }
      let s = Rc::new(RefCell::new(Struct { name, fields }));
      Ok(Value::Struct(s))
    }
    (".", [expr, field_name]) => {
      let s = to_struct(expr, env)?;
      let name = symbol_unwrap(field_name)?;
      let v =
        s.borrow().fields.get(name)
        .ok_or_else(||format!("field {} does not exist on struct {:?}.", name, s))?
        .clone();
      Ok(v)
    }
    ("while", exprs) => {
      if exprs.len() != 2 {
        return Err(format!("malformed while block"));
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
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      let args_exprs = match &exprs[1] { Expr::Expr{ args, .. } => args, _ => { return Err(format!("expected an expression")); }};
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

fn interpret_with_env(ast : &Expr, env : &mut Environment) -> Result<Value, String> {
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
      if s.as_str() == "break" {
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

