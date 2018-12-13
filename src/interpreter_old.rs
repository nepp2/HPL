
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
  Intrinsic(fn(&[Value]) -> Result<Value, String>),
}

fn intrinsic_functions<'l>(sc : &mut SymbolCache) -> HashMap<RefStr, FunctionDef<'l>> {

  macro_rules! intrinsic {
    ($n:expr, $a:ident, $b:ident, $c:ident, $f:expr) => {
      {
        let f : fn(&[Value]) -> Result<Value, String> =
          |vals : &[Value]| {
            let a : Result<$a, String> = vals[0].clone().into();
            let b : Result<$b, String> = vals[1].clone().into();
            let c : $c = ($f)(a?, b?);
            let v : Value = Value::from(c);
            Ok(v)
          };
        ($n, 2, f)
      }
    }
  }
/*
  fn intrinsic<'l, A, B, C>(sc : &mut SymbolCache, name: &str, f: fn(A, B) -> C) -> FunctionDef<'l>
    where Value: Into<Result<A, String>>, Value: Into<Result<B, String>>, Value: From<C>, A: 'static, B: 'static, C: 'static
  {
    let wrapped_f : Box<Fn(&[Value]) -> Result<Value, String>> =
      Box::new(move |vals : &[Value]| {
        let a : Result<A, String> = vals[0].clone().into();
        let b : Result<B, String> = vals[1].clone().into();
        let c : C = f(a?, b?);
        let v : Value = Value::from(c);
        Ok(v)
      });
    FunctionDef {
      info: FunctionInfo { name: sc.symbol(name), arguments: ["a", "b"].iter().map(|s| sc.symbol(*s)).collect() },
      handle: FunctionHandle::Intrinsic(wrapped_f),
    }
  }
  */

  fn def<'l>(sc : &mut SymbolCache, name: &str, num_params : i32, f: fn(&[Value]) -> Result<Value, String>) -> FunctionDef<'l> {
    let arguments : Vec<RefStr> = (0..num_params).map(|i| ((('a' as i32) + i) as u8 as char).to_string()).map(|s| sc.symbol(s)).collect();
    FunctionDef {
      info: FunctionInfo { name: sc.symbol(name), arguments },
      handle: FunctionHandle::Intrinsic(f),
    }
  }

  let instrinsics = vec![
    intrinsic!("+", f32, f32, f32, |a, b| a + b),
    intrinsic!("-", f32, f32, f32, |a, b| a - b),
    intrinsic!("*", f32, f32, f32, |a, b| a * b),
    intrinsic!("/", f32, f32, f32, |a, b| a / b),
    intrinsic!(">", f32, f32, bool, |a, b| a > b),
    intrinsic!("<", f32, f32, bool, |a, b| a < b),
    intrinsic!("<=", f32, f32, bool, |a, b| a <= b),
    intrinsic!(">=", f32, f32, bool, |a, b| a >= b),
    ("==", 2, |vs| {
      let b = vs[0] == vs[1];
      Ok(Value::from(b))
    }),
    intrinsic!("&&", bool, bool, bool, |a, b| a && b),
    intrinsic!("||", bool, bool, bool, |a, b| a || b),
    ("-", 1, |vs| {
      let f : Result<f32, String> = vs[0].clone().into();
      Ok(Value::from(-f?))
    }),
  ];

  let mut map = HashMap::new();
  for (n, params, f) in instrinsics {
    let d = def(sc, n, params, f);
    map.insert(d.info.name.clone(), d);
  }
  map
}

struct Environment<'l, 'e : 'l> {
  symbol_cache : &'l mut SymbolCache,

  values : &'l mut Vec<HashMap<RefStr, Value>>,
  functions : &'l mut Vec<HashMap<RefStr, FunctionDef<'e>>>,
  structs : &'l mut HashMap<RefStr, Rc<StructDef>>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_depth : i32,

  /// indicates whether the program is currently breaking out of a loop
  break_state : BreakState,
}

impl <'l, 'e> Environment<'l, 'e> {
  fn new(
    symbol_cache : &'l mut SymbolCache,
    values : &'l mut Vec<HashMap<RefStr, Value>>,
    functions : &'l mut Vec<HashMap<RefStr, FunctionDef<'e>>>,
    structs : &'l mut HashMap<RefStr, Rc<StructDef>>,
  ) -> Environment<'l, 'e> {
    Environment{
      symbol_cache, values, functions, structs,
      loop_depth: 0,
      break_state: BreakState::NotBreaking
    }
  }
}

fn interpret_function_call<'l, 'e>(expr : &'e Expr, function_name_expr: &'e Expr, args: &'e [Expr], env : &mut Environment<'l, 'e>)
  -> Result<Value, Error>
{
  let function_name = function_name_expr.symbol_unwrap()?;
  let mut arg_values = vec!();
  for i in 0..args.len() {
    let e = &args[i];
    let v = interpret_with_env(e, env)?;
    arg_values.push(v);
  }
  // TODO: this code is structured in a crazy way using direct returns because the borrow-checker is stupid
  let (mut vs, expr) = {
    match scoped_get(&mut env.functions, function_name) {
      Some(fd) => 
        match &fd.handle {
          FunctionHandle::Ast(expr) => {
            let mut args = HashMap::new();
            for (v, n) in arg_values.into_iter().zip(&fd.info.arguments) {
              args.insert(n.clone(), v);
            }
            (vec!(args), *expr)
          }
          FunctionHandle::Intrinsic(f) => {
            return f(arg_values.as_slice()).map_err(|s| error_raw(function_name_expr, s))
          }
        },
      None => return error(expr, format!("Found no function called '{}'", function_name)),
    }
  };
  let mut new_env = Environment::new(env.symbol_cache, &mut vs, env.functions, env.structs);
  interpret_with_env(&expr, &mut new_env)
}

fn to_value<'l, 'e, V>(e : &'e Expr, env : &mut Environment<'l, 'e>) -> Result<V, Error>
  where Value: Into<Result<V, String>>
{
  let v = interpret_with_env(e, env)?;
  let r : Result<V, String> = v.into();
  r.map_err(|s| error_raw(e, s))
}

/*
fn f_to_val(f : f32) -> Result<Value, String> {
  Ok(Value::Float(f))
}
fn b_to_val(b : bool) -> Result<Value, String> {
  Ok(Value::Bool(b))
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

fn interpret_tree<'l, 'e>(expr : &'e Expr, env : &mut Environment<'l, 'e>) -> Result<Value, Error> {
  let instr = expr.tree_symbol_unwrap()?.as_ref();
  let children = expr.children.as_slice();
  match (instr, children) {
    ("call", exprs) => {
      let function_name_expr = &exprs[0];
      let params = &exprs[1..];
      interpret_function_call(expr, function_name_expr, params, env)
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
              let array_rc : Array = to_value(array_expr, env)?;
              let mut array = array_rc.borrow_mut();
              let f = to_value(index_expr, env)?;
              let i = array_index(&array, f)?;
              array[i] = v;
              return Ok(Value::Unit)
            }
            (".", [struct_expr, field_expr]) => {
              let v = interpret_with_env(&value_expr, env)?;
              let structure : StructVal = to_value(struct_expr, env)?;
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
      let condition = to_value(&exprs[0], env)?;
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
      let s : StructVal = to_value(expr, env)?;
      let index = struct_field_index(&s.borrow().def, name_expr)?;
      let v = s.borrow().fields[index].clone();
      Ok(v)
    }
    ("while", exprs) => {
      if exprs.len() != 2 {
        return error(expr, format!("malformed while block"));
      }
      env.loop_depth += 1;
      while env.break_state != BreakState::Breaking && to_value(&exprs[0], env)? {
        interpret_with_env(&exprs[1], env)?;
      }
      env.loop_depth -= 1;
      env.break_state = BreakState::NotBreaking;
      Ok(Value::Unit)
    }
    ("fun", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let args_exprs = exprs[1].children.as_slice();
      let function_body = &exprs[2];
      let mut args = vec!();
      for e in args_exprs {
        args.push(e.symbol_to_refstr()?);
      }
      let def = FunctionDef {
        info: FunctionInfo { name: name.clone(), arguments: args },
        handle: FunctionHandle::Ast(function_body),
      };
      scoped_insert(&mut env.functions, name.clone(), def);
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
        let array_rc = to_value::<Array>(array_expr, env)?;
        let array = array_rc.borrow();
        let f = to_value(index_expr, env)?;
        let i = array_index(&array, f)?;
        Ok(array[i].clone())
      }
      else {
        error(expr, format!("index instruction expected 2 arguments. Found {}.", exprs.len()))
      }
    }
    _ => error(expr, format!("instruction '{}' with args {:?} is not supported by the interpreter.", instr, children)),
  }
}

fn interpret_with_env<'l, 'e>(expr : &'e Expr, env : &mut Environment<'l, 'e>) -> Result<Value, Error> {
  if env.break_state == BreakState::Breaking {
    // this basically skips all evaluations until we backtrack to the loop,
    // which will spot the break state and stop iterating.
    return Ok(Value::Unit);
  }
  match &expr.tag {
    ExprTag::Tree(_) => {
      interpret_tree(expr, env)
    }
    ExprTag::Symbol(s) => {
      if s.as_ref() == "break" {
        if env.loop_depth > 0 {
          env.break_state = BreakState::Breaking;
          Ok(Value::Unit)
        }
        else {
          error(expr, format!("can't break outside a loop"))
        }
      }
      else {
        match scoped_get(&mut env.values, &s) {
          Some(v) => Ok(v.clone()),
          None => error(expr, format!("symbol '{}' was not defined", s)),
        }
      }
    }
    ExprTag::LiteralString(s) => Ok(Value::String(s.clone())),
    ExprTag::LiteralFloat(f) => Ok(Value::Float(*f)),
    ExprTag::LiteralBool(b) => Ok(Value::Bool(*b)),
  }
}

pub fn interpret_with_cache(ast : &Expr, sc : &mut SymbolCache) -> Result<Value, Error> {
  let instrinsics = intrinsic_functions(sc);
  let mut vs = vec!(HashMap::new());
  let mut fs = vec!(instrinsics);
  let mut structs = HashMap::new();
  let mut env = Environment::new(sc, &mut vs, &mut fs, &mut structs);
  interpret_with_env(ast, &mut env)
}

pub fn interpret(ast : &Expr) -> Result<Value, Error> {
  let mut sc = SymbolCache::new();
  interpret_with_cache(ast, &mut sc)
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let mut sc = SymbolCache::new();
  let tokens = lexer::lex_with_cache(code, &mut sc).unwrap();
  let ast = parser::parse_with_cache(tokens, &mut sc).unwrap();
  let result = interpret_with_cache(&ast, &mut sc);
  println!("{:?}", result);
}

