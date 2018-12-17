
use parser;
use lexer;
use value::*;
use error::{Error, error, error_raw, error_no_loc};
use std::collections::HashMap;
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

enum FunctionHandle<'e> {
  Ast(&'e Expr),
  Intrinsic(fn(&[Value]) -> Result<Value, String>),
}

fn intrinsic_functions<'e>(sc : &mut SymbolCache) -> HashMap<RefStr, MultiMethod<'e>> {

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
        ($n, vec![type_tag!($a), type_tag!($b)], f)
      }
    }
  }

  macro_rules! type_tag {
    (f32) => { FLOAT };
    (bool) => { BOOL };
    (RefStr) => { STRING };
    (()) => { UNIT };
  }

  // TODO: awful bug - Can't have multiple operators with the same name

  let instrinsics = vec![
    intrinsic!("+", f32, f32, f32, |a, b| a + b),
    intrinsic!("-", f32, f32, f32, |a, b| a - b),
    intrinsic!("*", f32, f32, f32, |a, b| a * b),
    intrinsic!("/", f32, f32, f32, |a, b| a / b),
    intrinsic!(">", f32, f32, bool, |a, b| a > b),
    intrinsic!("<", f32, f32, bool, |a, b| a < b),
    intrinsic!("<=", f32, f32, bool, |a, b| a <= b),
    intrinsic!(">=", f32, f32, bool, |a, b| a >= b),
    ("==", vec![ANY, ANY], |vs| {
      let b = vs[0] == vs[1];
      Ok(Value::from(b))
    }),
    intrinsic!("&&", bool, bool, bool, |a, b| a && b),
    intrinsic!("||", bool, bool, bool, |a, b| a || b),
    ("-", vec![FLOAT], |vs| {
      let f : Result<f32, String> = vs[0].clone().into();
      Ok(Value::from(-f?))
    }),
  ];

  let mut functions = HashMap::new();
  for (n, arg_tags, f) in instrinsics {
    let arg_names : Vec<RefStr> =
      (0..arg_tags.len()).map(|i| ((('a' as usize) + i) as u8 as char)
      .to_string()).map(|s| sc.symbol(s)).collect();
    let m = Method { arg_names, arg_tags, handle: FunctionHandle::Intrinsic(f) };
    add_method(n, m, sc, &mut functions);
  }
  functions
}

fn add_method<'e>(name : &str, method : Method<'e>, sc : &mut SymbolCache, functions : &mut HashMap<RefStr, MultiMethod<'e>>) {
  if let Some(mm) = functions.get_mut(name) {
    mm.variants.push(method);
    return;
  }  
  let name = sc.symbol(name);
  let m = MultiMethod { variants: vec![method] };
  functions.insert(name, m);
}

/*

Multimethods
- look up the name of the function
- choose implementation that matches the arguments most closely

Things I need:
- every type needs a numerical tag
- there needs to be a "more general" relationship between some (maybe)

    can just have a single "any" tag
- should add an unsafe union of the core types, I guess

*/

struct Method<'e> {
  arg_tags : Vec<i32>,
  arg_names : Vec<RefStr>,
  handle : FunctionHandle<'e>,
}

struct MultiMethod<'e> {
  variants : Vec<Method<'e>>,
}

struct Environment<'l, 'e : 'l> {
  symbol_cache : &'l mut SymbolCache,

  values : &'l mut Vec<HashMap<RefStr, Value>>,
  functions : &'l mut HashMap<RefStr, MultiMethod<'e>>,
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
    functions : &'l mut HashMap<RefStr, MultiMethod<'e>>,
    structs : &'l mut HashMap<RefStr, Rc<StructDef>>,
  ) -> Environment<'l, 'e> {
    Environment{
      symbol_cache, values, functions, structs,
      loop_depth: 0,
      break_state: BreakState::NotBreaking
    }
  }

  fn add_function(&mut self, name : &str, method : Method<'e>) {
    add_method(name, method, &mut self.symbol_cache, &mut self.functions)
  }

  fn get_method(&self, name : &str, arg_tags : &[i32]) -> Option<&Method<'e>> {
    self.functions.get(name).and_then(|mm| {
      'outer: for m in mm.variants.iter() {
        if m.arg_tags.len() != arg_tags.len(){
          continue 'outer;
        }
        for (a, b) in m.arg_tags.iter().zip(arg_tags) {
          let (a, b) = (*a, *b);
          if a != b && a != 0 && b != 0 {
            continue 'outer;
          }
        }
        return Some(m)
      }
      None
    })
  }
}

fn interpret_function_call<'l, 'e>(expr : &'e Expr, function_name_expr: &'e Expr, args: &'e [Expr], env : &mut Environment<'l, 'e>)
  -> Result<Value, Error>
{
  let function_name = function_name_expr.symbol_unwrap()?;
  let mut arg_values = vec!();
  let mut arg_tags = vec!();
  for i in 0..args.len() {
    let e = &args[i];
    let v = interpret_with_env(e, env)?;
    arg_tags.push(v.tag());
    arg_values.push(v);
  }
  // TODO: this code is structured in a crazy way using direct returns because the borrow-checker is stupid
  let (mut values, expr) = {
    match env.get_method(function_name, arg_tags.as_slice()) {
      Some(m) => 
        match &m.handle {
          FunctionHandle::Ast(expr) => {
            let mut args = HashMap::new();
            for (v, n) in arg_values.into_iter().zip(&m.arg_names) {
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
  let mut new_env = Environment::new(env.symbol_cache, &mut values, env.functions, env.structs);
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
      let method = Method {
        arg_names: args,
        arg_tags: args_exprs.iter().map(|_| 0).collect(), // TODO: need to read the type signatures
        handle: FunctionHandle::Ast(function_body),
      };
      env.add_function(name, method);
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
  let mut initial_functions = intrinsic_functions(sc);
  let mut vs = vec!(HashMap::new());
  let mut structs = HashMap::new();
  let mut env = Environment::new(sc, &mut vs, &mut initial_functions, &mut structs);
  interpret_with_env(ast, &mut env)
}

pub fn interpret(ast : &Expr) -> Result<Value, Error> {
  let mut sc = SymbolCache::new();
  interpret_with_cache(ast, &mut sc)
}

pub fn interpret_string(code : &str) -> Result<Value, Error> {
  let mut sc = SymbolCache::new();
  let tokens = lexer::lex_with_cache(code, &mut sc).unwrap();
  let ast = parser::parse_with_cache(tokens, &mut sc).unwrap();
  interpret_with_cache(&ast, &mut sc)
}

#[test]
fn test_interpret() {
  let code = "(3 + 4) * 10";
  let result = interpret_string(code);
  println!("{:?}", result);
}

