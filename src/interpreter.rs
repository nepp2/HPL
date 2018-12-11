
use error::{Error, TextLocation, error, error_raw, error_no_loc};
use value::*;
use intrinsics::IntrinsicDef;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::usize;
use itertools::Itertools;

lazy_static! {
  static ref BYTECODE_OPERATORS : HashSet<&'static str> =
    vec!["+", "-", "*", "/", ">", "<", "<=", ">=",
    "==", "&&", "||", "-", "!"].into_iter().collect();
}


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
fn array_index(array : &Vec<Value>, index : f32) -> Result<usize, Error> {
  let i = index as usize;
  if index >= 0.0 && i < array.len() {
    Ok(i)
  }
  else {
    Err(error_no_loc(format!("Index out of bounds error. Array of {} elements given index {}.", array.len(), index)))
  }
}

fn intrinsic_functions<'l>(sc : &mut SymbolCache) -> Vec<FunctionDef<'l>> {
  
  fn intrinsic<'l>(sc : &mut SymbolCache, name: &str, args: &[&str], f: fn(&[Value]) -> Result<Value, Error>) -> FunctionDef<'l> {
    FunctionDef {
      info: FunctionInfo { name: sc.symbol(name), arguments: args.iter().map(|s| sc.symbol(*s)).collect() },
      handle: FunctionHandle::Intrinsic(f),
    }
  }

  vec![
    intrinsic(sc, "+", &["a", "b"], |&[a, b]| Ok(Value::Float(to_f(a)? + to_f(b)?))),
    intrinsic(sc, "-", &["a", "b"], |&[a, b]| Ok(Value::Float(to_f(a)? - to_f(b)?))),
    intrinsic(sc, "*", &["a", "b"], |&[a, b]| Ok(Value::Float(to_f(a)? * to_f(b)?))),
  ]
}

#[derive(Debug)]
pub struct FunctionInfo {
  pub name : RefStr,

  /// Number of arguments the function accepts
  pub arguments : Vec<RefStr>,
}

#[derive(PartialEq)]
enum BreakState {
  Breaking,
  NotBreaking,
}

struct Callable {
  t : FunctionType,
  handle : usize,
}

struct FunctionDef<'l> {
  info : FunctionInfo,
  handle : FunctionHandle<'l>,
}

enum FunctionHandle<'l> {
  Ast(&'l Expr),
  Intrinsic(fn(&[Value]) -> Result<Value, Error>),
}

struct VarScope {
  base_index : usize,
  vars : Vec<RefStr>,
}

struct LabelState {
  location : usize,
  references : Vec<usize>,
}

struct Environment<'l> {
  functions : &'l mut HashMap<RefStr, FunctionDef<'l>>,

  structs : &'l mut HashMap<RefStr, Rc<StructDef>>,
  symbol_cache : &'l mut SymbolCache,

  /// function name
  function_name : RefStr,

  /// the arguments that this function receives
  arguments : Vec<RefStr>,

  /// stores offset of each local variable in the stack frame
  locals : Vec<VarScope>,

  /// keeps track of labels
  labels : HashMap<RefStr, LabelState>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_break_labels : Vec<RefStr>,

  break_state : BreakState,
}

impl <'l> Environment<'l> {
  fn new(
    function_name : RefStr,
    arguments : Vec<RefStr>,
    functions : &'l mut HashMap<RefStr, FunctionDef<'l>>,
    structs : &'l mut HashMap<RefStr, Rc<StructDef>>,
    symbol_cache : &'l mut SymbolCache,
  ) -> Environment<'l> {
    let vs = VarScope { base_index: 0, vars: arguments.clone() };
    let locals = vec![vs];
    Environment{
      function_name, arguments,
      functions,
      structs, symbol_cache, locals,
      labels: HashMap::new(),
      loop_break_labels: vec!(),
      break_state : BreakState::NotBreaking,
    }
  }

  fn label(&mut self, s : &str) -> RefStr {
    let mut i = 0;
    let mut label_string;
    // TODO: this is not very efficient, and should maybe be fixed
    loop {
      label_string = format!("{}_{}",s, i);
      if !self.labels.contains_key(label_string.as_str()) {
        break;
      }
      i += 1;
    }
    let label = self.symbol_cache.symbol(label_string);
    self.labels.insert(label.clone(), LabelState { location: usize::MAX, references: vec!() });
    label
  }

  fn push_scope(&mut self, v : VarScope) {
    self.locals.push(v);
  }

  fn pop_scope(&mut self) {
    let new_local_count = self.count_locals();
    if new_local_count > self.max_locals {
      self.max_locals = new_local_count;
    }
    self.locals.pop();
  }

  fn allocate_var_offset(&mut self, name : RefStr) -> usize {
    let offset = self.count_locals();
    self.locals.last_mut().unwrap().vars.push(name);
    offset
  }

  fn count_locals(&self) -> usize {
    if self.locals.len() == 0 {
      0
    }
    else {
      let vs = &self.locals[self.locals.len()-1];
      vs.base_index + vs.vars.len()
    }
  }

  fn get_var_offset(&self, v : &str) -> Option<usize> {
    for vs in self.locals.iter().rev() {
      for i in (0..vs.vars.len()).rev() {
        if vs.vars[i].as_ref() == v {
          return Some(vs.base_index + i);
        }
      }
    }
    None
  }

  fn read_var(&self, v : &str) -> Option<Value> {
    panic!()
  }

  fn find_var_offset(&self, v : &str, loc : &TextLocation) -> Result<usize, Error> {
    self.get_var_offset(v)
      .ok_or_else(|| error_raw(*loc, format!("no variable called '{}' found in scope", v)))
  }

  fn get_callable(&self, name : &str) -> Option<Callable> {
    self.functions.get(name)
      .map(|f| (f.handle, FunctionType::Function))
      .or_else(|| {
        self.intrinsics.get(name)
        .map(|i| (i.handle, FunctionType::Intrinsic))
      })
      .map(|(handle, t)| Callable { handle, t} )
  }
}

fn function_call(function_expr: &Expr, args: &[Expr], env : &mut Environment)
  -> Result<Value, Error>
{
  let handle =
    function_expr.symbol_unwrap().ok()
    .and_then(|f| {
      if env.get_var_offset(f) == None {
        env.get_callable(f)
      }
      else { None }
    });
  if let Some(h) = handle {
    for i in 0..args.len() {
      compile(&args[i], env, true)?;
    }
    env.emit_always(BC::CallFunction(h.t, h.handle));
  }
  else {
    compile(function_expr, env, true)?;
    if args.len() > 0 {
      let v = VarScope { base_index: env.count_locals(), vars: vec!() };
      env.push_scope(v);
      let function_var = env.symbol_cache.symbol("[function_var]");
      let offset = env.allocate_var_offset(function_var);
      env.emit_always(BC::SetVar(offset));
      for i in 0..args.len() {
        compile(&args[i], env, true)?;
      }
      env.emit_always(BC::PushVar(offset));
      env.pop_scope();
    }
    env.emit_always(BC::CallFirstClassFunction);
  }
  if !push_answer {
    env.emit_always(BC::Pop);
  }
  Ok(())
}

fn interpret_instr(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  let instr = expr.tree_symbol_unwrap()?.as_ref();
  let children = expr.children.as_slice();
  match (instr, children) {
    ("call", exprs) => {
      let function_expr = &exprs[0];
      let params = &exprs[1..];
      function_call(function_expr, params, env)
    }
    ("block", exprs) => {
      let v = VarScope { base_index: env.count_locals(), vars: vec!() };
      env.push_scope(v);
      let num_exprs = exprs.len();
      if num_exprs > 1 {
        for i in 0..(num_exprs-1) {
          interpret(&exprs[i], env)?;
        }
      }
      let value =
        if num_exprs > 0 {
          interpret(&exprs[num_exprs-1], env)
        } else { Ok(Value::Unit) };
      env.pop_scope();
      value
    }
    ("let", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let val = interpret(&exprs[1], env)?;
      env.new_var(name.clone(), val);
      Ok(Value::Unit)
    }
    ("=", [_, assign_expr, value_expr]) => {
      match &assign_expr.tag {
        ExprTag::Symbol(var_symbol) => {
          let val = interpret(value_expr, env)?;
          let offset = env.set_var(&var_symbol, val)?;
          Ok(Value::Unit);
        }
        ExprTag::Tree(symbol) => {
          match (symbol.as_ref(), assign_expr.children.as_slice()) {
            ("index", [array_expr, index_expr]) => {
              let array = to_array(interpret(array_expr, env)?)?;
              let index = to_f(interpret(index_expr, env)?)?;
              let value = interpret(value_expr, env)?;
              let a = array.borrow_mut();
              let i = array_index(&a, index)?;
              a[i] = value;
              Ok(Value::Unit);
            }
            (".", [struct_expr, field_expr]) => {
              compile(struct_expr, env, true)?;
              compile(value_expr, env, true)?;
              let field_name = field_expr.symbol_unwrap()?;
              env.emit_always(BC::SetStructField(field_name.clone()));
              return Ok(());
            }
            _ => (),
          }
        }
        _ => (),
      }
      return error(assign_expr, format!("can't assign to {:?}", assign_expr));
    }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return error(expr, "malformed if expression");
      }
      let condition_true = to_b(interpret(&exprs[0], env)?)?;
      if condition_true {
        interpret(&exprs[1], env)?
      }
      else {
        if arg_count == 3 {
          interpret(&exprs[2], env)?
        }
        else {
          Ok(Value::Unit)
        }
      }
    }
    ("struct_define", exprs) => {
      if exprs.len() < 1 {
        return error(expr, "malformed struct definition");
      }
      let name_expr = &exprs[0];
      let name = name_expr.symbol_to_refstr()?;
      if env.structs.contains_key(&name) {
        return error(name_expr, format!("A struct called {} has already been defined.", name));
      }
      // TODO: check for duplicates?
      let field_exprs = &exprs[1..];
      let mut fields = vec![];
      for (e, _) in field_exprs.iter().tuples() {
        fields.push(e.symbol_to_refstr()?);
      }
      let def = Rc::new(StructDef { name: name.clone(), fields });
      env.structs.insert(name, def);
    }
    ("struct_instantiate", exprs) => {
      if exprs.len() < 1 || exprs.len() % 2 == 0 {
        return error(expr, format!("malformed struct instantiation {:?}", exprs));
      }
      let name_expr = &exprs[0];
      let name = name_expr.symbol_to_refstr()?;
      let def =
        env.structs.get(name.as_ref())
        .ok_or_else(|| error_raw(name_expr, format!("struct {} does not exist", name)))?.clone();
      env.emit(BC::NewStruct(def.clone()), push_answer);
      {
        let mut field_index_map =
          def.fields.iter().enumerate()
          .map(|(i, s)| (s.as_ref(), i)).collect::<HashMap<&str, usize>>();
        for (field, value) in exprs[1..].iter().tuples() {
          let field_name = field.symbol_to_refstr()?;
          compile(value, env, push_answer)?;
          let index = field_index_map.remove(field_name.as_ref())
            .ok_or_else(|| error_raw(field, format!("field {} does not exist", name)))?;
          env.emit(BC::StructFieldInit(index), push_answer);
        }
        if field_index_map.len() > 0 {
          return error(expr, "Some fields not initialised");
        }
      }
    }
    (".", [_, expr, field_name]) => {
      compile(expr, env, push_answer)?;
      let name = field_name.symbol_unwrap()?;
      env.emit(BC::PushStructField(name.clone()), push_answer);
    }
    ("while", exprs) => {
      does_not_push(expr, push_answer)?;
      if exprs.len() != 2 {
        return error(expr, "malformed while block");
      }
      let condition_label = env.label("loop_condition");
      let end_label = env.label("loop_end");
      env.loop_break_labels.push(end_label.clone());
      env.emit_label(condition_label.clone());
      compile(&exprs[0], env, true)?; // emit condition
      env.emit_jump_if_false(&end_label); // exit loop if condition fails
      compile(&exprs[1], env, false)?; // emit loop body
      env.emit_jump(&condition_label); // jump back to the condition
      env.emit_label(end_label);
      env.loop_break_labels.pop();
    }
    ("fun", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let args_exprs = exprs[1].children.as_slice();
      let function_body = &exprs[2];
      let mut params = vec![];
      for (arg, _) in args_exprs.iter().tuples() {
        params.push(arg.symbol_to_refstr()?);
      }
      compile_function(function_body, name.clone(), params, env.functions, env.intrinsics, env.structs, env.symbol_cache)?;
    }
    ("literal_array", exprs) => {
      for e in exprs {
        compile(e, env, push_answer)?;
      }
      env.emit(BC::NewArray(exprs.len()), push_answer);
    }
    ("index", exprs) => {
      if let [array_expr, index_expr] = exprs {
        compile(array_expr, env, push_answer)?;
        compile(index_expr, env, push_answer)?;
        env.emit(BC::ArrayIndex, push_answer);
      }
      else {
        return error(expr, format!("index instruction expected 2 arguments. Found {}.", exprs.len()));
      }
    }
    _ => {
      return error(expr, format!("instruction '{}' with {} args is not supported by the interpreter.", instr, children.len()));
    }
  }
}

fn interpret(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  if env.break_state == BreakState::Breaking {
    // this basically skips all evaluations until we backtrack to the loop,
    // which will spot the break state and stop iterating.
    return Ok(Value::Unit);
  }
  match &expr.tag {
    ExprTag::Tree(_) => {
      interpret_instr(expr, env)
    }
    ExprTag::Symbol(s) => {
      if s.as_ref() == "break" {
        if env.loop_break_labels.len() > 0 {
          env.break_state = BreakState::Breaking;
          Ok(Value::Unit)
        }
        else {
          error(expr, "can't break outside a loop")
        }
      }
      else {
        if let Some(v) = env.read_var(&s) {
          Ok(v)
        }
        else if let Some(callable) = env.get_callable(&s) {
          let v = Value::Function(callable.t, callable.handle);
          Ok(v)
        }
        else {
          return error(expr, format!("no variable or function in scope called '{}'", s));
        }
      }
    }
    ExprTag::LiteralString(s) => {
      Ok(Value::String(s.clone()))
    }
    ExprTag::LiteralFloat(f) => {
      Ok(Value::Float(*f))
    }
    ExprTag::LiteralBool(b) => {
      Ok(Value::Bool(*b))
    }
  }
}

fn interpret_function(
  function_body : &Expr,
  name : RefStr,
  arguments : Vec<RefStr>,
  functions : &mut HashMap<RefStr, FunctionDef>,
  structs : &mut HashMap<RefStr, Rc<StructDef>>,
  symbol_cache : &mut SymbolCache,)
  -> Result<Value, Error>
{
  let mut new_env = Environment::new(name, arguments, functions, structs, symbol_cache);
  interpret(function_body, &mut new_env)
}

pub fn interpret_program(
    expr : &Expr,
    sc : &mut SymbolCache,
    intrinsics : &HashMap<RefStr, IntrinsicDef>)
  -> Result<Value, Error>
{
  let mut functions = HashMap::new();
  let mut structs = HashMap::new();
  interpret_function(expr, sc.symbol("__program_main__"), vec![], &mut functions, intrinsics, &mut structs, sc)
}
