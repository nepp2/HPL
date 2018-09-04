
use parser::Expr;
use lexer::{RefStr, AsStr, SymbolCache};
use interpreter::{Value, Struct, Array, StructVal};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;

type FunctionHandle = usize;

enum BytecodeInstruction {
  Push(Value),
  PushVar(usize),
  Add,
  Call(FunctionHandle),
  Jump(RefStr),
  Label(RefStr),
  Return,
}

struct BytecodeFunction {
  instructions : Vec<BytecodeInstruction>
}

struct BytecodeProgram {
  functions : Vec<BytecodeFunction>,
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

struct FunctionDef {
  args : Vec<RefStr>,
  expr : Rc<Expr>,
}

type StructDef = HashSet<RefStr>;

struct VarScope {
  base_index : usize,
  vars : Vec<RefStr>,
}

struct Environment<'l> {
  functions : &'l mut HashMap<RefStr, BytecodeFunction>,
  structs : &'l mut HashMap<RefStr, StructDef>,
  symbol_cache : &'l mut SymbolCache,

  /// stores offset of each local variable in the stack frame
  locals : Vec<VarScope>,

  /// the maximum number of locals visible in any scope of the function
  max_locals : i32,

  instructions : Vec<BytecodeInstruction>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_depth : i32,
}

impl <'l> Environment<'l> {
  fn new(
    functions : &'l mut HashMap<RefStr, BytecodeFunction>,
    structs : &'l mut HashMap<RefStr, StructDef>,
    symbol_cache : &'l mut SymbolCache,
  ) -> Environment<'l> {
    Environment{
      functions, structs, symbol_cache,
      locals: vec!(),
      max_locals: 0,
      instructions: vec!(),
      loop_depth: 0,
    }
  }

  fn find_var_offset(&self, v : &str) -> Result<usize, String> {
    for vs in self.locals.iter().rev() {
      for i in (0..vs.vars.len()).rev() {
        if vs.vars[i].as_ref() == v {
          return Ok(vs.base_index + i);
        }
      }
    }
    Err(format!("no variable called '{}' found in scope", v))
  }
}

/*
fn compile_function_call(function_name: &str, args: &[Expr], env : &mut Environment)
  -> Result<Value, String>
{
  let mut arg_values = vec!();
  for i in 0..args.len() {
    let v = compile(&args[i], env)?;
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
  compile(&expr, &mut new_env)
}

fn compile_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment) -> Result<Value, String> {

  fn to_f(v : &Expr, env : &mut Environment) -> Result<f32, String> {
    match compile(v, env)? {
      Value::Float(f) => Ok(f),
      x => Err(format!("Expected float, found {:?}.", x))
    }
  }
  fn to_b(v : &Expr, env : &mut Environment) -> Result<bool, String> {
    match compile(v, env)? {
      Value::Bool(b) => Ok(b),
      x => Err(format!("Expected boolean, found {:?}.", x))
    }
  }
  fn to_array(v : &Expr, env : &mut Environment) -> Result<Array, String> {
    match compile(v, env)? {
      Value::Array(a) => Ok(a),
      x => Err(format!("Expected array, found {:?}.", x))
    }
  }
  fn to_struct(v : &Expr, env : &mut Environment) -> Result<StructVal, String> {
    match compile(v, env)? {
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
        ("==", [a, b]) => b_to_val(compile(a, env)? == compile(b, env)?),
        ("&&", [a, b]) => b_to_val(to_b(a, env)? && to_b(b, env)?),
        ("||", [a, b]) => b_to_val(to_b(a, env)? || to_b(b, env)?),
        ("-", [v]) => f_to_val(-to_f(v, env)?),
        _ => compile_function_call(symbol, params, env),
      }
    }
    ("block", exprs) => {
      env.values.push(HashMap::new());
      let last_val = {
        let expr_count = exprs.len();
        if expr_count > 1 {
          for i in 0..expr_count {
            let _ = compile(&exprs[i], env)?;
          }
        }
        compile(&exprs[expr_count-1], env)
      };
      env.values.pop();
      last_val
    }
    ("let", exprs) => {
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      let v = compile(&exprs[1], env)?;
      scoped_insert(&mut env.values, name.clone(), v);
      //println!("Assign value '{}' to variable '{}'", v, name);
      Ok(Value::Unit)
    }
    ("=", [Expr::Symbol(var_symbol), value_expr]) => {
      let v = compile(&value_expr, env)?;
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
          let v = compile(&value_expr, env)?;
          let array_rc = to_array(array_expr, env)?;
          let mut array = array_rc.borrow_mut();
          let f = to_f(index_expr, env)?;
          let i = array_index(&array, f)?;
          array[i] = v;
          Ok(Value::Unit)
        }
        (".", [struct_expr, field_expr]) => {
          let v = compile(&value_expr, env)?;
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
        compile(&exprs[1], env)
      }
      else if arg_count == 3 {
        compile(&exprs[2], env)
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
        let field_value = compile(&exprs[i+1], env)?;
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
        compile(&exprs[1], env)?;
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
        let v = compile(e, env)?;
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

*/

fn compile(ast : &Expr, env : &mut Environment) -> Result<(), String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      //compile_instr(symbol, args, env)
      return Err(format!("exprs are not implemented"));
    }
    Expr::Symbol(s) => {
      if s.as_str() == "break" {
        if env.loop_depth > 0 {
          let l = env.symbol_cache.symbol(format!("loop_end_{}", env.loop_depth));
          env.instructions.push(BytecodeInstruction::Jump(l));
        }
        else {
          return Err(format!("can't break outside a loop"));
        }
      }
      else {
        let offset = env.find_var_offset(s)?;
        env.instructions.push(BytecodeInstruction::PushVar(offset));
      }
    }
    Expr::LiteralFloat(f) => {
      let v = Value::Float(*f);
      env.instructions.push(BytecodeInstruction::Push(v));
    }
    Expr::LiteralBool(b) => {
      let v = Value::Bool(*b);
      env.instructions.push(BytecodeInstruction::Push(v));
    }
  }
  Ok(())
}

fn compile_bytecode(ast : &Expr) -> Result<BytecodeProgram, String> {
  let mut fs = HashMap::new();
  let mut structs = HashMap::new();
  let mut symbol_cache = SymbolCache::new();
  let mut env = Environment::new(&mut fs, &mut structs, &mut symbol_cache);
  compile(ast, &mut env)?;
  Err(format!("compiler does not exist"))
}

fn interpret_bytecode(program : &BytecodeProgram, entry_point : FunctionHandle) -> Result<Value, String> {
  let mut stack : Vec<Value> = vec!();
  let mut function =
    program.functions.get(entry_point).ok_or_else(|| format!("No function found"))?;
  let mut program_counter = 0;
  loop {
    if program_counter >= function.instructions.len() {
      return Err(format!("program counter out of bounds"));
    }
    match function.instructions[program_counter] {
      _ => (),
    }
    program_counter += 1;
  }
  return Ok(Value::Unit);
}

pub fn interpret(ast : &Expr) -> Result<Value, String> {
  let program = compile_bytecode(ast)?;
  interpret_bytecode(&program, 0)
}
