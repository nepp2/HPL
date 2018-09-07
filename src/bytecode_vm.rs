
use parser::Expr;
use lexer::{RefStr, AsStr, SymbolCache};
use interpreter::{Value, Struct, Array, StructVal};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;
use std::usize;
use std::iter;

type FunctionHandle = usize;

#[derive(Debug)]
enum BytecodeInstruction {
  Push(Value),
  PushVar(usize),
  Pop,
  Dup,
  NewArray(usize),
  ArrayIndex,
  SetVar(usize),
  Call(FunctionHandle),
  JumpIfFalse(usize),
  Jump(usize),
  BinaryOperator(RefStr),
  UnaryOperator(RefStr),
  Return,
}

use bytecode_vm::BytecodeInstruction as BC;

lazy_static! {
  static ref BYTECODE_OPERATORS : HashSet<&'static str> =
    vec!["+", "-", "*", "/", ">", "<", "<=", ">=",
    "==", "&&", "||", "-"].into_iter().collect();
}

#[derive(Debug)]
struct BytecodeFunction {
  instructions : Vec<BytecodeInstruction>,
  locals : usize,
}

#[derive(Debug)]
struct BytecodeProgram {
  functions : HashMap<RefStr, BytecodeFunction>,
}

// /// Insert the value in the last hashmap in the vector, which represents the local scope.
// fn scoped_insert<T>(stack : &mut Vec<HashMap<RefStr, T>>, s : RefStr, t : T) {
//   let i = stack.len()-1;
//   stack[i].insert(s, t);
// }

// /// Retrieve the value closest to the end of the vector of hashmaps (the most local scope)
// /// in the environment
// fn scoped_get<'l, T>(stack : &'l mut Vec<HashMap<RefStr, T>>, s : &str) -> Option<&'l mut T> {
//   for map in stack.iter_mut().rev() {
//     if map.contains_key(s) {
//       return Some(map.get_mut(s).unwrap());
//     }
//   }
//   return None;
// }

// struct FunctionDef {
//   args : Vec<RefStr>,
//   expr : Rc<Expr>,
// }

type StructDef = HashSet<RefStr>;

struct VarScope {
  base_index : usize,
  vars : Vec<RefStr>,
}

struct LabelState {
  location : usize,
  references : Vec<usize>,
}

struct Environment<'l> {
  functions : &'l mut HashMap<RefStr, BytecodeFunction>,
  structs : &'l mut HashMap<RefStr, StructDef>,
  symbol_cache : &'l mut SymbolCache,

  /// function name
  function_name : RefStr,

  /// stores offset of each local variable in the stack frame
  locals : Vec<VarScope>,

  /// keeps track of labels
  labels : HashMap<RefStr, LabelState>,

  /// the maximum number of locals visible in any scope of the function
  max_locals : usize,

  instructions : Vec<BytecodeInstruction>,

  /// indicates how many nested loops we are inside in the currently-executing function
  loop_break_labels : Vec<RefStr>,
}

impl <'l> Environment<'l> {
  fn new(
    function_name : RefStr,
    functions : &'l mut HashMap<RefStr, BytecodeFunction>,
    structs : &'l mut HashMap<RefStr, StructDef>,
    symbol_cache : &'l mut SymbolCache,
  ) -> Environment<'l> {
    Environment{
      function_name, functions, structs, symbol_cache,
      locals: vec!(),
      labels: HashMap::new(),
      max_locals: 0,
      instructions: vec!(),
      loop_break_labels: vec!(),
    }
  }

  fn complete(mut self) {
    // Fix the jump locations
    for (_, label) in self.labels {
      for r in label.references {
        let instr = match &self.instructions[r] {
          BC::Jump(_) => BC::Jump(label.location),
          BC::JumpIfFalse(_) => BC::JumpIfFalse(label.location),
          i => panic!("expected label and found {:?}", i),
        };
        self.instructions[r] = instr;
      }
    }
    let function = BytecodeFunction { instructions: self.instructions, locals: self.max_locals };
    self.functions.insert(self.function_name, function);
  }

  fn emit(&mut self, instruction : BytecodeInstruction, do_emit : bool) {
    if do_emit {
      self.instructions.push(instruction);
    }
  }

  fn emit_always(&mut self, instruction : BytecodeInstruction) {
    self.instructions.push(instruction);
  }

  fn emit_label(&mut self, label : RefStr) {
    let location = self.instructions.len();
    let current_location = &mut self.labels.get_mut(&label).unwrap().location;
    if *current_location != usize::MAX {
      panic!("label used twice in compiler");
    }
    *current_location = location;
  }

  fn emit_jump(&mut self, label : &str) {
    let location = self.instructions.len();
    self.labels.get_mut(label).unwrap().references.push(location);
    self.emit_always(BC::Jump(usize::MAX))
  }

  fn emit_jump_if_false(&mut self, label : &str) {
    let location = self.instructions.len();
    self.labels.get_mut(label).unwrap().references.push(location);
    self.emit_always(BC::JumpIfFalse(usize::MAX))
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

  fn count_locals(&self) -> usize {
    if self.locals.len() == 0 {
      0
    }
    else {
      let vs = &self.locals[self.locals.len()-1];
      vs.base_index + vs.vars.len()
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

*/

fn compile_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment, push_answer : bool) -> Result<(), String> {

  // fn symbol_unwrap(e : &Expr) -> Result<&RefStr, String> {
  //   if let Expr::Symbol(s) = e {
  //     Ok(s)
  //   }
  //   else {
  //     Err(format!("expected a symbol, found {:?}", e))
  //   }
  // }
  // fn symbol_to_refstr(e : &Expr) -> Result<RefStr, String> {
  //   symbol_unwrap(e).map(|s| s.clone())
  // }

  fn does_not_push(instr : &str, push_answer : bool) -> Result<(), String> {
    if push_answer {
      Err(format!("instruction '{}' is void, where a result is expected", instr))
    }
    else {
      Ok(())
    }
  }

  match (instr, args.as_slice()) {
    ("call", exprs) => {
      let symbol = match &exprs[0] {
        Expr::Symbol(s) => s,
        _ => return Err(format!("expected symbol")),
      };
      let params = &exprs[1..];
      if BYTECODE_OPERATORS.contains(symbol.as_ref()) {
        match params {
          [a, b] => {
            compile(a, env, push_answer)?;
            compile(b, env, push_answer)?;
            env.emit(BC::BinaryOperator(symbol.clone()), push_answer);
          }
          [v] => {
            compile(v, env, push_answer)?;
            env.emit(BC::UnaryOperator(symbol.clone()), push_answer);
          }
          _ => {
            return Err(format!("wrong number of arguments for operator"));
          }
        }
      }
      else {
        // TODO: compile_function_call(symbol, params, env);
        return Err(format!("user-defined functions not yet implemented"));
      }
    }
    ("block", exprs) => {
      let v = VarScope { base_index: env.count_locals(), vars: vec!() };
      env.locals.push(v);
      let num_exprs = exprs.len();
      if num_exprs > 1 {
        for i in 0..(num_exprs-1) {
          compile(&exprs[i], env, false)?;
        }
      }
      compile(&exprs[num_exprs-1], env, push_answer)?;
      let new_local_count = env.count_locals();
      if new_local_count > env.max_locals {
        env.max_locals = new_local_count;
      }
      env.locals.pop();
    }
    ("let", exprs) => {
      does_not_push(instr, push_answer)?;
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      compile(&exprs[1], env, true)?;
      let offset = env.count_locals();
      env.locals.last_mut().unwrap().vars.push(name.clone());
      env.emit_always(BC::SetVar(offset));
    }
    ("=", [Expr::Symbol(var_symbol), value_expr]) => {
      does_not_push(instr, push_answer)?;
      compile(&value_expr, env, true)?; // emit value
      let offset = env.find_var_offset(var_symbol)?;
      env.emit_always(BC::SetVar(offset));
    }
    // ("=", [Expr::Expr { symbol, args }, value_expr]) => {
    //   match (symbol.as_str(), args.as_slice()) {
    //     ("index", [array_expr, index_expr]) => {
    //       let v = compile(&value_expr, env)?;
    //       let array_rc = to_array(array_expr, env)?;
    //       let mut array = array_rc.borrow_mut();
    //       let f = to_f(index_expr, env)?;
    //       let i = array_index(&array, f)?;
    //       array[i] = v;
    //       Ok(Value::Unit)
    //     }
    //     (".", [struct_expr, field_expr]) => {
    //       let v = compile(&value_expr, env)?;
    //       let structure = to_struct(struct_expr, env)?;
    //       let field_name : &str = symbol_unwrap(field_expr)?;
    //       structure.borrow().fields.get(field_name)
    //         .ok_or_else(||format!("field {} does not exist on struct {:?}.", field_name, structure))?;
    //       *structure.borrow_mut().fields.get_mut(field_name).unwrap() = v;
    //       Ok(Value::Unit)
    //     }
    //     _ => Err(format!("can't assign to {:?}", (symbol, args))),
    //   }
    // }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return Err(format!("malformed if expression"));
      }
      let false_label = env.label("if_false_label");
      if arg_count == 3 {
        // has else branch
        let else_end_label = env.label("else_end_label");
        compile(&exprs[0], env, true)?;
        env.emit_jump_if_false(&false_label);
        compile(&exprs[1], env, push_answer)?;
        env.emit_jump(&else_end_label);
        env.emit_label(false_label);
        compile(&exprs[2], env, push_answer)?;
        env.emit_label(else_end_label);
      }
      else {
        // has no else branch
        does_not_push(instr, push_answer)?;
        compile(&exprs[0], env, true)?;
        env.emit_jump_if_false(&false_label);
        compile(&exprs[1], env, false)?;
        env.emit_label(false_label);
      }
    }
    // ("struct_define", exprs) => {
    //   if exprs.len() < 1 {
    //     return Err(format!("malformed struct definition"));
    //   }
    //   let struct_name = symbol_to_refstr(&exprs[0])?;
    //   if env.structs.contains_key(&struct_name) {
    //     return Err(format!("A struct called {} has already been defined.", struct_name));
    //   }
    //   let field_names =
    //     exprs[1..].iter().map(symbol_to_refstr)
    //     .collect::<Result<HashSet<RefStr>, String>>()?;
    //   env.structs.insert(struct_name, field_names);
    //   Ok(Value::Unit)
    // }
    // ("struct_instantiate", exprs) => {
    //   if exprs.len() < 1 || exprs.len() % 2 == 0 {
    //     return Err(format!("malformed struct instantiation {:?}", exprs));
    //   }
    //   let name = symbol_to_refstr(&exprs[0])?;
    //   {
    //     let struct_def =
    //       env.structs.get(name.as_str())
    //       .ok_or_else(|| format!("struct {} does not exist", name))?;
    //     for i in (1..exprs.len()).step_by(2) {
    //       let field_name = symbol_unwrap(&exprs[i])?;
    //       struct_def.get(field_name)
    //         .ok_or_else(|| format!("unexpected field '{}'", field_name))?;
    //     }
    //   };
    //   let mut fields = HashMap::new();
    //   for i in (1..exprs.len()).step_by(2) {
    //     let field_name = symbol_to_refstr(&exprs[i])?;
    //     let field_value = compile(&exprs[i+1], env)?;
    //     fields.insert(field_name, field_value);
    //   }
    //   let s = Rc::new(RefCell::new(Struct { name, fields }));
    //   Ok(Value::Struct(s))
    // }
    // (".", [expr, field_name]) => {
    //   let s = to_struct(expr, env)?;
    //   let name = symbol_unwrap(field_name)?;
    //   let v =
    //     s.borrow().fields.get(name)
    //     .ok_or_else(||format!("field {} does not exist on struct {:?}.", name, s))?
    //     .clone();
    //   Ok(v)
    // }
    ("while", exprs) => {
      does_not_push(instr, push_answer)?;
      if exprs.len() != 2 {
        return Err(format!("malformed while block"));
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
    // ("fun", exprs) => {
    //   let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
    //   let args_exprs = match &exprs[1] { Expr::Expr{ args, .. } => args, _ => { return Err(format!("expected an expression")); }};
    //   let function_body = Rc::new(exprs[2].clone());
    //   let mut args = vec!();
    //   for e in args_exprs {
    //     if let Expr::Symbol(s) = e {
    //       args.push(s.clone());
    //     }
    //     else {
    //       return Err(format!("expected a symbol"));
    //     }
    //   }
    //   scoped_insert(&mut env.functions, name.clone(), FunctionDef { args, expr: function_body });
    //   Ok(Value::Unit)
    // }
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
        return Err(format!("index instruction expected 2 arguments. Found {}.", exprs.len()));
      }
    }
    _ => {
      return Err(format!("instruction '{}' with args {:?} is not supported by the interpreter.", instr, args));
    }
  }
  Ok(())
}


fn compile(ast : &Expr, env : &mut Environment, push_answer : bool) -> Result<(), String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      compile_instr(symbol, args, env, push_answer)?;
    }
    Expr::Symbol(s) => {
      if s.as_str() == "break" {
        if let Some(l) = env.loop_break_labels.last().map(|s| s.clone()) {
          env.emit_jump(l.as_str());
        }
        else {
          return Err(format!("can't break outside a loop"));
        }
      }
      else {
        let offset = env.find_var_offset(s)?;
        env.emit(BC::PushVar(offset), push_answer);
      }
    }
    Expr::LiteralFloat(f) => {
      let v = Value::Float(*f);
      env.emit(BC::Push(v), push_answer);
    }
    Expr::LiteralBool(b) => {
      let v = Value::Bool(*b);
      env.emit(BC::Push(v), push_answer);
    }
  }
  Ok(())
}

fn compile_bytecode(ast : &Expr, entry_function_name : RefStr, symbol_cache : &mut SymbolCache) -> Result<BytecodeProgram, String> {
  let mut functions = HashMap::new();
  let mut structs = HashMap::new();
  {
    let mut env = Environment::new(entry_function_name, &mut functions, &mut structs, symbol_cache);
    compile(ast, &mut env, true)?;
    env.complete();
  }
  Ok(BytecodeProgram { functions })
}

fn to_f(v : Value) -> Result<f32, String> {
  match v {
    Value::Float(f) => Ok(f),
    x => Err(format!("Expected float, found {:?}.", x))
  }
}
fn to_b(v : Value) -> Result<bool, String> {
  match v {
    Value::Bool(b) => Ok(b),
    x => Err(format!("Expected boolean, found {:?}.", x))
  }
}
fn to_array(v : Value) -> Result<Array, String> {
  match v {
    Value::Array(a) => Ok(a),
    x => Err(format!("Expected array, found {:?}.", x))
  }
}
fn to_struct(v : Value) -> Result<StructVal, String> {
  match v {
    Value::Struct(s) => Ok(s),
    x => Err(format!("Expected struct, found {:?}.", x))
  }
}
fn f_to_val(f : f32) -> Value {
  Value::Float(f)
}
fn b_to_val(b : bool) -> Value {
  Value::Bool(b)
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

fn interpret_bytecode(program : &BytecodeProgram, entry_function : RefStr) -> Result<Value, String> {
  let mut stack : Vec<Value> = vec![];
  let function =
    program.functions.get(&entry_function).ok_or_else(|| format!("No function found"))?;
  let mut vars = vec!(Value::Unit; function.locals);
  let mut program_counter = 0;
  loop {
    if program_counter >= function.instructions.len() {
      println!("vars: {:?}, stack: {:?}", vars, stack);
      return Err(format!("program counter out of bounds"));
    }
    println!("vars: {:?}, stack: {:?}", vars, stack);
    println!("PC: {}, instruction: {:?}", program_counter, &function.instructions[program_counter]);    
    match &function.instructions[program_counter] {
      BC::Push(value) => {
        stack.push(value.clone());
      }
      BC::Pop => {
        stack.pop();
      }
      BC::PushVar(var_slot) => {
        let v = vars[*var_slot].clone();
        stack.push(v);
      }
      BC::Dup => {
        let v = stack.last().unwrap().clone();
        stack.push(v);
      }
      BC::NewArray(elements) => {
        let mut a = vec!(Value::Unit ; *elements);
        for i in (0..*elements).rev() {
          a[i] = stack.pop().unwrap();
        }
        let array = Rc::new(RefCell::new(a));
        stack.push(Value::Array(array));
      }
      BC::ArrayIndex => {
        let float_index = to_f(stack.pop().unwrap())?;
        let a = to_array(stack.pop().unwrap())?;
        let a = a.borrow();
        let i = array_index(&a, float_index)?;
        stack.push(a[i].clone());
      }
      BC::SetVar(var_slot) => {
        let v = stack.pop().unwrap();
        vars[*var_slot] = v;
      }
      BC::JumpIfFalse(location) => {
        if !to_b(stack.pop().unwrap())? {
          program_counter = *location;
          continue;
        }
      }
      BC::Jump(location) => {
        program_counter = *location;
        continue;
      }
      BC::BinaryOperator(operator) => {
        let b = stack.pop().unwrap();
        let a = stack.pop().unwrap();
        let v = match operator.as_ref() {
          "+" => Value::Float(to_f(a)? + to_f(b)?),
          "-" => Value::Float(to_f(a)? - to_f(b)?),
          "*" => Value::Float(to_f(a)? * to_f(b)?),
          "/" => Value::Float(to_f(a)? / to_f(b)?),
          ">" => Value::Bool(to_f(a)? > to_f(b)?),
          "<" => Value::Bool(to_f(a)? < to_f(b)?),
          "<=" => Value::Bool(to_f(a)? <= to_f(b)?),
          ">=" => Value::Bool(to_f(a)? >= to_f(b)?),
          "==" => Value::Bool(a == b),
          "&&" => Value::Bool(to_b(a)? && to_b(b)?),
          "||" => Value::Bool(to_b(a)? || to_b(b)?),
          op => return Err(format!("unsupported binary operator {}", op)),
        };
        stack.push(v);
      }
      BC::UnaryOperator(operator) => {
        let a = stack.pop().unwrap();
        let v = match operator.as_ref() {
          "-" => Value::Float(-to_f(a)?),
          op => return Err(format!("unsupported unary operator {}", op)),
        };
        stack.push(v);
      }
      i => return Err(format!("instruction '{:?}' not yet implemented.", i)),
    }
    program_counter += 1;
  }
  return Ok(Value::Unit);
}

pub fn interpret(ast : &Expr) -> Result<Value, String> {
  let mut symbol_cache = SymbolCache::new();
  let entry_function_name = symbol_cache.symbol("main");
  let program = compile_bytecode(ast, entry_function_name.clone(), &mut symbol_cache)?;
  for (name, f) in program.functions.iter() {
    println!("--------------------------------");
    println!("Function '{}':", name);
    for (i, instr) in f.instructions.iter().enumerate() {
      println!("{}:   {:?}", i, instr);
    }
    println!();
    println!("Max local variables: {}", f.locals);
    println!();
  }
  interpret_bytecode(&program, entry_function_name)?;
  Err(format!("interpreter doesn't work"))
}
