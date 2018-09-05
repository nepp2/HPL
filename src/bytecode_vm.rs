
use parser::Expr;
use lexer::{RefStr, AsStr, SymbolCache};
use interpreter::{Value, Struct, Array, StructVal};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;
use std::usize;

type FunctionHandle = usize;

#[derive(Debug)]
enum BytecodeInstruction {
  Push(Value),
  PushVar(usize),
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
  loop_depth : i32,
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
      loop_depth: 0,
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

  fn emit(&mut self, instruction : BytecodeInstruction) {
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
    self.emit(BC::Jump(usize::MAX))
  }

  fn emit_jump_if_false(&mut self, label : &str) {
    let location = self.instructions.len();
    self.labels.get_mut(label).unwrap().references.push(location);
    self.emit(BC::JumpIfFalse(usize::MAX))
  }

  fn label(&mut self, s : String) -> RefStr {
    if self.labels.contains_key(s.as_str()) {
      panic!("duplicate label used in compiler");
    }
    let label = self.symbol_cache.symbol(s);
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

fn compile_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment) -> Result<(), String> {

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

  // fn array_index(array : &Vec<Value>, index : f32) -> Result<usize, String> {
  //   let i = index as usize;
  //   if index >= 0.0 && i < array.len() {
  //     Ok(i)
  //   }
  //   else {
  //     Err(format!("Index out of bounds error. Array of {} elements given index {}.", array.len(), index))
  //   }
  // }

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
            compile(a, env)?;
            compile(b, env)?;
            env.emit(BC::BinaryOperator(symbol.clone()));
          }
          [v] => {
            compile(v, env)?;
            env.emit(BC::UnaryOperator(symbol.clone()));
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
      for e in exprs {
        compile(e, env)?;
      }
      let new_local_count = env.count_locals();
      if new_local_count > env.max_locals {
        env.max_locals = new_local_count;
      }
      env.locals.pop();
    }
    ("let", exprs) => {
      let name = match &exprs[0] { Expr::Symbol(s) => s, _ => { return Err(format!("expected a symbol")); }};
      compile(&exprs[1], env)?;
      let offset = env.count_locals();
      env.locals.last_mut().unwrap().vars.push(name.clone());
      env.emit(BC::SetVar(offset));
    }
    ("=", [Expr::Symbol(var_symbol), value_expr]) => {
      compile(&value_expr, env)?; // emit value
      let offset = env.find_var_offset(var_symbol)?;
      env.emit(BC::SetVar(offset));
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
    // ("if", exprs) => {
    //   let arg_count = exprs.len();
    //   if arg_count < 2 || arg_count > 3 {
    //     return Err(format!("malformed if expression"));
    //   }
    //   let condition = to_b(&exprs[0], env)?;
    //   if condition {
    //     compile(&exprs[1], env)
    //   }
    //   else if arg_count == 3 {
    //     compile(&exprs[2], env)
    //   }
    //   else {
    //     Ok(Value::Unit)
    //   }
    // }
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
      if exprs.len() != 2 {
        return Err(format!("malformed while block"));
      }
      env.loop_depth += 1;
      let id = env.loop_depth;
      let condition_label = env.label(format!("loop_condition_{}", id));
      let end_label = env.label(format!("loop_end_{}", id));
      env.emit_label(condition_label.clone());
      compile(&exprs[0], env)?; // emit condition
      env.emit_jump_if_false(&end_label); // exit loop if condition fails
      compile(&exprs[1], env)?; // emit loop body
      env.emit_jump(&condition_label); // jump back to the condition
      env.emit_label(end_label);
      env.loop_depth -= 1;
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
    // ("literal_array", exprs) => {
    //   let mut array_contents = Rc::new(RefCell::new(vec!()));
    //   for e in exprs {
    //     let v = compile(e, env)?;
    //     array_contents.borrow_mut().push(v);
    //   }
    //   Ok(Value::Array(array_contents))
    // }
    // ("index", exprs) => {
    //   if let [array_expr, index_expr] = exprs {
    //     let array_rc = to_array(array_expr, env)?;
    //     let array = array_rc.borrow();
    //     let f = to_f(index_expr, env)?;
    //     let i = array_index(&array, f)?;
    //     Ok(array[i].clone())
    //   }
    //   else {
    //     Err(format!("index instruction expected 2 arguments. Found {}.", exprs.len()))
    //   }
    // }
    _ => {
      return Err(format!("instruction '{}' with args {:?} is not supported by the interpreter.", instr, args));
    }
  }
  Ok(())
}


fn compile(ast : &Expr, env : &mut Environment) -> Result<(), String> {
  match ast {
    Expr::Expr{ symbol, args } => {
      compile_instr(symbol, args, env)?;
      //return Err(format!("exprs are not implemented"));
    }
    Expr::Symbol(s) => {
      if s.as_str() == "break" {
        if env.loop_depth > 0 {
          let l = format!("loop_end_{}", env.loop_depth);
          env.emit_jump(l.as_str());
        }
        else {
          return Err(format!("can't break outside a loop"));
        }
      }
      else {
        let offset = env.find_var_offset(s)?;
        env.emit(BC::PushVar(offset));
      }
    }
    Expr::LiteralFloat(f) => {
      let v = Value::Float(*f);
      env.emit(BC::Push(v));
    }
    Expr::LiteralBool(b) => {
      let v = Value::Bool(*b);
      env.emit(BC::Push(v));
    }
  }
  Ok(())
}

fn compile_bytecode(ast : &Expr, entry_function_name : RefStr, symbol_cache : &mut SymbolCache) -> Result<BytecodeProgram, String> {
  let mut functions = HashMap::new();
  let mut structs = HashMap::new();
  {
    let mut env = Environment::new(entry_function_name, &mut functions, &mut structs, symbol_cache);
    compile(ast, &mut env)?;
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

fn interpret_bytecode(program : &BytecodeProgram, entry_function : RefStr) -> Result<Value, String> {
  let function =
    program.functions.get(&entry_function).ok_or_else(|| format!("No function found"))?;

  let mut stack : Vec<Value> = vec![Value::Unit; function.locals];
  let mut program_counter = 0;
  loop {
    if program_counter >= function.instructions.len() {
      println!("--------------------------------");
      println!("Stack contents:");
      for (i, v) in stack.iter().enumerate() {
        println!("s{}:   {:?}", i, v);
      }
      println!();
      return Err(format!("program counter out of bounds"));
    }
    match &function.instructions[program_counter] {
      BC::Push(value) => {
        stack.push(value.clone());
      }
      BC::PushVar(var_slot) => {
        let v = stack[*var_slot].clone();
        stack.push(v);
      }
      BC::SetVar(var_slot) => {
        let v = stack.pop().unwrap();
        stack[*var_slot] = v;
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
