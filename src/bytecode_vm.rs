
use error::{Error, error_no_loc};
use value::*;
use intrinsics::IntrinsicDef;
use bytecode_compile::*;

use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::usize;
use std::iter;

use bytecode_compile::BytecodeInstruction as BC;

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
fn struct_field_index(def : &StructDef, field_name : &str) -> Result<usize, Error> {
  def.fields.iter().position(|s| s.as_ref() == field_name)
  .ok_or_else(||error_no_loc(format!("field {} does not exist on struct '{:?}'.", field_name, def)))
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

struct Call {
  function_handle : usize,

  /// Absolute position of the start of the locals (including any vars) in the main stack.
  stack_base : usize,

  /// Number of locals (including vars)
  locals : usize,

  /// Relative to the end of the locals. It's an index into the stack slice.
  stack_head : usize,

  /// Next instruction to be executed
  program_counter : usize,
}

impl Call {
  fn absolute_stack_size(&self) -> usize {
    self.stack_base + self.locals + self.stack_head
  }
}

fn new_function_call(function_handle : usize, stack_size : usize, info : &Vec<FunctionInfo>) -> Call{
  /*
    It's assumed at this point that any arguments passed to the function are neatly
    lined up on the stack. They will become the lower part of the new call's local
    variable space.
  */
  let info = &info[function_handle];
  Call {
    function_handle,
    stack_base: stack_size - info.arguments.len(),
    locals: info.locals,
    stack_head: 0,
    program_counter: 0,
  }
}

fn intrinsic_call(stack : &mut [Value], c : &mut Call, info : &IntrinsicDef) {
  // It's assumed at this point that any arguments passed to the function are neatly lined up on the stack
  let args = info.signature.args.len();
  let len = c.stack_head;
  let result = {
    let arg_slice = &stack[(len-args)..len];
    (info.fn_ref)(arg_slice)
  };
  push(stack, c, result);
}

fn pop(stack : &mut [Value], c : &mut Call) -> Value {
  c.stack_head -= 1;
  stack[c.stack_head].clone()
}

fn push(stack : &mut [Value], c : &mut Call, v : Value) {
  stack[c.stack_head] = v;
  c.stack_head += 1;
}

fn set_return_value(stack : &mut [Value], v : Value) {
  stack[0] = v;
}

fn interpret_bytecode(program : &BytecodeProgram, entry_function : usize) -> Result<Value, Error> {
  // TODO: refcounted pointer bug with uncleared stack entries
  let mut expandable_stack : Vec<Value> = vec![];
  let mut callstack : Vec<Call> = vec![];
  let mut c = new_function_call(entry_function, expandable_stack.len(), &program.function_info);
  loop {
    let instructions = &program.bytecode[c.function_handle];
    let (vars, stack) = {
      let min_stack = c.stack_base + c.locals + 100;
      // expand the stack if needed
      if expandable_stack.len() < min_stack {
        let extend_size = (min_stack - expandable_stack.len()) + 200;
        let it = iter::repeat(Value::Unit).take(extend_size);
        expandable_stack.extend(it);
      }
      expandable_stack[c.stack_base..].split_at_mut(c.locals)
    };
    loop {
      /*
      println!("vars: {:?}", vars);
      println!("stack: {:?}", &stack[..c.stack_head]);
      println!();
      println!(
        "Function: {}, PC: {}, instruction: {:?}", program.function_info[c.function_handle].name,
        c.program_counter, &instructions[c.program_counter]);
      */
      match &instructions[c.program_counter] {
        BC::Return => {
          let return_value = pop(stack, &mut c);
          if callstack.len() == 0 {
            return Ok(return_value);
          }
          set_return_value(stack, return_value);
          c = callstack.pop().unwrap();
          c.stack_head += 1; // accommodate newly returned value
          c.program_counter += 1; // move past the call instruction
          break;
        }
        BC::Push(value) => {
          push(stack, &mut c, value.clone());
        }
        BC::Pop => {
          pop(stack, &mut c);
        }
        BC::PushVar(var_slot) => {
          let v = vars[*var_slot].clone();
          push(stack, &mut c, v);
        }
        BC::NewArray(elements) => {
          let mut a = vec!(Value::Unit ; *elements);
          for i in (0..*elements).rev() {
            a[i] = pop(stack, &mut c);
          }
          let array = Rc::new(RefCell::new(a));
          push(stack, &mut c, Value::Array(array));
        }
        BC::ArrayIndex => {
          let float_index = to_f(pop(stack, &mut c))?;
          let a = to_array(pop(stack, &mut c))?;
          let a = a.borrow();
          let i = array_index(&a, float_index)?;
          push(stack, &mut c, a[i].clone());
        }
        BC::SetArrayIndex => {
          let v = pop(stack, &mut c);
          let f_index = to_f(pop(stack, &mut c))?;
          let a = to_array(pop(stack, &mut c))?;
          let mut array = a.borrow_mut();
          let i = array_index(&array, f_index)?;
          array[i] = v;
        }
        BC::NewStruct(def) => {
          let fields = vec![Value::Unit ; def.fields.len()];
          let s = Rc::new(RefCell::new(Struct { def: def.clone(), fields }));
          push(stack, &mut c, Value::Struct(s));
        }
        BC::StructFieldInit(index) => {
          let v = pop(stack, &mut c);
          let s = to_struct(&stack[c.stack_head-1])?;
          s.borrow_mut().fields[*index] = v;
        }
        BC::PushStructField(name) => {
          let s = pop(stack, &mut c);
          let s = to_struct(&s)?;
          let index = struct_field_index(&s.borrow().def, name)?;
          let v = s.borrow().fields[index].clone();
          push(stack, &mut c, v);
        }
        BC::SetStructField(name) => {
          let v = pop(stack, &mut c);
          let s = pop(stack, &mut c);
          let s = to_struct(&s)?;
          let index = struct_field_index(&s.borrow().def, name)?;
          s.borrow_mut().fields[index] = v;
        }
        BC::SetVar(var_slot) => {
          let v = pop(stack, &mut c);
          vars[*var_slot] = v;
        }
        BC::CallFunction(function_type, handle) => {
          // TODO: code duplicated in CallFirstClassFunction
          match function_type {
            FunctionType::Function => {
              let stack_size = c.absolute_stack_size();
              callstack.push(c);
              c = new_function_call(*handle, stack_size, &program.function_info);
              break;
            }
            FunctionType::Intrinsic => {
              let info = &program.intrinsic_info[*handle];
              intrinsic_call(stack, &mut c, info);
            }
          }
        }
        BC::CallFirstClassFunction => {
          let (function_type, handle) = to_function(pop(stack, &mut c))?;
          // TODO: code duplicated in CallFunction
          match function_type {
            FunctionType::Function => {
              let stack_size = c.absolute_stack_size();
              callstack.push(c);
              c = new_function_call(handle, stack_size, &program.function_info);
              break;
            }
            FunctionType::Intrinsic => {
              let info = &program.intrinsic_info[handle];
              intrinsic_call(stack, &mut c, info);
            }
          }
        }
        BC::JumpIfFalse(location) => {
          if !to_b(pop(stack, &mut c))? {
            c.program_counter = *location;
            continue;
          }
        }
        BC::Jump(location) => {
          c.program_counter = *location;
          continue;
        }
        BC::BinaryOperator(operator) => {
          let b = pop(stack, &mut c);
          let a = pop(stack, &mut c);
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
            op => return Err(error_no_loc(format!("unsupported binary operator {}", op))),
          };
          push(stack, &mut c, v);
        }
        BC::UnaryOperator(operator) => {
          let a = pop(stack, &mut c);
          let v = match operator.as_ref() {
            "-" => Value::Float(-to_f(a)?),
            "!" => Value::Bool(!to_b(a)?),
            op => return Err(error_no_loc(format!("unsupported unary operator {}", op))),
          };
          push(stack, &mut c, v);
        }
        // TODO remove: i => return error("instruction '{:?}' not yet implemented.", i)),
      }
      c.program_counter += 1;
    }
  }
}

pub fn print_program(program : &BytecodeProgram) {
  for (info, bytecode) in program.function_info.iter().zip(program.bytecode.iter()) {
    println!("--------------------------------");
    println!("Function '{}':", info.name);
    for (i, instr) in bytecode.iter().enumerate() {
      println!("{}:   {:?}", i, instr);
    }
    println!();
    println!("Max local variables: {}", info.locals);
    println!();
  }
}

pub fn interpret(expr : &Expr, symbol_cache : &mut SymbolCache, intrinsics : &HashMap<RefStr, IntrinsicDef>) -> Result<Value, Error> {
  let entry_function_name = symbol_cache.symbol("main");
  let program = compile_bytecode(expr, entry_function_name.clone(), symbol_cache, intrinsics)?;
  print_program(&program);
  let entry_function_handle = program.function_info.iter().position(|i| i.name == entry_function_name).unwrap();
  interpret_bytecode(&program, entry_function_handle)
}
