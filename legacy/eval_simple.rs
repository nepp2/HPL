
use crate::lexer;
use crate::parser;
use crate::parser::NO_TYPE;
use crate::value::*;
use crate::error::{Error, ErrorContent, error, error_raw};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use std::cell::RefCell;
use std::fmt;
use itertools::Itertools;
use std::mem;
use std::sync::atomic::{AtomicBool, Ordering};
use std::fs::File;
use std::io::Read;

#[derive(PartialEq)]
pub enum ExitState {
  NotExiting,
  Breaking,
  Returning,
}

type Ptr = u64;
type Symbol = u64;

enum MapVal {
  U64(u64), Map(Map), Block(Vec<u8>)
}
type Map = HashMap<Symbol, MapVal>;

#[derive(Default)]
pub struct SymbolTable {
  symbol_map : HashMap<RefStr, Symbol>,
  symbols : Vec<RefStr>,
}

impl SymbolTable {
  fn get(&mut self, s : impl Into<RefStr>) -> Symbol {
    panic!()
  }
}

fn homoiconise(expr : &Expr, st : &mut SymbolTable) -> Map {
  use self::MapVal::*;
  let tag = st.get("tag");
  match &expr.tag {
    ExprTag::Tree(_) => {
      hashmap!(tag => U64(st.get("tree")))
    }
    ExprTag::Symbol(s) => {
      let symbol = st.get("symbol");
      hashmap!(
        tag => U64(symbol),
        symbol => U64(st.get(s.clone())),
      )
    }
    ExprTag::LiteralString(s) => {
      let string = st.get("string");
      hashmap!(
        tag => U64(string),
        string => U64(st.get(s.clone())),
      )
    }
    ExprTag::LiteralFloat(f) => {
      let float = st.get("float");
      hashmap!(
        tag => U64(float),
        float => U64(f.to_bits() as u64),
      )
    }
    ExprTag::LiteralBool(b) => {
      let bool = st.get("bool");
      hashmap!(
        tag => U64(bool),
        bool => U64(if *b { 1 } else { 0 }),
      )
    }
    ExprTag::LiteralUnit => {
      let unit = st.get("unit");
      hashmap!(tag => U64(unit))
    }
  }
}

fn eval(expr : &Expr) {
  
}


pub struct Interpreter {
  pub mem_counter : Ptr,
  pub mem : HashMap<Ptr, Vec<u8>>,
  pub st : SymbolTable,
  pub interrupt_flag : Arc<AtomicBool>,

  /// indicates how many nested loops we are inside in the currently-executing function
  pub loop_depth : i32,

  /// indicates whether the program is currently breaking out of a loop
  /// or returning from the function
  pub exit_state : ExitState,
}

impl Interpreter {

  pub fn new(interrupt_flag : Arc<AtomicBool>) -> Interpreter {
    Interpreter{
      mem_counter: 0,
      mem: Default::default(),
      st: Default::default(),
      interrupt_flag,
      loop_depth: 0,
      exit_state: ExitState::NotExiting,
    }
  }

  fn malloc(&mut self, bytes : u64) -> Ptr {
    let ptr = self.mem_counter;
    self.mem_counter += 1;
    let allocation : Vec<u8> = vec![0; bytes as usize];
    self.mem.insert(ptr, allocation);
    ptr
  }

  fn free(&mut self, ptr : Ptr) {
    self.mem.remove(&ptr);
  }

  fn check_interrupt(&self) -> Result<(), String> {
    if self.interrupt_flag.load(Ordering::Relaxed) {
      Err(format!("Interpreter received interrupt"))
    }
    else {
      Ok(())
    }
  }

  fn dereference_variable(&mut self, env : Ptr, name : &str) -> Result<Value, ErrorContent> {
    let sym =
      self.st.symbol_map.get(name)
      .ok_or_else(|| format!("symbol not defined"))?;
    let env =
      self.mem.get(&env)
      .ok_or_else(|| format!("invalid pointer dereferenced"))?;


    panic!();
  }

  pub fn interpret(&mut self, code : &str) -> Result<(), Error> {
    panic!()
  }

  pub fn eval2(&mut self, expr : &Expr, env : Ptr, ret : &mut[u8]) -> Result<(), Error> {
    if self.exit_state != ExitState::NotExiting {
      // this skips all evaluations until we backtrack to something
      // that stops the exit state, such as a loop or function call
      return Ok(());
    }
    match &expr.tag {

    }
    Ok(())
  }

  pub fn eval(&mut self, expr : &Expr, env : Ptr) -> Result<Value, Error> {
    if self.exit_state != ExitState::NotExiting {
      // this skips all evaluations until we backtrack to something
      // that stops the exit state, such as a loop or function call
      return Ok(UNIT);
    }
    match &expr.tag {
      ExprTag::Tree(_) => {
        panic!()
      }
      ExprTag::Symbol(s) => {
        if s.as_ref() == "break" {
          if self.loop_depth > 0 {
            self.exit_state = ExitState::Breaking;
            Ok(UNIT)
          }
          else {
            error(expr, format!("can't break outside a loop"))
          }
        }
        else {
          let ptr = self.dereference_variable(env, &s).map_err(|c| error_raw(expr, c))?;
          Ok(ptr)
        }
      }
      ExprTag::LiteralString(s) => panic!(),
      ExprTag::LiteralFloat(f) => Ok(value(FLOAT_TAG, f.to_bits() as u64)),
      ExprTag::LiteralBool(b) => Ok(if *b { TRUE } else { FALSE }),
      ExprTag::LiteralUnit => Ok(UNIT),
    }
  }

}
