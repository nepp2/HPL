
use crate::interpret::{interpreter, Interpreter};
use crate::error::{Error, ErrorContent};
use crate::compiler::Val;
use crate::parser::EXPECTED_TOKEN_ERROR;

use rustyline::Editor;

pub enum ReplResult {
  Complete(Val),
  Incomplete,
  Failed(Error),
}

use ReplResult::*;

fn repl_eval(i : &mut Interpreter, code : &str) -> ReplResult {
  match i.eval(code) {
    Ok(e) => {
      return Complete(e);
    }
    Err(e) => {
      if let ErrorContent::Message(m) = &e.message {
        if m.as_str() == EXPECTED_TOKEN_ERROR {
          return Incomplete;
        }
      }
      return Failed(e);
    }
  }
}

pub fn run_repl() {
  let mut rl = Editor::<()>::new();
  let mut i = interpreter();

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      match repl_eval(&mut i, input_line.as_str()) {
        Complete(val) => {
          rl.add_history_entry(input_line);
          println!("{:?}", val);
          break;
        }
        Incomplete => {
          // get more tokens
          let next_line = rl.readline(". ").unwrap();
          input_line.push_str("\n");
          input_line.push_str(next_line.as_str());
        }
        Failed(e) => {
          rl.add_history_entry(input_line);
          println!("Error occured: {}", e.display());
          break;
        }
      }
    }
  }
}
