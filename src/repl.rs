
use rustyline::error::ReadlineError;
use rustyline::Editor;

use error::{Error, TextLocation};
use lexer;
use parser;
use bytecode_vm;
use value::Value;

fn interpret(text : &str) -> Result<Value, Error> {
  match lexer::lex(text) {
    Ok(tokens) => {
      let ast = parser::parse(tokens)?;
      let value = bytecode_vm::interpret(&ast)?;
      Ok(value)
    }
    Err(errors) => {
      error_result!("{:?}", errors)
    }
  }
}

pub fn repl() {
  // `()` can be used when no completer is required
  let mut rl = Editor::<()>::new();
  /* TODO
  if rl.load_history(".mal-history").is_err() {
      println!("No previous history.");
  }
  */

  loop {
    let readline = rl.readline("repl> ");
    match readline {
      Ok(line) => {
        rl.add_history_entry(&line);
        // TODO rl.save_history(".mal-history").unwrap();
        if line.len() > 0 {
          match interpret(&line) {
            Ok(v) => {
              println!("{:?}", v);
            }
            Err(s) => {
              println!("{:?}", s);
            }
          }
        }
      },
      Err(ReadlineError::Interrupted) => continue,
      Err(ReadlineError::Eof) => break,
      Err(err) => {
        println!("Error: {:?}", err);
        break
      }
    }
  }
}
