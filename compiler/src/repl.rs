
use crate::lexer;
use crate::parser;
use crate::parser::ReplParseResult::{Complete, Incomplete};
use crate::jit::interpreter;

use rustyline::Editor;

pub fn run_repl() {
  let mut rl = Editor::<()>::new();
  let mut i = interpreter();

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut i.cache)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut i.cache);
      match parsing_result {
        Ok(Complete(e)) => {
          // we have parsed a full expression
          rl.add_history_entry(input_line);
          match i.run_expression(&e) {
            Ok(value) => {
              println!("{:?}", value)
            }
            Err(err) => {
              println!("error: {}", err);
            }
          }
          break;
        }
        Ok(Incomplete) => {
          // get more tokens
          let next_line = rl.readline(". ").unwrap();
          input_line.push_str("\n");
          input_line.push_str(next_line.as_str());
        }
        Err(e) => {
          rl.add_history_entry(input_line);
          println!("Error occured: {}", e);
          break;
        }
      }
    }
  }
}
