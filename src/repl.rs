
use crate::lexer;
use crate::parser;
use crate::parser::ReplParseResult::{Complete, Incomplete};
use crate::jit::Interpreter;

use rustyline::Editor;

use dlltest;

use llvm_sys::support::LLVMLoadLibraryPermanently;

#[no_mangle]
pub extern "C" fn blah(a : i64, b : i64) -> i64 {
  a + b
}

// Adding the functions above to a global array,
// so Rust compiler won't remove them.
#[used]
static EXTERNAL_FNS: [extern fn(i64, i64) -> i64; 1] = [blah];

pub fn run_repl() {
  dlltest::blahblah(4, 5);

  let mut rl = Editor::<()>::new();
  let mut i = Interpreter::new();

  unsafe {
    LLVMLoadLibraryPermanently(std::ptr::null());
  }

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut i.sym)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut i.sym);
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
          println!("Error occured: {}", e);
          break;
        }
      }
    }
  }
}
