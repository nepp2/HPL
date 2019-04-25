
/*

Modified from code released under the license below:

######################################################
Copyright (c) 2014 Jauhien Piatlicki

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

[Except as contained in this notice, the name of <copyright holders>
shall not be used in advertising or otherwise to promote the sale, use
or other dealings in this Software without prior written authorization
from Jauhien Piatlicki.]
######################################################

*/

/*
TODO:
  * Change to the Rust repl thingy I tried to use before

*/

use std::io;
use std::io::Write;

use rustyline::error::ReadlineError;
use rustyline::Editor;

use crate::value::{SymbolTable, display_expr};
use crate::lexer;
use crate::parser;
use crate::parser::ReplParseResult::{Complete, Incomplete};

pub fn run_repl() {
  let mut sym = SymbolTable::new();

  let mut rl = Editor::<()>::new();

  'main: loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    // the constructed AST
    let mut ast = Vec::new();
    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut sym)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          continue 'main;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut sym);
      match parsing_result {
        Ok(Complete(exprs)) => {
          ast.extend(exprs.into_iter());
          // we have parsed a full expression
          rl.add_history_entry(input_line);
          break;
        }
        Ok(Incomplete) => {
          // wait for more tokens
        }
        Err(e) => {
          println!("Error occured: {}", e);
          continue 'main;
        }
      }
      let next_line = rl.readline(". ").unwrap();
      input_line.push_str("\n");
      input_line.push_str(next_line.as_str());
    }

    for e in ast {
      println!("{}", display_expr(&e, &mut sym));
      continue;
    }
  }
}
