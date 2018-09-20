use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use error::Error;
use parser;
use lexer;
use value::{Value};
use bytecode_vm;
use typecheck;

fn interpret(code: &str) -> Result<Value, Error> {
  let tokens = lexer::lex(&code).map_err(|mut es| es.remove(0))?;
  let ast = parser::parse(tokens)?;
  let value = bytecode_vm::interpret(&ast);
  println!("Type check result: {:?}", typecheck::typecheck(&ast));
  for (i, e) in ast.exprs.iter().enumerate() {
    println!("{}: {:?}, line: {}, {:?}", i, e.tag, e.loc.start.line, e.children);
  }
  value
}

fn load_and_run(path : &PathBuf){
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let result = interpret(&code);
  match result {
    Ok(f) => println!("Output: '{:?}'", f),
    Err(s) => println!("Error: {:?}", s),
  }
}

pub fn watch(path : &str) {
  // Create a channel to receive the events.
  let (tx, rx) = channel();

  // Create a watcher object, delivering debounced events.
  // The notification back-end is selected based on the platform.
  let mut watcher = watcher(tx, Duration::from_millis(500)).unwrap();

  // Add a path to be watched. All files and directories at that path and
  // below will be monitored for changes.
  watcher.watch(path, RecursiveMode::Recursive).unwrap();

  loop {
    match rx.recv() {
      Ok(event) => {
        match event {
          DebouncedEvent::Write(path) => {
            load_and_run(&path)
          }
          _ => {}
        }
      },
      Err(e) => println!("watch error: {:?}", e),
    }
  }
}