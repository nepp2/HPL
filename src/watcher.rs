use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use error::Error;
use parser;
use lexer;
use value::{Value, Type};
use bytecode_vm;
use typecheck;

fn print_type(r : Result<Type, Error>){
  match r {
    Ok(t) => println!("{:?}", t),
    Err(e) => {
      println!(
        "line: {}, column: {}, message: {}",
        e.location.start.line, e.location.start.col, e.message);
    }
  }
}

fn interpret(code: &str) -> Result<Value, Error> {
  let tokens = lexer::lex(&code).map_err(|mut es| es.remove(0))?;
  let mut expr = parser::parse(tokens)?;
  let r = typecheck::typecheck(&mut expr);
  print_type(r.map(|_| expr.type_info.clone()));
  let value = bytecode_vm::interpret(&expr);
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