use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use parser;
use lexer;
use value::{Value};
use bytecode_vm;

fn stringify_error<A, B>(r : Result<A, B>, s : &str) -> Result<A, String> {
  match r {
    Ok(a) => Ok(a),
    Err(_) => Err(s.to_string()),
  }
}

fn interpret(code: &str) -> Result<Value, String> {
  let tokens = stringify_error(lexer::lex(&code), "Lexer Error")?;
  let ast = parser::parse(tokens)?;
  bytecode_vm::interpret(&ast)
}

fn load_and_run(path : &PathBuf){
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let result = interpret(&code);
  match result {
    Ok(f) => println!("Output: '{:?}'", f),
    Err(s) => println!("Error: {}", s),
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