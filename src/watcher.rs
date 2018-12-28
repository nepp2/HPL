use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::channel;
use std::time::Duration;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use crate::error::Error;
use crate::value::Value;
use crate::interpreter;

fn print(r : Result<Value, Error>){
  match r {
    Ok(v) => println!("{:?}", v),
    Err(e) => {
      println!(
        "line: {}, column: {}, message: {}",
        e.location.start.line, e.location.start.col, e.message);
    }
  }
}

/*
fn interpret(code: &str) -> Result<Value, Error> {
  let intrinsics = intrinsics::get_intrinsics(&mut sc);
  typecheck::typecheck(&mut expr, &intrinsics)?;
  println!("Type: {:?}", expr.type_info);
  let entry_function = "top_level";
  let program = bytecode_compile::compile_to_bytecode(&expr, entry_function, &mut sc, &intrinsics)?;
  let value = bytecode_vm::interpret_bytecode(&program, entry_function);
  value
}
*/

fn load_and_run(path : &PathBuf){
  let mut f = File::open(path).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();
  let result = interpreter::interpret(&code);
  print(result);
}

pub fn watch(path : &str) {

  load_and_run(&PathBuf::from(path));

  // Create a channel to receive the events.
  let (tx, rx) = channel();

  // Create a watcher object, delivering debounced events.
  // The notification back-end is selected based on the platform.
  let mut watcher = watcher(tx, Duration::from_millis(500)).unwrap();

  // Add a path to be watched. All files and directories at that path and
  // below will be monitored for changes.
  watcher.watch(path, RecursiveMode::Recursive).unwrap();
  watcher.watch("prelude.code", RecursiveMode::Recursive).unwrap();

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