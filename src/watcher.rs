use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::{channel, TryRecvError};
use std::time::Duration;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::thread::JoinHandle;

use crate::error::Error;
use crate::value::Value;
use crate::interpreter;

fn print(r : Result<Value, Error>) -> String {
  match r {
    Ok(v) => format!("{:?}", v),
    Err(e) => {
      format!(
        "line: {}, column: {}, message: {}",
        e.location.start.line, e.location.start.col, e.message)
    }
  }
}

struct InterpreterTask {
  interrupt_flag : Arc<AtomicBool>,
  completion_flag : Arc<AtomicBool>,
  handle : JoinHandle<String>,
}

fn load_and_run(path : PathBuf) -> InterpreterTask {
  let interrupt_flag = Arc::new(AtomicBool::new(false));
  let completion_flag = Arc::new(AtomicBool::new(false));

  let iflag = interrupt_flag.clone();
  let cflag = completion_flag.clone();

  let handle = thread::spawn(move || {
    let mut f = File::open(path).expect("file not found");
    let mut code = String::new();
    f.read_to_string(&mut code).unwrap();
    let result = interpreter::interpret_with_interrupt(&code, iflag);
    let s = print(result);
    cflag.store(true, Ordering::Relaxed);
    s
  });

  InterpreterTask { interrupt_flag, completion_flag, handle }
}

pub fn watch(path : &str) {

  let mut task = Some(load_and_run(PathBuf::from(path)));

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

    if let Some(t) = task {
      if t.completion_flag.load(Ordering::Relaxed) {
        println!("{}", t.handle.join().unwrap());
        task = None;
      }
      else {
        task = Some(t)
      }
    }
    loop {
      match rx.try_recv() {
        Ok(event) => {
          match event {
            DebouncedEvent::Write(path) => {
              if let Some(t) = task {
                t.interrupt_flag.store(true, Ordering::Relaxed);
                println!("{}", t.handle.join().unwrap());
              }
              task = Some(load_and_run(path))
            }
            _ => {}
          }
        },
        Err(e) => match e {
          TryRecvError::Disconnected =>
            println!("watch error: {:?}", e),
          TryRecvError::Empty => break,
        },
      }
    }

    thread::sleep(Duration::from_millis(100));
  }
}