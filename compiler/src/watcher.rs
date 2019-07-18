use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::{channel, TryRecvError};
use std::time::Duration;
use std::thread;

use std::process::{Command, Stdio, Child };
use std::io::Read;
use std::str;

pub fn run_process(path : &str) -> Child {
  let exe = std::env::current_exe().unwrap();
  let exe = exe.to_str().unwrap();
  // let child = Command::new("cmd")
  //     .args(&["/C", exe, "run", path])
  let child = Command::new(exe)
      .args(&["run", path])
      .stdin(Stdio::piped())
      .stdout(Stdio::piped())
      .spawn()
      .expect("failed to execute child");
  child
}

pub fn watch(path : &str) {

  fn read_to_string<R : Read>(stream : &mut Option<R>, s : &mut String) {
    if let Some(stream) = stream.as_mut() {
      stream.read_to_string(s).unwrap();
    }
  }

  let mut process = Some(run_process(path));
  let mut output = String::new();
  let mut error = String::new();

  // Create a channel to receive the events.
  let (tx, rx) = channel();

  // Create a watcher object, delivering debounced events.
  // The notification back-end is selected based on the platform.
  let mut watcher = watcher(tx, Duration::from_millis(500)).unwrap();

  // Add a path to be watched. All files and directories at that path and
  // below will be monitored for changes.
  watcher.watch(path, RecursiveMode::Recursive).unwrap();
  watcher.watch("code/prelude.code", RecursiveMode::Recursive).unwrap();

  loop {
    //println!("loop");
    if let Some(mut p) = process {
      let exit_status = p.try_wait().expect("error");
      // TODO: ERROR - THIS CALL BLOCKS
      read_to_string(&mut p.stdout, &mut output);
      read_to_string(&mut p.stderr, &mut error);
      if let Some(exit_status) = exit_status {
        println!("{}", output);
        output.clear();
        if !exit_status.success() || error.len() > 0 {
          println!("ERROR:\n{}\n{}", exit_status, error);
          error.clear();
        }
        process = None;
      }
      else {
        process = Some(p);
        print!("{}", output);
        output.clear();
      }
    }
    //println!("loop2");
    match rx.try_recv() {
      Ok(event) => {
        match event {
          DebouncedEvent::Write(_) => {
            if let Some(p) = &mut process {
              p.kill().unwrap();
              println!("Child process killed");
            }
            process = Some(run_process(path));
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
    thread::sleep(Duration::from_millis(10));
  }
}