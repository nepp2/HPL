use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::{channel, TryRecvError};
use std::time::Duration;
use std::thread;

use std::process::{Command, Stdio, Child };
use std::str;

pub fn run_process(path : &str) -> Child {
  let exe = std::env::current_exe().unwrap();
  let exe = exe.to_str().unwrap();
  let child = Command::new("cmd")
      .args(&["/C", exe, "run", path])
      .stdin(Stdio::piped())
      .stdout(Stdio::piped())
      .spawn()
      .expect("failed to execute child");
  child
}

pub fn watch(path : &str) {

  let mut process = Some(run_process(path));

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

    if let Some(mut p) = process {
      let exited = p.try_wait().expect("error").is_some();
      if exited {
        let output = p.wait_with_output().unwrap();
        println!("process finished. output:\n{}",
          str::from_utf8(output.stdout.as_slice()).unwrap());
        if !output.status.success() {
          println!("ERROR:\n{}\n{}",
          output.status,
          str::from_utf8(output.stderr.as_slice()).unwrap());
        }
        process = None;
      }
      else {
        process = Some(p);
      }
    }
    loop {
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
    }
    thread::sleep(Duration::from_millis(10));
  }
}