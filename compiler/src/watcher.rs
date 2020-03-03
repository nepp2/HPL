use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent};
use std::sync::mpsc::{channel, TryRecvError};
use std::time::Duration;
use std::thread;
use std::default::Default;

use std::io::{BufReader, BufRead};
use std::str;

use subprocess::{Popen, PopenConfig, Redirection};

pub fn run_process(path : &str) -> Popen {
  let exe = std::env::current_exe().unwrap();
  let exe = exe.to_str().unwrap();
  let mut p = Popen::create(&[exe, "run", path], PopenConfig {
      stdout: Redirection::Pipe, ..Default::default()
  }).unwrap();
  let stdout = p.stdout.take().unwrap();
  thread::spawn(|| {
    let mut s = String::new();
    let mut buf = BufReader::new(stdout);
    loop {
      let i = buf.read_line(&mut s).unwrap();
      print!("{}", s);
      s.clear();
      if i == 0 {
        break;
      }
    }
    println!("Watcher stdout thread terminating");
  });
  p
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
  watcher.watch("code/core/prelude.code", RecursiveMode::Recursive).unwrap();

  loop {
    //println!("loop");
    if let Some(mut p) = process {
      // check if the process is still alive
      let exit_status = p.poll();

      if let Some(exit_status) = exit_status {
        let (_, err) = p.communicate(None).unwrap();
        if !exit_status.success() {
          println!("ERROR:\n{:?}", exit_status);
        }
        if let Some(err) = err {
          println!("{}", err);
        }
        process = None;
      }
      else {
        process = Some(p);
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
        TryRecvError::Empty => (),
      },
    }
    thread::sleep(Duration::from_millis(10));
  }
}