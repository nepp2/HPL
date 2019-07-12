
pub extern "C" fn hello_world() {
  println!("Hello world");
}

pub extern "C" fn hello_world2() {
  println!("Hello world");
  hello_world();
}

