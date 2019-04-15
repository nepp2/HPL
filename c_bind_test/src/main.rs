
extern crate libloading as lib;

fn call_dynamic() -> lib::Result<isize> {
  let lib = lib::Library::new("sdl2.dll")?;
  unsafe {
    let func: lib::Symbol<unsafe extern fn(u32) -> isize> = lib.get(b"SDL_Init")?;
    Ok(func(0))
  }
}

fn main() {
  let r = call_dynamic();
  println!("Result: {:?}", r);
}
