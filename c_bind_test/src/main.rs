
extern crate libloading as lib;
use std::any::Any;

pub trait RegisterFn<FN, ARG, RET> {
    fn to_fn(&mut self, f: FN) -> Box<FnAny>;
}

type FnAny = Fn(Vec<&mut Any>) -> Result<Box<Any>, ()>;

struct ForeignFunctionInterface {
}

impl<FN, ARG, RET> RegisterFn<FN, ARG, RET> for ForeignFunctionInterface
where
  ARG : Any + Clone,
  FN: Fn(ARG) -> RET + 'static,
  RET: Any,
{
    fn to_fn(&mut self, f: FN) -> Box<FnAny> {
      let fun = move |mut args: Vec<&mut Any>| {
          let mut drain = args.drain(..);
          // Downcast every element, return in case of a type mismatch
          let a = ((*drain.next().unwrap()).downcast_mut() as Option<&mut ARG>)
            .ok_or(())?;

          // Call the user-supplied function using ($clone) to
          // potentially clone the value, otherwise pass the reference.
          Ok(Box::new(f(a.clone())) as Box<Any>)
      };
      Box::new(fun)
    }
}

fn call_dynamic() -> lib::Result<isize> {
  let lib = lib::Library::new("sdl2.dll")?;
  let ffi = ForeignFunctionInterface{};
  unsafe {
    let func : lib::Symbol<unsafe extern fn(u32) -> isize> = lib.get(b"SDL_Init")?;
    let f = ffi.to_fn(func);
    Ok(func(0))
  }
}

fn main() {
  let r = call_dynamic();
  println!("Result: {:?}", r);
}
