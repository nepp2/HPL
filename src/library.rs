
use crate::value::*;
use crate::error::*;
use crate::interpreter::{Environment, FunctionHandle, Method};

fn into<T>(vals : Vec<usize>, i : usize, )

macro_rules! binary {
  ($env:expr, $n:expr, $a:ident, $b:ident, $c:ident, $f:expr) => {
    {
      let f : fn(Vec<Value>) -> Result<Value, String> =
        |vals : Vec<Value>| {
          let a : Result<$a, String> = vals.swap_remove(0, Value::Unit).into();
          let b : Result<$b, String> = vals.swap_remove(1, Value::Unit).into();
          let c : $c = ($f)(a?, b?);
          let v : Value = Value::from(c);
          Ok(v)
        };
      fun($env, $n, vec![type_tag!($a), type_tag!($b)], f)
    }
  }
}

macro_rules! type_tag {
  (f32) => { Type::Float };
  (bool) => { Type::Bool };
  (RefStr) => { Type::String };
  (()) => { Type::Unit };
}

type BuiltInFunction = fn(Vec<Value>) -> Result<Value, String>;

fn fun(env : &mut Environment, name : &'static str, arg_types : Vec<Type>, f : BuiltInFunction) {
  let arg_names : Vec<RefStr> =
    (0..arg_types.len()).map(|i| ((('a' as usize) + i) as u8 as char)
    .to_string()).map(|s| env.symbol_cache.symbol(s)).collect();
  let m = Method { arg_names, arg_types, handle: FunctionHandle::BuiltIn(f) };
  env.add_function(name, m).unwrap();
}

pub fn load_library(e : &mut Environment) {
  binary!(e, "+", f32, f32, f32, |a, b| a + b);
  binary!(e, "-", f32, f32, f32, |a, b| a - b);
  binary!(e, "*", f32, f32, f32, |a, b| a * b);
  binary!(e, "/", f32, f32, f32, |a, b| a / b);
  binary!(e, ">", f32, f32, bool, |a, b| a > b);
  binary!(e, "<", f32, f32, bool, |a, b| a < b);
  binary!(e, "<=", f32, f32, bool, |a, b| a <= b);
  binary!(e, ">=", f32, f32, bool, |a, b| a >= b);
  fun(e, "==", vec![Type::Any, Type::Any], |vs| {
    let b = vs[0] == vs[1];
    Ok(Value::from(b))
  });
  binary!(e, "&&", bool, bool, bool, |a, b| a && b);
  binary!(e, "||", bool, bool, bool, |a, b| a || b);
  fun(e, "-", vec![Type::Float], |vs| {
    let f : Result<f32, String> = vs[0].clone().into();
    Ok(Value::from(-f?))
  });
  fun(e, "len", vec![Type::Array], |vs| {
    let a = Into::<Result<Array, String>>::into(vs[0].clone())?;
    let len = a.borrow().len() as f32;
    Ok(Value::from(len))
  });

  load_sdl(e);
}

use sdl2;
use sdl2::{Sdl, VideoSubsystem, EventPump};
use sdl2::event::Event;
use sdl2::keyboard::{Keycode};
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use sdl2::video::{Window};
use std::time::Duration;

fn dpi_ratio(w : &Window) -> f32 {
  let (dw, _) = w.drawable_size();
  let (w, _) = w.size();
  (w as f32) / (dw as f32)
}

pub type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

pub struct SdlView {
  pub sdl : Sdl,
  pub video : VideoSubsystem, 
  pub dpi_ratio : f32,
  pub canvas : Canvas,
  pub events : EventPump,
}

pub fn create_sdl_view (width : u32, height : u32) -> SdlView {
  let sdl = sdl2::init().unwrap();
  let video = sdl.video().unwrap();

  let window = video.window("demo", width, height)
    .position_centered()
    .resizable()
    .build()
    .unwrap();

  let dpi_ratio = dpi_ratio(&window);
  let canvas = window.into_canvas().accelerated().build().unwrap();
  let events = sdl.event_pump().unwrap();

  SdlView { sdl, video, dpi_ratio, canvas, events }
}

pub fn run() {
  let (width, height) = (800, 600);
  let mut v = create_sdl_view(width, height);

  'mainloop: loop {
    for event in v.events.poll_iter() {
      match &event {
        &Event::Quit{..} |
        &Event::KeyDown {keycode: Some(Keycode::Escape), ..} =>
          break 'mainloop,
        _ => (),
      }

      v.canvas.set_draw_color(Color::RGBA(20, 20, 20, 255));
      v.canvas.clear();

      // draw background lines
      let (width, height) = (width as i32, height as i32);
      v.canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
      let line_interval = 15;
      for x in 0..(width/line_interval) {
        v.canvas.draw_line(Point::new(x * line_interval, 0), Point::new(x * line_interval, height)).unwrap();
      }
      for y in 0..(height/line_interval) {
        v.canvas.draw_line(Point::new(0, y * line_interval), Point::new(width, y * line_interval)).unwrap();
      }

      v.canvas.present();
      ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
    }
  }
}

fn load_sdl(e : &mut Environment) {
  fun(e, "create_sdl_view", vec![Type::Float, Type::Float], |vs| {
    let a = Into::<Result<Array, String>>::into(vs[0].clone())?;
    let len = a.borrow().len() as f32;
    Ok(Value::from(len))
  });
}
