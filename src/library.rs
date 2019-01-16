
use crate::value::*;
use crate::interpreter::{Interpreter, Environment, FunctionHandle, Method};
use std::mem;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use sdl2::video::WindowPos;

use sdl2;
use sdl2::{Sdl, VideoSubsystem, EventPump};
use sdl2::event::Event;
//use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use sdl2::video::{Window};
use std::time::Duration;

impl Value {
  fn convert<T>(self) -> Result<T, String>
    where Value: Into<Result<T, String>>
  {
    let r : Result<T, String> = self.into();
    return r;
  }

  /// Return the borrowed value and replace it in-place with Unit
  fn get(&mut self) -> Value {
    mem::replace(self, Value::Unit)
  }
}

macro_rules! binary {
  ($env:expr, $n:expr, $a:ident, $b:ident, $c:ident, $f:expr) => {
    {
      let f : BuiltInFunction =
        |_, mut vals : Vec<Value>| {
          let a = vals[0].get().convert::<$a>();
          let b = vals[1].get().convert::<$b>();
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

type BuiltInFunction = fn(&mut Environment, Vec<Value>) -> Result<Value, String>;

fn fun(env : &mut Environment, name : &'static str, arg_types : Vec<Type>, f : BuiltInFunction) {
  let arg_names : Vec<RefStr> =
    (0..arg_types.len()).map(|i| ((('a' as usize) + i) as u8 as char)
    .to_string()).map(|s| env.symbol_cache.symbol(s)).collect();
  let m = Method { arg_names, arg_types, handle: FunctionHandle::BuiltIn(f) };
  env.add_function(name, m).unwrap();
}

pub fn load_library(i : &mut Interpreter) {
  let e = &mut i.env;
  binary!(e, "+", f32, f32, f32, |a, b| a + b);
  binary!(e, "-", f32, f32, f32, |a, b| a - b);
  binary!(e, "*", f32, f32, f32, |a, b| a * b);
  binary!(e, "/", f32, f32, f32, |a, b| a / b);
  binary!(e, "%", f32, f32, f32, |a, b| a % b);
  binary!(e, ">", f32, f32, bool, |a, b| a > b);
  binary!(e, "<", f32, f32, bool, |a, b| a < b);
  binary!(e, "<=", f32, f32, bool, |a, b| a <= b);
  binary!(e, ">=", f32, f32, bool, |a, b| a >= b);
  fun(e, "==", vec![Type::Any, Type::Any], |_, vs| {
    let b = vs[0] == vs[1];
    Ok(Value::from(b))
  });
  fun(e, "!=", vec![Type::Any, Type::Any], |_, vs| {
    let b = vs[0] != vs[1];
    Ok(Value::from(b))
  });
  fun(e, "-", vec![Type::Float], |_, vs| {
    let f : Result<f32, String> = vs[0].clone().into();
    Ok(Value::from(-f?))
  });
  fun(e, "!", vec![Type::Bool], |_, vs| {
    let b : Result<bool, String> = vs[0].clone().into();
    Ok(Value::from(!(b?)))
  });
  fun(e, "len", vec![Type::Array], |_, vs| {
    let a = Into::<Result<Array, String>>::into(vs[0].clone())?;
    let len = a.borrow().len() as f32;
    Ok(Value::from(len))
  });
  fun(e, "add", vec![Type::Array, Type::Any], |_, vs| {
    let a = Into::<Result<Array, String>>::into(vs[0].clone())?;
    let v = vs[1].clone();
    a.borrow_mut().push(v);
    Ok(Value::Unit)
  });
  fun(e, "print", vec![Type::Any], |_, vs| {
    println!("{:?}", vs[0]);
    Ok(Value::Unit)
  });
  fun(e, "type_name", vec![Type::Any], |_, vs| {
    Ok(Value::String(vs[0].type_name()))
  });

  load_sdl(i);
}

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

impl Environment {
  fn ext_type(&mut self, s : &str) -> Type {
    Type::External(self.symbol_cache.symbol(s))
  }

  fn ext_val<V : 'static>(&mut self, s : &str, v : V) -> ExternalVal {
    ExternalVal {
      type_name: self.symbol_cache.symbol(s),
      val: Rc::new(RefCell::new(v)),
    }
  }
}

fn load_sdl(i : &mut Interpreter) {

  let code = "
    struct sdl_event_keydown { key : string }
    struct sdl_event_keyup { key : string }
    struct sdl_event_quit { }
    struct sdl_event_mouse_motion { x, y }
    struct sdl_event_mouse_down { x, y, button }
    struct sdl_event_mouse_up { x, y, button }
    struct sdl_event_mouse_wheel { y }
    // struct sdl_window_resized { }
  ";

  i.interpret(code).unwrap();

  let e = &mut i.env;
  const SDL_VIEW : &'static str = "sdl_view";
  let sdl_view_type = e.ext_type(SDL_VIEW);

  fun(e, "create_sdl_view", vec![Type::Float, Type::Float], |e, mut vs| {
    let a = vs[0].get().convert::<f32>()? as u32;
    let b = vs[1].get().convert::<f32>()? as u32;
    let v = e.ext_val(SDL_VIEW, create_sdl_view(a, b));
    Ok(Value::External(v))
  });

  fun(e, "set_window_pos", vec![sdl_view_type.clone(), Type::Any, Type::Any], |_, mut vs| {
    fn to_pos(v : Value) -> Result<WindowPos, String> {
      if v == Value::Unit { Ok(WindowPos::Centered) }
      else { Ok(WindowPos::Positioned(v.convert::<f32>()? as i32)) }
    }
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    let x = to_pos(vs[1].get())?;
    let y = to_pos(vs[2].get())?;
    view.canvas.window_mut().set_position(x, y);
    Ok(Value::Unit)
  });

  fn new_struct(e : &mut Environment, name : &str, vals : HashMap<RefStr, Value>)
    -> Result<Value, String>
  {
    return e.instantiate_struct(name, vals).map(|s| Value::Struct(s));
  }

  fun(e, "poll_event_any", vec![sdl_view_type.clone()], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    if let Some(e) = view.events.poll_event() {
      let s = format!("{:?}", e);
      return Ok(Value::String(s.into()));
    }
    Ok(Value::Unit)
  });

  fun(e, "poll_event", vec![sdl_view_type.clone()], |e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    let event = if let Some(e) = view.events.poll_event() {
      e
    }
    else {
      return Ok(Value::Unit);
    };
    match event {
      Event::KeyDown {keycode, ..} => {
        if let Some(kc) = keycode {
          return new_struct(e, "sdl_event_keydown", hashmap!{
            "key".into() => format!("{}", kc).into(),
          });
        }
      }
      Event::KeyUp {keycode, ..} => {
        if let Some(kc) = keycode {
          return new_struct(e, "sdl_event_keyup", hashmap!{
            "key".into() => format!("{}", kc).into(),
          });
        }
      }
      Event::Quit { .. } => {
        return new_struct(e, "sdl_event_quit", hashmap!{});
      }
      Event::MouseMotion { x, y, .. } => {
          return new_struct(e, "sdl_event_mouse_motion", hashmap!{
            "x".into() => (x as f32).into(),
            "y".into() => (y as f32).into(),
          });
      }
      Event::MouseButtonDown { x, y, mouse_btn, .. } => {
          return new_struct(e, "sdl_event_mouse_down", hashmap!{
            "x".into() => (x as f32).into(),
            "y".into() => (y as f32).into(),
            "button".into() => format!("{:?}", mouse_btn).into(),
          });
      }
      Event::MouseButtonUp { x, y, mouse_btn, .. } => {
          return new_struct(e, "sdl_event_mouse_up", hashmap!{
            "x".into() => (x as f32).into(),
            "y".into() => (y as f32).into(),
            "button".into() => format!("{:?}", mouse_btn).into(),
          });
      }
      Event::MouseWheel { y, .. } => {
          return new_struct(e, "sdl_event_mouse_wheel", hashmap!{
            "y".into() => (y as f32).into(),
          });
      }
      _ => (),
    }
    return Ok(Value::Unit);
  });

  fun(e, "clear", vec![sdl_view_type.clone()], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.clear();
    return Ok(Value::Unit);
  });

  fun(e, "set_draw_color", vec![sdl_view_type.clone(), Type::Float, Type::Float, Type::Float, Type::Float], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let r = vs[1].get().convert::<f32>()? as u8;
    let g = vs[2].get().convert::<f32>()? as u8;
    let b = vs[3].get().convert::<f32>()? as u8;
    let a = vs[4].get().convert::<f32>()? as u8;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.set_draw_color(Color::RGBA(r, g, b, a));
    return Ok(Value::Unit);
  });

  fun(e, "draw_line", vec![sdl_view_type.clone(), Type::Float, Type::Float, Type::Float, Type::Float], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let x1 = vs[1].get().convert::<f32>()? as i32;
    let y1 = vs[2].get().convert::<f32>()? as i32;
    let x2 = vs[3].get().convert::<f32>()? as i32;
    let y2 = vs[4].get().convert::<f32>()? as i32;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.draw_line(Point::new(x1, y1), Point::new(x2, y2)).unwrap();
    return Ok(Value::Unit);
  });

  fun(e, "draw_rect", vec![sdl_view_type.clone(), Type::Float, Type::Float, Type::Float, Type::Float], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let x = vs[1].get().convert::<f32>()? as i32;
    let y = vs[2].get().convert::<f32>()? as i32;
    let w = vs[3].get().convert::<f32>()? as u32;
    let h = vs[4].get().convert::<f32>()? as u32;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.draw_rect(Rect::new(x, y, w, h)).unwrap();
    return Ok(Value::Unit);
  });

  fun(e, "fill_rect", vec![sdl_view_type.clone(), Type::Float, Type::Float, Type::Float, Type::Float], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let x = vs[1].get().convert::<f32>()? as i32;
    let y = vs[2].get().convert::<f32>()? as i32;
    let w = vs[3].get().convert::<f32>()? as u32;
    let h = vs[4].get().convert::<f32>()? as u32;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.fill_rect(Rect::new(x, y, w, h)).unwrap();
    return Ok(Value::Unit);
  });

  fun(e, "present", vec![sdl_view_type.clone()], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    view.canvas.present();
    return Ok(Value::Unit);
  });

  fun(e, "sleep", vec![Type::Float], |_e, mut vs| {
    let millis = vs[0].get().convert::<f32>()?;
    let micros = millis * 1000.0;
    Duration::from_micros(micros as u64);
    return Ok(Value::Unit);
  });
}
