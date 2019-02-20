
use crate::error::{Error, ErrorContent};
use crate::value::*;
use crate::eval::{
  Environment, FunctionHandle, Function, eval_string,
  add_module, get_module_id, Module, BlockScope};
use std::mem;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use rand::prelude::*;
use std::fs::File;
use std::io::Read;

use sdl2::video::WindowPos;
use sdl2;
use sdl2::{Sdl, VideoSubsystem, EventPump};
use sdl2::event::Event;
//use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use sdl2::video::{Window};

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

type BuiltInFunction = fn(&mut Environment, Vec<Value>) -> Result<Value, ErrorContent>;

fn fun(env : &mut Environment, name : &'static str, arg_types : Vec<Type>, f : BuiltInFunction) {
  let arg_names : Vec<Symbol> =
    (0..arg_types.len()).map(|i| ((('a' as usize) + i) as u8 as char)
    .to_string()).map(|s| env.sym.get(s)).collect();
  let visible_modules = env.visible_modules();
  let f = Function { module_id: env.current_module, visible_modules, arg_names, arg_types, handle: FunctionHandle::BuiltIn(f) };
  let name_symbol = env.sym.get(name);
  env.add_function(name_symbol, f).unwrap();
}

pub fn load_library(e : &mut Environment) {
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
  fun(e, "unary_-", vec![Type::Float], |_, vs| {
    let f : Result<f32, String> = vs[0].clone().into();
    Ok(Value::from(-f?))
  });
  fun(e, "unary_!", vec![Type::Bool], |_, vs| {
    let b : Result<bool, String> = vs[0].clone().into();
    Ok(Value::from(!(b?)))
  });
  fun(e, "sqrt", vec![Type::Float], |_e, mut vs| {
    let f = vs[0].get().convert::<f32>()?;
    Ok(Value::from(f.sqrt()))
  });
  fun(e, "floor", vec![Type::Float], |_e, mut vs| {
    let v = vs[0].get().convert::<f32>()? as i64;
    Ok(Value::from(v as f32))
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
  fun(e, "pop", vec![Type::Array], |_, vs| {
    let a = Into::<Result<Array, String>>::into(vs[0].clone())?;
    let v = a.borrow_mut().pop();
    v.ok_or_else(|| format!("can't pop from empty array").into())
  });
  fun(e, "print", vec![Type::Any], |e, vs| {
    println!("{:?}", vs[0].to_string(&mut e.sym));
    Ok(Value::Unit)
  });
  fun(e, "type_name", vec![Type::Any], |e, vs| {
    Ok(Value::String(vs[0].to_type().name(&mut e.sym)))
  });
  fun(e, "import_module", vec![Type::String], |e, vs| {
    let name = Into::<Result<Symbol, String>>::into(vs[0].clone())?;
    import_module(e, name, false)?;
    Ok(Value::Unit)
  });
  fun(e, "import_module_fresh", vec![Type::String], |e, vs| {
    let name = Into::<Result<Symbol, String>>::into(vs[0].clone())?;
    import_module(e, name, true)?;
    Ok(Value::Unit)
  });

  const WATCHER : &'static str = "watcher";
  let watcher_type = e.ext_type(WATCHER);

  fun(e, "create_watcher", vec![], |e, mut _vs| {
    let v = e.ext_val(WATCHER, create_watcher());
    Ok(Value::External(v))
  });
  fun(e, "watch_module", vec![watcher_type.clone(), Type::String], |e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let w = v.downcast_mut::<FileWatcher>().unwrap();
    let module_name = vs[1].get().convert::<Symbol>()?;
    let path = format!("code/{}.code", e.sym.str(module_name));
    w.watcher.watch(path.as_str(), RecursiveMode::Recursive)
      .map_err(|_| format!("failed to watch file '{}'", path))?;
    Ok(Value::Unit)
  });
  fun(e, "poll_watcher_event", vec![watcher_type], |e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let w = v.downcast_mut::<FileWatcher>().unwrap();
    if let Some(s) = poll_watcher_event(w) {
      Ok(Value::from(e.sym.get(s)))
    }
    else {
      Ok(Value::Unit)
    }
  });
  load_sdl(e);
}

use notify::{Watcher, RecursiveMode, watcher, DebouncedEvent, ReadDirectoryChangesWatcher};
use std::sync::mpsc::{channel, TryRecvError, Receiver};

struct FileWatcher {
  watcher : ReadDirectoryChangesWatcher,
  rx : Receiver<DebouncedEvent>,
}

fn create_watcher() -> FileWatcher {
  let (tx, rx) = channel();
  let watcher = watcher(tx, Duration::from_millis(500)).unwrap();
  FileWatcher { watcher, rx}
}

fn poll_watcher_event(w : &mut FileWatcher) -> Option<String> {
  match w.rx.try_recv() {
    Ok(event) => {
      match event {
        DebouncedEvent::Write(path) => {
          let module_name = path.file_stem().unwrap().to_str().unwrap();
          Some(module_name.into())
        }
        _ => None
      }
    },
    Err(e) => match e {
      TryRecvError::Disconnected => None,
      TryRecvError::Empty => None,
    },
  }
}

fn import_module(env : &mut Environment, module_name: Symbol, load_fresh : bool) -> Result<(), ErrorContent> {
  fn inner_error(e : Error, name : &str) -> ErrorContent {
    ErrorContent::InnerError(format!("Error when loading module '{}'", name), Box::new(e))
  }
  if let Some(id) = get_module_id(env.loaded_modules, module_name) {
    if load_fresh {
      let module = Module::new(module_name);
      env.loaded_modules[id.i] = module;
      load_module(env, module_name, id).map_err(|er| inner_error(er, env.sym.str(module_name)))?;
    }
    env.import_module(id)?;
  }
  else {
    let module = Module::new(module_name);
    let id = add_module(env.loaded_modules, module);
    load_module(env, module_name, id).map_err(|er| inner_error(er, env.sym.str(module_name)))?;
    env.import_module(id)?;
  }
  Ok(())
}

fn load_module(env : &mut Environment, module_name: Symbol, module_id : ModuleId) -> Result<(), Error> {
  let file_name = format!("code/{}.code", env.sym.str(module_name));
  let mut f = File::open(file_name).expect("file not found");
  let mut code = String::new();
  f.read_to_string(&mut code).unwrap();

  let prelude_id = get_module_id(env.loaded_modules, env.sym.get("prelude")).unwrap();
  let initial_scope = BlockScope {
    variables: hashmap![],
    modules: vec![prelude_id, module_id],
  };

  let mut new_env = Environment::new(
    env.sym, env.loaded_modules,
    module_id, env.interrupt_flag, initial_scope);
  eval_string(&code, &mut new_env)?;
  Ok(())
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

impl Environment<'_> {
  fn ext_type(&mut self, s : &str) -> Type {
    Type::External(self.sym.get(s))
  }

  fn ext_val<V : 'static>(&mut self, s : &str, v : V) -> ExternalVal {
    ExternalVal {
      type_name: self.sym.get(s),
      val: Rc::new(RefCell::new(v)),
    }
  }
}

fn load_sdl(e : &mut Environment) {

  let code = "
    struct sdl_event_keydown { key : string }
    struct sdl_event_keyup { key : string }
    struct sdl_event_quit { }
    struct sdl_event_mouse_motion { x, y }
    struct sdl_event_mouse_down { x, y, button }
    struct sdl_event_mouse_up { x, y, button }
    struct sdl_event_mouse_wheel { y }
    struct sdl_event_window { event }
    // struct sdl_window_resized { }
  ";

  eval_string(code, e).unwrap();
  
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

  fn f<V : Into<Value>>(e : &mut Environment, field_name : &str, v : V) -> (Symbol, Value) {
    (e.sym.get(field_name), v.into())
  }
  fn s(e : &mut Environment, field_name : &str, v : String) -> (Symbol, Value) {
    (e.sym.get(field_name), e.sym.get(v).into())
  }

  fn new_struct(e : &mut Environment, name : &str, vals : Vec<(Symbol, Value)>)
    -> Result<Value, ErrorContent>
  {
    let name = e.sym.get(name);
    return e.instantiate_struct(name, vals).map(|s| Value::Struct(s));
  }

  fun(e, "poll_sdl_event_string", vec![sdl_view_type.clone()], |env, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let view = v.downcast_mut::<SdlView>().unwrap();
    if let Some(e) = view.events.poll_event() {
      let s = format!("{:?}", e);
      return Ok(Value::String(env.sym.get(s)));
    }
    Ok(Value::Unit)
  });

  fun(e, "poll_sdl_event", vec![sdl_view_type.clone()], |e, mut vs| {
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
          let fields = vec![s(e, "key", format!("{}", kc))];
          return new_struct(e, "sdl_event_keydown", fields);
        }
      }
      Event::KeyUp {keycode, ..} => {
        if let Some(kc) = keycode {
          let fields = vec![s(e, "key", format!("{}", kc))];
          return new_struct(e, "sdl_event_keyup", fields);
        }
      }
      Event::Quit { .. } => {
        return new_struct(e, "sdl_event_quit", vec![]);
      }
      Event::MouseMotion { x, y, .. } => {
          let fields = vec![
            f(e, "x", x as f32),
            f(e, "y", y as f32),
          ];
          return new_struct(e, "sdl_event_mouse_motion", fields);
      }
      Event::MouseButtonDown { x, y, mouse_btn, .. } => {
          let fields = vec![
            f(e, "x", x as f32),
            f(e, "y", y as f32),
            s(e, "button", format!("{:?}", mouse_btn)),
          ];
          return new_struct(e, "sdl_event_mouse_down", fields);
      }
      Event::MouseButtonUp { x, y, mouse_btn, .. } => {
          let fields = vec![
            f(e, "x", x as f32),
            f(e, "y", y as f32),
            s(e, "button", format!("{:?}", mouse_btn)),
          ];
          return new_struct(e, "sdl_event_mouse_up", fields);
      }
      Event::MouseWheel { y, .. } => {
          let fields = vec![
            f(e, "y", y as f32),
          ];
          return new_struct(e, "sdl_event_mouse_wheel", fields);
      }
      Event::Window { win_event, .. } => {
        let fields = vec![
          s(e, "event", format!("{:?}", win_event)),
        ];
        return new_struct(e, "sdl_event_window", fields);
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

  const TIME_SNAPSHOT : &'static str = "time_snapshot";
  let time_snapshot_type = e.ext_type(TIME_SNAPSHOT);

  fun(e, "time_now", vec![], |e, mut _vs| {
    let v = e.ext_val(TIME_SNAPSHOT, Instant::now());
    Ok(Value::External(v))
  });

  fun(e, "time_since", vec![time_snapshot_type], |_e, mut vs| {
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let instant = v.downcast_mut::<Instant>().unwrap();
    let new_now = Instant::now();
    let duration = new_now.duration_since(*instant);
    let f = duration.subsec_micros() as f32 / 1000.0;
    Ok(Value::from(f))
  });

  const RANDOM_GENERATOR : &'static str = "random_generator";
  let random_generator = e.ext_type(RANDOM_GENERATOR);

  fun(e, "random_generator", vec![], |e, mut _vs| {
    let rng : StdRng = SeedableRng::seed_from_u64(0);
    let v = e.ext_val(RANDOM_GENERATOR, rng);
    Ok(Value::External(v))
  });

  fun(e, "next_rand", vec![random_generator], |_e, mut vs| {  
    let v = vs[0].get().convert::<ExternalVal>()?;
    let mut v = v.val.borrow_mut();
    let rng = v.downcast_mut::<StdRng>().unwrap();
    Ok(Value::Float(rng.gen()))
  });
}
