
use sdl2;
use sdl2::{Sdl, VideoSubsystem, EventPump};
use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::{Keycode, Scancode, KeyboardState};
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use sdl2::render::BlendMode;
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

pub fn init (width : u32, height : u32) -> SdlView {
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
  let mut v = init(width, height);

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
