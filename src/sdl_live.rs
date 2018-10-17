
use sdl2;
use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::{Keycode, Scancode, KeyboardState};
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use sdl2::render::BlendMode;
use sdl2::video::{Window};

fn dpi_ratio(w : &Window) -> f32 {
  let (dw, _) = w.drawable_size();
  let (w, _) = w.size();
  (w as f32) / (dw as f32)
}

pub fn run_sdl2_app() {

	let (width, height) = (1800, 900);

  let sdl_context = sdl2::init().unwrap();
  let video_subsystem = sdl_context.video().unwrap();

  let window = video_subsystem.window("demo", width, height)
    .position_centered()
    .resizable()
    .build()
    .unwrap();

  let dpi_ratio = dpi_ratio(&window);

  let mut canvas = window.into_canvas().accelerated().build().unwrap();

  canvas.set_blend_mode(BlendMode::Blend);

  canvas.clear();
  canvas.present();

  let mut events = sdl_context.event_pump().unwrap();

  let mut texture_creator = canvas.texture_creator();
  
  'mainloop: loop {

    for event in events.poll_iter() {
      // handle event
    }

    ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
	}
}