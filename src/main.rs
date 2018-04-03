extern crate sdl2;

use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use std::cmp;
use std::time::Duration;

type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

static BOX_W : i32 = 400;
static BOX_H : i32 = 300;

fn draw_stuff(w : i32, h : i32, text : &mut string, canvas : &mut Canvas){
	let (rw, rh) = (BOX_W, BOX_H);
	let x = (w/2) - (rw/2);
	let y = (h/2) - (rh/2);
	canvas.fill_rect(Rect::new(x, y, rw as u32, rh as u32)).unwrap();
}

pub fn main() {

	let (mut width, mut height) = (800, 600);

    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem.window("rust-sdl2 demo: Cursor", width, height)
      .position_centered()
      .resizable()
      .build()
      .unwrap();

    let mut canvas = window.into_canvas().software().build().unwrap();

    canvas.clear();
    canvas.present();

    let mut events = sdl_context.event_pump().unwrap();

    let mut xd = 0;
    let mut yd = 0;

    let mut rects = vec!();

    let mut text = "Hello World".to_string();

    'mainloop: loop {
        for event in events.poll_iter() {
            match event {
                Event::Quit{..} |
                Event::KeyDown {keycode: Option::Some(Keycode::Escape), ..} =>
                    break 'mainloop,
	            Event::MouseButtonUp {x, y, ..} => {
	             	let xp = cmp::min(x, xd);
	             	let yp = cmp::min(y, yd);
	             	let w = (x - xd).abs() as u32;
	             	let h = (y - yd).abs() as u32;
	             	rects.push(Rect::new(xp, yp, w, h));
	            },
	            Event::MouseButtonDown {x, y, ..} => {
	                xd = x;
	                yd = y;
	            }
	            Event::Window { win_event, .. } => {
	            	match win_event {
	            		WindowEvent::Resized(x, y) => {
	            			width = x as u32;
	            			height = y as u32;
	            		},
	            		_ => {}
	            	}
	            }
                _e => {}
            }
        }
        ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
        // The rest of the loop goes here...

		canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
        canvas.clear();
        canvas.set_draw_color(Color::RGBA(255, 255, 255, 255));
        for r in rects.iter() {
        	canvas.fill_rect(*r).unwrap();
    	}
        draw_stuff(width as i32, height as i32, &mut text, &mut canvas);
        canvas.present();
	}
}

