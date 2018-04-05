extern crate sdl2;
extern crate rusttype;

use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use std::cmp;
use std::time::Duration;
use sdl2::pixels::PixelFormatEnum::RGBA8888;
use sdl2::render::{TextureAccess::Streaming, TextureCreator, Texture, BlendMode};
use sdl2::video::WindowContext;

type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

static BOX_W : i32 = 400;
static BOX_H : i32 = 300;

use rusttype::{point, FontCollection, PositionedGlyph, Scale};
use std::io::Write;

fn draw_font() -> (Vec<u8>, u32, u32) {
  let font_data = include_bytes!("../fonts/consola.ttf");
  let collection = FontCollection::from_bytes(font_data as &[u8]).unwrap_or_else(|e| {
    panic!("error constructing a FontCollection from bytes: {}", e);
  });
  let font = collection.into_font() // only succeeds if collection consists of one font
    .unwrap_or_else(|e| {
      panic!("error turning FontCollection into a Font: {}", e);
    });

  // Desired font pixel height
  let height: f32 = 20.0; // to get 80 chars across (fits most terminals); adjust as desired
  let pixel_height = height.ceil() as usize;

  // 2x scale in x direction to counter the aspect ratio of monospace characters.
  let scale = Scale {
    x: height,
    y: height,
  };

  // The origin of a line of text is at the baseline (roughly where
  // non-descending letters sit). We don't want to clip the text, so we shift
  // it down with an offset when laying it out. v_metrics.ascent is the
  // distance between the baseline and the highest edge of any glyph in
  // the font. That's enough to guarantee that there's no clipping.
  let v_metrics = font.v_metrics(scale);
  let offset = point(0.0, v_metrics.ascent);

  // Glyphs to draw for "RustType". Feel free to try other strings.
  let glyphs: Vec<PositionedGlyph> = font.layout("Hello World", scale, offset).collect();

  // Find the most visually pleasing width to display
  let width = glyphs
    .iter()
    .rev()
    .map(|g| g.position().x as f32 + g.unpositioned().h_metrics().advance_width)
    .next()
    .unwrap_or(0.0)
    .ceil() as usize;

  // Rasterise directly into ASCII art.
  let mut pixel_data = vec![0 as u8; width * 4 * pixel_height];
  for g in glyphs {
    if let Some(bb) = g.pixel_bounding_box() {
      g.draw(|x, y, v| {
        println!("x: {}, y: {}, v: {}", x, y, v);
        // v should be in the range 0.0 to 1.0
        let a = (v * 255f32) as u8;
        let x = (x as i32) + bb.min.x;
        let y = (y as i32) + bb.min.y;
        // There's still a possibility that the glyph clips the boundaries of the bitmap
        if x >= 0 && x < width as i32 && y >= 0 && y < pixel_height as i32 {
          let i = ((y as usize) * width + (x as usize)) * 4;
          println!("x: {}, y: {}, i: {}, a: {}", x, y, i, a);
          pixel_data[i] = a;
        }
      })
    }
  }

  return (pixel_data, width as u32, pixel_height as u32);

  /* Print it out
  let stdout = ::std::io::stdout();
  let mut handle = stdout.lock();
  for j in 0..pixel_height {
    handle
      .write(&pixel_data[j * width..(j + 1) * width])
      .unwrap();
    handle.write(b"\n").unwrap();
  }
  */
}

fn create_text(tc : &TextureCreator<WindowContext>) -> Texture {
  let (pixels, width, height) = draw_font();
  let mut texture = tc.create_texture(RGBA8888, Streaming, width, height).unwrap();
  texture.update(Rect::new(0, 0, width, height), &pixels[..], (width*4) as usize).unwrap();
  texture.set_blend_mode(BlendMode::Blend);
  println!("width: {}, height: {}", width, height);
  return texture;
}

fn draw_stuff(w : i32, h : i32, text : &Texture, canvas : &mut Canvas){
	let (rw, rh) = (BOX_W, BOX_H);
	let x = (w/2) - (rw/2);
	let y = (h/2) - (rh/2);
  let rect = Rect::new(x, y, rw as u32, rh as u32);
	canvas.fill_rect(rect).unwrap();
  let q = text.query();
  let _rq = Rect::new(x, y, q.width, q.height);
  canvas.copy(text, None, Some(_rq)).unwrap();
}

pub fn main() {

	let (mut width, mut height) = (800, 600);

    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem.window("cauldron", width, height)
      .position_centered()
      .resizable()
      .build()
      .unwrap();

    let mut canvas = window.into_canvas().accelerated().build().unwrap();

    canvas.set_blend_mode(BlendMode::Blend);

    let texture_creator = canvas.texture_creator();
    let text = create_text(&texture_creator);

    canvas.clear();
    canvas.present();

    let mut events = sdl_context.event_pump().unwrap();

    let mut xd = 0;
    let mut yd = 0;

    let mut rects = vec!();

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
	        },
	        Event::Window { win_event, .. } => {
	          match win_event {
	            WindowEvent::Resized(x, y) => {
	            	width = x as u32;
	            	height = y as u32;
	            },
	            _ => {}
	          }
	        },
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
      draw_stuff(width as i32, height as i32, &text, &mut canvas);
      canvas.present();
	}
}

