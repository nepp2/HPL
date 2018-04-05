extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;

use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use std::cmp;
use std::time::Duration;
use sdl2::pixels::PixelFormatEnum::{RGBA8888, Index8};
use sdl2::render::{TextureAccess::Streaming, TextureCreator, Texture, BlendMode};
use sdl2::video::WindowContext;
use rusttype::{point, Font, FontCollection, PositionedGlyph, Scale};
use rusttype::gpu_cache::{CacheBuilder, Cache};

type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

static BOX_W : i32 = 400;
static BOX_H : i32 = 300;

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
        // v should be in the range 0.0 to 1.0
        let a = (v * 255f32) as u8;
        let x = (x as i32) + bb.min.x;
        let y = (y as i32) + bb.min.y;
        // There's still a possibility that the glyph clips the boundaries of the bitmap
        if x >= 0 && x < width as i32 && y >= 0 && y < pixel_height as i32 {
          let i = ((y as usize) * width + (x as usize)) * 4;
          pixel_data[i] = a;
        }
      })
    }
  }

  return (pixel_data, width as u32, pixel_height as u32);
}

fn layout_paragraph<'a>(
    font: &'a Font,
    scale: Scale,
    width: u32,
    text: &str,
) -> Vec<PositionedGlyph<'a>> {
    use unicode_normalization::UnicodeNormalization;
    let mut result = Vec::new();
    let v_metrics = font.v_metrics(scale);
    let advance_height = v_metrics.ascent - v_metrics.descent + v_metrics.line_gap;
    let mut caret = point(0.0, v_metrics.ascent);
    let mut last_glyph_id = None;
    for c in text.nfc() {
        if c.is_control() {
            match c {
                '\r' => {
                    caret = point(0.0, caret.y + advance_height);
                }
                '\n' => {}
                _ => {}
            }
            continue;
        }
        let base_glyph = font.glyph(c);
        if let Some(id) = last_glyph_id.take() {
            caret.x += font.pair_kerning(scale, id, base_glyph.id());
        }
        last_glyph_id = Some(base_glyph.id());
        let mut glyph = base_glyph.scaled(scale).positioned(caret);
        if let Some(bb) = glyph.pixel_bounding_box() {
            if bb.max.x > width as i32 {
                caret = point(0.0, caret.y + advance_height);
                glyph = glyph.into_unpositioned().positioned(caret);
                last_glyph_id = None;
            }
        }
        caret.x += glyph.unpositioned().h_metrics().advance_width;
        result.push(glyph);
    }
    result
}

fn create_text(tc : &TextureCreator<WindowContext>) -> Texture {
  let (pixels, width, height) = draw_font();
  let mut texture = tc.create_texture(RGBA8888, Streaming, width, height).unwrap();
  texture.update(Rect::new(0, 0, width, height), &pixels[..], (width*4) as usize).unwrap();
  texture.set_blend_mode(BlendMode::Blend);
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
  // TODO canvas.copy(text, None, Some(_rq)).unwrap();
}

fn draw_text(
  canvas : &mut Canvas, font : & Font, text : &str, x : i32, y : i32, scale : Scale,
  cache : &mut Cache, cache_width : u32, cache_height : u32, cache_tex : &mut Texture)
{
  let glyphs = layout_paragraph(&font, scale, BOX_W as u32, text);
  for glyph in &glyphs {
      cache.queue_glyph(0, glyph.clone());
  }
  cache
    .cache_queued(|rect, data| {
        cache_tex.update(
          Rect::new(
            rect.min.x as i32,
            rect.min.y as i32,
            rect.width() as u32,
            rect.height() as u32),
          data,
          rect.width() as usize
        ).unwrap();
    })
    .unwrap();

  let (cw, ch) = (cache_width as f32, cache_height as f32);
  for g in glyphs.iter() {
    if let Ok(Some((uv_rect, offset_rect))) = cache.rect_for(0, g) {
        let screen_rect = Rect::new(
          x + offset_rect.min.x,
          y + offset_rect.min.y,
          offset_rect.width() as u32,
          offset_rect.height() as u32);
        let source_rect = Rect::new(
          (uv_rect.min.x * cw) as i32,
          (uv_rect.min.y * ch) as i32,
          (uv_rect.width() * cw) as u32,
          (uv_rect.height() * ch) as u32);
        canvas.copy(&cache_tex, Some(source_rect), Some(screen_rect)).unwrap();
    }
  }
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

  let display_index = window.display_index().unwrap();

  let mut canvas = window.into_canvas().accelerated().build().unwrap();

  canvas.set_blend_mode(BlendMode::Blend);

  let texture_creator = canvas.texture_creator();
  let text_texture = create_text(&texture_creator);

  canvas.clear();
  canvas.present();

  let mut events = sdl_context.event_pump().unwrap();

  let mut xd = 0;
  let mut yd = 0;

  let mut rects = vec!();

  // #### Font stuff ####
  let (_diagonal_dpi_, horizontal_dpi, _vertical_dpi) = video_subsystem.display_dpi(display_index).unwrap();

  let (cache_width, cache_height) = (512 * horizontal_dpi as u32, 512 * horizontal_dpi as u32);
  let mut cache = CacheBuilder {
      width: cache_width,
      height: cache_height,
      ..CacheBuilder::default()
  }.build();

  let mut cache_tex = texture_creator.create_texture(Index8, Streaming, cache_width, cache_height).unwrap();

  let font_data = include_bytes!("../fonts/consola.ttf");
  let font = Font::from_bytes(font_data as &[u8]).unwrap();
  let text: String = "A japanese poem:\r
\r
色は匂へど散りぬるを我が世誰ぞ常ならむ有為の奥山今日越えて浅き夢見じ酔ひもせず\r
\r
Feel free to type out some text, and delete it with Backspace. \
You can also try resizing this window.".into();


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
    draw_stuff(width as i32, height as i32, &text_texture, &mut canvas);

    let tx = (width/2) as i32 - (BOX_W/2);
    let ty = (height/2) as i32 - (BOX_H/2);
    let scale = Scale::uniform(24.0 * horizontal_dpi);
    draw_text(
      &mut canvas, &font, &text, tx, ty, scale,
      &mut cache, cache_width, cache_height, &mut cache_tex);

    canvas.present();
	}
}

