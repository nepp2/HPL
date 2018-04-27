
use rusttype::{point, Font, FontCollection, PositionedGlyph, Scale, VMetrics};
use rusttype::gpu_cache::{CacheBuilder, Cache};
use sdl2::render::{TextureAccess::Streaming, Texture, BlendMode, Canvas, TextureCreator};
use sdl2::pixels::PixelFormatEnum::{RGBA4444};
use sdl2::video::{Window, WindowContext};
use sdl2::rect::Rect;
use ropey::Rope;

pub struct FontRenderState<'a> {
  dpi_ratio : f32,
  font : Font<'static>,
  cache : Cache<'a>,
  cache_width : u32,
  cache_height : u32,
  cache_tex : Texture<'a>,
}

impl<'a> FontRenderState<'a> {
  pub fn new<'b>(texture_creator : &'b TextureCreator<WindowContext>, font_data : &'static [u8], dpi_ratio : f32) -> FontRenderState<'a>
    where 'b: 'a
  {
    let collection = FontCollection::from_bytes(font_data).unwrap_or_else(|e| {
      panic!("error constructing a FontCollection from bytes: {}", e);
    });
    let font = collection.font_at(0) // only succeeds if collection consists of one font
      .unwrap_or_else(|e| {
        panic!("error turning FontCollection into a Font: {}", e);
      });

    let (cache_width, cache_height) = (512 * dpi_ratio as u32, 512 * dpi_ratio as u32);
    let cache = CacheBuilder {
        width: cache_width,
        height: cache_height,
        ..CacheBuilder::default()
    }.build();

    let mut cache_tex = texture_creator.create_texture(RGBA4444, Streaming, cache_width, cache_height).unwrap();
    cache_tex.set_blend_mode(BlendMode::Blend);

    FontRenderState { dpi_ratio, font, cache, cache_width, cache_height, cache_tex }
  }

  pub fn draw_text(&mut self, canvas : &mut Canvas<Window>, text_buffer : &Rope, attribs : &LayoutAttribs)
  {
    let cache = &mut self.cache;
    let font = &self.font;
    let cache_tex = &mut self.cache_tex;

    let glyphs = layout_paragraph(font, attribs, text_buffer);
    for glyph in &glyphs {
      cache.queue_glyph(0, glyph.clone());
    }
    cache
      .cache_queued(|rect, data| {
          let r =
            Rect::new(
              rect.min.x as i32,
              rect.min.y as i32,
              rect.width() as u32,
              rect.height() as u32);
          
          // TODO: this may be very inefficient. Not sure.
          cache_tex.with_lock(Some(r), |target, pitch|{
            let (w, h) = (r.width() as usize, r.height() as usize);
            for y in 0..h {
              let off = y * pitch;
              for x in 0..w {
                let off = off + (x * 2);
                let v = data[w * y + x] >> 4;
                target[off] = 0x00 | v; // Blue, Alpha
                target[off + 1] = 0xF0; // Red, Green
              }
            }
          }).unwrap();
      })
      .unwrap();

    let (cw, ch) = (self.cache_width as f32, self.cache_height as f32);
    for g in glyphs.iter() {
      if let Ok(Some((uv_rect, offset_rect))) = cache.rect_for(0, g) {
          let screen_rect = Rect::new(
            offset_rect.min.x,
            offset_rect.min.y,
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

  pub fn layout_attribs(&self, font_scale : f32) -> LayoutAttribs {
    let scale = Scale::uniform(font_scale * self.dpi_ratio);
    let font = &self.font;

    let v_metrics = font.v_metrics(scale);
    LayoutAttribs {
      advance_height: v_metrics.ascent - v_metrics.descent + v_metrics.line_gap,
      advance_width: {
        let g = font.glyph('a').scaled(scale);
        let g_width = g.h_metrics().advance_width;
        let kern = font.pair_kerning(scale, g.id(), g.id());
        g_width + kern
      },
      v_metrics,
      scale
    }
  }
}

pub struct LayoutAttribs {
  pub advance_width : f32,
  pub advance_height : f32,
  pub v_metrics : VMetrics,
  pub scale : Scale,
}

fn layout_paragraph<'a>(
  font: & Font<'a>,
  attribs : &LayoutAttribs,
  text_buffer : &Rope)
    -> Vec<PositionedGlyph<'a>>
{
    use unicode_normalization::UnicodeNormalization;
    let mut result = Vec::new();
    let mut caret = point(0.0, attribs.v_metrics.ascent);

    for l in text_buffer.lines() {
      // TODO: I'm not convinced that this handles multi-codepoint glyphs properly. Maybe the nfc function does.
      for c in l.chars().nfc() {
        if c.is_control() {
          continue;
        }
        let base_glyph = font.glyph(c);
        let mut glyph = base_glyph.scaled(attribs.scale).positioned(caret);
        caret.x += attribs.advance_width;
        result.push(glyph);
      }
      caret = point(0.0, caret.y + attribs.advance_height);
    }
    result
}
