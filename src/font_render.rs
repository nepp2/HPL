
use rusttype::{point, Font, FontCollection, PositionedGlyph, Scale, VMetrics};
use rusttype::gpu_cache::{CacheBuilder, Cache};
use sdl2::render::{TextureAccess::Streaming, Texture, BlendMode, Canvas};
use sdl2::pixels::PixelFormatEnum::{RGBA4444};
use sdl2::video::Window;

pub struct FontRenderState {
  attribs : LayoutAttribs
}

impl FontRenderState {
  pub fn new(canvas : Canvas<Window>, font_data : &[u8], dpi_ratio : f32) -> FontRenderState {
    let collection = FontCollection::from_bytes(font_data).unwrap_or_else(|e| {
      panic!("error constructing a FontCollection from bytes: {}", e);
    });
    let font = collection.font_at(0) // only succeeds if collection consists of one font
      .unwrap_or_else(|e| {
        panic!("error turning FontCollection into a Font: {}", e);
      });

    let (cache_width, cache_height) = (512 * dpi_ratio as u32, 512 * dpi_ratio as u32);
    let mut cache = CacheBuilder {
        width: cache_width,
        height: cache_height,
        ..CacheBuilder::default()
    }.build();

    let texture_creator = canvas.texture_creator();
    let mut cache_tex = texture_creator.create_texture(RGBA4444, Streaming, cache_width, cache_height).unwrap();
    cache_tex.set_blend_mode(BlendMode::Blend);

    panic!();
  }
}

struct LayoutAttribs {
  advance_width : f32,
  advance_height : f32,
  v_metrics : VMetrics,
  scale : Scale,
}

fn layout_attribs(font : &Font, scale : Scale) -> LayoutAttribs {
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

