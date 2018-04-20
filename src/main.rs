extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;

use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::{Keycode, Scancode, KeyboardState};
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use std::cmp;
use std::time::Duration;
use std::collections::VecDeque;
use sdl2::pixels::PixelFormatEnum::{RGBA4444};
use sdl2::render::{TextureAccess::Streaming, Texture, BlendMode};
use sdl2::video::{Window};
use rusttype::{point, Font, FontCollection, PositionedGlyph, Scale, VMetrics};
use rusttype::gpu_cache::{CacheBuilder, Cache};
use ropey::Rope;
use clipboard::{ClipboardProvider, ClipboardContext};

/*

TODO:

I have not properly understood the distiction between byte, character and grapheme in
the Ropey library. As a result I have been programming quite defensively. I might
be able to simplify some of the code if I look this up. There might be bugs too...

*/

type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

static BOX_W : i32 = 400;
static BOX_H : i32 = 300;

static TEXT: &str = "Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";

struct LayoutAttribs {
  advance_width : f32,
  advance_height : f32,
  v_metrics : VMetrics,
  buffer_width : f32,
  scale : Scale,
}

fn layout_attribs(font : &Font, scale : Scale, buffer_width : f32) -> LayoutAttribs {
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
    buffer_width,
    scale
  }
}

fn layout_paragraph<'a>(
  font: &'a Font,
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

// TODO: this takes way too many paramters, so there should probably be some structs or something
fn draw_text<'l>(
  canvas : &mut Canvas, font : &'l Font, text_buffer : &Rope, attribs : &LayoutAttribs,
  cache : &mut Cache<'l>, cache_width : u32, cache_height : u32, cache_tex : &mut Texture)
{
  let glyphs = layout_paragraph(&font, attribs, text_buffer);
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

  let (cw, ch) = (cache_width as f32, cache_height as f32);
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

fn dpi_ratio(w : &Window) -> f32 {
  let (dw, _) = w.drawable_size();
  let (w, _) = w.size();
  (w as f32) / (dw as f32)
}

// TODO: Pos might sometimes be changed in terms of graphemes instead
// codepoints. Not sure.
#[derive(Copy, Clone)]
struct Caret {
  pos : usize,
  // maintains consistency for vertical motion of the caret
  preferred_column : usize,
  // tracks highlighting
  marker : Option<usize>,
}

fn step_right(caret : &mut Caret, text : &Rope, shift_down : bool){
  if let Some(m) = caret.marker {
    if !shift_down {
      // dehighlight and jump to the right of the highlighted region
      caret.marker = None;
      caret.pos = cmp::max(m, caret.pos);
      return;
    }
  }
  // else, move the caret right
  if caret.pos < text.len_chars() {
    caret.pos = text.next_grapheme_boundary(caret.pos);
  }
  caret.preferred_column = caret.pos;
}

fn step_left(caret : &mut Caret, text : &Rope, shift_down : bool){
  if let Some(m) = caret.marker {
    if !shift_down {
      // dehighlight and jump to the left of the highlighted region
      caret.marker = None;
      caret.pos = cmp::min(m, caret.pos);
      return;
    }
  }
  // else, move the caret left
  if caret.pos > 0 {
    caret.pos = text.prev_grapheme_boundary(caret.pos);
  }
  caret.preferred_column = caret.pos;
}

/*
  This is basically a replacement for the "char_to_line" function
  which behaves in a more convenient way for me. The default function
  will imagine a newline at the end of the rope, even when there is no
  newline character. This function very crudely corrects that, but
  should also be treated as suspicious and possibly broken.
*/
fn char_to_line(text : &Rope, pos : usize) -> usize {
  let l = text.char_to_line(pos);
  if l == text.len_lines() { l - 1 }
  else { l }
}

fn line_change(caret : &mut Caret, text : &Rope, dir : i32){
  let new_line = char_to_line(text, caret.pos) as i32 + dir;
  if new_line < 0 || new_line >= (text.len_lines() as i32) {
    return;
  }

  let mut line_offset_graphemes = {
    let line_start_pos = text.line_to_char(char_to_line(text, caret.preferred_column));
    text.slice(line_start_pos..caret.preferred_column).graphemes().count()
  };

  let line = text.line(new_line as usize);
  let new_line_graphemes = line.graphemes().count() - 1;
  if line_offset_graphemes > new_line_graphemes {
    line_offset_graphemes = cmp::max(0, new_line_graphemes);
  }

  let mut pos = 0;
  while line_offset_graphemes > 0 && pos < line.len_chars() {
    pos = line.next_grapheme_boundary(pos);
    line_offset_graphemes -= 1;
  }
  caret.pos = text.line_to_char(new_line as usize) + pos;
}

fn step_up(caret : &mut Caret, text : &Rope, shift_down : bool){
  if !shift_down {
    caret.marker = None;
  }
  line_change(caret, text, -1);
}

fn step_down(caret : &mut Caret, text : &Rope, shift_down : bool){
  if !shift_down {
    caret.marker = None;
  }
  line_change(caret, text, 1);
}

fn copy_text(caret : &Caret, text_buffer : &Rope){
  if let Some(marker) = caret.marker {
    let pos_a = cmp::min(caret.pos, marker);
    let pos_b = cmp::max(caret.pos, marker);
    let s = text_buffer.slice(pos_a..pos_b).to_string();
    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    ctx.set_contents(s).unwrap();
  }
}

fn remove_highlighted_text(caret : &mut Caret, text_buffer : &mut Rope){
  let marker = caret.marker.unwrap();
  let pos_a = cmp::min(caret.pos, marker);
  let pos_b = cmp::max(caret.pos, marker);
  text_buffer.remove(pos_a..pos_b);
  caret.pos = pos_a;
  caret.marker = None;
}

fn insert_text(caret : &mut Caret, text_buffer : &mut Rope, text : &str){
  if caret.marker.is_some() {
    remove_highlighted_text(caret, text_buffer);
  }
  text_buffer.insert(caret.pos, text);
  caret.pos += text.chars().count();
}

fn backspace_text(caret : &mut Caret, text_buffer : &mut Rope){
  if caret.marker.is_some() {
    remove_highlighted_text(caret, text_buffer);
  }
  else {
    if caret.pos == 0 { return; }
    let start = text_buffer.prev_grapheme_boundary(caret.pos);
    text_buffer.remove(start..caret.pos);
    caret.pos = start;
  }
}

struct GraphemePos { line : usize, offset : usize }

fn grapheme_pos(text_buffer : &Rope, char_pos : usize) -> GraphemePos {
  let line = char_to_line(text_buffer, char_pos);
  let line_start_pos = text_buffer.line_to_char(line);
  let offset = text_buffer.slice(line_start_pos..char_pos).graphemes().count();
  GraphemePos{ offset, line }
}

/// indicates how many chars are in the line before control characters like \n or \r
fn count_line_chars(text_buffer : &Rope, line : usize) -> usize {
  let l = text_buffer.line(line);
  let mut end = l.len_chars();
  loop {
    if end <= 0 { return 0; }
    let prev = l.prev_grapheme_boundary(end);
    if l.char(prev).is_control() {
      end = prev;
    }
    else {
      return end;
    }
  }
}

/// count the graphemes in a line before new line characters
fn count_line_graphemes(text_buffer : &Rope, line : usize) -> usize {
  let num_line_chars = count_line_chars(text_buffer, line);
  let line_start_pos = text_buffer.line_to_char(line);
  text_buffer.slice(line_start_pos..(line_start_pos+num_line_chars)).graphemes().count()
}

fn draw_highlight(canvas : &mut Canvas, pos_a : usize, pos_b : usize, text_buffer : &Rope, attribs : &LayoutAttribs) {
  let (pos_a, pos_b) = {
    let a = cmp::min(pos_a, pos_b);
    let b = cmp::max(pos_a, pos_b);
    (a, b)
  };
  let ga = grapheme_pos(text_buffer, pos_a);
  let gb = grapheme_pos(text_buffer, pos_b);
  fn highlight_rect(offset_a : usize, offset_b : usize, line : usize, attribs : &LayoutAttribs) -> Rect {
    let start = (offset_a as f32 * attribs.advance_width) as i32;
    let end = (offset_b as f32 * attribs.advance_width) as i32;
    Rect::new(
      start,
      (line as f32 * attribs.advance_height) as i32,
      (end - start) as u32,
      (attribs.v_metrics.ascent - attribs.v_metrics.descent) as u32)
  }
  if ga.line == gb.line {
    canvas.fill_rect(highlight_rect(ga.offset, gb.offset, ga.line, attribs)).unwrap();
  }
  else{
    canvas.fill_rect(highlight_rect(ga.offset, count_line_graphemes(text_buffer, ga.line), ga.line, attribs)).unwrap();
    if (gb.line - ga.line) > 1 {
      for line in (ga.line+1)..gb.line {
        canvas.fill_rect(highlight_rect(0, count_line_graphemes(text_buffer, line), line, attribs)).unwrap();
      }
    }
    canvas.fill_rect(highlight_rect(0, gb.offset, gb.line, attribs)).unwrap();
  }
}

fn draw_caret(canvas : &mut Canvas, char_pos : usize, text_buffer : &Rope, attribs : &LayoutAttribs){
  let pos = grapheme_pos(text_buffer, char_pos);
  let cursor_rect =
    Rect::new(
      (pos.offset as f32 * attribs.advance_width) as i32,
      (pos.line as f32 * attribs.advance_height) as i32,
      2,
      (attribs.v_metrics.ascent - attribs.v_metrics.descent) as u32);
  canvas.fill_rect(cursor_rect).unwrap();
}

struct Action {
  caret : Caret,
  buffer : String,
}

fn move_caret(editor_state : &mut TextEditorState, caret_move : CaretMove) {
  match caret_move.move_type {
    CaretMoveType::Left => {
      step_left(&mut editor_state.caret, &mut editor_state.buffer, caret_move.highlighting)
    }
    CaretMoveType::Right => {
      step_right(&mut editor_state.caret, &mut editor_state.buffer, caret_move.highlighting)
    }
    CaretMoveType::Up => {
      step_up(&mut editor_state.caret, &mut editor_state.buffer, caret_move.highlighting)
    }
    CaretMoveType::Down => {
      step_down(&mut editor_state.caret, &mut editor_state.buffer, caret_move.highlighting)
    }
  }
}

fn process_action(editor_state : &mut TextEditorState, action : EditAction) {
  match action {
    EditAction::InsertText(text) => {
      let caret_before = editor_state.caret;
      insert_text(&mut editor_state.caret, &mut editor_state.buffer, &text);
      let caret_after = editor_state.caret;
      let edit = TextEdit { caret_before, caret_after, text, edit_type: EditType::Insert };
      editor_state.edit_history.push(edit);
    }
    EditAction::MoveCaret(caret_move) => {
      move_caret(editor_state, caret_move);
    }
    EditAction::Backspace => {
      backspace_text(&mut editor_state.caret, &mut editor_state.buffer);
    }
    EditAction::Delete => {
      
    }
    EditAction::Undo => {
      
    }
    EditAction::Redo => {

    }
  }
}

fn undo(editor_state : &mut TextEditorState){
  if let Some(edit) = editor_state.edit_history.pop() {
    match edit.edit_type {
      EditType::Insert => {
        //backspace_text(caret, text_buffer)
      }
      EditType::Remove => {

      }
    }
  }
}

struct TextEdit {
  caret_before : Caret,
  caret_after : Caret,
  text : String,
  edit_type : EditType,
}

enum EditType {
  Insert, Remove
}

struct TextEditorState {
  buffer : Rope,
  caret : Caret,
  edit_history : Vec<TextEdit>,
  redo_buffer : Vec<TextEdit>,
}

impl TextEditorState {
  fn new(s : &str) -> TextEditorState {
    let mut buffer = Rope::new();
    buffer.insert(0, TEXT);
    TextEditorState {
      buffer,
      caret : Caret {pos : 0, preferred_column : 0, marker : None },
      edit_history : vec!(),
      redo_buffer : vec!(),
    }
  }
}

enum EditAction {
  InsertText(String),
  MoveCaret(CaretMove),
  Backspace,
  Delete,
  Undo,
  Redo,
}

struct CaretMove {
  highlighting : bool,
  move_type : CaretMoveType,
}

enum CaretMoveType {
  Left, Right, Up, Down
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

  let dpi_ratio = dpi_ratio(&window);

  let mut canvas = window.into_canvas().accelerated().build().unwrap();

  canvas.set_blend_mode(BlendMode::Blend);

  canvas.clear();
  canvas.present();

  let mut events = sdl_context.event_pump().unwrap();

  let mut xd = 0;
  let mut yd = 0;

  let font_scale = 12.0;

  let mut rects = vec!();

  // #### Font stuff ####
  let font_data = include_bytes!("../fonts/consola.ttf");
  // TODO: this consolas file does not support all unicode characters.
  // The "msgothic.ttc" font file does, but it's not monospaced.

  let collection = FontCollection::from_bytes(font_data as &[u8]).unwrap_or_else(|e| {
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

  let mut editor = TextEditorState::new(TEXT);

  let mut actions = VecDeque::new();

  // TODO this boolean flag is too simplistic to handle the various ways of highlighting properly

  'mainloop: loop {

    let (shift_down, ctrl_down) = {
      fn is_pressed(keyboard : &KeyboardState, key : Keycode) -> bool {
        keyboard.is_scancode_pressed(Scancode::from_keycode(key).unwrap())
      }
      let keyboard = events.keyboard_state();
      let sd = is_pressed(&keyboard, Keycode::LShift) || is_pressed(&keyboard, Keycode::RShift);
      let cd = is_pressed(&keyboard, Keycode::LCtrl) || is_pressed(&keyboard, Keycode::RCtrl);
      (sd, cd)
    };

    if editor.caret.marker.is_none() && shift_down {
      editor.caret.marker = Some(editor.caret.pos);
    }

    // TODO events.mouse_state();
    fn caret_move(move_type : CaretMoveType, highlighting : bool) -> EditAction {
      EditAction::MoveCaret(CaretMove{ highlighting, move_type })
    }

    for event in events.poll_iter() {
      match event {
        Event::Quit{..} |
        Event::KeyDown {keycode: Some(Keycode::Escape), ..} =>
          break 'mainloop,
        Event::KeyDown {keycode: Some(k), ..} => {
          match k {
            Keycode::Left => {
              actions.push_back(caret_move(CaretMoveType::Left, shift_down));
            }
            Keycode::Right => {
              actions.push_back(caret_move(CaretMoveType::Right, shift_down));
            }
            Keycode::Up => {
              actions.push_back(caret_move(CaretMoveType::Up, shift_down));
            }
            Keycode::Down => {
              actions.push_back(caret_move(CaretMoveType::Down, shift_down));
            }
            Keycode::Backspace => {
              actions.push_back(EditAction::Backspace);
            }
            Keycode::Delete => {
              actions.push_back(EditAction::Backspace);
            }
            Keycode::LShift | Keycode::RShift => {
              if editor.caret.marker.is_none() {
                editor.caret.marker = Some(editor.caret.pos);
              }
            }
            Keycode::C => {
              if ctrl_down && editor.caret.marker.is_some() {
                copy_text(&editor.caret, &editor.buffer);
              }
            }
            Keycode::X => {
              if ctrl_down && editor.caret.marker.is_some() {
                copy_text(&editor.caret, &editor.buffer);
                actions.push_back(EditAction::Backspace);
              }
            }
            Keycode::V => {
              if ctrl_down {
                let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
                if let Ok(s) = ctx.get_contents() {
                  actions.push_back(EditAction::InsertText(s));
                }
              }
            }
            Keycode::Z => {
              if ctrl_down {
                actions.push_back(EditAction::Undo);
              }
            }
            Keycode::Y => {
              if ctrl_down {
                actions.push_back(EditAction::Redo);
              }
            }
            _ => {
            }
          }
        },
        Event::TextInput { text, .. } => {
          actions.push_back(EditAction::InsertText(text));
        },
        Event::TextEditing { text, .. } => {
          if text.len() > 0 {
            actions.push_back(EditAction::InsertText(text));
          }
        },
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
    while let Some(a) = actions.pop_front() {
      process_action(&mut editor, a);
    }

    ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
    // The rest of the loop goes here...

    canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
    canvas.clear();
    canvas.set_draw_color(Color::RGBA(255, 255, 255, 255));
    for r in rects.iter() {
      canvas.fill_rect(*r).unwrap();
    }

    let (rw, rh) = (BOX_W, BOX_H);
    let tx = (width/2) as i32 - (rw/2);
    let ty = (height/2) as i32 - (rh/2);
    let text_rectangle = Rect::new(tx, ty, rw as u32, rh as u32);

    {
      canvas.set_clip_rect(text_rectangle);
      canvas.set_viewport(text_rectangle);

      canvas.fill_rect(Rect::new(0, 0, rw as u32, rh as u32)).unwrap();

      let scale = Scale::uniform(font_scale * dpi_ratio);
      let attribs = layout_attribs(&font, scale, BOX_W as f32);

      canvas.set_draw_color(Color::RGBA(0, 255, 0, 255));
      if let Some(marker) = editor.caret.marker {
        draw_highlight(&mut canvas, editor.caret.pos, marker, &editor.buffer, &attribs);
      }
      else {
        draw_caret(&mut canvas, editor.caret.pos, &editor.buffer, &attribs);
      }

      draw_text(
        &mut canvas, &font, &editor.buffer, &attribs,
        &mut cache, cache_width, cache_height, &mut cache_tex);

      canvas.set_clip_rect(None);
      canvas.set_viewport(None);
    }
    canvas.present();
	}
}

