extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;

mod lexer;
mod parser;

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

static TEXT: &str = "Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";

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

mod caret {
  #[derive(Copy, Clone, Debug)]
  pub struct Caret {
    position : usize,
    pub preferred_column : Option<usize>,
    // tracks highlighting
    pub marker : Option<usize>,
  }

  impl Caret {
    pub fn new() -> Caret{
      Caret {
        position: 0,
        preferred_column: None,
        marker: None,
      }
    }

    /// also resets preferred column
    pub fn set_pos(&mut self, pos : usize) {
      self.position = pos;
      self.preferred_column = None;
    }

    pub fn set_pos_and_preferred_column(&mut self, pos : usize, preferred_column : usize) {
      self.position = pos;
      self.preferred_column = Some(preferred_column);
    }

    pub fn pos(&self) -> usize {
      self.position
    }
  }
}

use caret::Caret;

fn step_right(caret : &mut Caret, text : &Rope, shift_down : bool){
  if let Some(m) = caret.marker {
    if !shift_down {
      // dehighlight and jump to the right of the highlighted region
      caret.marker = None;
      let pos = cmp::max(m, caret.pos());
      caret.set_pos(pos);
      return;
    }
  }
  // else, move the caret right
  if caret.pos() < text.len_chars() {
    let pos = text.next_grapheme_boundary(caret.pos());
    caret.set_pos(pos);
  }
}

fn step_left(caret : &mut Caret, text : &Rope, shift_down : bool){
  if let Some(m) = caret.marker {
    if !shift_down {
      // dehighlight and jump to the left of the highlighted region
      caret.marker = None;
      let pos = cmp::min(m, caret.pos());
      caret.set_pos(pos);
      return;
    }
  }
  // else, move the caret left
  if caret.pos() > 0 {
    let pos = text.prev_grapheme_boundary(caret.pos());
    caret.set_pos(pos);
  }
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
  let new_line = char_to_line(text, caret.pos()) as i32 + dir;
  if new_line < 0 || new_line >= (text.len_lines() as i32) {
    return;
  }

  let preferred_column = caret.preferred_column.unwrap_or(caret.pos());
  let mut line_offset_graphemes = {
    let line_start_pos = text.line_to_char(char_to_line(text, preferred_column));
    text.slice(line_start_pos..preferred_column).graphemes().count()
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
  pos = text.line_to_char(new_line as usize) + pos;
  let old_pos = caret.pos();
  caret.set_pos_and_preferred_column(pos, old_pos);
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
    let (pos_a, pos_b) = order_values(caret.pos(), marker);
    let s = text_buffer.slice(pos_a..pos_b).to_string();
    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    ctx.set_contents(s).unwrap();
  }
}

/// returns a and b in ascending order
fn order_values(a : usize, b : usize) -> (usize, usize) {
  (cmp::min(a, b), cmp::max(a, b))
}

fn remove_highlighted_text(caret : &mut Caret, text_buffer : &Rope) -> String {
  let (pos_a, pos_b) = order_values(caret.pos(), caret.marker.unwrap());
  let deleted_string = text_buffer.slice(pos_a..pos_b).to_string();
  caret.set_pos(pos_a);
  caret.marker = None;
  deleted_string
}

fn insert_text_edit(caret : &Caret, text_buffer : &Rope, text_inserted : String) -> TextEdit {
  let caret_before = *caret;
  let mut caret = *caret;
  let text_deleted =
    if caret.marker.is_some() {
      remove_highlighted_text(&mut caret, text_buffer)
    }
    else{
      String::new()
    };
  let char_index = caret.pos();
  let pos = caret.pos() + text_inserted.chars().count();
  caret.set_pos(pos);
  TextEdit{
    caret_before, caret_after: caret,
    text_deleted, text_inserted, char_index
  }
}

fn delete_text_edit(caret : &Caret, text_buffer : &Rope, is_backspace : bool) -> Option<TextEdit> {
  let caret_before = *caret;
  let mut caret = *caret;
  let text_deleted =
    if caret.marker.is_some() {
      remove_highlighted_text(&mut caret, text_buffer)
    }
    else {
      let delete_to =
      if is_backspace { text_buffer.prev_grapheme_boundary(caret.pos()) }
      else { text_buffer.next_grapheme_boundary(caret.pos()) };
      let (pos_a, pos_b) = order_values(delete_to, caret.pos());
      caret.set_pos(pos_a);
      text_buffer.slice(pos_a..pos_b).to_string()
    };
  if text_deleted.len() > 0 {
    let char_index = caret.pos();
    let caret_after = caret;
    let text_inserted = String::new();
    Some(TextEdit{ caret_before, caret_after, text_deleted, text_inserted, char_index })
  }
  else { None }
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

fn apply_text_edit(editor_state : &mut TextEditorState, edit : &TextEdit){
  let start = edit.char_index;
  if edit.text_deleted.len() > 0 {
    let end_delete = start + edit.text_deleted.chars().count();
    editor_state.buffer.remove(start..end_delete);
  }
  if edit.text_inserted.len() > 0 {
    editor_state.buffer.insert(start, &edit.text_inserted);
  }
  editor_state.caret = edit.caret_after;
}

fn reverse_text_edit(editor_state : &mut TextEditorState, edit : &TextEdit){
  let start = edit.char_index;
  if edit.text_inserted.len() > 0 {
    let end_delete = start + edit.text_inserted.chars().count();
    editor_state.buffer.remove(start..end_delete);
  }
  if edit.text_deleted.len() > 0 {
    editor_state.buffer.insert(start, &edit.text_deleted);
  }
  editor_state.caret = edit.caret_before;
}

fn process_action(editor_state : &mut TextEditorState, action : EditAction) {
  match action {
    EditAction::InsertText(text) => {
      let edit = insert_text_edit(&editor_state.caret, &editor_state.buffer, text);
      apply_text_edit(editor_state, &edit);
      editor_state.edit_history.push(edit);
      editor_state.redo_buffer.clear();
    }
    EditAction::MoveCaret(caret_move) => {
      move_caret(editor_state, caret_move);
    }
    EditAction::Backspace => {
      if let Some(edit) = delete_text_edit(&editor_state.caret, &editor_state.buffer, true) {
        apply_text_edit(editor_state, &edit);
        editor_state.edit_history.push(edit);
        editor_state.redo_buffer.clear();
      }
    }
    EditAction::Delete => {
      if let Some(edit) = delete_text_edit(&editor_state.caret, &editor_state.buffer, false) {
        apply_text_edit(editor_state, &edit);
        editor_state.edit_history.push(edit);
        editor_state.redo_buffer.clear();
      }
    }
    EditAction::Undo => {
      if let Some(edit) = editor_state.edit_history.pop() {
        reverse_text_edit(editor_state, &edit);
        editor_state.redo_buffer.push(edit);
      }      
    }
    EditAction::Redo => {
      if let Some(edit) = editor_state.redo_buffer.pop() {
        apply_text_edit(editor_state, &edit);
        editor_state.edit_history.push(edit);
      }
    }
  }
}

#[derive(Debug)]
struct TextEdit {
  caret_before : Caret,
  caret_after : Caret,
  char_index : usize,
  text_deleted : String,
  text_inserted : String,
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
    buffer.insert(0, s);
    TextEditorState {
      buffer,
      caret : Caret::new(),
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

pub fn run_sdl2_app() {

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

  let font_scale = 18.0;

  let (box_width, box_height) = (600, 400);

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
      editor.caret.marker = Some(editor.caret.pos());
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
              actions.push_back(EditAction::Delete);
            }
            Keycode::LShift | Keycode::RShift => {
              if editor.caret.marker.is_none() {
                editor.caret.marker = Some(editor.caret.pos());
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

    let tx = (width/2) as i32 - (box_width/2);
    let ty = (height/2) as i32 - (box_height/2);
    let text_rectangle = Rect::new(tx, ty, box_width as u32, box_height as u32);

    {
      canvas.set_clip_rect(text_rectangle);
      canvas.set_viewport(text_rectangle);

      canvas.fill_rect(Rect::new(0, 0, box_width as u32, box_height as u32)).unwrap();

      let scale = Scale::uniform(font_scale * dpi_ratio);
      let attribs = layout_attribs(&font, scale);

      canvas.set_draw_color(Color::RGBA(0, 255, 0, 255));
      if let Some(marker) = editor.caret.marker {
        draw_highlight(&mut canvas, editor.caret.pos(), marker, &editor.buffer, &attribs);
      }
      else {
        draw_caret(&mut canvas, editor.caret.pos(), &editor.buffer, &attribs);
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

fn main(){
  //run_sdl2_app();
  parser::test_parse();
}
