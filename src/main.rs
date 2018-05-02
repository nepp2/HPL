extern crate sdl2;
extern crate rusttype;
extern crate unicode_normalization;
extern crate ropey;
extern crate clipboard;

/*

TODO:

I have realised that the glyphs for the paragraph don't need to be repositioned every frame.
Retaining their position is a bit messy given that they hold lifetimes.
There's probably no point in optimising this now.

*/

mod font_render;
mod text_edit;
mod lexer;
mod parser;
mod interpreter;

use sdl2::event::Event;
use sdl2::event::WindowEvent;
use sdl2::keyboard::{Keycode, Scancode, KeyboardState};
use sdl2::pixels::Color;
use sdl2::rect::{Rect, Point};
use std::cmp;
use std::time::Duration;
use sdl2::render::BlendMode;
use sdl2::video::{Window};
use ropey::Rope;
use clipboard::{ClipboardProvider, ClipboardContext};
use text_edit::{TextEditorState, CaretMove, CaretMoveType, TextEdit};
use text_edit::caret::Caret;
use font_render::{FontRenderState, LayoutAttribs };


static TEXT: &str = "45 + 58";

/*
"Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";
*/

struct NodePair {
  input : TextNode,
  output : TextNode,
}

struct TextNode {
  editor : TextEditorState,
  bounds : Rect,
}

impl NodePair {
  fn insert_text(&mut self, edit_history : &mut EditHistory, text : String) {
    let edit = self.input.editor.insert(text);
    edit_history.apply_edit(self, edit);
  }

  fn move_caret(&mut self, move_type : CaretMoveType, highlighting : bool) {
    self.input.editor.move_caret(CaretMove{ highlighting, move_type });
  }

  fn backspace(&mut self, edit_history : &mut EditHistory) {
    if let Some(edit) = self.input.editor.backspace() {
      edit_history.apply_edit(self, edit);
    }
  }

  fn delete(&mut self, edit_history : &mut EditHistory) {
    if let Some(edit) = self.input.editor.delete() {
      edit_history.apply_edit(self, edit);
    }
  }

  fn is_some_text_highlighted(&mut self) -> bool {
    let c = self.input.editor.caret;
    if let Some(marker) = c.marker {
      return marker != c.pos()
    }
    return false;
  }

  fn paste(&mut self, edit_history : &mut EditHistory){
    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    if let Ok(s) = ctx.get_contents() {
      self.insert_text(edit_history, s);
    }
  }

  fn copy_selection(&mut self){
    if self.is_some_text_highlighted() {
      let highlighted_string = self.input.editor.get_highlighted_string();
      if !highlighted_string.is_empty() {
        let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
        ctx.set_contents(highlighted_string).unwrap();
      }
    }
  }

  fn text_changed(&mut self) {
    fn interpret(text : &str) -> Result<f32, String> {
      match lexer::lex(text) {
        Ok(tokens) => {
          let ast = parser::parse(tokens)?;
          let value = interpreter::interpret(ast)?;
          Ok(value)
        }
        Err(errors) => {
          Err(format!("{:?}", errors))
        }
      }
    }
    let s = match interpret(&self.input.editor.buffer.to_string()) {
      Ok(v) => format!("{}", v), Err(e) => e,
    };
    let mut buffer = Rope::new();
    buffer.insert(0, &s);
    self.output.editor.buffer = buffer;
  }
}

struct AppState {
  node_pair : NodePair,
  edit_history : EditHistory,
  font_scale : f32,
}

struct EditHistory {
  undo_buffer : Vec<TextEdit>,
  redo_buffer : Vec<TextEdit>,
}

impl EditHistory {
  fn apply_edit(&mut self, node_pair : &mut NodePair, text_edit : TextEdit) {
    node_pair.input.editor.apply_edit(&text_edit);
    self.undo_buffer.push(text_edit);
    self.redo_buffer.clear();
    node_pair.text_changed();
  }
}

impl AppState {

  fn new(text : &str) -> AppState {
    let font_scale = 18.0;
    let (box_width, box_height) = (600, 400);
    let input = TextNode {
      editor: TextEditorState::new(text),
      bounds: Rect::new(50, 50, box_width as u32, box_height as u32),
    };
    let output = TextNode {
      editor: TextEditorState::new(""),
      bounds: Rect::new(box_width + 100, 50, box_width as u32, box_height as u32),
    };
    let mut node_pair = NodePair {
      input,
      output,
    };
    node_pair.text_changed();
    AppState {
      node_pair,
      edit_history : EditHistory {
        undo_buffer: vec!(),
        redo_buffer: vec!(),
      },
      font_scale,
    }
  }

  fn handle_focused_node_event(&mut self, event : &Event, shift_down : bool, ctrl_down : bool) {
    handle_text_node_event(&mut self.node_pair, &mut self.edit_history, event, shift_down, ctrl_down)
  }

  fn undo(&mut self) {
    let history = &mut self.edit_history;
    if let Some(edit) = history.undo_buffer.pop() {
      self.node_pair.input.editor.reverse_edit(&edit);
      history.redo_buffer.push(edit);
      self.node_pair.text_changed();
    }
  }

  fn redo(&mut self) {
    let history = &mut self.edit_history;
    if let Some(edit) = history.redo_buffer.pop() {
      self.node_pair.input.editor.apply_edit(&edit);
      history.undo_buffer.push(edit);
      self.node_pair.text_changed();
    }
  }

}

type Canvas = sdl2::render::Canvas<sdl2::video::Window>;

fn dpi_ratio(w : &Window) -> f32 {
  let (dw, _) = w.drawable_size();
  let (w, _) = w.size();
  (w as f32) / (dw as f32)
}

struct GraphemePos { line : usize, offset : usize }

fn grapheme_pos(text_buffer : &Rope, char_pos : usize) -> GraphemePos {
  let line = text_edit::char_to_line(text_buffer, char_pos);
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

fn draw_text_node(node : &TextNode, font_render : &mut FontRenderState, canvas : &mut Canvas, attribs : &LayoutAttribs, focused : bool){
    let rect = node.bounds;

    let back_rect = rect;
    canvas.set_draw_color(Color::RGBA(100, 100, 100, 255));
    canvas.fill_rect(back_rect).unwrap();

    let text_rect = Rect::new(rect.x() + 2, rect.y() + 22, rect.width() - 4, rect.height() - 24);
    canvas.set_draw_color(Color::RGBA(39, 40, 34, 255));
    canvas.fill_rect(text_rect).unwrap();

    canvas.set_clip_rect(text_rect);
    canvas.set_viewport(text_rect);

    let editor = &node.editor;
    if let Some(marker) = editor.caret.marker {
      if focused {
        canvas.set_draw_color(Color::RGBA(73, 72, 62, 255));
      }
      else {
        canvas.set_draw_color(Color::RGBA(73, 73, 73, 255));
      }
      draw_highlight(canvas, editor.caret.pos(), marker, &editor.buffer, &attribs);
    }
    if focused {
      canvas.set_draw_color(Color::RGBA(230, 219, 116, 255));
      draw_caret(canvas, editor.caret.pos(), &editor.buffer, &attribs);
    }

    font_render.draw_text(canvas, &editor.buffer, &attribs);

    canvas.set_clip_rect(None);
    canvas.set_viewport(None);
}

fn draw_app(app : &AppState, width : i32, height : i32, font_render : &mut FontRenderState, canvas : &mut Canvas) {
  canvas.set_draw_color(Color::RGBA(15, 15, 15, 255));
  canvas.clear();

  canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
  
  //canvas.t

  let line_interval = 15;
  for x in 0..(width/line_interval) {
    canvas.draw_line(Point::new(x * line_interval, 0), Point::new(x * line_interval, height)).unwrap();
  }
  for y in 0..(height/line_interval) {
    canvas.draw_line(Point::new(0, y * line_interval), Point::new(width, y * line_interval)).unwrap();
  }

  // TODO: at the moment this is recalculated every frame. Maybe it shouldn't be.
  let attribs = font_render.layout_attribs(app.font_scale);

  draw_text_node(&app.node_pair.input, font_render, canvas, &attribs, true);
  draw_text_node(&app.node_pair.output, font_render, canvas, &attribs, false);

  canvas.present();
}

fn handle_text_node_event(node : &mut NodePair, edit_history : &mut EditHistory, event : &Event, shift_down : bool, ctrl_down : bool) {
  match event {
    &Event::KeyDown {keycode: Some(k), ..} => {
      match k {
        Keycode::Left => {
          node.move_caret(CaretMoveType::Left, shift_down);
        }
        Keycode::Right => {
          node.move_caret(CaretMoveType::Right, shift_down);
        }
        Keycode::Up => {
          node.move_caret(CaretMoveType::Up, shift_down);
        }
        Keycode::Down => {
          node.move_caret(CaretMoveType::Down, shift_down);
        }
        Keycode::Return => {
          node.insert_text(edit_history, "\n".to_string());
        }
        Keycode::Backspace => {
          node.backspace(edit_history);
        }
        Keycode::Delete => {
          node.delete(edit_history);
        }
        Keycode::C => {
          if ctrl_down {
            node.copy_selection();
          }
        }
        Keycode::X => {
          if ctrl_down && node.is_some_text_highlighted() {
            node.copy_selection();
            node.backspace(edit_history);
          }
        }
        Keycode::V => {
          if ctrl_down {
            node.paste(edit_history);
          }
        }
        _ => {}
      }
    }
    &Event::TextInput { ref text, .. } => {
      node.insert_text(edit_history, text.to_string());
    }
    &Event::TextEditing { text: _, .. } => {
      // TODO: Apparently text editing is just a component of text input, so it might not need to be here.
      //if text.len() > 0 {
      //  app.insert_text(uid, text);
      //}
    }
    _e => {}
  }
}

pub fn run_sdl2_app() {

	let (width, height) = (1800, 900);

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

  // #### Font stuff ####
  let font_data : &'static[u8] = include_bytes!("../fonts/consola.ttf");
  // TODO: this consolas file does not support all unicode characters.
  // The "msgothic.ttc" font file does, but it's not monospaced.

  let mut texture_creator = canvas.texture_creator();

  let mut font_render = FontRenderState::new(&mut texture_creator, font_data, dpi_ratio);

  let mut app = AppState::new(TEXT);
  
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

    for event in events.poll_iter() {
      match &event {
        &Event::Quit{..} |
        &Event::KeyDown {keycode: Some(Keycode::Escape), ..} =>
          break 'mainloop,
        &Event::KeyDown {keycode: Some(k), ..} => {
          match k {
            Keycode::Z => {
              if ctrl_down {
                app.undo();
              }
            }
            Keycode::Y => {
              if ctrl_down {
                app.redo();
              }
            }
            _ => {
            }
          }
        },
        &Event::MouseButtonUp {x: _, y: _, ..} => {
          // empty
        },
        &Event::MouseButtonDown {x: _, y: _, ..} => {
          // empty
        },
        &Event::Window { win_event, .. } => {
          match win_event {
            WindowEvent::Resized(_x, _y) => {
              // empty
            },
            _ => {}
          }
        },
        _e => {}
      }

      app.handle_focused_node_event(&event, shift_down, ctrl_down);
    }

    ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
    // The rest of the loop goes here...

    draw_app(&mut app, width as i32, height as i32, &mut font_render, &mut canvas);
	}
}

fn main(){
  run_sdl2_app();
  //parser::test_parse();
  //interpreter::test_interpret();
}

