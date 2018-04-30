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

Once I'm done with the font stuff I am going to split some of the editing code (undo/redo
buffer, etc) out of text_edit.rs. Then I can put some custom logic in for doing things
like live-interpreting code that is typed into the text field.

I expect the first time I get this working it will immediately crash, as I do almost nothing
to handle errors in the parser or interpreter. It just panics! Hopefully this is easier
to fix in Rust than it was in F#...

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
use sdl2::rect::Rect;
use std::cmp;
use std::time::Duration;
use sdl2::render::BlendMode;
use sdl2::video::{Window};
use ropey::Rope;
use clipboard::{ClipboardProvider, ClipboardContext};
use text_edit::{TextEditorState, CaretMove, CaretMoveType, TextEdit};
use text_edit::caret::Caret;
use font_render::{FontRenderState, LayoutAttribs };


static TEXT: &str = "Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";

pub struct AppState {
  editor : TextEditorState,
  edit_history : Vec<TextEdit>,
  redo_buffer : Vec<TextEdit>,
  editor_rectangle : Rect,
  font_scale : f32,
}

impl AppState {
  pub fn new(editor_rectangle : Rect, font_scale : f32) -> AppState {
    AppState {
      editor: TextEditorState::new(TEXT),
      edit_history: vec!(),
      redo_buffer: vec!(),
      editor_rectangle,
      font_scale,
    }
  }

  fn insert_text(&mut self, text : String) {
    let edit = self.editor.insert(text);
    self.apply_edit(edit);
  }

  fn move_caret(&mut self, move_type : CaretMoveType, highlighting : bool) {
    self.editor.move_caret(CaretMove{ highlighting, move_type });
  }

  fn backspace(&mut self) {
    if let Some(edit) = self.editor.backspace() {
      self.apply_edit(edit);
    }
  }

  fn delete(&mut self) {
    if let Some(edit) = self.editor.delete() {
      self.apply_edit(edit);
    }
  }

  fn apply_edit(&mut self, edit : TextEdit) {
    self.editor.apply_edit(&edit);
    self.edit_history.push(edit);
    self.redo_buffer.clear();
    self.text_changed();
  }

  fn undo(&mut self) {
    if let Some(edit) = self.edit_history.pop() {
      self.editor.reverse_edit(&edit);
      self.redo_buffer.push(edit);
      self.text_changed();
    }
  }

  fn redo(&mut self) {
    if let Some(edit) = self.redo_buffer.pop() {
      self.editor.apply_edit(&edit);
      self.edit_history.push(edit);
      self.text_changed();
    }
  }

  fn is_some_text_highlighted(&mut self) -> bool {
    let c = self.editor.caret;
    if let Some(marker) = c.marker {
      marker != c.pos()
    }
    else {
      false
    }
  }

  fn paste(&mut self){
    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    if let Ok(s) = ctx.get_contents() {
      self.insert_text(s);
    }
  }

  fn copy_selection(&mut self){
    if self.is_some_text_highlighted() {
      let highlighted_string = self.editor.get_highlighted_string();
      if !highlighted_string.is_empty() {
        let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
        ctx.set_contents(highlighted_string).unwrap();
      }
    }
  }

  fn start_highlighting(&mut self){
    if self.editor.caret.marker.is_none() {
      self.editor.caret.marker = Some(self.editor.caret.pos());
    }
  }

  fn interpret(&self) -> Result<f32, String> {
    let text = self.editor.buffer.to_string();
    let tokens = lexer::lex(&text)?;
    let ast = parser::parse(tokens)?;
    let value = interpreter::interpret(ast)?;
    Ok(value)
  }

  /// this is called when the contents of the text editor have been modified
  fn text_changed(&mut self) {
    match self.interpret() {
      Ok(v) => {
        println!("Value is '{}'", v);  
      }
      Err(e) => {
        println!("Error; {}", e);
      }
    };
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

fn draw_app(app : &AppState, font_render : &mut FontRenderState, canvas : &mut Canvas) {
  canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
  canvas.clear();

  {
    let rect = app.editor_rectangle;
    canvas.set_clip_rect(rect);
    canvas.set_viewport(rect);

    canvas.set_draw_color(Color::RGBA(255, 255, 255, 255));
    canvas.fill_rect(Rect::new(0, 0, rect.width(), rect.height())).unwrap();

      // TODO: at the moment this is recalculated every frame. Maybe it shouldn't be.
    let attribs = font_render.layout_attribs(app.font_scale);

    canvas.set_draw_color(Color::RGBA(0, 255, 0, 255));

    let editor = &app.editor;
    if let Some(marker) = editor.caret.marker {
      draw_highlight(canvas, editor.caret.pos(), marker, &editor.buffer, &attribs);
    }
    else {
      draw_caret(canvas, editor.caret.pos(), &editor.buffer, &attribs);
    }

    font_render.draw_text(canvas, &editor.buffer, &attribs);

    canvas.set_clip_rect(None);
    canvas.set_viewport(None);
  }
  canvas.present();
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

  let font_scale = 18.0;

  let (box_width, box_height) = (600, 400);

  // #### Font stuff ####
  let font_data : &'static[u8] = include_bytes!("../fonts/consola.ttf");
  // TODO: this consolas file does not support all unicode characters.
  // The "msgothic.ttc" font file does, but it's not monospaced.

  let mut texture_creator = canvas.texture_creator();

  let mut font_render = FontRenderState::new(&mut texture_creator, font_data, dpi_ratio);

  let editor_rectangle = {
    let tx = (width/2) as i32 - (box_width/2);
    let ty = (height/2) as i32 - (box_height/2);
    Rect::new(tx, ty, box_width as u32, box_height as u32)
  };

  let mut app = AppState::new(editor_rectangle, font_scale);
  
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

    if shift_down {
      app.start_highlighting();
    }

    for event in events.poll_iter() {
      match event {
        Event::Quit{..} |
        Event::KeyDown {keycode: Some(Keycode::Escape), ..} =>
          break 'mainloop,
        Event::KeyDown {keycode: Some(k), ..} => {
          match k {
            Keycode::Left => {
              app.move_caret(CaretMoveType::Left, shift_down);
            }
            Keycode::Right => {
              app.move_caret(CaretMoveType::Right, shift_down);
            }
            Keycode::Up => {
              app.move_caret(CaretMoveType::Up, shift_down);
            }
            Keycode::Down => {
              app.move_caret(CaretMoveType::Down, shift_down);
            }
            Keycode::Backspace => {
              app.backspace();
            }
            Keycode::Delete => {
              app.delete();
            }
            Keycode::C => {
              if ctrl_down {
                app.copy_selection();
              }
            }
            Keycode::X => {
              if ctrl_down && app.is_some_text_highlighted() {
                app.copy_selection();
                app.backspace();
              }
            }
            Keycode::V => {
              if ctrl_down {
                app.paste();
              }
            }
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
        Event::TextInput { text, .. } => {
          app.insert_text(text);
        },
        Event::TextEditing { text, .. } => {
          if text.len() > 0 {
            app.insert_text(text);
          }
        },
        Event::MouseButtonUp {x, y, ..} => {
          // empty
        },
        Event::MouseButtonDown {x, y, ..} => {
          // empty
        },
        Event::Window { win_event, .. } => {
          match win_event {
            WindowEvent::Resized(x, y) => {
              // empty
            },
            _ => {}
          }
        },
        _e => {}
      }
    }

    ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
    // The rest of the loop goes here...

    draw_app(&mut app, &mut font_render, &mut canvas);
	}
}

fn main(){
  run_sdl2_app();
  //parser::test_parse();
  //interpreter::test_interpret();
}

