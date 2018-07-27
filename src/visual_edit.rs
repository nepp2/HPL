/*

TODO:

I have realised that the glyphs for the paragraph don't need to be repositioned every frame.
Retaining their position is a bit messy given that they hold lifetimes.
There's probably no point in optimising this now.

*/

use sdl2;
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
use rand;
use rand::Rng;

use lexer;
use parser;
use interpreter;
use text_edit;


static TEXT: &str = "45 + 58";

/*
"Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";
*/

/*

I now want a scene graph, because I'm moving nodes relative to other nodes.
This is likely to happen more in the future, so it might be worth investing
in the abstraction now. On the other hand, I have made this early investment
mistake repeatedly. Right now it is quite a special case, so maybe I should
forget about it.

If I _were_ to make a scene graph, how would I do it?
- Copy the Unity "transform" style?
- 

*/


struct Node {
  uid : u64,
  parent : Option<u64>,
  bounds : Rect,
}

impl Node {
  const HEADER_HEIGHT : u32 = 20;
}

struct CodeEditor {
  input_node_uid : u64,
  input : TextEditorState,
}

trait RectExt<T> {
    fn subtract_margin(&self, thickness : i32) -> T;
}

impl RectExt<Rect> for Rect {
  fn subtract_margin(&self, thickness : i32) -> Rect {
    let t = (thickness * 2) as u32;
    Rect::new(self.x() + thickness, self.y() + thickness, self.width() - t, self.height() - t)
  }
}

impl CodeEditor {

  fn insert_text(&mut self, edit_history : &mut EditHistory, text : String) {
    let edit = self.input.insert(text);
    edit_history.apply_text_edit(self, edit);
  }

  fn move_caret(&mut self, move_type : CaretMoveType, highlighting : bool) {
    self.input.move_caret(CaretMove{ highlighting, move_type });
  }

  fn backspace(&mut self, edit_history : &mut EditHistory) {
    if let Some(edit) = self.input.backspace() {
      edit_history.apply_text_edit(self, edit);
    }
  }

  fn delete(&mut self, edit_history : &mut EditHistory) {
    if let Some(edit) = self.input.delete() {
      edit_history.apply_text_edit(self, edit);
    }
  }

  fn is_some_text_highlighted(&mut self) -> bool {
    let c = self.input.caret;
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
      let highlighted_string = self.input.get_highlighted_string();
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
    /*
    let s = match interpret(&self.input.buffer.to_string()) {
      Ok(v) => format!("{}", v), Err(e) => e,
    };
    let mut buffer = Rope::new();
    buffer.insert(0, &s);
    self.output.buffer = buffer;
    */
  }
}

#[derive(PartialEq, Clone)]
enum EditMode {
  NoFocusedNode,
  TextEditing(u64),
  Dragging { uid : u64, offset : Point },
}

struct AppState {
  uid_generator : u64,
  nodes : Vec<Node>,
  code_editors : Vec<CodeEditor>,
  edit_history : EditHistory,
  font_scale : f32,
  edit_mode : EditMode,
}

struct NodeEdit {
  uid : u64,
  edit : TextEdit,
}

struct EditHistory {
  undo_buffer : Vec<NodeEdit>,
  redo_buffer : Vec<NodeEdit>,
}

impl EditHistory {
  fn apply_text_edit(&mut self, code_editor : &mut CodeEditor, edit : TextEdit) {
    code_editor.input.apply_edit(&edit);
    self.undo_buffer.push(NodeEdit{ uid: code_editor.input_node_uid, edit });
    self.redo_buffer.clear();
    code_editor.text_changed();
  }
}

impl AppState {

  fn new() -> AppState {
    let font_scale = 16.0;
    let (box_width, box_height) = (400, 300);
    let mut app = AppState {
      uid_generator: 0,
      nodes: vec!(),
      code_editors: vec!(),
      edit_history: EditHistory {
        undo_buffer: vec!(),
        redo_buffer: vec!(),
      },
      font_scale,
      edit_mode: EditMode::NoFocusedNode,
    };
    let bounds = Rect::new(40, 40, box_width as u32, box_height as u32);
    let uid = app.create_code_editor(TEXT, bounds);
    app.edit_mode = EditMode::TextEditing(uid);
    app
  }

  fn create_node(&mut self, bounds : Rect, parent : Option<u64>) -> u64 {
    let uid = self.uid_generator;
    self.uid_generator += 1;
    let node = Node { uid, bounds, parent };
    self.nodes.push(node);
    uid
  }

  fn absolute_bounds(&self, uid : u64) -> Rect {
    let (mut bounds, mut parent_uid) = {
      let n = self.nodes.iter().find(|tn| tn.uid == uid).unwrap();
      (n.bounds, n.parent)
    };
    loop {
      if let Some(puid) = parent_uid {
        if let Some(parent) = self.nodes.iter().find(|tn| tn.uid == puid) {
          let (x, y) = (bounds.x(), bounds.y());
          bounds.set_x(x + parent.bounds.x());
          bounds.set_y(y + parent.bounds.y());
          parent_uid = parent.parent;
          continue;
        }
      }
      return bounds;
    }
  }

  fn create_code_editor(&mut self, text : &str, bounds : Rect) -> u64 {
    let input_node_uid = self.create_node(bounds, None);
    let mut code_editor = CodeEditor {
      input_node_uid,
      input: TextEditorState::new(text),
      //output: TextEditorState::new(""),
    };
    code_editor.text_changed();
    self.code_editors.push(code_editor);
    input_node_uid
  }

  fn handle_event(&mut self, event : &Event, shift_down : bool, ctrl_down : bool) {
    // Handle node events
    //handle_node_bounds_event(uid, self.absolute_bounds(uid), &mut self.edit_mode, event);
    match event {
      &Event::MouseButtonDown {x, y, ..} => {
        let mut clicked = None;
        for n in self.nodes.iter() {
          let b = self.absolute_bounds(n.uid);
          let r = Rect::new(b.x(), b.y(), b.width(), Node::HEADER_HEIGHT);
          if r.contains_point((x, y)) {
            clicked = Some(n);
            self.edit_mode = EditMode::Dragging {
              uid: n.uid, offset: Point::new(x - r.x(), y - r.y()),
            };
            break;
          }
        }
        // TODO: select the node, and bring it to the front
      }
      _e => {}
    }

    /*
    let r = Rect::new(bounds.x(), bounds.y(), bounds.width(), Node::HEADER_HEIGHT);
    if r.contains_point((x, y)) {
      *edit_mode = EditMode::Dragging { uid, offset: Point::new(x - r.x(), y - r.y()) };
    }
    */

    // Handle focused events
    match self.edit_mode {
      EditMode::TextEditing(uid) => {
        let code_editor = self.code_editors.iter_mut().find(|x| x.input_node_uid == uid).unwrap();
        handle_text_editing_event(code_editor, &mut self.edit_history, event, shift_down, ctrl_down)
      }
      EditMode::Dragging { uid, offset } => {
        let mut node = self.nodes.iter_mut().find(|tn| tn.uid == uid).unwrap();
        handle_dragging_event(&mut node, &mut self.edit_mode, event, offset);
      }
      EditMode::NoFocusedNode => (),
    }
  }

  fn undo(&mut self) {
    let history = &mut self.edit_history;
    if let Some(edit) = history.undo_buffer.pop() {
      let node = self.code_editors.iter_mut().find(|x| x.input_node_uid == edit.uid).unwrap();
      node.input.reverse_edit(&edit.edit);
      history.redo_buffer.push(edit);
      self.edit_mode = EditMode::TextEditing(node.input_node_uid);
      node.text_changed();
    }
  }

  fn redo(&mut self) {
    let history = &mut self.edit_history;
    if let Some(edit) = history.redo_buffer.pop() {
      let node = self.code_editors.iter_mut().find(|x| x.input_node_uid == edit.uid).unwrap();
      node.input.apply_edit(&edit.edit);
      history.undo_buffer.push(edit);
      self.edit_mode = EditMode::TextEditing(node.input_node_uid);
      node.text_changed();
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

fn draw_text_node(bounds : Rect, editor : &TextEditorState, font_render : &mut FontRenderState, canvas : &mut Canvas, attribs : &LayoutAttribs, focused : bool, dragging : bool){
    fn content_rect(bounds : Rect) -> Rect {
      Rect::new(
        bounds.x(), bounds.y() + (Node::HEADER_HEIGHT as i32),
        bounds.width(), bounds.height() - Node::HEADER_HEIGHT)
    }

    let back_colour =
      if focused || dragging { Color::RGBA(150, 150, 150, 255) }
      else { Color::RGBA(100, 100, 100, 255) };
    canvas.set_draw_color(back_colour);
    canvas.fill_rect(bounds).unwrap();

    let text_rect = content_rect(bounds).subtract_margin(2);
    canvas.set_draw_color(Color::RGBA(39, 40, 34, 255));
    canvas.fill_rect(text_rect).unwrap();

    let text_rect = text_rect.subtract_margin(4);
    canvas.set_clip_rect(text_rect);
    canvas.set_viewport(text_rect);

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
  canvas.set_draw_color(Color::RGBA(20, 20, 20, 255));
  canvas.clear();

  // draw background lines
  canvas.set_draw_color(Color::RGBA(0, 0, 0, 255));
  let line_interval = 15;
  for x in 0..(width/line_interval) {
    canvas.draw_line(Point::new(x * line_interval, 0), Point::new(x * line_interval, height)).unwrap();
  }
  for y in 0..(height/line_interval) {
    canvas.draw_line(Point::new(0, y * line_interval), Point::new(width, y * line_interval)).unwrap();
  }

  // draw the text nodes
  let attribs = font_render.layout_attribs(app.font_scale);

  for c in app.code_editors.iter() {
    let focus = EditMode::TextEditing(c.input_node_uid) == app.edit_mode;
    let dragging = if let EditMode::Dragging { uid, .. } = app.edit_mode { uid == c.input_node_uid } else { false };
    draw_text_node(app.absolute_bounds(c.input_node_uid), &c.input, font_render, canvas, &attribs, focus, dragging);
    //draw_text_node(app.absolute_bounds(c.output_node_uid), &c.output, font_render, canvas, &attribs, false);
  }

  canvas.present();
}

fn handle_text_editing_event(editor: &mut CodeEditor, edit_history : &mut EditHistory, event : &Event, shift_down : bool, ctrl_down : bool) {
  match event {
    &Event::KeyDown {keycode: Some(k), ..} => {
      match k {
        Keycode::Left => {
          editor.move_caret(CaretMoveType::Left, shift_down);
        }
        Keycode::Right => {
          editor.move_caret(CaretMoveType::Right, shift_down);
        }
        Keycode::Up => {
          editor.move_caret(CaretMoveType::Up, shift_down);
        }
        Keycode::Down => {
          editor.move_caret(CaretMoveType::Down, shift_down);
        }
        Keycode::Return => {
          editor.insert_text(edit_history, "\n".to_string());
        }
        Keycode::Backspace => {
          editor.backspace(edit_history);
        }
        Keycode::Delete => {
          editor.delete(edit_history);
        }
        Keycode::C => {
          if ctrl_down {
            editor.copy_selection();
          }
        }
        Keycode::X => {
          if ctrl_down && editor.is_some_text_highlighted() {
            editor.copy_selection();
            editor.backspace(edit_history);
          }
        }
        Keycode::V => {
          if ctrl_down {
            editor.paste(edit_history);
          }
        }
        _ => {}
      }
    }
    &Event::TextInput { ref text, .. } => {
      editor.insert_text(edit_history, text.to_string());
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

fn handle_dragging_event(node : &mut Node, edit_mode : &mut EditMode, event : &Event, drag_offset : Point) {
  match event {
    &Event::MouseButtonUp {x: _, y: _, ..} => {
      *edit_mode = EditMode::TextEditing(node.uid);
    }
    &Event::MouseMotion {x, y, ..} => {
      node.bounds.set_x(x - drag_offset.x());
      node.bounds.set_y(y - drag_offset.y());
    }
    _e => {}
  }
}

fn generate_app_state(app : &mut AppState) {  
  let mut rng = rand::thread_rng();
  for _ in 0..5 {
    let x = rng.gen_range(0, 1000);
    let y = rng.gen_range(0, 1000);
    let w = rng.gen_range(100, 400);
    let h = rng.gen_range(100, 400);
    let bounds = Rect::new(x, y, w, h);
    app.create_code_editor("butt", bounds);
  }
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

  // #### Font stuff ####
  let font_data : &'static[u8] = include_bytes!("../fonts/consola.ttf");
  // TODO: this consolas file does not support all unicode characters.
  // The "msgothic.ttc" font file does, but it's not monospaced.

  let mut texture_creator = canvas.texture_creator();

  let mut font_render = FontRenderState::new(&mut texture_creator, font_data, dpi_ratio);

  let mut app = AppState::new();

  generate_app_state(&mut app);
  
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

      app.handle_event(&event, shift_down, ctrl_down);
    }

    draw_app(&mut app, width as i32, height as i32, &mut font_render, &mut canvas);

    ::std::thread::sleep(Duration::new(0, 1_000_000_000u32 / 60));
	}
}


