
use ropey::Rope;
use std::cmp;

/*

TODO:

I have not properly understood the distiction between byte, character and grapheme in
the Ropey library. As a result I have been programming quite defensively. I might
be able to simplify some of the code if I look this up. There might be bugs too...

*/

pub mod caret {
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

use text_edit::caret::Caret;

/*
  This is basically a replacement for the "char_to_line" function
  which behaves in a more convenient way for me. The default function
  will imagine a newline at the end of the rope, even when there is no
  newline character. This function very crudely corrects that, but
  should also be treated as suspicious and possibly broken.
*/
pub fn char_to_line(text : &Rope, pos : usize) -> usize {
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

pub struct CaretMove {
  pub highlighting : bool,
  pub move_type : CaretMoveType,
}

pub enum CaretMoveType {
  Left, Right, Up, Down
}

#[derive(Debug)]
pub struct TextEdit {
  caret_before : Caret,
  caret_after : Caret,
  char_index : usize,
  text_deleted : String,
  text_inserted : String,
}

pub struct TextEditorState {
  pub buffer : Rope,
  pub caret : Caret,
}

impl TextEditorState {
  pub fn new(s : &str) -> TextEditorState {
    let mut buffer = Rope::new();
    buffer.insert(0, s);
    TextEditorState {
      buffer,
      caret : Caret::new(),
    }
  }

  pub fn get_highlighted_string(&self) -> String {
    if let Some(marker) = self.caret.marker {
      let (pos_a, pos_b) = order_values(self.caret.pos(), marker);
      self.buffer.slice(pos_a..pos_b).to_string()
    }
    else {
      String::new()
    }
  }

  pub fn move_caret(&mut self, caret_move : CaretMove) {
    let old_pos = self.caret.pos();
    match caret_move.move_type {
      CaretMoveType::Left => {
        step_left(&mut self.caret, &mut self.buffer, caret_move.highlighting)
      }
      CaretMoveType::Right => {
        step_right(&mut self.caret, &mut self.buffer, caret_move.highlighting)
      }
      CaretMoveType::Up => {
        step_up(&mut self.caret, &mut self.buffer, caret_move.highlighting)
      }
      CaretMoveType::Down => {
        step_down(&mut self.caret, &mut self.buffer, caret_move.highlighting)
      }
    }
    // Turn highlighting off if the caret has returned to the marker position
    if let Some(marker) = self.caret.marker {
      if marker == self.caret.pos() {
        self.caret.marker = None;
      }
    }
    // Turn highlighting on if it is off, but the user has moved the caret while holding highlight
    else if caret_move.highlighting && self.caret.pos() != old_pos {
      self.caret.marker = Some(old_pos);
    }
  }

  pub fn apply_edit(&mut self, edit : &TextEdit){
    apply_text_edit(self, edit);
  }

  pub fn reverse_edit(&mut self, edit : &TextEdit){
    reverse_text_edit(self, edit);
  }

  pub fn insert(&self, text_inserted : String) -> TextEdit {
    insert_text_edit(&self.caret, &self.buffer, text_inserted)
  }

  pub fn delete(&self) -> Option<TextEdit> {
    delete_text_edit(&self.caret, &self.buffer, false)
  }

  pub fn backspace(&self) -> Option<TextEdit> {
    delete_text_edit(&self.caret, &self.buffer, true)
  }
}
