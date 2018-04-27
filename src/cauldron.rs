
use text_edit::{TextEditorState, TextEdit, CaretMove};

static TEXT: &str = "Here is some text.\r

cit\u{0065}\u{0301}  <<< this tests grapheme correctness

Feel free to type stuff.\r
And delete it with Backspace.";

pub struct AppState {
  text_edit : TextEditorState,
  edit_history : Vec<TextEdit>,
  redo_buffer : Vec<TextEdit>,
}

impl AppState {
  pub fn new() -> AppState {
    AppState {
      text_edit: TextEditorState::new(TEXT),
      edit_history: vec!(),
      redo_buffer: vec!(),
    }
  }

  pub fn process_action(&mut self, action : EditAction){
    process_action(self, action);
  }
}

pub enum EditAction {
  InsertText(String),
  MoveCaret(CaretMove),
  Backspace,
  Delete,
  Undo,
  Redo,
}

fn process_action(app : &mut AppState, action : EditAction) {
  let editor = &mut app.text_edit;
  match action {
    EditAction::InsertText(text) => {
      let edit = editor.insert(text);
      editor.apply_edit(&edit);
      app.edit_history.push(edit);
      app.redo_buffer.clear();
    }
    EditAction::MoveCaret(caret_move) => {
      editor.move_caret(caret_move);
    }
    EditAction::Backspace => {
      if let Some(edit) = editor.backspace() {
        editor.apply_edit(&edit);
        app.edit_history.push(edit);
        app.redo_buffer.clear();
      }
    }
    EditAction::Delete => {
      if let Some(edit) = editor.delete() {
        editor.apply_edit(&edit);
        app.edit_history.push(edit);
        app.redo_buffer.clear();
      }
    }
    EditAction::Undo => {
      if let Some(edit) = app.edit_history.pop() {
        editor.reverse_edit(&edit);
        app.redo_buffer.push(edit);
      }      
    }
    EditAction::Redo => {
      if let Some(edit) = app.redo_buffer.pop() {
        editor.apply_edit(&edit);
        app.edit_history.push(edit);
      }
    }
  }
}
