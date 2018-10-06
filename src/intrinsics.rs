
use value::{RefStr, Value, Type};

pub struct IntrinsicInfo {
  pub name : RefStr,

  /// Number of arguments the function accepts
  pub arguments : Vec<(RefStr, Type)>,

  pub return_type : Type,

  /// Reference to the intrinsic function
  pub fn_ref : fn(&[Value]) -> Option<Value>,
}
