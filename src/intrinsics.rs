
use value::{RefStr, Value, Type, FunctionSignature, SymbolCache};
use std::collections::HashMap;
use std::rc::Rc;

pub struct IntrinsicInfo {
  pub name : RefStr,

  /// Number of arguments the function accepts
  pub arguments : Vec<(RefStr, Type)>,

  pub return_type : Type,

  /// Reference to the intrinsic function
  pub fn_ref : fn(&[Value]) -> Option<Value>,
}

pub fn get_intrinsics(symbol_cache : &mut SymbolCache) -> HashMap<RefStr, Rc<FunctionSignature>> {
  let print = FunctionSignature {
    return_type: Type::Unit,
    args: vec![Type::Any],
  };
  let mut m = HashMap::new();
  m.insert(symbol_cache.symbol("print"), Rc::new(print));
  m
}

