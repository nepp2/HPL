
use value::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::mem::size_of;

#[derive(Clone)]
pub struct IntrinsicDef {
  pub name : RefStr,

  pub handle : usize,

  pub signature : Rc<FunctionSignature>,

  /// Reference to the intrinsic function
  pub fn_ref : fn(&[Value]) -> Value,
}

struct IntrinsicFactory<'l> {
  sc : &'l mut SymbolCache,
  map : HashMap<RefStr, IntrinsicDef>,
}

impl <'l> IntrinsicFactory<'l> {
  fn add(&mut self, name : &str, args : Vec<Type>, return_type : Type, fn_ref : fn(&[Value]) -> Value) {
    let handle = self.map.len();
    let i = IntrinsicDef {
      name: self.sc.symbol(name),
      handle,
      signature: Rc::new(FunctionSignature { args, return_type }),
      fn_ref,
    };
    self.map.insert(i.name.clone(), i);
  }
}

pub fn get_intrinsics(sc : &mut SymbolCache) -> HashMap<RefStr, IntrinsicDef> {
  let mut i = IntrinsicFactory { sc, map: HashMap::new() };
  i.add("print", vec![Type::Any], Type::Unit, |vs| {
    println!("{:?}", vs[0]);
    Value::Unit
  });
  i.add("size_of_thing", vec![], Type::Float, |_| {
    let s = size_of::<Value>();
    Value::Float(s as f32)
  });
  i.map
}

