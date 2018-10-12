
use value::{RefStr, Value, Type, FunctionSignature, SymbolCache};
use std::collections::HashMap;
use std::rc::Rc;

pub struct IntrinsicDef {
  pub name : RefStr,

  pub signature : Rc<FunctionSignature>,

  /// Reference to the intrinsic function
  pub fn_ref : fn(&[Value]) -> Value,
}

fn intrinsic(sc : &mut SymbolCache, name : &str, args : Vec<Type>, return_type : Type, fn_ref : fn(&[Value]) -> Value) -> IntrinsicDef {
  IntrinsicDef {
    name: sc.symbol(name),
    signature: Rc::new(FunctionSignature { args, return_type }),
    fn_ref,
  }
}

pub fn get_intrinsics(sc : &mut SymbolCache) -> HashMap<RefStr, IntrinsicDef> {
  let intrinsics = vec![
    intrinsic(sc, "print", vec![Type::Any], Type::Unit, |vs| {
      println!("{:?}", vs[0]);
      Value::Unit
    }),
  ];
  let mut m = HashMap::new();
  for i in intrinsics {
    m.insert(i.name.clone(), i);
  }
  m
}

