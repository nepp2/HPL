use crate::error::TextLocation;
use crate::expr::{StringCache, UIDGenerator};
use crate::types::{
  Type, PType, TypeInfo,
  UnitId, SignatureBuilder, SymbolDefinition,
  PolyTypeId, SymbolInit,
};

pub fn get_intrinsics(gen : &mut UIDGenerator, cache : &StringCache) -> TypeInfo {
  use PType::*;

  fn create_definition(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, name : &str,
    args : &[&Type], return_type : &Type, polymorphic : bool)
      -> SymbolDefinition
  {
    let mut sig = SignatureBuilder::new(return_type.clone());
    for &a in args {
      sig.append_arg(a.clone());
    }
    SymbolDefinition {
      id: gen.next().into(), unit_id,
      name: cache.get(name),
      type_tag: sig.into(),
      initialiser: SymbolInit::Intrinsic,
      polymorphic,
    }
  }

  fn add_intrinsic(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
    name : &str, args : &[&Type], return_type : &Type)
  {
    let g = create_definition(cache, gen, unit_id, name, args, return_type, false);
    t.symbols.insert(g.id, g);
  }
  
  fn add_polymorphic_intrinsic(
    cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
    name : &str, args : &[&Type], return_type : &Type)
  {
    let g = create_definition(cache, gen, unit_id, name, args, return_type, true);
    t.symbols.insert(g.id, g);
  }

  let unit_id = gen.next().into();
  let mut types = TypeInfo::new(unit_id);
  let prim_number_types : &[Type] =
    &[I64.into(), I32.into(), F32.into(), F64.into(),
      U64.into(), U32.into(), U16.into(), U8.into() ];
  let boolean : &Type = &Bool.into();
  for t in prim_number_types {
    add_intrinsic(cache, gen, unit_id, &mut types, "-", &[t], t);
    for &n in &["+", "-", "*", "/"] {
      add_intrinsic(cache, gen, unit_id, &mut types, n, &[t, t], t);
    }
    for &n in &["==", ">", "<", ">=", "<=", "!="] {
      add_intrinsic(cache, gen, unit_id, &mut types, n, &[t, t], boolean);
    }
  }
  for &n in &["&&", "||"] {
    add_intrinsic(cache, gen, unit_id, &mut types, n, &[boolean, boolean], boolean);
  }
  add_intrinsic(cache, gen, unit_id, &mut types, "!", &[boolean], boolean);

  for prim in &[I64.into(), I32.into(), U64.into(), U32.into()] {
    for container in &[Type::ptr_to, Type::array_of] {
      let gid : PolyTypeId = gen.next().into();
      let gt : Type = gid.into();
      let gcontainer = container(gt.clone());
      let args = &[&gcontainer, prim];
      add_polymorphic_intrinsic(cache, gen, unit_id, &mut types, "Index", args, &gt);
    }
  }
  {
    let gid : PolyTypeId = gen.next().into();
    let gt : Type = gid.into();
    let gptr = Type::ptr_to(gt.clone());
    add_polymorphic_intrinsic(cache, gen, unit_id, &mut types, "*", &[&gptr], &gt);
  }
  {
    let gid : PolyTypeId = gen.next().into();
    let gt : Type = gid.into();
    let gptr = Type::ptr_to(gt.clone());
    add_polymorphic_intrinsic(cache, gen, unit_id, &mut types, "&", &[&gt], &gptr);
  }
  types
}

#[derive(Clone, PartialEq, Debug)]
pub enum Val {
  Void,
  F64(f64),
  F32(f32),
  I64(i64),
  U64(u64),
  I32(i32),
  U32(u32),
  U16(u16),
  U8(u8),
  String(String),
  Bool(bool),
}
