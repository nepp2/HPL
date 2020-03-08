use crate::expr::{StringCache, UIDGenerator, RefStr};
use crate::types::{
  Type, PType, TypeInfo, TypeContent,
  UnitId, SignatureBuilder, SymbolDefinition,
  SymbolInit
};

use PType::*;
use TypeContent::Polytype;

pub fn get_intrinsics(intrinsics_id : UnitId, gen : &mut UIDGenerator, cache : &StringCache) -> TypeInfo {
  let unit_id = intrinsics_id;
  let mut types = TypeInfo::new(unit_id);
  let prim_number_types : &[Type] =
    &[I64.into(), I32.into(), F32.into(), F64.into(),
      U64.into(), U32.into(), U16.into(), U8.into() ];
  let boolean : &Type = &Bool.into();
  for t in prim_number_types {
    add_intrinsic(cache, gen, unit_id, &mut types, "-", &[t], t);
    for &n in &["+", "-", "*", "/", "%"] {
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

  let tvar = cache.get("A");
  for index_type in &[I64.into(), I32.into(), U64.into(), U32.into()] {
    for container in &[Type::ptr_to, Type::array_of] {
      let tv : Type = Polytype(tvar.clone()).into();
      let gcontainer = container(tv.clone());
      let args = &[&gcontainer, index_type];
      add_polymorphic_intrinsic(
        cache, gen, unit_id, &mut types, "Index", args, &tv, vec![tvar.clone()]);
    }
  }
  {
    let tv : Type = Polytype(tvar.clone()).into();
    let gptr = Type::ptr_to(tv.clone());
    add_polymorphic_intrinsic(
      cache, gen, unit_id, &mut types, "*", &[&gptr], &tv, vec![tvar.clone()]);
  }
  {
    let tv : Type = Polytype(tvar.clone()).into();
    let gptr = Type::ptr_to(tv.clone());
    add_polymorphic_intrinsic(
      cache, gen, unit_id, &mut types, "&", &[&tv], &gptr, vec![tvar.clone()]);
  }
  {
    let tv : Type = Polytype(tvar.clone()).into();
    add_polymorphic_intrinsic(
      cache, gen, unit_id, &mut types, "UnsafeZeroInit", &[], &tv, vec![tvar.clone()]);
  }
  types
}

fn create_definition(
  cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, name : &str,
  args : &[&Type], return_type : &Type, type_vars : Vec<RefStr>)
    -> SymbolDefinition
{
  let mut sig = SignatureBuilder::new(return_type.clone());
  for &a in args {
    sig.append_arg(a.clone());
  }
  let id = unit_id.new_symbol_id(gen);
  SymbolDefinition {
    id, unit_id,
    name: cache.get(name),
    type_tag: sig.into(),
    initialiser: SymbolInit::Intrinsic,
    type_vars,
  }
}

fn add_intrinsic(
  cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
  name : &str, args : &[&Type], return_type : &Type)
{
  let def = create_definition(cache, gen, unit_id, name, args, return_type, vec![]);
  t.symbols.insert(def.id, def);
}

fn add_polymorphic_intrinsic(
  cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
  name : &str, args : &[&Type], return_type : &Type, type_vars : Vec<RefStr>)
{
  let def = create_definition(cache, gen, unit_id, name, args, return_type, type_vars);
  t.symbols.insert(def.id, def);
}
