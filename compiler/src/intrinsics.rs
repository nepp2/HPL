
use crate::error::TextLocation;
use crate::expr::{StringCache, UIDGenerator, RefStr};
use crate::types::{
  Type, PType, TypeInfo, TypeContent,
  UnitId, SignatureBuilder, SymbolDefinition,
  SymbolInit, TypeDefinition,
};
use crate::structure::{TypeKind, Reference};
use PType::*;
use TypeContent::Polytype;

pub fn get_intrinsics(intrinsics_id : UnitId, gen : &mut UIDGenerator, cache : &StringCache) -> TypeInfo {
  let unit_id = intrinsics_id;
  let mut types = TypeInfo::new(unit_id);

  // Add string type
  add_type_def(
    cache, gen, unit_id, &mut types,
    "string",
    vec![
      ("data", Type::ptr_to(PType::U8.into())),
      ("length", PType::U64.into()),
    ],
    vec![]);

  // Add primitive numerical operations
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

  // Add polymorphic instrinsic operations
  let tvar = cache.get("A");
  let tv : Type = Polytype(tvar.clone()).into();
  let pointer_type = Type::ptr_to(tv.clone());
  let array_type = Type::new(TypeContent::Def(cache.get("array"), unit_id), vec![tv.clone()]);
  for &container in &[&pointer_type, &array_type] {
    for index_type in &[I64.into(), I32.into(), U64.into(), U32.into()] {
      let args = &[container, index_type];
      add_polymorphic_intrinsic(
        cache, gen, unit_id, &mut types, "Index", args, &tv, vec![tvar.clone()]);
    }
  }
  add_polymorphic_intrinsic(
    cache, gen, unit_id, &mut types, "*", &[&pointer_type], &tv, vec![tvar.clone()]);
  add_polymorphic_intrinsic(
    cache, gen, unit_id, &mut types, "&", &[&tv], &pointer_type, vec![tvar.clone()]);
  add_polymorphic_intrinsic(
    cache, gen, unit_id, &mut types, "UnsafeZeroInit", &[], &tv, vec![tvar.clone()]);

  // Add array type
  add_type_def(
    cache, gen, unit_id, &mut types,
    "array",
    vec![
      ("data", pointer_type),
      ("length", PType::U64.into()),
    ],
    vec![tvar]);

  types
}

fn add_type_def(cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
  name : &str, fields: Vec<(&str, Type)>, type_vars : Vec<RefStr>)
{
  let type_def = TypeDefinition {
    name: cache.get(name),
    unit_id,
    kind: TypeKind::Struct,
    fields: fields.into_iter().map(|(name, t)| {
      let reference = Reference { 
        id: gen.next().into(),
        name: cache.get(name),
        loc: TextLocation::zero()
      };
      (reference, t)
    }).collect(),
    type_vars,
  };
  t.type_defs.insert(type_def.name.clone(), type_def);
}

fn create_symbol_def(
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
  let def = create_symbol_def(cache, gen, unit_id, name, args, return_type, vec![]);
  t.symbols.insert(def.id, def);
}

fn add_polymorphic_intrinsic(
  cache : &StringCache, gen : &mut UIDGenerator, unit_id : UnitId, t : &mut TypeInfo,
  name : &str, args : &[&Type], return_type : &Type, type_vars : Vec<RefStr>)
{
  let def = create_symbol_def(cache, gen, unit_id, name, args, return_type, type_vars);
  t.symbols.insert(def.id, def);
}
