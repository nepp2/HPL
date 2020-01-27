
// TODO: Carlos says I should have more comments than the occasional TODO

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::RefStr;

use crate::structure::{
  Node, NodeId, Nodes, Content, PrimitiveVal, TypeKind, ReferenceId,
  LabelId, NodeValueType, VarScope, Reference };
use crate::types::{
  Type, PType, TypeDefinition, SymbolInit, SymbolId, TypeMapping,
  SymbolDefinition, TypeInfo, TypeContent, UnitId };
use crate::code_store::CodeStore;
use crate::llvm_compile::SymbolLocation;

use std::collections::HashMap;

use inkwell::AddressSpace;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context};
use inkwell::module::{Module, Linkage};
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::passes::PassManager;
use inkwell::types::{
  BasicTypeEnum, BasicType, StructType, PointerType, FunctionType, AnyTypeEnum, ArrayType,
  IntType, FloatType };
use inkwell::values::{
  BasicValueEnum, BasicValue, FloatValue, StructValue, IntValue,
  FunctionValue, PointerValue, GlobalValue };
use inkwell::{FloatPredicate, IntPredicate};
use inkwell::targets::TargetData;

pub fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

// TODO: maybe add this macro to a utils lib?
// macro_rules! unwrap_enum {
//   ( $enum_name:ident, $variant_name:ident, $v:expr) => { 
//     if let $enum_name::$variant_name(x) = $v { x } else { panic!() }
//   };
// }

/// Indicates whether a value is a pointer to the stack,
/// or stored directly in a register.
#[derive(PartialEq, Clone, Copy)]
enum Storage {
  Register,
  Pointer,
}

/// Either holds a gen val or represents void
enum MaybeVal {
  IsVal(GenVal),
  Void,
}

use MaybeVal::*;

impl MaybeVal {
  fn unwrap(self) -> GenVal {
    match self { IsVal(gv) => gv, Void => panic!("expected value, found void.") }
  }
}

/// Represents an SSA value in some LLVM IR. Might be stored directly in an LLVM register,
/// or might be a pointer to somewhere on the stack/heap.
#[derive(PartialEq)]
struct GenVal {
  storage : Storage,
  value : BasicValueEnum,
}

impl Into<MaybeVal> for GenVal {
  fn into(self) -> MaybeVal {
    IsVal(self)
  }
}

fn reg(value : BasicValueEnum) -> GenVal {
  GenVal { storage: Storage::Register, value }
}

fn pointer(ptr : PointerValue) -> GenVal {
  GenVal { storage: Storage::Pointer, value: ptr.as_basic_value_enum() }
}

fn const_zero(t : BasicTypeEnum) -> BasicValueEnum {
  use BasicTypeEnum::*;
  match t {
    FloatType(t) => t.const_zero().into(),
    IntType(t) => t.const_zero().into(),
    ArrayType(t) => t.const_zero().into(),
    PointerType(t) => t.const_null().into(),
    StructType(t) => t.const_zero().into(),
    VectorType(t) => t.const_zero().into(),
  }
}

fn basic_type(t : AnyTypeEnum) -> Option<BasicTypeEnum> {
  use AnyTypeEnum::*;
  let bt = match t {
    FloatType(t) => t.as_basic_type_enum(),
    IntType(t) => t.as_basic_type_enum(),
    ArrayType(t) => t.as_basic_type_enum(),
    PointerType(t) => t.as_basic_type_enum(),
    StructType(t) => t.as_basic_type_enum(),
    VectorType(t) => t.as_basic_type_enum(),
    VoidType(_t) => return None,
    FunctionType(_t) => return None,
  };
  Some(bt)
}

fn name_basic_type(t : &BasicValueEnum, s : &str) {
  use BasicValueEnum::*;
  match t {
    ArrayValue(v) => v.set_name(s),
    IntValue(v) => v.set_name(s),
    FloatValue(v) => v.set_name(s),
    PointerValue(v) => v.set_name(s),
    StructValue(v) => v.set_name(s),
    VectorValue(v) => v.set_name(s),
  }
}

#[derive(Copy, Clone)]
enum ShortCircuitOp { And, Or }

/// Code generates a module
pub struct Gen<'l> {
  context: &'l Context,
  module : &'l mut Module,
  target_data : &'l TargetData,

  /// Globals that need linking when the execution engine is created
  globals_to_link: &'l mut Vec<(GlobalValue, SymbolLocation)>,

  /// Functions that need linking when the execution engine is created
  functions_to_link: &'l mut Vec<(FunctionValue, SymbolLocation)>,

  struct_types: HashMap<RefStr, StructType>,

  pm : &'l PassManager<FunctionValue>,
}

#[derive(Clone, Copy)]
struct Destructible {
  value : PointerValue,
  drop_reference : FunctionValue,
}

struct Block {
  destructibles : Vec<Destructible>,
}

impl Block {
  fn new() -> Self {
    Block { destructibles: vec![] }
  }
}

struct LabelState {
  /// Indicates how many blocks there are beneath this label
  block_depth : usize,

  exit_block : BasicBlock,
  phi_values : Vec<(BasicValueEnum, BasicBlock)>,
}

/// Code generates a single function (can spawn children to code-generate internal functions)
pub struct GenFunction<'l, 'a> {
  gen : &'l mut Gen<'a>,
  builder: Builder,

  // the llvm function being populated
  fn_val : FunctionValue,

  variables: HashMap<ReferenceId, PointerValue>,

  blocks: Vec<Block>,

  /// stack of labels in scopes and their state
  labels_in_scope: Vec<(LabelId, LabelState)>,
}

pub struct CompileInfo<'l> {
  code_store : &'l CodeStore,
  t : &'l TypeInfo,
  nodes : &'l Nodes,
  mapping : &'l TypeMapping,
}

impl <'l> CompileInfo<'l> {

  pub fn new(
    code_store : &'l CodeStore,
    t : &'l TypeInfo,
    nodes : &'l Nodes,
    mapping : &'l TypeMapping,
  )
      -> Self 
  {
    CompileInfo { code_store, t, nodes, mapping }
  }

  fn typed_node(&self, nid : NodeId) -> TypedNode {
    let node = self.nodes.node(nid);
    TypedNode { info: self, node }
  }

  fn symbol_def(&self, symbol_id : SymbolId) -> &SymbolDefinition {
    self.code_store.symbol_def(symbol_id)
  }

  fn symbol_node(&self, unit_id : UnitId, symbol_id : SymbolId) -> &Node {
    let mapping  = self.code_store.type_mapping(unit_id);
    let node_id = *mapping.symbol_def_nodes.get(&symbol_id).unwrap();
    self.code_store.nodes(unit_id).node(node_id)
  }

  fn find_type_def(&self, name : &str, unit_id : UnitId) -> Option<&TypeDefinition> {
    if self.t.unit_id == unit_id { return self.t.find_type_def(name) }
    self.code_store.types(unit_id).find_type_def(name)
  }

  fn get_global_def(&self, unit_id : UnitId, global_id : SymbolId) -> Option<&SymbolDefinition> {
    if self.t.unit_id == unit_id {
      self.t.symbols.get(&global_id)
    }
    else {
      self.code_store.types(unit_id).symbols.get(&global_id)
    }
  }
}

#[derive(Clone, Copy)]
struct TypedNode<'l> {
  info : &'l CompileInfo<'l>,
  node : &'l Node,
}

impl <'l> Into<TextLocation> for TypedNode<'l> {
  fn into(self) -> TextLocation {
    self.node.loc
  }
}

impl <'l> TypedNode<'l> {
  fn type_tag(&self) -> &Type {
    self.info.mapping.node_type.get(&self.node.id).unwrap()
  }

  fn get(&self, nid : NodeId) -> TypedNode {
    self.info.typed_node(nid.into())
  }

  fn node_value_type(&self) -> NodeValueType {
    self.node.content.node_value_type()
  }

  fn content(&self) -> &'l Content {
    &self.node.content
  }

  fn sizeof_type(&self) -> Option<&Type> {
    self.info.mapping.sizeof_info.get(&self.node.id)
  }

  fn node_symbol_def(&self) -> Option<&SymbolDefinition> {
    let symbol_id = *self.info.mapping.symbol_references.get(&self.node.id)?;
    let def = self.info.symbol_def(symbol_id);
    Some(def)
  }

  fn node_type_def(&self) -> Option<&TypeDefinition> {
    if let TypeContent::Def(name, unit_id) = &self.type_tag().content {
      return self.info.find_type_def(name, *unit_id);
    }
    None
  }

  fn is_intrinsic_function(&self) -> bool {
    self.node_symbol_def()
    .map(|def| if let SymbolInit::Intrinsic = def.initialiser { true } else { false })
    .unwrap_or(false)
  }
}

impl <'l> Gen<'l> {

  pub fn new(
    context: &'l Context,
    module : &'l mut Module,
    target_data : &'l TargetData,
    globals_to_link: &'l mut Vec<(GlobalValue, SymbolLocation)>,
    functions_to_link: &'l mut Vec<(FunctionValue, SymbolLocation)>,
    pm : &'l PassManager<FunctionValue>,
  )
      -> Gen<'l>
  {
    Gen {
      context, module,
      target_data,
      globals_to_link,
      functions_to_link,
      struct_types: HashMap::new(),
      pm,
    }
  }

  /// Code-generates a module, returning a reference to the top-level function in the module
  pub fn codegen_module(mut self, info : &'l CompileInfo) -> Result<(), Error> {
    // Declare all the globals and functions
    let mut functions_to_codegen = vec!();
    for def in info.t.symbols.values() {
      if !def.is_polymorphic() {
        let t = self.to_basic_type(info, &def.type_tag).unwrap();
        match &def.initialiser {
          SymbolInit::CBind => {
            let loc = info.symbol_node(def.unit_id, def.id).loc;
            let symloc = SymbolLocation::CBind(def.name.clone());
            if let Some(sig) = def.type_tag.sig() {
              let f = self.codegen_prototype(info, def.name.as_ref(), sig.return_type, None, sig.args);
              self.functions_to_link.push((f, symloc));
            }
            else {
              let gv = self.module.add_global(t, Some(AddressSpace::Generic), &def.name);
              self.globals_to_link.push((gv, symloc));
            }
          }
          SymbolInit::Expression(_node) => {
            self.add_global(const_zero(t), false, &def.name);
            let aaa = (); // Do static initialisation where possible
            // let v = self.codegen_static(info.typed_node(node_id))?;
            // self.add_global(v, false, &name);
          }
          SymbolInit::Function(init) => {
            let sig = def.type_tag.sig().unwrap();
            let f =
              self.codegen_prototype(
                info, init.name_for_codegen.as_ref(), sig.return_type,
                Some(&init.args), sig.args);
            functions_to_codegen.push((f, init.args.as_slice(), init.body));
          }
          SymbolInit::Intrinsic => (),
        }
      }
    }

    // codegen the functions
    for (p, args, body) in functions_to_codegen {
      self.codegen_function(p, info.typed_node(body), args)?;
    }

    Ok(())
  }

  fn codegen_prototype(
    &mut self,
    info : &CompileInfo,
    name : &str,
    return_type : &Type,
    args : Option<&[Reference]>,
    arg_types : &[Type])
      -> FunctionValue
  {
    let fn_type = self.to_function_type(info, arg_types, return_type);
    let function = self.module.add_function(name, fn_type, None);

    // let i : u32 = !0; //LLVMAttributeFunctionIndex;
    // TODO: is this equivalent to the old line above?
    let i = AttributeLoc::Function;
    //function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("norecurse"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("nounwind"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("nonlazybind"), 0));
    //function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("readnone"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("uwtable"), 0));
    function.add_attribute(i, self.context.create_string_attribute("probe-stack", "__rust_probestack"));
    function.add_attribute(i, self.context.create_string_attribute("target-cpu", "x86-64"));

    // set arguments names
    if let Some(args) = args {
      for (i, arg) in function.get_param_iter().enumerate() {
        name_basic_type(&arg, args[i].name.as_ref());
      }
    }
    function
  }

  fn codegen_function(
    &mut self,
    prototype_handle : FunctionValue,
    body : TypedNode<'l>,
    args : &[Reference])
      -> Result<FunctionValue, Error>
  {
    // this function is here because Rust doesn't have a proper try/catch yet
    fn generate(body : TypedNode, args : &[Reference], genf : &mut GenFunction)
      -> Result<(), Error>
    {
      let function = genf.fn_val;
      let entry = genf.gen.context.append_basic_block(&function, "entry");

      genf.builder.position_at_end(&entry);

      // set function parameters
      for (arg_value, arg_symbol) in function.get_param_iter().zip(args) {
        genf.init_local_var(arg_symbol.id, &arg_symbol.name, arg_value);
      }

      // compile body and emit return
      genf.codegen_return(Some(body))?;

      // return the whole thing after verification and optimization
      if function.verify(true) {
        genf.gen.pm.run_on(&function);
        Ok(())
      }
      else {
        error(body, "invalid generated function.")
      }
    }

    let builder = self.context.create_builder();
    let mut gen_function = GenFunction::new(self, builder, prototype_handle);

    match generate(body, args, &mut gen_function) {
      Ok(_) => Ok(prototype_handle),
      Err(e) => {
        dump_module(self.module);
        // This library uses copy semantics for a resource can be deleted,
        // because it is usually not deleted. As a result, it's possible to
        // get use-after-free bugs, so this operation is unsafe. I'm sure
        // this design could be improved.
        unsafe {
          prototype_handle.delete();
        }
        Err(e)
      }
    }
  }

  fn codegen_static(&mut self, node : TypedNode) -> Result<BasicValueEnum, Error> {
    use TypeContent::*;
    use PType::*;
    let v = match node.content() {
      Content::Literal(v) => {
        match v {
          PrimitiveVal::Float(f) => {
            match &node.type_tag().content {
              Prim(F64) => self.context.f64_type().const_float(*f).into(),
              Prim(F32) => self.context.f32_type().const_float(*f as f64).into(),
              _ => panic!("primitive type error {}", node.type_tag()),
            }
          }
          PrimitiveVal::Int(i) => {
            match &node.type_tag().content {
              // TODO the signed values should maybe pass "true" here?
              Prim(I64) => self.context.i64_type().const_int(*i as u64, false).into(),
              Prim(I32) => self.context.i32_type().const_int(*i as u64, false).into(),
              Prim(U64) => self.context.i64_type().const_int(*i as u64, false).into(),
              Prim(U32) => self.context.i32_type().const_int(*i as u64, false).into(),
              Prim(U16) => self.context.i16_type().const_int(*i as u64, false).into(),
              Prim(U8) => self.context.i8_type().const_int(*i as u64, false).into(),
              _ => panic!("primitive type error {}", node.type_tag()),
            }
            
          }
          PrimitiveVal::Bool(b) =>
            self.context.bool_type().const_int(if *b { 1 } else { 0 }, false).into(),
          PrimitiveVal::Void => {
            return error(node, "static variables cannot be void");
          },
          PrimitiveVal::String(_s) => {
            return error(node, "static strings not supported");
          }
        }
      }
      _ => {
        return error(node, "unsupported construct in static initialiser");
      }
    };
    Ok(v)
  }

  // special case for handling struct/union fields to prevent infinite recursion
  fn to_basic_type_no_cycle(&mut self, info : &CompileInfo, t : &Type) -> Option<BasicTypeEnum> {
    match &t.content {
      TypeContent::Ptr => {
        let t = self.context.i8_type().ptr_type(AddressSpace::Generic);
        Some(t.into())
      }
      _ => {
        self.to_basic_type(info, t)
      }
    }
  }

  fn to_basic_type(&mut self, info : &CompileInfo, t : &Type) -> Option<BasicTypeEnum> {
    match &t.content {
      TypeContent::Prim(t) => {
        match t {
          PType::Void => None,
          PType::F64 => Some(self.context.f64_type().into()),
          PType::F32 => Some(self.context.f32_type().into()),
          PType::I64 => Some(self.context.i64_type().into()),
          PType::I32 => Some(self.context.i32_type().into()),
          PType::U64 => Some(self.context.i64_type().into()),
          PType::U32 => Some(self.context.i32_type().into()),
          PType::U16 => Some(self.context.i16_type().into()),
          PType::U8 => Some(self.context.i8_type().into()),
          PType::Bool => Some(self.context.bool_type().into()),
        }
      }
      TypeContent::Fun => {
        let sig = t.sig().unwrap();
        let t = self.to_function_type(info, sig.args.as_ref(), &sig.return_type);
        Some(t.ptr_type(AddressSpace::Generic).into())
      }
      TypeContent::Def(name, unit_id) => {
        if let Some(def) = info.find_type_def(name, *unit_id) {
          Some(self.composite_type(info, &def).as_basic_type_enum())
        }
        else {
          panic!("type `{}` not found", name);
        }
      }
      TypeContent::Array => {
        let t = t.array().unwrap();
        Some(self.bounded_array_type(info, t).into())
      }
      TypeContent::Ptr => {
        let t = t.ptr().unwrap();
        let bt = self.to_basic_type(info, t);
        Some(self.pointer_to_type(bt).into())
      }
      TypeContent::Polytype(_) => panic!(),
      TypeContent::Abstract(_) => panic!(),
    }
  }

  /// Creates an array struct roughly like this:
  /// 
  /// struct array(T) {
  ///   ptr : ptr(T)
  ///   length : u64
  /// }
  /// 
  fn bounded_array_type(&mut self, info : &CompileInfo, t : &Type) -> StructType {
    let bt = self.to_basic_type(info, t);
    let t = self.pointer_to_type(bt).into();
    let i64_type = self.context.i64_type();
    self.context.struct_type(&[t, i64_type.into()], false)
  }

  fn to_function_type(&mut self, info : &CompileInfo, arg_types : &[Type], return_type : &Type) -> FunctionType {
    let arg_types =
      arg_types.iter().map(|t| self.to_basic_type(info, t).unwrap())
      .collect::<Vec<BasicTypeEnum>>();
    let arg_types = arg_types.as_slice();

    let return_type = self.to_basic_type(info, return_type);
    self.function_type(return_type, arg_types)
  }

  fn function_type(&self, return_type : Option<BasicTypeEnum>, arg_types : &[BasicTypeEnum])
    -> FunctionType
  {
    if let Some(return_type) = return_type {
      use BasicTypeEnum::*;
      match return_type {
        ArrayType(t) => t.fn_type(arg_types, false),
        IntType(t) => t.fn_type(arg_types, false),
        FloatType(t) => t.fn_type(arg_types, false),
        PointerType(t) => t.fn_type(arg_types, false),
        StructType(t) => t.fn_type(arg_types, false),
        VectorType(t) => t.fn_type(arg_types, false),
      }
    }
    else {
      self.context.void_type().fn_type(arg_types, false)
    }
  }

  fn array_of_type(&self, t : BasicTypeEnum, length : u32) -> ArrayType {
    use BasicTypeEnum::*;
    match t {
      ArrayType(t) => t.array_type(length),
      IntType(t) => t.array_type(length),
      FloatType(t) => t.array_type(length),
      PointerType(t) => t.array_type(length),
      StructType(t) => t.array_type(length),
      VectorType(t) => t.array_type(length),
    }
  }

  fn size_of_type(&self, t : Option<BasicTypeEnum>) -> IntValue {
    if let Some(t) = t {
    use BasicTypeEnum::*;
      match t {
        ArrayType(t) => t.size_of().unwrap(),
        IntType(t) => t.size_of(),
        FloatType(t) => t.size_of(),
        PointerType(t) => t.size_of(),
        StructType(t) => t.size_of().unwrap(),
        VectorType(t) => t.size_of().unwrap(),
      }
    }
    else {
      self.context.i64_type().const_zero()
    }
  }

  fn pointer_to_type(&self, t : Option<BasicTypeEnum>) -> PointerType {
    if let Some(t) = t {
    use BasicTypeEnum::*;
      match t {
        ArrayType(t) => t.ptr_type(AddressSpace::Generic),
        IntType(t) => t.ptr_type(AddressSpace::Generic),
        FloatType(t) => t.ptr_type(AddressSpace::Generic),
        PointerType(t) => t.ptr_type(AddressSpace::Generic),
        StructType(t) => t.ptr_type(AddressSpace::Generic),
        VectorType(t) => t.ptr_type(AddressSpace::Generic),
      }
    }
    else {
      self.context.i8_type().ptr_type(AddressSpace::Generic)
    }
  }

  fn composite_type(&mut self, info : &CompileInfo, def : &TypeDefinition) -> StructType {
    if let Some(t) = self.struct_types.get(&def.name) {
      return *t;
    }
    let t = match def.kind {
      TypeKind::Struct => {
        let types =
          def.fields.iter().map(|(_, t)| {
            self.to_basic_type_no_cycle(info, t).unwrap()
          })
          .collect::<Vec<BasicTypeEnum>>();
        self.context.struct_type(&types, false)
      }
      TypeKind::Union => {
        let mut union_bitwidth = 0;
        let mut bt : Option<BasicTypeEnum> = None;
        let mut widest_alignment = 0;
        for (_, t) in def.fields.iter() {
          if let Some(t) = self.to_basic_type_no_cycle(info, t) {
            let alignment = self.target_data.get_preferred_alignment(&t);
            if alignment > widest_alignment {
              widest_alignment = alignment;
              bt = Some(t)
            }
            let width = self.target_data.get_bit_size(&t);
            if width > union_bitwidth {
              union_bitwidth = width;
            }
          }
        }
        if let Some(t) = bt {
          let val_bitwidth = self.target_data.get_bit_size(&t);
          assert!(union_bitwidth >= val_bitwidth);
          let difference = union_bitwidth - val_bitwidth;
          assert!(difference % 8 == 0);
          let padding = self.context.i8_type().array_type(difference as u32 / 8);
          self.context.struct_type(&[t, padding.into()], true)
        }
        else {
          let padding = self.context.i8_type().array_type(union_bitwidth as u32 / 8);
          self.context.struct_type(&[padding.into()], true)
        }
      }
    };
    self.struct_types.insert(def.name.clone(), t);
    return t;
  }

  fn add_global(&mut self, initial_value : BasicValueEnum, is_constant : bool, name : &str) -> PointerValue {
    let gv = self.module.add_global(initial_value.get_type(), Some(AddressSpace::Generic), name);
    gv.set_initializer(&initial_value);
    gv.set_constant(is_constant);
    gv.set_linkage(Linkage::Internal);
    //gv.set_alignment(8); // TODO: is this needed?
    gv.as_pointer_value()
  }
}

macro_rules! codegen_type {
  (PointerValue, $e:ident, $gen:ident) => { $gen.codegen_pointer($e) };
  (FloatValue, $e:ident, $gen:ident) => { $gen.codegen_float($e) };
  (IntValue, $e:ident, $gen:ident) => { $gen.codegen_int($e) };
}

macro_rules! convert_op {
  ($op_name:ident, $type_name:ident, $type_width:expr, $a:ident, $gen:ident) => {
    {
      let a = codegen_type!($type_name, $a, $gen)?;
      let t = $type_width;
      let v = ($gen).builder.$op_name(a, t, "conversion_result");
      reg(v.into())
    }
  }
}

macro_rules! binary_op {
  ($op_name:ident, $gen:ident, $a:ident, $b:ident) => {
    {
      let fv = ($gen).builder.$op_name($a, $b, "op_result");
      Ok(reg(fv.into()))
    }
  }
}

macro_rules! unary_op {
  ($op_name:ident, $type_name:ident, $gen:ident, $a:ident) => {
    {
      let a = codegen_type!($type_name, $a, $gen)?;
      let v = ($gen).builder.$op_name(a, "op_result");
      reg(v.into())
    }
  }
}

macro_rules! compare_op {
  ($op_name:ident, $pred:expr, $gen:ident, $a:ident, $b:ident) => {
    {
      let fv = ($gen).builder.$op_name($pred, $a, $b, "cpm_result");
      Ok(reg(fv.into()))
    }
  }
}

fn float_binary_ops(gf : &mut GenFunction, name: &str, a : TypedNode, b : TypedNode)
  -> Result<GenVal, Error>
{
  let a = gf.codegen_float(a)?;
  let b = gf.codegen_float(b)?;
  match name {
    "+" => binary_op!(build_float_add, gf, a, b),
    "-" => binary_op!(build_float_sub, gf, a, b),
    "*" => binary_op!(build_float_mul, gf, a, b),
    "/" => binary_op!(build_float_div, gf, a, b),
    ">" => compare_op!(build_float_compare, FloatPredicate::OGT, gf, a, b),
    ">=" => compare_op!(build_float_compare, FloatPredicate::OGE, gf, a, b),
    "<" => compare_op!(build_float_compare, FloatPredicate::OLT, gf, a, b),
    "<=" => compare_op!(build_float_compare, FloatPredicate::OLE, gf, a, b),
    "==" => compare_op!(build_float_compare, FloatPredicate::OEQ, gf, a, b),
    _ => panic!("invalid intrinsic"),
  }
}

fn integer_binary_ops(
  gf : &mut GenFunction, name: &str,
  node_a : TypedNode, node_b : TypedNode
) -> Result<GenVal, Error>
{
  let t = node_a.type_tag();
  let a = gf.codegen_int(node_a)?;
  let b = gf.codegen_int(node_b)?;
  match name {
    "+" => binary_op!(build_int_add, gf, a, b),
    "-" => binary_op!(build_int_sub, gf, a, b),
    "*" => binary_op!(build_int_mul, gf, a, b),
    "/" => {
      if t.signed_int() {
        binary_op!(build_int_signed_div, gf, a, b)
      }
      else {
        binary_op!(build_int_unsigned_div, gf, a, b)
      }
    }
    ">" => compare_op!(build_int_compare, IntPredicate::SGT, gf, a, b),
    ">=" => compare_op!(build_int_compare, IntPredicate::SGE, gf, a, b),
    "<" => compare_op!(build_int_compare, IntPredicate::SLT, gf, a, b),
    "<=" => compare_op!(build_int_compare, IntPredicate::SLE, gf, a, b),
    "==" => compare_op!(build_int_compare, IntPredicate::EQ, gf, a, b),
    "!=" => compare_op!(build_int_compare, IntPredicate::NE, gf, a, b),
    _ =>
      panic!("invalid intrinsic '{} {} {}'",
        node_a.type_tag(), name, node_b.type_tag()),
  }
}

fn codegen_index(
  gf : &mut GenFunction, container : TypedNode, index : TypedNode)
    -> Result<MaybeVal, Error>
{
  let ptr = match (&container.type_tag().content, index.type_tag().int()) {
    (TypeContent::Ptr, true) => {
      gf.codegen_pointer(container)?
    }
    (TypeContent::Array, true) => {
      // TODO: add bounds checks
      let array = gf.codegen_struct(container)?;
      gf.builder.build_extract_value(array, 0, "array_pointer")
        .unwrap().into_pointer_value()
    }
    _ => panic!("unsupported index intrinsic"),
  };
  let index = gf.codegen_int(index)?;
  let element_ptr = unsafe { gf.builder.build_gep(ptr, &[index], "element_ptr") };
  return Ok(pointer(element_ptr).into());
}

fn codegen_intrinsic_call(gf : &mut GenFunction, node : TypedNode, name : &str, args : &[NodeId])
  -> Result<MaybeVal, Error>
{
  use TypeContent::*;
  use PType::*;
  let gv : GenVal = if let [a, b] = args {
    let (a, b) = (node.get(*a), node.get(*b));
    if name == "Index" {
      return codegen_index(gf, a, b);
    }
    let (ta, tb) = (a.type_tag(), b.type_tag());
    if ta != tb {
      panic!("invalid intrinsic {} {} {}", ta, name, tb);
    }
    if ta.float() {
      float_binary_ops(gf, name, a, b)?
    }
    else if ta.int() {
      integer_binary_ops(gf, name, a, b)?
    }
    else if ta.content == Prim(Bool) {
      match name {
        "&&" => gf.codegen_short_circuit_op(a, b, ShortCircuitOp::And)?,
        "||" => gf.codegen_short_circuit_op(a, b, ShortCircuitOp::Or)?,
        _ => panic!("invalid intrinsic"),
      }
    }
    else {
      return error(node,
        format!("encountered unrecognised intrinsic, {} {} {}.",
          a.type_tag(), name, b.type_tag()));
    }
  }
  else if let [a] = args {
    let a = node.get(*a);
    match (&a.type_tag().content, name) {
      (Prim(F64), "-") => unary_op!(build_float_neg, FloatValue, gf, a),
      (Prim(I64), "-") => unary_op!(build_int_neg, IntValue, gf, a),
      (Prim(Bool), "!") => unary_op!(build_not, IntValue, gf, a),
      (Ptr, "*") => {
        let ptr = gf.codegen_pointer(a)?;
        pointer(ptr)
      }
      (_, "&") => gf.codegen_address_of_expression(a)?,
      _ => return error(node, "encountered unrecognised intrinsic"),
    }
  }
  else {
    return error(node, "encountered unrecognised intrinsic");
  };
  Ok(gv.into())
}

impl <'l, 'a> GenFunction<'l, 'a> {

  pub fn new(gen: &'l mut Gen<'a>, builder : Builder, fn_val : FunctionValue) -> GenFunction<'l, 'a> {
    let variables = HashMap::new();
    GenFunction{ gen, fn_val, builder, variables, blocks: vec![Block::new()], labels_in_scope: vec![] }
  }

  fn create_entry_block_alloca(&self, t : BasicTypeEnum, name : &str) -> PointerValue {
    let current_block = self.builder.get_insert_block().unwrap();
    let function = self.fn_val;
    let entry = function.get_first_basic_block().unwrap();
    match entry.get_first_instruction() {
      Some(fi) => self.builder.position_before(&fi),
      None => self.builder.position_at_end(&entry),
    }
    let pointer = self.builder.build_alloca(t, name);
    self.builder.position_at_end(&current_block);
    pointer
  }

  fn init_local_var(&mut self, var_id : ReferenceId, name: &str, value : BasicValueEnum) {
    let pointer = self.create_entry_block_alloca(value.get_type(), name);
    self.builder.build_store(pointer, value);
    self.add_var_pointer_to_scope(var_id, pointer);
  }

  fn init_global_var(&mut self, name : &str, value : BasicValueEnum) {
    let gv = self.gen.module.get_global(name).unwrap();
    let pointer = gv.as_pointer_value();
    self.builder.build_store(pointer, value);
  }

  fn add_var_pointer_to_scope(&mut self, id : ReferenceId, pointer : PointerValue) {
    if self.variables.contains_key(&id) { 
      panic!("variable initialised twice!");
    }
    self.variables.insert(id, pointer);
  }

  fn codegen_value(&mut self, n : TypedNode) -> Result<BasicValueEnum, Error> {
    Ok(self.codegen_expression_to_register(n)?.unwrap())
  }

  fn codegen_float(&mut self, n : TypedNode) -> Result<FloatValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::FloatValue(f) => Ok(f),
      t => error(n, format!("Expected float, found {:?}", t)),
    }
  }

  fn codegen_struct(&mut self, n : TypedNode) -> Result<StructValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::StructValue(sv) => Ok(sv),
      t => error(n, format!("Expected struct, found {:?}", t)),
    }
  }

  fn codegen_int(&mut self, n : TypedNode) -> Result<IntValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::IntValue(i) => Ok(i),
      t => error(n, format!("Expected int, found {:?}", t)),
    }
  }

  fn codegen_pointer(&mut self, n : TypedNode) -> Result<PointerValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::PointerValue(p) => Ok(p),
      t => error(n, format!("Expected pointer, found {:?}", t)),
    }
  }

  fn codegen_expression_to_register(&mut self, n : TypedNode) -> Result<Option<BasicValueEnum>, Error> {
    let v = self.codegen_expression(n)?;
    Ok(self.maybeval_to_register(v))
  }

  fn maybeval_to_register(&mut self, v : MaybeVal) -> Option<BasicValueEnum> {
    if let IsVal(v) = v {
      Some(self.genval_to_register(v))
    }
    else {
      None
    }
  }

  fn genval_to_register(&mut self, v : GenVal) -> BasicValueEnum {
    match v.storage {
      Storage::Pointer => {
        let ptr = *v.value.as_pointer_value();
        self.builder.build_load(ptr, "stack_value")
      }
      Storage::Register => {
        v.value
      }
    }
  }

  fn codegen_convert(&mut self, convert_node : TypedNode, value_to_convert : TypedNode) -> Result<GenVal, Error> {
    fn int_type(gen : &Gen, width : u64) -> IntType {
      match width {
        1 => gen.context.bool_type(),
        8 => gen.context.i8_type(),
        16 => gen.context.i16_type(),
        32 => gen.context.i32_type(),
        64 => gen.context.i64_type(),
        128 => gen.context.i128_type(),
        _ => panic!(),
      }
    }
    fn float_type(gen : &Gen, width : u64) -> FloatType {
      match width {
        16 => gen.context.f16_type(),
        32 => gen.context.f32_type(),
        64 => gen.context.f64_type(),
        128 => gen.context.f128_type(),
        _ => panic!(),
      }
    }
    let info = convert_node.info;
    let from_type = value_to_convert.type_tag();
    let to_type = convert_node.type_tag();
    let from_llvm_type = self.gen.to_basic_type(info, from_type).ok_or_else(|| error_raw(value_to_convert, "can't cast from void"))?;
    let to_llvm_type = self.gen.to_basic_type(info, to_type).ok_or_else(|| error_raw(convert_node, "can't cast to void"))?;
    let n = value_to_convert;
    
    let from_float = from_type.float();
    let from_signed = from_type.signed_int();
    let from_unsigned = from_type.unsigned_int();
    let from_int = from_signed || from_unsigned;
    let from_width = self.gen.target_data.get_bit_size(&from_llvm_type);
    let from_pointer = from_type.pointer();

    let to_float = to_type.float();
    let to_signed = to_type.signed_int();
    let to_unsigned = to_type.unsigned_int();
    let to_int = to_signed || to_unsigned;
    let to_width = self.gen.target_data.get_bit_size(&to_llvm_type);
    let to_pointer = to_type.pointer();

    // Pointer casts
    if from_pointer && to_unsigned {
      let t = int_type(&self.gen, to_width);
      return Ok(convert_op!(build_ptr_to_int, PointerValue, t, n, self));
    }
    if from_unsigned && to_pointer {
      let t = *self.gen.to_basic_type(info, to_type).unwrap().as_pointer_type();
      return Ok(convert_op!(build_int_to_ptr, IntValue, t, n, self));
    }
    if from_pointer && to_pointer {
      let t = *self.gen.to_basic_type(info, to_type).unwrap().as_pointer_type();
      return Ok(convert_op!(build_pointer_cast, PointerValue, t, n, self));
    }

    // truncate
    if to_width < from_width {
      if from_int && to_int {
        let t = int_type(&self.gen, to_width);
        return Ok(convert_op!(build_int_truncate, IntValue, t, n, self));
      }
      if from_float && to_float {
        let t = float_type(&self.gen, to_width);
        return Ok(convert_op!(build_float_trunc, FloatValue, t, n, self));
      }
    }
    // extend
    if to_width > from_width {
      if from_signed && to_int {
        let t = int_type(&self.gen, to_width);
        return Ok(convert_op!(build_int_s_extend, IntValue, t, n, self));
      }
      if from_unsigned && to_int {
        let t = int_type(&self.gen, to_width);
        return Ok(convert_op!(build_int_z_extend, IntValue, t, n, self));
      }
      if from_float && to_float {
        let t = float_type(&self.gen, to_width);
        return Ok(convert_op!(build_float_ext, FloatValue, t, n, self));
      }
    }
    // same-width int casts
    if to_width == from_width && from_int && to_int {
      let v = self.codegen_value(n)?;
      return Ok(reg(v));
    }
    // float/int conversions
    if from_signed && to_float {
      let t = float_type(&self.gen, to_width);
      return Ok(convert_op!(build_signed_int_to_float, IntValue, t, n, self));
    }
    if from_unsigned && to_float {
      let t = float_type(&self.gen, to_width);
      return Ok(convert_op!(build_unsigned_int_to_float, IntValue, t, n, self));
    }
    if from_float && to_signed {
      let t = int_type(&self.gen, to_width);
      return Ok(convert_op!(build_float_to_signed_int, FloatValue, t, n, self));
    }
    if from_float && to_unsigned {
      let t = int_type(&self.gen, to_width);
      return Ok(convert_op!(build_float_to_unsigned_int, FloatValue, t, n, self));
    }
    return error(convert_node, "type cast not supported");
  }

  fn codegen_short_circuit_op(&mut self, a : TypedNode, b : TypedNode, op : ShortCircuitOp)
    -> Result<GenVal, Error>
  {
    use ShortCircuitOp::*;
    let short_circuit_outcome = match op {
      And => self.gen.context.bool_type().const_int(0, false),
      Or => self.gen.context.bool_type().const_int(1, false),
    };
    // create basic blocks
    let f = self.fn_val;
    let b_start_block = self.gen.context.append_basic_block(&f, "b_block");
    let end_block = self.gen.context.append_basic_block(&f, "end");
    // compute a
    let a_value = self.codegen_int(a)?;
    let a_end_block = self.builder.get_insert_block().unwrap();
    match op {
      And => self.builder.build_conditional_branch(a_value, &b_start_block, &end_block),
      Or => self.builder.build_conditional_branch(a_value, &end_block, &b_start_block),
    };
    // maybe compute b
    self.builder.position_at_end(&b_start_block);
    let b_value = self.codegen_int(b)?;
    let b_end_block = self.builder.get_insert_block().unwrap();
    self.builder.build_unconditional_branch(&end_block);
    // end block
    self.builder.position_at_end(&end_block);
    let phi = self.builder.build_phi(self.gen.context.bool_type(), "result");
    phi.add_incoming(&[
      (&short_circuit_outcome, &a_end_block),
      (&b_value, &b_end_block),
    ]);
    return Ok(reg(phi.as_basic_value()));
  }

  fn codegen_struct_initialise(&mut self, info : &CompileInfo, def : &TypeDefinition, args : &[BasicValueEnum]) -> GenVal {
    let t = self.gen.composite_type(info, def);
    let mut sv = t.get_undef();
    for (i, v) in args.iter().enumerate() {
      let field_val = if let BasicValueEnum::PointerValue(pv) = v {
        // Cast all pointer types to void before assigning to struct fields
        let void_ptr_type = self.gen.context.i8_type().ptr_type(AddressSpace::Generic);
        self.builder.build_pointer_cast(*pv, void_ptr_type, "void_cast").into()
      }
      else {
        *v
      };
      sv = self.builder.build_insert_value(sv, field_val, i as u32, "insert_field").unwrap().into_struct_value();
    }
    reg(sv.into())
  }

  fn codegen_union_initialise(&mut self, info : &CompileInfo, def : &TypeDefinition, val : BasicValueEnum) -> GenVal {
    let union_type = self.gen.composite_type(info, def).as_basic_type_enum();
    let ptr = self.create_entry_block_alloca(union_type, &def.name);
    let variant_type = self.gen.pointer_to_type(Some(val.get_type()));
    let variant_ptr = self.builder.build_pointer_cast(ptr, variant_type, "union_cast");
    self.builder.build_store(variant_ptr, val);
    pointer(ptr)
  }

  fn codegen_address_of_genval(&mut self, v : GenVal) -> Result<PointerValue, Error> {
    match v.storage {
      Storage::Register => {
        let ptr = self.create_entry_block_alloca(v.value.get_type(), "reference");
        self.builder.build_store(ptr, v.value);
        Ok(ptr)
      }
      Storage::Pointer => {
        Ok(*v.value.as_pointer_value())
      }
    }
  }

  fn codegen_address_of_expression(&mut self, value : TypedNode) -> Result<GenVal, Error> {
    let v = self.codegen_expression(value)?.unwrap();
    Ok(reg(self.codegen_address_of_genval(v)?.into()))
  }

  /// ensure necessary definitions are inserted and linking operations performed when a global is referenced
  fn get_linked_global_value(&mut self, node : TypedNode, def : &SymbolDefinition) -> GenVal {
    let info = node.info;
    // Replace any polymorphic def with the correct monomorphic instance
    let def = if def.is_polymorphic() {
      let id = info.code_store.poly_instance(def.id, node.type_tag()).unwrap();
      let def = info.symbol_def(id);
      def
    }
    else {
      def
    };
    match def.initialiser {
      SymbolInit::Expression(_) => {
        let gv = self.get_linked_global_reference(info, def);
        pointer(gv.as_pointer_value())
      }
      SymbolInit::Function(_) => {
        let fv = self.get_linked_function_reference(info, def);
        reg(fv.as_global_value().as_pointer_value().into())
      }
      SymbolInit::CBind => {
        if let Some(sig) = def.type_tag.sig() {
          let fv = if let Some(local_f) = self.gen.module.get_function(&def.name) {
            local_f
          }
          else {
            let f = self.gen.codegen_prototype(info, &def.name, sig.return_type, None, sig.args);
            let loc = info.symbol_node(def.unit_id, def.id).loc;
            let symloc = SymbolLocation::CBind(def.name.clone());
            self.gen.functions_to_link.push((f, symloc));
            f
          };
          reg(fv.as_global_value().as_pointer_value().into())
        }
        else {
          let gv = self.get_linked_global_reference(info, def);
          pointer(gv.as_pointer_value())
        }
      }
      SymbolInit::Intrinsic => {
        panic!("cannot get reference to intrinsic");
      }
    }
  }

  /// ensure necessary definitions are inserted and linking operations performed when a global is referenced
  fn get_linked_global_reference(&mut self, info: &CompileInfo, def : &SymbolDefinition) -> GlobalValue {
    // Check if it was already added
    if let Some(gv) = self.gen.module.get_global(&def.name) {
      gv
    }
    // Else find and include it
    else {
      let t = self.gen.to_basic_type(info, &def.type_tag).unwrap();
      let gv = self.gen.module.add_global(t, Some(AddressSpace::Generic), &def.name);
      let symloc = SymbolLocation::Global(def.unit_id, def.id);
      self.gen.globals_to_link.push((gv, symloc));
      gv
    }
  }

  fn get_linked_function_reference(&mut self, info: &CompileInfo, def : &SymbolDefinition) -> FunctionValue {
    if def.is_polymorphic() {
      panic!("{} {}", "Tried to get the address of a polymorphic function definition.",
        "This will always fail, and means there is a bug somewhere earlier in the pipeline.");
    }
    match &def.initialiser {
      SymbolInit::Function(init) => {
        // Check if it was already added
        if let Some(f) = self.gen.module.get_function(&init.name_for_codegen) {
          f
        }
        // Else find and include it
        else {
          let sig = def.type_tag.sig().unwrap();
          let f = self.gen.codegen_prototype(info, &init.name_for_codegen, sig.return_type, Some(&init.args), sig.args);
          let symloc = SymbolLocation::Function(def.unit_id, def.id);
          self.gen.functions_to_link.push((f, symloc));
          f
        }
      }
      _ => panic!("expected function initialiser"),
    }
  }

  fn build_function_call(&mut self, f : PointerValue, args : &[BasicValueEnum], name : &str) -> MaybeVal {
    let call = self.builder.build_call(f, args, name);
    let r = call.try_as_basic_value().left();
    return r.map(reg).map(IsVal).unwrap_or(Void);
  }

  fn codegen_function_call(&mut self, node : TypedNode, function : TypedNode, args : &[NodeId])
    -> Result<MaybeVal, Error>
  {
    // Check if it's an intrinsic
    if function.is_intrinsic_function() {
      let name = &function.node_symbol_def().unwrap().name;
      return codegen_intrinsic_call(self, node, name, args);
    }

    // Check if it's a static call or a function value
    let function_pointer = if let Some(def) = node.node_symbol_def() {
      let v = self.get_linked_global_value(node, &def);
      *self.genval_to_register(v).as_pointer_value()
    }
    else {
      self.codegen_pointer(function)?
    };
    let mut arg_vals = vec!();
    for &a in args.iter() {
      let a = node.get(a);
      let v = self.codegen_value(a)?;
      arg_vals.push(v);
    }
    Ok(self.build_function_call(function_pointer, arg_vals.as_slice(), "return_val"))
  }

  fn get_linked_drop_reference(&mut self, info : &CompileInfo, t : &Type) -> Option<FunctionValue> {
    if let TypeContent::Def(name, unit_id) = &t.content {
      let def = info.find_type_def(name, *unit_id).unwrap();
      if let Some(drop) = &def.drop_function {
        let drop_def = info.symbol_def(drop.symbol_id);
        return Some(self.get_linked_function_reference(info, drop_def));
      }
    }
    None
  }

  fn get_linked_clone_reference(&mut self, info : &CompileInfo, t : &Type) -> Option<FunctionValue> {
    if let TypeContent::Def(name, unit_id) = &t.content {
      let def = info.find_type_def(name, *unit_id).unwrap();
      if let Some(clone) = &def.clone_function {
        let clone_def = info.symbol_def(clone.symbol_id);
        return Some(self.get_linked_function_reference(info, clone_def));
      }
    }
    None
  }

  /// Makes sure newly created values that need to be dropped are registered with the block that they
  /// were created in. This means they must have an address on the stack.
  fn codegen_drop_value_registration(&mut self, node : TypedNode, v : MaybeVal) -> Result<MaybeVal, Error> {
    if node.node_value_type() == NodeValueType::Owned {
      if let Some(drop_reference) = self.get_linked_drop_reference(node.info, node.type_tag()) {
        if drop_reference != self.fn_val {
          // do not auto-drop recursively
          let p = self.codegen_address_of_genval(v.unwrap())?;
          let d = Destructible{ drop_reference, value: p };
          self.blocks.last_mut().unwrap().destructibles.push(d);
          return Ok(pointer(p).into());
        }
      }
    }
    return Ok(v);
  }

  fn codegen_cloned_expression(&mut self, info : &CompileInfo, t : &Type, val : MaybeVal) -> Result<MaybeVal, Error> {
    if let Some(clone) = self.get_linked_clone_reference(info, t) {
      // do not auto-clone recursively
      if clone != self.fn_val {
        let val = self.codegen_address_of_genval(val.unwrap())?;
        let fun_ptr = clone.as_global_value().as_pointer_value();
        return Ok(self.build_function_call(fun_ptr, &[val.into()], "cloned"));
      }
    }
    Ok(val)
  }

  fn codegen_owned_expression(&mut self, node : TypedNode) -> Result<MaybeVal, Error> {
    let val = self.codegen_without_drop_value_registration(node)?;
    if node.node_value_type() == NodeValueType::Owned {
      Ok(val)
    }
    else {
      self.codegen_cloned_expression(node.info, node.type_tag(), val)
    }
  }

  fn codegen_drop_value(&mut self, d : Destructible) {
    let fp = d.drop_reference.as_global_value().as_pointer_value();
    self.build_function_call(fp, &[d.value.into()], "void");
  }


  fn codegen_expression(&mut self, node : TypedNode) -> Result<MaybeVal, Error> {
    let v = self.codegen_without_drop_value_registration(node)?;
    return self.codegen_drop_value_registration(node, v);
  }

  fn codegen_without_drop_value_registration(&mut self, node : TypedNode) -> Result<MaybeVal, Error> {
    let info = node.info;
    let v : GenVal = match node.content() {
      Content::FunctionCall{ function, args } => {
        return self.codegen_function_call(node, node.get(*function), args);
      }
      Content::SizeOf{ .. } => {
        let sizeof_type = node.sizeof_type().expect("sizeof node has no type associated with it");
        let t = self.gen.to_basic_type(info, &sizeof_type);
        reg(self.gen.size_of_type(t).into())
      }
      Content::Convert{ from_value, .. } => {
        self.codegen_convert(node, node.get(*from_value))?
      }
      Content::While{ condition, body } => {
        let (cond_node, body_node) = (node.get(*condition), node.get(*body));
        let f = self.fn_val;
        let cond_block = self.gen.context.append_basic_block(&f, "cond");
        let body_block = self.gen.context.append_basic_block(&f, "loop_body");
        let exit_block = self.gen.context.append_basic_block(&f, "loop_exit");
        // jump to condition
        self.builder.build_unconditional_branch(&cond_block);
        // conditional branch
        self.builder.position_at_end(&cond_block);
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(cond_value, &body_block, &exit_block);
        // loop body
        self.builder.position_at_end(&body_block);
        self.codegen_expression(body_node)?;

        // loop back to start
        self.builder.build_unconditional_branch(&cond_block);
        // exit
        self.builder.position_at_end(&exit_block);
        return Ok(Void);
      }
      Content::IfThen { condition, then_branch } => {
        let (cond_node, then_node) = (node.get(*condition), node.get(*then_branch));
        let f = self.fn_val;
        let then_block = self.gen.context.append_basic_block(&f, "then");
        let end_block = self.gen.context.append_basic_block(&f, "endif");
        // conditional branch
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(cond_value, &then_block, &end_block);
        // then block
        self.builder.position_at_end(&then_block);
        self.codegen_expression(then_node)?;
        self.builder.build_unconditional_branch(&end_block);
        // end block
        self.builder.position_at_end(&end_block);
        return Ok(Void);
      }
      Content::Label{ label, body } => {
        let body = node.get(*body);
        let f = self.fn_val;
        let exit_block = self.gen.context.append_basic_block(&f, "exit_label");
        let block_depth = self.blocks.len();
        let label_state = LabelState { block_depth, exit_block, phi_values: vec![] };
        self.labels_in_scope.push((*label, label_state));
        let value = self.codegen_expression_to_register(body)?;
        let block = self.builder.get_insert_block().unwrap();
        let (_, label_state) = self.labels_in_scope.pop().unwrap();
        self.builder.build_unconditional_branch(&label_state.exit_block);
        self.builder.position_at_end(&label_state.exit_block);
        if let Some(v) = value {
          let phi = self.builder.build_phi(v.get_type(), "label_return");
          phi.add_incoming(&[(&v, &block)]);
          for (v, b) in label_state.phi_values.iter() {
            phi.add_incoming(&[(v, b)]);
          }
          reg(phi.as_basic_value())
        }
        else {
          return Ok(Void);
        }
      }
      Content::IfThenElse{ condition, then_branch, else_branch } => {
        let condition = node.get(*condition);
        let then_branch = node.get(*then_branch);
        let else_branch = node.get(*else_branch);
        // create basic blocks
        let f = self.fn_val;
        let then_start_block = self.gen.context.append_basic_block(&f, "then");
        let else_start_block = self.gen.context.append_basic_block(&f, "else");
        let end_block = self.gen.context.append_basic_block(&f, "endif");
        // conditional branch
        let cond_value = self.codegen_int(condition)?;
        self.builder.build_conditional_branch(
          cond_value, &then_start_block, &else_start_block);
        // then block
        self.builder.position_at_end(&then_start_block);
        let then_value = self.codegen_expression_to_register(then_branch)?;
        let then_end_block = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(&end_block);
        // else block
        self.builder.position_at_end(&else_start_block);
        let else_value = self.codegen_expression_to_register(else_branch)?;
        let else_end_block = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(&end_block);
        // end block
        self.builder.position_at_end(&end_block);
        if then_value.is_some() && else_value.is_some() {
          let v1 = then_value.unwrap();
          let v2 = else_value.unwrap();
          let phi = self.builder.build_phi(v1.get_type(), "if_result");
          phi.add_incoming(&[
            (&v1, &then_end_block),
            (&v2, &else_end_block),
          ]);
          reg(phi.as_basic_value())
        }
        else {
          return Ok(Void);
        }
      }
      Content::Block(nodes) => {
        // TODO: call any necessary Drop functions
        let node_count = nodes.len();
        self.blocks.push(Block::new());
        let block_value = if node_count > 0 {
          for i in 0..(node_count-1) {
            self.codegen_expression(node.get(nodes[i]))?;
          }
          // Make sure the last value is owned
          self.codegen_owned_expression(node.get(nodes[node_count-1]))
        }
        else {
          Ok(Void)
        };
        let b = self.blocks.pop().unwrap();
        for d in b.destructibles {
          self.codegen_drop_value(d);
        }
        return block_value;
      }
      Content::Quote(e) => {
        // TODO: this works by just allocating the quote on the heap and then just trusting that it will still be there
        // at runtime. It works fine for a single-process JIT, although it's pretty hacky. It will NOT work for static
        // compilation, or for any code passed between processes.
        let v = Box::into_raw(e.clone()) as u64;
        let v = self.gen.context.i64_type().const_int(v, false);

        let t = self.gen.to_basic_type(info, node.type_tag()).unwrap(); // should be pointer to expr
        reg(self.builder.build_int_to_ptr(v, t.into_pointer_type(), "quote_expr").into())
      }
      Content::CBind{ .. } => {
        return Ok(Void);
      }
      Content::FunctionDefinition{ .. } => {
        return Ok(Void);
      }
      Content::TypeDefinition{ .. } => {
        // TODO: is nothing required here?
        return Ok(Void);
      }
      Content::TypeConstructor{ name:_, field_values } => {
        // TODO: log values that need to be dropped
        let a : Result<Vec<BasicValueEnum>, Error> =
          field_values.iter().map(|(_, a)| self.codegen_value(node.get(*a))).collect();
        let def = node.node_type_def().unwrap();
        match def.kind {
          TypeKind::Struct => {
            self.codegen_struct_initialise(info, &def, a?.as_slice())
          }
          TypeKind::Union => {
            self.codegen_union_initialise(info, &def, a?[0])
          }
        }
      }
      Content::FieldAccess{ container, field } => {
        let container = node.get(*container);
        let mut v = self.codegen_expression(container)?.unwrap();
        let mut ct = container.type_tag();
        while let Some(inner) = ct.ptr() {
          ct = inner;
          let ptr = self.genval_to_register(v);
          v = pointer(*ptr.as_pointer_value());
        }
        let def = match &ct.content {
          TypeContent::Def(name, unit_id) => {
            info.find_type_def(name, *unit_id).unwrap()
          }
          _ => panic!(),
        };
        match def.kind {
          TypeKind::Struct => {
            let (field_index, _) =
              def.fields.iter().enumerate()
              .find(|(_, (n, _))| n.name.as_ref() == field.name.as_ref()).unwrap();
            match v.storage {
              Storage::Register => {
                // if the struct is in a register, dereference the field into a register
                let reg_val =
                  self.builder.build_extract_value(
                    *v.value.as_struct_value(), field_index as u32, &field.name).unwrap();
                reg(reg_val)
              }
              Storage::Pointer => {
                // if this is a pointer to the struct, get a pointer to the field
                let ptr = *v.value.as_pointer_value();
                let field_ptr_untyped = unsafe {
                  self.builder.build_struct_gep(ptr, field_index as u32, &field.name)
                };
                let t = self.gen.to_basic_type(info, node.type_tag());
                // this cast is necessary because all pointer fields are tagged as void pointers
                // in the IR, due to an issue with generating cyclic references
                let field_ptr =
                  self.builder.build_pointer_cast(
                    field_ptr_untyped, self.gen.pointer_to_type(t), "field_cast");
                pointer(field_ptr)
              }
            }
          }
          TypeKind::Union => {
            let t = self.gen.to_basic_type(info, node.type_tag());
            match v.storage {
              Storage::Register => {
                // if the struct is in a register, dereference the field into a register
                let reg_val =
                  self.builder.build_bitcast(v.value, t.unwrap(), "union_cast");
                reg(reg_val)
              }
              Storage::Pointer => {
                // if this is a pointer to the struct, get a pointer to the field
                let ptr = *v.value.as_pointer_value();
                let field_ptr = self.builder.build_pointer_cast(ptr, self.gen.pointer_to_type(t), "union_cast");
                pointer(field_ptr)
              }
            }
          }
        }
      }
      Content::ArrayLiteral(elements) => {
        if let Some(inner_type) = node.type_tag().array() {
          let element_type = self.gen.to_basic_type(info, inner_type).unwrap();
          let length = self.gen.context.i32_type().const_int(elements.len() as u64, false).into();
          let array_ptr = self.builder.build_array_malloc(element_type, length, "array_malloc");
          for (i, e) in elements.iter().enumerate() {
            let v = self.codegen_value(node.get(*e))?;
            let index = self.gen.context.i32_type().const_int(i as u64, false).into();
            let element_ptr = unsafe { self.builder.build_gep(array_ptr, &[index], "element_ptr") };
            self.builder.build_store(element_ptr, v);
          }
          let array_type = self.gen.bounded_array_type(info, inner_type);
          let mut sv = array_type.get_undef();
          sv = self.builder.build_insert_value(sv, array_ptr, 0, "array_ptr").unwrap().into_struct_value();
          let length = self.gen.context.i64_type().const_int(elements.len() as u64, false);
          sv = self.builder.build_insert_value(sv, length, 1, "array_length").unwrap().into_struct_value();
          reg(sv.into())
        }
        else{
          panic!();
        }
      }
      Content::Assignment{ assignee, value } => {
        // TODO: WHAT IS BEING ASSIGNED TO? Should only work for FIELDS and ARRAYS
        let (assignee, value) = (node.get(*assignee), node.get(*value));
        let assign_location = self.codegen_expression(assignee)?.unwrap();
        let assign_ptr = match assign_location.storage {
          Storage::Pointer => {
            *assign_location.value.as_pointer_value()
          }
          Storage::Register => {
            return error(assignee, "cannot assign to this construct");
          }
        };
        // Make sure the value being assigned is fully owned
        let val = self.codegen_owned_expression(value)?;
        // Drop the value being overwritten
        if let Some(drop_reference) = self.get_linked_drop_reference(info, assignee.type_tag()) {
          let d = Destructible { drop_reference, value: assign_ptr };
          self.codegen_drop_value(d);
        }
        // TODO: this is very inefficient when assigning large structs. Can optimise
        // by detecting pointers and using the memcopy intrinsic
        let reg_val = self.maybeval_to_register(val).unwrap();
        self.builder.build_store(assign_ptr, reg_val);
        return Ok(Void);
      }
      Content::VariableInitialise{ name, type_tag: _, value, var_scope } => {
        let value = node.get(*value);
        match var_scope {
          VarScope::Local => {
            let v = self.codegen_value(value)?;
            self.init_local_var(name.id, &name.name, v);
          }
          VarScope::Global(_) => {
            let aaa = (); // THIS SHOULDN'T HAPPEN FOR CONST GLOBALS
            let v = self.codegen_value(value)?;
            self.init_global_var(&name.name, v);
          }
        }
        return Ok(Void);
      }
      Content::Reference { name, refers_to } => {
        if let Some(ptr) = refers_to.as_ref().and_then(|sid| self.variables.get(sid)) {
          pointer(*ptr)
        }
        else if let Some(def) = node.node_symbol_def() {
          self.get_linked_global_value(node, &def)
        }
        else {
          panic!("no value found for reference '{}'!", name);
        }
      }
      Content::BreakToLabel{ label, return_value } => {
        // Generate fully owned value
        let v = return_value.as_ref().map(|n| {
          let n = node.get(*n);
          let v = self.codegen_owned_expression(n)?;
          Ok(self.maybeval_to_register(v))
        }).unwrap_or(Ok(None))?;
        let label_state = self.labels_in_scope.iter_mut().find(|(l, _)| l == label);
        if let Some((_, label_state)) = label_state {
          if let Some(v) = v {
            let block = self.builder.get_insert_block().unwrap();
            label_state.phi_values.push((v, block));
          }
          let exit_block = label_state.exit_block;
          let label_block_depth = label_state.block_depth;
          // Drop all the values we're about to jump past
          let destructibles =
            self.blocks.iter().skip(label_block_depth).rev()
            .flat_map(|b| b.destructibles.iter()).cloned()
            .collect::<Vec<_>>();
          for d in destructibles {
            self.codegen_drop_value(d);
          }
          //let i = self.labels_in_scope.iter().rev().take_while(||);
          self.builder.build_unconditional_branch(&exit_block);
          // create a dummy block to hold instructions after the branch
          let dummy_block = self.gen.context.append_basic_block(&self.fn_val, "dummy_block");
          self.builder.position_at_end(&dummy_block);
          return Ok(Void);
        }
        return error(node, "label not found");
      }
      Content::Literal(v) => {
        match v {
          PrimitiveVal::Void => return Ok(Void),
          PrimitiveVal::String(s) => {
            let vs : &[u8] = s.as_ref();
            let byte = self.gen.context.i8_type();
            let vs : Vec<IntValue> =
              vs.iter().map(|v|
                byte.const_int(*v as u64, false).into()).collect();
            let const_array : BasicValueEnum = self.gen.context.i8_type().const_array(vs.as_slice()).into();
            let name = &s.as_str()[0..std::cmp::min(s.len(), 10)];
            let ptr = self.gen.add_global(const_array, true, name);
            let cast_to = self.gen.context.i8_type().ptr_type(AddressSpace::Generic);
            let string_pointer = self.builder.build_pointer_cast(ptr, cast_to, "string_pointer");
            let string_length = self.gen.context.i64_type().const_int(vs.len() as u64, false);
            let def = node.node_type_def().unwrap();
            self.codegen_struct_initialise(info, &def, &[string_pointer.into(), string_length.into()])
          }
          _ => reg(self.gen.codegen_static(node)?),
        }
      }
    };
    Ok(v.into())
  }

  fn codegen_return(&mut self, value_node : Option<TypedNode>) -> Result<(), Error> {
    // TODO: Call the necessary Drop and Clone functions
    if let Some(value_node) = value_node {
      let v = self.codegen_expression_to_register(value_node)?;
      self.builder.build_return(v.as_ref().map(|v| v as &dyn BasicValue));
    }
    else {
      self.builder.build_return(None);
    }
    Ok(())
  }
}
