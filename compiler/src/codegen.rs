
// TODO: Carlos says I should have more comments than the occasional TODO

use crate::error::{Error, error, error_raw, ErrorContent};
use crate::expr::RefStr;
use crate::typecheck::{
  TypedNode, Content, Type, Val, TypeDefinition, TypeKind,
  FunctionDefinition, VarScope, TypedModule, FunctionImplementation,
  TOP_LEVEL_FUNCTION_NAME };

use std::rc::Rc;
use std::collections::HashMap;

use inkwell::AddressSpace;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context};
use inkwell::module::{Module, Linkage};
use inkwell::attributes::Attribute;
use inkwell::passes::PassManager;
use inkwell::types::{
  BasicTypeEnum, BasicType, StructType, PointerType, FunctionType, AnyTypeEnum, ArrayType,
  IntType, FloatType };
use inkwell::values::{
  BasicValueEnum, BasicValue, FloatValue, IntValue, FunctionValue, PointerValue, GlobalValue };
use inkwell::{FloatPredicate, IntPredicate};
use inkwell::targets::TargetData;

pub fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

macro_rules! unwrap_enum {
  ( $enum_name:ident, $variant_name:ident, $v:expr) => { 
    if let $enum_name::$variant_name(x) = $v { x } else { panic!() }
  };
}

macro_rules! codegen_type {
  (PointerValue, $e:ident, $gen:ident) => { $gen.codegen_pointer($e) };
  (FloatValue, $e:ident, $gen:ident) => { $gen.codegen_float($e) };
  (IntValue, $e:ident, $gen:ident) => { $gen.codegen_int($e) };
}

macro_rules! binary_op {
  ($op_name:ident, $type_name:ident, $a:ident, $b:ident, $gen:ident) => {
    {
      let a = codegen_type!($type_name, $a, $gen)?;
      let b = codegen_type!($type_name, $b, $gen)?;
      let fv = ($gen).builder.$op_name(a, b, "op_result");
      reg(fv.into())
    }
  }
}

macro_rules! unary_op {
  ($op_name:ident, $type_name:ident, $a:ident, $gen:ident) => {
    {
      let a = codegen_type!($type_name, $a, $gen)?;
      let v = ($gen).builder.$op_name(a, "op_result");
      reg(v.into())
    }
  }
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

macro_rules! compare_op {
  ($op_name:ident, $pred:expr, $type_name:ident, $a:ident, $b:ident, $gen:ident) => {
    {
      let a = codegen_type!($type_name, $a, $gen)?;
      let b = codegen_type!($type_name, $b, $gen)?;
      let fv = ($gen).builder.$op_name($pred, a, b, "cpm_result");
      reg(fv.into())
    }
  }
}

/// Indicates whether a value is a pointer to the stack,
/// or stored directly in a register.
#[derive(PartialEq)]
enum Storage {
  Register,
  Pointer,
}

/// Represents an SSA value in some LLVM IR. Might be stored directly in an LLVM register,
/// or might be a pointer to somewhere on the stack/heap.
#[derive(PartialEq)]
struct GenVal {
  storage : Storage,
  value : BasicValueEnum,
}

fn reg(value : BasicValueEnum) -> GenVal {
  GenVal { storage: Storage::Register, value }
}

fn pointer(ptr : PointerValue) -> GenVal {
  GenVal { storage: Storage::Pointer, value: ptr.as_basic_value_enum() }
}

struct LoopLabels {
  condition : BasicBlock,
  exit : BasicBlock,
}

/*
impl From<Option<BasicValueEnum>> for GenVal {
  fn from(v : Option<BasicValueEnum>) -> GenVal {
    match v {
      Some(v) => GenVal::Register(v),
      None => GenVal::Void,
    }
  }
}
*/

fn const_null(t : BasicTypeEnum) -> BasicValueEnum {
  use BasicTypeEnum::*;
  match t {
    FloatType(t) => t.const_null().into(),
    IntType(t) => t.const_null().into(),
    ArrayType(t) => t.const_null().into(),
    PointerType(t) => t.const_null().into(),
    StructType(t) => t.const_null().into(),
    VectorType(t) => t.const_null().into(),
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

#[derive(Copy, Clone)]
enum ShortCircuitOp { And, Or }

/// Code generates a single function (can spawn children to code-generate internal functions)
pub struct Gen<'l> {
  context: &'l mut Context,
  module : &'l mut Module,
  target_data : &'l TargetData,
  builder: Builder,
  type_info : &'l TypedModule,

  /// Used by the JIT to link globals between modules
  external_globals: &'l mut HashMap<RefStr, GlobalValue>,

  /// Used by the JIT to link functions between modules
  external_functions: &'l mut HashMap<RefStr, FunctionValue>,

  /// Used by the JIT to link c functions
  c_functions: &'l mut HashMap<RefStr, (FunctionValue, usize)>,

  variables: HashMap<RefStr, PointerValue>,
  struct_types: HashMap<RefStr, StructType>,

  /// A stack of values indicating the entry and exit labels for each loop
  loop_labels: Vec<LoopLabels>,

  pm : &'l PassManager<FunctionValue>,
}

impl <'l> Gen<'l> {

  pub fn new(
    context: &'l mut Context,
    module : &'l mut Module,
    target_data : &'l TargetData,
    type_info : &'l TypedModule,
    external_globals: &'l mut HashMap<RefStr, GlobalValue>,
    external_functions: &'l mut HashMap<RefStr, FunctionValue>,
    c_functions: &'l mut HashMap<RefStr, (FunctionValue, usize)>,
    pm : &'l PassManager<FunctionValue>,
  )
      -> Gen<'l>
  {
    let builder = context.create_builder();
    let variables = HashMap::new();
    Gen {
      context, module,
      target_data, builder,
      type_info,
      external_globals,
      external_functions,
      c_functions,
      variables,
      struct_types: HashMap::new(),
      loop_labels: vec!(),
      pm,
    }
  }

  pub fn child_function_gen<'lc>(&'lc mut self)
    -> Gen<'lc>
  {
    Gen::new(
      self.context, self.module, self.target_data, self.type_info, self.external_globals,
      self.external_functions, self.c_functions, self.pm)
  }

  fn create_entry_block_alloca(&self, t : BasicTypeEnum, name : &str) -> PointerValue {
    let current_block = self.builder.get_insert_block().unwrap();
    let function = current_block.get_parent().unwrap();
    let entry = function.get_entry_basic_block().unwrap();
    match entry.get_first_instruction() {
      Some(fi) => self.builder.position_before(&fi),
      None => self.builder.position_at_end(&entry),
    }
    let pointer = self.builder.build_alloca(t, name);
    self.builder.position_at_end(&current_block);
    pointer
  }

  fn add_global(&mut self, initial_value : BasicValueEnum, is_constant : bool, name : &str) -> PointerValue {
    let gv = self.module.add_global(initial_value.get_type(), Some(AddressSpace::Generic), name);
    gv.set_initializer(&initial_value);
    gv.set_constant(is_constant);
    gv.set_linkage(Linkage::Internal);
    //gv.set_alignment(8); // TODO: is this needed?
    gv.as_pointer_value()
  }

  fn init_variable(&mut self, name : RefStr, var_scope : VarScope, value : BasicValueEnum)
    -> Result<(), ErrorContent>
  {
    if self.variables.contains_key(&name) {
      return Err(format!("variable with name '{}' already defined", name).into());
    }
    let pointer = match var_scope {
      VarScope::Global => {
        self.add_global(const_null(value.get_type()), false, &name)
      }
      VarScope::Local => {
        self.create_entry_block_alloca(value.get_type(), &name)
      }
    };
    self.builder.build_store(pointer, value);
    self.variables.insert(name, pointer);
    Ok(())
  }

  fn codegen_value(&mut self, n : &TypedNode) -> Result<BasicValueEnum, Error> {
    Ok(self.codegen_expression_to_register(n)?.unwrap())
  }

  fn codegen_float(&mut self, n : &TypedNode) -> Result<FloatValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::FloatValue(f) => Ok(f),
      t => error(n.loc, format!("Expected float, found {:?}", t)),
    }
  }

  fn codegen_int(&mut self, n : &TypedNode) -> Result<IntValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::IntValue(i) => Ok(i),
      t => error(n.loc, format!("Expected int, found {:?}", t)),
    }
  }

  fn codegen_pointer(&mut self, n : &TypedNode) -> Result<PointerValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::PointerValue(p) => Ok(p),
      t => error(n.loc, format!("Expected pointer, found {:?}", t)),
    }
  }

  fn codegen_expression_to_register(&mut self, node : &TypedNode) -> Result<Option<BasicValueEnum>, Error> {
    if let Some(v) = self.codegen_expression(node)? {
      let reg_val = match v.storage {
        Storage::Pointer => {
          let ptr = *v.value.as_pointer_value();
          self.builder.build_load(ptr, "assignment_value")
        }
        Storage::Register => {
          v.value
        }
      };
      Ok(Some(reg_val))
    }
    else {
      Ok(None)
    }
  }

  fn codegen_convert(&mut self, convert_node : &TypedNode, value_to_convert : &TypedNode) -> Result<GenVal, Error> {
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

    let from_type = &value_to_convert.type_tag;
    let to_type = &convert_node.type_tag;
    let from_llvm_type = self.to_basic_type(from_type).ok_or_else(|| error_raw(value_to_convert.loc, "can't cast from void"))?;
    let to_llvm_type = self.to_basic_type(to_type).ok_or_else(|| error_raw(convert_node.loc, "can't cast to void"))?;
    let n = value_to_convert;
    
    let from_float = from_type.float();
    let from_signed = from_type.signed_int();
    let from_unsigned = from_type.unsigned_int();
    let from_int = from_signed || from_unsigned;
    let from_width = self.target_data.get_bit_size(&from_llvm_type);
    let from_pointer = from_type.pointer();

    let to_float = to_type.float();
    let to_signed = to_type.signed_int();
    let to_unsigned = to_type.unsigned_int();
    let to_int = to_signed || to_unsigned;
    let to_width = self.target_data.get_bit_size(&to_llvm_type);
    let to_pointer = to_type.pointer();

    // Pointer casts
    if from_pointer && to_unsigned {
      let t = int_type(self, to_width);
      return Ok(convert_op!(build_ptr_to_int, PointerValue, t, n, self));
    }
    if from_unsigned && to_pointer {
      let t = *self.to_basic_type(to_type).unwrap().as_pointer_type();
      return Ok(convert_op!(build_int_to_ptr, IntValue, t, n, self));
    }
    if from_pointer && to_pointer {
      let t = *self.to_basic_type(to_type).unwrap().as_pointer_type();
      return Ok(convert_op!(build_pointer_cast, PointerValue, t, n, self));
    }

    // truncate
    if to_width < from_width {
      if from_int && to_int {
        let t = int_type(self, to_width);
        return Ok(convert_op!(build_int_truncate, IntValue, t, n, self));
      }
      if from_float && to_float {
        let t = float_type(self, to_width);
        return Ok(convert_op!(build_float_trunc, FloatValue, t, n, self));
      }
    }
    // extend
    if to_width > from_width {
      if from_signed && to_int {
        let t = int_type(self, to_width);
        return Ok(convert_op!(build_int_s_extend, IntValue, t, n, self));
      }
      if from_unsigned && to_int {
        let t = int_type(self, to_width);
        return Ok(convert_op!(build_int_z_extend, IntValue, t, n, self));
      }
      if from_float && to_float {
        let t = float_type(self, to_width);
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
      let t = float_type(self, to_width);
      return Ok(convert_op!(build_signed_int_to_float, IntValue, t, n, self));
    }
    if from_unsigned && to_float {
      let t = float_type(self, to_width);
      return Ok(convert_op!(build_unsigned_int_to_float, IntValue, t, n, self));
    }
    if from_float && to_signed {
      let t = int_type(self, to_width);
      return Ok(convert_op!(build_float_to_signed_int, FloatValue, t, n, self));
    }
    if from_float && to_unsigned {
      let t = int_type(self, to_width);
      return Ok(convert_op!(build_float_to_unsigned_int, FloatValue, t, n, self));
    }
    return error(convert_node.loc, "type cast not supported");
  }

  fn codegen_short_circuit_op(&mut self, a : &TypedNode, b : &TypedNode, op : ShortCircuitOp)
    -> Result<GenVal, Error>
  {
    use ShortCircuitOp::*;
    let short_circuit_outcome = match op {
      And => self.context.bool_type().const_int(0, false),
      Or => self.context.bool_type().const_int(1, false),
    };
    // create basic blocks
    let a_start_block = self.builder.get_insert_block().unwrap();
    let f = a_start_block.get_parent().unwrap();
    let b_start_block = self.context.append_basic_block(&f, "b_block");
    let end_block = self.context.append_basic_block(&f, "end");
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
    let phi = self.builder.build_phi(self.context.bool_type(), "result");
    phi.add_incoming(&[
      (&short_circuit_outcome, &a_end_block),
      (&b_value, &b_end_block),
    ]);
    return Ok(reg(phi.as_basic_value()));
  }

  fn codegen_struct_initialise(&mut self, def : &TypeDefinition, args : &[BasicValueEnum]) -> GenVal {
    let t = self.struct_type(def);
    let mut sv = t.get_undef();
    for (i, v) in args.iter().enumerate() {
      sv = self.builder.build_insert_value(sv, *v, i as u32, "insert_field").unwrap().into_struct_value();
    }
    reg(sv.into())
  }

  fn codegen_union_initialise(&mut self, def : &TypeDefinition, val : BasicValueEnum) -> GenVal {
    let union_type = self.struct_type(def).as_basic_type_enum();
    let ptr = self.create_entry_block_alloca(union_type, &def.name);
    let variant_type = self.pointer_to_type(Some(val.get_type()));
    let variant_ptr = self.builder.build_pointer_cast(ptr, variant_type, "union_cast");
    self.builder.build_store(variant_ptr, val);
    pointer(ptr)
  }

  fn codegen_address_of_expression(&mut self, value : &TypedNode) -> Result<GenVal, Error> {
    let v = self.codegen_expression(value)?.unwrap();
    match v.storage {
      Storage::Register => {
        let ptr = self.create_entry_block_alloca(v.value.get_type(), "reference");
        self.builder.build_store(ptr, v.value);
        Ok(reg(ptr.into()))
      }
      Storage::Pointer => {
        Ok(reg(v.value))
      }
    }
  }

  /// ensure necessary definitions are inserted and linking operations performed when a function is referenced
  fn get_linked_function_reference(&mut self, def : &FunctionDefinition) -> FunctionValue {
    if let Some(local_f) = self.module.get_function(&def.name) {
      local_f
    }
    else{
      let f = self.codegen_prototype(&def.name, &def.signature.return_type, &def.args, &def.signature.args);
      match def.implementation {
        FunctionImplementation::CFunction(Some(address)) => {
          self.c_functions.insert(def.name.clone(), (f, address));
        }
        _ => {
          self.external_functions.insert(def.name.clone(), f);
        }
      }
      f
    }
  }

  fn codegen_function_call(&mut self, function_value : &TypedNode, args : &[TypedNode])
    -> Result<Option<GenVal>, Error>
  {
    //let f = self.get_linked_function_reference(def);
    let mut arg_vals = vec!();
    let function_pointer = self.codegen_pointer(function_value)?;
    for a in args.iter() {
      let v = self.codegen_value(a)?;
      arg_vals.push(v);
    }
    let call = self.builder.build_call(function_pointer, arg_vals.as_slice(), "tmp");
    let r = call.try_as_basic_value().left();
    return Ok(r.map(reg));
  }

  fn codegen_expression(&mut self, node : &TypedNode) -> Result<Option<GenVal>, Error> {
    let v : GenVal = match &node.content {
      Content::FunctionCall(function_value, args) => {
        return self.codegen_function_call(function_value, args);
      }
      Content::IntrinsicCall(name, args) => {
        if let [a, b] = args.as_slice() {
          match (&a.type_tag, name.as_ref()) {
          (Type::F64, "+") => binary_op!(build_float_add, FloatValue, a, b, self),
            (Type::F64, "-") => binary_op!(build_float_sub, FloatValue, a, b, self),
            (Type::F64, "*") => binary_op!(build_float_mul, FloatValue, a, b, self),
            (Type::F64, "/") => binary_op!(build_float_div, FloatValue, a, b, self),
            (Type::F64, ">") => compare_op!(build_float_compare, FloatPredicate::OGT, FloatValue, a, b, self),
            (Type::F64, ">=") => compare_op!(build_float_compare, FloatPredicate::OGE, FloatValue, a, b, self),
            (Type::F64, "<") => compare_op!(build_float_compare, FloatPredicate::OLT, FloatValue, a, b, self),
            (Type::F64, "<=") => compare_op!(build_float_compare, FloatPredicate::OLE, FloatValue, a, b, self),
            (Type::F64, "==") => compare_op!(build_float_compare, FloatPredicate::OEQ, FloatValue, a, b, self),
            (Type::I64, "+") => binary_op!(build_int_add, IntValue, a, b, self),
            (Type::I64, "-") => binary_op!(build_int_sub, IntValue, a, b, self),
            (Type::I64, "*") => binary_op!(build_int_mul, IntValue, a, b, self),
            // TODO: why is this commented out?
            // (Type::I64, "/") => binary_op!(build_int_div, IntValue, a, b, self),
            (Type::I64, ">") => compare_op!(build_int_compare, IntPredicate::SGT, IntValue, a, b, self),
            (Type::I64, ">=") => compare_op!(build_int_compare, IntPredicate::SGE, IntValue, a, b, self),
            (Type::I64, "<") => compare_op!(build_int_compare, IntPredicate::SLT, IntValue, a, b, self),
            (Type::I64, "<=") => compare_op!(build_int_compare, IntPredicate::SLE, IntValue, a, b, self),
            (Type::I64, "==") => compare_op!(build_int_compare, IntPredicate::EQ, IntValue, a, b, self),
            (Type::Bool, "&&") => self.codegen_short_circuit_op(a, b, ShortCircuitOp::And)?,
            (Type::Bool, "||") => self.codegen_short_circuit_op(a, b, ShortCircuitOp::Or)?,
            _ => return error(node.loc, "encountered unrecognised intrinsic"),
          }        
        }
        else if let [a] = args.as_slice() {
          match (&a.type_tag, name.as_ref()) {
            (Type::F64, "unary_-") => unary_op!(build_float_neg, FloatValue, a, self),
            (Type::I64, "unary_-") => unary_op!(build_int_neg, IntValue, a, self),
            (Type::Bool, "unary_!") => unary_op!(build_not, IntValue, a, self),
            (_, "unary_ref") => self.codegen_address_of_expression(a)?,
            _ => return error(node.loc, "encountered unrecognised intrinsic"),
          }
        }
        else {
          return error(node.loc, "encountered unrecognised intrinsic");
        }
      }
      Content::SizeOf(t) => {
        let t = self.to_basic_type(&t);
        reg(self.size_of_type(t).into())
      }
      Content::Convert(n) => {
        self.codegen_convert(node, n)?
      }
      Content::While(ns) => {
        let (cond_node, body_node) = (&ns.0, &ns.1);
        let f = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        let cond_block = self.context.append_basic_block(&f, "cond");
        let body_block = self.context.append_basic_block(&f, "loop_body");
        let exit_block = self.context.append_basic_block(&f, "loop_exit");
        let labels = LoopLabels { condition: cond_block, exit: exit_block };
        // jump to condition
        self.builder.build_unconditional_branch(&labels.condition);
        // conditional branch
        self.builder.position_at_end(&labels.condition);
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(cond_value, &body_block, &labels.exit);
        // loop body
        self.builder.position_at_end(&body_block);
        self.loop_labels.push(labels);
        self.codegen_expression(body_node)?;
        let labels = self.loop_labels.pop().unwrap();
        // loop back to start
        self.builder.build_unconditional_branch(&labels.condition);
        // exit
        self.builder.position_at_end(&labels.exit);
        return Ok(None);
      }
      Content::Break => {
        if let Some(labels) = self.loop_labels.last() {
          self.builder.build_unconditional_branch(&labels.exit);
          // create a dummy block to hold instructions after the break
          let f = self.builder.get_insert_block().unwrap().get_parent().unwrap();
          let dummy_block = self.context.append_basic_block(&f, "dummy_block");
          self.builder.position_at_end(&dummy_block);
          return Ok(None);
        }
        else {
          return error(node.loc, "can only break inside a loop");
        }
      }
      Content::IfThen(ns) => {
        let (cond_node, then_node) = (&ns.0, &ns.1);
        let block = self.builder.get_insert_block().unwrap();
        let f = block.get_parent().unwrap();
        let then_block = self.context.append_basic_block(&f, "then");
        let end_block = self.context.append_basic_block(&f, "endif");
        // conditional branch
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(cond_value, &then_block, &end_block);
        // then block
        self.builder.position_at_end(&then_block);
        self.codegen_expression(then_node)?;
        self.builder.build_unconditional_branch(&end_block);
        // end block
        self.builder.position_at_end(&end_block);
        return Ok(None);
      }
      Content::IfThenElse(ns) => {
        let (cond_node, then_node, else_node) = (&ns.0, &ns.1, &ns.2);
        // create basic blocks
        let block = self.builder.get_insert_block().unwrap();
        let f = block.get_parent().unwrap();
        let then_start_block = self.context.append_basic_block(&f, "then");
        let else_start_block = self.context.append_basic_block(&f, "else");
        let end_block = self.context.append_basic_block(&f, "endif");
        // conditional branch
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(
          cond_value, &then_start_block, &else_start_block);
        // then block
        self.builder.position_at_end(&then_start_block);
        let then_value = self.codegen_expression_to_register(then_node)?;
        let then_end_block = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(&end_block);
        // else block
        self.builder.position_at_end(&else_start_block);
        let else_value = self.codegen_expression_to_register(else_node)?;
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
          return Ok(None);
        }
      }
      Content::Block(nodes) => {
        let node_count = nodes.len();
        if node_count > 0 {
          for i in 0..(node_count-1) {
            self.codegen_expression(&nodes[i])?;
          }
          return self.codegen_expression(&nodes[node_count-1]);
        }
        return Ok(None);
      }
      Content::Quote(e) => {
        let v = Box::into_raw(e.clone()) as u64;
        let v = self.context.i64_type().const_int(v, false);
        let t = self.context.i8_type().ptr_type(AddressSpace::Generic);
        reg(self.builder.build_int_to_ptr(v, t, "quote_expr").into())
      }
      Content::CFunctionPrototype(_def) => {
        return Ok(None);
      }
      Content::FunctionDefinition(name) => {
        let def = self.type_info.functions.get(name).unwrap();
        let body = unwrap_enum!(FunctionImplementation, Normal, &def.implementation);
        self.child_function_gen().codegen_function(
          node, body, &def.name, &def.args, &def.signature.args)?;
        return Ok(None);
      }
      Content::TypeDefinition(_def) => {
        // TODO: is nothing required here?
        return Ok(None);
      }
      Content::StructInstantiate(struct_name, args) => {
        let a : Result<Vec<BasicValueEnum>, Error> =
          args.iter().map(|a| self.codegen_value(a)).collect();
        let def = self.type_info.types.get(struct_name).unwrap();
        self.codegen_struct_initialise(def, a?.as_slice())
      }
      Content::UnionInstantiate(union_name, arg) => {
        let val = self.codegen_value(&arg.1)?;
        let def = self.type_info.types.get(union_name).unwrap();
        self.codegen_union_initialise(def, val)
      }
      Content::FieldAccess(x) => {
        let (type_val_node, field_name) = (&x.0, &x.1);
        let v = self.codegen_expression(type_val_node)?.unwrap();
        let def = match &type_val_node.type_tag {
          Type::Def(name) => self.type_info.types.get(name).unwrap(),
          _ => panic!(),
        };
        match def.kind {
          TypeKind::Struct => {
            let (field_index, _) =
              def.fields.iter().enumerate()
              .find(|(_, (n, _))| n==field_name).unwrap();
            match v.storage {
              Storage::Register => {
                // if the struct is in a register, dereference the field into a register
                let reg_val =
                  self.builder.build_extract_value(
                    *v.value.as_struct_value(), field_index as u32, field_name).unwrap();
                reg(reg_val)
              }
              Storage::Pointer => {
                // if this is a pointer to the struct, get a pointer to the field
                let ptr = *v.value.as_pointer_value();
                let field_ptr = unsafe {
                  self.builder.build_struct_gep(ptr, field_index as u32, field_name)
                };
                pointer(field_ptr)
              }
            }
          }
          TypeKind::Union => {
            let t = self.to_basic_type(&node.type_tag);
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
                let field_ptr = self.builder.build_pointer_cast(ptr, self.pointer_to_type(t), "union_cast");
                pointer(field_ptr)
              }
            }
          }
        }
      }
      Content::ArrayLiteral(elements) => {
        if let Type::Ptr(inner_type) = &node.type_tag {
          let element_type = self.to_basic_type(inner_type).unwrap();
          let length = self.context.i32_type().const_int(elements.len() as u64, false).into();
          let array_ptr = self.builder.build_array_malloc(element_type, length, "array_malloc");
          for (i, e) in elements.iter().enumerate() {
            let v = self.codegen_value(e)?;
            let index = self.context.i32_type().const_int(i as u64, false).into();
            let element_ptr = unsafe { self.builder.build_gep(array_ptr, &[index], "element_ptr") };
            self.builder.build_store(element_ptr, v);
          }
          reg(array_ptr.into())
        }
        else{
          panic!();
        }
      }
      Content::Index(ns) => {
        let (array_node, index_node) = (&ns.0, &ns.1);
        let array = self.codegen_pointer(array_node)?;
        let index = self.codegen_int(index_node)?;
        let element_ptr = unsafe { self.builder.build_gep(array, &[index], "element_ptr") };
        pointer(element_ptr)
      }
      Content::Assignment(ns) => {
        let (assign_node, value_node) = (&ns.0, &ns.1);
        let assign_location = self.codegen_expression(assign_node)?.unwrap();
        let ptr = match assign_location.storage {
          Storage::Pointer => {
            *assign_location.value.as_pointer_value()
          }
          Storage::Register => {
            return error(assign_node.loc, "cannot assign to this construct");
          }
        };
        // TODO: this is very inefficient when assigning large structs. Can optimise
        // by detecting pointers and using the memcopy intrinsic
        let reg_val = self.codegen_expression_to_register(value_node)?.unwrap();
        self.builder.build_store(ptr, reg_val);
        return Ok(None);
      }
      Content::VariableInitialise(name, value_node, var_scope) => {
        let v = self.codegen_expression_to_register(value_node)?
          .ok_or_else(|| error_raw(value_node.loc, "expected value for initialiser, found void"))?;
        self.init_variable(name.clone(), *var_scope, v)
          .map_err(|c| error_raw(node.loc, c))?; 
        return Ok(None);
      }
      Content::VariableReference(name) => {
        if let Some(ptr) = self.variables.get(name) {
          pointer(*ptr)
        }
        else if let Some(gv) = self.external_globals.get(name) {
          let ptr = gv.as_pointer_value();
          pointer(ptr)
        }
        else if let Some(type_tag) = self.type_info.globals.get(name) {
          let t = self.to_basic_type(type_tag).unwrap();
          let gv = self.module.add_global(t, Some(AddressSpace::Generic), &name);
          gv.set_constant(false);
          self.external_globals.insert(name.clone(), gv);
          pointer(gv.as_pointer_value())
        }
        else {
          return error(node.loc, format!("unknown variable name '{}'.", name));
        }
      }
      Content::FunctionReference(name) => {
        let def =
          self.type_info.functions.get(name)
          .ok_or_else(|| error_raw(node.loc, format!("could not find function with name '{}'", name)))?;
        let f = self.get_linked_function_reference(def);
        reg(f.as_global_value().as_pointer_value().into())
      }
      Content::Deref(_n) => {
        /*
        TODO
        let ptr =
          self.codegen_pointer(n)?
          .ok_or_else(|| error_raw(n.loc, "cannot dereference this construct"))?;
        reg(self.builder.build_load(ptr, "deref"))
        */
        panic!();
      }
      Content::ExplicitReturn(n) => {
        self.codegen_return(n.as_ref().map(|b| b as &TypedNode))?;
        // create a dummy block to hold instructions after the return
        let f = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        let dummy_block = self.context.append_basic_block(&f, "dummy_block");
        self.builder.position_at_end(&dummy_block);
        return Ok(None);
      }
      Content::Literal(v) => {
        match v {
          Val::F64(f) => reg(self.context.f64_type().const_float(*f).into()),
          Val::F32(f) => reg(self.context.f32_type().const_float(*f as f64).into()),
          Val::I64(i) => reg(self.context.i64_type().const_int(*i as u64, false).into()), // TODO the signed values should maybe pass "true" here?
          Val::I32(i) => reg(self.context.i32_type().const_int(*i as u64, false).into()),
          Val::U64(i) => reg(self.context.i64_type().const_int(*i as u64, false).into()),
          Val::U32(i) => reg(self.context.i32_type().const_int(*i as u64, false).into()),
          Val::U16(i) => reg(self.context.i16_type().const_int(*i as u64, false).into()),
          Val::U8(i) => reg(self.context.i8_type().const_int(*i as u64, false).into()),
          Val::Bool(b) =>
            reg(self.context.bool_type().const_int(if *b { 1 } else { 0 }, false).into()),
          Val::Void => return Ok(None),
          Val::String(s) => {
            let vs : &[u8] = s.as_ref();
            let byte = self.context.i8_type();
            let vs : Vec<IntValue> =
              vs.iter().map(|v|
                byte.const_int(*v as u64, false).into()).collect();
            let const_array : BasicValueEnum = self.context.i8_type().const_array(vs.as_slice()).into();
            let name = &s.as_str()[0..std::cmp::min(s.len(), 10)];
            let ptr = self.add_global(const_array, true, name);
            let cast_to = self.context.i8_type().ptr_type(AddressSpace::Generic);
            let string_pointer = self.builder.build_pointer_cast(ptr, cast_to, "string_pointer");
            let string_length = self.context.i64_type().const_int(vs.len() as u64, false);
            let def = self.type_info.types.get("string").unwrap();
            self.codegen_struct_initialise(def, &[string_pointer.into(), string_length.into()])
          }
        }
      }
    };
    Ok(Some(v))
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

  fn to_basic_type(&mut self, t : &Type) -> Option<BasicTypeEnum> {
    match t {
      Type::Void => None,
      Type::F64 => Some(self.context.f64_type().into()),
      Type::F32 => Some(self.context.f32_type().into()),
      Type::I64 => Some(self.context.i64_type().into()),
      Type::I32 => Some(self.context.i32_type().into()),
      Type::U64 => Some(self.context.i64_type().into()),
      Type::U32 => Some(self.context.i32_type().into()),
      Type::U16 => Some(self.context.i16_type().into()),
      Type::U8 => Some(self.context.i8_type().into()),
      Type::Bool => Some(self.context.bool_type().into()),
      Type::Fun(sig) => {
        let t = self.to_function_type(sig.args.as_slice(), &sig.return_type);
        Some(t.ptr_type(AddressSpace::Generic).into())
      }
      Type::Def(name) => {
        let def = self.type_info.types.get(name).unwrap();
        Some(self.struct_type(def).as_basic_type_enum())
      }
      Type::Ptr(t) => {
        let bt = self.to_basic_type(t);
        Some(self.pointer_to_type(bt).into())
      }
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
      self.context.void_type().ptr_type(AddressSpace::Generic)
    }
  }

  fn to_function_type(&mut self, arg_types : &[Type], return_type : &Type) -> FunctionType {
    let arg_types =
      arg_types.iter().map(|t| self.to_basic_type(t).unwrap())
      .collect::<Vec<BasicTypeEnum>>();
    let arg_types = arg_types.as_slice();

    let return_type = self.to_basic_type(return_type);
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

  fn struct_type(&mut self, def : &TypeDefinition) -> StructType {
    if let Some(t) = self.struct_types.get(&def.name) {
      return *t;
    }
    let t = match def.kind {
      TypeKind::Struct => {
        let types =
          def.fields.iter().map(|(_, t)| {
            self.to_basic_type(t).unwrap()
          })
          .collect::<Vec<BasicTypeEnum>>();
        self.context.struct_type(&types, false)
      }
      TypeKind::Union => {
        let mut union_bitwidth = 0;
        let mut bt : Option<BasicTypeEnum> = None;
        let mut widest_alignment = 0;
        for (_, t) in def.fields.iter() {
          if let Some(t) = self.to_basic_type(t) {
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

  fn codegen_return(&mut self, value_node : Option<&TypedNode>) -> Result<(), Error> {
    if let Some(value_node) = value_node {
      let v = self.codegen_expression_to_register(value_node)?;
      self.builder.build_return(v.as_ref().map(|v| v as &BasicValue));
    }
    else {
      self.builder.build_return(None);
    }
    Ok(())
  }

  fn codegen_prototype(
    &mut self, name : &str,
    return_type : &Type,
    args : &[RefStr],
    arg_types : &[Type])
      -> FunctionValue
  {
    let fn_type = self.to_function_type(arg_types, return_type);
    let function = self.module.add_function(name, fn_type, None);

    let i : u32 = !0; //LLVMAttributeFunctionIndex;
    //function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("norecurse"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("nounwind"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("nonlazybind"), 0));
    //function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("readnone"), 0));
    function.add_attribute(i, self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("uwtable"), 0));
    function.add_attribute(i, self.context.create_string_attribute("probe-stack", "__rust_probestack"));
    function.add_attribute(i, self.context.create_string_attribute("target-cpu", "x86-64"));

    // set arguments names
    for (i, arg) in function.get_param_iter().enumerate() {
      Gen::name_basic_type(&arg, args[i].as_ref());
    }
    function
  }

  fn codegen_function(
    mut self,
    function_node : &TypedNode,
    body : &TypedNode,
    name : &str,
    args : &[RefStr],
    arg_types : &[Type])
      -> Result<FunctionValue, Error>
  {
    let function = self.codegen_prototype(name, &body.type_tag, args, arg_types);

    // this function is here because Rust doesn't have a proper try/catch yet
    fn generate(
      function_node : &TypedNode, body : &TypedNode, function : FunctionValue,
      args : &[RefStr], gen : &mut Gen) -> Result<(), Error>
    {
      let entry = gen.context.append_basic_block(&function, "entry");

      gen.builder.position_at_end(&entry);

      // set function parameters
      for (arg_value, arg_name) in function.get_param_iter().zip(args) {
        gen.init_variable(arg_name.clone(), VarScope::Local, arg_value)
          .map_err(|c| error_raw(function_node.loc, c))?;
      }

      // compile body and emit return
      gen.codegen_return(Some(body))?;

      // return the whole thing after verification and optimization
      if function.verify(true) {
        gen.pm.run_on(&function);
        Ok(())
      }
      else {
        error(function_node.loc, "invalid generated function.")
      }
    }

    match generate(function_node, body, function, args, &mut self) {
      Ok(_) => Ok(function),
      Err(e) => {
        dump_module(self.module);
        // This library uses copy semantics for a resource can be deleted,
        // because it is usually not deleted. As a result, it's possible to
        // get use-after-free bugs, so this operation is unsafe. I'm sure
        // this design could be improved.
        unsafe {
          function.delete();
        }
        Err(e)
      }
    }
  }

  /// Code-generates a module, returning a reference to the top-level function in the module
  pub fn codegen_module(mut self, module : &TypedModule) -> Result<(), Error> {
    let gen = &mut self;
    for (name, f) in module.functions.iter() {
      match &f.implementation {
        FunctionImplementation::Normal(body) => {
          let child = gen.child_function_gen();
          child.codegen_function(body, body, name, f.args.as_slice(), f.signature.args.as_slice())?;
        }
        _ => (),
      }
    }
    Ok(())
  }
}
