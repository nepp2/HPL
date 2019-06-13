
/*

Modified from code released under the license below:

######################################################
Copyright (c) 2014 Jauhien Piatlicki

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

[Except as contained in this notice, the name of <copyright holders>
shall not be used in advertising or otherwise to promote the sale, use
or other dealings in this Software without prior written authorization
from Jauhien Piatlicki.]
######################################################

*/

// TODO: Carlos says I should have more comments than the occasional TODO

use crate::error::{Error, error, error_raw, ErrorContent};
use crate::value::RefStr;
use crate::typecheck::{
  AstNode, Content, Type, Val, StructDefinition, FunctionDefinition, VarScope};

use std::rc::Rc;
use std::collections::HashMap;

use inkwell::AddressSpace;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context};
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::types::{BasicTypeEnum, BasicType, StructType, PointerType, FunctionType, AnyTypeEnum};
use inkwell::values::{
  BasicValueEnum, BasicValue, FloatValue, IntValue, FunctionValue, PointerValue, GlobalValue };
use inkwell::{FloatPredicate, IntPredicate};

pub fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

macro_rules! codegen_type {
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
      let fv = ($gen).builder.$op_name(a, "op_result");
      reg(fv.into())
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
  builder: Builder,
  functions: &'l mut HashMap<RefStr, FunctionValue>,
  external_globals: &'l mut HashMap<RefStr, GlobalValue>,
  function_defs: &'l HashMap<RefStr, Rc<FunctionDefinition>>,
  global_var_types: &'l HashMap<RefStr, Type>,
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
    functions: &'l mut HashMap<RefStr, FunctionValue>,
    external_globals: &'l mut HashMap<RefStr, GlobalValue>,
    function_defs: &'l HashMap<RefStr, Rc<FunctionDefinition>>,
    global_var_types: &'l HashMap<RefStr, Type>,
    pm : &'l PassManager<FunctionValue>,
  )
      -> Gen<'l>
  {
    let builder = context.create_builder();
    let variables = HashMap::new();
    Gen {
      context, module, builder,
      functions, external_globals,
      function_defs,
      global_var_types, variables,
      struct_types: HashMap::new(),
      loop_labels: vec!(),
      pm,
    }
  }

  pub fn child_function_gen<'lc>(&'lc mut self, global_var_types: &'lc HashMap<RefStr, Type>)
    -> Gen<'lc>
  {
    Gen::new(self.context, self.module, self.functions, self.external_globals, self.function_defs, global_var_types, self.pm)
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

  fn init_variable(&mut self, name : RefStr, var_scope : VarScope, value : BasicValueEnum)
    -> Result<(), ErrorContent>
  {
    if self.variables.contains_key(&name) {
      return Err(format!("variable with name '{}' already defined", name).into());
    }
    let pointer = match var_scope {
      VarScope::Global => {
        //TODO let gv = self.module.add_global(value.get_type(), Some(AddressSpace::Global), &name);
        let gv = self.module.add_global(value.get_type(), None, &name);
        let null = const_null(value.get_type());
        gv.set_initializer(&null);
        gv.set_constant(false);
        gv.set_linkage(Linkage::Internal);
        gv.set_alignment(8);
        gv.as_pointer_value()
      }
      VarScope::Local => {
        self.create_entry_block_alloca(value.get_type(), &name)
      }
    };
    self.builder.build_store(pointer, value);
    self.variables.insert(name, pointer);
    Ok(())
  }

  fn codegen_value(&mut self, n : &AstNode) -> Result<BasicValueEnum, Error> {
    Ok(self.codegen_expression_to_register(n)?.unwrap())
  }

  fn codegen_float(&mut self, n : &AstNode) -> Result<FloatValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::FloatValue(f) => Ok(f),
      t => error(n.loc, format!("Expected float, found {:?}", t)),
    }
  }

  fn codegen_int(&mut self, n : &AstNode) -> Result<IntValue, Error> {
    let v = self.codegen_value(n)?;
    match v {
      BasicValueEnum::IntValue(i) => Ok(i),
      t => error(n.loc, format!("Expected int, found {:?}", t)),
    }
  }

  fn codegen_expression_to_register(&mut self, ast : &AstNode) -> Result<Option<BasicValueEnum>, Error> {
    if let Some(v) = self.codegen_expression(ast)? {
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

  fn codegen_short_circuit_op(&mut self, a : &AstNode, b : &AstNode, op : ShortCircuitOp)
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

  fn codegen_function_call(&mut self, ast : &AstNode, name : &RefStr, args : &[AstNode])
    -> Result<Option<GenVal>, Error>
  {
    let f =
      *self.functions.get(name)
      .ok_or_else(|| error_raw(ast.loc, format!("could not find function with name '{}'", name)))?;
    if f.count_params() as usize != args.len() {
        return error(ast.loc, "incorrect number of arguments passed");
    }
    // insert a prototype if needed
    let f = {
      if let Some(local_f) = self.module.get_function(name) {
        local_f
      }
      else{
        let def = self.function_defs.get(name).unwrap();
        let f = self.codegen_prototype(&def.name, &def.signature.return_type, &def.args, &def.signature.args);
        f.set_linkage(Linkage::External);
        f
      }
    };

    let mut arg_vals = vec!();
    for a in args.iter() {
      let v = self.codegen_value(a)?;
      arg_vals.push(v);
    }
    let call = self.builder.build_call(f, arg_vals.as_slice(), "tmp");
    println!("{:?}", call);
    let r = call.try_as_basic_value().left();
    return Ok(r.map(reg));
  }

  fn codegen_expression(&mut self, ast : &AstNode) -> Result<Option<GenVal>, Error> {
    let v : GenVal = match &ast.content {
      Content::FunctionCall(name, args) => {
        return self.codegen_function_call(ast, name, args);
      }
      Content::IntrinsicCall(name, args) => {
        if let [a, b] = args.as_slice() {
          match (&a.type_tag, name.as_ref()) {
          (Type::Float, "+") => binary_op!(build_float_add, FloatValue, a, b, self),
            (Type::Float, "-") => binary_op!(build_float_sub, FloatValue, a, b, self),
            (Type::Float, "*") => binary_op!(build_float_mul, FloatValue, a, b, self),
            (Type::Float, "/") => binary_op!(build_float_div, FloatValue, a, b, self),
            (Type::Float, ">") => compare_op!(build_float_compare, FloatPredicate::OGT, FloatValue, a, b, self),
            (Type::Float, ">=") => compare_op!(build_float_compare, FloatPredicate::OGE, FloatValue, a, b, self),
            (Type::Float, "<") => compare_op!(build_float_compare, FloatPredicate::OLT, FloatValue, a, b, self),
            (Type::Float, "<=") => compare_op!(build_float_compare, FloatPredicate::OLE, FloatValue, a, b, self),
            (Type::Float, "==") => compare_op!(build_float_compare, FloatPredicate::OEQ, FloatValue, a, b, self),
            (Type::I64, "+") => binary_op!(build_int_add, IntValue, a, b, self),
            (Type::I64, "-") => binary_op!(build_int_sub, IntValue, a, b, self),
            (Type::I64, "*") => binary_op!(build_int_mul, IntValue, a, b, self),
            //(Type::I64, "/") => binary_op!(build_int_div, IntValue, a, b, self),
            (Type::I64, ">") => compare_op!(build_int_compare, IntPredicate::SGT, IntValue, a, b, self),
            (Type::I64, ">=") => compare_op!(build_int_compare, IntPredicate::SGE, IntValue, a, b, self),
            (Type::I64, "<") => compare_op!(build_int_compare, IntPredicate::SLT, IntValue, a, b, self),
            (Type::I64, "<=") => compare_op!(build_int_compare, IntPredicate::SLE, IntValue, a, b, self),
            (Type::I64, "==") => compare_op!(build_int_compare, IntPredicate::EQ, IntValue, a, b, self),
            (Type::Bool, "&&") => self.codegen_short_circuit_op(a, b, ShortCircuitOp::And)?,
            (Type::Bool, "||") => self.codegen_short_circuit_op(a, b, ShortCircuitOp::Or)?,
            _ => return error(ast.loc, "encountered unrecognised intrinsic"),
          }        
        }
        else if let [a] = args.as_slice() {
          match (&a.type_tag, name.as_ref()) {
            (Type::Float, "unary_-") => unary_op!(build_float_neg, FloatValue, a, self),
            (Type::I64, "unary_-") => unary_op!(build_int_neg, IntValue, a, self),
            (Type::Bool, "unary_!") => unary_op!(build_not, IntValue, a, self),
            _ => return error(ast.loc, "encountered unrecognised intrinsic"),
          }
        }
        else {
          return error(ast.loc, "encountered unrecognised intrinsic");
        }
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
          return error(ast.loc, "can only break inside a loop");
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
      Content::CFunctionPrototype(def) => {
        let f = self.codegen_prototype(&def.name, &def.signature.return_type, &def.args, &def.signature.args);
        self.functions.insert(def.name.clone(), f);
        return Ok(None);
      }
      Content::FunctionDefinition(def, body) => {
        let global_var_types = HashMap::new();
        self.child_function_gen(&global_var_types).codegen_function(
          ast, body, &def.name, &def.args, &def.signature.args, false)?;
        return Ok(None);
      }
      Content::StructDefinition(_def) => {
        // TODO: is nothing required here?
        return Ok(None);
      }
      Content::StructInstantiate(def, args) => {
        let t = self.struct_type(def).as_basic_type_enum();
        let ptr = self.create_entry_block_alloca(t, &def.name);
        for (i, a) in args.iter().enumerate() {
          let v = self.codegen_value(a)?;
          let element_ptr = unsafe {
            self.builder.build_struct_gep(ptr, i as u32, &def.fields[i].0)
          };
          self.builder.build_store(element_ptr, v);
        }
        pointer(ptr)
      }
      Content::FieldAccess(x, field_index) => {
        let (struct_val_node, field_name) = (&x.0, &x.1);
        let v = self.codegen_expression(struct_val_node)?.unwrap();
        match v.storage {
          Storage::Register => {
            // if the struct is in a register, dereference the field into a register
            let reg_val =
              self.builder.build_extract_value(
                *v.value.as_struct_value(), *field_index as u32, field_name).unwrap();
            reg(reg_val)
          }
          Storage::Pointer => {
            // if this is a pointer to the struct, get a pointer to the field
            let ptr = *v.value.as_pointer_value();
            let field_ptr = unsafe {
              self.builder.build_struct_gep(ptr, *field_index as u32, field_name)
            };
            pointer(field_ptr)
          }
        }
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
        let reg_val = self.codegen_expression_to_register(value_node)?.unwrap();
        self.builder.build_store(ptr, reg_val);
        return Ok(None);
      }
      Content::VariableInitialise(name, value_node, var_scope) => {
        let v = self.codegen_expression_to_register(value_node)?
          .ok_or_else(|| error_raw(value_node.loc, "expected value for initialiser, found void"))?;
        self.init_variable(name.clone(), *var_scope, v)
          .map_err(|c| error_raw(ast.loc, c))?; 
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
        else if let Some(type_tag) = self.global_var_types.get(name) {
          let t = self.to_basic_type(type_tag).unwrap();
          let gv = self.module.add_global(t, Some(AddressSpace::Global), &name);
          gv.set_constant(false);
          self.external_globals.insert(name.clone(), gv);
          pointer(gv.as_pointer_value())
        }
        else {
          return error(ast.loc, format!("unknown variable name '{}'.", name));
        }
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
        self.codegen_return(n.as_ref().map(|b| b as &AstNode))?;
        // create a dummy block to hold instructions after the return
        let f = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        let dummy_block = self.context.append_basic_block(&f, "dummy_block");
        self.builder.position_at_end(&dummy_block);
        return Ok(None);
      }
      Content::Literal(v) => {
        match v {
          Val::Float(f) => reg(self.context.f64_type().const_float(*f).into()),
          Val::I64(i) => reg(self.context.i64_type().const_int(*i as u64, false).into()),
          Val::Bool(b) =>
            reg(self.context.bool_type().const_int(if *b { 1 } else { 0 }, false).into()),
          Val::Void => return Ok(None),
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
      Type::Float => Some(self.context.f64_type().into()),
      Type::I64 => Some(self.context.i64_type().into()),
      Type::Bool => Some(self.context.bool_type().into()),
      Type::Struct(def) => Some(self.struct_type(def).as_basic_type_enum()),
      Type::Ptr(t) => {
        let bt = self.to_basic_type(t);
        Some(self.pointer_to_type(bt).into())
      }
    }
  }

  fn pointer_to_type(&self, t : Option<BasicTypeEnum>) -> PointerType {
    if let Some(t) = t {
    use BasicTypeEnum::*;
      match t {
        ArrayType(t) => t.ptr_type(AddressSpace::Local),
        IntType(t) => t.ptr_type(AddressSpace::Local),
        FloatType(t) => t.ptr_type(AddressSpace::Local),
        PointerType(t) => t.ptr_type(AddressSpace::Local),
        StructType(t) => t.ptr_type(AddressSpace::Local),
        VectorType(t) => t.ptr_type(AddressSpace::Local),
      }
    }
    else {
      self.context.void_type().ptr_type(AddressSpace::Local)
    }
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

  fn struct_type(&mut self, def : &StructDefinition) -> StructType {
    if let Some(t) = self.struct_types.get(&def.name) {
      return *t;
    }
    let types =
      def.fields.iter().map(|(_, t)| {
        self.to_basic_type(t).unwrap()
      })
      .collect::<Vec<BasicTypeEnum>>();
    let t = self.context.struct_type(&types, false);
    self.struct_types.insert(def.name.clone(), t);
    return t;
  }

  fn codegen_return(&mut self, value_node : Option<&AstNode>) -> Result<(), Error> {
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
    let arg_types =
      arg_types.iter().map(|t| self.to_basic_type(t).unwrap())
      .collect::<Vec<BasicTypeEnum>>();
    let arg_types = arg_types.as_slice();

    let return_type = self.to_basic_type(return_type);
    let fn_type = self.function_type(return_type, arg_types);
    let function = self.module.add_function(name, fn_type, Some(Linkage::External));

    // set arguments names
    for (i, arg) in function.get_param_iter().enumerate() {
      Gen::name_basic_type(&arg, args[i].as_ref());
    }
    function
  }

  fn codegen_function(
    mut self,
    function_node : &AstNode,
    body : &AstNode,
    name : &str,
    args : &[RefStr],
    arg_types : &[Type],
    is_top_level : bool)
      -> Result<FunctionValue, Error>
  {
    let function = self.codegen_prototype(name, &body.type_tag, args, arg_types);

    if !is_top_level {
      self.functions.insert(name.into(), function);
    }

    // this function is here because Rust doesn't have a proper try/catch yet
    fn generate(
      function_node : &AstNode, body : &AstNode, function : FunctionValue,
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
  pub fn codegen_module(self, ast : &AstNode) -> Result<FunctionValue, Error> {
    self.codegen_function(&ast, &ast, "top_level", &[], &[], true)
  }
}
