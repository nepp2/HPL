
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

use std::rc::Rc;

use rustyline::Editor;

use crate::error::{Error, error, error_raw, ErrorContent};
use crate::value::{SymbolTable, display_expr, RefStr, Expr};
use crate::lexer;
use crate::parser;
use crate::parser::ReplParseResult::{Complete, Incomplete};
use crate::typecheck::{
  AstNode, Content, Type, Val, StructDefinition, FunctionDefinition, TypeChecker};

use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context, ContextRef};
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{BasicTypeEnum, BasicType, StructType};
use inkwell::values::{
  BasicValueEnum, BasicValue, FloatValue, IntValue, FunctionValue, PointerValue };
use inkwell::{OptimizationLevel, FloatPredicate};
use inkwell::execution_engine::ExecutionEngine;

fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

macro_rules! codegen_type {
  (FloatValue, $e:ident, $jit:ident) => { $jit.codegen_float($e) };
  (IntValue, $e:ident, $jit:ident) => { $jit.codegen_int($e) };
}

macro_rules! binary_op {
  ($op_name:ident, $type_name:ident, $a:ident, $b:ident, $jit:ident) => {
    {
      let a = codegen_type!($type_name, $a, $jit)?;
      let b = codegen_type!($type_name, $b, $jit)?;
      let fv = ($jit).builder.$op_name(a, b, "op_result");
      fv.into()
    }
  }
}

macro_rules! unary_op {
  ($op_name:ident, $type_name:ident, $a:ident, $jit:ident) => {
    {
      let a = codegen_type!($type_name, $a, $jit)?;
      let fv = ($jit).builder.$op_name(a, "op_result");
      fv.into()
    }
  }
}

macro_rules! compare_op {
  ($op_name:ident, $pred:expr, $type_name:ident, $a:ident, $b:ident, $jit:ident) => {
    {
      let a = codegen_type!($type_name, $a, $jit)?;
      let b = codegen_type!($type_name, $b, $jit)?;
      let fv = ($jit).builder.$op_name($pred, a, b, "cpm_result");
      fv.into()
    }
  }
}

struct LoopLabels {
  condition : BasicBlock,
  exit : BasicBlock,
}

enum ShortCircuitOp { And, Or }

pub struct Jit<'l> {
  context: &'l mut ContextRef,
  builder: Builder,
  variables: HashMap<RefStr, PointerValue>,
  struct_types: HashMap<RefStr, StructType>,

  /// A stack of values indicating the entry and exit labels for each loop
  loop_labels: Vec<LoopLabels>,

  module : &'l mut Module,
  pm : &'l mut PassManager,
}

impl <'l> Jit<'l> {

  pub fn new(context: &'l mut ContextRef, module : &'l mut Module, pm : &'l mut PassManager) -> Jit<'l> {
    Jit {
      context, builder: Builder::create(), module, pm,
      variables: HashMap::new(),
      struct_types: HashMap::new(),
      loop_labels: vec!(),
    }
  }

  pub fn child(&mut self) -> Jit {
    Jit::new(self.context, self.module, self.pm)
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

  fn init_variable(&mut self, name : RefStr, value : BasicValueEnum)
    -> Result<(), ErrorContent>
  {
    if self.variables.contains_key(&name) {
      return Err("variable with this name already defined".into());
    }
    let pointer = self.create_entry_block_alloca(value.get_type(), &name);
    self.builder.build_store(pointer, value);
    self.variables.insert(name, pointer);
    Ok(())
  }

  fn codegen_float(&mut self, n : &AstNode) -> Result<FloatValue, Error> {
  let v = self.codegen_expression(n)?;
  match v {
    Some(BasicValueEnum::FloatValue(f)) => Ok(f),
    t => error(n.loc, format!("Expected float, found {:?}", t)),
  }
}

  fn codegen_int(&mut self, n : &AstNode) -> Result<IntValue, Error> {
    let v = self.codegen_expression(n)?;
    match v {
      Some(BasicValueEnum::IntValue(i)) => Ok(i),
      t => error(n.loc, format!("Expected int, found {:?}", t)),
    }
  }

  fn codegen_short_circuit_op(&mut self, a : &AstNode, b : &AstNode, op : ShortCircuitOp)
    -> Result<BasicValueEnum, Error>
  {
    use ShortCircuitOp::*;
    let short_circuit_outcome = match op {
      And => self.context.bool_type().const_int(0, false),
      Or => self.context.bool_type().const_int(1, false),
    };
    // create basic blocks
    let a_block = self.builder.get_insert_block().unwrap();
    let f = a_block.get_parent().unwrap();
    let b_block = self.context.append_basic_block(&f, "b_block");
    let end_block = self.context.append_basic_block(&f, "end");
    // compute a
    let a_value = self.codegen_int(a)?;
    let a_end_block = self.builder.get_insert_block().unwrap();
    match op {
      And => self.builder.build_conditional_branch(a_value, &b_block, &end_block),
      Or => self.builder.build_conditional_branch(a_value, &end_block, &b_block),
    };
    // maybe compute b
    self.builder.position_at_end(&b_block);
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
    return Ok(phi.as_basic_value());
  }

  fn codegen_expression(&mut self, ast : &AstNode) -> Result<Option<BasicValueEnum>, Error> {
    let v : BasicValueEnum = match &ast.content {
      Content::FunctionCall(name, args) => {
        let f =
          self.module.get_function(name)
          .ok_or_else(|| error_raw(ast.loc, format!("could not find function with name '{}'", name)))?;
        if f.count_params() as usize != args.len() {
            return error(ast.loc, "incorrect number of arguments passed");
        }
        let mut arg_vals = vec!();
        for a in args.iter() {
          let v =
            self.codegen_expression(a)?
            .ok_or_else(|| error_raw(a.loc, "expected value expression"))?;
          arg_vals.push(v);
        }
        return Ok(self.builder.build_call(f, arg_vals.as_slice(), "tmp").try_as_basic_value().left())
      }
      Content::IntrinsicCall(name, args) => {
        if let [a, b] = args.as_slice() {
          match name.as_ref() {
            "+" => binary_op!(build_float_add, FloatValue, a, b, self),
            "-" => binary_op!(build_float_sub, FloatValue, a, b, self),
            "*" => binary_op!(build_float_mul, FloatValue, a, b, self),
            "/" => binary_op!(build_float_div, FloatValue, a, b, self),
            ">" => compare_op!(build_float_compare, FloatPredicate::OGT, FloatValue, a, b, self),
            ">=" => compare_op!(build_float_compare, FloatPredicate::OGE, FloatValue, a, b, self),
            "<" => compare_op!(build_float_compare, FloatPredicate::OLT, FloatValue, a, b, self),
            "<=" => compare_op!(build_float_compare, FloatPredicate::OLE, FloatValue, a, b, self),
            "==" => compare_op!(build_float_compare, FloatPredicate::OEQ, FloatValue, a, b, self),
            "&&" => self.codegen_short_circuit_op(a, b, ShortCircuitOp::And)?,
            "||" => self.codegen_short_circuit_op(a, b, ShortCircuitOp::Or)?,
            _ => return error(ast.loc, "encountered unrecognised intrinsic"),
          }        
        }
        else if let [a] = args.as_slice() {
          match name.as_ref() {
            "unary_-" => unary_op!(build_float_neg, FloatValue, a, self),
            "unary_!" => unary_op!(build_not, IntValue, a, self),
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
          // create a dummy block to hold instructions after the break
          let f = self.builder.get_insert_block().unwrap().get_parent().unwrap();
          let dummy_block = self.context.append_basic_block(&f, "dummy_block");
          self.builder.build_unconditional_branch(&labels.exit);
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
        let then_block = self.context.append_basic_block(&f, "then");
        let else_block = self.context.append_basic_block(&f, "else");
        let end_block = self.context.append_basic_block(&f, "endif");
        // conditional branch
        let cond_value = self.codegen_int(cond_node)?;
        self.builder.build_conditional_branch(cond_value, &then_block, &else_block);
        // then block
        self.builder.position_at_end(&then_block);
        let then_value = self.codegen_expression(then_node)?;
        let then_block = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(&end_block);
        // else block
        self.builder.position_at_end(&else_block);
        let else_value = self.codegen_expression(else_node)?;
        let else_block = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(&end_block);
        // end block
        self.builder.position_at_end(&end_block);
        if then_value.is_some() && else_value.is_some() {
          let v1 = then_value.unwrap();
          let v2 = else_value.unwrap();
          let phi = self.builder.build_phi(v1.get_type(), "if_result");
          phi.add_incoming(&[
            (&v1, &then_block),
            (&v2, &else_block),
          ]);
          return Ok(Some(phi.as_basic_value()))
        }
        return Ok(None);
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
      Content::FunctionDefinition(def, body) => {
        self.child().codegen_function(ast, body, &def.name, &def.args)?;
        return Ok(None);
      }
      Content::StructDefinition(_def) => {
        // TODO: is nothing required here?
        return Ok(None);
      }
      Content::StructInstantiate(def, args) => {
        let t = self.struct_type(def).as_basic_type_enum();
        let ptr = self.create_entry_block_alloca(t, &def.name);
        let struct_val = self.builder.build_load(ptr, "struct_load").into_struct_value();
        for (i, a) in args.iter().enumerate() {
          let v = self.codegen_expression(a)?.unwrap();
          self.builder.build_insert_value(struct_val, v, i as u32, &def.fields[i].0);
        }
        struct_val.as_basic_value_enum()
      }
      Content::FieldAccess(x, field_index) => {
        let (struct_val_node, field_name) = (&x.0, &x.1);
        let v = *self.codegen_expression(struct_val_node)?.unwrap().as_struct_value();
        self.builder.build_extract_value(v, *field_index as u32, field_name).unwrap()
      }
      Content::Assignment(ns) => {
        let (assign_node, value_node) = (&ns.0, &ns.1);
        let ptr =
          self.codegen_pointer(assign_node)?.
          ok_or_else(|| error_raw(assign_node.loc, "cannot assign to this construct"))?;
        let value = self.codegen_expression(value_node)?.unwrap();
        self.builder.build_store(ptr, value);
        return Ok(None);
      }
      Content::VariableInitialise(name, value_node) => {
        let value = self.codegen_expression(value_node)?
          .ok_or_else(|| error_raw(value_node.loc, "expected value for initialiser, found void"))?;
        self.init_variable(name.clone(), value)
          .map_err(|c| error_raw(ast.loc, c))?; 
        return Ok(None);
      }
      Content::VariableReference(name) => {
        if let Some(ptr) = self.variables.get(name) {
          self.builder.build_load(*ptr, name)
        }
        else {
          return error(ast.loc, format!("unknown variable name '{}'.", name));
        }
      }
      Content::Literal(v) => {
        match v {
          Val::Float(f) => self.context.f64_type().const_float(*f).into(),
          Val::Bool(b) =>
            self.context.bool_type().const_int(if *b { 1 } else { 0 }, false).into(),
          Val::Void => return Ok(None),
        }
      }
    };
    Ok(Some(v))
  }

  fn codegen_pointer(&mut self, ast : &AstNode) -> Result<Option<PointerValue>, Error> {
    match &ast.content {
      Content::VariableReference(name) => {
        if let Some(ptr) = self.variables.get(name) {
          Ok(Some(*ptr))
        }
        else {
          return error(ast.loc, format!("unknown variable name '{}'.", name));
        }
      }
      _ => Ok(None)
    }
  }

  fn to_basic_type(&mut self, t : &Type) -> Option<BasicTypeEnum> {
    match t {
      Type::Void => None,
      Type::Float => Some(self.context.f64_type().into()),
      Type::Bool => Some(self.context.bool_type().into()),
      Type::Struct(def) => Some(self.struct_type(def).as_basic_type_enum()),
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

  fn codegen_function(
    mut self,
    function_node : &AstNode,
    body : &AstNode,
    name : &str,
    args : &[RefStr])
      -> Result<FunctionValue, Error>
  {
    /* TODO: is this needed?
    // check if declaration with this name was already done
    if module.get_function(name).is_some() {
      return error(node, format!("function '{}' already defined", name));
    };
    */

    let f64_type = self.context.f64_type();
    let arg_types = std::iter::repeat(f64_type)
      .take(args.len())
      .map(|f| f.into())
      .collect::<Vec<BasicTypeEnum>>();
    let arg_types = arg_types.as_slice();

    let fn_type = match &body.type_tag {
      Type::Bool => self.context.bool_type().fn_type(arg_types, false),
      Type::Float => self.context.f64_type().fn_type(arg_types, false),
      Type::Void => self.context.void_type().fn_type(arg_types, false),
      Type::Struct(def) => self.struct_type(def).fn_type(arg_types, false),
    };
    let function = self.module.add_function(name, fn_type, None);

    // this function is here because Rust doesn't have a proper try/catch yet
    fn generate(
      function_node : &AstNode, body : &AstNode, function : FunctionValue,
      args : &[RefStr], jit : &mut Jit) -> Result<(), Error>
    {
      // set arguments names
      for (i, arg) in function.get_param_iter().enumerate() {
        arg.into_float_value().set_name(args[i].as_ref());
      }

      let entry = jit.context.append_basic_block(&function, "entry");

      jit.builder.position_at_end(&entry);

      // set function parameters
      for (arg_value, arg_name) in function.get_param_iter().zip(args) {
        jit.init_variable(arg_name.clone(), arg_value)
          .map_err(|c| error_raw(function_node.loc, c))?;
      }

      // compile body
      let body_val = jit.codegen_expression(body)?;

      // emit return (via stupid API)
      match body_val {
        Some(b) => {
          jit.builder.build_return(Some(&b));
        }
        None => {
          jit.builder.build_return(None);
        }
      }

      // return the whole thing after verification and optimization
      if function.verify(true) {
        jit.pm.run_on_function(&function);
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
}

pub struct Interpreter {
  sym : SymbolTable,
  context : ContextRef,
  module : Module,
  functions : HashMap<RefStr, Rc<FunctionDefinition>>,
  struct_types : HashMap<RefStr, Rc<StructDefinition>>,
  pass_manager : PassManager,
}

impl Interpreter {
  pub fn new() -> Interpreter {
    let sym = SymbolTable::new();
    let context = Context::get_global();
    let module = Module::create("top_level");
    let functions = HashMap::new();
    let struct_types = HashMap::new();
    let pm = PassManager::create_for_function(&module);

    // TODO: enable optimisation again

   // pm.add_instruction_combining_pass();
    //pm.add_reassociate_pass();
    //pm.add_gvn_pass();
    //pm.add_cfg_simplification_pass();
    //pm.add_basic_alias_analysis_pass();
    //pm.add_promote_memory_to_register_pass();
    //pm.add_instruction_combining_pass();
    //pm.add_reassociate_pass();
    
    pm.initialize();

    Interpreter { sym, context, module, functions, struct_types, pass_manager: pm }
  }

  pub fn function_jit(&mut self) -> Jit {
    Jit::new(&mut self.context, &mut self.module, &mut self.pass_manager)
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {
    let tokens =
        lexer::lex(code, &mut self.sym)
        .map_err(|mut es| es.remove(0))?;
    let expr = parser::parse(tokens, &mut self.sym)?;
    self.run_expression(&expr)
  }

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    run_expression(expr, self)
  }
}

fn run_expression(expr : &Expr, i: &mut Interpreter) -> Result<Val, Error> {
  let mut type_checker = 
    TypeChecker::new(HashMap::new(), &mut i.functions, &mut i.struct_types, &mut i.sym);
  let ast = type_checker.to_ast(expr)?;
  let f = {
    let jit = i.function_jit();
    jit.codegen_function(&ast, &ast, "top_level", &[])?
  };
  println!("{}", display_expr(expr));
  dump_module(&i.module);

  fn execute<T>(expr : &Expr, f : FunctionValue, ee : &ExecutionEngine) -> Result<T, Error> {
    let function_name = f.get_name().to_str().unwrap();
    let v = unsafe {
      let jit_function =
        ee.get_function::<unsafe extern "C" fn() -> T>(function_name)
        .map_err(|e| error_raw(expr, format!("{:?}", e)))?;
      jit_function.call()
    };
    Ok(v)
  }
  let ee =
    i.module.create_jit_execution_engine(OptimizationLevel::None)
    .map_err(|e| error_raw(expr, e.to_string()))?;
  let result = match ast.type_tag {
    Type::Bool => execute::<bool>(expr, f, &ee).map(Val::Bool),
    Type::Float => execute::<f64>(expr, f, &ee).map(Val::Float),
    Type::Void => execute::<()>(expr, f, &ee).map(|_| Val::Void),
    Type::Struct(_) =>
      error(expr, "can't return a struct from a top-level function"),
  };
  ee.remove_module(&i.module).unwrap();
  result
}

pub fn run_repl() {

  let mut rl = Editor::<()>::new();
  let mut i = Interpreter::new();

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut i.sym)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut i.sym);
      match parsing_result {
        Ok(Complete(e)) => {
          // we have parsed a full expression
          rl.add_history_entry(input_line);
          match run_expression(&e, &mut i) {
            Ok(value) => {
              println!("{:?}", value)
            }
            Err(err) => {
              println!("error: {}", err);
            }
          }
          break;
        }
        Ok(Incomplete) => {
          // get more tokens
          let next_line = rl.readline(". ").unwrap();
          input_line.push_str("\n");
          input_line.push_str(next_line.as_str());
        }
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      }
    }
  }
}
