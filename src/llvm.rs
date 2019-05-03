
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

use std::io;
use std::io::Write;
use std::rc::Rc;
use std::any::Any;

use rustyline::error::ReadlineError;
use rustyline::Editor;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::value::{SymbolTable, display_expr, RefStr, Expr, ExprTag};
use crate::lexer;
use crate::parser;
use crate::parser::ReplParseResult::{Complete, Incomplete};

use std::collections::HashMap;
use itertools::Itertools;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context, ContextRef};
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{BasicTypeEnum, AnyTypeEnum};
use inkwell::values::{BasicValueEnum, FloatValue, IntValue, FunctionValue };
use inkwell::{OptimizationLevel, FloatPredicate};
use inkwell::execution_engine::ExecutionEngine;

#[derive(Clone, Copy, PartialEq)]
pub enum Type {
  Void, Float, Bool
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Val {
  Void, Float(f64), Bool(bool)
}

impl Type {
  fn from_string(s : &str) -> Option<Type> {
    match s {
      "float" => Some(Type::Float),
      "bool" => Some(Type::Bool),
      "()" => Some(Type::Void),
      other => {
        if other == parser::NO_TYPE {
          Some(Type::Float)
        }
        else {
          None
        }
      }
    }
  }
}

enum Content {
  Literal(f64),
  VariableReference(RefStr),
  IfThen(Box<(AstNode, AstNode)>),
  IfThenElse(Box<(AstNode, AstNode, AstNode)>),
  Block(Vec<AstNode>),
  FunctionDefinition(RefStr, Vec<(RefStr, Type)>, Box<AstNode>),
  FunctionCall(RefStr, Vec<AstNode>),
  IntrinsicCall(RefStr, Vec<AstNode>),
}

struct AstNode {
  type_tag : Type,
  content : Content,
  loc : TextLocation,
}

fn ast(expr : &Expr, type_tag : Type, content : Content) -> AstNode {
  AstNode {
    type_tag,
    content,
    loc: expr.loc,
  }
}

struct TypeChecker<'l> {
  variables: HashMap<RefStr, Type>,
  functions: &'l mut HashMap<RefStr, Type>,
  sym: &'l mut SymbolTable,
}

impl <'l> TypeChecker<'l> {
  fn to_ast(&mut self, expr : &Expr) -> Result<AstNode, Error> {
    match &expr.tag {
      ExprTag::Tree(_) => {
        let instr = expr.tree_symbol_unwrap()?;
        let children = expr.children.as_slice();
        match (instr.as_ref(), children) {
          ("call", exprs) => {
            let function_name = exprs[0].symbol_unwrap()?;
            if exprs.len() == 3 {
              let tag = match function_name.as_ref() {
                "+" | "-" | "*" | "/" => Some(Type::Float),
                ">" | ">="| "<" | "<=" | "==" => Some(Type::Bool),
                _ => None,
              };
              if let Some(tag) = tag {
                let a = self.to_ast(&exprs[1])?;
                let b = self.to_ast(&exprs[2])?;
                return Ok(ast(expr, tag, Content::IntrinsicCall(function_name.clone(), vec!(a, b))))
              }
            }
            if let Some(t) = self.functions.get(function_name.as_ref()) {
              let t = *t;
              let args =
                exprs[1..].iter().map(|e| self.to_ast(e))
                .collect::<Result<Vec<AstNode>, Error>>()?;
              return Ok(ast(expr, t, Content::FunctionCall(function_name.clone(), args)));
            }
            error(expr, "unknown function")
          }
          ("if", exprs) => {
            if exprs.len() > 3 {
              return error(expr, "malformed if expression");
            }
            let condition = self.to_ast(&exprs[0])?;
            let then_branch = self.to_ast(&exprs[1])?;
            if exprs.len() == 3 {
              let else_branch = self.to_ast(&exprs[2])?;
              if then_branch.type_tag != else_branch.type_tag {
                return error(expr, "if/else branch type mismatch");
              }
              Ok(ast(expr, then_branch.type_tag, Content::IfThenElse(Box::new((condition, then_branch, else_branch)))))
            }
            else {
              Ok(ast(expr, Type::Void, Content::IfThen(Box::new((condition, then_branch)))))
            }
          }
          ("block", exprs) => {
            let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<AstNode>, Error>>()?;
            let tag = if nodes.len() > 0 {
              nodes[nodes.len()-1].type_tag
            }
            else{
              Type::Void
            };
            Ok(ast(expr, tag, Content::Block(nodes)))
          }
          ("fun", exprs) => {
            let name = exprs[0].symbol_unwrap()?;
            let args_exprs = exprs[1].children.as_slice();
            let function_body = &exprs[2];
            let mut args = vec!();
            for (name_expr, type_expr) in args_exprs.iter().tuples() {
              let name = name_expr.symbol_unwrap()?;
              let type_tag =
                Type::from_string(type_expr.symbol_unwrap()?.as_ref())
                .ok_or_else(|| error_raw(type_expr, "unrecognised type"))?;
              args.push((name.clone(), type_tag));
            }
            let mut type_checker = TypeChecker { variables : args.iter().cloned().collect(), functions: self.functions, sym: self.sym };
            let body = type_checker.to_ast(function_body)?;
            if self.functions.contains_key(name.as_ref()) {
              return error(expr, "function with that name already defined");
            }
            self.functions.insert(name.clone(), body.type_tag);
            Ok(ast(expr, Type::Void, Content::FunctionDefinition(name.clone(), args, Box::new(body))))
          }
          _ => return error(expr, "unsupported expression"),
        }
      }
      ExprTag::Symbol(s) => {
        if let Some(t) = self.variables.get(s.as_ref()) {
          Ok(ast(expr, *t, Content::VariableReference(s.clone())))
        }
        else {
          error(expr, "unknown variable name")
        }
      }
      ExprTag::LiteralFloat(f) => {
        Ok(ast(expr, Type::Float, Content::Literal(*f as f64)))
      }
      _ => error(expr, "unsupported expression"),
    }
  }
}

pub struct Jit<'l> {
  context: &'l mut ContextRef,
  builder: &'l mut Builder,
  named_values: HashMap<RefStr, BasicValueEnum>,
  module : &'l mut Module,
  pm : &'l mut PassManager,
  sym : &'l mut SymbolTable,
}

impl <'l> Jit<'l> {
  pub fn new(context: &'l mut ContextRef, builder: &'l mut Builder, module : &'l mut Module, pm : &'l mut PassManager, sym : &'l mut SymbolTable) -> Jit<'l> {
    Jit {
      context, builder, module, pm,
      named_values: HashMap::new(),
      sym,
    }
  }
}

fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

fn codegen_float(n : &AstNode, jit: &mut Jit) -> Result<FloatValue, Error> {
  let v = codegen_expression(n, jit)?;
  match v {
    Some(BasicValueEnum::FloatValue(f)) => Ok(f),
    t => error(n.loc, format!("Expected float, found {:?}", t)),
  }
}

fn codegen_int(n : &AstNode, jit: &mut Jit) -> Result<IntValue, Error> {
  let v = codegen_expression(n, jit)?;
  match v {
    Some(BasicValueEnum::IntValue(i)) => Ok(i),
    t => error(n.loc, format!("Expected int, found {:?}", t)),
  }
}

macro_rules! codegen_type {
  (FloatValue, $e:ident, $jit:ident) => { codegen_float($e, $jit) };
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

fn codegen_expression(ast : &AstNode, jit: &mut Jit) -> Result<Option<BasicValueEnum>, Error> {
  let v : BasicValueEnum = match &ast.content {
    Content::FunctionCall(name, args) => {
      let f =
        jit.module.get_function(name)
        .ok_or_else(|| error_raw(ast.loc, format!("could not find function with name '{}'", name)))?;
      if f.count_params() as usize != args.len() {
          return error(ast.loc, "incorrect number of arguments passed");
      }
      let mut arg_vals = vec!();
      for a in args.iter() {
        let v =
          codegen_expression(a, jit)?
          .ok_or_else(|| error_raw(a.loc, "expected value expression"))?;
        arg_vals.push(v);
      }
      return Ok(jit.builder.build_call(f, arg_vals.as_slice(), "tmp").try_as_basic_value().left())
    }
    Content::IntrinsicCall(name, args) => {
      if let [a, b] = args.as_slice() {
        match name.as_ref() {
          "+" => binary_op!(build_float_add, FloatValue, a, b, jit),
          "-" => binary_op!(build_float_sub, FloatValue, a, b, jit),
          "*" => binary_op!(build_float_mul, FloatValue, a, b, jit),
          "/" => binary_op!(build_float_div, FloatValue, a, b, jit),
          ">" => compare_op!(build_float_compare, FloatPredicate::OGT, FloatValue, a, b, jit),
          ">=" => compare_op!(build_float_compare, FloatPredicate::OGE, FloatValue, a, b, jit),
          "<" => compare_op!(build_float_compare, FloatPredicate::OLT, FloatValue, a, b, jit),
          "<=" => compare_op!(build_float_compare, FloatPredicate::OLE, FloatValue, a, b, jit),
          "==" => compare_op!(build_float_compare, FloatPredicate::OEQ, FloatValue, a, b, jit),
          _ => return error(ast.loc, "encountered unrecognised intrinsic"),
        }        
      }
      else {
        return error(ast.loc, "encountered unrecognised intrinsic");
      }
    }
    Content::IfThen(ns) => {
      let (cond_node, then_node) = (&ns.0, &ns.1);
      let cond_value = codegen_int(cond_node, jit)?;
      let block = jit.builder.get_insert_block().unwrap();
      let f = block.get_parent().unwrap();
      let then_block = jit.context.append_basic_block(&f, "then");
      let end_block = jit.context.append_basic_block(&f, "endif");
      jit.builder.build_conditional_branch(cond_value, &then_block, &end_block);
      jit.builder.position_at_end(&then_block);
      codegen_expression(then_node, jit)?;
      jit.builder.build_unconditional_branch(&end_block);
      return Ok(None);
    }
    Content::IfThenElse(ns) => {
      let (cond_node, then_node, else_node) = (&ns.0, &ns.1, &ns.2);
      // generate condition value
      let cond_value = codegen_int(cond_node, jit)?;
      // create basic blocks
      let block = jit.builder.get_insert_block().unwrap();
      let f = block.get_parent().unwrap();
      let then_block = jit.context.append_basic_block(&f, "then");
      let else_block = jit.context.append_basic_block(&f, "else");
      let end_block = jit.context.append_basic_block(&f, "endif");
      // conditional branch
      jit.builder.build_conditional_branch(cond_value, &then_block, &else_block);
      // then block
      jit.builder.position_at_end(&then_block);
      let then_value = codegen_expression(then_node, jit)?;
      let then_block = jit.builder.get_insert_block().unwrap();
      jit.builder.build_unconditional_branch(&end_block);
      // else block
      jit.builder.position_at_end(&else_block);
      let else_value = codegen_expression(else_node, jit)?;
      let else_block = jit.builder.get_insert_block().unwrap();
      jit.builder.build_unconditional_branch(&end_block);
      // end block
      jit.builder.position_at_end(&end_block);
      if then_value.is_some() && else_value.is_some() {
        let v1 = then_value.unwrap();
        let v2 = else_value.unwrap();
        let phi = jit.builder.build_phi(v1.get_type(), "if_result");
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
          codegen_expression(&nodes[i], jit)?;
        }
        return codegen_expression(&nodes[node_count-1], jit);
      }
      return Ok(None);
    }
    Content::FunctionDefinition(name, arg_nodes, body) => {
      let mut args = vec!();
      for (arg, _) in arg_nodes.iter() {
        args.push(arg.clone());
      }
      let current_block = jit.builder.get_insert_block().unwrap();
      codegen_function(ast, body, name.as_ref(), args, jit)?;
      jit.builder.position_at_end(&current_block);
      return Ok(None);
    }
    Content::VariableReference(s) => {
      if let Some(value) = jit.named_values.get(s) {
        *value
      }
      else {
        return error(ast.loc, "unknown variable name")
      }
    }
    Content::Literal(f) => {
      jit.context.f64_type().const_float(*f).into()
    }
    _ => return error(ast.loc, "unsupported expression"),
  };
  Ok(Some(v))
}

fn codegen_function(
  function_node : &AstNode,
  body : &AstNode,
  name : &str,
  args : Vec<RefStr>,
  jit: &mut Jit)
    -> Result<FunctionValue, Error>
{
  /* TODO: is this needed?
  // check if declaration with this name was already done
  if module.get_function(name).is_some() {
    return error(node, format!("function '{}' already defined", name));
  };
  */

  // we have no global variables, so we can clear all the
  // previously defined named values as they come from other functions
  jit.named_values.clear();

  let f64_type = jit.context.f64_type();
  let args_types = std::iter::repeat(f64_type)
    .take(args.len())
    .map(|f| f.into())
    .collect::<Vec<BasicTypeEnum>>();
  let args_types = args_types.as_slice();

  let fn_type = match body.type_tag {
    Type::Bool => jit.context.bool_type().fn_type(args_types, false),
    Type::Float => jit.context.f64_type().fn_type(args_types, false),
    Type::Void => jit.context.void_type().fn_type(args_types, false),
  };
  let function = jit.module.add_function(name, fn_type, None);

  // this exists to catch errors and delete the function if needed
  fn generate(function_node : &AstNode, body : &AstNode, function : FunctionValue, args : Vec<RefStr>, jit : &mut Jit) -> Result<(), Error> {
    // set arguments names
    for (i, arg) in function.get_param_iter().enumerate() {
      arg.into_float_value().set_name(args[i].as_ref());
    }

    let entry = jit.context.append_basic_block(&function, "entry");

    jit.builder.position_at_end(&entry);

    // set function parameters
    for (param, arg) in function.get_param_iter().zip(&args) {
      jit.named_values.insert(arg.clone(), param);
    }

    // compile body
    let body_val = codegen_expression(body, jit)?;

    // clear local variables
    jit.named_values.clear();

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

  match generate(function_node, body, function, args, jit) {
    Ok(_) => Ok(function),
    Err(e) => {
      dump_module(jit.module);
      // This library uses copy semantics for a resource can be deleted, because it is usually not deleted.
      // As a result, it's possible to get use-after-free bugs, so this operation is unsafe. I'm sure this
      // design could be improved.
      unsafe {
        function.delete();
      }
      Err(e)
    }
  }
}

pub struct Interpreter {
  sym : SymbolTable,
  context : ContextRef,
  builder : Builder,
  module : Module,
  functions : HashMap<RefStr, Type>,
  pass_manager : PassManager,
}

impl Interpreter {
  pub fn new() -> Interpreter {
    let sym = SymbolTable::new();
    let context = Context::get_global();
    let builder = Builder::create();
    let module = Module::create("top_level");
    let functions = HashMap::new();
    let pm = PassManager::create_for_function(&module);
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.add_gvn_pass();
    pm.add_cfg_simplification_pass();
    pm.add_basic_alias_analysis_pass();
    pm.add_promote_memory_to_register_pass();
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.initialize();

    Interpreter { sym, context, builder, module, functions, pass_manager: pm }
  }

  pub fn run(&mut self, code : &str) -> Result<Val, Error> {
    let tokens =
        lexer::lex(code, &mut self.sym)
        .map_err(|mut es| es.remove(0))?;
    let expr = parser::parse(tokens, &mut self.sym)?;
    self.run_expression(&expr)
  }

  pub fn run_expression(&mut self, expr : &Expr) -> Result<Val, Error> {
    let mut jit = Jit::new(&mut self.context, &mut self.builder, &mut self.module, &mut self.pass_manager, &mut self.sym);
    run_expression(expr, &mut jit, &mut self.functions)
  }
}

//pub val : Rc<RefCell<Any>>,

fn run_expression(expr : &Expr, jit: &mut Jit, functions : &mut HashMap<RefStr, Type>) -> Result<Val, Error> {
  let mut type_checker = TypeChecker { variables: HashMap::new(), functions: functions, sym: jit.sym };
  let ast = type_checker.to_ast(expr)?;
  let f = codegen_function(&ast, &ast, "top_level", vec!(), jit)?;
  println!("{}", display_expr(expr));
  dump_module(&jit.module);

  fn execute<T>(expr : &Expr, f : FunctionValue, ee : &ExecutionEngine) -> Result<T, Error> {
    let function_name = f.get_name().to_str().unwrap();
    let v = unsafe {
      let jit_function = ee.get_function::<unsafe extern "C" fn() -> T>(function_name).map_err(|e| error_raw(expr, format!("{:?}", e)))?;
      jit_function.call()
    };
    Ok(v)
  }
  let ee = jit.module.create_jit_execution_engine(OptimizationLevel::None).map_err(|e| error_raw(expr, e.to_string()))?;
  let result = match ast.type_tag {
    Type::Bool => execute::<bool>(expr, f, &ee).map(Val::Bool),
    Type::Float => execute::<f64>(expr, f, &ee).map(Val::Float),
    Type::Void => execute::<()>(expr, f, &ee).map(|_| Val::Void),
  };
  ee.remove_module(jit.module).unwrap();
  result
}

pub fn run_repl() {

  let mut rl = Editor::<()>::new();
  let mut i = Interpreter::new();
  let mut jit = Jit::new(&mut i.context, &mut i.builder, &mut i.module, &mut i.pass_manager, &mut i.sym);

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut jit.sym)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut jit.sym);
      match parsing_result {
        Ok(Complete(e)) => {
          // we have parsed a full expression
          rl.add_history_entry(input_line);
          match run_expression(&e, &mut jit, &mut i.functions) {
            Ok(value) => {
              println!("{:?}", value)
            }
            Err(err) => {
              println!("error: {:?}", err);
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
