
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

use rustyline::error::ReadlineError;
use rustyline::Editor;

use crate::error::{Error, error, error_raw};
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
use inkwell::values::{BasicValueEnum, AnyValueEnum, FloatValue, FunctionValue, PointerValue, GenericValue, BasicValue};
use inkwell::{OptimizationLevel, FloatPredicate};
use inkwell::execution_engine::ExecutionEngine;

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

fn f(e : &Expr, jit: &mut Jit) -> Result<FloatValue, Error> {
  let v = codegen_expression(e, jit)?;
  match v {
    Some(BasicValueEnum::FloatValue(f)) => Ok(f),
    t => error(e, format!("Expected float, found {:?}", t)),
  }
}

fn codegen_op(exprs : &[&Expr], jit: &mut Jit) -> Result<Option<BasicValueEnum>, Error> {
  match exprs {
    [op, a, b] => {
      let fv = match op {
        "+" => jit.builder.build_float_add(f(a, jit)?, f(b, jit)?, "add_result"),
        "-" => jit.builder.build_float_sub(f(a, jit)?, f(b, jit)?, "sub_result"),
        "*" => jit.builder.build_float_mul(f(a, jit)?, f(b, jit)?, "mul_result"),
        "/" => jit.builder.build_float_div(f(a, jit)?, f(b, jit)?, "div_result"),
        _ => return Ok(None);
      };
      Ok(fv.into())
    }
  }
}

fn codegen_expression(expr : &Expr, jit: &mut Jit) -> Result<Option<BasicValueEnum>, Error> {
  let v : BasicValueEnum = match &expr.tag {
    ExprTag::Tree(_) => {
      let instr = jit.sym.str(expr.tree_symbol_unwrap()?);
      let children = expr.children.as_slice();
      match (instr, children) {
        ("call", [op, a, b]) => {
          let lhs_value = f(a, jit)?;
          let rhs_value = f(b, jit)?;
          match name {
            [op, a, b] => {
              "+" => jit.builder.build_float_add(lhs_value, rhs_value, "add_result").into(),
              "-" => jit.builder.build_float_sub(lhs_value, rhs_value, "sub_result").into(),
              "*" => jit.builder.build_float_mul(lhs_value, rhs_value, "mul_result").into(),
              "/" => jit.builder.build_float_div(lhs_value, rhs_value, "div_result").into(),
            }
          }
          let lhs_value = codegen_float(a, jit)?;
          let rhs_value = codegen_float(b, jit)?;
          let op_str = jit.sym.str(op.symbol_unwrap()?);
          match op_str {
            "+" => jit.builder.build_float_add(lhs_value, rhs_value, "add_result").into(),
            "-" => jit.builder.build_float_sub(lhs_value, rhs_value, "sub_result").into(),
            "*" => jit.builder.build_float_mul(lhs_value, rhs_value, "mul_result").into(),
            "/" => jit.builder.build_float_div(lhs_value, rhs_value, "div_result").into(),
            _ => {

              let function = match jit.module.get_function(name) {
                  Some(function) => function,
                  None => return error("unknown function referenced")
              };

              if function.count_params() as usize != args.len() {
                  return error("incorrect number of arguments passed")
              }

              let mut args_value = Vec::new();
              for arg in args.iter() {
                  let (arg_value, _) = try!(arg.codegen(context, module_provider));
                  args_value.push(arg_value);
              }

              Ok((context.builder.build_call(function.to_ref(),
                                              args_value.as_mut_slice(),
                                              "calltmp"),
                  false))
              return error(expr, "unsupported operation")
            },
          }
        }
        ("block", exprs) => {
          let expr_count = exprs.len();
          if expr_count > 0 {
            for i in 0..(expr_count-1) {
              codegen_expression(&exprs[i], jit)?;
            }
            return codegen_expression(&exprs[expr_count-1], jit);
          }
          return Ok(None);
        }
        ("fun", exprs) => {
          let name = jit.sym.refstr(exprs[0].symbol_unwrap()?);
          let args_exprs = exprs[1].children.as_slice();
          let function_body = &exprs[2];
          let mut args = vec!();
          for (arg, _) in args_exprs.iter().tuples() {
            args.push(jit.sym.refstr(arg.symbol_unwrap()?));
          }
          let current_block = jit.builder.get_insert_block().unwrap();
          codegen_function(expr, function_body, name.as_ref(), args, jit)?;
          jit.builder.position_at_end(&current_block);
          return Ok(None);
        }
        _ => return error(expr, "unsupported expression"),
      }
    }
    ExprTag::Symbol(s) => {
      if let Some(value) = jit.named_values.get(jit.sym.str(*s)) {
        *value
      }
      else {
        return error(expr, "unknown variable name")
      }
    }
    ExprTag::LiteralFloat(f) => {
      jit.context.f64_type().const_float(*f as f64).into()
    }
    _ => return error(expr, "unsupported expression"),
  };
  Ok(Some(v))
}

fn codegen_function(
  expr : &Expr,
  body : &Expr,
  name : &str,
  args : Vec<RefStr>,
  jit: &mut Jit)
    -> Result<FunctionValue, Error>
{
  /* TODO: is this needed?
  // check if declaration with this name was already done
  if module.get_function(name).is_some() {
    return error(expr, format!("function '{}' already defined", name));
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

  let fn_type = jit.context.f64_type().fn_type(args_types, false);
  let function = jit.module.add_function(name, fn_type, None);

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
      let f = jit.context.f64_type().const_float(-1.0);
      jit.builder.build_return(Some(&f));
    }
  }

  // return the whole thing after verification and optimization
  if function.verify(true) {
    jit.pm.run_on_function(&function);
    Ok(function)
  }
  else {
    // This library uses copy semantics for a resource can be deleted, because it is usually not deleted.
    // As a result, it's possible to get use-after-free bugs, so this operation is unsafe. I'm sure this
    // design could be improved.
    dump_module(&jit.module);
    unsafe {
      function.delete();
    }
    error(expr, "invalid generated function.")
  }
}

fn run_expression(expr : &Expr, jit: &mut Jit) -> Result<(), Error> {
  let f = codegen_function(expr, expr, "top_level", vec!(), jit)?;
  println!("{}", display_expr(expr, jit.sym));
  dump_module(&jit.module);

  fn execute(expr : &Expr, f : FunctionValue, ee : &ExecutionEngine) -> Result<f64, Error> {
    let function_name = f.get_name().to_str().unwrap();
    unsafe {
      let jit_function = ee.get_function::<unsafe extern "C" fn() -> f64>(function_name).map_err(|e| error_raw(expr, format!("{:?}", e)))?;
      Ok(jit_function.call())
    }
  }
  let ee = jit.module.create_jit_execution_engine(OptimizationLevel::None).map_err(|e| error_raw(expr, e.to_string()))?;
  let result = execute(expr, f, &ee);
  ee.remove_module(jit.module).unwrap();
  println!("result: {}", result?);
  Ok(())
}

pub fn run_repl() {
  let mut sym = SymbolTable::new();

  let mut rl = Editor::<()>::new();

  let mut context = Context::get_global();
  let mut builder = Builder::create();

  let mut expressions = vec![];

  let mut module = Module::create("top_level");

  let mut pm = PassManager::create_for_function(&module);
  pm.add_instruction_combining_pass();
  pm.add_reassociate_pass();
  pm.add_gvn_pass();
  pm.add_cfg_simplification_pass();
  pm.add_basic_alias_analysis_pass();
  pm.add_promote_memory_to_register_pass();
  pm.add_instruction_combining_pass();
  pm.add_reassociate_pass();
  pm.initialize();

  let mut jit = Jit::new(&mut context, &mut builder, &mut module, &mut pm, &mut sym);

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
          match run_expression(&e, &mut jit) {
            Ok(_) => {
              // record the expression
              expressions.push(e);
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
