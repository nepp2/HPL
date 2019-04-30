
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

use crate::error::{Error, error};
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

pub struct Ctx {
  context: ContextRef,
  builder: Builder,
  named_values: HashMap<RefStr, BasicValueEnum>,
}

impl Ctx {
  pub fn new() -> Ctx {
    Ctx {
      context: Context::get_global(),
      builder: Builder::create(),
      named_values: HashMap::new(),
    }
  }
}

fn dump_module(module : &Module) {
  println!("{}", module.print_to_string().to_string())
}

fn codegen_float(e : &Expr, ctx: &mut Ctx, module: &mut Module, sym : &mut SymbolTable) -> Result<FloatValue, Error> {
  let v = codegen_expression(e, ctx, module, sym)?;
  match v {
    Some(BasicValueEnum::FloatValue(f)) => Ok(f),
    t => error(e, format!("Expected float, found {:?}", t)),
  }
}

fn codegen_expression(expr : &Expr, ctx: &mut Ctx, module: &mut Module, sym : &mut SymbolTable) -> Result<Option<BasicValueEnum>, Error> {
  let v : BasicValueEnum = match &expr.tag {
    ExprTag::Tree(_) => {
      let instr = sym.str(expr.tree_symbol_unwrap()?);
      let children = expr.children.as_slice();
      match (instr, children) {
        ("call", [op, a, b]) => {
          let lhs_value = codegen_float(a, ctx, module, sym)?;
          let rhs_value = codegen_float(b, ctx, module, sym)?;
          let op_str = sym.str(op.symbol_unwrap()?);
          match op_str {
            "+" => ctx.builder.build_float_add(lhs_value, rhs_value, "add_result").into(),
            "-" => ctx.builder.build_float_sub(lhs_value, rhs_value, "sub_result").into(),
            "*" => ctx.builder.build_float_mul(lhs_value, rhs_value, "mul_result").into(),
            "/" => ctx.builder.build_float_div(lhs_value, rhs_value, "div_result").into(),
            _ => return error(expr, "unsupported operation"),
          }
        }
        ("block", exprs) => {
          let expr_count = exprs.len();
          if expr_count > 0 {
            for i in 0..(expr_count-1) {
              codegen_expression(&exprs[i], ctx, module, sym)?;
            }
            return codegen_expression(&exprs[expr_count-1], ctx, module, sym);
          }
          return Ok(None);
        }
        ("fun", exprs) => {
          let name = sym.refstr(exprs[0].symbol_unwrap()?);
          let args_exprs = exprs[1].children.as_slice();
          let function_body = &exprs[2];

          let mut args = vec!();
          for (arg, _) in args_exprs.iter().tuples() {
            args.push(sym.refstr(arg.symbol_unwrap()?));
          }
          codegen_function(expr, function_body, name.as_ref(), args, ctx, module, sym)?;
          return Ok(None);
        }
        _ => return error(expr, "unsupported expression"),
      }
    }
    ExprTag::LiteralFloat(f) => {
      ctx.context.f64_type().const_float(*f as f64).into()
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
  ctx: &mut Ctx,
  module: &mut Module,
  sym : &mut SymbolTable)
    -> Result<FunctionValue, Error>
{
  // check if declaration with this name was already done
  if module.get_function(name).is_some() {
    return error(expr, format!("function '{}' already defined", name));
  };

  // we have no global variables, so we can clear all the
  // previously defined named values as they come from other functions
  ctx.named_values.clear();

  let ret_type = ctx.context.f64_type();
  let args_types = std::iter::repeat(ret_type)
    .take(args.len())
    .map(|f| f.into())
    .collect::<Vec<BasicTypeEnum>>();
  let args_types = args_types.as_slice();

  let fn_type = ctx.context.f64_type().fn_type(args_types, false);
  let function = module.add_function(name, fn_type, None);

  // set arguments names
  for (i, arg) in function.get_param_iter().enumerate() {
    arg.into_float_value().set_name(args[i].as_ref());
  }

  let entry = ctx.context.append_basic_block(&function, "entry");

  ctx.builder.position_at_end(&entry);

  // set function parameters
  for (param, arg) in function.get_param_iter().zip(&args) {
    ctx.named_values.insert(arg.clone(), param);
  }

  // compile body
  let body_val = codegen_expression(body, ctx, module, sym)?;

  // clear local variables
  ctx.named_values.clear();

  // emit return (via stupid API)
  match body_val {
    Some(b) => { ctx.builder.build_return(Some(&b)); }
    None => { ctx.builder.build_return(None); }
  }

  // return the whole thing after verification and optimization
  if function.verify(true) {
    // TODO: make this line work later
    // ctx.pass_manager.run_on_function(&function);
    Ok(function)
  }
  else {
    // This library uses copy semantics for a resource can be deleted, because it is usually not deleted.
    // As a result, it's possible to get use-after-free bugs, so this operation is unsafe. I'm sure this
    // design could be improved.
    unsafe {
        function.delete();
    }
    error(expr, "invalid generated function.")
  }
}

fn run_expression(expr : &Expr, ctx: &mut Ctx, module: &mut Module, sym : &mut SymbolTable) {
  codegen_function(expr, expr, "top_level", vec!(), ctx, module, sym).unwrap();
  println!("{}", display_expr(expr, sym));
  dump_module(module);
}

pub fn run_repl() {
  let mut sym = SymbolTable::new();

  let mut rl = Editor::<()>::new();

  let mut ctx = Ctx::new();
  let mut module = Module::create("top_level");

  loop {
    let mut input_line = rl.readline("repl> ").unwrap();

    loop {
      let lex_result =
        lexer::lex(input_line.as_str(), &mut sym)
        .map_err(|mut es| es.remove(0));
      let tokens = match lex_result {
        Ok(tokens) => tokens,
        Err(e) => {
          println!("Error occured: {}", e);
          break;
        }
      };
      let parsing_result = parser::repl_parse(tokens, &mut sym);
      match parsing_result {
        Ok(Complete(e)) => {
          // we have parsed a full expression
          rl.add_history_entry(input_line);
          run_expression(&e, &mut ctx, &mut module, &mut sym);
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
