
use crate::lexer;
use crate::parser;
use crate::parser::NO_TYPE;
use crate::value::*;
use crate::error::{Error, ErrorContent, error, error_raw};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use std::cell::RefCell;
use std::fmt;
use itertools::Itertools;
use std::mem;
use std::sync::atomic::{AtomicBool, Ordering};

#[derive(PartialEq)]
pub enum ExitState {
  NotExiting,
  Breaking,
  Returning(Value),
}

pub enum FunctionHandle {
  Ast(Rc<Expr>),
  BuiltIn(fn(&mut Environment, Vec<Value>) -> Result<Value, ErrorContent>),
}

impl fmt::Debug for FunctionHandle {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      FunctionHandle::Ast(_) => write!(f, "FunctionHandle::Ast"),
      FunctionHandle::BuiltIn(_) => write!(f, "FunctionHandle::BuiltIn"),
    }
  }
}

#[derive(Debug)]
pub struct Function {
  pub module_id : ModuleId,
  pub visible_modules : Vec<ModuleId>,
  pub arg_types : Vec<Type>,
  pub arg_names : Vec<Symbol>,
  pub handle : FunctionHandle,
}

#[derive(Default)]
pub struct BlockScope {
  pub variables : HashMap<Symbol, Value>,
  pub modules : Vec<ModuleId>,
}

pub fn get_module_id(loaded_modules : &mut Vec<Module>, name : Symbol) -> Option<ModuleId> {
  loaded_modules.iter().enumerate()
    .find(|(_, m)| m.name == name)
    .map(|(i, _)| ModuleId{i})
}

pub fn add_module(loaded_modules : &mut Vec<Module>, m : Module) -> ModuleId {
  let id = ModuleId { i: loaded_modules.len() };
  loaded_modules.push(m);
  id
}

#[derive(Debug)]
pub struct Module {
  pub name : Symbol,
  // TODO: is this needed?
  // pub modules : Vec<ModuleId>,
  pub functions : HashMap<Symbol, Function>,
  pub structs : HashMap<Symbol, Rc<StructDef>>,
}

impl Module {
  pub fn new(name : Symbol) -> Module {
    Module {
      name,
      functions: Default::default(),
      structs: Default::default(),
    }
  }
}

pub struct Environment<'l> {

  pub sym : &'l mut SymbolTable,
  pub loaded_modules : &'l mut Vec<Module>,
  pub current_module : ModuleId,
  pub interrupt_flag : &'l mut Arc<AtomicBool>,

  pub scope : Vec<BlockScope>,

  /// indicates how many nested loops we are inside in the currently-executing function
  pub loop_depth : i32,

  /// indicates whether the program is currently breaking out of a loop
  /// or returning from the function
  pub exit_state : ExitState,

}

pub fn iter_modules<'m>(scope : &'m Vec<BlockScope>) -> impl Iterator<Item = &'m ModuleId> {
  scope.iter().rev()
  .flat_map(|b| b.modules.iter())
}

impl <'l> Environment<'l> {

  pub fn new(
    sym : &'l mut SymbolTable,
    loaded_modules : &'l mut Vec<Module>,
    current_module : ModuleId,
    interrupt_flag : &'l mut Arc<AtomicBool>,
    initial_scope : BlockScope,
  ) -> Environment<'l> {
    Environment{
      sym, loaded_modules,
      current_module, interrupt_flag,
      scope: vec![initial_scope],
      loop_depth: 0,
      exit_state: ExitState::NotExiting,
    }
  }

  fn str(&self, s : Symbol) -> &str {
    self.sym.str(s)
  }

  fn check_interrupt(&self) -> Result<(), String> {
    if self.interrupt_flag.load(Ordering::Relaxed) {
      Err(format!("Interpreter received interrupt"))
    }
    else {
      Ok(())
    }
  }

  fn current_block_scope(&mut self) -> &mut BlockScope {
    self.scope.last_mut().unwrap()
  }

  fn new_variable(&mut self, s : Symbol, v : Value) {
    self.current_block_scope().variables.insert(s, v);
  }

  pub fn import_module(&mut self, module_id : ModuleId) -> Result<(), String> {
    if let Some(id) = iter_modules(&self.scope).find(|id| *id == &module_id) {
      let m = &self.loaded_modules[id.i];
      return Err(format!("Module '{}' already imported", self.sym.str(m.name)));
    }
    self.current_block_scope().modules.push(module_id);
    Ok(())
  }

  /// Retrieve the value closest to the end of the vector of hashmaps (the most local scope)
  /// in the environment
  fn dereference_variable(&mut self, s : Symbol) -> Option<&mut Value> {
    for block in self.scope.iter_mut().rev() {
      let v = block.variables.get_mut(&s);
      if v.is_some() {
        return v;
      }
    }
    return None;
  }

  pub fn visible_modules(&self) -> Vec<ModuleId> {
    iter_modules(&self.scope).cloned().collect()
  }

  pub fn current_module_mut(&mut self) -> &mut Module {
    &mut self.loaded_modules[self.current_module.i]
  }

  pub fn current_module(&self) -> &Module {
    &self.loaded_modules[self.current_module.i]
  }

  pub fn struct_lookup(&self, name : Symbol) -> Option<&Rc<StructDef>> {
    for id in iter_modules(&self.scope) {
      let m = &self.loaded_modules[id.i];
      if let Some(s) = m.structs.get(&name) {
        return Some(s);
      }
    }
    None
  }

  fn struct_field_index(&self, def : &StructDef, field_expr : &Expr) -> Result<usize, Error> {
    let field_name = field_expr.symbol_unwrap()?;
    def.fields.iter().position(|s| *s == field_name)
      .ok_or_else(||error_raw(field_expr,
        format!("field {} does not exist on struct {:?}.", self.str(field_name), def)))
  }

  pub fn add_struct(&mut self, def: StructDef) -> Result<(), String> {
    if self.struct_lookup(def.name).is_some() {
      return Err(format!("A struct called {} has already been defined.", self.sym.str(def.name)));
    }
    self.current_module_mut().structs.insert(def.name.clone(), Rc::new(def));
    Ok(())
  }

  pub fn instantiate_struct(&mut self, name: Symbol, field_value_pairs: Vec<(Symbol, Value)>)
    -> Result<StructVal, ErrorContent>
  {
    let def = {
      if let Some(def) = self.struct_lookup(name) {
        def.clone()
      }
      else {
        let fields = field_value_pairs.iter().map(|t| t.0).collect();
        let m = self.current_module_mut();
        let def = Rc::new(StructDef { module: m.name, name: name.into(), fields });
        m.structs.insert(def.name.clone(), def.clone());
        def
      }
    };
    let mut field_values = vec![];
    let mut i = 0;
    let num_fields = def.fields.len();
    for (found, value) in field_value_pairs {
      if i >= num_fields {
        return Err(format!("found unexpected field: {}", self.str(found)).into());
      }
      let expected = def.fields[i];
      if expected != found {
        return Err(format!("expected field name '{}', but found '{}'", self.str(expected), self.str(found)).into());
      }
      field_values.push(value);
      i += 1;
    }
    if i < num_fields {
      return Err(format!("some fields were not initialised: {:?}", &def.fields[i..num_fields]).into());
    }
    Ok(Rc::new(RefCell::new(Struct { def, fields : field_values })))
  }

  pub fn add_function(&mut self, name : Symbol, function : Function) -> Result<(), String> {
    // Check if anything with this precise signature is already defined
    for id in iter_modules(&self.scope) {
      let module = &mut self.loaded_modules[id.i];
      if module.functions.contains_key(&name) {
        return Err(format!("function {} defined more than once.", self.str(name)))
      }
    }
    self.current_module_mut().functions.insert(name, function);
    Ok(())
  }

  fn get_function<'m, A>(&'m self, name : Symbol, module_ids : A)
    -> Result<&Function, String>
    where A : Iterator<Item = &'m ModuleId>
  {
    for id in module_ids {
      let module = &self.loaded_modules[id.i];
      if let Some(f) = module.functions.get(&name) {
        return Ok(f)
      }
    }
    Err(format!("No function called '{}' defined", self.str(name)))
  }

  fn symbol_to_type(&self, symbol : Symbol) -> Result<Type, String> {
    let s = self.str(symbol);
    if s == NO_TYPE {
      return Ok(Type::Any);
    }
    match s.as_ref() {
      "float" => Ok(Type::Float),
      "string" => Ok(Type::String),
      "unit" => Ok(Type::Unit),
      "bool" => Ok(Type::Bool),
      "array" => Ok(Type::Array),
      "any" => Ok(Type::Any),
      _ => {
        if self.struct_lookup(symbol).is_some() {
          Ok(Type::Struct{
            module: self.current_module().name,
            name: symbol,
          })
        }
        else {
          Err(format!("{:?} is not a valid type", s))
        }
      }
    }
  }
}

fn call_function(
  error_source : &Expr, function_name: Symbol,
  visible_modules: Option<&Vec<ModuleId>>, arg_values: Vec<Value>,
  env : &mut Environment)
  -> Result<Value, Error>
{
  let r = if let Some(ids) = visible_modules {
    env.get_function(function_name, ids.iter())
  }
  else {
    env.get_function(function_name, iter_modules(&env.scope))
  };
  let f = r.map_err(|s| error_raw(error_source, s))?;
  if f.arg_names.len() != arg_values.len() {
    return error(error_source,
      format!("function '{}' expected {} arguments, but received {}",
        env.str(function_name), f.arg_names.len(), arg_values.len()))
  }
  match &f.handle {
    FunctionHandle::Ast(expr) => {
      let mut args = HashMap::new();
      for (v, n) in arg_values.into_iter().zip(&f.arg_names) {
        args.insert(n.clone(), v);
      }
      let block = BlockScope {
        variables: args,
        modules: f.visible_modules.clone()
      };
      let expr = expr.clone();
      let mut new_env = Environment::new(
        env.sym, env.loaded_modules, f.module_id, env.interrupt_flag, block);
      let r = eval(&expr, &mut new_env)?;
      let es = mem::replace(&mut new_env.exit_state, ExitState::NotExiting);
      if let ExitState::Returning(v) = es {
        Ok(v)
      }
      else {
        Ok(r)
      }
    }
    FunctionHandle::BuiltIn(f) => {
      f(env, arg_values).map_err(|e| error_raw(error_source, e))
    }
  }
}

fn eval_function_call(expr : &Expr, function_expr: &Expr, args: &[Expr], env : &mut Environment)
  -> Result<Value, Error>
{ 
  fn eval_named_function_call(
    expr : &Expr, function_name: Symbol, visible_modules: Option<&Vec<ModuleId>>,
    args: &[Expr], env : &mut Environment)
    -> Result<Value, Error>
  {
    let mut arg_values = vec!();
    for i in 0..args.len() {
      let e = &args[i];
      let v = eval(e, env)?;
      arg_values.push(v);
    }
    call_function(expr, function_name, visible_modules, arg_values, env)
  }
  // Decide whether this is a first class function or a static function reference
  let symbol = function_expr.symbol_unwrap().ok();
  let var = symbol.and_then(|s| env.dereference_variable(s));
  if let Some(v) = var {
    // Symbol refers to a local variable (containing function reference)
    let r : Result<FunctionRef, String> = v.clone().into();
    let f = r.map_err(|s| error_raw(function_expr, s))?;
    eval_named_function_call(expr, f.name, Some(&f.visible_modules), args, env)
  }
  else if let Some(name) = symbol {
    // Assume it's a symbol referring to a function
    eval_named_function_call(expr, name, None, args, env)
  }
  else {
    // More complex expression, which must be evaluated to a function reference
    let f = to_value::<FunctionRef>(function_expr, env)?;
    eval_named_function_call(expr, f.name, Some(&f.visible_modules), args, env)
  }
}

fn to_value<V>(e : &Expr, env : &mut Environment) -> Result<V, Error>
  where Value: Into<Result<V, String>>
{
  let v = eval(e, env)?;
  let r : Result<V, String> = v.into();
  r.map_err(|s| error_raw(e, s))
}

fn array_index(e : &Expr, array : &Vec<Value>, index : f32) -> Result<usize, Error> {
  let i = index as usize;
  if index >= 0.0 && i < array.len() {
    Ok(i)
  }
  else {
    error(e, format!("Index out of bounds error. Array of {} elements given index {}.", array.len(), index))
  }
}

fn eval_tree(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  // Check if the interrupt flag is set
  // TODO: this is a very slow thing to do for every instruction
  env.check_interrupt().map_err(|s| error_raw(expr, s))?;

  let instr = env.str(expr.tree_symbol_unwrap()?);
  let children = expr.children.as_slice();
  match (instr, children) {
    ("call", exprs) => {
      let function_name_expr = &exprs[0];
      let params = &exprs[1..];
      eval_function_call(expr, function_name_expr, params, env)
    }
    ("block", exprs) => {
      fn evaluate_block(exprs : &[Expr], env : &mut Environment)
        -> Result<Value, Error>
      {
        let expr_count = exprs.len();
        if expr_count > 0 {
          for i in 0..(expr_count-1) {
            let v = eval(&exprs[i], env)?;
            if env.exit_state != ExitState::NotExiting {
              return Ok(v);
            }
          }
          return eval(&exprs[expr_count-1], env)
        }
        Ok(Value::Unit)
      }

      env.scope.push(Default::default());
      let val = evaluate_block(exprs, env);
      env.scope.pop();
      val
    }
    ("let", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let v = eval(&exprs[1], env)?;
      env.new_variable(name.clone(), v);
      Ok(Value::Unit)
    }
    ("&&", [a, b]) => {
      let v = to_value(a, env)? && to_value(b, env)?;
      Ok(Value::from(v))
    }
    ("||", [a, b]) => {
      let v = to_value(a, env)? || to_value(b, env)?;
      Ok(Value::from(v))
    }
    ("=", [assign_expr, value_expr]) => {
      match &assign_expr.tag {
        ExprTag::Symbol(var_symbol) => {
          let value = eval(&value_expr, env)?;
          match env.dereference_variable(*var_symbol) {
            Some(var) => {
              *var = value;
            }
            None => {
              let var_name = env.str(*var_symbol);
              return error(assign_expr,
                format!("symbol '{}' was not defined", var_name));
            }
          }
          return Ok(Value::Unit)
        }
        ExprTag::Tree(symbol) => {
          match (env.str(*symbol), assign_expr.children.as_slice()) {
            ("index", [array_expr, index_expr]) => {
              let v = eval(&value_expr, env)?;
              let array_rc : Array = to_value(array_expr, env)?;
              let mut array = array_rc.borrow_mut();
              let f = to_value(index_expr, env)?;
              let i = array_index(expr, &array, f)?;
              array[i] = v;
              return Ok(Value::Unit)
            }
            (".", [struct_expr, field_expr]) => {
              let v = eval(&value_expr, env)?;
              let structure : StructVal = to_value(struct_expr, env)?;
              let index = env.struct_field_index(&structure.borrow().def, field_expr)?;
              structure.borrow_mut().fields[index] = v;
              return Ok(Value::Unit)
            }
            _ => return error(assign_expr, format!("can't assign to {:?}", assign_expr)),
          }
        }
        _ => (),
      }
      error(assign_expr, format!("can't assign to {:?}", assign_expr))
    }
    ("return", exprs) => {
      if exprs.len() > 1 {
        return error(expr, format!("malformed return expression"));
      }
      let return_val =
        if exprs.len() == 1 {
          eval(&exprs[0], env)?
        }
        else {
          Value::Unit
        };
      env.exit_state = ExitState::Returning(return_val);
      Ok(Value::Unit)
    }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return error(expr, format!("malformed if expression"));
      }
      let condition = to_value(&exprs[0], env)?;
      if condition {
        eval(&exprs[1], env)
      }
      else if arg_count == 3 {
        eval(&exprs[2], env)
      }
      else {
        Ok(Value::Unit)
      }
    }
    ("struct_define", exprs) => {
      if exprs.len() < 1 {
        return error(expr, "malformed struct definition");
      }
      let name_expr = &exprs[0];
      let name = name_expr.symbol_unwrap()?;
      // TODO: check for duplicates?
      let field_exprs = &exprs[1..];
      let mut fields = vec![];
      // TODO: record the field types, and check them!
      for (e, _) in field_exprs.iter().tuples() {
        fields.push(e.symbol_unwrap()?);
      }
      let module = env.current_module().name.clone();
      let def = StructDef { module, name, fields };
      env.add_struct(def).map_err(|s| error_raw(name_expr, s))?;
      Ok(Value::Unit)
    }
    ("struct_instantiate", exprs) => {
      if exprs.len() < 1 || exprs.len() % 2 == 0 {
        return error(expr, format!("malformed struct instantiation {:?}", expr));
      }
      let name_expr = &exprs[0];
      let field_exprs = &exprs[1..];
      let name = name_expr.symbol_unwrap()?;
      let field_value_pairs =
        field_exprs.iter().tuples().map(|(field, value)| {
          let field_name = field.symbol_unwrap()?;
          let field_value = eval(value, env)?;
          Ok((field_name, field_value))
        })
        .collect::<Result<Vec<(Symbol, Value)>, Error>>()?;
      let s = env.instantiate_struct(name, field_value_pairs).map_err(|s| error_raw(expr, s))?;
      Ok(Value::Struct(s))
    }
    (".", [expr, name_expr]) => {
      let s : StructVal = to_value(expr, env)?;
      let index = env.struct_field_index(&s.borrow().def, name_expr)?;
      let v = s.borrow().fields[index].clone();
      Ok(v)
    }
    ("while", exprs) => {
      if exprs.len() != 2 {
        return error(expr, format!("malformed while block"));
      }
      env.loop_depth += 1;
      while env.exit_state == ExitState::NotExiting && to_value(&exprs[0], env)? {
        eval(&exprs[1], env)?;
      }
      env.loop_depth -= 1;
      if env.exit_state == ExitState::Breaking {
        env.exit_state = ExitState::NotExiting;
      }
      Ok(Value::Unit)
    }
    ("for", exprs) => {
      if exprs.len() != 3 {
        return error(expr, format!("malformed for block"));
      }
      fn from_value<V>(v : Value) -> Result<V, String>
        where Value : Into<Result<V, String>>
      {
        v.into()
      }
      fn to_range(env : &mut Environment, v : Value) -> Result<(i64, i64), ErrorContent> {
        let r : StructVal = from_value(v)?;
        let range = r.borrow();
        if env.str(range.def.name) != "range" {
          return Err(format!("expected range struct in for loop").into());
        }
        let start : f32 = from_value(range.fields[0].clone())?;
        let end : f32 = from_value(range.fields[1].clone())?;
        Ok((start as i64, end as i64))
      }
      let var = exprs[0].symbol_unwrap()?;
      let range_struct = eval(&exprs[1], env)?;
      let (start, end) =
        to_range(env, range_struct)
        .map_err(|e| error_raw(&exprs[1], e))?;
      let body = &exprs[2];
      env.scope.push(Default::default());
      env.new_variable(var.clone(), Value::Unit);
      env.loop_depth += 1;
      for i in start..end {
        let v : Value = (i as f32).into();
        let var_ref = env.dereference_variable(var).unwrap();
        *var_ref = v;
        eval(body, env)?;
        if env.exit_state != ExitState::NotExiting {
          break;
        }
      }
      env.loop_depth -= 1;
      env.scope.pop();
      if env.exit_state == ExitState::Breaking {
        env.exit_state = ExitState::NotExiting;
      }
      Ok(Value::Unit)
    }
    ("fun", exprs) => {
      let name = exprs[0].symbol_unwrap()?;
      let args_exprs = exprs[1].children.as_slice();
      let function_body = &exprs[2];
      let mut arg_names = vec!();
      let mut arg_types = vec!();
      for (arg, type_expr) in args_exprs.iter().tuples() {
        arg_names.push(arg.symbol_unwrap()?);
        let arg_type =
          env.symbol_to_type(type_expr.symbol_unwrap()?)
          .map_err(|s| error_raw(type_expr, s))?;
        arg_types.push(arg_type);
      }
      let f = Function {
        module_id: env.current_module,
        visible_modules: env.visible_modules(),
        arg_names, arg_types,
        handle: FunctionHandle::Ast(Rc::new(function_body.clone())),
      };
      env.add_function(name, f).map_err(|s| error_raw(expr, s))?;
      Ok(Value::Unit)
    }
    ("literal_array", exprs) => {
      let array_contents = Rc::new(RefCell::new(vec!()));
      for e in exprs {
        let v = eval(e, env)?;
        array_contents.borrow_mut().push(v);
      }
      Ok(Value::Array(array_contents))
    }
    ("index", exprs) => {
      if let [array_expr, index_expr] = exprs {
        let array_rc = to_value::<Array>(array_expr, env)?;
        let array = array_rc.borrow();
        let f = to_value(index_expr, env)?;
        let i = array_index(expr, &array, f)?;
        Ok(array[i].clone())
      }
      else {
        error(expr, format!("index instruction expected 2 arguments. Found {}.", exprs.len()))
      }
    }
    _ => {
      let child_tags = children.iter().map(|e| e.tag.clone()).collect::<Vec<ExprTag>>();
      error(expr, format!("instruction '{}' with args '{:?}' is not supported by the interpreter.", instr, child_tags))
    }
  }
}

pub fn eval(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  if env.exit_state != ExitState::NotExiting {
    // this skips all evaluations until we backtrack to something
    // that stops the exit state, such as a loop or function call
    return Ok(Value::Unit);
  }
  match &expr.tag {
    ExprTag::Tree(_) => {
      eval_tree(expr, env)
    }
    ExprTag::Symbol(s) => {
      if env.str(*s) == "break" {
        if env.loop_depth > 0 {
          env.exit_state = ExitState::Breaking;
          Ok(Value::Unit)
        }
        else {
          error(expr, format!("can't break outside a loop"))
        }
      }
      else if let Some(v) = env.dereference_variable(*s) {
        Ok(v.clone())
      }
      else if
        iter_modules(&env.scope)
        .map(|id| &env.loaded_modules[id.i])
        .find(|m| m.functions.contains_key(&s))
        .is_some()
      {
        Ok(Value::Function(FunctionRef{ name: s.clone(), visible_modules: env.visible_modules() }))
      }
      else {
        return error(expr, format!("no variable or function in scope called '{}'", env.str(*s)));
      }
    }
    ExprTag::LiteralString(s) => Ok(Value::from(*s)),
    ExprTag::LiteralFloat(f) => Ok(Value::from(*f)),
    ExprTag::LiteralBool(b) => Ok(Value::from(*b)),
    ExprTag::LiteralUnit => Ok(Value::Unit),
  }
}

pub fn eval_string(code : &str, env : &mut Environment) -> Result<Value, Error> {
  let tokens =
    lexer::lex(code, env.sym)
    .map_err(|mut es| es.remove(0))?;
  let ast = parser::parse(tokens, env.sym)?;
  eval(&ast, env)
}

