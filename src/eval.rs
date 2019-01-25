
use crate::lexer;
use crate::parser;
use crate::parser::NO_TYPE;
use crate::value::*;
use crate::error::{Error, error, error_raw};
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
  BuiltIn(fn(&mut Environment, Vec<Value>) -> Result<Value, String>),
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
pub struct Method {
  pub visible_modules : Vec<ModuleId>,
  pub arg_types : Vec<Type>,
  pub arg_names : Vec<RefStr>,
  pub handle : FunctionHandle,
}

pub struct MultiMethod {
  pub variants : Vec<Method>,
}

#[derive(Default, Debug)]
pub struct BlockScope {
  pub variables : HashMap<RefStr, Value>,
  pub modules : Vec<ModuleId>,
}

pub struct Module {
  pub name : RefStr,
  // TODO: is this needed?
  // pub modules : Vec<ModuleId>,
  pub functions : HashMap<RefStr, MultiMethod>,
  pub structs : HashMap<RefStr, Rc<StructDef>>,
}

impl Module {
  pub fn new(name : RefStr) -> Module {
    Module {
      name,
      functions: Default::default(),
      structs: Default::default(),
    }
  }
}

pub struct Environment<'l> {

  pub symbol_cache : &'l mut SymbolCache,
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

pub fn iter_modules<'m>(scope : &'m Vec<BlockScope>)
  -> impl Iterator<Item = &'m ModuleId> {
  scope.iter().rev()
  .flat_map(|b| b.modules.iter())
}

impl <'l> Environment<'l> {

  pub fn new(
    symbol_cache : &'l mut SymbolCache,
    loaded_modules : &'l mut Vec<Module>,
    current_module : ModuleId,
    interrupt_flag : &'l mut Arc<AtomicBool>,
    initial_scope : BlockScope,
  ) -> Environment<'l> {
    Environment{
      symbol_cache, loaded_modules,
      current_module, interrupt_flag,
      scope: vec![initial_scope],
      loop_depth: 0,
      exit_state: ExitState::NotExiting,
    }
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

  fn new_variable(&mut self, s : RefStr, v : Value) {
    self.current_block_scope().variables.insert(s, v);
  }

  /// Retrieve the value closest to the end of the vector of hashmaps (the most local scope)
  /// in the environment
  fn dereference_variable(&mut self, s : &str) -> Option<&mut Value> {
    for block in self.scope.iter_mut().rev() {
      let map = &mut block.variables;
      if map.contains_key(s) {
        return Some(map.get_mut(s).unwrap());
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

  pub fn struct_lookup(&self, name : &str) -> Option<&Rc<StructDef>> {
    for id in iter_modules(&self.scope) {
      let m = &self.loaded_modules[id.i];
      if let Some(s) = m.structs.get(name) {
        return Some(s);
      }
    }
    None
  }

  pub fn add_struct(&mut self, def: StructDef) -> Result<(), String> {
    if self.struct_lookup(&def.name).is_some() {
      return Err(format!("A struct called {} has already been defined.", def.name));
    }
    self.current_module_mut().structs.insert(def.name.clone(), Rc::new(def));
    Ok(())
  }

  pub fn instantiate_struct(&self, name: &str, mut value_map: HashMap<RefStr, Value>)
    -> Result<StructVal, String>
  {
    let def =
      self.struct_lookup(name)
      .ok_or_else(|| format!("struct {} does not exist", name))?.clone();
    let fields =
      def.fields.iter().map(|s| {
        value_map.remove(s.as_ref())
          .ok_or_else(|| format!("expected field '{}', but it was not defined", s))
      })
      .collect::<Result<Vec<Value>, String>>()?;
    if value_map.len() > 0 {
      return Err(format!("unexpected field(s) defined: '{:?}'", value_map.keys()));
    }
    Ok(Rc::new(RefCell::new(Struct { def, fields })))
  }

  pub fn add_function(&mut self, name : &str, method : Method) -> Result<(), String> {
    // Check if anything with this precise signature is already defined
    for id in iter_modules(&self.scope) {
      let m = &mut self.loaded_modules[id.i];
      if let Some(mm) = m.functions.get_mut(name) {
        for m in mm.variants.iter() {
          if m.arg_types == method.arg_types {
            return Err(format!("function {} defined more than once with the same signature.", name))
          }
        }
        mm.variants.push(method);
        return Ok(());
      }
    }
    // Add the method to the current scope. Check if this scope already has a multi-method.
    if let Some(mm) = self.current_module_mut().functions.get_mut(name) {
      mm.variants.push(method);
    }
    else {
      let name = self.symbol_cache.symbol(name);
      let mm = MultiMethod { variants: vec![method] };
      self.current_module_mut().functions.insert(name, mm);
    }
    Ok(())
  }

  fn get_method<'m, A>(&'m self, name : &str, arg_types : &[Type], module_ids : A)
    -> Result<&Method, String>
    where A : Iterator<Item = &'m ModuleId>
  {
    for id in module_ids {
      let module = &self.loaded_modules[id.i];
      if let Some(mm) = module.functions.get(name) {
        'outer: for m in mm.variants.iter() {
          if m.arg_types.len() != arg_types.len(){
            continue 'outer;
          }
          for (a, b) in m.arg_types.iter().zip(arg_types) {
            if a != b && *a != Type::Any && *b != Type::Any {
              continue 'outer;
            }
          }
          return Ok(m)
        }
      }
    }
    Err(format!("Cannot dispatch function '{}' with signature {:?}.", name, arg_types))
  }

  fn string_to_type(&self, s : &RefStr) -> Result<Type, String> {
    if s.as_ref() == NO_TYPE {
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
        if self.struct_lookup(s).is_some() {
          Ok(Type::Struct{
            module: self.current_module().name.clone(),
            name: s.clone(),
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
  error_source : &Expr, function_name: &str,
  visible_modules: Option<&Vec<ModuleId>>, arg_values: Vec<Value>,
  arg_types: Vec<Type>, env : &mut Environment)
  -> Result<Value, Error>
{
  let r = if let Some(ids) = visible_modules {
    env.get_method(function_name, arg_types.as_slice(), ids.iter())
  }
  else {
    env.get_method(function_name, arg_types.as_slice(), iter_modules(&env.scope))
  };
  let m = r.map_err(|s| error_raw(error_source, s))?;
  match &m.handle {
    FunctionHandle::Ast(expr) => {
      let mut args = HashMap::new();
      for (v, n) in arg_values.into_iter().zip(&m.arg_names) {
        args.insert(n.clone(), v);
      }
      let block = BlockScope {
        variables: args,
        modules: m.visible_modules.clone()
      };
      let expr = expr.clone();
      let mut new_env = Environment::new(env.symbol_cache, env.loaded_modules, env.current_module, env.interrupt_flag, block);
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
      f(env, arg_values).map_err(|s| error_raw(error_source, s))
    }
  }
}

fn eval_function_call(expr : &Expr, function_expr: &Expr, args: &[Expr], env : &mut Environment)
  -> Result<Value, Error>
{ 
  fn eval_named_function_call(
    expr : &Expr, function_name: &str, visible_modules: Option<&Vec<ModuleId>>,
    args: &[Expr], env : &mut Environment)
    -> Result<Value, Error>
  {
    let mut arg_values = vec!();
    let mut arg_types = vec!();
    for i in 0..args.len() {
      let e = &args[i];
      let v = eval(e, env)?;
      arg_types.push(v.to_type());
      arg_values.push(v);
    }
    call_function(expr, function_name, visible_modules, arg_values, arg_types, env)
  }
  // Decide whether this is a first class function or a static function reference
  let symbol = function_expr.symbol_unwrap().ok();
  let var = symbol.and_then(|s| env.dereference_variable(s));
  if let Some(v) = var {
    // Symbol refers to a local variable (containing function reference)
    let r : Result<FunctionRef, String> = v.clone().into();
    let f = r.map_err(|s| error_raw(function_expr, s))?;
    eval_named_function_call(expr, &f.name, Some(&f.visible_modules), args, env)
  }
  else if let Some(name) = symbol {
    // Assume it's a symbol referring to a function
    eval_named_function_call(expr, name, None, args, env)
  }
  else {
    // More complex expression, which must be evaluated to a function reference
    let f = to_value::<FunctionRef>(function_expr, env)?;
    eval_named_function_call(expr, &f.name, Some(&f.visible_modules), args, env)
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

fn struct_field_index(def : &StructDef, field_expr : &Expr) -> Result<usize, Error> {
  let field_name : &str = field_expr.symbol_unwrap()?;
  def.fields.iter().position(|s| s.as_ref() == field_name)
  .ok_or_else(||error_raw(field_expr, format!("field {} does not exist on struct {:?}.", field_name, def)))
}

fn eval_tree(expr : &Expr, env : &mut Environment) -> Result<Value, Error> {
  // Check if the interrupt flag is set
  // TODO: this is a very slow thing to do for every instruction
  env.check_interrupt().map_err(|s| error_raw(expr, s))?;

  let instr = expr.tree_symbol_unwrap()?.as_ref();
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
      Ok(Value::Bool(v))
    }
    ("||", [a, b]) => {
      let v = to_value(a, env)? || to_value(b, env)?;
      Ok(Value::Bool(v))
    }
    ("=", [assign_expr, value_expr]) => {
      match &assign_expr.tag {
        ExprTag::Symbol(var_symbol) => {
          let value = eval(&value_expr, env)?;
          let var =
            env.dereference_variable(var_symbol)
            .ok_or_else(|| error_raw(assign_expr, format!("symbol '{}' was not defined", var_symbol)))?;
          *var = value;
          return Ok(Value::Unit)
        }
        ExprTag::Tree(symbol) => {
          match (symbol.as_ref(), assign_expr.children.as_slice()) {
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
              let index = struct_field_index(&structure.borrow().def, field_expr)?;
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
      let name = name_expr.symbol_to_refstr()?;
      // TODO: check for duplicates?
      let field_exprs = &exprs[1..];
      let mut fields = vec![];
      // TODO: record the field types, and check them!
      for (e, _) in field_exprs.iter().tuples() {
        fields.push(e.symbol_to_refstr()?);
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
      let name = name_expr.symbol_to_refstr()?;
      let value_map =
        field_exprs.iter().tuples().map(|(field, value)| {
          let field_name = field.symbol_to_refstr()?;
          let field_value = eval(value, env)?;
          Ok((field_name, field_value))
        })
        .collect::<Result<HashMap<RefStr, Value>, Error>>()?;
      let s = env.instantiate_struct(&name, value_map).map_err(|s| error_raw(expr, s))?;
      Ok(Value::Struct(s))
    }
    (".", [expr, name_expr]) => {
      let s : StructVal = to_value(expr, env)?;
      let index = struct_field_index(&s.borrow().def, name_expr)?;
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
      // TODO: this for loop implementation is wildly slow, for many different reasons.
      let var = exprs[0].symbol_unwrap()?;
      let iterable = {
        let thing = eval(&exprs[1], env)?;
        let thing_type = thing.to_type();
        call_function(&exprs[1], "iterator", None, vec![thing], vec![thing_type], env)?
      };
      let iterable_type = iterable.to_type();
      let body = &exprs[2];
      env.scope.push(Default::default());
      env.new_variable(var.clone(), Value::Unit);
      env.loop_depth += 1;
      while env.exit_state == ExitState::NotExiting {
        let item = call_function(&exprs[1], "next_item", None, vec![iterable.clone()], vec![iterable_type.clone()], env)?;
        if item == Value::Unit {
          break;
        }
        let var_ref = env.dereference_variable(var).unwrap();
        *var_ref = item;
        eval(body, env)?;
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
        arg_names.push(arg.symbol_to_refstr()?);
        let arg_type =
          env.string_to_type(&type_expr.symbol_to_refstr()?)
          .map_err(|s| error_raw(type_expr, s))?;
        arg_types.push(arg_type);
      }
      let method = Method {
        visible_modules: env.visible_modules(),
        arg_names, arg_types,
        handle: FunctionHandle::Ast(Rc::new(function_body.clone())),
      };
      env.add_function(name, method).map_err(|s| error_raw(expr, s))?;
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
    _ => error(expr, format!("instruction '{}' with args {:?} is not supported by the interpreter.", instr, children)),
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
      if s.as_ref() == "break" {
        if env.loop_depth > 0 {
          env.exit_state = ExitState::Breaking;
          Ok(Value::Unit)
        }
        else {
          error(expr, format!("can't break outside a loop"))
        }
      }
      else if let Some(v) = env.dereference_variable(&s) {
        Ok(v.clone())
      }
      else if
        iter_modules(&env.scope)
        .map(|id| &env.loaded_modules[id.i])
        .find(|m| m.functions.contains_key(s.as_ref()))
        .is_some()
      {
        Ok(Value::Function(FunctionRef{ name: s.clone(), visible_modules: env.visible_modules() }))
      }
      else {
        return error(expr, format!("no variable or function in scope called '{}'", s));
      }
    }
    ExprTag::LiteralString(s) => Ok(Value::String(s.clone())),
    ExprTag::LiteralFloat(f) => Ok(Value::Float(*f)),
    ExprTag::LiteralBool(b) => Ok(Value::Bool(*b)),
    ExprTag::LiteralUnit => Ok(Value::Unit),
  }
}

pub fn eval_string(code : &str, env : &mut Environment) -> Result<Value, Error> {
  let tokens =
    lexer::lex_with_cache(code, env.symbol_cache)
    .map_err(|mut es| es.remove(0))?;
  let ast = parser::parse_with_cache(tokens, env.symbol_cache)?;
  eval(&ast, env)
}

