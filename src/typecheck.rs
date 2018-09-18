
use error::{Error, TextLocation};
use parser::Expr;
use value::RefStr;
use utils::{symbol_unwrap, symbol_to_refstr};
use std::collections::HashMap;

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
  Unit, Float, Bool, Array, Struct(RefStr), Any
}

struct FunctionSignature {
  return_type : Type,
  args : Vec<Type>,
}

struct StructType {
  name : RefStr,
  fields : Vec<(RefStr, Type)>,
}


struct Environment<'l> {
  functions : &'l mut HashMap<RefStr, FunctionSignature>,
  structs : &'l mut HashMap<RefStr, StructType>,
  locals : Vec<Vec<(RefStr, Type)>>,
}

impl <'l> Environment <'l> {
  fn new(
    functions : &'l mut HashMap<RefStr, FunctionSignature>,
    structs : &'l mut HashMap<RefStr, StructType>,
    arguments : Vec<(RefStr, Type)>) -> Environment<'l>
  {
    let locals = vec![arguments];
    Environment { functions, structs, locals }
  }

  fn find_var_type(&self, v : &str) -> Result<Type, Error> {
    for vs in self.locals.iter().rev() {
      for (name, t) in vs.iter().rev() {
        if name.as_ref() == v {
          return Ok(t.clone());
        }
      }
    }
    error_result!("no variable called '{}' found in scope", v)
  }

  fn find_field_type(&self, struct_name : &str, field_name : &str) -> Result<Type, Error> {
    let def = 
      self.structs.get(struct_name)
      .ok_or_else(|| error!("struct {} does not exist", struct_name))?.clone();
    let (_, field_type) =
      def.fields.iter().find(|(n, _)| n.as_ref() == field_name)
      .ok_or_else(|| error!("field {} does not exist on struct {}", field_name, struct_name))?;
    Ok(field_type.clone())
  }
}

fn type_unify(a : &Type, b : &Type) -> Result<Type, Error> {
  if a == &Type::Any {
    Ok(b.clone())
  }
  else if b == &Type::Any {
    Ok(a.clone())
  }
  else if a == b {
    Ok(a.clone())
  }
  else {
    error_result!("Expected types {:?} and {:?} to match.", a, b)
  }
}

fn types_compatible(a : &Type, b : &Type) -> bool {
  type_unify(a, b).is_ok()
}

fn assert_expected_found(expected : &Type, found : &Type) -> Result<(), Error> {
  if !types_compatible(expected, found) {
    return error_result!("Expected type {:?}, but found type {:?}.", expected, found);
  }
  return Ok(());
}

fn struct_name(t : Type) -> Result<RefStr, Error> {
  match t {
    Type::Struct(s) => Ok(s),
    _ => error_result!("Expected a struct but found type {:?}.", t),
  }
}

fn string_to_type(s : &str) -> Result<Type, Error> {
  match s {
    "float" => Ok(Type::Float),
    "unit" => Ok(Type::Unit),
    "bool" => Ok(Type::Bool),
    "array" => Ok(Type::Array),
    "any" | "[NO_TYPE]" => Ok(Type::Any),
    _ => error_result!("{:?} is not a valid type", s),
  }
}

fn typecheck_function_call(function_name: RefStr, args: &[Type], env : &mut Environment) -> Result<Type, Error> {
  let def = env.functions.get(&function_name)
    .ok_or_else(|| error!("Found no function called '{}'", function_name))?;
  for (e_t, f_t) in def.args.iter().zip(args) {
    assert_expected_found(e_t, f_t)?;
  }
  Ok(def.return_type.clone())
}

fn typecheck_instr(instr : &str, args : &Vec<Expr>, env : &mut Environment) -> Result<Type, Error> {
  match (instr, args.as_slice()) {
    ("call", exprs) => {
      let symbol = match &exprs[0] {
        Expr::Symbol(s) => s,
        _ => return error_result!("expected symbol"),
      };
      let params = exprs[1..].iter().map(|e| typecheck_env(e, env)).collect::<Result<Vec<Type>, Error>>()?;
      fn binary(expected_a : &Type, a : &Type, expected_b : &Type, b : &Type, returns : Type) -> Result<Type, Error> {
        assert_expected_found(expected_a, a)?;
        assert_expected_found(expected_b, b)?;
        Ok(returns)
      }
      match params.as_slice() {
        [a, b] => {
          match symbol.as_ref() {
            "+" | "-" | "*" | "/" => return binary(&Type::Float, a, &Type::Float, b, Type::Float),
            ">" | "<" | "<=" | ">=" => return binary(&Type::Float, a, &Type::Float, b, Type::Bool),
            "==" => { type_unify(a, b)?; return Ok(Type::Bool); }
            "&&" | "||" => return binary(&Type::Bool, a, &Type::Bool, b, Type::Bool),
            _ => {}
          }
        }
        [v] => {
          match symbol.as_ref() {
            "-" => { assert_expected_found(&Type::Float, v)?; return Ok(Type::Float); }
            "!" => { assert_expected_found(&Type::Bool, v)?; return Ok(Type::Bool); }
            _ => {}
          }
        }
        _ => (),
      }
      return typecheck_function_call(symbol.clone(), &params, env);
    }
    ("block", exprs) => {
      env.locals.push(vec![]);
      let num_exprs = exprs.len();
      if num_exprs > 1 {
        for i in 0..(num_exprs-1) {
          typecheck_env(&exprs[i], env)?;
        }
      }
      let block_type = typecheck_env(&exprs[num_exprs-1], env)?;
      env.locals.pop();
      Ok(block_type)
    }
    ("let", [Expr::Symbol(var_symbol), value_expr]) => {
      let value_type = typecheck_env(value_expr, env)?;
      env.locals.last_mut().unwrap().push((var_symbol.clone(), value_type));
      Ok(Type::Unit)
    }
    ("=", [Expr::Symbol(var_symbol), value_expr]) => {
      let var_type = env.find_var_type(var_symbol)?;
      let value_type = typecheck_env(&value_expr, env)?;
      if !types_compatible(&value_type, &var_type) {
        return error_result!("can't assign value of type {:?} to variable of type {:?}", value_type, var_type);
      }
      Ok(Type::Unit)
    }
    ("=", [Expr::Expr { symbol, args }, value_expr]) => {
      match (symbol.as_ref(), args.as_slice()) {
        ("index", [array_expr, index_expr]) => {
          let array_type = typecheck_env(array_expr, env)?;
          assert_expected_found(&Type::Array, &array_type)?;
          let index_type = typecheck_env(index_expr, env)?;
          assert_expected_found(&Type::Float, &index_type)?;
          let _value_type = typecheck_env(&value_expr, env)?;
          // TODO: array types aren't generic, so we can't check the value being assigned yet
          Ok(Type::Unit)
        }
        (".", [struct_expr, field_expr]) => {
          let struct_type = typecheck_env(struct_expr, env)?;
          let struct_name = struct_name(struct_type)?;
          let value_type = typecheck_env(&value_expr, env)?;
          let field_name = symbol_unwrap(field_expr)?;
          let field_type = env.find_field_type(&struct_name, &field_name)?;
          if !types_compatible(&value_type, &field_type) {
            return error_result!("can't assign value of type {:?} to field of type {:?}", value_type, field_type);
          }
          Ok(Type::Unit)
        }
        _ => error_result!("can't assign to {:?}", (symbol, args)),
      }
    }
    ("if", exprs) => {
      let arg_count = exprs.len();
      if arg_count < 2 || arg_count > 3 {
        return error_result!("malformed if expression");
      }
      let condition_type = typecheck_env(&exprs[0], env)?;
      assert_expected_found(&Type::Bool, &condition_type)?;
      let then_type = typecheck_env(&exprs[1], env)?;
      if arg_count == 3 {
        let else_type = typecheck_env(&exprs[2], env)?;
        type_unify(&then_type, &else_type)
      }
      else {
        Ok(Type::Unit)
      }
    }
    ("struct_define", exprs) => {
      if exprs.len() < 1 {
        return error_result!("malformed struct definition");
      }
      let name = symbol_to_refstr(&exprs[0])?;
      if env.structs.contains_key(&name) {
        return error_result!("A struct called {} has already been defined.", name);
      }
      // TODO: check for duplicates?
      let field_exprs = &exprs[1..];
      let mut fields = vec![];
      for i in (0..(field_exprs.len()-1)).step_by(2) {
        let name = symbol_to_refstr(&field_exprs[i])?;
        let field_type = string_to_type(symbol_unwrap(&field_exprs[i+1])?)?;
        fields.push((name, field_type));
      }
      let def = StructType { name: name.clone(), fields };
      env.structs.insert(name, def);
      Ok(Type::Unit)
    }
    ("struct_instantiate", exprs) => {
      if exprs.len() < 1 || exprs.len() % 2 == 0 {
        return error_result!("malformed struct instantiation {:?}", exprs);
      }
      let name = symbol_to_refstr(&exprs[0])?;
      let mut field_type_map = {
        let def =
          env.structs.get(name.as_ref())
          .ok_or_else(|| error!("struct {} does not exist", name))?.clone();
        def.fields.iter()
        .map(|(s, t)| (s.clone(), t.clone()))
        .collect::<HashMap<RefStr, Type>>()
      };
      for i in (1..exprs.len()).step_by(2) {
        let field_name = symbol_to_refstr(&exprs[i])?;
        let type_name = typecheck_env(&exprs[i+1], env)?;
        let expected_type = field_type_map.remove(field_name.as_ref())
          .ok_or_else(|| error!("field {} does not exist", name))?;
        assert_expected_found(&expected_type, &type_name)?;
      }
      if field_type_map.len() > 0 {
        return error_result!("Some fields not initialised: {:?}", field_type_map);
      }
      Ok(Type::Struct(name))
    }
    (".", [expr, field_name]) => {
      let struct_name = struct_name(typecheck_env(expr, env)?)?;
      let field_name = symbol_unwrap(field_name)?;
      let field_type = env.find_field_type(&struct_name, field_name)?;
      Ok(field_type)
    }
    ("while", exprs) => {
      if exprs.len() != 2 {
        return error_result!("malformed while block");
      }
      let condition_type = typecheck_env(&exprs[0], env)?;
      assert_expected_found(&Type::Bool, &condition_type)?;
      let _body_type = typecheck_env(&exprs[1], env)?;
      Ok(Type::Unit)
    }
    ("fun", [Expr::Symbol(name), Expr::Expr{ args, .. }, function_body ]) => {
      let mut params = vec![];
      for i in (0..(args.len()-1)).step_by(2) {
        let name = symbol_unwrap(&args[i])?.clone();
        let arg_type = string_to_type(symbol_unwrap(&args[i+1])?)?;
        params.push((name, arg_type));
      }
      let args = params.iter().map(|(_, t)| t.clone()).collect();
      let mut new_env = Environment::new(&mut env.functions, &mut env.structs, params);
      let return_type = typecheck_env(function_body, &mut new_env)?;
      let signature = FunctionSignature { return_type, args };
      new_env.functions.insert(name.clone(), signature);
      Ok(Type::Unit)
    }
    ("literal_array", exprs) => {
      for e in exprs {
        typecheck_env(e, env)?;
      }
      Ok(Type::Array)
    }
    ("index", exprs) => {
      if let [array_expr, index_expr] = exprs {
        let array_type = typecheck_env(array_expr, env)?;
        assert_expected_found(&Type::Array, &array_type)?;
        let index_type = typecheck_env(index_expr, env)?;
        assert_expected_found(&Type::Float, &index_type)?;
        Ok(Type::Any)
      }
      else {
        return error_result!("index instruction expected 2 arguments. Found {}.", exprs.len());
      }
    }
    _ => {
      error_result!("instruction '{}' with args {:?} is not supported by the type checker.", instr, args)
    }
  }
}

fn typecheck_env(ast : &Expr, env : &mut Environment) -> Result<Type, Error> {
  match ast {
    Expr::Expr{ symbol, args } => {
      typecheck_instr(symbol, args, env)
    }
    Expr::Symbol(s) => {
      if s.as_ref() == "break" {
        Ok(Type::Unit)
      }
      else {
        env.find_var_type(s)
      }
    }
    Expr::LiteralFloat(_) => {
      Ok(Type::Float)
    }
    Expr::LiteralBool(_) => {
      Ok(Type::Bool)
    }
  }
}

pub fn typecheck(ast : &Expr) -> Result<Type, Error> {
  let mut functions = HashMap::new();
  let mut structs = HashMap::new();
  let mut env = Environment::new(&mut functions, &mut structs, vec![]);
  typecheck_env(ast, &mut env)
}
