
use std::rc::Rc;
use std::fmt::Write;
use itertools::Itertools;

use crate::error::{Error, error, error_raw, TextLocation};
use crate::expr::{StringCache, RefStr, Expr, ExprContent, UIDGenerator};

use std::collections::{HashMap, HashSet};

#[derive(Clone, PartialEq, Debug)]
pub enum Val {
  Void,
  F64(f64),
  F32(f32),
  I64(i64),
  U64(u64),
  I32(i32),
  U32(u32),
  U16(u16),
  U8(u8),
  String(String),
  Bool(bool),
}

pub static TOP_LEVEL_FUNCTION_NAME : &'static str = "top_level";

#[derive(Debug, Clone, Copy)]
pub enum VarScope { Local, Global }

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LabelId {
  id : u64
}

#[derive(Debug)]
pub enum Content {
  Literal(Val),
  VariableInitialise(RefStr, Box<TypedNode>, VarScope),
  Assignment(Box<(TypedNode, TypedNode)>),
  IfThen(Box<(TypedNode, TypedNode)>),
  IfThenElse(Box<(TypedNode, TypedNode, TypedNode)>),
  Block(Vec<TypedNode>),
  Quote(Box<Expr>),
  Reference(RefStr),
  FunctionDefinition(RefStr),
  CBind(RefStr),
  TypeDefinition(RefStr),
  TypeConstructor(RefStr, Vec<(Option<RefStr>, TypedNode)>),
  FieldAccess(Box<(TypedNode, RefStr)>),
  Index(Box<(TypedNode, TypedNode)>),
  ArrayLiteral(Vec<TypedNode>),
  FunctionCall(Box<TypedNode>, Vec<TypedNode>),
  While(Box<(TypedNode, TypedNode)>),
  Convert(Box<(TypedNode, TypedNode)>),
  SizeOf(Box<TypedNode>),

  Label(Box<TypedNode>, LabelId),
  /// TODO: clone returned value, dropping all block values down the stack
  BreakToLabel(LabelId, Option<Box<TypedNode>>),
}

use Content::*;

#[derive(Debug)]
pub struct TypedNode {
  pub content : Content,
  pub loc : TextLocation,
}

fn node(expr : &Expr, content : Content) -> TypedNode {
  TypedNode { content, loc: expr.loc }
}

pub struct GlobalDefinition {
  pub name : RefStr,
  pub c_address : Option<usize>,
}

struct SymbolReference {
  symbol_name : RefStr,
  reference_location : TextLocation,
}

pub struct TypeChecker<'l> {
  uid_generator : &'l mut UIDGenerator,
  local_symbol_table : &'l HashMap<RefStr, usize>,

  type_definition_references : Vec<SymbolReference>,

  cache: &'l StringCache,
}

pub struct FunctionChecker<'l, 'lt> {
  t : &'l mut TypeChecker<'lt>,

  is_top_level : bool,

  labels_in_scope : Vec<LabelId>,
}

impl <'l> TypeChecker<'l> {

  pub fn new(
    uid_generator : &'l mut UIDGenerator,
    local_symbol_table : &'l HashMap<RefStr, usize>,
    cache : &'l StringCache)
      -> TypeChecker<'l>
  {
    TypeChecker {
      uid_generator,
      local_symbol_table,
      type_definition_references: vec!(),
      cache,
    }
  }
}

impl <'l, 'lt> FunctionChecker<'l, 'lt> {

  pub fn new(
    t : &'l mut TypeChecker<'lt>,
    is_top_level : bool)
      -> FunctionChecker<'l, 'lt>
  {
    FunctionChecker {
      t,
      is_top_level,
      labels_in_scope : vec![],
    }
  }

  fn typed_symbol(&mut self, e : &Expr) -> Result<(RefStr, Option<TypedNode>), Error> {
    if let Some((":", [s, t])) = e.try_construct() {
      let name = self.cached(s.unwrap_symbol()?);
      let type_tag = self.to_ast(t)?;
      Ok((name, Some(type_tag)))
    }
    else if let Ok(s) = e.unwrap_symbol() {
      let name = self.cached(s);
      Ok((name, None))
    }
    else {
      error(e, "invalid typed symbol construct")
    }
  }

  fn cached(&self, s : &str) -> RefStr {
    self.t.cache.get(s)
  }

  fn compile_template_arguments(&mut self, e : &Expr, args : &mut Vec<TypedNode>) -> Result<(), Error> {
    match e.try_construct() {
      Some(("$", [e])) => {
        args.push(self.to_ast(e)?);
      }
      Some((_, es)) => {
        for e in es {
          self.compile_template_arguments(e, args)?;
        }
      }
      _ => (),
    }
    Ok(())
  }

  /// Converts a quote to a typed node and handles templating if necessary
  fn quote_to_ast(&mut self, expr : &Expr, quoted_expr : &Expr) -> Result<TypedNode, Error> {
    // TODO: this function is kind of verbose and difficult to read
    let e = quoted_expr;
    let mut template_args = vec![];
    self.compile_template_arguments(e, &mut template_args)?;
    let main_quote = node(expr, Quote(Box::new(e.clone())));
    if template_args.len() > 0 {
      let template_quote_ref = reference(expr, self.cached("template_quote"));
      let array_literal = array_literal(expr, template_args);
      Ok(function_call(expr, template_quote_ref, vec![main_quote, array_literal]))
    }
    else {
      Ok(main_quote)
    }
  }

  fn to_type_constructor(&mut self, expr : &Expr, exprs : &[Expr]) -> Result<TypedNode, Error> {
    if exprs.len() < 1 {
      return error(expr, format!("malformed type instantiation"));
    }
    let name_expr = &exprs[0];
    let field_exprs = &exprs[1..];
    let name = name_expr.unwrap_symbol()?;
    let fields =
      field_exprs.iter().map(|e| {
        if let Some((":", [name, value])) = e.try_construct() {
          let name = self.cached(name.unwrap_symbol()?);
          Ok((Some(name), self.to_ast(value)?))
        }
        else {
          Ok((None, self.to_ast(e)?))
        }
      })
      .collect::<Result<Vec<(Option<RefStr>, TypedNode)>, Error>>()?;
    let c = TypeConstructor(self.cached(name), fields);
    Ok(node(expr, c))
  }

  fn construct_to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let (instr, children) = expr.unwrap_construct()?;
    match (instr, children) {
      ("call", exprs) => {
        let function_expr = &exprs[0];
        match function_expr.try_symbol() {
          Some("new") => return self.to_type_constructor(expr, &exprs[1..]),
          Some("sizeof") => {
            if exprs.len() == 2 {
              let type_tag = self.to_ast(&exprs[1])?;
              return Ok(node(expr, SizeOf(Box::new(type_tag))));
            }
          }
          _ => (),
        }
        let args =
          exprs[1..].iter().map(|e| self.to_ast(e))
          .collect::<Result<Vec<TypedNode>, Error>>()?;
        // Slight confusing control flow. This block returns a function pointer value, but only
        // if it fails to return early (which it will do if it finds either a matching intrinsic
        // or a matching function overload). It's structured this way to give better error messages.
        let function_value = self.to_ast(function_expr)?;
        let content = FunctionCall(Box::new(function_value), args);
        return Ok(node(expr, content));
      }
      ("as", [a, b]) => {
        let a = self.to_ast(a)?;
        let b = self.to_ast(b)?;
        Ok(node(expr, Convert(Box::new((a, b)))))
      }
      ("let", [e]) => {
        if let Some(("=", [name_expr, value_expr])) = e.try_construct() {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let v = Box::new(self.to_ast(value_expr)?);
          // The first scope is used for function arguments. The second
          // is the top level of the function.
          let c = if self.is_top_level && self.scope_map.len() == 2 {
            // global variable
            let def = GlobalDefinition { name: name.clone(), type_tag: v.type_tag.clone(), c_address: None };
            self.t.add_global(name.clone(), def);
            VariableInitialise(name, v, VarScope::Global)
          }
          else {
            // local variable
            let scoped_name = self.create_scoped_variable_name(name);
            self.variables.insert(scoped_name.clone(), v.type_tag.clone());
            VariableInitialise(scoped_name, v, VarScope::Local)
          };
          return Ok(node(expr, Type::Void, c));
        }
        error(expr, "malformed let expression")
      }
      ("#", [quoted_expr]) => {
        self.quote_to_ast(expr, quoted_expr)
      }
      ("=", [assign_expr, value_expr]) => {
        let a = self.to_ast(assign_expr)?;
        let b = self.to_ast(value_expr)?;
        Ok(node(expr, Type::Void, Assignment(Box::new((a, b)))))
      }
      ("return", exprs) => {
        if exprs.len() > 1 {
          return error(expr, format!("malformed return expression"));
        }
        let (return_val, type_tag) =
          if exprs.len() == 1 {
            let v = self.to_ast(&exprs[0])?;
            let t = v.type_tag.clone();
            (Some(Box::new(v)), t)
          }
          else {
            (None, Type::Void)
          };
        let c = BreakToLabel(*self.labels_in_scope.first().unwrap(), return_val);
        Ok(node(expr, type_tag, c))
      }
      ("while", [condition_expr, body_expr]) => {
        let label = LabelId { id: self.t.uid_generator.next() };
        // Add label to scope in case the loop breaks
        self.labels_in_scope.push(label);
        let condition = self.to_ast(condition_expr)?;
        let body = self.to_ast(body_expr)?;
        let while_node = node(expr, Type::Void, While(Box::new((condition, body))));
        let labelled_while = node(expr, Type::Void, Label(Box::new(while_node), label));
        // Remove label
        self.labels_in_scope.pop();
        Ok(labelled_while)
      }
      // ("for", [var_range_expr, body_expr]) => {
      //   if let Some(("in", [var, range])) = var_range_expr.try_construct() {
      //     if let Some(var_name) = var.try_symbol() {
      //       /*
      //         {
      //           let #range = range(0, 10)
      //           let #end = #range.end
      //           let i = #range.start
      //           while i < #end {
      //             $body_expr
      //             i = i + 1
      //           }
      //         }
      //       */

      //       let range_node = self.to_ast(range)?;
      //       let for_block = block(expr, vec![
      //         let_var(expr, range_var, range_node),
      //         let_var(expr, end_var, field_access(expr, range_var, "end")),
      //         let_var(expr, loop_var, field_access(expr, range_var, "start")),
      //         node(expr, Type::Void, While((
      //           intrinsic("<", vec![loop_var, end_var]),
      //           block(expr, vec![
      //             self.to_ast(body_expr)?,
      //             assignment(loop_var, intrinsic("+", vec![loop_var, literal_int(1)])),
      //           ])
      //         ).into()))
      //       ]);
      //       return Ok(for_block);
      //     }
      //   }
      //   error(expr, "malformed for expression")
      // }
      ("if", exprs) => {
        if exprs.len() > 3 {
          return error(expr, "malformed if expression");
        }
        let condition = self.to_ast(&exprs[0])?;
        condition.assert_type(Type::Bool)?;
        let then_branch = self.to_ast(&exprs[1])?;
        if exprs.len() == 3 {
          let else_branch = self.to_ast(&exprs[2])?;
          if then_branch.type_tag != else_branch.type_tag {
            return error(expr, "if/else branch type mismatch");
          }
          let t = then_branch.type_tag.clone();
          let c = IfThenElse(Box::new((condition, then_branch, else_branch)));
          Ok(node(expr, t, c))
        }
        else {
          Ok(node(expr, Type::Void, IfThen(Box::new((condition, then_branch)))))
        }
      }
      ("block", exprs) => {
        self.scope_map.push(HashMap::new());
        let mut nodes = vec![];
        if let Some(last) = exprs.last() {
          for e in &exprs[0..exprs.len()-1] {
            nodes.push(self.to_ast(e)?);
          }
          let n = self.to_ast(last)?;
          nodes.push(n);
        }
        //let nodes = exprs.iter().map(|e| self.to_ast(e)).collect::<Result<Vec<TypedNode>, Error>>()?;
        self.scope_map.pop();
        let t = nodes.last().map(|n| n.type_tag.clone()).unwrap_or(Type::Void);
        Ok(node(expr, t, Block(nodes)))
      }
      ("cbind", [e]) => {
        if let (":", [name_expr, type_expr]) = e.unwrap_construct()? {
          let name = self.cached(name_expr.unwrap_symbol()?);
          let type_tag = self.t.to_type(type_expr)?;
          let address = self.t.local_symbol_table.get(&name).map(|v| *v);
          if address.is_none() {
            // TODO: check the signature of the function too
            println!("Warning: C binding '{}' not linked. LLVM linker may link it instead.", name);
            // return error(expr, "tried to bind non-existing C function")
          }
          // TODO: Why is it necessary to treat function pointers specially? If I treat
          // them as globals the tests stop passing, but I'm not sure why.
          if let Type::Fun(sig) = &type_tag {
            let args =
              sig.args.iter().enumerate().
              map(|(i, _)| ((i + 65) as u8 as char).to_string().into())
              .collect();
            let def = FunctionDefinition {
              name_in_code: name.clone(),
              name_for_codegen: name.clone(),
              args,
              signature: sig.clone(),
              implementation: FunctionImplementation::CFunction(address),
              module_id: self.t.module.id,
              definition_location: expr.loc,
            };
            self.t.add_function(def);
          }
          else {
            let def = GlobalDefinition { name: name.clone(), type_tag, c_address: address };
            self.t.add_global(name.clone(), def);
          }
          return Ok(node(expr, Type::Void, CBind(name)))
        }
        error(expr, "invalid cbind expression")
      }
      ("fun", exprs) => {
        if let [name, args_exprs, function_body] = exprs {
          let name = self.cached(name.unwrap_symbol()?);
          let args_exprs = args_exprs.children();
          let mut arg_names = vec!();
          let mut arg_types = vec!();
          for arg in args_exprs.iter() {
            let (name, type_tag) = self.t.typed_symbol(arg)?;
            if type_tag == Type::Void {
              return error(expr, "functions args cannot be void");
            }
            arg_names.push(name);
            arg_types.push(type_tag);
          }
          let args = arg_names.iter().cloned().zip(arg_types.iter().cloned()).collect();
          let mut function_checker = FunctionChecker::new(self.t, false, args);
          let body = function_checker.to_function_body(function_body)?;
          if self.t.find_function(&name, arg_types.as_slice()).is_some() {
            return error(expr, "function with that name already defined");
          }
          let signature = Rc::new(FunctionSignature {
            return_type: body.type_tag.clone(),
            args: arg_types,
          });
          let def = FunctionDefinition {
            name_in_code: name.clone(),
            name_for_codegen: format!("{}.{}", name, self.t.uid_generator.next()).into(),
            args: arg_names,
            signature,
            implementation: FunctionImplementation::Normal(body),
            module_id: self.t.module.id,
            definition_location: expr.loc,
          };
          self.t.add_function(def);
          return Ok(node(expr, Type::Void, FunctionDefinition(name)))
        }
        error(expr, "malformed function definition")
      }
      ("union", exprs) => {
        let name = self.cached(&exprs[0].unwrap_symbol()?);
        Ok(node(expr, Type::Void, TypeDefinition(name)))
      }
      ("struct", exprs) => {
        let name = self.cached(&exprs[0].unwrap_symbol()?);
        Ok(node(expr, Type::Void, TypeDefinition(name)))
      }
      (".", [container_expr, field_expr]) => {
        let container_val = self.to_ast_dereferenced(container_expr)?;
        let field_name = self.cached(field_expr.unwrap_symbol()?);
        let def = match &container_val.type_tag {
          Type::Def(type_name) => self.t.find_type_def(type_name).unwrap(),
          _ => return error(container_expr, format!("expected struct or union, found {:?}", container_val.type_tag)),
        };
        let (_, field_type) =
          def.fields.iter().find(|(n, _)| n==&field_name)
          .ok_or_else(|| error_raw(field_expr, "type does not have field with this name"))?;
        let field_type = field_type.clone();
        let c = FieldAccess(Box::new((container_val, field_name)));
        Ok(node(expr, field_type, c))
      }
      ("array", exprs) => {
        let mut elements = vec!();
        for e in exprs {
          elements.push(self.to_ast(e)?);
        }
        let t =
          if let Some(a) = elements.first() {
            for b in &elements[1..] {
              if a.type_tag != b.type_tag {
                return error(expr, format!("array initialiser contains more than one type."));
              }
            }
            a.type_tag.clone()
          }
          else {
            // dummy value for an empty array
            Type::U8
          };
        Ok(node(expr, Type::Array(Box::new(t)), ArrayLiteral(elements)))
      }
      ("index", exprs) => {
        let array_expr = &exprs[0];
        if let [index_expr] = &exprs[1..] {
          let array = self.to_ast(array_expr)?;
          let inner_type = match &array.type_tag {
            Type::Array(t) => *(t).clone(),
            Type::Ptr(t) => *(t).clone(),
            _ => return error(array_expr, "expected array"),
          };
          let index = self.to_ast(index_expr)?;
          if index.type_tag != Type::I64 {
            return error(array_expr, "expected integer");
          }
          return Ok(node(expr, inner_type, Index(Box::new((array, index)))));
        }
        error(expr, "malformed array index expression")
      }
      (construct, _) => {
        error(expr, format!("invalid '{}' expression", construct))
      }
    }
  }

  fn to_ast_dereferenced(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    let mut n = self.to_ast(expr)?;
    loop {
      match &n.type_tag {
        Type::Ptr(t) => {
          let t : Type = (**t).clone();
          let c = IntrinsicCall(self.cached("*"), vec![n]);
          n = node(expr, t, c);
        }
        _ => return Ok(n),
      }
    }
  }

  pub fn to_ast(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    match &expr.content {
      ExprContent::List(_, _) => {
        return self.construct_to_ast(expr);
      }
      ExprContent::Symbol(s) => {
        // this is just a normal symbol
        let s = self.cached(s.as_str());
        if s.as_ref() == "break" {
          let c = BreakToLabel(*self.labels_in_scope.last().unwrap(), None);
          return Ok(node(expr, Type::Void, c));
        }
        if let Some(variable) = self.variable_to_ast(expr, &s) {
          return Ok(variable)
        }
        let mut function_iter = self.t.find_functions(&s);
        if let Some(def) = function_iter.next() {
          if function_iter.next().is_some() {
            return error(expr, "can't disambiguate multiple functions with the same name");
          }
          let c = FunctionReference(def.function_reference());
          return Ok(node(expr, Type::Fun(def.signature.clone()), c));
        }
        error(expr, format!("unknown symbol '{}'", s))
      }
      ExprContent::LiteralString(s) => {
        let v = Val::String(s.as_str().to_string());
        let s = self.t.find_type_def("string").unwrap();
        Ok(node(expr, Type::Def(s.name.clone()), Literal(v)))
      }
      ExprContent::LiteralFloat(f) => {
        let v = Val::F64(*f as f64);
        Ok(node(expr, Type::F64, Literal(v)))
      }
      ExprContent::LiteralInt(v) => {
        let v = Val::I64(*v as i64);
        Ok(node(expr, Type::I64, Literal(v)))
      }
      ExprContent::LiteralBool(b) => {
        let v = Val::Bool(*b);
        Ok(node(expr, Type::Bool, Literal(v)))
      },
      ExprContent::LiteralUnit => {
        Ok(node(expr, Type::Void, Literal(Val::Void)))
      },
      // _ => error(expr, "unsupported expression"),
    }
  }

  fn to_function_body(&mut self, expr : &Expr) -> Result<TypedNode, Error> {
    if self.labels_in_scope.len() != 0 {
      panic!("labels_in_scope in invalid state");
    }
    let label = LabelId{ id: self.t.uid_generator.next() };
    self.labels_in_scope.push(label);
    let body = self.to_ast(expr)?;
    self.labels_in_scope.pop();
    let t = body.type_tag.clone();
    let c = Label(Box::new(body), label);
    Ok(node(expr, t, c))
  }
}

fn loc_struct(expr : &Expr, loc_def : &TypeDefinition, marker_def : &TypeDefinition) -> TypedNode {
  let start = {
    let col = u64_literal(expr, expr.loc.start.col as u64);
    let line = u64_literal(expr, expr.loc.start.line as u64);
    struct_instantiate(expr, marker_def, vec![col, line])
  };
  let end = {
    let col = u64_literal(expr, expr.loc.end.col as u64);
    let line = u64_literal(expr, expr.loc.end.line as u64);
    struct_instantiate(expr, marker_def, vec![col, line])
  };
  struct_instantiate(expr, loc_def, vec![start, end])
}

fn u64_literal(expr : &Expr, i : u64) -> TypedNode {
  node(expr, Literal(Val::U64(i)))
}

fn array_literal(expr : &Expr, args : Vec<TypedNode>) -> TypedNode {
  let args = ArrayLiteral(args);
  node(expr, args)
}

fn reference(expr : &Expr, name : RefStr) -> TypedNode {
  node(expr, Content::Reference(name))
}

fn function_call(expr : &Expr, function : TypedNode, args : Vec<TypedNode>) -> TypedNode {
  let function_ref = node(expr, t, c);
  let function_call = FunctionCall(Box::new(function_ref), args);
  node(expr, def.signature.return_type.clone(), function_call)
}

fn struct_instantiate(expr : &Expr, def : &TypeDefinition, args : Vec<TypedNode>) -> TypedNode {
  node(expr,
    Type::Def(def.name.clone()),
    StructInstantiate(def.name.clone(), args))
}

pub fn to_typed_module(uid_generator : &mut UIDGenerator, local_symbol_table : &HashMap<RefStr, usize>, modules : &[&TypedModule], cache : &StringCache, expr : &Expr) -> Result<TypedModule, Error> {
  let mut module = TypedModule::new(uid_generator.next());
  let mut type_checker =
    TypeChecker::new(uid_generator, &mut module, modules, local_symbol_table, cache);
  
  let mut types = vec!();
  find_type_definitions(expr, &mut types);

  // Process the types
  for e in types {
    type_checker.add_type_definition(e)?;
  }

  // Process the rest of the module (adds functions and globals)
  let mut function_checker =
    FunctionChecker::new(&mut type_checker, true, HashMap::new());
  let body = function_checker.to_function_body(expr)?;

  // Check any unresolved symbols
  let unresolved_types : Vec<_> = type_checker.type_definition_references.drain(0..).collect();
  for t in unresolved_types {
    if type_checker.find_type_def(&t.symbol_name).is_none() {
      return error(t.reference_location, format!("type definition '{}' not found", t.symbol_name));
    }
  }

  // Look for drop functions and clone functions
  fn register_f(
    type_checker : &mut TypeChecker,
    function_name : &str,
    f : fn(&mut TypeDefinition, &FunctionDefinition) -> Result<(), Error>)
      -> Result<(), Error>
  {
    let functions = type_checker.module.functions.iter().filter(move |def| def.name_in_code.as_ref() == function_name);
    for fun_def in functions {
      if let [Type::Ptr(t)] = fun_def.signature.args.as_slice() {
        if let Type::Def(n) = &**t {
          if let Some(type_def) = type_checker.module.types.get_mut(n) {
            if type_def.kind == TypeKind::Struct {
              f(type_def, fun_def)?;
            }
          }
          else {
            println!("Types: {:?}", type_checker.module.types.keys());
            return error(fun_def.definition_location,
              format!("Function {} must be defined in the same module as type {}.", function_name, n));
          }
        }
      }
    }    
    Ok(())
  }
  register_f(&mut type_checker, "Drop", |td, fd| {
    if fd.signature.return_type == Type::Void {
      td.drop_function = Some(fd.function_reference());
      return Ok(());
    }
    error(fd.definition_location, "Drop function must have void return")
  })?;
  register_f(&mut type_checker, "Clone", |td, fd| {
    if let Type::Def(n) = &fd.signature.return_type {
      if n == &td.name {
        td.clone_function = Some(fd.function_reference());
        return Ok(());
      }
    }
    error(fd.definition_location, "Clone function must return new instance")
  })?;

  // TODO: figure out which types are Move and which are Copy

  let name = cache.get(TOP_LEVEL_FUNCTION_NAME);
  if type_checker.module.functions.iter().find(|def| def.name_in_code == name).is_some() {
    return error(expr, "top level function already defined!");
  }
  let signature = Rc::new(FunctionSignature {
    return_type: body.type_tag.clone(),
    args: vec!(),
  });
  let def = FunctionDefinition {
    name_in_code: name.clone(),
    name_for_codegen: name,
    args: vec!(),
    signature,
    implementation: FunctionImplementation::Normal(body),
    module_id: type_checker.module.id,
    definition_location: expr.loc,
  };
  type_checker.add_function(def);
  Ok(module)
}
