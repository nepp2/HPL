
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment the error reporting for incorrect
/// programs is nondeterministic due to iteration over Rust's secure, randomised
/// HashMaps. This should be fixed at some point so that the most useful error
/// messages are reliably shown to users.

use itertools::Itertools;

use crate::{error, expr, structure, types, inference_constraints, code_store};

use error::{Error, error, error_raw, TextLocation, ErrorContent};
use expr::{UIDGenerator, Uid, RefStr, StringCache};
use structure::{
  NodeId, TypeKind, Nodes,
};
use types::{
  Type, TypeContent, TypeInfo, TypeDirectory, SymbolId,
  SignatureBuilder, incremental_unify, TypeMapping,
  UnifyResult, UnitId, AbstractType, SymbolInit, SymbolDefinition,
};
use inference_constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSymbol, Assertion,
};
use code_store::CodeStore;

use std::collections::{HashMap, VecDeque};

use TypeContent::*;

pub fn infer_types(
  unit_id : UnitId,
  code_store : &CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<(TypeInfo, TypeMapping), Error>
{
  let mut mapping = TypeMapping::new();
  let mut errors = vec![];
  let mut new_types = TypeInfo::new(unit_id);
  let imports : Vec<_> =
    code_store.types.values().collect();
  let mut type_directory =
    TypeDirectory::new(unit_id, imports.as_slice(), &mut new_types);
  let nodes = code_store.nodes(unit_id);
  let c =
    inference_constraints::get_module_constraints(
      &nodes, &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, code_store, &mut type_directory,
    &mut mapping, &c, cache, gen, &mut errors);
  i.infer();
  if errors.len() > 0 {    
    let c = ErrorContent::InnerErrors("type errors".into(), errors);
    error(nodes.root().loc, c)
  }
  else {
    Ok((new_types, mapping))
  }
}

pub fn typecheck_polymorphic_function_instance(
  instance_unit : UnitId,
  poly_function : &SymbolDefinition,
  instance_type : &Type,
  code_store : &CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<(TypeInfo, TypeMapping, SymbolId), Error>
{
  let mut mapping = TypeMapping::new();
  let mut errors = vec![];
  let mut new_types = TypeInfo::new(instance_unit);
  let aaa = (); // TODO: type directory should just take the code store, and be a lot simpler
  let imports : Vec<_> = code_store.types.values().collect();
  let mut type_directory =
    TypeDirectory::new(instance_unit, imports.as_slice(), &mut new_types);
  let nodes = code_store.nodes(poly_function.unit_id);
  let source_node =
    *code_store.type_mapping(poly_function.unit_id)
    .symbol_def_nodes.get(&poly_function.id).unwrap();
  let instanced_type_vars = poly_function.instanced_type_vars(instance_type);
  let (c, symbol_id) =
    inference_constraints::get_polymorphic_function_instance_constraints(
      &nodes, source_node, instance_type.clone(), instanced_type_vars.as_slice(),
      &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, code_store, &mut type_directory,
    &mut mapping, &c, cache, gen, &mut errors);
  i.infer();
  if errors.len() > 0 {
    let c = ErrorContent::InnerErrors("type errors".into(), errors);
    error(nodes.root().loc, c)
  }
  else {
    Ok((new_types, mapping, symbol_id))
  }
}

struct Inference<'a> {
  nodes : &'a Nodes,
  code_store : &'a CodeStore,
  t : &'a mut TypeDirectory<'a>,
  mapping : &'a mut TypeMapping,
  c : &'a Constraints,
  cache : &'a StringCache,
  gen : &'a mut UIDGenerator,
  errors : &'a mut Vec<Error>,
  dependency_map : ConstraintDependencyMap<'a>,
  next_edge_set : HashMap<Uid, &'a Constraint>,
  resolved : HashMap<TypeSymbol, Type>,
}

impl <'a> Inference<'a> {

  fn new(
    nodes : &'a Nodes,
    code_store : &'a CodeStore,
    t : &'a mut TypeDirectory<'a>,
    mapping : &'a mut TypeMapping,
    c : &'a Constraints,
    cache : &'a StringCache,
    gen : &'a mut UIDGenerator,
    errors : &'a mut Vec<Error>)
      -> Self
  {
    Inference {
      nodes, code_store, t, mapping, c, cache, gen, errors,
      dependency_map: ConstraintDependencyMap::new(),
      next_edge_set: HashMap::new(),
      resolved: HashMap::new(),
    }
  }

  fn get_type(&self, ts : TypeSymbol) -> Option<&Type> {
    self.resolved.get(&ts)
  }

  fn type_updated(&mut self, ts : TypeSymbol) {
    if let Some(cs) = self.dependency_map.ts_map.get(&ts) {
      for &c in cs.iter() {
        self.next_edge_set.insert(c.id, c);
      }
    }
  }

  fn update_type(&mut self, ts : TypeSymbol, t : &Type) -> UnifyResult {
    let ts_type = if let Some(t) = self.resolved.get_mut(&ts) {
      t
    }
    else {
      self.resolved.entry(ts).or_insert(Type::any())
    };
    let r = incremental_unify(t, ts_type);
    if !r.unify_success {
      let s = format!("conflicting types inferred; {} and {}.", t, ts_type);
      let e = error_raw(self.loc(ts), s);
      self.errors.push(e);
    }
    if r.mutable_type_changed {
      self.type_updated(ts);
    }
    r
  }

  /// returns true if the input type `t` was mutated
  fn update_type_mut(&mut self, ts : TypeSymbol, t : &mut Type) -> bool {
    let r = self.update_type(ts, t);
    if r.immutable_type_changed && r.unify_success {
      let r = incremental_unify(self.resolved.get(&ts).unwrap(), t);
      if !r.unify_success { panic!("unification is not commutable!") }
      true
    }
    else {
      false
    }
  }

  fn loc(&self, ts : TypeSymbol) -> TextLocation {
    *self.c.symbols.get(&ts).unwrap()
  }

  fn unresolved_constraint_error(&mut self, c : &Constraint) {
    use ConstraintContent::*;
    let e = match &c.content  {
      Equalivalent(_a, _b) => return,
      // this error should always be accompanied by other unresolved constraints
      Function{ function:_, args:_, return_type:_ } => return,
      Constructor { def_ts:_ , fields:_ } => return,
      Convert { val:_, into_type_ts:_ } => return,
      SymbolDef { symbol_id, type_symbol:_ } => {
        let def = self.t.get_symbol_mut(*symbol_id);
        let node_id = *self.mapping.symbol_def_nodes.get(symbol_id).unwrap();
        let loc = self.nodes.node(node_id).loc;
        error_raw(loc,
          format!("Global definition '{}' not resolved. Inferred type {}.", def.name, def.type_tag))
      }
      GlobalReference { node:_, name, result } => {
        let any = Type::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols = self.t.find_symbol(&name, t);
        let cs = &self.code_store;
        let s = symbols.iter().map(|g| {
          let def = cs.symbol_def(g.symbol_id);
          format!("      {} : {}", def.name, g.resolved_type)
        }).join("\n");
        error_raw(self.loc(*result),
          format!("Reference '{}' of type '{}' not resolved\n   Symbols available:\n{}", name, t, s))
      }
      FieldAccess{ container:_, field, result:_ } => {
        error_raw(field.loc,
          format!("field access '{}' not resolved", field.name))
      }
      Array{ array, element:_ } => {
        error_raw(self.loc(*array), "array literal not resolved")
      }
      SizeOf { node:_, ts } => {
        error_raw(self.loc(*ts), "sizeof type not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, symbol_id : SymbolId) {
    self.mapping.symbol_references.insert(node, symbol_id);
  }

  fn resolve_abstract_defs<'l>(&self, loc : TextLocation, t : &'l Type)
    -> Result<Type, Error> 
  {
    let content = match &t.content {
      Abstract(AbstractType::Def(name)) => {
        if let Some(def) = self.t.find_type_def(name) {
          let children = if t.children.len() == 0 {
            def.type_vars.iter().map(|_| Type::any()).collect()
          }
          else if t.children.len() != def.type_vars.len() {
            return error(loc, "incorrect number of type arguments");
          }
          else {
            t.children.iter().map(|c| self.resolve_abstract_defs(loc, c))
              .collect::<Result<Vec<_>, Error>>()?
          };
          let content = Def(name.clone(), def.unit_id);
          return Ok(Type::new(content, children));
        }
        else {
          return error(loc, format!("type definition '{}' was not found", name));
        }
      }
      _ => t.content.clone(),
    };
    let mut children = vec![];
    for c in t.children() {
      let c = self.resolve_abstract_defs(loc, c)?;
      children.push(c.into())
    }
    Ok(Type::new(content, children))
  }

  fn process_assertion(&mut self, a : &'a Assertion) {
    fn to_resolved(i : &mut Inference, t : &Option<(Type, TextLocation)>) -> Type {
      if let Some((t, loc)) = t.as_ref() {
        match i.resolve_abstract_defs(*loc, t) {
          Ok(t) => return t,
          Err(e) => i.errors.push(e),
        }
      }
      Type::any()
    }
    match a {
      Assertion::Assert(ts, t) => {
        let loc = self.loc(*ts);
        match self.resolve_abstract_defs(loc, t) {
          Ok(t) => {
            self.resolved.insert(*ts, t);
          }
          Err(e) => {
            self.errors.push(e);
          }
        }
      }
      Assertion::AssertTypeDef{ typename, fields } => {
        let mut fs = vec![];
        for f in fields {
          fs.push(to_resolved(self, f));
        }
        let def = self.t.get_type_def_mut(typename);
        for (i, t) in fs.into_iter().enumerate() {
          def.fields[i].1 = t;
        }
      }
    }
  }

  fn process_constraint(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content  {
      Equalivalent(a, b) => {
        if let Some(t) = self.get_type(*a) {
          let t = t.clone();
          self.update_type(*b, &t);
        }
        if let Some(t) = self.get_type(*b) {
          let t = t.clone();
          self.update_type(*a, &t);
        }
      }
      Function{ function, args, return_type } => {
        if let Some(t) = self.get_type(*function) {
          if let Some(mut sig) = t.sig_builder() {
            for (i, t) in sig.args().iter_mut().enumerate() {
              self.update_type_mut(args[i], t);
            }
            let rt = sig.return_type();
            self.update_type_mut(*return_type, rt);
            self.update_type(*function, &sig.into());
          }
        }
        else {
          let any = Type::any();
          let return_type = self.get_type(*return_type).cloned().unwrap_or(any.clone());
          let mut sig = SignatureBuilder::new(return_type.into());
          for &arg in args {
            let arg = self.get_type(arg).cloned().unwrap_or(any.clone());
            sig.append_arg(arg);
          }
          self.update_type(*function, &sig.into());
        }
      }
      Constructor { def_ts, fields } => {
        if let Some(t) = self.resolved.get(def_ts) {
          if let Def(name, unit_id) = &t.content {
            self.dependency_map.register_typedef(name, c);
            let def = self.t.get_type_def(name, *unit_id);
            match def.kind {
              TypeKind::Struct => {
                if fields.len() == def.fields.len() {
                  let it = fields.iter().zip(def.fields.iter());
                  let mut field_types = vec![];
                  for ((arg_name, _), (field_name, field_type)) in it {
                    let mut field_type = field_type.clone();
                    def.instance_type(&mut field_type, t.children.as_slice());
                    field_types.push(field_type.clone());
                    if let Some(arg_name) = arg_name {
                      if arg_name.name != field_name.name {
                        self.errors.push(error_raw(arg_name.loc, "incorrect field name"));
                      }
                    }
                  }
                  for(i, t) in field_types.into_iter().enumerate() {
                    self.update_type(fields[i].1, &t);
                  }
                }
                else{
                  let e = error_raw(self.loc(*def_ts), "incorrect number of field arguments for struct");
                  self.errors.push(e);
                }
              }
              TypeKind::Union => {
                if let [(Some(sym), ts)] = fields.as_slice() {
                  if let Some((_, t)) = def.fields.iter().find(|(n, _)| n.name == sym.name) {
                    let t = t.clone();
                    self.update_type(*ts, &t);
                  }
                  else {
                    self.errors.push(error_raw(sym.loc, "field does not exist in this union"));
                  }
                }
                else {
                  let s = format!("incorrect number of field arguments for union '{}'", def.name);
                  let e = error_raw(self.loc(*def_ts), s);
                  self.errors.push(e);
                }
              }
            }
          }
        }
      }
      Convert { val, into_type_ts } => {
        let t = self.get_type(*val);
        let into = self.get_type(*into_type_ts);
        if let [Some(t), Some(into)] = &[t, into] {
          if t.is_concrete() && into.is_concrete() {
            fn abstract_contains(t : &Type, into_type : &Type) -> bool {
              if let Abstract(abs_t) = &t.content {
                return abs_t.contains_type(into_type);
              }
              false
            }
            let valid =
              abstract_contains(t, into) ||
              (t.pointer() && into.pointer()) ||
              (t.number() && into.number()) ||
              (t.pointer() && into.unsigned_int()) ||
              (t.unsigned_int() && into.pointer());
            if !valid {
              let s = format!("type conversion from {} into {} not supported", t, into);
              self.errors.push(error_raw(self.loc(*val), s));
            }
          }
        }
      }
      // TODO: improve this and make it work again
      // TypeDefField { container, field_index, field_type } => {
      //   if let Some(ctype) = self.resolved.get(container) {
      //     if let Def(name, _) = &ctype.as_type().content {
      //       let def = self.t.get_type_def_mut(name);
      //       if let Some(inferred_type) = self.resolved.get(field_type) {
      //         let t = &mut def.fields[*field_index].1;
      //         let r = incremental_unify_polymorphic(inferred_type, t);
      //         if r.new_type_changed {
      //           // Trigger any constraints looking for this def
      //           if let Some(cs) = self.dependency_map.typedef_map.get(name) {
      //             for &c in cs.values() {
      //               self.next_edge_set.insert(c.id, c);
      //             }
      //           }
      //         }
      //       }
      //     }
      //   }
      // }
      SymbolDef{ symbol_id, type_symbol } => {
        // Use global def to update the type symbol
        let mut t = self.t.get_symbol_mut(*symbol_id).type_tag.clone();
        let def_type_changed = self.update_type_mut(*type_symbol, &mut t);
        // Use the type symbol to update the global def
        if def_type_changed {
          let def = self.t.get_symbol_mut(*symbol_id);
          def.type_tag = t;
          // Trigger any constraints looking for this name
          if let Some(cs) = self.dependency_map.global_map.get(&def.name) {
            for &c in cs.iter() {
              self.next_edge_set.insert(c.id, c);
            }
          }
        }
      }
      GlobalReference { node, name, result } => {
        let any = Type::any();
        let t = self.get_type(*result).cloned().unwrap_or(any);
        match self.t.find_symbol(&name, &t) {
          [rs] => {
            let resolved_type = rs.resolved_type.clone();
            let id = rs.symbol_id;
            self.register_def(*node, id);
            self.update_type(*result, &resolved_type);
          }
          [] => {
            // Global will never be resolved, but if an error is generated
            // here it may be recorded several times.
          }
          _ => (), // Multiple matches. Global can't be resolved yet.
        }
      }
      FieldAccess{ container, field, result } => {
        let container_type = self.resolved.get(container);
        if let Some(ct) = container_type {
          let mut t = ct;
          // Dereference any pointers
          while let Some(inner) = t.ptr() {
            t = inner;
          }
          if let Def(name, unit_id) = &t.content {
            self.dependency_map.register_typedef(name, c);
            let def = self.t.get_type_def(&name, *unit_id);
            let field_type = def.instanced_field_type(&field.name, t.children.as_slice());
            if let Some(t) = field_type {
              self.update_type(*result, &t);
            }
            else {
              let s = format!("type '{}' has no field '{}'", def.name, field.name);
              self.errors.push(error_raw(field.loc, s));
            }
          }
        }
      }
      Array{ array, element } => {
        if let Some(element_type) = self.get_type(*element) {
          let et = element_type.clone();
          self.update_type(*array, &et.array_of());
        }
        else if let Some(array_type) = self.get_type(*array) {
          if let Some(element_type) = array_type.array() {
            let et = element_type.clone();
            self.update_type(*element, &et);
          }
        }
      }
      SizeOf { node, ts } => {
        if let Some(t) = self.get_type(*ts) {
          if t.is_concrete() {
            let t = t.clone().into();
            self.mapping.sizeof_info.insert(*node, t);
          }
        }
      }
    }
  }

  /// Tries to harden a type symbol into a concrete type
  fn try_harden_type_symbol(&mut self, ts : TypeSymbol) {
    if let Some(default) = self.resolved.get(&ts).unwrap().try_harden_literal() {
      self.update_type(ts, &default);
    }
  }

  fn infer(mut self) {
    println!("To resolve: {}", self.c.symbols.len());
    for a in self.c.assertions.iter() {
      self.process_assertion(a);
    }
    for c in self.c.constraints.iter() {
      self.dependency_map.populate_dependency_map(c);
      self.next_edge_set.insert(c.id, c);
    }
    let mut literals = VecDeque::with_capacity(self.c.literals.len());
    for lit in self.c.literals.iter() {
      literals.push_back(*self.c.node_symbols.get(lit).unwrap());
    }
    let mut total_constraints_processed = 0;
    let mut active_edge_set = HashMap::new();
    while (self.next_edge_set.len() > 0 || literals.len() > 0) && self.errors.len() == 0 {
      std::mem::swap(&mut self.next_edge_set, &mut active_edge_set);
      for (_, c) in active_edge_set.drain() {
        total_constraints_processed += 1;
        self.process_constraint(c);
      }
      // If nothing was resolved, try to harden a literal (in lexical order)
      if self.next_edge_set.is_empty() && literals.len() > 0 {
        self.try_harden_type_symbol(literals.pop_back().unwrap());
      }
    }
    println!("Unique constraints: {}\n", self.c.constraints.len());
    println!("Constraints processed (including duplicates): {}\n", total_constraints_processed);

    // Generate errors if program has unresolved symbols
    let mut unresolved = 0;
    active_edge_set.clear();
    if self.errors.is_empty() {
      for (ts, _) in self.c.symbols.iter() {
        if !self.resolved.get(ts).map(|t| t.is_concrete()).unwrap_or(false) {
          unresolved += 1;
          if let Some(cs) = self.dependency_map.ts_map.get(ts) {
            for c in cs { active_edge_set.insert(c.id, c); }
          }
          // Generate errors for unresolved constraints
          let error_count = self.errors.len();
          for (_, c) in active_edge_set.drain() {
            self.unresolved_constraint_error(c);
          }
          if error_count == self.errors.len() {
            self.errors.push(error_raw(self.loc(*ts), "unresolved type"));
          }
        }
      }
    }

    if self.errors.is_empty() && unresolved > 0 {
      panic!("Unresolved types found, but no errors generated!");
    }

    // Assign types to all of the nodes
    if self.errors.is_empty() {
      for (n, ts) in self.c.node_symbols.iter() {
        let t = self.get_type(*ts).unwrap().clone();
        // Make sure the type isn't abstract
        if t.is_concrete() {
          self.mapping.node_type.insert(*n, t);
        }
        else {
          panic!("abstract type but no error");
        }
      }
    }

    // Find polymorphic definitions
    if self.errors.is_empty() {
      for (node_id, symbol_id) in self.mapping.symbol_references.iter() {
        let def = self.t.find_type_info(symbol_id.uid).symbols.get(symbol_id).unwrap().clone();
        if def.is_polymorphic() {
          if let SymbolInit::Function(_) = def.initialiser {
            let t = self.mapping.node_type.get(node_id).unwrap();
            self.mapping.polymorphic_references.insert((*symbol_id, t.clone()));
          }
        }
      }
    }
  }
}

struct ConstraintDependencyMap<'a> {
  global_map : HashMap<RefStr, Vec<&'a Constraint>>,
  typedef_map : HashMap<RefStr, HashMap<Uid, &'a Constraint>>,
  ts_map : HashMap<TypeSymbol, Vec<&'a Constraint>>,
}

impl <'a> ConstraintDependencyMap<'a> {

  fn new() -> Self {
    ConstraintDependencyMap {
      global_map: HashMap::new(),
      typedef_map: HashMap::new(),
      ts_map: HashMap::new() }
  }

  fn ts(&mut self, ts : &TypeSymbol, c : &'a Constraint) {
    self.ts_map.entry(*ts).or_insert(vec![]).push(c);
  }

  fn global(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.global_map.get_mut(name) { cs.push(c); }
    else { self.global_map.insert(name.clone(), vec![c]); }
  }

  fn register_typedef(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.typedef_map.get_mut(name) {
      cs.insert(c.id, c);
    }
    else {
      let mut cs = HashMap::new();
      cs.insert(c.id, c);
      self.typedef_map.insert(name.clone(), cs);
    }
  }

  fn populate_dependency_map(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content {
      Equalivalent(a, b) => {
        self.ts(a, c);
        self.ts(b, c);
      }
      Array{ array, element } => {
        self.ts(array, c);
        self.ts(element, c);
      },
      Convert{ val, into_type_ts } => {
        self.ts(val, c);
        self.ts(into_type_ts, c);
      }
      FieldAccess { container, field:_, result } => {
        self.ts(container, c);
        self.ts(result, c);
      },
      Constructor { def_ts, fields } => {
        self.ts(def_ts, c);
        for (_, ts) in fields { self.ts(ts, c) }
      },
      Function { function, args, return_type } => {
        self.ts(function, c);
        for ts in args { self.ts(ts, c) }
        self.ts(return_type, c);
      },
      SymbolDef { symbol_id:_, type_symbol } => self.ts(type_symbol, c),
      GlobalReference { node:_, name, result } => {
        self.global(name, c);
        self.ts(result, c);
      }
      SizeOf { node:_, ts } => {
        self.ts(ts, c);
      }
    }
  }
}
