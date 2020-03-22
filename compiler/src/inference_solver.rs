
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment the error reporting for incorrect
/// programs is nondeterministic due to iteration over Rust's secure, randomised
/// HashMaps. This should be fixed at some point so that the most useful error
/// messages are reliably shown to users.

use itertools::Itertools;

use crate::{common, error, structure, types, inference_constraints, code_store, compiler};

use common::*;
use error::{Error, error, error_raw, TextLocation, ErrorContent};
use structure::{
  NodeId, TypeKind, Nodes,
};
use types::{
  Type, PType, TypeContent, TypeInfo, SymbolId, incremental_unify,
  TypeMapping, UnifyResult, AbstractType, SymbolInit,
};
use inference_constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSlot, Assertion,
  Errors, TypeDirectory,
};
use code_store::CodeStore;
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;

use std::collections::{HashMap, VecDeque};

use TypeContent::*;

pub fn infer_types(
  unit_id : UnitId,
  code_store : &mut CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
  imports : Vec<UnitId>,
)
  -> Result<(), Error>
{
  code_store.types.insert(unit_id, TypeInfo::new(unit_id));
  let mut mapping = TypeMapping::new();
  let mut errors = Errors::new();
  let mut type_directory =
    TypeDirectory::new(imports, unit_id, &mut code_store.types);
  let nodes = code_store.nodes.get(&unit_id).unwrap();
  let c =
    inference_constraints::get_module_constraints(
      &nodes, &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, &mut type_directory,
    &mut mapping, &c, &mut errors);
  i.infer();
  if !errors.is_empty() {    
    let c = ErrorContent::InnerErrors("type errors".into(), errors.concrete_errors);
    return error(nodes.root().loc, c);
  }
  code_store.type_mappings.insert(unit_id, mapping);
  Ok(())
}

pub fn typecheck_polymorphic_function_instance(
  instance_unit : UnitId,
  poly_function_id : SymbolId,
  instance_type : &Type,
  code_store : &mut CodeStore,
  cache : &StringCache,
  gen : &mut UIDGenerator,
)
  -> Result<SymbolId, Error>
{
  code_store.types.insert(instance_unit, TypeInfo::new(instance_unit));
  let mut mapping = TypeMapping::new();
  let mut errors = Errors::new();
  let imports : Vec<_> = code_store.get_imports(instance_unit).cloned().collect();
  let instanced_type_vars =
    code_store.symbol_def(poly_function_id).instanced_type_vars(instance_type);
  let mut type_directory =
    TypeDirectory::new(imports, instance_unit, &mut code_store.types);
  let nodes = code_store.nodes.get(&poly_function_id.uid).unwrap();
  let source_node =
    *code_store.type_mappings.get(&poly_function_id.uid).unwrap()
    .symbol_def_nodes.get(&poly_function_id).unwrap();
  let (c, symbol_id) =
    inference_constraints::get_polymorphic_function_instance_constraints(
      &nodes, source_node, instance_type.clone(), instanced_type_vars.as_slice(),
      &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, &mut type_directory,
    &mut mapping, &c, &mut errors);
  i.infer();
  if !errors.is_empty() {
    let c = ErrorContent::InnerErrors("type errors".into(), errors.concrete_errors);
    return error(nodes.root().loc, c);
  }
  code_store.type_mappings.insert(instance_unit, mapping);
  Ok(symbol_id)
}

struct Inference<'a> {
  nodes : &'a Nodes,
  t : &'a mut TypeDirectory<'a>,
  mapping : &'a mut TypeMapping,
  c : &'a Constraints,
  errors : &'a mut Errors,
  dependency_map : ConstraintDependencyMap<'a>,
  next_edge_set : HashMap<Uid, &'a Constraint>,
  resolved : HashMap<TypeSlot, Type>,
}

impl <'a> Inference<'a> {

  fn new(
    nodes : &'a Nodes,
    t : &'a mut TypeDirectory<'a>,
    mapping : &'a mut TypeMapping,
    c : &'a Constraints,
    errors : &'a mut Errors)
      -> Self
  {
    Inference {
      nodes, t, mapping, c, errors,
      dependency_map: ConstraintDependencyMap::new(),
      next_edge_set: HashMap::new(),
      resolved: HashMap::new(),
    }
  }

  fn get_type(&self, slot : TypeSlot) -> Option<&Type> {
    self.resolved.get(&slot)
  }

  fn type_updated(&mut self, slot : TypeSlot) {
    if let Some(cs) = self.dependency_map.ts_map.get(&slot) {
      for &c in cs.iter() {
        self.next_edge_set.insert(c.id, c);
      }
    }
  }

  fn update_type(&mut self, slot : TypeSlot, t : &Type) -> UnifyResult {
    let ts_type = if let Some(t) = self.resolved.get_mut(&slot) {
      t
    }
    else {
      self.resolved.entry(slot).or_insert(Type::any())
    };
    let r = incremental_unify(t, ts_type);
    if !r.unify_success {
      let s = format!("conflicting types inferred; {} and {}.", t, ts_type);
      let e = error_raw(self.loc(slot), s);
      self.errors.push(e);
    }
    if r.mutable_type_changed {
      self.type_updated(slot);
    }
    r
  }

  /// returns true if the input type `t` was mutated
  fn update_type_mut(&mut self, slot : TypeSlot, t : &mut Type) -> bool {
    let r = self.update_type(slot, t);
    if r.immutable_type_changed && r.unify_success {
      let r = incremental_unify(self.resolved.get(&slot).unwrap(), t);
      if !r.unify_success { panic!("unification is not commutable!") }
      true
    }
    else {
      false
    }
  }

  fn loc(&self, slot : TypeSlot) -> TextLocation {
    *self.c.slots.get(&slot).unwrap()
  }

  fn unresolved_constraint_error(&mut self, c : &Constraint) {
    if self.errors.failed_constraint_ids.contains(&c.id) {
      return;
    }
    self.errors.failed_constraint_ids.insert(c.id);
    use ConstraintContent::*;
    let e = match &c.content  {
      Equalivalent(_a, _b) => return,
      Branch{ output:_, cases:_ } => return,
      // this error should always be accompanied by other unresolved constraints
      Function{ function:_, args:_, return_type:_ } => return,
      Constructor { def_slot:_ , fields:_ } => return,
      Convert { val:_, into_type_slot:_ } => return,
      SymbolDef { symbol_id, slot:_ } => {
        let def = self.t.get_symbol_mut(*symbol_id);
        let node_id = *self.mapping.symbol_def_nodes.get(symbol_id).unwrap();
        let loc = self.nodes.node(node_id).loc;
        error_raw(loc,
          format!("Symbol definition '{}' not resolved. Inferred type {}.", def.name, def.type_tag))
      }
      SymbolReference { node:_, name, result } => {
        let any = Type::any();
        let t = self.resolved.get(result).unwrap_or(&any);
        let symbols : Vec<_> = self.t.find_symbol(&name, t).iter().cloned().collect();
        let s = symbols.iter().map(|rs| {
          let def = self.t.get_symbol(rs.id);
          format!("      {} : {}", def.name, rs.resolved_type)
        }).join("\n");
        error_raw(self.loc(*result),
          format!("Reference '{}' of type '{}' not resolved\n   Symbols available:\n{}", name, t, s))
      }
      FieldAccess{ container:_, field, result:_ } => {
        error_raw(field.loc,
          format!("field access '{}' not resolved", field.name))
      }
      TypeParameter{ parent, parameter } => {
        let any = Type::any();
        let a = self.resolved.get(parent).unwrap_or(&any);
        let b = self.resolved.get(parameter).unwrap_or(&any);
        error_raw(self.loc(*parent), format!("type parameter not resolved - {}, {}", a, b))
      }
      SizeOf { node:_, slot } => {
        error_raw(self.loc(*slot), "sizeof type not resolved")
      }
    };
    self.errors.push(e);
  }

  fn register_def(&mut self, node : NodeId, symbol_id : SymbolId) {
    self.mapping.symbol_references.insert(node, symbol_id);
  }

  /// Recursively copies, turning all `Abstract(Def)` types into resolved `Def` types,
  /// or throwing an error if no `Def` is found.
  fn resolve_abstract_defs<'l>(&self, loc : TextLocation, t : &'l Type)
    -> Result<Type, Error> 
  {
    let content = match &t.content {
      Abstract(AbstractType::Def(name)) => {
        if let Some(def) = self.t.find_type_def(name) {
          let len = t.children().len();
          if !(len == def.type_vars.len() || len == 0) {
            return error(loc, "incorrect number of type arguments");
          }
          let mut children = vec![];
          for i in 0..def.type_vars.len() {
            let c = match t.children.get(i) {
              Some(c) => self.resolve_abstract_defs(loc, c)?,
              None => Type::any(),
            };
            children.push(c);
          }
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
      Assertion::Assert(slot, t) => {
        let loc = self.loc(*slot);
        match self.resolve_abstract_defs(loc, t) {
          Ok(t) => {
            self.resolved.insert(*slot, t);
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

  fn force_equivalence(&mut self, a : TypeSlot, b : TypeSlot) {
    if let Some(t) = self.get_type(a) {
      let t = t.clone();
      self.update_type(b, &t);
    }
    if let Some(t) = self.get_type(b) {
      let t = t.clone();
      self.update_type(a, &t);
    }
  }

  fn process_constraint(&mut self, c : &'a Constraint) {
    use ConstraintContent::*;
    match &c.content  {
      Equalivalent(a, b) =>
        self.force_equivalence(*a, *b),
      Branch{ output, cases } => {
        if let Some(t) = self.get_type(*output) {
          if t.content == TypeContent::Prim(PType::Void) {
            return;
          }
          if t.is_concrete() {
            for slot in cases {
              self.force_equivalence(*output, *slot);
            }
            return;
          }
        }
        // Check if the branch types are all known, and none are void
        for slot in cases {
          if let Some(t) = self.get_type(*slot) {
            if t.content == TypeContent::Prim(PType::Void) {
              // One of the branches is void, so the output is void
              let t = t.clone();
              self.update_type(*output, &t);
              return;
            }
            if t.is_concrete() {
              continue;
            }
          }
          // This type isn't known/concrete yet, so cannot assert the output type
          return;
        }
        // The branch types are all known. Unify each one with the output.
        for slot in cases {
          self.force_equivalence(*output, *slot);
        }
      }
      Function{ function, args, return_type } => {
        if let Some(t) = self.get_type(*function) {
          if let Some(mut sig) = t.sig_builder() {
            if sig.args().len() == args.len() {
              for (i, t) in sig.args().iter_mut().enumerate() {
                self.update_type_mut(args[i], t);
              }
              let rt = sig.return_type();
              self.update_type_mut(*return_type, rt);
              self.update_type(*function, &sig.into());
            }
          }
        }
      }
      Constructor { def_slot, fields } => {
        if let Some(t) = self.resolved.get(def_slot) {
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
                  let e = error_raw(self.loc(*def_slot), "incorrect number of field arguments for struct");
                  self.errors.push(e);
                }
              }
              TypeKind::Union => {
                if let [(Some(sym), slot)] = fields.as_slice() {
                  if let Some((_, t)) = def.fields.iter().find(|(n, _)| n.name == sym.name) {
                    let t = t.clone();
                    self.update_type(*slot, &t);
                  }
                  else {
                    self.errors.push(error_raw(sym.loc, "field does not exist in this union"));
                  }
                }
                else {
                  let s = format!("incorrect number of field arguments for union '{}'", def.name);
                  let e = error_raw(self.loc(*def_slot), s);
                  self.errors.push(e);
                }
              }
            }
          }
        }
      }
      Convert { val, into_type_slot } => {
        let t = self.get_type(*val);
        let into = self.get_type(*into_type_slot);
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
      SymbolDef{ symbol_id, slot } => {
        // Use symbol def to update the type symbol
        let mut t = self.t.get_symbol_mut(*symbol_id).type_tag.clone();
        let def_type_changed = self.update_type_mut(*slot, &mut t);
        // Use the type symbol to update the symbol def
        if def_type_changed {
          let def = self.t.get_symbol_mut(*symbol_id);
          def.type_tag = t;
          // Trigger any constraints looking for this name
          if let Some(cs) = self.dependency_map.symbol_map.get(&def.name) {
            for &c in cs.iter() {
              self.next_edge_set.insert(c.id, c);
            }
          }
        }
      }
      SymbolReference { node, name, result } => {
        let any = Type::any();
        let t = self.get_type(*result).cloned().unwrap_or(any);
        match self.t.find_symbol(&name, &t) {
          [resolved_symbol] => {
            let resolved_type = resolved_symbol.resolved_type.clone();
            let id = resolved_symbol.id;
            self.register_def(*node, id);
            self.update_type(*result, &resolved_type);
          }
          [] => {
            // Symbol will never be resolved. Report error, because at the moment it's the only guaranteed
            // way to catch symbols that don't exist (their type might still be resolved).
            // TODO: This is a bit too subtle for comfort, and should possibly be made clearer later.
            self.unresolved_constraint_error(c);
          }
          syms => {
            // Multiple matches. Global can't be resolved yet, but it can be narrowed where all of the possibilities agree.
            let mut t = types::type_intersection(&syms[0].resolved_type, &syms[1].resolved_type);
            for sym in &syms[2..] {
              t = types::type_intersection(&t, &sym.resolved_type);
            }
            self.update_type(*result, &t);
          }
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
      TypeParameter{ parent, parameter } => {
        if let Some(parameter_type) = self.get_type(*parameter) {
          let mut new_parent_type = self.get_type(*parent).cloned().unwrap_or(Type::any());
          new_parent_type.children.clear();
          new_parent_type.children.push(parameter_type.clone());
          self.update_type(*parent, &new_parent_type);
        }
        if let Some(parent_type) = self.get_type(*parent) {
          if let [param] = parent_type.children() {
            let new_param = param.clone();
            self.update_type(*parameter, &new_param);
          }
        }
      }
      SizeOf { node, slot } => {
        if let Some(t) = self.get_type(*slot) {
          if t.is_concrete() {
            let t = t.clone().into();
            self.mapping.sizeof_info.insert(*node, t);
          }
        }
      }
    }
  }

  /// Tries to harden a type slot into a concrete type
  fn try_harden_slot(&mut self, slot : TypeSlot) {
    if let Some(default) = self.resolved.get(&slot).unwrap().try_harden_literal() {
      self.update_type(slot, &default);
    }
  }

  fn infer(mut self) {
    if DEBUG {
      println!("To resolve: {}", self.c.slots.len());
    }
    for a in self.c.assertions.iter() {
      self.process_assertion(a);
    }
    for c in self.c.constraints.iter() {
      self.dependency_map.populate_dependency_map(c);
      self.next_edge_set.insert(c.id, c);
    }
    let mut literals = VecDeque::with_capacity(self.c.literals.len());
    for lit in self.c.literals.iter() {
      literals.push_back(*self.c.node_slots.get(lit).unwrap());
    }
    let mut total_constraints_processed = 0;
    let mut active_edge_set = HashMap::new();
    while (self.next_edge_set.len() > 0 || literals.len() > 0) && self.errors.is_empty() {
      std::mem::swap(&mut self.next_edge_set, &mut active_edge_set);
      for (_, c) in active_edge_set.drain() {
        total_constraints_processed += 1;
        self.process_constraint(c);
      }
      // If nothing was resolved, try to harden a literal (in lexical order)
      if self.next_edge_set.is_empty() && literals.len() > 0 {
        self.try_harden_slot(literals.pop_front().unwrap());
      }
    }
    if DEBUG {
      println!("Unique constraints: {}\n", self.c.constraints.len());
      println!("Constraints processed (including duplicates): {}\n", total_constraints_processed);
    }

    // Look for errors
    if self.errors.is_empty() {
      // Generate errors if program has unresolved type slots
      let mut unresolved = 0;
      active_edge_set.clear();
      for (slot, _) in self.c.slots.iter() {
        if !self.resolved.get(slot).map(|t| t.is_concrete()).unwrap_or(false) {
          unresolved += 1;
          if let Some(cs) = self.dependency_map.ts_map.get(slot) {
            for c in cs { active_edge_set.insert(c.id, c); }
          }
          // Generate errors for unresolved constraints
          let error_count = self.errors.concrete_errors.len();
          for (_, c) in active_edge_set.drain() {
            self.unresolved_constraint_error(c);
          }
          if error_count == self.errors.concrete_errors.len() {
            self.errors.push(error_raw(self.loc(*slot), "unresolved type"));
          }
        }
      }
      if self.errors.is_empty() && unresolved > 0 {
        panic!("Unresolved types found, but no errors generated!");
      }
  
      // Generate errors if program has unresolved symbols
      for c in self.c.constraints.iter() {
        if let ConstraintContent::SymbolReference{node, ..} = &c.content {
          if !self.mapping.symbol_references.contains_key(node) {
            self.unresolved_constraint_error(c);
          }
        }
      }
    }

    // Assign types to all of the nodes
    if self.errors.is_empty() {
      for (n, slot) in self.c.node_slots.iter() {
        let t = self.get_type(*slot).unwrap().clone();
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
        let def = self.t.get_symbol(*symbol_id);
        if def.is_polymorphic() {
          if let SymbolInit::Function(_) = def.initialiser {
            let t = self.mapping.node_type.get(node_id).unwrap();
            self.mapping.polymorphic_references.insert((*symbol_id, t.clone()));
          }
        }
      }
    }

    // Sort any errors lexically
    if !self.errors.is_empty() {
      self.errors.concrete_errors.sort_unstable_by_key(|e| e.location);
    }
  }
}

struct ConstraintDependencyMap<'a> {
  symbol_map : HashMap<RefStr, Vec<&'a Constraint>>,
  typedef_map : HashMap<RefStr, HashMap<Uid, &'a Constraint>>,
  ts_map : HashMap<TypeSlot, Vec<&'a Constraint>>,
}

impl <'a> ConstraintDependencyMap<'a> {

  fn new() -> Self {
    ConstraintDependencyMap {
      symbol_map: HashMap::new(),
      typedef_map: HashMap::new(),
      ts_map: HashMap::new() }
  }

  fn slot(&mut self, slot : &TypeSlot, c : &'a Constraint) {
    self.ts_map.entry(*slot).or_insert(vec![]).push(c);
  }

  fn symbol(&mut self, name : &RefStr, c : &'a Constraint) {
    if let Some(cs) = self.symbol_map.get_mut(name) { cs.push(c); }
    else { self.symbol_map.insert(name.clone(), vec![c]); }
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
        self.slot(a, c);
        self.slot(b, c);
      }
      Branch{ output, cases } => {
        self.slot(output, c);
        for slot in cases {
          self.slot(slot, c);
        }
      }
      TypeParameter{ parent, parameter } => {
        self.slot(parent, c);
        self.slot(parameter, c);
      },
      Convert{ val, into_type_slot } => {
        self.slot(val, c);
        self.slot(into_type_slot, c);
      }
      FieldAccess { container, field:_, result } => {
        self.slot(container, c);
        self.slot(result, c);
      },
      Constructor { def_slot, fields } => {
        self.slot(def_slot, c);
        for (_, slot) in fields { self.slot(slot, c) }
      },
      Function { function, args, return_type } => {
        self.slot(function, c);
        for slot in args { self.slot(slot, c) }
        self.slot(return_type, c);
      },
      SymbolDef { symbol_id:_, slot } => self.slot(slot, c),
      SymbolReference { node:_, name, result } => {
        self.symbol(name, c);
        self.slot(result, c);
      }
      SizeOf { node:_, slot } => {
        self.slot(slot, c);
      }
    }
  }
}
