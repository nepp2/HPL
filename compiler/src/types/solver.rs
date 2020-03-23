
/// This type inference algorithm works by building a set of constraints and then
/// incrementally unifying them. At the moment the error reporting for incorrect
/// programs is nondeterministic due to iteration over Rust's secure, randomised
/// HashMaps. This should be fixed at some point so that the most useful error
/// messages are reliably shown to users.

use itertools::Itertools;

use crate::{common, error, structure, code_store, compiler};
use crate::types::{types, constraints, slots, type_graph, type_errors};

use common::*;
use error::{Error, error, error_raw, TextLocation, ErrorContent};
use structure::{
  NodeId, TypeKind, Nodes,
};

use types::{
  Type, PType, TypeContent, TypeInfo, SymbolId,
  TypeMapping, AbstractType, SymbolInit,
};
use constraints::{
  Constraint, ConstraintContent,
  Constraints, TypeSlot, Assertion,
  TypeDirectory,
};
use slots::Slots;
use type_graph::TypeGraph;
use type_errors::TypeErrors;
use code_store::CodeStore;
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;

use std::collections::{HashMap, VecDeque};

use TypeContent::*;

pub fn typecheck_module(
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
  let mut errors = TypeErrors::new();
  let mut type_directory =
    TypeDirectory::new(imports, unit_id, &mut code_store.types);
  let nodes = code_store.nodes.get(&unit_id).unwrap();
  let c =
    constraints::get_module_constraints(
      &nodes, &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, &mut type_directory,
    &mut mapping, &c);
  i.infer(&mut errors);
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
  let mut errors = TypeErrors::new();
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
    constraints::get_polymorphic_function_instance_constraints(
      &nodes, source_node, instance_type.clone(), instanced_type_vars.as_slice(),
      &mut type_directory, &mut mapping, cache, gen, &mut errors);
  let i = Inference::new(
    &nodes, &mut type_directory,
    &mut mapping, &c);
  i.infer(&mut errors);
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
}

impl <'a> Inference<'a> {

  fn new(
    nodes : &'a Nodes,
    t : &'a mut TypeDirectory<'a>,
    mapping : &'a mut TypeMapping,
    c : &'a Constraints)
      -> Self
  {
    Inference { nodes, t, mapping, c }
  }

  fn unresolved_constraint_error(&mut self, errors : &mut TypeErrors, slots : &mut Slots, c : &Constraint) {
    if errors.failed_constraint_ids.contains(&c.id) {
      return;
    }
    errors.failed_constraint_ids.insert(c.id);
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
        let t = slots.get_or_any(*result);
        let symbols : Vec<_> = self.t.find_symbol(&name, t).iter().cloned().collect();
        let s = symbols.iter().map(|rs| {
          let def = self.t.get_symbol(rs.id);
          format!("      {} : {}", def.name, rs.resolved_type)
        }).join("\n");
        error_raw(self.c.loc(*result),
          format!("Reference '{}' of type '{}' not resolved\n   Symbols available:\n{}", name, t, s))
      }
      FieldAccess{ container:_, field, result:_ } => {
        error_raw(field.loc,
          format!("field access '{}' not resolved", field.name))
      }
      TypeParameter{ parent, parameter } => {
        let a = slots.get_or_any(*parent);
        let b = slots.get_or_any(*parameter);
        error_raw(self.c.loc(*parent), format!("type parameter not resolved - {}, {}", a, b))
      }
      SizeOf { node:_, slot } => {
        error_raw(self.c.loc(*slot), "sizeof type not resolved")
      }
    };
    errors.push(e);
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

  fn process_assertion(
    &mut self,
    slots : &mut Slots,
    g : &mut TypeGraph,
    errors : &mut TypeErrors,
    a : &'a Assertion
  ) {
    fn to_resolved(i : &mut Inference, errors : &mut TypeErrors, t : &Option<(Type, TextLocation)>) -> Type {
      if let Some((t, loc)) = t.as_ref() {
        match i.resolve_abstract_defs(*loc, t) {
          Ok(t) => return t,
          Err(e) => errors.push(e),
        }
      }
      Type::any()
    }
    match a {
      Assertion::Assert(slot, t) => {
        let loc = self.c.loc(*slot);
        match self.resolve_abstract_defs(loc, t) {
          Ok(t) => {
            slots.update_type(g, errors, *slot, &t);
          }
          Err(e) => {
            errors.push(e);
          }
        }
      }
      Assertion::AssertTypeDef{ typename, fields } => {
        let mut fs = vec![];
        for f in fields {
          fs.push(to_resolved(self, errors, f));
        }
        let def = self.t.get_type_def_mut(typename);
        for (i, t) in fs.into_iter().enumerate() {
          def.fields[i].1 = t;
        }
      }
    }
  }

  fn process_constraint(
    &mut self,
    slots : &mut Slots<'a>,
    g : &mut TypeGraph<'a>,
    errors : &mut TypeErrors,
    c : &'a Constraint)
  {
    use ConstraintContent::*;
    match &c.content  {
      Equalivalent(a, b) =>
        force_equivalence(slots, g, errors, *a, *b),
      Branch{ output, cases } => {
        if let Some(t) = slots.get(*output) {
          if t.content == TypeContent::Prim(PType::Void) {
            return;
          }
          if t.is_concrete() {
            for slot in cases {
              force_equivalence(slots, g, errors, *output, *slot);
            }
            return;
          }
        }
        // Check if the branch types are all known, and none are void
        for slot in cases {
          if let Some(t) = slots.get(*slot) {
            if t.content == TypeContent::Prim(PType::Void) {
              // One of the branches is void, so the output is void
              let t = t.clone();
              slots.update_type(g, errors, *output, &t);
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
          force_equivalence(slots, g, errors, *output, *slot);
        }
      }
      Function{ function, args, return_type } => {
        if let Some(t) = slots.get(*function) {
          if let Some(mut sig) = t.sig_builder() {
            if sig.args().len() == args.len() {
              for (i, t) in sig.args().iter_mut().enumerate() {
                slots.update_type_mut(g, errors, args[i], t);
              }
              let rt = sig.return_type();
              slots.update_type_mut(g, errors, *return_type, rt);
              slots.update_type(g, errors, *function, &sig.into());
            }
          }
        }
      }
      Constructor { def_slot, fields } => {
        if let Some(t) = slots.get(*def_slot) {
          if let Def(name, unit_id) = &t.content {
            g.register_typedef(name, c);
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
                        errors.push(error_raw(arg_name.loc, "incorrect field name"));
                      }
                    }
                  }
                  for(i, t) in field_types.into_iter().enumerate() {
                    slots.update_type(g, errors, fields[i].1, &t);
                  }
                }
                else{
                  let e = error_raw(self.c.loc(*def_slot), "incorrect number of field arguments for struct");
                  errors.push(e);
                }
              }
              TypeKind::Union => {
                if let [(Some(sym), slot)] = fields.as_slice() {
                  if let Some((_, t)) = def.fields.iter().find(|(n, _)| n.name == sym.name) {
                    let t = t.clone();
                    slots.update_type(g, errors, *slot, &t);
                  }
                  else {
                    errors.push(error_raw(sym.loc, "field does not exist in this union"));
                  }
                }
                else {
                  let s = format!("incorrect number of field arguments for union '{}'", def.name);
                  let e = error_raw(self.c.loc(*def_slot), s);
                  errors.push(e);
                }
              }
            }
          }
        }
      }
      Convert { val, into_type_slot } => {
        let t = slots.get(*val);
        let into = slots.get(*into_type_slot);
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
              errors.push(error_raw(self.c.loc(*val), s));
            }
          }
        }
      }
      SymbolDef{ symbol_id, slot } => {
        // Use symbol def to update the type symbol
        let mut t = self.t.get_symbol_mut(*symbol_id).type_tag.clone();
        let def_type_changed = slots.update_type_mut(g, errors, *slot, &mut t);
        // Use the type symbol to update the symbol def
        if def_type_changed {
          let def = self.t.get_symbol_mut(*symbol_id);
          def.type_tag = t;
          g.symbol_updated(def);
        }
      }
      SymbolReference { node, name, result } => {
        let t = slots.get_or_any(*result);
        match self.t.find_symbol(&name, t) {
          [resolved_symbol] => {
            let resolved_type = resolved_symbol.resolved_type.clone();
            let id = resolved_symbol.id;
            self.register_def(*node, id);
            slots.update_type(g, errors, *result, &resolved_type);
          }
          [] => {
            // Symbol will never be resolved. Report error, because at the moment it's the only guaranteed
            // way to catch symbols that don't exist (their type might still be resolved).
            // TODO: This is a bit too subtle for comfort, and should possibly be made clearer later.
            self.unresolved_constraint_error(errors, slots, c);
          }
          syms => {
            // Multiple matches. Global can't be resolved yet, but it can be narrowed where all of the possibilities agree.
            let mut t = types::type_intersection(&syms[0].resolved_type, &syms[1].resolved_type);
            for sym in &syms[2..] {
              t = types::type_intersection(&t, &sym.resolved_type);
            }
            slots.update_type(g, errors, *result, &t);
          }
        }
      }
      FieldAccess{ container, field, result } => {
        let container_type = slots.get(*container);
        if let Some(ct) = container_type {
          let mut t = ct;
          // Dereference any pointers
          while let Some(inner) = t.ptr() {
            t = inner;
          }
          if let Def(name, unit_id) = &t.content {
            g.register_typedef(name, c);
            let def = self.t.get_type_def(&name, *unit_id);
            let field_type = def.instanced_field_type(&field.name, t.children.as_slice());
            if let Some(t) = field_type {
              slots.update_type(g, errors, *result, &t);
            }
            else {
              let s = format!("type '{}' has no field '{}'", def.name, field.name);
              errors.push(error_raw(field.loc, s));
            }
          }
        }
      }
      TypeParameter{ parent, parameter } => {
        if let Some(parameter_type) = slots.get(*parameter) {
          let mut new_parent_type = slots.get(*parent).cloned().unwrap_or(Type::any());
          new_parent_type.children.clear();
          new_parent_type.children.push(parameter_type.clone());
          slots.update_type(g, errors, *parent, &new_parent_type);
        }
        if let Some(parent_type) = slots.get(*parent) {
          if let [param] = parent_type.children() {
            let new_param = param.clone();
            slots.update_type(g, errors, *parameter, &new_param);
          }
        }
      }
      SizeOf { node, slot } => {
        if let Some(t) = slots.get(*slot) {
          if t.is_concrete() {
            let t = t.clone().into();
            self.mapping.sizeof_info.insert(*node, t);
          }
        }
      }
    }
  }

  /// Tries to harden a type slot into a concrete type
  fn try_harden_slot(
    &mut self,
    slots : &mut Slots,
    g : &mut TypeGraph,
    errors : &mut TypeErrors,
    slot : TypeSlot)
  {
    if let Some(default) = slots.get(slot).unwrap().try_harden_literal() {
      slots.update_type(g, errors, slot, &default);
    }
  }

  fn infer(mut self, errors : &mut TypeErrors) {
    if DEBUG {
      println!("To resolve: {}", self.c.slots.len());
    }
    let mut slots = Slots::new(self.c);
    let mut g = TypeGraph::new(self.c);
    let mut literals = VecDeque::with_capacity(self.c.literals.len());
    for lit in self.c.literals.iter() {
      literals.push_back(*self.c.node_slots.get(lit).unwrap());
    }
    for a in self.c.assertions.iter() {
      self.process_assertion(&mut slots, &mut g, errors, a);
    }
    let mut total_constrainslot_processed = 0;
    let mut active_edge_set = HashMap::new();
    let mut next_edge_set = HashMap::new();
    for c in self.c.constraints.iter() {
      next_edge_set.insert(c.id, c);
    }
    while (next_edge_set.len() > 0 || literals.len() > 0) && errors.is_empty() {
      std::mem::swap(&mut next_edge_set, &mut active_edge_set);
      for (_, c) in active_edge_set.drain() {
        total_constrainslot_processed += 1;
        self.process_constraint(&mut slots, &mut g, errors, c);
      }
      g.find_boundary_constraints(&mut next_edge_set);
      // If nothing was resolved, try to harden a literal (in lexical order)
      if next_edge_set.is_empty() && literals.len() > 0 {
        self.try_harden_slot(&mut slots, &mut g, errors, literals.pop_front().unwrap());
      }
      g.find_boundary_constraints(&mut next_edge_set);
    }
    if DEBUG {
      println!("Unique constraints: {}\n", self.c.constraints.len());
      println!("Constraints processed (including duplicates): {}\n", total_constrainslot_processed);
    }

    // Look for errors
    if errors.is_empty() {
      // Generate errors if program has unresolved type slots
      active_edge_set.clear();
      slots.find_all_unresolved_constraints(&g, &mut active_edge_set);
      // Generate errors for unresolved constraints
      let unresolved_count = active_edge_set.len();
      for (_, c) in active_edge_set.drain() {
        self.unresolved_constraint_error(errors, &mut slots, c);
      }
      // Generate errors if program has unresolved symbols
      for c in self.c.constraints.iter() {
        if let ConstraintContent::SymbolReference{node, ..} = &c.content {
          if !self.mapping.symbol_references.contains_key(node) {
            self.unresolved_constraint_error(errors, &mut slots, c);
          }
        }
      }
      if errors.is_empty() && unresolved_count > 0 {
        panic!("Unresolved types found, but no errors generated!");
      }
    }

    // Assign types to all of the nodes
    if errors.is_empty() {
      for (n, slot) in self.c.node_slots.iter() {
        let t = slots.get(*slot).unwrap().clone();
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
    if errors.is_empty() {
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
    if !errors.is_empty() {
      errors.concrete_errors.sort_unstable_by_key(|e| e.location);
    }
  }
}

fn force_equivalence(
  slots : &mut Slots,
  g : &mut TypeGraph,
  errors : &mut TypeErrors,
  a : TypeSlot, b : TypeSlot)
{
  if let Some(t) = slots.get(a) {
    let t = t.clone();
    slots.update_type(g, errors, b, &t);
  }
  if let Some(t) = slots.get(b) {
    let t = t.clone();
    slots.update_type(g, errors, a, &t);
  }
}
