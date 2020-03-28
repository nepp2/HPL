
// TODO: REMOVE THIS
#![allow(dead_code)]

use crate::{common, structure};
use common::*;
use structure::{Node, Content};

/*

We have to know whether function types are being

*/

enum ReferenceType {
  Ref, // indicates that the type can be treated as a reference
  Val, // indicates that the type _must_ be treated as a value
}

use ReferenceType::*;

fn merge(a : ReferenceType, b : ReferenceType) -> ReferenceType {
  match (a, b) {
    (Ref, Ref) => Ref,
    _ => Val, // any combination of ref and val just becomes a val
  }
}

fn reference_type(n : Node) -> ReferenceType {
  use Content::*;
  match &n.content {
    Literal(_val) => Val,
    VariableInitialise{ name:_, type_tag:_, value:_, var_scope:_ } => Val,
    TypeAlias{ alias:_, type_aliased:_ } => Val,
    Assignment{ assignee :_, value:_ } => {
      // check that assignee is a ref
      Val
    },
    IfThen{ condition:_, then_branch:_ } => Val,
    IfThenElse{ condition:_, then_branch:_, else_branch:_ } => {
      panic!()
    }
    Block(_node) => {
      panic!()
    }
    Quote(_expr) => Val,
    Reference { name:_, refers_to:_ } => Ref,
    FunctionDefinition{ name:_, args:_, return_tag:_, type_vars:_, body:_ } => {
      panic!()
    }
    CBind { name:_, type_tag:_ } => Val,
    TypeDefinition{ name:_, kind:_, fields:_, type_vars:_ } => Val,
    TypeConstructor{ name:_, field_values:_ } => Val,
    FieldAccess{ container:_, field:_ } => Ref,
    ArrayLiteral(_elements) => Val,
    FunctionCall{ function:_, args:_ } => {
      // get the function type
      // check that any "ref" arguments are receiving a ref
      panic!()
    }
    While{ condition:_, body:_ } => Val,
    Convert{ from_value:_, into_type:_ } => Val,
    SizeOf{ type_tag:_ } => Val,
    Label{ label:_, body:_ } => {
      panic!()
    }
    BreakToLabel{ label:_, return_value:_ } => {
      panic!()
    },
  }
}
