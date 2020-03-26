
use std::fmt;

use crate::{common, compiler, error, expr, structure};
use common::*;
use error::{Error, error, error_raw, TextLocation};
use expr::{Expr, ExprContent};
use structure::{
  Node, NodeId, ReferenceId, Content, PrimitiveVal, LabelId,
  VarScope, GlobalType, Reference, Nodes
};
use crate::types::types::{
  Type, PType, TypeDefinition, FunctionInit, SymbolDefinition,
  SymbolInit, SymbolId, AbstractType,
  SignatureBuilder, TypeMapping, TypeContent,
  ResolvedSymbol, TypeInfo,
};
use crate::types::type_errors::TypeErrors;
use compiler::DEBUG_PRINTING_TYPE_INFERENCE as DEBUG;

use std::collections::HashMap;

enum ReferenceType {
  Ref,
  Val,
  Nil,
}

fn reference_type(n : Node) -> ReferenceType {
  use Content::*;
  use ReferenceType::*;
  match &n.content {
    Literal(val) => Val,
    VariableInitialise{ name, type_tag, value, var_scope  } => Nil,
    TypeAlias{ alias, type_aliased } => Nil,
    Assignment{ assignee , value } => Nil,
    IfThen{ condition, then_branch } => Nil,
    IfThenElse{ condition, then_branch, else_branch } => (),
    Block(node) => (),
    Quote(expr) => Val,
    Reference { name, refers_to } => Ref,
    FunctionDefinition{ name, args, return_tag, type_vars, body } => (),
    CBind { name, type_tag } => Nil,
    TypeDefinition{ name, kind, fields, type_vars } => Nil,
    TypeConstructor{ name, field_values } => Val,
    FieldAccess{ container, field } => Ref,
    ArrayLiteral(elements) => Val,
    FunctionCall{ function, args } => (),
    While{ condition, body } => Nil,
    Convert{ from_value, into_type } => Val,
    SizeOf{ type_tag } => Val,
    Label{ label, body } => (),
    BreakToLabel{ label, return_value } => (),
  }
}
