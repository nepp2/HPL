# Regions

The goal is that mutation and multi-aliasing can be isolated within regions.

This is intended to achieve the same kind of local reasoning made possible by Rust and immutable languages like Haskell.

## Rust's lifetimes

Rust lifetimes are difficult to manage for a number of reasons:
  - they do not provide a cheap allocation mechanism
  - they do not permit mutable multi-aliasing
  - there is no default, environmental lifetime that can be assumed
  - lifetimes are tied to the stack, rather than to a moveable object

## Verona's cowns

Verona has a concept of concurrent ownership and of memory regions, though I'm not sure whether these are decoupled from one-another.

An abstraction representing concurrent ownership of a resource.

These could, in principle, provide a cheap bump allocator.

# Design proposal - Region type

```code

```

