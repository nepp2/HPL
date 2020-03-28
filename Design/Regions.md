# Regions

The goal is that mutation and multi-aliasing can be isolated within regions.

This is intended to achieve the same kind of local reasoning made possible by Rust and immutable languages like Haskell.

## Rust's lifetimes

Rust lifetimes are difficult to manage for a number of reasons:
  - they do not provide a cheap allocation mechanism
  - they do not permit mutable multi-aliasing
  - there is no default, environmental lifetime that can be assumed
  - lifetimes are tied to the stack, rather than to a moveable object

## MLKit region-based memory

In MLKit, programs have a stack of regions which grows and shrinks according to lexical scope, and then the compiler can attempt to determine which region each value should be allocated in using lifetime/escape analysis. In practise, it is not possible to infer a finite lifetime for every value in any arbitrary ML program, and so many allocations are allocated in the global region and cannot be collected. These accrue as permanent space leaks, until the process terminates.

These space leaks can be prevented by using a different garbage collection scheme to manage the global scope, such as a tracing or reference-counting collector. They could also be averted through some form of manual, checked annotation, but it might be challenging to model every allocation in terms of lexical regions. In particular, an object which persists for some unknown quanitity of cycles in a gameloop does not seem simple to model this way.

Regions could abandon the lexical stack structure and instead be owned by an object, which acts as the sole entry-point to the data structure allocated within the region. This object can then either be dropped, or shrunk via tracing garbage-collection, without any difficulty in identifying the GC roots (there is only one).

## Verona's cowns

Verona has a concept of concurrent ownership and of memory regions, though I'm not sure whether these are decoupled from one-another.

An abstraction representing concurrent ownership of a resource.

These could, in principle, provide a cheap bump allocator.

# Design proposal - Region type

How do regions interact with one-another? How is data copied between them? Can references from one region exist inside another? How would garbage collection work, in that case?

Every module can declare some external regions. It doesn't know who is calling it, but it knows what regions exist and what their relationships are. For example:

```rust
  region ext;

  fun write(ref(ext) f : file, data : array(u8)) {
    
  }
```

