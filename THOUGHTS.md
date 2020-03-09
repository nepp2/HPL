
# Design - March 2020

There are two language features I need to add at some point, and they should complement each other very neatly. These are:

- A runtime `Type` type, allowing the fields of structs to be queried.
- Some kind of inline macro expansion

I think that, in combination with polymorphism, this can be used to implement features like auto-derived functions for equality, hash, etc. And potentially this can also be used to support tracing garbage collection.

```rust
  fun print(a : T) with T {
    $(
      let t = type(T)
      let b = block_expr()
      for f in t.field_names {
        b.push(#(println(a.$f)))
      }
      b
    )
  }
```


# Design - the smallest possible core language?

It is expensive to implement compiler features. Ideally, as much of the language would be self-bootstrapped as possible, in the style of Lisp.

But what is the smallest set of core language features required to do this?

## Language primitives

- bool, i64, i32, u64, u32, u16 and u8
- pointers
- arrays
- tuples

What is the type of a type? That needs to be an extensible system, and every type needs to be a runtime value.

```rust
  struct Type {
    name : String
    primitive_shape : Primitive
  }
```

## Primitive operations

def symbol = expression
run expression

macro(expr, expr, expr) -> expr

def struct = macro(name : expr, fields : array(expr)) {
  def(name)
}

## Structs

How would you implement structs? A struct is a tuple of values, where each index has a name. What cases need to be handled?

- Initialise the struct
- Dereference a field
- Typecheck the struct

```rust
  struct blah {
    x : i64
    y : i32
  }
  let b = blah.new(50, 60)
  b.x = 5

  // the above could desugar into

  def blah = env {
    def field::x = 0 : usize
    def field::y = 1 : usize
    def shape = tuple(i64, i32) : prim
  }

  let b = (50, 60) : blah::shape
  b[blah::field::x] = 5

  // and unions...
  union bleh {
    x : i64
    b : blah
  }
  let b = bleh.new(x: 50)
  b.x = 5

  // could desugar into

  def bleh = env {
    def variant::x = i64 : prim
    def variant::y = blah // how does this work?
    def shape =
      if field::x.size() > field::y.size()
        { field::x } else { field::y }
  }

  let b = zero() : bleh::shape
  *(&b as ptr(bleh::variant::x)) = 50 : bleh::variant::x
  *(&b as ptr(bleh::variant::x)) = 5

```

This is a little complicated, because the `def`s are constant values that must be evaluated before the rest of the file can be type-checked. The `env` construct creates a new namespace, which is returned as a constant. I'm not sure what can happen inside there.


# Other thoughts

## 1

All defs are constant and evaluated separately. Types are defs that match a particular interface?

## 2

How can a language have an extensible type system? How does Terra do it? Terra might be a red herring, because it can rely on the highly-dynamic features of Lua. Though it would still be illuminating to know. And using a base of dynamism could be valid. Are there any languages which statically compile to dynamic semantics? I presume C# can.

Types would be extensible if they are represented as S-Expressions. They might also be slower. Is this strictly worse than just using *dynamic objects*? (Basically supporting symbol dictionaries). I suppose this could be the `any` type.

## 4

What is the smallest core of my current language?

- Numbers, bools, pointers, strings
- If, While, For, Break, Return
- Structs, Unions
- Arrays
- Functions
- Polymorphic functions
- Polymorphic structs

What could be replaced, and how?

- For
  - Could be implemented in terms of While, or an even simpler `loop` primitive
  - Only if there is some kind of *syntactic macro system* and *extensible syntax*
- Unions
  - These are just a group of auto-generated structs with tags on the front
- Structs
  - Could perhaps be replaced with *tuples*
  - With *named tuples*
  - With a combination of *names* and *tuples*?
    - e.g. Name("Point", Tuple(Name("x", I64), Name("y", U32)))
- Polymorphic functions
  - A polymorphic function can't be monomorphised until type information is available. In the Scopes model all functions are polymorphic and type information is always passed forwards. Function evaluation is like a memoized macro call which returns a reference to the monomorphised, callable function.
  - Polymorphism has special support partly for the sake of type inference. So if it was implemented as an extension, would type inference have to be as well?

The problem with making a language out of crazy scheme-style macros is that compile times might be quite high. Particularly because all these macros are being JIT-compiled, in my case.

# Vague V1 plan

Statically typed language. Dynamic types not really needed.

Safe most of the time. Support unsafe junk too.

Reference-counted pointers. How do I implement them?
 * Default synax (e.g. `[1, 2, 3]`) allocates a dynamically-sized, reference-counted array.

How do I implement `drop` functions for reference-counted pointers? (and other resources)
 * Function overloading would work

Do I need function overloading?
 * This would make implementing `drop` functions much neater
 * Overloading means that the ABI is going to be ugly. But who cares about ABI? I'm not trying to replace C.

Do I need to support generics/templates out of the box?
 * The pointer and array types are built in. Reference-counted pointers aren't, so that's maybe a problem.
 * Seems like probably not, for V1.

Support binding C functions properly

Support loading modules somehow (like they are DLLs?)

Support metaprogramming?
