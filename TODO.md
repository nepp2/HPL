
# THOUGHTS

In general I prefer a value-based approach, because it seems like a cleaner way to make use
of the heap and the full power of the language.

The issue with a value-based approach is that it requires some kind of REPL functionality. This
is because the workflow for a normal language is that you parse the whole file, then
typecheck it, then code-generate it, then evaluate it. Since the values only arrive at the end,
a value returned from line 1 cannot affect the typecheck or code generation phases of line 2.

The simplest default is to evaluate each expression in the top level block as if entered into a
REPL. In theory most of these expressions can be discarded once the block is evaluated. We only
need to keep the function definitions and any proper globals.

A slight optimisation on this is to group together lines that don't affect each other. So a
chain of function/struct definitions can all be code-generated together, which will also allow
circular references to be resolved.

When the top-level has been evaluated, the important modules can be merged and the rest can be
discarded. This is pretty stupid and expensive, but oh well. One day it can use a real interpreter
I guess.

# Values

So with a value-based approach, how do I represent types and functions? How do I link them?

In Terra, a function (for example) is a special object in Lua. It is likely just an an id.
It can be inspected, but it can also be called (via the dynamism of lua). When it is referenced
from a Terra function it is transformed into a simple function pointer and linked.

```rust

  // `type` is represented as a u64, and can be declared as a struct in the prelude
  let foo : type = i64

  // This adds a function to the module and code-generates it
  declare_function('example, [(a, i64), (b, foo)], '{ a + b })

  // This line cannot be type-checked and compiled until the previous line has fully executed
  let e = example(4, 5)

  // this is syntactic sugar for `declare_function`
  fun example(a : i64, b : foo) { a + b }

  // This adds a struct to the module
  declare_struct('array, [(length, i64), (data, ptr(u8))])
  
  // this is syntactic sugar for `declare_struct`
  struct array {
    length : i64
    data : ptr(u8)
  }

```

Question: how do functions handle recursion? What about mutual recursion?

# Types

All types are values. They are stored as (module, id) combos, and can be looked up in a central directory.

# Functions

There are two different understandings of first-class functions. A function object in the terra sense is
something that can be inspected, linked, called, etc. In the classic sense, a first-class-function is just
a function pointer or a closure.

One way to unify them is to store the function pointer in the function object, and have the compiler 
look for an overload function called something like "invoke". This would return a function pointer of
the appropriate type, which could then be called.

# Generics

???

