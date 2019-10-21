# TODO - 21/10/2019

There is some kind of bug in my quote templating tests. However, the bug might actually be in the mapping between the `Expr` type in my Rust code and the `expr` type in the scripting language.

I could try making a more minimal example to surface this problem.

Okay, it looks like the problem is that my structs are not actually compatible with C structs, because they pay no attention to alignment. I was expecting this, but had forgotten about it. I'm not exactly sure what rules C follows on alignment, and how they change depending on the platform (it forms part of the ABI compatibility issue).

```rust
  struct Blah {
    a : i8,
    b : i64,
  }
```

I get the bug when I represent the union tag as a `u8`, but it works fine if I change the representation to a `u64`. I'm not sure why this is, as everything I've read suggests that llvm should not treat `{ i8, i64 }` as a packed struct. The C examples I've tried on Godbolt don't seem to. However, I did find a Rust example in which padding was generated. I'm still unclear on exactly what triggered this.


# THOUGHTS - 17/10/2019

I never really solved the "create_module" function issue. Instead I just decided that, for now, the host module can unsafely retrieve function pointers from module handlers. Then it just casts them to whatever type it expects them to be and tries to call it. A better long term solution probably involves a way of asserting the return type that is dynamically checked. I suppose it could return a dynamic type which undergoes a checked cast to the expected type, if those two things are supported at some point.

## Quote templating

I'm adding a `$` operator intended to facilitate the creation of quotes.

I need a `symbol` function too. Then the `$` operator can always expect expressions.

  ```rust
    let a = #5
    let b = #10
    
    let e = #($a + $b)

    // `e` should now contain the expression #(5 + 10)
  ```

So how does this work? Every time the code runs it has to build a new expression. So I need functions for doing this. The easiest way is just to clone the existing expressions recursively, until I hit a `$`. At this point I have to somehow substitute in the correct value, corresponding to an expression which should already have been evaluated.

  ```rust
    let a = #5
    let b = #10
    
    // This is what could be generated
    let e = {
      clone_expr(#($a + $b), [a, b])
    }
  ```


# THOUGHTS - 16/10/2019

I'm considering whether the REPL model is really a good idea. If the language behaves differently in different places, is it even powerful enough to build the kind of module system I'm talking about? It can maybe be done at the top level, but then I can't abstract over any of it? Can I make similar
functionality work in functions somehow?

If the system requires fresh type information and code-generation between each line, the answer is no. Isn't it? Unsure, but code-generation seems like the problem that won't be easily avoided.

## Types as values option

```rust

  let mb = module_builder()

  declare_global(#v, i64, '3)

  declare_function(mb, #example, [(a, i64), (b, foo)], #{ a + b })

  declare_struct(#array, [(length, i64), (data, ptr(u8))])

  let b = mb.build()

  // not sure how to then use this

```

## With the current semantics (types aren't values, modules are compiled as a unit)

```rust

  // Brings new module into scope
  module {
    global v = 3

    fun example(a : i64, b : foo) {
      a + b
    }

    struct array {
      length : i64
      data : ptr(u8)
    }
  }

  module {
    example(v, 4)
  }

  // This is equivalent to the module block above
  create_module( #(example(v, 4)) )

  // the modules are all deallocated at the end of the scope

```

This seems very promising. But there are some questions to be answered:

  1. How would you use this to handle generic types like RC?
  2. How do I pass values into the modules?
  3. How do I specify which other modules they can see?

```rust

  fun rc(t : expr) {
    create_module(#{
      struct rc_inner {
        count : i64
        the_rest : \t
      }

      struct rc {
        data : ptr(rc_inner)
      }

      rc
    })
  }

  module rc(t : type) {
    struct rc_inner {
      count : i64
      the_rest : #t
    }

    struct rc {
      data : ptr(rc_inner)
    }

    rc
  }

```

## A New Problem

The "create_module" function doesn't work so well because it can't return type information.

A special language construct could return type information, but then it wouldn't be able to use runtime values to influence the code generation of the new module. This is because you wouldn't know what type the new module will return until actually running the code, after typechecking had already happened.

Instead it could just do a checked cast to a particular return type (or something equivalent). Functions could potentially be accessed as though from a DLL. But that wouldn't work if they used types internal to the module.


# THOUGHTS - 15/10/2019

In general I prefer a value-based approach, because it seems like a cleaner way to make use of the heap and the full power of the language.

The issue with a value-based approach is that it requires some kind of REPL functionality. This is because the workflow for a normal language is that you parse the whole file, then typecheck it, then code-generate it, then evaluate it. Since the values only arrive at the end, a value returned from line 1 cannot affect the typecheck or code generation phases of line 2.

The simplest default is to evaluate each expression in the top level block as if entered into a REPL. In theory most of these expressions can be discarded once the block is evaluated. We only need to keep the function definitions and any proper globals.

A slight optimisation on this is to group together lines that don't affect each other. So a chain of function/struct definitions can all be code-generated together, which will also allow circular references to be resolved.

When the top-level has been evaluated, the important modules can be merged and the rest can be discarded. This is pretty stupid and expensive, but oh well. One day it can use a real interpreter I guess.

# Values

So with a value-based approach, how do I represent types and functions? How do I link them?

In Terra, a function (for example) is a special object in Lua. It is likely just an an id. It can be inspected, but it can also be called (via the dynamism of lua). When it is referenced from a Terra function it is transformed into a simple function pointer and linked.

```rust

  // `type` is represented as a u64, and can be declared as a struct in the prelude
  let foo : type = i64

  // This adds a function to the module and code-generates it
  declare_function(#example, [(a, i64), (b, foo)], #{ a + b })

  // This line cannot be type-checked and compiled until the previous line has fully executed
  let e = example(4, 5)

  // this is syntactic sugar for `declare_function`
  fun example(a : i64, b : foo) { a + b }

  // This adds a struct to the module
  declare_struct(#array, [(length, i64), (data, ptr(u8))])
  
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

There are two different understandings of first-class functions. A function object in the terra sense is something that can be inspected, linked, called, etc. In the classic sense, a first-class-function is just a function pointer or a closure.

One way to unify them is to store the function pointer in the function object, and have the compiler look for an overload function called something like "invoke". This would return a function pointer of the appropriate type, which could then be called.

# Generics

???

