# THOUGHTS - 29/11/2019

The old prelude doesn't work fully because build_module can't find the existing modules. I'm not sure what solution is desirable here. The easiest thing is to say that modules are first-class values. You have to pass references to them into `build_module`.

It's not clear how a module would obtain a reference to itself. It could be passed into the top_level function. It could go in via CBind too, but then there will be name conflicts. Or they could use the file-name and the module name (assuming modules are always named).

Okay, it actually makes a lot of sense that there should be a global store of modules. Maybe just in the compiler. The `build_module` function can resume using this for now, but there should eventually be some way of narrowing what a module can see.

## TODO

- Add a global module store
- Reintroduce function call/global constraints when new symbols are resolved
- Make sure that the equivalence constraints hang around.
- Implement polymorphic functions

# THOUGHTS - 26/11/2019

Resolving function types is complicated if the function is both polymorphic and overloaded. But all polymorphic functions are overloaded, right? This is not really true from the perspective of symbol resolution. You resolve repeatedly against the polymorphic symbol instead of the specialisations, because the important detail is the particular function body that you dispatch on.

A potential resolution rule is: try to resolve on monomorphic functions first. If you find nothing, then try the polymorphic ones.

In both cases it should be possible to resolve using incomplete types.

## Yesterday's hack

I realised there is a potential ordering problem with resolution, if functions are able to shadow each other:

```Rust
  fun blah(a : float, b : float) { ... }
  fun blah(a : float, b : float) { ... }
  blah(3, 4)
```

Which blah is called? It may depend on which order they happen to be resolved in. If one of them is from a previous module, it will likely win. However, it seems that a new blah should really shadow the old one. If we just wait for all new blah symbols to be resolved, we can end up with a tangle:

```Rust
  fun blah(a : float, b : float) { ... }

  // --- new module ---

  fun blah(a : float) {
    bloo(a)
  }
  fun bloo(a : float) {
    blah(a, 5)
  }
```

This will never terminate, even though the desired behaviour is obvious. If we resolve it naively it works, but then the shadowing example will resolve incorrectly. Another way to fix it is just to never drop constraints. Keep iterating on everything, and only stop once nothing is happening.

Finally, I could fix it by re-introducing function call constraints where relevant.

## A list of stuff to fix

- ~~Get rid of the checks on unresolved symbols~~
- ~~Merge all symbols into one kind~~
- ~~Do overload matches on return types too, using the "unknown" Type~~
- Reintroduce function call/global constraints when new symbols are resolved
- ~~Turn index operations into function calls properly~~
- Make sure that the equivalence constraints hang around.

# THOUGHTS - 25/11/2019

Hopelessly stuck again, trying to figure out how to handle function resolution in the presence of both overloading and two-way type inference. I had the idea that I could detect when all of the information is available and then just choose the single matching implementation if there is one, or return an error otherwise. But that is complicated to implement in practise, and has become a bit of a mess with globals and generics. Consider the following:

```Rust
  fun blah(a : float, b : float) {
    blah(a as int, b as int)
  }

  fun blah(a : int, b : int) {
    a + b
  }
```

This is hard to resolve because I deliberately wait for all overloads of a function name to be defined before resolving any function calls to them. So here, `blah` can never resolve itself because it calls an overload with its own name. This could be fixed with a return type annotation, but that is kind of weird. This is why most languages dispatch on the first argument, which works pretty well for method chaining.

Another problem I'm having is in resolving globals. Globals exist in the same namespace as functions, and a global variable might hold a reference to a function. So the exact same syntax works for function calls and for global variables references. So I should possibly unify the type resolution mechanism, but that's tricky because I want to evaluate globals eagerly when they clearly aren't functions, but in the presence of overloading they can't be evaluated eagerly.

```Rust
  fun blah(a : float) { }

  static blah = 5

  let a = blah

  a(6)
```

The code above is ambiguous until `a` is used. Then the correct `blah` can be inferred. But then blah has to be inferred from a type.

## Possible Solution

The language lets you define whatever symbol you want, but complains if you try to call something that's ambiguous. It then has two mechanisms for disambiguating in relevant cases; you can either manually specify the namespace (when namespaces are supported), or you can call a function with method-call syntax. This tells the type checker to try and resolve overloads. It also applies to the language's operators.

The first advantage is that global resolution is now always simple. The second is that type inference will work much better for normal functions. It still doesn't really fix the general complexity of overloads, and I'm not sure whether it should dispatch on more than the type of the first argument. It could also dispatch on the number of arguments, possibly.

# THOUGHTS - 22/11/2019

This arena type allows the storage of persistant regions alongside pointers into the region. It currently does not provide compile-time safety. Instead it makes a best-effort at runtime safety with slightly expensive dereferencing checks (which should be optimised out in release builds). However, it might be possible to provide compile-time safety with a carefully-designed interface. Specifically, arenas contain top-level types which can only be accessed by passing closures into an access function.

```Rust
  pub impl <T> Arena<T> {
    pub fn access(&self, Fn(&Allocator, &mut T)) {
      ...
    }
  }
```

Arena pointers can only be obtained inside this closure (which receives the arena allocator as an argument). However, the closure would likely need to capture some external data to do anything interesting. If this external data is immutable I think the interface would be safe, but that might be a painful restriction. To lift this restriction the type system would need to somehow guarantee that no arena pointers can escape from the closure.

```Rust
  let mut v = vec![];
  arena.access(|allocator, t| {
    let x : Ap<i64> = allocator.alloc(5);
    v.push(x); // uh oh
  })
```

The arena pointers should also not be allowed to store anything that must be dropped. Or it must detect them and store a reference in a drop list to be dropped when the arena is freed (although this will not be much faster than using an Rc pointer would have been.) I'm not sure if Rust's type system can express these things.

This simple interface would allow the user to build and store tree structures of regions, but it would not easily
allow them to build graphs of regions. A better interface could probably do that though.

# TODO - 21/11/2019

- Look up type definitions properly in the codegen step
- Fix the type evaluation (needs to retrigger equivalences)

# TODO - 19/11/2019

Currently types and modules are stored together in one big blob. They have to be because otherwise a Type could end up with two different TypeIds, and that would break Type comparisons.

```Rust
  #[derive(Clone)]
  pub struct Types {
    types : BiMap<TypeId, Type>,

    signatures : BiMap<SigId, FunctionSignature>,

    type_definition_names : BiMap<DefId, RefStr>,
  }
```

It is critical that the mapping `TypeId -> Type` should be one-to-one. However, when obtaining fresh TypeIds there's no way to avoid the possibility of creating a many-to-one mapping by accident, except by keeping a global store of all existing TypeIds.

Module A: ptr(u32) -> id x
Module B: ptr(u32) -> id y
Module C depends on A and B: if ptr(u32) uses x, it will not match signatures containing y (for example).

One solution is to use an arena and replace all the ids with pointers.

# TODO - 18/11/2019

- Remove overloaded functions (for now). Namespacing is a better idea.
- Consider removing destructors. Replace with memory regions. Consider defer.
- Add syntactic macros. Implement for loops.
- Support generics.

# THOUGHTS - 13/11/2019

I don't need generics to support stuff like arithmetic and indexing. I just needed to special-case indexing for pointer types. For everything else, overloaded functions work.

# THOUGHTS - 12/11/2019

I went on a big type inference detour. It's close to done, but it is still limited in power due to the unfriendliness of overloading. That is a problem for another day.

Problems for right now are that the codegen doesn't yet use the new node and type structure. In fact it can't yet, because I need to decide how to handle things like arithmetic and indexing. I am trying to code-generate these to functions, but that might be a bit premature. I would need a generics system first, really.

Secondly, I need to decide how to pass information about where to find functions, type defs and globals. This might involve swapping to immutable maps inside the modules.

# THOUGHTS - 31/10/2019

Close to finishing a crude Drop and Clone system.

There are two (big) outstanding problems:

1. I don't detect whether an assignment is into a variable or a field/array. I think these are the only times a drop/clone should happen. It's worth noting that it would be very hard to tell what's behind a raw pointer. I could make all assignments do a clone as long as they _aren't_ to a local variable, but then I'd have to prevent people from taking raw pointers to local variables.

2. Drop does not do anything about nested types! To implement this via metaprogramming I'd need some type introspection features.

# THOUGHTS - 29/10/2019

## RC pointers, arrays and strings

Instead of figuring out how to make a proper system of generics, at the moment I'm just emulating it by generating new names for types, and generating overloaded functions. It's pretty ugly and won't scale well, but it seems to work as a first-pass. To make RC pointers actually work, I still need to make the auto-Drop/Clone function system work.

The array creation code also relies on the built-in array type, which is currently used by array literals. This is fairly stupid because it is heap-allocated, so there are two heap allocations every time an array is initialised!

I will eventually want to turn strings into rc u8 arrays. This will require some special support in the codegen for string literals, which may be tricky to get right in a forward-compatible way. The best option may be to call some literal constructor function, which may then be defined in the prelude. However, it's important that the string data should only be allocated once (probably as a global).

## Errors

I need to provide good error messages for metaprogramming, so I need a proper error system in the language. It should generate errors that are indistinguishable from those generated by the rust code. However, initially I can provide a panic function which just calls Rust's panic with a string, as a stopgap solution.

I could implement exceptions, or aim for a slightly more automated version of the Rust error system.

```rust
  fun can_fail(a : i64) : error(string) {
    if a < 3 {
      "cool"
    }
    else {
      error("fuck")
    }
  }

  let s = can_fail(2)?
```

# THOUGHTS - 25/10/2019

What would I need to implement everything internally?
What would I want the code that does it to look like?

Decide whether to pursue this:

``` Rust
  #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
  pub struct TypeId { module_id : u64, type_id : u64 }

  pub struct TypeDirectory {
    types : HashMap<TypeId, ComplexType>
  }

  impl TypeDirectory {

    fn display(&self, t : &Type, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match t {
        Type::ComplexType(id) =>
          self.display_complex(self.types.get(id).unwrap(), f),
        t => write!(f, "{:?}", t),
      }
    }

    fn display_complex(&self, t : &ComplexType, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match t {
        ComplexType::Fun(sig) => {
          write!(f, "fun({}) => {}",
            sig.args.iter().map(|t| self.displayable(t)).join(", "),
            self.displayable(&sig.return_type))
        }
        ComplexType::Def{name, params} =>
          write!(f, "{}({})", name,
            params.iter().map(|t| self.displayable(t)).join(", ")),
        ComplexType::Array(t) => write!(f, "array({})", self.displayable(t)),
        ComplexType::Ptr(t) => write!(f, "ptr({})", self.displayable(t)),
      }
    }

    fn displayable<'l>(&'l self, t : &'l Type) -> DisplayableType<'l> {
      DisplayableType { t, d: self }
    }
  }

  struct DisplayableType<'l> {
    t : TypeId,
    d : &'l TypeDirectory,
  }

  impl <'l> fmt::Display for DisplayableType<'l> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      self.d.display(self.t, f)
    }
  }
```

# THOUGHTS - 24/10/2019

## On reference counting

What if reference counting ONLY happens in response to block ends, function returns and field assignments?

```rust
  a.v = thing // (a.v.Drop(); a.v = thing.Move())
  thing() // if the type is move, log the BasicValue with the block
  v // if returned from a block and the type is move, call move
  } // upon exiting the block, Drop all of the BasicValues logged so far (in reverse order? or does it matter?)
```

I think this works. It's kind of ugly, but oh well. I'm not sure how to optimise away the `Clone` and `Drop` reliably when returning something. Will I be able to compare BasicValue references? It's actually not just an optimisation, but absolutely essential for a resource that isn't just a refcount.

It's also unclear how dereferencing an RC pointer should work.

## Special-case reference counting?

I could also implement reference counting as a special language feature, which then hooks into the Drop calls. If a type needs to be dropped properly, then it uses reference-counted pointers? This could introduce too much codegen machinery specific to a particular feature, however.

## On arrays and unsized types

I should provide a language-level type for inline vectors. The size of the vector should be included in the type, and if left unspecified the vector should be considered "dynamically sized", which means it must be heap allocated and managed using unsafe code. A dynamically-sized vector can sit at the end of a struct, and can be used to implement runtime-managed types like heap-allocated arrays and RC pointers.

I'm not sure if vector is the right name. Or whether this is two different concepts which shouldn't be conflated.

## On module hotloading and type safety

I plan to allow hotloaded modules to safely return values by checking that the return type is understood by the host module. This is a bit tricky because modules are generated dynamically so their return type changes. This means that the host must assert the return type it expects, and an error is returned if the newly generated module doesn't return the type expected.

```rust
  module m : i64 {
    5
  }
  m.value
```

Modules also need to be able to receive information from their host. There could be syntax for that, like:

```rust
  let a = some_value()
  module(a) : i64 {
    a.v + 4
  }
```

But then how do I specify which other modules a module can see? Perhaps a better syntax would just be variable capture |_and_ module capture, like:

```rust
  module {
    fun blah(a : i32, b : i32) { a + b }
  }
  let a = some_value()
  module m : i64 {
    blah(a.v, 4)
  }
```

The module `m` captures the variable `a` and also now depends on the module containing `blah`.

# THOUGHTS - 23/10/2019

I am very bad at explaining the point of this project, on any kind of vaguely detailed technical level. Internally I have been thinking of the language and compiler as an alternative to Terra and Extempore which aims to unify the high-performance language and the metaprogramming language. But I suspect this explanation would mostly result in blank stares.

## Function duplication issue

I realised that I need to consider a very simple but also very important optimisation for generic functions. For example, the Drop function for a reference-counted pointer should be shared. However, other functions might not be shared, because they could dispatch differently on an overloaded function.

This is maybe not much of a pressing issue.

## The fastest way forward

I am stuck worrying about the best way to enable a user-friendly way to make widespread use of reference-counted pointers. If I instead take my lead from HPC#, I don't really need to. All I need is reference-counted containers, like arrays.

## Rules for Move and Drop

They need to be inserted in various places:

1. When exiting a block (either at a break, return or just the last statement)
  - Call Drop on all variables now out of scope (except for function parameters)
2. When a value is assigned
  - Call Drop on the current value
  - Call Move on the new value
3. When a value is passed into a constructor
4. On returning a value from a function
5. On any value that is returned from a function without being assigned?

I've gotten lost on this. This is basically the same as Constructors and Destructors in C++, with the addition of either Move or Clone. Or both? Really I'm suggesting that the function should detect whether something is used once, twice or not at all. In that case it should be built into the type system, really. Any struct can be either Copy or Move. This property must be inferred based on its contents. If it is Move, it must be cloned and dropped appropriately. Any variable referring to a move type, then, must carry information about whether it has been moved.

This is actually pretty difficult, because I have to handle situations like this:

```rust
  let r = some_resource()
  if cond {
    consume(r)
  }
  // is r consumed?
```

If one branch of an if statement consumes a Move value, then the other one must as well, even if the other branch doesn't explicitly exist. Can I just choose the hamfisted option instead? I detect if something is Move, and then I just call functions everywhere to make sure it gets shepherded around correctly. I remember implementing a system this way in the past.

# THOUGHTS - 22/10/2019

## RC pointers

I'm thinking about how to implement reference-counted pointers, and prototyping in the scratchpad.

## Module issues

I realised that my `build_module` function could break Rust's borrowing rules quite badly. It borrows all of the stuff from `Interpreter`, which _might_ already be borrowed for the loading of the parent module. Although since the parent module is actually being run, maybe it's okay?

## For Loops

I had a think about implementing for loops. The plan is to do it without any new codegen code, by transforming the AST to reuse existing features (like while loops). I think it would work fine, but it's slightly irritating to implement, and I'm not sure how to define a generic interface for iteration yet. I could just enforce the use of the range struct.

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

## Maybe solved

The problem seems to be the way that Rust handles C representations of its enums (when they are acting as tagged unions). This is described here: https://rust-lang.github.io/rfcs/2195-really-tagged-unions.html

The short version is that an enum declared with `repr(u8)` is represented as a bunch of structs which each have their own tag field, and live together in a union. I'm not sure if any other variation currently works. I read that `repr(C, u8)` was planned to work differently, but I'm not sure if it's actually implemented.

Anyway, I got the tests to pass.

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

