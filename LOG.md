# LOG - 28/01/2020

I still have a polymorphism bug. I'm wondering if I should have built around a smaller number of constraints, where everything is modelled as a function.

A constructor becomes a function. Field accesses become functions too. e.g.

```rust
struct Point { x : i32, y : i32 }
```

becomes:

```rust
  fun @construct.point(i32, i32) -> Point
  fun @point.x(Point) -> i32
  fun @point.y(Point) -> i32
```

But in order to do this, all modules would have to be searchable in this format. Would all type definitions just disappear?

# LOG - 27/01/2020

Fixed polymorphic structs, as they didn't typecheck properly _or_ codegen properly.

I then ran into the issue that I don't provide an option to differentiate between reference and value semantics in an implicit way. You can explicitly take a pointer to something and then call a function with it, but you can't call a function that implicitly takes certain arguments as pointers.

This a problem for any function that mutates its arguments. For example:

```rust
  fun add(list : list(T), item : T) with T {
    // add an element to a list
  }
```
This signature would work in a language like Java or Python, but in this language the list struct will be passed by value. So it is copied into the function, then modified locally, and the external copy is left unchanged.

Another problem is that, with overloading and implicit referencing, the following two function signatures will clash:

```rust
  fun add(list : list(T), item : T) with T { ... }
  fun add(list : ptr(list(T)), item : T) with T { ... }
```

An alternative syntax that would make this clearer could look like this:

```rust
  fun add(list : list(T), item : T) with T { ... }
  fun add(ref list : list(T), item : T) with T { ... }
```

I'm not sure how this would actually work as a type. It seems like something which possibly only needs to influence code generation... Although the type system has to know when a function pointer's arguments need to be refs or values.

The common modern approach to reference semantics is to make them a fixed characteristic of the type. For example, `class Foo` is always passed around as a pointer, while `struct Bar` is always passed as a value. This works, but it limits the memory model, specifically because a `class` instance can never be stored inline.

Julia divides types based on whether they are immutable or mutable. The compiler is then free to store and pass immutable objects as values or references, but must pass mutable objects as references. Immutable objects are copied when updated, but this can compile down to fast in-place mutation if they are stored inline in a mutable variable or object.

The Rust and C++ style of growable list only works thanks to move semantics. In other languages, a growable list will be allocated as at least two heap objects. This is likely true in Swift.

I think the quickest solution, for now, is to implement the list as a java-style reference type, like an array list. I can decide what to do about this later.

# LOG - 24/01/2020

My current linking strategy doesn't work very well. It might be better to record which symbols need to be linked in the codegen stage, and then handle it afterwards in a linking step.

This could remove the subunit complexity, and pave the way for more fine-grained hotloading later, if modules are separated by function.

It's likely that the type inference still has some bugs, based on the output I got from the full polymorphism example in `scratchpad.code`. For now I have disabled most of the code to get the simplest case working.

# LOG - 23/01/2020

Type checking polymorphic stuff is now proving tricky specifically when polymorphic type tags are used inside the function body. For example, the `ptr(T)` in the example below is a problem:

```rust
fun list() => list(T) with T {
  list.new(0, 0 as ptr(T), 0)
}
```

It's hard to swap the types in the node graph because I currently know the type of the function, but not of the individual type parameters. I might be able to find and retrieve this information somehow. Perhaps I should _not_ convert the names of type parameters into numerical ids?

# LOG - 22/01/2020

I need to typecheck the polymorphic instances. That means they need to refer to node graphs. Do I duplicate nodes, or just repurpose some existing ones? I'm concerned about node id clashes. However, clashes could be fixed by addressing nodes with their unit_id as well.

The old node graphs also slightly incorrect for the instances, because they make references to polymorphic types. There will also need to be some effort made to link the symbol ids together. I may just be able to add special support for type checking polymorphic instances.

# LOG - 20/01/2020

- ~~Stop trying to codegen the polymorphic functions~~
- Typecheck the monomorphised functions
- Codegen the monomorphised functions
- Check that they link

The monomorphised functions can't be generated before their parent modules, because they might refer to other stuff in those modules. So any that are called inside their parent should be generated inside them.

# LOG - 17/01/2020

It could be a goal that hotloaded programs can also compile into static binaries, without any extra effort. This is not the case when modules are loaded with dynamic, runtime code, such as a `load_module` function. This could potentially be fixed by providing a clear distinction between code that runs at compile time and code that runs at runtime.

Ultimately there needs to be some kind of declarative structure to the relationships between modules. However, if we initially support a totally dynamic module loading system, the declarative system can be built on top of it as a library within the language.

I may just be able to use static-style imports already:

- `main` imports (prelude, events, game)
- `events` imports (prelude)
- `game` imports (prelude, events)

Where `events` stores a history of events as global state. This is ugly because it uses global state, and it's not very general; it's hard to see how to build a node graph system based on this, especially if you wanted to have many instances of a node (or node graph) without superfluous code generation.

However, explicit imports are also a desirable feature for usability. This should probably be separated from the idea of hotloading. Instead it is like an assert which changes the visible namespace.

For now, a module should just import whatever it's told to by its parent (recursively). This means modules will need knowledge of their own `UnitId`. These are effectively self references.

I'm trying to create something akin to a synchronous actor, which also provides guarantees about which types it can see. When it is reloaded, every instance would need to be replaced. Any graph processing system would need a graph of compile-time evaluated code modules, as well as a graph of data and events. These modules should be data, then. Code must be very strictly wired together according to the type system. So really it just needs to be possible to query a module's dependencies.

# LOG - 13/01/2020

## A list of requirements for live-edited Tetris

Core:
  - Expressive enough language
    - Finish polymorphism
      - Not strictly required, but painful without
      - Interesting to explore later
      - Introduces a lot of code complexity
  - Can load & replace modules dynamically
    - Maybe just DLL style?

Nice to have:
  - A module hotloading system that is memory safe and preserves soundness
  - Powerful metaprogramming system (for extending the language more easily, in the Lisp style)
  - Proper windows C ABI support
    - Currently just kludging it manually in each type signature, which is both horrififying and effective

Not currently on the list:
  - Memory safety
  - Region system
    - Data structures with isolated heaps
    - Heap-local garbage collection
  - Visual node graph

## Breakdown of core tasks

- Finish polymorphism
  - ~~Typecheck generic functions and structs~~
  - ~~Find set of functions to monomorphise~~
  - Add a new code database that processes a queue to typecheck and codegen modules
  - Typecheck the monomorphised functions
  - Codegen the monomorphised functions
  - _Don't_ try to codegen the polymorphic versions
- Load and replace modules in basic DLL style
  - Load & codegen modules dynamically
    - May work already
  - Retrieve function pointers from loaded modules
    - May work already
  - Fix module unloading if necessary
    - Might not be required. Depends how quickly memory leakage becomes a problem.
- Update old tetris code

## Problem

To typecheck & generate a new implementation of `list` (for example), the type-checking has to happen in the context of the prelude's imports. The current structure of the compiler makes this pretty difficult. Managing imports and references to types & functions has been one of the uglier parts of the compiler for a while now.

I should simplify this somehow. There needs to be some data structure storing all module dependencies. Monomorphised functions could be added as individual modules. But sharing them between different modules will require some special support as well. Type checking and code generation could happen in response to a queue. So a module will queue functions to be monomorphised, and then the consumer will either find an existing implementation or typecheck and codegen a new one.

So I need a code database type thing, in charge of generating code and finding definitions and so-on.

# LOG - 13/01/2020

I was thinking about supporting template-style macros which can be nested within each other to code-generate a module.

Probably the first thing to do is just to make polymorphic code generation work and then go from there. I like the idea that macros should be typed functions. Although it doesn't really make sense because the execution is then in the wrong phase. So really I want compile-time constexpr expansion instead of macros? Should it be memoised? How is purity enforced? Perhaps all functions marked (or inferred) as pure are eligible as macros. But there should be syntax to indicate that an expression is being evaluated into an embedded `expr`. I suppose this comes back to the `$` syntax used for existing macros.

There is a note in the Scopes devblog about compile-time const evaluation being deprecated because it slowed down compilation. I'm not sure that applies to this project as much because live compilation will be supported, and compile-time evaluation isn't being done by an interpreter. However, using a JIT is a big up-front cost.

I'm also not sure whether macro-expansion style code generation should be necessary, given the dynamic code-loading model of the whole language. This is another reason to delay this feature until module loading is properly worked-out.

Is polymorphism really required for simple module loading functionality? Or possibly it's just needed to make tetris in a sensible way.

# LOG - 08/01/2020

The important thing is that the host module imposes a concrete type interface, and the loaded module returns an error if it does not conform to it.

Some syntax is required to express this interface. The interface is a set of symbols with types defined by the host module. This could be retrieved just as a struct; e.g.

```rust
  struct my_interface {
    init : fun() => State
    update : fun(State)
    render : fun(render_view, State)
  }

  let m = load_module("game.code")
  // this function has a polymorphic return type, but it's sort of acting like a typed macro...
  let i : my_interface = m.load_interface()

  let state = i.init()
  i.update(state)
  i.render(render_view, state)
```

The `State` type can't be defined by the child module, even if it was only ever referenced in the parent using a pointer. The problem is that there's nothing really stopping the parent module from holding onto these pointers indefinitely, despite the fact that the State type may change, making old values invalid. So it seems as though it is fundamentally broken to have an interface including any types defined by the loaded module.

So then how do you build tetris in a way that permits live modification of state? I suppose the answer is that the child module holds state, and the parent just passes it events, the types of which the parent can confidently define. The parent may receive module events from the child module handle, indicating that it should be reloaded (or whatever).

Module state should probably be separated from the module's code, so it's not just a bunch of globals.

It also seems that module dependencies should eventually be managed automatically, instead of being managed manually in response to module handles and module events. But this would require a standardised and extremely flexible module graph interface, which I am not yet sure on the design for.

# LOG - 07/01/2020

Think about having some kind of central code database. This would track:
- module origin
  - might be a file path
  - might have been loaded _by_ a particular file
- module source code
- module types
- compiled modules
- dependencies between modules
- monomorphised functions

When is a module invalidated? How is it reloaded? Should this be automatic, or should the database just have some kind of API? What happens if a module tries to unload itself while it is in use?

What if modules can only call their own functions, and are automatically unloaded when their own lexical scope ends?

Alternatively, modules could be introduced to lexical scope by a function call that informs the code database, so it can increment a counter. Then it knows whether they need to be loaded, or whether it needs to crash because they aren't available, or whatever. The problem with this is that it means the outer module actually depends on the inner module, which is not a useful relationship for reloading. What is a useful relationship for reloading?

The key is that we have static types, so we need to specify an interface that the reloadable module conforms to.

e.g.

```rust
  fun hello() {
    println("hello world")
  }

  reload run_stuff(e : Event) {
    hello()
  }
```

# LOG - 06/01/2020

A consistent theme to my many realisations over the past 4 years is that freeform expression in programming languages is important. Having the space to commit acts of great programmatic foolishness is valuable. Whenever we suppose that perhaps we curtail this freedom in some particular way, such as by imposing a limitation on the shape of our data structures, or how we can update them, or what we can do with them, we are incurring a huge cost in usability. And yet, these limitations can provide invaluable properties, such as referential transparency, memory safety, data-race freedom or cache coherence.

I have realised that both of these things can often be achieved as long as the freedom can be bounded in some way. Garbage collection, for example, is great as long as it happens in local heaps, can be controlled, and can be totally bypassed by dropping the heap. Shared mutability is fine as long as you know that no references can escape from the bounded data structure; so from a zoomed out level the graph can be thought of as a single mutable node.

Many of these ideas are realised in the Pony programming language. However, this programming language is designed around the actor model, which involves a system of asynchronous message passing and queues. I'm not sure if synchronous calls are possible between actors. If they are not, the actor model is perhaps more heavyweight than what I need for this project. However, the Pony type system and much of its runtime could surely be adapted for a simpler, synchronous model of programming.

# LOG - 30/12/2019

- Polymorphic type checking code doesn't work yet
  - ~~Stupid problem with the AST's handling of explicit return types.~~
  - ~~The `list` type I created isn't resolved currently, for whatever reason.~~

At the moment, polymorphic functions are not registered correctly. Initially, the simplest rule is to require that all of their type arguments are explicit. They still can't be registered up-front, because they need to wait for all the local type definitions to be resolved first.

- I don't have any solution for generating polymorphic variants yet.
  - Can just make do a lazy bodge job for now. Don't worry about duplication or reloading modules.

# LOG - 18/12/2019

I introduced a lot of changes at once:

- Type definitions are now resolved in the inference stage, for reasons unclear.
- Type definitions may be polymorphic.
- Function bodies may be polymorphic.

These are hard to actually implement because:

- Typedef polytypes are quite different to function polytypes.
  - Their type signature can't be incrementally resolved as a single type. But I could generate constraints for each field.

- I can't overwrite a generic type with something more specific when unifying with the typedef or globaldef. I was doing this before.

- I don't know how to inform a field reference that its type has been updated. A field access constraint has no dependency link to the typedef. This dependency isn't even known until later. They could be linked and triggered using the field string instead. (pretty gross, but oh well).


# LOG - 13/12/2019

There is a huge bug in the way types are resolved. Defs are resolved by looking up their name in the list of supplied modules, but this goes for all the defs in the supplied modules too. Since the modules passed in might reference different modules, this is very broken.

## Solution
1. A def should be an abstract type until it is resolved to a specific typedef id.
  (what about a global reference?)

2. The type directory has access to every single module loaded, so that it can look up all types referenced by the modules it uses.

3. Monotype possibly stays, but just strips generic IDs and replaces them with the Any type

# LOG - 06/12/2019

Implementing polymorphic functions requires:
  - New syntax for declaring their type parameters
  - An AST that can carry this information
  - ???

```rust
  fun alloc[V](v : V) : ptr(V) {
    ...
  }
```

I like the idea of polymorphic functions whose body is generated by a macro that takes the types as input. Instead of macros I could maybe have generalised static evaluation with a directive that can embed static expressions.

Do I actually need polymorphic functions for Tetris? What do I need? I need to be able to load and destroy modules. Destroying a module should mark any module that depends on it as dirty. This is a bit complicated because if you can pass modules as first-class values, you can destroy the module that is in active use. I can just carefully not do that for now.

I also need for loops. Are these hard to implement? It's kind of annoying to do for-loops over array without them. Possible though.

# LOG - 05/12/2019

- ~~Type inference of new symbols should allow their types to be refined incrementally~~
- Prevent unnecessary array allocation
  - Add sized array type to support stack/global allocation?
    - Pass around as an unsized array reference (could break easily)
    - Add region (lifetime?) to the type?
  - Detect constant expressions and allocate them globally
  - Maybe always allocate on the stack (or as global) without putting it in type info?

# LOG - 02/12/2019

I'm contemplating the possible wrongness of regions. Although not that they are very wrong. Just that possibly a slot map would be a better choice. Or some combination of the two.

Requirements:
- confidence that there is no accidental mutable aliasing
- in-place mutations to types
- confidence that different arenas don't contain pointers into each other

# LOG - 01/12/2019

- Declare symbols immediately, but with incomplete types.
- Implement polymorphic functions

# LOG - 30/11/2019

The current problem is that Globals aren't registered without concrete values (because abstract values may no longer be obtained by equivalence). At the moment this global issue only happens due to REPL mode. Maybe REPL globals should just be resolved in lexical scope again. This broke them previously, but I'm sure it could be made to work.

# LOG - 29/11/2019

The old prelude doesn't work fully because build_module can't find the existing modules. I'm not sure what solution is desirable here. The easiest thing is to say that modules are first-class values. You have to pass references to them into `build_module`.

It's not clear how a module would obtain a reference to itself. It could be passed into the top_level function. It could go in via CBind too, but then there will be name conflicts. Or they could use the file-name and the module name (assuming modules are always named).

Okay, it actually makes a lot of sense that there should be a global store of modules. Maybe just in the compiler. The `build_module` function can resume using this for now, but there should eventually be some way of narrowing what a module can see.

## LOG

- ~~Add a global module store~~
- Reintroduce function call/global constraints when new symbols are resolved
- Make sure that the equivalence constraints hang around.
- Implement polymorphic functions

# LOG - 26/11/2019

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

# LOG - 25/11/2019

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

# LOG - 22/11/2019

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

# LOG - 21/11/2019

- Look up type definitions properly in the codegen step
- Fix the type evaluation (needs to retrigger equivalences)

# LOG - 19/11/2019

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

# LOG - 18/11/2019

- Remove overloaded functions (for now). Namespacing is a better idea.
- Consider removing destructors. Replace with memory regions. Consider defer.
- Add syntactic macros. Implement for loops.
- Support generics.

# LOG - 13/11/2019

I don't need generics to support stuff like arithmetic and indexing. I just needed to special-case indexing for pointer types. For everything else, overloaded functions work.

# LOG - 12/11/2019

I went on a big type inference detour. It's close to done, but it is still limited in power due to the unfriendliness of overloading. That is a problem for another day.

Problems for right now are that the codegen doesn't yet use the new node and type structure. In fact it can't yet, because I need to decide how to handle things like arithmetic and indexing. I am trying to code-generate these to functions, but that might be a bit premature. I would need a generics system first, really.

Secondly, I need to decide how to pass information about where to find functions, type defs and globals. This might involve swapping to immutable maps inside the modules.

# LOG - 31/10/2019

Close to finishing a crude Drop and Clone system.

There are two (big) outstanding problems:

1. I don't detect whether an assignment is into a variable or a field/array. I think these are the only times a drop/clone should happen. It's worth noting that it would be very hard to tell what's behind a raw pointer. I could make all assignments do a clone as long as they _aren't_ to a local variable, but then I'd have to prevent people from taking raw pointers to local variables.

2. Drop does not do anything about nested types! To implement this via metaprogramming I'd need some type introspection features.

# LOG - 29/10/2019

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

# LOG - 25/10/2019

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

# LOG - 24/10/2019

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

# LOG - 23/10/2019

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

# LOG - 22/10/2019

## RC pointers

I'm thinking about how to implement reference-counted pointers, and prototyping in the scratchpad.

## Module issues

I realised that my `build_module` function could break Rust's borrowing rules quite badly. It borrows all of the stuff from `Interpreter`, which _might_ already be borrowed for the loading of the parent module. Although since the parent module is actually being run, maybe it's okay?

## For Loops

I had a think about implementing for loops. The plan is to do it without any new codegen code, by transforming the AST to reuse existing features (like while loops). I think it would work fine, but it's slightly irritating to implement, and I'm not sure how to define a generic interface for iteration yet. I could just enforce the use of the range struct.

# LOG - 21/10/2019

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

# LOG - 17/10/2019

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


# LOG - 16/10/2019

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


# LOG - 15/10/2019

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

