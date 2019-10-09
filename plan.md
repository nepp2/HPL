
# Plan

## Problems
* Need to be able to define, for example, a `Drop` function for lots of different types.
  * Introduced function overloading based arg types
* I introduced overloading, but the code generation makes stupid assumptions about the names of functions. This means that they will clash for overloaded functions.
  * This can just be fixed by introducing UIDs or something.
  * Gotta be careful to find all the places that make dumb assumptions about the name.
* How do I implement dynamic types with function overloading?
  * With overloading this becomes multimethods, which sound complex to implement.
  * If I swap to methods it's more plausible
    * Every dynamic type just carries a pointer to a function table containing all of its methods, alongside its field table

## Roadmap

* Port tetris demo
* Support RC pointers for safe memory/resource deallocation
* Consider supporting dynamic types
* Support the Windows ABI properly (instead of hacking around it)
* Enable basic metaprogramming

## Other

### React hooks

React hooks may be an interesting approach to state management in the reactive paradigm. 

### Migrate to ORC

ORC is the newest JIT api. It has some new features (like lazy loading) and might just be better thought-out in general. I think it would require using the C interface directly.

Really I should try to find an example JIT implemented using ORC.

### Nim destructors

This blog post by the creator of Nim is interesting:

https://nim-lang.org/araq/destructors.html

It talks about stuff like copying, moving, avoiding pointers, and includes a proposal to copy strings by default(!).