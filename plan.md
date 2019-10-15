
# Plan

## Reference-counted pointers

Implement a special-case RC type?

Or the yak-shaving plan:
 * Implement basic primitives for powerful metaprogramming system
 * Use this to implement something like generic types/functions
 * Use these to implement RC and Drop(RC)
 * Modify compiler to look for and call drop when possible

## Roadmap

* Support RC pointers for safe memory/resource deallocation
* Port tetris demo
* Consider supporting dynamic types
* Support the Windows ABI properly (instead of hacking around it)
* Enable basic metaprogramming


## Vague V1 plan

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