
# Plan

* Fix the cycle problem crudely
* Make very small metaprogramming example
* Consider how to port tetris

## Roadmap

* Solve the cyclic reference issue
* Enable basic metaprogramming
* Support RC pointers for safe memory/resource deallocation
* Consider supporting dynamic types
* Consider hindley-milner style inference
* Support the Windows ABI properly (instead of hacking around it)

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