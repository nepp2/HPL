
# References to add:

- Pony (maybe project Verona?)
- Elm
- React and Redux
- Mun (https://mun-lang.org/)
- Clojure's tools.namespace (https://github.com/clojure/tools.namespace)
  - Solves the problem of code reloading leaving old stuff littered around
  - Similar to the loader scripts I'm working on
  - As described here: https://www.youtube.com/watch?v=50vU6rp2jyA

# Terra

http://terralang.org/

Terra is a programming language that the design of this one quite a lot. It uses LLVM to code generate of high performance systems which are specified in a C-like language called Terra. However, Lua is embedded within the compilation process in such a way that it has total control, and can dramatically alter the semantics and behaviour of the Terra lanugage. For example, the Terra system can be extended with templates and dynamic dispatch with very simple lua scripts.

As lua is an interactive, intepreted language, Terra can be used as an interactive code generation system. This means it is suitable for tasks like high-performance numerical computing, offering quite a different approach to the Julia language.

# Emtempore

https://extemporelang.github.io/

A high-performance live coding system implemented on top of Scheme. Quite similar to Terra in a lot of ways. Scheme acts as a metaprogramming language to govern the interactive use of a high-performance C-like lisp dialect.

# Scopes

https://scopes.readthedocs.io/en/latest/about.html

Another programming system similar to Terra and Extempore. However, it attempts to present a single, unified language which can control its own code generation, much like this system. It is based on lisp-style s-expressions, but uses an alternative front-end syntax based on whitespace instead of parens, which also has some support for infix operators.

It is designed for game development and seems to be pursuing a borrow-checking approach to memory management inspired by Rust's, but with full type inference. Although it has full type inference, it is forward-inference only. So, much like a C++ template, the type checker can only provide feedback in response to a template instantiation.

It has an interesting opt-in approach to function overloading whose behaviour can be altered separately within the scope of each module that imports the function.

Scopes seem to have a smaller and more powerful core language than this project. Some trade-offs:

- Scopes is a REPL-based language; its top level is executed sequentially, and can modify the environment at will. This is simple and powerful.
- BORGOL is not REPL-based, although it can emulate a REPL quite easily. It is based around modules with precisely tracked dependencies, rather than a global environment (or a nested series of scoped environments). In other words, it is more like Java than Python. Interactivity comes from hot-swapping modules.
- Scopes does forward type inference. I'm not sure if it type-checks a function before it's called? BORGOL does full type inference (within each module).
- The forward type inference in Scopes means that parametric polymorphism is straightforward. _All_ functions are code generated on-demand. BORGOL has separate machinary for polymorphic functions (currently they behave like C++ templates).
- The Scopes language (presumably) behaves differently within functions. A function body cannot introduce new symbols based on variable runtime data and then immediately make use of them, whereas top-level code can. In BORGOL, top-level scope is the same as function scope; a symbol can be dynamically loaded and called, but this will be very explicit in the code (as in C).

# GOAL (Game-Oriented Assembly Lisp)

https://en.wikipedia.org/wiki/Game_Oriented_Assembly_Lisp

The (somewhat) famous lisp dialect from the early days of Naughty Dog, which apparently mixed high-level features with the ability to generate assembly code. It was also used as an interactive editing tool for loading compiled code into running games. This is very similar to what I'm doing.

# Jai

A low-level programming language designed for game development by Jonathan Blow. It is not targetting memory safety or RAII. Instead it intends to support the programming patterns that many game developers have found to be more practical and performant. Like most game engine developers, Jonathan Blow advocates managing memory in large chunks, instead of on a per-object basis. In practise this often means putting lots of objects in large, flat arrays in global scope. This is probably best understood as a relational approach to managing data structures. It has many advantages, in terms of performance, simplicity and even ease of use. Jai is also aiming to provide better support for short-lived memory arenas, in the style of region-based memory management.

As mentioned before, Jai seeks to make these things easy, but not necessarily robust. Instead of enforcing correctness properties in the type system or runtime, the team's strategy is to try and make memory errors as easy to debug as other types of error.

Jai also attempts to address issues in compilation time, just by delivering a highly-optimised compiler.

https://www.youtube.com/playlist?list=PLmV5I2fxaiCKfxMBrNsU1kgKJXD3PkyxO


# Cranelift JIT

https://github.com/bytecodealliance/cranelift

A JIT designed to be a WASM back-end. Potentially the ideal JIT compiler for this project, when it is more mature. It should be much faster than LLVM at generating code, but its output is likely to run slower than LLVM's output. Cranelift makes sense as a JIT for development, and LLVM as an AoT compiler for producing binary releases.

# Things I should look into

## Sema

A paper titled "Designing for a pluralist and user-friendly live code language ecosystem with Sema".

http://sro.sussex.ac.uk/id/eprint/87404/

## Nim destructors

This blog post by the creator of Nim is interesting:

https://nim-lang.org/araq/destructors.html

It talks about stuff like copying, moving, avoiding pointers, and includes a proposal to copy strings by default(!).
