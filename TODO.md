
# Language design

## Plan

Implement a special-case RC type?

Or the yak-shaving plan:
 * Implement basic primitives for powerful metaprogramming system
 * Use this to implement something like generic types/functions
 * Use these to implement RC and Drop
 * Modify compiler to look for and call drop when possible

## Issues

### Make top-level like a REPL

 * The top-level function is no longer a single initialisation function.
 * Instead, each semi-colon separated expression is executed one at a time, as if entered into a REPL.
 * These expressions may interact with the environment in a number of ways
   * Introduce a new type
   * Introduce a new function
   * Introduce a temporary global (let)
   * Introduce a permanent global (global)
 * How should "let" be handled?
   * Heap allocation to be freed afterwards?
 * How can the memory footprint be compressed afterwards?
   * Maybe the function modules can be merged
   * Can all of the ir modules be dropped?
 
 Is this behaviour incompatible with AoT compilation? Can it be considered a build script? Do any part of these REPL scripts actually need to run on the client?

 Clearly functions that modify modules and generate code _can't_ run on the client. The idea was that this would all be done at compile-time. For that to work there does need to be some kind of clean separation of values. A module _must_ be able to initialise itself from scratch. So which of the features above breaks that?

 I think the key idea is that there are modules used to build a module, and there are totally different modules that it depends on at runtime. How do I separate these things?

 Proposal: a module is a script that returns a module object. I can call methods on a module object, but I can't call any functions on it. It can only be code-generated and handed as input to another module.

### Alternative to REPL

Support an eval keyword, which immediately compiles and links any code given to it as an internal module, as if it had been passed in by someone else. It can see all the other input modules.

```
    eval {
        fun array(t : expr) {
            'struct array {
                length : u64
                data : ptr(\t)
            }
        }
    }
```

### Macros

 * How should they work?
 * How do basic lisp macros work?
 * Is it basically a template language?
 * Can I avoid any special syntactic forms?
 * The problem with macros is that they make execution incremental within modules, which currently isn't supported.

### Generic types

 * Should they be built into the language?
 * Should they be built using a macro system?

### Reference counted pointers

 * Implement the rc type
   * Does it require generic structs, or should it just be built-in?
   * Even with generic structs, how do I handle automatic dereferencing with dot syntax?
     * Just overload a magic dereference function?
     * But then how do you access the actual fields?
   * How should array be structured?
     * Array(T) { length: u64, Ptr(T) }

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
