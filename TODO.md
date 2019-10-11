
# Language design

## V1

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

Support loading modules properly (like they are DLLs?)

Support metaprogramming?

### TODO

* Finish fixing the overloading support. Seems like a nice thing to have.
  * Linking is a problem. I have to link functions between modules. I have to link global variables between modules. I have to link external C functions. There are slightly different mechanisms for each. The only thing I really need to change for function overloading is the way that functions are linked between modules, and perhaps also within modules.
  * When a function name is referenced, in code, I can say exactly which function it is and which module it's from. This can happen in the type checker. So there shouldn't really be a complex problem when linking stuff.