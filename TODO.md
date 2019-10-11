
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
