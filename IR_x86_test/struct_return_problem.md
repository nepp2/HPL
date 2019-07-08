# Struct return problem

When I return a struct from my jitted language to a calling Rust function, the result is garbled. I did a lot of investigation into possible ABI issues and so on, but found nothing I was clearly doing wrong.

Eventually I tried creating x86 versions of two equivalent bits of code. One in Rust, and one in Cauldron. I wanted to compare the ABI and instructions used manually. As far as I can tell, they were returning the struct in exactly the same way (in two specific CPU registers), and using the same instructions.

# Workaround

Everything seems to work fine if I just use C-style OUT parameters. Instead of directly returning a struct, you pass a pointer to the memory that the struct should be written to.

# Theories

## Incompatible LLVM versions

I'm using LLVM 8, I think. Rust might be using an older version?

*Counter-point*: they should both conform to the same C ABI, or they wouldn't be able to call C function.

## Some mystery LLVM attribute/config

I managed to replicate all of the attributes that seemed significant, but my IR file still isn't 100% identical to what Rust and C generate.
