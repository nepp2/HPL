
# Immediate TODO list


# Roadmap

- ~~Support polymorphism~~
- ~~Port tetris demo~~
- Make a time-travelling UI for demo
- Make a node-based module loading system

# Low priority issues

## TypeDirectory legacy

The `TypeDirectory` struct in `types.rs` is pretty ugly code, and can probably be replaced with some simpler use of the `CodeStore` type.

## Broken C ABI

I haven't made any effort to support the C ABI beyond using the default behaviour of LLVM. This behaviour is definitely incorrect on Windows. I am currently hacking around it because I know what the most common ABI issue is; any type larger than 64 bits will never actually be passed by value in a Windows C function, even if the signature implies that it is. Instead it is passed as a const pointer. I hack around this by just passing types like this by pointer.

E.g. the following C function signature:

`void some_function(BigStruct x) { ... }`

becomes this instead:

`void some_function(BigStruct *x) { ... }`

which looks like this in my language's current syntax:

`fun(x : ptr(BigStruct))`

## Module loading memory safety issue

The current `load_module` function is probably not memory safe. E.g. if something is borrowed from one of the `CodeStore` hash maps, calling `load_module` from inside the language may append to that hash map, causing its underlying array to be dropped and reallocated. Then that borrowed reference is a dangling pointer.

In practise it might be quite unlikely for this to happen, but I should still look into it.

## Slow JIT compilation

LLVM is not a fast JIT, and I am not even using the newest version of its API. I believe I am using an MCJIT-style JIT instead of the newer Orc API.

Cranelift is probably a much better JIT library, because its designed for native-code JIT compilation in the browser, so the authors care a lot about startup time. It's also a Rust library. It didn't seem very mature when I started this project, but it's moving very quickly.
