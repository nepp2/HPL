
# Plan

## Issues

### Can't get symbols to link properly

I have failed to link symbols both from the parent executable and from other JIT-compiled modules.

This is true both for functions and global variables. Right now I'm hoping that it's the same problem.

Possible solutions:

- FinalizeObject
  - Properly "finalized" modules in MCJIT might be able to link symbols
- Cargo linker flag
  - Some guy on stackoverflow implied that C++ executables sometimes need to be compiled with a special flag to make sure that symbols are still available for linking
  - I guess you don't normally link against a runnable exe, so maybe the linker strips them?
  - The same thing might be possible/necessary in Rust via a compiler flag
- Implement SectionMemoryManager
  - Both the C++ MCJIT and iron-kaleidoscope example override MCJIT's memory manager to supply symbols from other JIT-compiled modules
  - This shouldn't affect symbols linked from the parent binary though
- Migrate to ORC

### FinalizeObject

Properly "finalized" modules in MCJIT might be able to link symbols

### Cargo linker flag

Some guy on stackoverflow implied that C++ executables sometimes need to be compiled with a special flag to make sure that symbols are still available for linking.

I guess you don't normally link against symbols from a runnable exe, so maybe the linker strips them? This is plausible partly because the system currently has no trouble linking against symbols like `malloc` and `sin`. I'm not sure if this is because they have special status as part of LibC, or if they have some special status in LLVM (e.g. maybe they are intrinsics).

It's possibel that I can pass the same flag to rustc, to achieve the same thing.

### Implement SectionMemoryManager

Both the C++ MCJIT and iron-kaleidoscope example override MCJIT's memory manager to supply symbols from other JIT-compiled modules.

This shouldn't affect symbols linked from the parent binary though.

### Investigate Julia further

Julia must be solving the same issue. I suspect it works either by using the SectionMemoryManager, or by manually linking global symbols into each module (or possibly both?).

One thing worth noting about Julia is that it uses far too much memory for use in game development.

### Migrate to ORC

ORC is the newest JIT api. It has some new features (like lazy loading) and might just be better thought-out in general. I think it would require using the C interface directly.

Really I should try to find an example JIT implemented using ORC.

## Roadmap

- Create the worksheet-style workflow with the new JIT
- Link symbols
  - from parent executable
  - between modules
    - For REPL
    - For structuring programs!
  - from DLLs
- Implement arrays
  - stack values?
  - with malloc?
