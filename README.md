# Programming language research prototype

This is a language for programming games. It is very unfinished.

## Goals

### Unify the engine and scripting language

Usually a game engine is written in C++, and the gameplay code will be written in something like C# or Lua. This language aims to be good at both, just as [Julia](https://julialang.org/) does in the scientific computing domain.

### Enable live programming functionality

The initial target is simple live programming functionality in the vein of React/Redux and Elm. That means providing strong, pervasive support for hot-swapping code, and a time-travelling debugger. These features are usually delivered through pervasive immutability. The heavy allocation patterns and pointer indirection this usually involves are not ideal for game engine functionality. This language aims to permit mutability by instead guaranteeing restricted aliasing at key moments.

## Other Requirements

- Simple, high-level language
- High throughput (good cache behaviour)
- No unpredictable garbage collection pauses
- State transitions are local and explicit
- States can be reliably serialised and recovered

## Plan

- Reactive programming model, where events are handled in memory regions
- Restrict aliasing across region boundaries (surviving pointers are unique when the region ends)
- Cheap memory allocation and zero-latency collection within regions
- High-level programming constructs available within region without lifetime analysis
- Restricted aliasing enables easy serialisation for live programming features
- Regions make state transitions explicit in a high-level way

## Problems

The biggest problem is how to manage region boundaries without introducing high language complexity. The proposed solution is to stratify all allocations into two different types. There are ephemeral region allocations, and persistent allocations from a global heap. They have different field assignment semantics; assignment by reference and assignment by value, respectively.

It's not obvious whether this can be presented in a nice way. To some extent languages like Python and R already do this with their numerical computing libraries, so hopefully it's not as crazy as it sounds.

It's also unclear how painful it will be to keep all persistent state in structures which don't permit multi-aliasing or cycles. I will likely permit multi-aliasing for immutable types like strings.

