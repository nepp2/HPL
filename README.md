# Reactive game development prototype

This is a research project aiming to create a live, reactive programming environment for writing games and game technology.

This prototype includes a custom programming language. However, we also hope to provide insights that can be generalised for use in existing high-performance programming languages, such as C, C++ and Rust.

## Goals

- Expressive, general-purpose, memory-safe language
- High throughput (good cache behaviour)
- No unpredictable garbage collection pauses
- Reactive, node-based programming model, with hot code reloading in nodes
- Immediate feedback in response to all changes, with live visualisations
- Extensible node editor, supporting asset pipelines and asset creation

## Planned language semantics

- Each node's state is isolated in a memory region
- A region can be dropped or garbage-collected
- High-level programming constructs available within regions without lifetime analysis

## Current Progress (Jan 2020)

The language in its current state could be summarised as C with type-inference, templates and a very simple module system. It is JIT-compiled with LLVM, but could also be AoT compiled to a binary without much difficulty. Modules can be hotloaded. This is all very pre-alpha, however.

The language does not yet aim for memory safety, as settling on a design for the reactive programming model and hotloadable modules takes priority. I am currently working on the modules and reloading, in order to prototype a basic node graph system.

# Building

_(Note: I would not recommend that anyone else attempt to build or run this software yet. It is at a very early stage of development, lacks documentation and is frequently broken.)_

- Install LLVM 8 (instructions for Windows below)
- Just run `cargo build`

## Installing LLVM on Windows

Based on these instructions: https://llvm.org/docs/GettingStartedVS.html

### Summary

* Download the source code
* Install CMake and python 3.x
* Point CMake GUI at the source
* Click "config", which should prompt a little window to pop up:
  * Choose Win64 from the drop-down
  * Add `host=x64` as an option (the instructions linked say `-Thost=x64`, but actually mean `-T host=x64`, and the `-T` is implicit in this dialog box)
* Leave the default options, except for:
  * change the installation directory from "program files" to something with no spaces, or everything will compile but cargo won't be able to build the bindings.
* Click "generate". Should spit everything out into a target folder
* Open LLVM.sln. Check that it says "Win64".
  * Might need to open Visual Studio as an administrator if the install directory is somewhere protected
* Change from "Debug" to "Release"
* Build the "INSTALL" project. I think this should run with no errors.
* Add the newly-installed `llvm/bin` folder to the user's `PATH` environment variable

### Why do you have to build LLVM from source?

From the llvm-sys documentation:

> You must use a version of Rust that uses the same compiler as you build LLVM with, either MSVC or MinGW. Fortunately, a mismatch like this will cause errors at compile-time when llvm-config provides options which are supported by only one of them, so if you're using the other it will cause the build to fail.

The prebuilt windows binaries on the LLVM website do not work, so I presume they are not built with the visual studio compiler (MSVC). I could use the MinGW Rust, but that's just a whole other hassle. It seems less well supported.

### Isn't the LLVM JIT slow?

In the long-term I would explore other options for fast JIT compilation. In the short-term I will rely on the incremental compilation model that this project is built around, and the fact that my test programs are unlikely to be very large.
