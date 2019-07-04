# Programming language research prototype

Project to create a live programming environment for game development, built on top of a custom programming language and reactive programming model.

## Goals

- Simple, high-level language
- High throughput (good cache behaviour)
- No unpredictable garbage collection pauses
- Immediate feedback in response to all changes, with live visualisations
- Extensible editor, supporting asset pipelines and even asset creation

## Plan

- Reactive programming model, where events are handled in memory regions
- Restrict aliasing across region boundaries (surviving pointers are unique when the region ends)
- Cheap memory allocation and zero-latency collection within regions
- High-level programming constructs available within region without lifetime analysis
- Regions make state transitions explicit in a high-level way

# Building

- Install LLVM 8 on your system (instructions for Windows below)
- Just run `cargo build`

## Installing LLVM on Windows

Based on these instructions: https://llvm.org/docs/GettingStartedVS.html

## Summary

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

