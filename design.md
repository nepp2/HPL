
# Design

I'm still trying to implement polymorphism. I got stuck when I started thinking about how to integrate it with a system of hotloadable modules. Now I'm not sure how this system should work.

I discovered the Scopes programming language and I feel as though I have overcomplicated things. It has a similar design, but I believe it has far fewer features in the core language. I am also wondering whether I really could make the whole language somewhat REPL-based. What core commands are needed?

- Bind value to symbol
- Create function value
- Code blocks
- Primitive
- local variable

## Language primitives

- numbers
- arrays
- tuples

## Structs

How would you implement structs? A struct is a tuple of values, where each index has a name.

```rust
  struct blah {
    x : i64
    y : i32
  }
  let b = blah.new(50, 60)
  b.x = 5

  // the above could desugar into

  def blah = env {
    def field::x = 0 : usize
    def field::y = 1 : usize
    def shape = tuple(i64, i32) : prim
  }

  let b = (50, 60) : blah::shape
  b[blah::field::x] = 5

  // and unions...
  union bleh {
    x : i64
    b : blah
  }
  let b = bleh.new(x: 50)
  b.x = 5

  // could desugar into

  def bleh = env {
    def variant::x = i64 : prim
    def variant::y = blah // how does this work?
    def shape =
      if field::x.size() > field::y.size()
        { field::x } else { field::y }
  }

  let b = zero() : bleh::shape
  *(&b as ptr(bleh::variant::x)) = 50 : bleh::variant::x
  *(&b as ptr(bleh::variant::x)) = 5

```

This is a little complicated, because the `def`s are constant values that must be evaluated before the rest of the file can be type-checked. The `env` construct creates a new namespace, which is returned as a constant. I'm not sure what can happen inside there.


# Idea

All defs are constant and evaluated separately. Types are defs that match a particular interface?