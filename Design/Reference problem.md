
# Solution

Introduce `ref` keyword?

Reference capability is an important part of a function's type, in the context of first class functions, because it affects the values that are valid to pass, and it affects the code-generation of the call sites.

This means that it could be difficult to infer the types of first-class functions:

```rust
  fun blah(f) {
    let b = 0
    f(b)
  }
```

The type of `f` could be `fun(i64)` or `fun(ref i64)`

```rust
  fun blah(f) {
    let b = 0
    f(ref b)
  }
```

this works, but then breaks this syntax:

```rust
  fun blah(f) {
    let b = 0
    b.f()
  }
```

I really can't decide if I want this syntax, but it seems important in cases like this:

```rust
  thing.increment(5) // current target style
  increment(thing, 5) // no dot application
  thing_increment(thing, 5) // no overloading
  thing_increment(ref thing, 5) // no implicit dereferencing
```

The list type I have raises another issue; lists are currently always references, so the `ref` keyword is not necessary. This is inconsistent and may feel confusing:

```rust
  fn increment(ref thing, i) { ... } // does mutation
  fn add(list, x) { ... } // also does mutation, but no ref keyword required
```

With implicit dereferencing, this is at least something for library authors to worry about, instead of users.

Julia works out whether something needs to be a reference or not automatically, and only lets the user determine whether it's immutable. The rule of thumb is that mutable things have to be references, and since their lifetimes aren't known they have to be heap allocated. It may remove the heap allocations if compiler analysis can infer a safe lifetime constraint, but this is often impossible.

# Implicit casting

At the moment the language is value-oriented, like C. The only reference type is pointer, which is actually treated like a value, so there is no implicit reference-casting. This makes it harder to write methods that modify values:

```rust
  struct thing { tick : i64 }

  fun update(t : thing) {
    t.tick += 1
  }

  let t = thing.new(0)
  t.update() // t is copied into the function by value, so the local t is unmodified

  println(t.tick) // prints 0

  fun update2(t : ptr(thing)) {
    t.tick += 1
  }

  t.update2() // this does't resolve, because the type signature does match. Can't auto-cast t to a pointer.

  (&t).update2() // this works, but it's ugly
  update2(&t) // this works, but it's inconsistent with the rest of the language
```

Possible solutions:
  - Get rid of method call syntax
    - makes code a bit uglier
    - behaviour is still a bit surprising
  - Use a keyword to indicate when arguments are mutable references
    - This isn't really part of the type system. It just alters the runtime semantics.

```rust
  struct thing { tick : i64 }

  fun update(ref t : thing) {
    t.tick += 1
  }

  let t = thing.new(0)
  t.update()

  println(t.tick) // prints 1

  fun update2(t : thing) {
    t.tick += 1 // should this be an error?
  }
```
