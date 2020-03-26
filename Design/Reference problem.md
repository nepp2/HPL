
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
