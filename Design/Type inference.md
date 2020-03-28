# Current system

Can infer the types of variables, globals and function arguments. Infers by extrapolating information from known types:
- Literals
- Explicit type tags
- Previously inferred types

Resolving symbols references is difficult due to overloading. A reference can only be resolved when it is certain that no other symbol matches its type. Types start from 'any', and are iteratively refined.

## Limitations

- Can't infer generics (it knows when stuff is unresolved, but doesn't know where its type came from)
- Currently very slow, due to the symbol resolution mechanism
  - it is at least N*M
    - N is the number of symbols visible
    - M is the number of symbol references in the new module
- Can't infer types from field names (this is fixable, but isn't that useful anyway)

