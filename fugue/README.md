# Fugue

A functional programming language with a number of useful features:
  - Polymorphic types, with full type inference
  - Typed holes and hole inference
  - A built-in Hoogle-like interface for searching the environment
  - An optional prelude
  - User-defined data-types
  - A built-in program synthesis engine, _Fantasia_.

To build:
  1. Clone the repository.
  2. Install the Haskell toolchain (GHC, Cabal).
  3. Run `cabal new-run` in the root directory.

# Fantasia

The focus of my 4th year Research project. A synthesis engine built right into Fugue!

To run, boot up a Fugue REPL and then use the `:s` command:

```
fugue> :s fun_name : t1 -> t2 -> t3
```

For example, the above will instigate the synthesis of a two-argument function called `fun_name`.