# Module and Core Library Roadmap

## Summary

Add `mod` as a source-language namespace feature and lower it before the verified checker sees the program. Rocq core syntax remains flat: module paths are resolved in the OCaml frontend to canonical names such as `core::option::Option`, then passed through the existing `global_env` and extracted end-to-end checker.

The initial core library lives under `core/` and is loaded at runtime before the user file. It contains only `core::option::Option` and `core::result::Result`.

## Phase 1: Module Syntax and Flattening

- Add `mod Name { top_item* }` to top-level syntax.
- Add qualified paths `ID::ID::...` for type names, trait names, function calls, struct literals, and enum constructors.
- Keep all module items public in v1. Do not add `pub`, `use`, aliases, glob imports, re-exports, `self`, `super`, or file-based module declarations.
- Resolve names before de Bruijn conversion. A module item becomes a flat canonical string name; local variables and type parameters still take precedence in their existing scopes.
- Reject duplicate item/module names in the same module. Do not merge duplicate `mod` declarations.

## Phase 2: Runtime Core Library Loading

- Load `.facet` files from `core/` in filename order. `FACET_CORE_DIR` overrides the directory for tests or alternate installations.
- Parse core files with the normal parser and prepend their items to the user program before module flattening and validation.
- Reserve top-level `mod core` for the runtime core library; user source files cannot define it.
- Keep the OCaml CLI accept/reject path on `infer_program_env_end2end`; core definitions are ordinary items, not a fallback checker path.

## Initial Core Surface

```facet
mod core {
  mod option {
    enum Option<T> {
      None,
      Some(affine T),
    }
  }

  mod result {
    enum Result<T, E> {
      Ok(affine T),
      Err(affine E),
    }
  }
}
```

There is no prelude in v1, so users must write fully qualified names such as `core::option::Option` and `core::result::Result`.

## Validation and Tests

- Valid tests cover nested module function calls, module-qualified user enums, and construction/match of `core::option::Option` and `core::result::Result`.
- Invalid tests cover unknown qualified paths, duplicate items in a module, user-defined `mod core`, unqualified core names, and wrong generic arity.
- Run `dune build`, `sh tests/run.sh`, `sh tests/fir/run.sh`, and `cd rocq && make` when the Rocq extraction artifacts need to be refreshed.
