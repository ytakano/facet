# Module System Implementation Plan

## Baseline: Done

- Inline `mod Name { ... }` parses as source-level namespaces.
- Qualified paths flatten to canonical names such as `core::option::Option` before de Bruijn conversion.
- Runtime core loading reads `core/*.facet`, or `FACET_CORE_DIR` when set, before the user file.
- `core::option::Option` and `core::result::Result` live in `core/lib.facet`.
- User source files cannot define top-level `mod core`.
- The OCaml CLI still uses extracted `infer_program_env_end2end` as the only checker authority.

## Next Small Tasks

1. **M2.1 diagnostics**: done. Unresolved qualified function, enum constructor, struct literal, trait, and type paths are rejected before raw elaboration with the original path in the validation error.
2. **M3.1 visibility syntax**: done. `pub` parses on modules/functions/structs/enums/traits and is stored in the named AST; enforcement remains deferred to M3.2.
3. **M3.2 visibility resolver**: done. Flattening rejects private qualified paths outside the owner module subtree and respects private module ancestors.
4. **M3.3 visibility fixtures**: done. Covered public path access, private sibling rejection, child access to parent private helpers, private module ancestors, and public core paths.
5. **M4.1 named imports**: done. `use path;` imports a module-local final segment, resolves to the same canonical path as explicit qualification, and rejects unknown, private, duplicate, or ambiguous imports.
6. **M4.2 import aliases**: done. `use path as Name;` binds a module-local alias for function/type paths and rejects private targets or alias collisions.
7. **M5.1 file module declarations**: parse `mod foo;` and load `foo.facet` or `foo/mod.facet` relative to the declaring file, rejecting missing files, duplicate inline/file modules, and cycles.
8. **M6.1 package root flags**: add explicit `--core-dir DIR` and, if needed, `--package-root DIR`; keep `core::...` globally available.

## Current Scope Rules

- No prelude, glob imports, re-exports, dependency packages, or semantic `Copy`/`Clone`/`Drop` integration before M6.
- Keep parser changes narrow; do not break existing struct literal, enum constructor, or place parsing.
- Keep module loading/name resolution in OCaml frontend only; Rocq core remains flat.
- Each completed task gets its own commit after updating this file.

## Verification Per Task

- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh` when name changes might affect FIR output
- `cd rocq && make` only when Rocq extraction or generated checker artifacts change
