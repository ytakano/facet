# Module System Implementation Plan

## Baseline: Done

- Inline `mod Name { ... }` parses as source-level namespaces.
- Qualified paths flatten to canonical names such as `core::option::Option` before de Bruijn conversion.
- Runtime core loading reads `core/*.facet`, or `FACET_CORE_DIR` when set, before the user file.
- `core::option::Option` and `core::result::Result` live in `core/lib.facet`.
- User source files cannot define top-level `mod core`.
- The OCaml CLI still uses extracted `infer_program_env_end2end` as the only checker authority.

## Next Small Tasks

1. **M2.1 diagnostics**: replace generic `raw elaboration failed` for unresolved qualified module/type/enum/function paths with source-level validation errors that include the original path.
2. **M3.1 visibility syntax**: parse `pub` on modules and item definitions, store it in the named AST, and preserve current behavior by treating all omitted visibility as private only after M3.2 is ready.
3. **M3.2 visibility resolver**: enforce private/public access during module flattening. Private items are visible in the defining module and child modules; public items are visible by explicit path from outside.
4. **M3.3 visibility tests/docs**: add valid/invalid fixtures for public sibling access, private sibling rejection, child access to parent private helper, and public item dependency policy.
5. **M4.1 named imports**: parse `use path;`, resolve module-local type/function/constructor names, and reject ambiguous imports. No aliases or glob imports yet.
6. **M4.2 import aliases**: add `use path as Name;` for type/function paths.
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
