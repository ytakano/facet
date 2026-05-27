---
applyTo: "fixtures/**,rocq/theories/TypeSystem/TypeChecker.v"
---

Use when modifying Rocq extraction, extracted OCaml checker code, extraction mappings, runtime stubs, or the trusted boundary between Rocq and OCaml.

## Goal

Preserve the meaning of the verified Rocq checker when extracted to OCaml.

## Checkpoints

1. Identify which Rocq definitions are extracted.
2. Confirm that `infer_program_env_end2end` and `check_program_env_end2end` are extracted.
3. Confirm that the OCaml entry point calls `infer_program_env_end2end`, not a duplicated implementation or fallback checker.
4. Review custom extraction mappings.
5. Check whether extracted types preserve intended semantics:
   - nat
   - Z
   - bool
   - string
   - list
   - option
   - result-like encodings
6. Ensure OCaml glue code does not reinterpret success/failure.
7. Add an end-to-end test through the actual CLI.
8. Add a direct checker test if possible.

## Hard constraints

- Do not edit generated extracted OCaml manually.
- Do not replace extracted logic with handwritten OCaml logic.
- Do not trust parser/desugar unless separately checked.
- Do not introduce partial OCaml functions at the checker boundary without explicit error handling.

- Do not use extracted `infer_full_env`, `infer_full_env_roots`, or `check_program_env` as an OCaml CLI acceptance fallback.
