---
name: facet-extraction-boundary
description: Use when modifying Rocq extraction, extracted OCaml checker code, extraction mappings, runtime stubs, or the trusted boundary between Rocq and OCaml.
---

## Goal

Preserve the meaning of the verified Rocq checker when extracted to OCaml.

## Checkpoints

1. Identify which Rocq definitions are extracted.
2. Confirm that the OCaml entry point calls the extracted checker, not a duplicated implementation.
3. Review custom extraction mappings.
4. Check whether extracted types preserve intended semantics:
   - nat
   - Z
   - bool
   - string
   - list
   - option
   - result-like encodings
5. Ensure OCaml glue code does not reinterpret success/failure.
6. Add an end-to-end test through the actual CLI.
7. Add a direct checker test if possible.

## Hard constraints

- Do not edit generated extracted OCaml manually.
- Do not replace extracted logic with handwritten OCaml logic.
- Do not trust parser/desugar unless separately checked.
- Do not introduce partial OCaml functions at the checker boundary without explicit error handling.
