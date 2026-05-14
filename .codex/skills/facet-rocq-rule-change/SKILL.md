---
name: facet-rocq-rule-change
description: Use when changing Facet typing rules, ownership rules, effects, borrowing, lifetimes, drop elaboration, or checker definitions in Rocq.
---

## Required workflow

1. Identify the affected source construct.
2. Identify the corresponding core AST construct.
3. Locate the Rocq definitions:
   - syntax
   - typing relation
   - executable checker
   - soundness theorem, if any
4. Update the specification before or together with the executable checker.
5. Record proof gaps explicitly.
6. Add valid and invalid examples in tests/.
7. Run Rocq build.
8. If extraction is affected, run extraction and OCaml tests.

## Hard constraints

- Do not silently weaken linearity.
- Do not conflate affine discard with linear drop.
- Do not permit move-out from borrowed places.
- Do not change executable checker behavior without updating the corresponding typing rule or documenting the mismatch.
- Do not claim soundness for parser/desugar/OCaml wrapper unless those layers are covered.
