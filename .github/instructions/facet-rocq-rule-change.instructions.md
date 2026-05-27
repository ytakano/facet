---
applyTo: "rocq/**"
---

Use when changing Facet typing rules, ownership rules, effects, borrowing, lifetimes, drop elaboration, or checker definitions in Rocq.

## Purpose

This skill is for changes that may affect the formal semantics, type system, ownership discipline, effect system, borrow/lifetime rules, drop elaboration, executable checker, extraction, or type safety of Facet.

Facet has Rocq proofs for core type safety. Changes to typing-related rules must preserve the intended safety theorem, or explicitly record the remaining proof gap.

## Required workflow

1. Identify the affected source-language construct.
2. Identify the corresponding core AST construct.
3. Locate the Rocq definitions affected by the change:
   - syntax
   - well-formedness rules
   - typing relation
   - ownership / usage rules
   - borrowing / lifetime rules
   - effect rules
   - drop elaboration rules
   - executable checker
   - checker soundness theorem
   - type safety theorem and supporting lemmas
4. Determine the formal safety boundary:
   - Does the theorem cover the core AST only?
   - Does it cover elaborated terms after drop insertion?
   - Does it cover the executable checker?
   - Does it cover parser, desugar, extraction, or OCaml wrapper code?
   - If a layer is not covered, do not claim safety for that layer.
5. Update the specification before or together with the executable checker.
6. If the executable checker behavior changes, update one of:
   - the corresponding typing rule,
   - the checker soundness proof,
   - the documented mismatch,
   - or an explicit proof-gap note.
7. Update type-safety-related proofs as needed:
   - preservation
   - progress
   - substitution
   - weakening / strengthening
   - usage splitting
   - linearity invariants
   - borrow validity
   - lifetime validity
   - drop preservation
   - effect preservation
   - checker soundness
8. Record proof gaps explicitly.
   - List any `Admitted`, `Axiom`, unfinished lemma, or intentionally weakened theorem.
   - Explain whether the gap affects type safety, checker soundness, or only convenience lemmas.
9. Add valid and invalid examples in `tests/`.
   - Include negative tests for rejected programs.
   - Include examples that exercise the source construct and the corresponding core construct when applicable.
   - Include ownership/borrowing/drop/effect edge cases.
10. Run the Rocq build.
    - When Rocq compile times are high, profile and optimize the bottlenecks before committing changes.
11. If extraction is affected, run extraction and OCaml tests.

## Hard constraints

- Do not silently weaken linearity.
- Do not conflate affine discard with linear drop.
- Do not permit move-out from borrowed places.
- Do not allow use-after-move through checker changes.
- Do not allow use-after-free through lifetime-rule changes.
- Do not allow duplicated consumption of linear values.
- Do not treat drop elaboration as a substitute for affine discard.
- Do not change executable checker behavior without updating the corresponding typing rule or documenting the mismatch.
- Do not weaken theorem statements just to make proofs pass.
- Do not claim checker soundness unless the executable checker is covered by a soundness theorem.
- Do not claim source-language type safety unless parser/desugar/elaboration are covered.
- Do not claim soundness for parser, desugar, extraction, or OCaml wrapper code unless those layers are formally covered.
- Do not treat extraction tests as a proof of soundness.

## Expected final report

When finishing a change, report:

1. Changed source construct.
2. Changed core AST construct.
3. Changed Rocq files.
4. Changed typing/checker/drop/effect rules.
5. Affected safety theorem or checker soundness theorem.
6. Remaining proof gaps, if any.
7. Tests added or updated.
8. Rocq build result.
9. Extraction/OCaml test result, if relevant.
