# End-to-end safety roadmap

## Goal

CLI acceptance uses only the extracted Rocq `infer_program_env_end2end`
checker.  `ErrNotImplemented` is a rejection, never a fallback to another
checker.  Parser/de Bruijn correctness is outside this roadmap.

Required theorem names stay intact:

- `infer_program_env_end2end_sound`
- `check_program_env_end2end_sound`
- `infer_program_env_end2end_big_step_safe_checked_initial_ready`

## Status

| Task | Status |
|------|--------|
| T1: `ECallExpr` `TFn`/`TClosure` in roots checker | done |
| T2c: `TTypeForall` in roots checker | done |
| T2d: `TForall` in roots checker | done |
| T3: switch OCaml CLI to `infer_program_env_end2end` | done |
| T4: CI entrypoint enforcement | done |
| T2a: `ECallGeneric` safety gate | blocked: generic runtime instantiation |
| T2e/T2g/T2b: function-value and captured-call gates | done except generic/type-forall cases under T2a |
| T2f: deref/reborrow/ref-write roots coverage | in progress |

## Current baseline

Latest full `sh tests/run.sh` baseline (2026-05-30): 29 valid-test failures; invalid tests pass.

- 18 `ErrEndToEndSafetyGateFailed`: generic direct calls, type-forall
  function values, mixed forall function values, generic-item function values,
  and generic local-bound bodies.
- 11 T2f failures:
  - 10 `ErrNotImplemented`: `EAssign`/`EReplace` through `PDeref` and
    inferred-let coverage.
  - 1 `ErrContextCheckFailed`: nested shared reborrow cleanup.

## Active T2f slices

1. Done: add concrete `place_resolved_roots` indirect none/self/one-hop facts.
2. Done: canonicalize singleton store-root resolution and prove same-length equivalence transport.
3. Done: prove no-shadow domain/length wrapper for resolved-root equivalence.
4. Done: prove resolved-root rename transport in Alpha/Shadow contexts under scoped collision invariants.
5. Done: add concrete instantiate facts for stable singleton store chains.
6. Done: add semantic singleton-result instantiate and resolved-root namedness
   helpers.
7. Done: add no-shadow equivalent transport for resolved singleton instantiate.
8. Done: prove non-shadow resolved-root rename transport without namedness.
9. Done: add store-name collision weakening/transport helpers for resolved
   root alpha support.
10. Done: add non-shadow resolved borrow/deref Prop rules and alpha
    support; keep shadow-safe rules out for now.
11. Blocked: resolved shadow-safe Prop rules need call-frame tail stability;
    appending outer roots can change `place_resolved_roots`.
12. Done: route indirect borrow and immediate deref-borrow roots through
   `place_resolved_roots` for singleton stores; keep raw-root fallback.
13. Done: route non-shadow `EAssign`/`EReplace` through resolved
    singleton `PDeref` roots; shadow-safe unchanged.
14. Done: invalid rejections preserved for linear refs, immutable writes,
    borrow conflicts, unresolved roots, and ambiguous roots.
15. Done: add stable depth-based resolved write target and route
    non-shadow indirect `EAssign`/`EReplace` through target root lookup.
16. Done: route shadow-safe resolved `EAssign`/`EReplace` through target root lookup; full Rocq/extraction and OCaml build pass.
17. Done: align resolved write Prop rules with checker-enforced target mutability.
18. Next: prove pathless resolved writes admissible for provenance/readiness gate; targeted valid indirect writes still reject there.

The resolver remains narrow: it follows bounded singleton store-root chains and
does not accept ambiguous/non-singleton update targets.

## Required checks

After each Rocq/extraction slice:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- targeted CLI tests for the changed construct

Before roadmap completion:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

## Acceptance criteria

- No OCaml fallback checker path accepts programs.
- No `Admitted`, `Axiom`, proof-hole, or weakened theorem is introduced.
- Generated OCaml fixtures are updated only by Rocq extraction.
- All T2f valid programs pass and matching invalid programs still reject.
