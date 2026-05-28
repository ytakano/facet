# End-to-end safety roadmap

## Goal

Use one extracted Rocq checker path for CLI acceptance:
`infer_program_env_end2end`.  The OCaml CLI must not recover
`ErrNotImplemented` by falling back to `infer_full_env`, `infer_full_env_roots`,
`check_program_env`, or handwritten checker logic.

The theorem boundary is the alpha-normalized core `global_env` produced after
the parser/de Bruijn frontend.  Parser and de Bruijn correctness are outside
this roadmap.

## Status

| Task | Status |
|------|--------|
| T1: ECallExpr TFn/TClosure in roots checker | done (276b83e) |
| T2c: TTypeForall in roots checker | done (80ca8bf) |
| T2d: TForall (HRT) in roots checker | done (a4ea88a) |
| T3: switch OCaml CLI to `infer_program_env_end2end` | done |
| T4: CI enforcement of entrypoint policy | done (8bd3d82) |
| T2a: `ECallGeneric` safety gate | pending |
| T2e: function-value parameter/local call safety gate | pending |
| T2g: mixed lifetime/type forall roots calls | pending |
| T2b: `ELetInfer` captured closure call safety gate | pending |
| T2f: deref/reborrow/ref-write roots coverage | pending |

## Current blockers

With the CLI using `infer_program_env_end2end`, `sh tests/run.sh` currently has
38 valid-test failures:

- 24 `ErrEndToEndSafetyGateFailed`
  - `ECallGeneric fname type_args args` direct-call bodies.
  - `ECallExpr (EVar x) args` function-value calls.
  - captured closure calls through local bindings.
- 3 mixed `for<'a, T>` function-value calls rejected as malformed HRT bodies.
- 11 `ErrNotImplemented`
  - deref/reborrow/write-through-reference roots coverage.

## Remaining implementation slices

### T2a: `ECallGeneric` safety gate

- Extend the direct-call Prop summary and executable checker to recognize
  `ECallGeneric fname type_args args` without erasing type arguments
  unsoundly.
- Prove the checker branch sound and bridge generic-call evaluation to the
  existing direct-call runtime safety route.
- Target valid failures: `explicit_generic_call`, `generic_direct_call_*`, and
  generic expected-call forms.

### T2e: function-value parameter/local call safety gate

- Add a summary case for `ECallExpr (EVar x) args` when roots/shadow-safe typing
  proves the callee is a valid function value.
- Extend the executable gate and soundness proof.
- Extend captured runtime safety to route evaluated closure values through the
  callee-body safety theorem.
- Target valid failures: HRT function-parameter calls, type-forall
  function-value calls, and generic item-as-value calls.

### T2g: mixed lifetime/type forall roots calls

- Reuse `infer_mixed_forall_call_env` in roots and shadow-safe `ECallExpr`
  branches when a `TForall` body is `TTypeForall`.
- Keep structural, elaborated, roots, and shadow-safe call inference aligned.
- Target valid failures: `mixed_forall_fn_value_*`.

### T2b: captured closure local binding safety gate

- Accept `ELetInfer m x (EMakeClosure ...) (ECallExpr (EVar x) args)` with the
  same freshness, capture, and root-exclusion checks as annotated local closure
  calls.
- Target valid failures: `tests/valid/closure/capture_*`.

### T2f: deref/reborrow/ref-write roots coverage

- Add roots and shadow-safe coverage for `EDeref` and nested `PDeref` write and
  reborrow paths required by the valid suite.
- Preserve existing invalid rejections for linear refs, immutable writes, and
  borrow conflicts.
- Target valid failures: assign-through-ref, reborrow, and replace-through-ref
  cases.

## Required checks

Run after each Rocq/extraction slice:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- targeted CLI tests for the slice

Run before declaring the roadmap complete:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

## Acceptance criteria

- Accepted CLI programs pass through `infer_program_env_end2end`.
- `ErrNotImplemented` is a rejection, never a fallback trigger.
- Required theorem names remain present:
  `infer_program_env_end2end_sound`,
  `check_program_env_end2end_sound`, and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready`.
- Generated OCaml fixtures are updated only by Rocq extraction.
- CI and `AGENTS.md` enforce the end-to-end checker entrypoint policy.
- All tests must pass finally.
