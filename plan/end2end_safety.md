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
| T2a: `ECallGeneric` safety gate | blocked: generic runtime instantiation proof gap |
| T2e.1: monomorphic `TFn` variable call safety gate | done |
| T2e.2: HRT/closure function-value calls | blocked: runtime callee bridge needed |
| T2g: mixed lifetime/type forall roots calls | done |
| T2b.1: captured callee return-root evidence | done |
| T2b.2: captured closure runtime safety | in progress |
| T2b.3: captured closure regressions | pending |
| T2f: deref/reborrow/ref-write roots coverage | blocked: nested place root model needed |

## Current blockers

With the CLI using `infer_program_env_end2end`, `sh tests/run.sh` currently has
36 valid-test failures:

- 25 `ErrEndToEndSafetyGateFailed`
  - `ECallGeneric fname type_args args` direct-call bodies.
  - Remaining function-value calls: `TClosure`, lifetime-only `TForall`,
    type-forall, mixed `for<'a, T>`, and generic-item function values still
    need their runtime callee bridges.
  - captured closure calls through local bindings.  These fail first in the
    synthesized `__facet_closure` callee because returning a hidden capture
    leaves roots tied to `fn_params ++ fn_captures`.
- 11 `ErrNotImplemented`
  - deref/reborrow/write-through-reference roots coverage.  Nested `PDeref`
    places make `place_path` return `None`; roots typing needs explicit
    location/value root resolution before these paths can be accepted.

## Remaining implementation slices

### T2a: `ECallGeneric` safety gate

Blocked by generic runtime semantics.  The checker types `ECallGeneric` against
`apply_type_params type_args (fn_params fdef)` and
`subst_type_params_ty type_args (fn_ret fdef)`, but `Eval_CallGeneric` currently
alpha-renames and evaluates the uninstantiated `fdef` body and binds
uninstantiated params.  The direct-call runtime proof cannot soundly invert an
instantiated argument value, such as `isize`, back to `TParam 0`.

Required before accepting this gate:

- Add expression/function type-parameter instantiation for runtime calls.
- Evaluate `ECallGeneric` using the instantiated function body and params.
- Prove roots/shadow-safe preservation across type-parameter substitution.
- Then extend the safety gate and runtime route for generic direct calls.

### T2e: function-value parameter/local call safety gate

T2e.1 accepts only monomorphic `TFn` variable callees:
`ECallExpr (EVar x) args`.  The safety proof must recover that the runtime
`VClosure fname []` target has a base callee-body provenance summary.

T2e.1 tasks:

- Done prep: add checker/Prop summary evidence for general
  `ECallExpr callee args` function-value calls.
- Done prep: add empty-capture `ECallExpr` runtime helpers that reuse the
  direct-call callee summary route after callee inversion, including a `TFn`
  direct-call roots synthesis helper.
- Done prep: add a value-typing inversion that runtime closures are empty.
- Done prep: add `TFn` signature-bridge helpers for exact, compatible, and
  lifetime-equivalent runtime closure signatures.
- Done prep: strengthen runtime empty-closure typing so `fn_value_ty`
  witnesses require `fn_captures fdef = []`.
- Done prep: restrict general function-value summary evidence to
  non-type-generic callee types.
- Done prep: add a composed `TFn` `ECallExpr` runtime preservation wrapper.
- Done prep: add empty-closure `TFn` evidence for non-generic, non-HRT callees.
- Done prep: add a `TFn` wrapper that builds callee-route evidence from the
  callee summary.
- Done: narrow the general function-value gate to `EVar` callees inferred as `TFn`.
- Done: strengthen initial-store runtime evidence so stored empty function
  closures target functions with base callee-body provenance summaries.
- Done: extend non-capturing and captured runtime safety to consume the new
  `EVar` `TFn` branch.
- Done: targeted local and function-parameter monomorphic function-value
  call regressions pass.

Remaining T2e blockers:

- `TForall` function values need lifetime-instantiated runtime callee evidence.
- `TClosure` values need captured-callee return-root evidence.
- Type-forall and mixed forall function values stay under T2a.

### T2g: mixed lifetime/type forall roots calls

Done.  Roots and shadow-safe checkers route mixed `TForall`/`TTypeForall`
callee bodies through `infer_mixed_forall_call_env`, with matching roots,
alpha-renaming, readiness, and runtime-safety proof branches.  The remaining
mixed valid failures are function-value safety-gate failures under T2e, not
malformed HRT-body roots rejections.

### T2b: captured closure local binding safety gate

T2b targets source closures elaborated to `EMakeClosure` plus
`ECallExpr (EVar x) args`.  The generated `__facet_closure` callee may safely
return roots from hidden captures, but must still exclude ordinary params.

T2b tasks:

- Done: relax captured-callee summaries/checkers to allow return roots from
  `fn_captures` while preserving param exclusion, readiness, typing, and
  capture exactness.
- T2b.2: update captured-call runtime proofs so returned roots are bounded by
  argument roots plus copied capture roots, and temporary closure bindings stay
  excluded.
- T2b.3: run `tests/valid/closure/capture_*` and `tests/invalid/closure/*`,
  then record the remaining valid failure count.

### T2f: deref/reborrow/ref-write roots coverage

Blocked by nested place roots.  Current roots typing relies on
`place_path p = Some (x, path)`, but `PDeref` returns `None`, so nested deref
places are rejected before borrow, assign, replace, or deref-borrow rules can
run.

Required before accepting this gate:

- Add root-resolution helpers for nested places that separate location roots
  from value roots behind references.
- Define how writes through `PDeref` update the resolved store root.
- Add matching roots/shadow-safe constructors and soundness lemmas.
- Preserve invalid rejections for linear refs, immutable writes, and borrow
  conflicts.
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
