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
| T2e.2: HRT/closure function-value calls | in progress: direct HRT TFn EVar calls pass |
| T2g: mixed lifetime/type forall roots calls | done |
| T2b.1: captured callee base gate | done |
| T2b.2: local captured-call bridge | done |
| T2b.3: captured closure regressions | done |
| T2f: deref/reborrow/ref-write roots coverage | blocked: nested place root model needed |

## Current blockers

With the CLI using `infer_program_env_end2end`, the last full `sh tests/run.sh`
run after `ad74b28` had 33 valid-test failures:

- 23 `ErrEndToEndSafetyGateFailed`
  - `ECallGeneric fname type_args args` direct-call bodies.
  - Remaining function-value calls: `TClosure`, lifetime-only `TForall`,
    type-forall, mixed `for<'a, T>`, and generic-item function values still need
    runtime callee bridges.
  - Captured shared-ref closure function-value calls remain under T2e.2.
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

T2e.2 tasks:

- Done: add roots/shadow typing and soundness for lifetime-only `TForall`
  bodies whose core is `TClosure`; `capture_shared_ref` now reaches the
  existing safety-gate path and passes.
- Done: add compiled runtime wrappers for lifetime-only `TForall` `EVar`
  callees whose body is `TFn`.
- Done: connect summary evidence and non-capturing/captured runtime safety
  branches for direct-body HRT `TFn` EVar calls;
  `hrt_call_function_param` passes.
- Done: refresh the full-suite baseline after `ad74b28`; one HRT safety-gate
  failure was removed.
- Done prep: add non-function value/store summary helpers needed to preserve
  closure-target summaries across let-bound non-function values.
- Done prep: add store-typed/exact-summary closure-target summary helpers for
  the sequential-let runtime route.
- Done prep: relocate closure-target store summary helpers from
  `EnvRuntimeBaseSafety.v` to `EnvRuntimeShadowSummaryFacts.v` so later runtime
  safety modules can share them earlier in the dependency order.
- Done prep: add a later store-safe expression-summary Prop for recursive
  function-value calls without changing the extracted checker.
- Done prep: add the extracted store-safe expression-summary checker helper.
- Done prep: prove the store-safe expression-summary checker helper sound.
- Done prep: add a focused store-safe EVar-call/`let` checker and soundness
  proof for the sequential-let route.
- Done prep: add an EVar closure-target summary recovery helper for the
  sequential-let runtime route.
- Done prep: move the non-function value classifier into the checker and
  require narrow `let` bindings to be non-function values.
- Done prep: add a combined captured-call/store-safe checker helper without
  routing the end-to-end entrypoint to it yet.
- Done prep: prove Prop-level soundness and env-readiness for the combined
  checker helper.
- Done prep: narrow the store-safe function-value-call argument checker
  to vars and provenance-proven `fn` items, and add store-summary
  preservation helpers for `EVar`, `store_mark_used`, and `store_remove`.
- Done prep: prove narrow argument evaluation preserves closure-target
  store summaries for the sequential-call runtime route.
- Done prep: derive runtime root-name/key outputs from typed narrow
  summaries and output store typing.
- Done prep: expose direct-call cleanup final-store equality for
  preserving closure-target summaries after function-value calls.
- Done prep: add high-level function-value-call final-store equality
  wrappers for monomorphic and lifetime-forall `EVar` calls.
- Done prep: prove narrow function-value calls preserve closure-target
  store summaries through monomorphic and lifetime-forall direct-call cleanup.
- Done prep: factor captured-call runtime safety into a reusable
  single-function theorem for the combined gate.
- Done prep: add a monomorphic `TFn` narrow function-value-call
  runtime package lemma.
- Done prep: add a lifetime-forall `TFn` narrow function-value-call
  runtime package lemma.
- Done prep: prove the recursive narrow runtime package theorem.
- Done prep: prove the combined runtime safety/readiness theorem.
- Done prep: factor narrow store-safe callee Prop; measured checker-level
  branch factoring as a `Qed` bottleneck and kept the checker inline.
- Done prep: add direct-call argument bind helpers for preserving
  closure-target summaries across `bind_params`.
- Done prep: add store-safe direct-call arg value summaries so
  bind-param preservation does not require env-wide provenance.
- Done prep: route `infer_fn_env_end2end` through the combined gate and
  support narrow `let`/`let-infer` cleanup via root exclusion.
- Done prep: refactor narrow function-value-call summaries to use
  Prop-level callee typing instead of executable `EVar` inference witnesses.
- Done prep: prove structural root-instantiation preservation for
  narrow store-safe summaries.
- Done prep: prove store-safe direct-call argument evidence is
  preserved by alpha-renaming.
- Done prep: add focused `ECallExpr`/`EVar` disjointness helper for
  narrow alpha preservation.
- Done prep: add alpha-renamed function-value-call intro for narrow
  store-safe summaries.
- Done prep: add alpha-renamed `let`/`let-infer` intros for narrow
  store-safe summaries.
- Done prep: factor renamed `let` root-exclusion and collision side
  conditions for narrow alpha preservation.
- Done prep: derive renamed `let` body no-collision from narrow
  summaries.
- Done prep: prove `EVar` callee output preserves rename no-collision
  for narrow alpha preservation.
- Done prep: relate narrow summary roots to return roots and preserve
  return-root exclusion.
- Done prep: prove structural alpha-renaming preservation for narrow
  store-safe summaries.
- Done prep: add Prop-level direct-call branch for callee narrow
  store-safe summaries.
- Done prep: wire executable direct-call narrow checker branch and
  prove checker soundness for it.
- Done prep: preserve narrow store-safe summaries under appended fresh
  caller root frames.
- Done prep: recover root-name/key facts from prefix store typing for
  narrow runtime summaries.
- Done prep: derive narrow runtime output root-name/key facts from
  context-named inputs and prefix store typing.
- Done prep: bridge direct-call callees with narrow summaries through
  alpha-renaming, root instantiation, and caller tail frames.
- Done prep: require store-safe direct-call args for direct narrow
  captured-call summaries so bound params preserve closure-target summaries.
- Done prep: add a prefix-start direct-call component route for
  monomorphic `TFn` call expressions.
- Done prep: add prefix-start direct-call final-store equality for
  monomorphic `TFn` call expressions.
- Done prep: add prefix-start direct-call component and final-store wrappers
  for lifetime-forall `TFn` `EVar` calls.
- Done prep: add prefix/ctx tail-fresh support for direct-call narrow
  callee-route bridging.
- Done prep: add a prefix/ctx direct-call narrow callee-route bridge.
- Done prep: add monomorphic prefix-start runtime package support for
  store-safe narrow `TFn` calls.
- Done prep: add lifetime-forall prefix-start runtime package support for
  store-safe narrow `TFn` calls.
- Done prep: add recursive prefix/ctx runtime package support for
  store-safe narrow summaries.
- Done prep: add store-level root/key naming preservation for
  store-safe function-value-call args.
- Done prep: add store-named direct-call bridge helpers for
  prefix narrow runtime routes.
- Done prep: add store-named prefix-start runtime package support for
  narrow monomorphic and lifetime-forall `TFn` calls, including `let` cleanup.
- Done prep: transfer store-safe narrow summaries through
  `global_env_with_local_bounds` for direct-call runtime wiring.
- Done prep: thread store-ref-target preservation through narrow prefix runtime packages.
- Done prep: add prefix-named final-store equality and frame-scope helpers for narrow `TFn` calls.
- Done prep: add `typed_args_roots` adapter from lifetime-substituted params to anonymous param-ty lists.
- Done prep: add runtime signature bridge for lifetime-substituted direct-call params.
- Done prep: add bind-param root/key naming helpers for direct narrow runtime starts.
- Done prep: lift frame-scope preservation to recursive narrow summaries.
- Done prep: lift param-cover and param-scope preservation to recursive narrow summaries.
- Done prep: add store-named direct-call narrow callee-route bridge.
- Remaining proof gap: finish the captured-call direct-narrow branch.  The
  summary now has provenance, direct-narrow, and body-narrow cases; the proof
  needs a direct-call runtime wrapper that consumes callee store-safe narrow
  summaries.
- Then re-run the remaining HRT valid/invalid tests and update the full count.

Out of scope for T2e.2:

- Type-forall and mixed forall function values stay under T2a.

### T2g: mixed lifetime/type forall roots calls

Done.  Roots and shadow-safe checkers route mixed `TForall`/`TTypeForall`
callee bodies through `infer_mixed_forall_call_env`, with matching roots,
alpha-renaming, readiness, and runtime-safety proof branches.  The remaining
mixed valid failures are function-value safety-gate failures under T2e, not
malformed HRT-body roots rejections.

### T2b: captured closure local binding safety gate

T2b targets source closures elaborated to `EMakeClosure` plus
`ECallExpr (EVar x) args`.  The generated `__facet_closure` callee is currently
checked as a top-level function, but only has captured-callee evidence.

T2b tasks:

- Done: add a base captured-callee branch to the captured-call gate and safety
  proof.  Keep strict `fn_params ++ fn_captures` roots/env exclusion.
- Done: add an outer-`let` expression-summary bridge for local captured calls returning runtime-rootless values.
- Done: generalize the function gate to consume exact expression summaries for non-`if` bodies.
- Done: `capture_function_param`, `capture_unrestricted_annotated_let_call`, and `capture_unrestricted_let_call` pass; `capture_shared_ref` remains under the T2e higher-rank closure-value blocker; all `tests/invalid/closure/*` reject.

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
