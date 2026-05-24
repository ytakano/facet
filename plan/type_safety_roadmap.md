# Type Safety Roadmap

This is the active Codex-facing implementation guide. Keep it short: it should
answer what to do next, what not to change, and which reference file has the
details.

## Read Order

1. Read this file first.
2. For theorem/checker names, use `plan/type_safety_endpoints.md`.
3. For closure implementation details, use `plan/type_safety_closure_notes.md`.
4. For completed proof inventory, use `plan/type_safety_roadmap_inventory.md`.
5. For older milestone notes, use `plan/type_safety_roadmap_history.md`.
6. For surface closure design, use `plan/closure.md`.

Do not mine reference files for new work unless this file points there.

## Goal

Prove operational type safety for the user-facing ordinary checker pipeline.

Canonical target:

```coq
infer_full_env env f = infer_ok (T, Γ')
  -> initial_store_for_fn f s
  -> eval env s (fn_body f) s' v
  -> value_has_type env s' v (fn_ret f).
```

Current accepted-program checker:

```coq
check_program_env_alpha
```

Executable safety validators discharge proof evidence. The ordinary checker now
uses the ordinary safety gate below before accepting a function.

## Current State

- The strongest checked-initial safety endpoint for the general provenance
  route is:

  ```coq
  check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready
  ```

- The strongest checked-initial safety endpoint for direct-call-local evidence
  is:

  ```coq
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready
  ```

- The strongest checked-initial safety endpoint for local non-capturing
  function-value calls is:

  ```coq
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary_big_step_safe_checked_initial_ready
  ```

- The strongest checked-initial safety endpoint for local captured closure
  calls is:

  ```coq
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready
  ```

- The elaborated checked-initial endpoint for inferred local-let captured
  closure calls is:

  ```coq
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready
  ```

- Initial runtime readiness is still an execution-state premise, currently via
  `check_initial_root_runtime_ready`. It is not a program acceptance condition.
- Ordinary checker acceptance is gated by `check_fn_ordinary_safety_gate`.
  A function must pass the legacy full checker and one of the root-shadow,
  direct-call, non-capturing function-value, or captured-call sidecar routes.
- Direct `ECall` and syntactic `ECallExpr (EFn fname) args` are handled by
  localized sidecar routes. Do not add direct calls to ordinary expression
  readiness.
- General `ECallExpr callee args` remains staged. Non-capturing function
  values, immutable-copy captured closures, ordinary checker support for
  callable shared-reference captured closures, and captured-call sidecar
  support for nonzero-lifetime copied shared-reference captures are in place
  for both direct make-closure calls and annotated local-let calls. Mutable and
  affine/linear captures remain later work.

## Current Safety Routes

No new proof target is selected here. Treat the current endpoints as completed
safe entry points and preserve their contracts unless a later task explicitly
chooses a target and justifies the contract change.

Current captured-call sidecar coverage includes:

- direct `ECallExpr (EMakeClosure fname captures) args`;
- annotated local-let captured calls:

  ```coq
  ELet m x T (EMakeClosure fname captures)
    (ECallExpr (EVar x) args)
  ```

- inferred local-let captured calls through elaboration by
  `infer_program_env_alpha_elab`;
- expression-level exact sidecar evidence used by the checked-initial
  captured-call route, including `if` evidence where the exact sidecar carries
  the branch root-env equality required by the root/shadow proof path.

Shared-reference captured-call support is with-env for the direct and
annotated local-let routes. It handles nonzero-lifetime copied
shared-reference captures without making closure calls ordinary direct-call
evidence.

Keep these invariants stable:

- Closure-call lifetime instantiation stays local to the
  `TForall ... TClosure` call path.
- Exact sidecar capture checking uses
  `check_make_closure_captures_exact_sctx_with_env`.
- Captured-call root evidence uses copied runtime capture roots, not arbitrary
  caller root-env entries.
- Canonical shared-reference captures are frame-relative; do not coerce them
  back into the older `captured_call_frame_ready` shape.
- `ELetInfer` still has no core `Eval_LetInfer`; inferred local-let coverage is
  via elaborated annotated bodies, and safety is claimed for the elaborated
  environment.

## Current Captured Closure Facts

Detailed notes are in `plan/type_safety_closure_notes.md`. Stable facts:

- `TClosure` is distinct from `TFn`.
- `EMakeClosure fname captures` exists for immutable unrestricted captures and
  currently types as a `TClosure`.
- `fn_def` has separate `fn_params` and `fn_captures`.
- Function bodies use:

  ```coq
  fn_body_ctx f = params_ctx (fn_params f ++ fn_captures f)
  ```

- Direct `EFn` and direct `ECall` remain empty-capture only.
- Captured-call sidecar evidence exists for direct make-closure calls and the
  local-let/elaborated routes listed above.
- Captured callee summaries expose `NoDup` for:

  ```coq
  ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))
  ```

## Future Candidate Areas

These are candidate areas only; do not treat this list as a selected next
proof target.

- Mutable and affine/linear captures.
- Broader general-callee `ECallExpr callee args` coverage beyond the current
  direct, non-capturing function-value, and captured-call routes.
- Semantics-level support for `ELetInfer`, if the language design later needs
  safety for the original inferred-let core form rather than the elaborated
  environment.
- Progress, after a future small-step semantics exists.
- Remaining false negatives from `plan/review.md` that can be reduced without
  weakening the ordinary safety gate.

## TypeSafety Module Ownership

The TypeSafety split is complete enough for the current roadmap. Do not start
another file-splitting batch just because a file is large. Move existing lemmas
only when a new proof requires a clear dependency boundary, or when compile-time
measurement identifies a concrete bottleneck.

Going forward:

- Add new direct-call helper facts and route cores to the focused direct-call
  modules, with public wrappers in `TypeSafetyDirectCallWrappers.v`.
- Add new captured-call helper facts and route cores to the focused
  captured-call, runtime-args, or closure cleanup split modules according to
  their current dependencies.
- Keep public theorem names visible through `TypeSafety.v`, but add wrappers to
  focused `*Wrappers.v` files instead of growing `TypeSafety.v`.
- Keep proof statements stable unless the active implementation task requires a
  theorem-strengthening step.

Current ownership pattern:

- `TypeSafety.v`, `TypeSafetyCallFrame.v`, `TypeSafetyCapturedCall.v`,
  `TypeSafetyClosureRuntimeArgs.v`, `TypeSafetyClosureWrappers.v`,
  `TypeSafetyBasePreservation.v`, and `TypeSafetyPrefixPreservation.v` are
  compatibility/export surfaces for the current split. Do not assume they own
  old moved proof bodies just because older notes said so.
- Focused split modules own proof bodies. For example, direct-call setup,
  body, evidence, and route facts live in the direct-call split modules;
  captured-call make/let/evidence facts live in the captured-call split
  modules; closure cleanup facts live in the cleanup split modules; and public
  theorem names are kept stable through wrapper/export modules.
- Treat detailed completed ownership lists as inventory/history notes, not as
  active routing instructions. Before adding or moving a proof, inspect the
  current imports and nearest focused module instead of following stale
  roadmap inventory.

When adding a new proof or wrapper, run at least:

```sh
cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeSafety.v
```

If a future task really needs another split, first record the measured reason
in this file and keep the split separate from theorem-strengthening work.

## Fixed Boundaries

- Big-step preservation comes before progress.
- Progress is deferred until a future small-step semantics exists.
- The ordinary checker remains the primary accepted-program interface.
- Root provenance remains proof evidence, but the ordinary accepted-program
  checker is intentionally filtered by `check_fn_ordinary_safety_gate`.
- Do not bypass the ordinary safety gate to recover old ready-gap acceptance.
- Do not add `Axiom`, `Admitted`, or `Abort`.
- Do not silently weaken linearity, borrowing, reference-target safety, or drop
  behavior.
- Do not duplicate type-checking logic in OCaml.

## Review Gates

Keep the old review cases in `plan/review.md` as regression/proof gates while
reducing validator false negatives:

- active-borrow access for ordinary reads/moves;
- linear aggregate obligations for every linear component path;
- `&mut T` invariance in the referent type;
- struct field mutability for assignment and `replace`;
- local type annotation lifetime elision rejection;
- generic trait arity and bound validation;
- let-local reference escape is rejected by the ordinary safety gate;
- `replace p e_new` target self-use and alias/borrow variants.

## Sub-Agent Policy

Use sub-agents only for implementation tasks. Before spawning a sub-agent,
state why the task is implementation-only.

Do not delegate:

- uncertainty reduction;
- proof design;
- choosing a new invariant;
- changing checker contract;
- repository-wide investigation.

Allowed delegation examples:

- proving a named helper whose statement and dependencies are fixed;
- mechanical theorem rewiring after the main proof shape is fixed;
- focused regression test updates after expected behavior is fixed.

## Required Checks

For type-system work:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|Abort\.|DEBUG|idtac" rocq/theories
```

For roadmap-only edits:

```sh
git diff --check
```

The `rg` command exits with status 1 when no matches are found; that is
success.

## Commit Policy

After implementation and checks pass, commit with GPG signing disabled:

```sh
git commit --no-gpg-sign -m "<short imperative subject>"
```
