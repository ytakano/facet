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

Executable safety validators are sidecars. They discharge proof evidence; they
do not redefine the language accepted by the ordinary checker.

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

- Initial runtime readiness is still an execution-state premise, currently via
  `check_initial_root_runtime_ready`. It is not a program acceptance condition.
- Ordinary checker acceptance still exceeds validator acceptance.
- Direct `ECall` and syntactic `ECallExpr (EFn fname) args` are handled by
  localized sidecar routes. Do not add direct calls to ordinary expression
  readiness.
- General `ECallExpr callee args` remains staged: first non-capturing function
  values, then immutable-copy captured closures, then captured references and
  lifetimes, then mutable and affine/linear captures.

## Next Implementation Order

Work in this order unless a proof exposes a soundness gap:

1. **Captured closure call bridge.**
   Implement the Stage 7a bridge for only:

   ```coq
   ECallExpr (EMakeClosure fname captures) args
   ```

   Use the existing captured-call sidecar package and connect it to:

   ```coq
   eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased
   ```

   The immediate blocker is constructing:

   ```coq
   captured_call_frame_ready env captured Rcap s_args R_args
   ```

   for the store copied by `copy_capture_store_as`.

2. **Capture-reference-free Prop mirror.**
   Keep the Prop mirror structural, matching `capture_ref_free_ty_b`.
   Then prove:

   - `capture_ref_free_ty_b` sound into the Prop mirror;
   - values typed at that Prop have empty runtime roots, without first trying
     to prove that `ty_compatible` preserves the Prop on the actual type;
   - exact capture copy yields `captured_store_runtime_ready` for the copied
     hidden capture store.

   Current progress: `capture_ref_free_ty` and
   `capture_ref_free_ty_b_sound` exist, and the Prop no longer has broad
   compatibility/usage constructors. `runtime_rootless_ty` exists in
   `TypeSafety.v`, its struct case factors instantiated fields through
   `runtime_rootless_fields`, executable `capture_ref_free_ty_b` checks imply it,
   lifetime-equivalence preserves it, and
   `ty_compatible_runtime_rootless_actual` handles compatibility without
   broadening `capture_ref_free_ty`. Do not reintroduce a constructor like
   `CRFT_CompatibleActual`: it is too strong for function argument
   contravariance and `TC_Fn_Closure`.

   Current proof endpoint: `value_has_type_runtime_rootless_empty_roots` proves
   runtime-rootless typed values fit in the empty root set, including
   `VHT_Compatible` and `VHT_LifetimeEquiv`.

   Current captured-store endpoint:
   `copy_capture_store_as_captured_store_runtime_ready` constructs
   `empty_root_env_for_store captured` as `Rcap` and proves exact capture copy
   yields `captured_store_runtime_ready`.

   Current captured-frame endpoint:
   `copy_capture_store_as_captured_call_frame_ready` proves exact capture copy
   can be composed with evaluated preservation-ready arguments using
   `captured_call_frame_ready_compose`, with `Rcap` fixed to
   `empty_root_env_for_store captured`.

3. **Argument/capture frame composition.**
   The local composition bridge is now in place:

   - `preservation_ready_eval_store_names_mutual` proves preservation-ready
     argument evaluation does not add store names;
   - `check_make_closure_captures_exact_sctx_params_fresh_in_store` proves
     exact hidden capture parameter names are absent from the caller store;
   - `eval_make_closure_exact_captured_call_frame_params_ready_auto` and
     `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto`
     expose the bridge without an external `captured_call_frame_ready` premise.
   - `captured_call_callee_body_root_shadow_provenance_instantiated_bridge`
     and its `_with_result_subset` variant instantiate captured callee body
     summaries once the target runtime root environment is supplied.

   Next implementation task: prove the runtime root-environment equivalence for
   captured calls:

   ```coq
   call_param_root_env (fn_params fcall) arg_roots
     (empty_root_env_for_store captured ++ R_args)
   ```

   must correspond to instantiating
   `initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)` with
   normal argument roots for params and empty roots for captures, after
   alpha-renaming params. Then call the instantiated bridge and the automatic
   cleanup wrapper from the captured-call sidecar summary.

4. **Final captured-call executable endpoint.**
   Add the checked-initial wrapper for:

   ```coq
   check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
   ```

   Do not widen validators beyond the existing
   `ECallExpr (EMakeClosure fname captures) args` sidecar shape before this
   theorem exists.

5. **Handle `if` last.**
   The known `if` blocker is that ordinary `TES_If` does not expose
   `root_env_equiv R2 R3`, while root/shadow routes require it. Do not
   strengthen `TES_If` or ordinary checker acceptance just to manufacture
   root/shadow sidecar evidence.

## Current Captured Closure Facts

Detailed notes are in `plan/type_safety_closure_notes.md`. Active facts needed
for the next task:

- `TClosure` is distinct from `TFn`.
- `EMakeClosure fname captures` exists for immutable unrestricted
  reference-free captures.
- `fn_def` has separate `fn_params` and `fn_captures`.
- Function bodies use:

  ```coq
  fn_body_ctx f = params_ctx (fn_params f ++ fn_captures f)
  ```

- Direct `EFn` and direct `ECall` remain empty-capture only.
- Captured-call sidecar evidence exists for exactly
  `ECallExpr (EMakeClosure fname captures) args`.
- Captured callee summaries expose `NoDup` for:

  ```coq
  ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))
  ```

- The rejected route, "`ty_compatible Ω T_actual T_expected` plus
  `capture_ref_free_ty T_expected` implies `capture_ref_free_ty T_actual`",
  fails for function argument contravariance and `TC_Fn_Closure`. The next
  route must prove root emptiness from `value_has_type` directly.

## Fixed Boundaries

- Big-step preservation comes before progress.
- Progress is deferred until a future small-step semantics exists.
- The ordinary checker remains the primary accepted-program interface.
- Root provenance is a sidecar API, not the language definition.
- Do not prove ordinary safety by making the root checker stricter than the
  ordinary checker.
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
- let-local reference escape;
- `replace p e_new` target self-use and alias/borrow variants.

## Sub-Agent Policy

Follow `plan/implementation.md`.

Use sub-agents only for implementation-only work. Before spawning a sub-agent,
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
