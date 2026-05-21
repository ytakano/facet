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

- The strongest checked-initial safety endpoint for local captured closure
  calls is:

  ```coq
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready
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

Work in this order unless a proof exposes a soundness gap.

1. **Add the annotated local-let captured-call sidecar branch.**

   Target shape:

   ```coq
   ELet m x T (EMakeClosure fname captures)
     (ECallExpr (EVar x) args)
   ```

   TypeSafety bridge status: done.

   Checked-in preservation bridge:

   ```coq
   eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components
   ```

   The bridge packages the hidden closure binding, evaluated arguments,
   copied captures, alpha-renamed callee body evidence, and hidden-frame
   cleanup. It proves final store typing and return value typing for the
   annotated local-let shape above.

   Supporting cleanup endpoint:

   ```coq
   eval_let_make_closure_captured_call_hidden_cleanup_package
   ```

   Required executable guards:

   - `ident_eqb x y` for the callee variable;
   - `usage_eqb (ty_usage T) UUnrestricted`;
   - `x` not in `captures`;
   - `x` not in `args_free_vars_ts args`;
   - `x` not in `args_local_store_names args`;
   - `preservation_ready_args_b args`;
   - exact capture check with `check_make_closure_captures_exact_sctx`;
   - existing captured callee summary.

   Current implementation status:

   - `local_captured_call_target_expr` recognizes the annotated local-let
     shape and checks the syntactic freshness guards. Its soundness helper is
     in `EnvRuntimeSafety.v`.
   - `check_fn_root_shadow_captured_call_provenance_summary` now has the
     annotated local-let captured-call branch.
   - The branch uses two synthetic checks:
     - direct synthetic body:
       `ECallExpr (EMakeClosure fname captures) args`, used to extract
       `typed_args_roots ... args (fn_params fcallee) ...` in the original
       caller context;
     - let synthetic body:
       `ELet m x T (EMakeClosure fname captures)
          (ECallExpr (EMakeClosure fname captures) args)`, used to prove the
       local binding `x` is fresh for the initial root/store frame.
   - The final captured-call checked-initial safety theorem has the local-let
     branch wired through
     `eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components`.

   Next proof task:

   - Add focused regression examples for the local-let captured-call sidecar if
     future changes touch this checker branch.
   - Then move to the next staged closure shape, or start the TypeSafety file
     split below.

   Do not add `ELetInfer` support in the same step.

2. **Handle `if` last.**

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

## TypeSafety.v Split Plan

`rocq/theories/TypeSystem/TypeSafety.v` is large enough that new closure work
should stop growing it indefinitely. Do not do a broad file split while the
local-let captured closure bridge is unstable.

Short-term rule:

- Keep the local-let captured closure bridge in `TypeSafety.v` while the
  checker sidecar is being wired, so theorem references stay local and easy to
  inspect.
- Avoid moving existing lemmas while changing proof statements.
- If adding clearly independent root facts, prefer statements that can later
  move as a batch.

The first split batch is done:

- `TypeSafetyRootFacts.v` now holds root/value rootless facts that are
  frame-independent and broadly reused.
- `TypeSafety.v` exports `TypeSafetyRootFacts`, so downstream modules that
  import `TypeSafety` still see the moved names.

The second split batch is done:

- `TypeSafetyHiddenFrame.v` now holds the first hidden-frame support batch:
  root/store append facts, captured frame readiness, empty capture root
  environments, copied-capture rootless/runtime-ready facts, and captured
  frame store typing facts.
- It also holds the primitive hidden `store_add` stripping support batch:
  store-add lookup/update inversion facts, root-reference exclusion
  preservation for store operations, and `eval_place_store_add_strip`.
- `TypeSafetyReadiness.v` holds preservation-readiness predicates and the
  store-name preservation facts used by hidden-frame stripping.
- `TypeSafetyHiddenFrame.v` now holds the readiness-dependent hidden-frame
  mutual strip batch, from `args_free_vars_ts` through
  `eval_let_make_closure_captured_call_args_strip`.
- `TypeSafetyHiddenFrame.v` now also holds the parameter freshness facts used
  by captured-call alpha-renaming and exact capture checking.
- `TypeSafetyHiddenFrame.v` now holds the frame-scope foundation batch:
  argument value typing, parameter prefix/scope, hidden frame scope, frame
  static freshness, and update/remove preservation facts through
  `store_frame_scope_no_local_under_params`.
- `TypeSafety.v` exports `TypeSafetyHiddenFrame`, so downstream modules that
  import `TypeSafety` still see the moved names.

Continue splitting in small batches:

1. Create focused files and update `rocq/_CoqProject` in the same commit.
2. Preferred targets:
   - `TypeSafetyHiddenFrame.v`: move the remaining hidden-frame cleanup and
     erasure facts in separate small batches.
   - `TypeSafetyClosure.v`: captured store/frame readiness and captured closure
     call preservation bridges.
3. Move lemmas only when dependencies are clear. After each batch run:

   ```sh
   cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeSafety.v
   ```

4. Keep public theorem names stable unless every caller is updated in the same
   commit.

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
