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
- General `ECallExpr callee args` remains staged. Non-capturing function
  values, immutable-copy captured closures, and ordinary checker support for
  callable shared-reference captured closures are in place. Runtime sidecar
  evidence for captured references still comes next; mutable and affine/linear
  captures remain later work.

## Next Implementation Order

Work in this order unless a proof exposes a soundness gap.

1. **Resolve the Stage 7b captured-reference runtime-root invariant.**

   Core status: ordinary `EMakeClosure` capture checking now accepts
   immutable unrestricted shared-reference values, rejects mutable bindings
   and non-unrestricted captures, infers the closure env lifetime by searching
   captured shared-reference lifetimes, and still keeps exact sidecar capture
   validators reference-free. The Prop typing, executable checker, checker
   soundness, structural typing, alpha-renaming, and env typing soundness paths
   support calling `TForall ... (TClosure env_lt params ret)` by instantiating
   unresolved closure lifetimes from the enclosing lexical lifetime context.

   Surface status: raw closure elaboration now inherits the enclosing lifetime
   context for synthetic closure helper functions. Surface shared-reference
   closure literals can be constructed and called by the ordinary checker.

   Implemented proof support:

   - Sidecar-only exact capture checking with closure-env lifetime evidence is
     in place:

     ```coq
     check_make_closure_captures_exact_sctx_with_env
     ```

   - Copied capture root construction and frame-relative captured-frame
     readiness helpers are in place, including:

     ```coq
     copy_capture_roots_as
     capture_value_roots
     capture_store_root_sets
     capture_store_root_env
     captured_call_frame_ready_in_frame
     captured_call_frame_params_ready_in_frame
     copy_capture_store_exact_with_env_params_store_typed_in_frame
     copy_capture_store_as_captured_values_canonical_roots_with_env
     copy_capture_store_as_captured_store_runtime_ready_in_frame_with_env
     captured_call_bind_params_call_param_root_env_ready_in_frame
     captured_call_frame_args_values_have_types_in_frame
     eval_make_closure_exact_captured_call_frame_params_ready_auto_with_env
     eval_make_closure_captured_call_runtime_args_ready_in_frame_core
     eval_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_core
     captured_call_binding_runtime_root_env_equiv_with_roots
     copy_capture_roots_as_equiv_root_env_add_params_roots
     capture_store_root_env_equiv_root_env_add_params_roots
     ```

   Resolved runtime-root invariant:

   - Stage 7b now uses canonical copied capture roots derived from copied
     runtime values, not arbitrary caller root-env entries.
   - Ref-free captured values use `[]`; shared-reference captured values use the
     singleton store root from the copied `VRef`.
   - This avoids the prior over-approximation gap where source root-env entries
     could mention roots no longer named after argument evaluation.

   Progress in current slice:

   - The captured-call body cleanup bridge now accepts
     `captured_call_frame_ready_in_frame` through in-frame parameter readiness.
     Existing reference-free wrappers still accept `captured_call_frame_ready`
     via the existing self-to-in-frame coercions.
   - The direct captured-call proof now routes through the in-frame cleanup
     path and uses canonical-root helper plumbing internally. However, the
     public direct theorem still consumes
     `check_make_closure_captures_exact_sctx` and derives the with-env helper
     only for the reference-free `LStatic` case.

   Next implementation task:

   - Strengthen the direct captured-call theorem so its public premise is
     `check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
     (fn_captures fdef) = infer_ok (env_lt, captured_tys)`.
   - Remove the remaining reference-free fallback facts from the direct proof,
     especially the path that proves copied capture root sets collapse to
     `repeat []`.
   - Carry `capture_store_root_env captured` and `capture_store_root_sets
     captured` through body instantiation, root-exclusion, and cleanup without
     requiring rootless captured values.
   - Only after that strengthened direct theorem compiles, replace the direct
     captured-call sidecar checker branch with
     `check_make_closure_captures_exact_sctx_with_env`.

   Blocker found:

   - Do not try to coerce canonical shared-reference captures back into
     `captured_call_frame_ready`. The canonical root env is intentionally
     frame-relative.
   - Do not widen the direct checker sidecar while the public direct theorem
     still exposes `check_make_closure_captures_exact_sctx`; that path remains
     reference-free even though it uses the in-frame cleanup bridge internally.
   - Do not widen the annotated local-let branch to with-env captures yet. Its
     hidden closure binding is currently rooted as `root_env_add x [] R_args`;
     shared-reference captures require either a new hidden-closure root
     invariant or a different root assignment for `x`.

   Still required after the invariant is fixed:

   - Keep closure-call lifetime instantiation local to the
     `TForall ... TClosure` call path. Do not silently erase helper function
     lifetimes or make closure calls ordinary direct-call evidence.
   - Keep `tests/valid/closure/capture_shared_ref.facet` as the surface
     regression that constructs and calls a shared-reference closure.
   - Keep the invalid fixtures for missing outlives support, mutable binding
     capture, and `&mut` capture rejection.
   - Do not widen executable sidecar validators or captured-call routes until
     the captured-call preservation theorem is rewired to canonical capture
     roots and compiles.

2. **Keep the annotated local-let captured-call sidecar branch stable.**

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

   Focused regressions are done:

   - `TypeChecker.v` checks that the ordinary checker accepts the local-let
     captured-call shape, direct/non-capturing sidecars reject it, and the
     captured-call sidecar accepts it.
   - `tests/valid/closure/capture_unrestricted_annotated_let_call.facet`
     covers the annotated surface local-let shape.

   Next proof task:

   - Do not add `ELetInfer` captured-call support in the same step. The current
     operational semantics has no `Eval_LetInfer`, so existing `ELetInfer`
     preservation is vacuous by inversion on evaluation.
   - If widening captured-call sidecar coverage, first add an operational
     semantics case or choose an already-evaluable surface shape.

3. **Handle `if` last.**

   The known `if` blocker is that ordinary `TES_If` does not expose
   `root_env_equiv R2 R3`, while root/shadow routes require it. Do not
   strengthen `TES_If` or ordinary checker acceptance just to manufacture
   root/shadow sidecar evidence.

## Current Captured Closure Facts

Detailed notes are in `plan/type_safety_closure_notes.md`. Active facts needed
for the next task:

- `TClosure` is distinct from `TFn`.
- `EMakeClosure fname captures` exists for immutable unrestricted
  reference-free captures and currently types as a `TClosure`.
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

## TypeSafety Module Ownership

The TypeSafety split is complete enough for the current roadmap. Do not start
another file-splitting batch just because a file is large. Move existing lemmas
only when a new proof requires a clear dependency boundary, or when compile-time
measurement identifies a concrete bottleneck.

Going forward:

- Add new direct-call helper facts and route cores to the focused direct-call
  modules, with public wrappers in `TypeSafetyDirectCallWrappers.v`.
- Add new captured-call helper facts and route cores to
  `TypeSafetyCapturedCall.v`, `TypeSafetyClosureRuntimeArgs.v`, or the closure
  cleanup modules according to the ownership list below.
- Keep public theorem names visible through `TypeSafety.v`, but add wrappers to
  focused `*Wrappers.v` files instead of growing `TypeSafety.v`.
- Keep proof statements stable unless the active implementation task requires a
  theorem-strengthening step.

Completed ownership:

- `TypeSafetyRootFacts.v` now holds root/value rootless facts that are
  frame-independent and broadly reused.
- `TypeSafety.v` exports `TypeSafetyRootFacts`, so downstream modules that
  import `TypeSafety` still see the moved names.
- `TypeSafetyHiddenFrameBase.v` now holds the first hidden-frame support batch:
  root/store append facts, captured frame readiness, empty capture root
  environments, copied-capture rootless/runtime-ready facts, and captured
  frame store typing facts.
- It also holds the primitive hidden `store_add` stripping support batch:
  store-add lookup/update inversion facts, root-reference exclusion
  preservation for store operations, and `eval_place_store_add_strip`.
- `TypeSafetyReadiness.v` holds preservation-readiness predicates and the
  store-name preservation facts used by hidden-frame stripping.
- `TypeSafetyHiddenFrameStrip.v` now holds the readiness-dependent hidden-frame
  mutual strip batch, from `args_free_vars_ts` through
  `eval_let_make_closure_captured_call_args_strip`.
- `TypeSafetyCallFrame.v` now holds call-frame/root-env foundations from
  `params_fresh_in_store` through `call_param_root_env_no_shadow`, including
  parameter freshness, argument value typing, bind-params facts,
  `store_param_prefix`, `root_env_add_params_roots`, `root_env_remove_params`,
  `call_param_root_env`, tail-frame freshness, and shadow-safe tail-frame
  helpers.
- `TypeSafetyFrameScope.v` now holds the frame-scope foundation batch:
  `store_param_scope`, hidden frame scope, frame static freshness, and
  update/remove preservation facts through
  `store_frame_scope_no_local_under_params`.
- `TypeSafetyProvenanceReady.v` now holds the readiness-to-provenance bridge
  `preservation_ready_implies_provenance_ready*`, the local eval induction
  scheme, runtime provenance-readiness preservation, and root-exclusion facts
  through `store_roots_exclude_root`.
- `TypeSafetyRootEnvParams.v` now holds root-env covers/excludes helpers,
  captured-call runtime root-env composition facts, and params exclusion facts
  through `call_param_root_env_excludes_params`.
- `TypeSafetyRootsReady.v` now holds the roots-ready support batch:
  direct-place lookup helpers, root/store/ctx named facts, provenance
  readiness, `typed_fields_roots_cons_inv_ts`, typed roots named/key named
  mutual facts, `eval_preserves_roots_ready_mutual`, and the parameterized
  prefix wrapper core
  `eval_preserves_roots_ready_prefix_mutual_with_preservation_core`.
  `TypeSafety.v` keeps the public `eval_preserves_roots_ready_prefix_mutual`
  theorem and passes `eval_preserves_typing_ready_prefix_mutual` into the core.
- `TypeSafetyParamScopeReady.v` now holds param-scope roots-ready
  preservation through `eval_preserves_param_scope_roots_ready_mutual`.
- `TypeSafetyFrameScopeReady.v` now holds frame-scope roots-ready
  preservation through `eval_preserves_frame_scope_roots_ready_mutual`.
- `TypeSafetyHiddenFrameCleanupFacts.v` now holds the hidden-frame cleanup
  foundation facts through `store_typed_remove_params_store_param_prefix`.
- `TypeSafetyHiddenFrame.v` is now only an export aggregator for the split
  hidden-frame modules.
- `TypeSafetyClosureRuntimeArgs.v` now holds the first captured-call readiness helper
  batch: bind-params call-root readiness, captured argument value typing, hidden
  closure-frame argument typing, evaluated-argument store-name freshness, and
  `captured_call_frame_ready_store_add_right`.
- `TypeSafetyRootNamed.v` owns the parameterized root-name/key preservation
  cores and the standalone `root_env_store_keys_named_excludes_names` helper.
- `TypeSafetyBasePreservation.v` owns the basic big-step preservation cases
  from `eval_args_preserves_typing` through `eval_letinfer_preserves_typing`.
  It also owns the main preservation core
  `eval_preserves_typing_ready_mutual_core` and the parameterized structural
  endpoint cores
  `typed_fn_env_structural_big_step_safe_ready_with_preservation_core` and
  `checked_fn_env_structural_big_step_safe_ready_with_preservation_core`.
  `TypeSafety.v` exports it through the wrapper modules.
- `TypeSafetyPrefixPreservation.v` owns prefix-preservation cores:
  `eval_preserves_typing_ready_prefix_mutual_core`,
  `eval_preserves_typing_roots_ready_prefix_mutual_core`,
  `eval_preserves_typing_ready_with_call_invariants_mutual_with_preservation_core`,
  and `eval_let_roots_ready_preserves_typing_with_preservation_core`.
  `TypeSafetyPreservationWrappers.v` keeps the public theorem names as wrappers.
- `TypeSafetyRootPreservation.v` owns
  `eval_preserves_typing_roots_ready_mutual_core`.
  `TypeSafetyPreservationWrappers.v` keeps the public
  `eval_preserves_typing_roots_ready_mutual` theorem as a wrapper.
- `TypeSafetyPreservationWrappers.v` owns the public preservation wrappers:
  main ready preservation, structural endpoint safety, prefix preservation,
  roots-ready preservation, root-name preservation, and root-key preservation.
- Closure cleanup is split by proof layer:
  `TypeSafetyClosureCleanupFrame.v` owns bind-params cleanup support and the
  frame cleanup cores through
  `eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core`;
  `TypeSafetyClosureCleanupCtxErased.v` owns body-context and hidden-frame
  erased cleanup cores through
  `eval_let_make_closure_captured_call_hidden_cleanup_package_with_preservation_core`;
  `TypeSafetyClosureCleanupCaptured.v` owns captured-call cleanup variants
  through
  `eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased_with_preservation_core`;
  `TypeSafetyClosureCleanupMakeClosure.v` owns make-closure captured cleanup
  cores through
  `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto_with_preservation_core`.
  `TypeSafetyClosureCleanup.v` is now only an export aggregator, and
  `TypeSafetyClosureWrappers.v` keeps the public wrappers that pass the main
  preservation, frame-scope, prefix-typing, and param-scope facts into these
  cores.
- `TypeSafetyClosureRuntimeArgs.v` now holds the captured runtime-readiness helper batch:
  copied-capture frame readiness, exact captured frame params readiness, and
  the non-hidden/hidden runtime-args readiness cores used by
  `eval_make_closure_captured_call_runtime_args_ready_auto` and
  `eval_let_make_closure_captured_call_runtime_args_ready_auto`.
- `TypeSafetyClosureRuntimeArgs.v` now also holds the parameterized captured
  runtime-args wrapper cores:
  `eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core`
  and
  `eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core`.
  `TypeSafetyClosureWrappers.v` keeps the public wrappers and passes the main
  preservation, root-name, and root-key mutual theorems into the cores.
- `TypeSafetyClosure.v` is now only an export aggregator for
  `TypeSafetyClosureRuntimeArgs.v` and `TypeSafetyClosureCleanup.v`.
- `TypeSafetyDirectCallSetup.v` now holds direct-call statement definitions,
  function-env uniqueness and lookup helpers, and setup facts through
  `lookup_fn_in_unique_by_name`.
- `TypeSafetyDirectCallBody.v` now holds direct-call body/prefix/cleanup and
  fresh-args helper cores through
  `eval_args_root_sets_union_excludes_fresh_name_with_preservation_core`.
- `TypeSafetyDirectCallEvidence.v` now holds direct-call callee evidence
  definitions and summary bridge cores through
  `direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique_with_preservation_core`.
- `TypeSafetyDirectCallRoute.v` now holds direct-call route cores,
  `eval_call_expr_fn_as_call`, and the callee-summary route core.
- `TypeSafetyDirectCall.v` is now only an export aggregator for the split
  direct-call modules. `TypeSafetyDirectCallWrappers.v` keeps the public
  direct-call wrappers and passes the main preservation, root-name, root-key,
  frame-scope, prefix-typing, and param-scope preservation mutual theorems into
  the cores.
- `TypeSafetyCapturedCall.v` now holds the captured callee evidence
  instantiation batch:
  `captured_call_callee_body_root_shadow_provenance_instantiated_bridge`,
  `captured_call_callee_body_root_shadow_provenance_instantiated_bridge_with_result_subset`,
  and
  `captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame`.
  It also owns the captured-call alpha-renaming binding initial support facts.
  It also owns parameterized captured-call preservation bridge cores:
  `eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body_with_preservation_core`,
  `eval_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core`,
  and
  `eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core`.
  `TypeSafetyClosureWrappers.v` keeps the public captured-call preservation
  bridge wrappers and passes the main preservation, root-name, root-key,
  frame-scope, prefix-typing, and param-scope preservation mutual theorems into
  the cores.
- `TypeSafetyDirectPlace.v` now owns direct-place runtime target, runtime path
  lookup, and copy/move contradiction helpers.
- `TypeSafetyLocalFacts.v` now owns the early local-shadow, nil-lifetime, and
  root subset helper facts through `value_roots_exclude_root_stores_subset`.
- `TypeSafety.v` is now an export aggregator. It exports the focused proof
  modules plus `TypeSafetyPreservationWrappers.v`,
  `TypeSafetyClosureWrappers.v`, and `TypeSafetyDirectCallWrappers.v`, so
  downstream modules that import `TypeSafety` still see the public theorem
  names.

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
