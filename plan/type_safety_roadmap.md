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

- The elaborated checked-initial endpoint for inferred local-let captured
  closure calls is:

  ```coq
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready
  ```

- Initial runtime readiness is still an execution-state premise, currently via
  `check_initial_root_runtime_ready`. It is not a program acceptance condition.
- Ordinary checker acceptance still exceeds validator acceptance.
- Direct `ECall` and syntactic `ECallExpr (EFn fname) args` are handled by
  localized sidecar routes. Do not add direct calls to ordinary expression
  readiness.
- General `ECallExpr callee args` remains staged. Non-capturing function
  values, immutable-copy captured closures, ordinary checker support for
  callable shared-reference captured closures, and captured-call sidecar
  support for nonzero-lifetime copied shared-reference captures are in place
  for both direct make-closure calls and annotated local-let calls. Mutable and
  affine/linear captures remain later work.

## Next Implementation Order

Work in this order unless a proof exposes a soundness gap.

1. **Keep captured-reference sidecar widening stable.**

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
   - The direct captured-call proof now consumes
     `check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
     (fn_captures fdef) = infer_ok (env_lt, captured_tys)`.
   - The direct proof carries `capture_store_root_env captured` and
     `capture_store_root_sets captured` through body instantiation,
     root-exclusion, and cleanup without collapsing copied capture roots to
     `repeat []`.
   - The direct captured-call sidecar checker branch now uses
     `check_make_closure_captures_exact_sctx_with_env`.
   - The captured-call exact sidecar evidence now carries a separate returned
     root bound. Direct/provenance evidence returns its typed roots, `if`
     evidence unions branch returned roots, and captured-call evidence returns
     the typed call roots unioned with a static capture bound.
   - The direct captured-call sidecar checker branch now requires
     `capture_root_bound R captures (fn_captures fcallee) = Some _` before it
     accepts captured-call evidence. This keeps the static sidecar evidence
     from accepting copied-reference captures whose source roots are absent
     from the caller root environment.
   - The static/runtime capture-root bound is now proved:

     ```coq
     capture_store_root_sets_bound_from_capture_root_bound
     ```

     It relates `copy_capture_store_as`, `store_roots_within R s`, and
     `capture_root_bound R captures caps = Some capture_roots` to
     `root_set_stores_subset (root_sets_union
     (capture_store_root_sets captured)) capture_roots`.

   Completed package support:

   - The captured-call body cleanup core now exposes the body returned-root
     fact:

     ```coq
     value_roots_within roots_body ret
     ```

     The expression cleanup wrapper also carries that fact through its
     package. Compatibility wrappers still project the older store/value
     surface.
   - Hidden-frame cleanup now propagates returned-root evidence through the
     subset bound used by local-let captured calls.
   - The annotated local-let captured-call preservation core now exposes an
     existential copied-capture package with final `store_roots_within`,
     returned `value_roots_within`, `store_no_shadow`, and
     `root_env_no_shadow`. The public compatibility wrapper still projects the
     older store/value surface.
   - The subset bridge exists as
     `captured_call_callee_body_root_shadow_provenance_instantiated_bridge_with_result_subset`
     and is used by the captured-call make/let routes. It relates the
     instantiated body returned roots to the argument/captured-store root
     union needed by the direct with-env captured-call path.

  Exact local-let evidence status:

   - The exact `ELet` sidecar constructor is in place for the annotated
     local-let captured-call shape.
   - Its eval package uses the local-let copied-capture package plus
     `capture_store_root_sets_bound_from_capture_root_bound` to weaken returned
     roots from copied capture roots to the static `capture_root_bound`.
   - The executable expression checker has the matching exact local-let branch,
     guarded by exact capture checking, static capture-root bounds, hidden
     binding freshness, direct synthetic-call compatibility, and returned type
     compatibility.

   Annotated local-let captured-call route:

   - Do not try to coerce canonical shared-reference captures back into
     `captured_call_frame_ready`. The canonical root env is intentionally
     frame-relative.
   - The annotated-local-let runtime helper now roots the hidden closure
     binding as
     `root_env_add x (root_sets_union (capture_store_root_sets captured))
     R_args`.
   - The hidden-frame cleanup path proves returned-value safety directly from
     `roots_body`, `roots_exclude_params`, and `roots_exclude x roots_body`
     instead of requiring the whole body root env to exclude callee
     params/captures. This keeps the inaccessible hidden `x` binding rooted
     without making it an ordinary tail entry.
   - The annotated local-let sidecar checker branch now uses
     `check_make_closure_captures_exact_sctx_with_env`.
   - The captured-call runtime helper API now carries the call-site lifetime
     substitution `σ`, accepts arguments typed against
     `apply_lt_params σ (fn_params fdef)`, and returns
     `value_has_type ... (apply_lt_ty σ (fn_ret fdef))`. Existing zero-lifetime
     wrapper routes instantiate this with `[]`.
   - The root/shadow structural rules, alpha-renaming support, executable root
     checkers, root soundness proofs, direct exact sidecar evidence, eval
     packages, checked-initial captured safety theorem, and function-level
     sidecar checker now carry the same `σ` for direct
     `ECallExpr (EMakeClosure fname captures) args`.
   - The annotated local-let exact sidecar evidence no longer requires
     `fn_lifetimes fcallee = 0`. It carries the direct synthetic call return
     type and proves compatibility from that instantiated type to the final
     local-let type.
   - `TypeChecker.v` has a direct sidecar regression for a nonzero-lifetime
     copied shared-reference capture:

     ```coq
     shared_ref_capture_direct_call_sidecar_accepts
     shared_ref_capture_local_let_call_sidecar_accepts
     ```

   Still required:

   - Keep closure-call lifetime instantiation local to the
     `TForall ... TClosure` call path. Do not silently erase helper function
     lifetimes or make closure calls ordinary direct-call evidence.
   - Keep `tests/valid/closure/capture_shared_ref.facet` as the surface
     regression that constructs and calls a shared-reference closure.
   - Keep the invalid fixtures for missing outlives support, mutable binding
     capture, and `&mut` capture rejection.
   - Keep closure-call validator expansion staged by proof coverage. The direct
     captured-call and annotated local-let routes are now with-env.

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
   - exact capture check with `check_make_closure_captures_exact_sctx_with_env`;
   - existing captured callee summary.

  Current implementation status:

  - `local_captured_call_target_expr` recognizes the annotated local-let
     shape and checks the syntactic freshness guards. Its soundness helper is
     in `EnvRuntimeSafety.v`.
  - `expr_root_shadow_captured_call_provenance_summary_exact` has an
     `ERSCE_LocalCapturedLet` constructor for the exact annotated shape.
  - `check_fn_root_shadow_captured_call_provenance_summary` now has the
     annotated local-let captured-call branch.
  - `check_expr_root_shadow_captured_call_provenance_summary_fuel` now has the
     corresponding exact expression branch used by `if` and expression-level
     sidecar evidence.
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

   Inferred local-let status:

   - Core `ELetInfer` still has no `Eval_LetInfer`, and
     `preservation_ready_expr_b` continues to reject it.
   - Inferred local-let coverage is routed through elaboration instead:
     `infer_program_env_alpha_elab` rewrites successful `ELetInfer` bodies
     into annotated `ELet` bodies before the captured-call sidecar runs.
   - `check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary`
     is the executable wrapper for that route. Its readiness bridge in
     `EnvRuntimeSafety.v` exposes the captured-call summary evidence for the
     elaborated environment returned by `infer_program_env_alpha_elab`.
   - The checked-initial safety theorem for this route evaluates functions in
     the elaborated environment returned by `infer_program_env_alpha_elab`;
     it does not claim semantics preservation for the original `ELetInfer`
     source body.
   - `TypeChecker.v` has a focused example for the inferred local-let captured
     closure call: the original core shape is not accepted by the direct
     captured-call summary, while the elaborated route is accepted.

3. **Handle `if` last.**

   The known `if` blocker is that ordinary `TES_If` does not expose
   `root_env_equiv R2 R3`, while root/shadow routes require it. Do not
   strengthen `TES_If` or ordinary checker acceptance just to manufacture
   root/shadow sidecar evidence.

   Current staged implementation:

   - `TypeChecker.v` has a fuel-aligned internal expression helper,
     `check_expr_root_shadow_captured_call_provenance_summary_fuel`, plus the
     existing 10000-fuel public wrapper
     `check_expr_root_shadow_captured_call_provenance_summary`. This avoids
     manufacturing branch evidence from fresh top-level fuel when proving an
     enclosing `if`.
   - `EnvRuntimeSafety.v` keeps the older unindexed Prop evidence shape and
     now also has exact, output-indexed evidence:

     ```coq
     expr_root_shadow_captured_call_provenance_summary_exact
     ```

     The exact `if` constructor carries the same branch typings, merge, and
     root equivalence as `TERS_If`.
   - Checker soundness from the fuel-aligned helper to the exact evidence is
     in place. The function-level captured-call summary checker now has an
     `EIf` branch guarded by the exact expression helper, return
     compatibility, and parameter root-exclusion checks.

   Remaining proof task:

   - A focused captured-call preservation helper now exists:

     ```coq
     eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components
     ```

     It consumes the full shadow-safe typing judgment for
     `ECallExpr (EMakeClosure fname captures) args`, extracts typed argument
     roots internally, and reuses the with-env captured-call wrapper. This
     removes the captured-branch argument-root extraction from the eventual
     `if` proof body.
   - The exact arbitrary-branch preservation bridge now exists:

     ```coq
     eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing
     ```

     It evaluates the condition with ordinary provenance readiness, carries
     store/root/name/key invariants into the selected branch, and reuses the
     direct/captured-call wrappers under branch `R1`/`Σ1`.
   - The exact package bridge now exists:

     ```coq
     eval_expr_root_shadow_captured_call_provenance_summary_exact_package
     ```

     It exposes final store typing, return typing, final store roots, returned
     roots, final store no-shadow, and final root-env no-shadow. The exact
     `if` evidence carries syntactic branch root-env equality from
     `root_env_eqb`, which is stronger than the semantic equivalence needed by
     `TERS_If`.
   - The final captured-call checked-initial safety theorem now has an `if`
     summary case that delegates to
     `eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing`.

  Next proof task:

   - Do not add broader expression forms unless their package preservation
     route is already covered. The exact annotated local-let captured-call
     route is now wired through expression-level and checked-initial safety.

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

Use sub-agents only for design or implementation-only work. Before spawning a
sub-agent, state why the task is design or implementation-only.

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
