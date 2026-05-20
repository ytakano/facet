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

Work in this order unless a proof exposes a soundness gap:

1. **Captured closure call bridge.** Done.
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
   - `captured_call_frame_root_tail_fresh_names_for_fresh_call` proves the
     copied-capture/runtime-argument frame can be used as a tail frame for the
     alpha-renamed callee body.
   - `captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame`
     exposes the TypeSafety-side bridge without depending on
     `EnvRuntimeSafety.v` summary predicates.

   Next implementation task: in `EnvRuntimeSafety.v`, destruct the captured
   sidecar summary, pass the callee-body components to the TypeSafety-side
   tail-frame bridge, then call the automatic cleanup wrapper. The runtime root
   environment is:

   ```coq
   call_param_root_env (fn_params fcall) arg_roots
     (empty_root_env_for_store captured ++ R_args)
   ```

   Treat this as instantiating params with `arg_roots`, captures with empty
   roots, then tail-framing over the copied-capture/argument root environment.

   Current progress: the runtime argument/captured-frame package now has
   TypeSafety-side helpers:

   - `captured_call_bind_params_call_param_root_env_ready`;
   - `captured_call_frame_args_values_have_types`;
   - `captured_call_runtime_root_env_covers_params_captures`;
   - `eval_make_closure_captured_call_runtime_args_ready_auto`;
   - `eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body`;
   - `alpha_rename_params_initial_root_env_rename_stable_tail_ts`;
   - `alpha_rename_fn_def_binding_initial_support_facts`;
   - `alpha_rename_fn_def_binding_params_alpha_ts`;
   - `empty_root_env_for_store_params_fresh_lookup_none`;
   - `captured_call_runtime_args_tail_excludes_binding_params`;
   - `captured_call_runtime_args_tail_fresh_names_for_fresh_call`;
   - `empty_root_env_for_captured_params_equiv`;
   - `captured_call_runtime_root_env_binding_split_equiv`;
   - `captured_call_binding_runtime_root_env_equiv`;
   - `apply_lt_ty_nil_ts`;
   - `eval_make_closure_captured_call_expr_preserves_typing_with_callee_components`.

   The last helper is the current stable connection point. It consumes the raw
   callee components stored in
   `callee_body_root_shadow_captured_callee_provenance_summary`, alpha-renames
   and instantiates the callee body at
   `call_param_root_env (fn_params fcall) arg_roots
   (empty_root_env_for_store captured ++ R_args)`, packages runtime args,
   copied captures, frame coverage, cleanup, and final value typing.

   Completed proof subtask: the root-env equivalence between binding
   instantiation and the copied-capture base frame is now available as
   `captured_call_binding_runtime_root_env_equiv`:

   ```coq
   root_env_equiv
     (call_param_root_env (fn_params fcall) arg_roots
       (empty_root_env_for_store captured))
     (root_env_instantiate
       (root_subst_of_params
         (fn_params fdef ++ fn_captures fdef)
         (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
       (initial_root_env_for_params_origin
         (fn_params fdef ++ fn_captures fdef)
         (fn_params fcall ++ fn_captures fcall)))
   ```

   This `EnvRuntimeSafety.v` connection is now complete for the direct
   `ECallExpr (EMakeClosure fname captures) args` shape. Do not add more
   captured-call checker branches until a matching TypeSafety-side helper
   exists.

   Important hidden-frame note: the local let form

   ```coq
   ELet m x T (EMakeClosure fname captures)
     (ECallExpr (EVar x) args)
   ```

   cannot be justified from only:

   - `x` not in `captures`;
   - `x` not in `args_local_store_names args`;
   - `x` not in the syntactic free variables of `args`.

   Those conditions rule out direct syntactic access to `x`, but they do not
   rule out an argument dereferencing an existing reference value that points
   to the future hidden binding name `x`. The argument-stripping proof must
   also consume runtime root/alias evidence excluding `x` from the reachable
   argument roots, or otherwise prove from the initial root environment that
   no evaluated argument can reach the hidden binding.

   Current low-level progress for that route: `TypeSafety.v` now has the
   store operation commute/lookup facts needed to factor a fresh hidden
   `store_add` through argument evaluation:

   - `store_lookup_store_add_same`;
   - `store_lookup_store_add_diff`;
   - `store_mark_used_store_add_diff`;
   - `store_update_state_store_add_diff`;
   - `store_update_val_store_add_diff`;
   - `store_update_path_store_add_diff`;
   - `store_restore_path_store_add_diff`.
   - `value_fields_refs_exclude_lookup`;
   - `value_refs_exclude_lookup_ref_neq`;
   - `store_refs_exclude_lookup_ref_neq`;
   - `eval_place_store_add_strip`.
   - `store_update_state_store_add_inv`;
   - `store_update_val_store_add_inv`;
   - `store_update_path_store_add_inv`;
   - `store_restore_path_store_add_inv`;
   - `store_consume_path_store_add_inv`;
   - `value_refs_exclude_lookup_path`;
   - `store_refs_exclude_lookup`;
   - `store_mark_used_refs_exclude_root`;
   - `store_update_state_refs_exclude_root`;
   - `store_restore_path_refs_exclude_root`;
   - `store_consume_path_refs_exclude_root`;
   - `store_update_val_refs_exclude_root`;
   - `value_update_path_refs_exclude_root`;
   - `store_update_path_refs_exclude_root`.
   - `args_free_vars_ts`;
   - `fields_free_vars_ts`;
   - `args_free_vars_ts_cons_notin`;
   - `fields_free_vars_ts_cons_notin`;
   - `args_local_store_names_cons_notin`;
   - `fields_local_store_names_cons_notin`;
   - `lookup_expr_field_in`;
   - `fields_free_vars_ts_lookup_notin`;
   - `fields_local_store_names_lookup_notin`;
   - `store_refs_exclude_lookup_value`;
   - `hidden_frame_eval_strip_mutual`;
   - `preservation_ready_eval_args_hidden_frame_strip`.

   `preservation_ready_eval_args_hidden_frame_strip` is the current stable
   proof endpoint for hidden-frame argument stripping. It relates evaluation
   of preservation-ready args under `store_add x T hidden s` to evaluation over
   `s`, assuming syntactic absence of `x` from free variables/local store names
   and the runtime invariant `store_refs_exclude_root x s`. This runtime
   invariant is the necessary evidence that evaluated args cannot indirectly
   reach the hidden binding through existing references.

4. **Final captured-call executable endpoint.** Done.
   The checked-initial wrapper exists:

   ```coq
   check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
   ```

   It proves safety for the localized
   `ECallExpr (EMakeClosure fname captures) args` sidecar shape by destructing
   the captured summary in `EnvRuntimeSafety.v`, aligning the runtime/typed
   callee via `fn_env_unique_by_name`, and calling
   `eval_make_closure_captured_call_expr_preserves_typing_with_callee_components`.

5. **Next: reduce captured-call validator false negatives.**
   Keep the proof endpoint above stable. Only widen the executable sidecar when
   the new shape has a matching Prop summary and a local proof path to the same
   endpoint. Good next candidates are small structural variants of
   `ECallExpr (EMakeClosure fname captures) args`; do not mix this into
   ordinary expression readiness.

   Do not implement let-bound captured closure values by merely adding a broad
   `value_has_type` constructor for `VClosure fname captured`. Even a mutual
   constructor carrying only "captured entries have their stored types" is not
   enough: it makes existing root facts false. In particular,
   `closure_value_ty fdef captured_tys` currently erases `captured_tys` from the
   type core and only keeps their aggregate usage. Since
   `runtime_rootless_ty` accepts `TFn` without inspecting captured values, a
   captured closure containing references could be typed as a rootless function
   value, contradicting `value_has_type_runtime_rootless_empty_roots_mut`.

   Any future general `VClosure fname captured` route must therefore carry root
   evidence as well as type evidence, or avoid installing it as a global
   `value_has_type` constructor. Acceptable next designs are:

   - proof-local bridge from `Eval_MakeClosure` plus exact copy evidence to the
     captured-call preservation endpoint, without widening global runtime
     typing;
   - a frame/projection theorem for closure results that keeps captured roots in
     the frame instead of requiring `value_roots_within []`;
   - a stronger closure runtime typing predicate whose statement includes both
     captured entry types and captured root bounds, with all rootless lemmas
     updated deliberately.

   The attempted checker shape:

   ```coq
   ELet m x T (EMakeClosure fname captures)
     (ECallExpr (EVar x) args)
   ```

   also needs extra evidence before it can be accepted by the sidecar:

   - `x` is not in `captures`;
   - `x` is not in `args_local_store_names args`;
   - `x` is not in the free variables of `args`;
   - evaluating preservation-ready `args` under `store_add x ... s` is
     equivalent to evaluating them under `s`, up to the final removal of `x`;
   - the call-body proof must not require `store_typed` for
     `store_add x T (VClosure fname captured) s`, because that would require a
     global captured-closure `value_has_type` constructor;
   - alpha-renaming must be shown stable, or frame-insensitive, when the hidden
     let binding `x` appears in the runtime `store_names` used for
     `alpha_rename_fn_def`;
   - the final value excludes `x`, so `store_remove x` preserves its type.

   Until those facts exist, keep the executable captured-call validator limited
   to direct `ECallExpr (EMakeClosure fname captures) args`.

   The safe next proof task is not checker plumbing. First add a TypeSafety-side
   lemma for a proof-local hidden binding frame:

   ```coq
   eval env s
     (ELet m x T (EMakeClosure fname captures)
       (ECallExpr (EVar x) args)) s' v
   ```

   The lemma should destruct the evaluation, use `Eval_MakeClosure` only as
   exact capture-copy evidence, avoid typing the temporary closure binding as a
   normal store entry, and prove the captured-call body cleanup with `x` treated
   as an erased frame name. Only after that helper compiles should
   `check_fn_root_shadow_captured_call_provenance_summary` grow a local-let
   branch.

   Current hidden-frame progress: `TypeSafety.v` has
   `copied_captured_closure_roots_empty`, which derives
   `value_roots_within [] (VClosure fname captured)` from exact capture-copy
   evidence and `captured_store_runtime_ready`, without adding a global
   captured-closure `value_has_type` constructor.

   Current hidden-frame stripping endpoint:

   ```coq
   preservation_ready_eval_args_hidden_frame_strip
   ```

   It proves args-evaluation invariance for preservation-ready args under an
   irrelevant hidden binding, with the required runtime evidence
   `store_refs_exclude_root x s`.

   Current let-bound captured-call progress:

   ```coq
   eval_let_make_closure_captured_call_args_strip
   ```

   This destructs the exact local-let captured-call evaluation shape, treats
   `Eval_MakeClosure` as exact capture-copy evidence, rejects the consuming
   callee-variable path via unrestricted usage, and strips argument evaluation
   from `store_add x T (VClosure fname captured) s` back to `s`. Supporting
   helpers now include `store_refs_exclude_root_app`,
   `store_add_refs_exclude_root`, `bind_params_refs_exclude_root`,
   `store_remove_store_add_same`,
   `store_remove_params_store_add_non_param`,
   `store_remove_hidden_after_params`,
   `store_remove_hidden_after_param_groups`,
   `captured_params_store_typed_remove_hidden_app`, and alpha-renaming
   not-in-used wrappers for renamed params/body locals.

   Current hidden-frame cleanup endpoint:

   ```coq
   eval_captured_call_body_ctx_cleanup_hidden_frame_erased
   eval_let_make_closure_captured_call_hidden_cleanup_package
   ```

   This is the proof-local body cleanup variant for
   `captured ++ store_add x T hidden s_args`. It avoids requiring
   `store_typed` for the temporary closure binding and erases `x` from the
   final store. It now derives return-value reference exclusion from
   `roots_exclude x roots_body`. The `_subset` wrapper additionally accepts
   `root_set_stores_subset roots_body roots_bound` plus
   `roots_exclude x roots_bound`, matching the existing captured-call
   result-subset bridge style.

   `eval_let_make_closure_captured_call_hidden_cleanup_package` is the current
   local-let bridge endpoint. It destructs the stripped local-let evaluation,
   exposes copied captures, evaluated args, alpha-renamed callee components,
   and body evaluation, then provides a continuation that runs the hidden-frame
   cleanup once the caller supplies the callee body typing/root package and a
   root bound excluding `x`.

   Next hidden-frame proof subtask: construct that caller-side package
   automatically for the local-let shape. Reuse the existing captured-call
   instantiated-body helpers, but target
   `captured ++ store_add x T (VClosure fname captured) s_args` and supply a
   `roots_bound` that excludes the hidden name `x`. Do this before adding any
   checker branch.

6. **Handle `if` last.**
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
