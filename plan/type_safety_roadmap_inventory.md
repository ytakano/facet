# Type Safety Detailed Inventory

This file holds historical proof inventory and completed milestone detail that
was split out of `plan/type_safety_roadmap.md`. It is reference material, not
the active implementation queue. For the next task, read the roadmap first.

## Detailed Status Inventory

This section records context and completed proof work. It is intentionally more
verbose than the quick path. Do not use it as the primary implementation order.

1. `[done]` Revert the temporary root-checker restriction on shadowing `let`
   initializers.
   - Target files:
     - `rocq/theories/TypeSystem/EnvStructuralRules.v`
     - `rocq/theories/TypeSystem/TypeChecker.v`
     - `rocq/theories/TypeSystem/EnvRootSoundness.v`
     - `rocq/theories/TypeSystem/TypeSafety.v`
     - regenerated `fixtures/TypeChecker.ml`
     - regenerated `fixtures/TypeChecker.mli` if extraction changes it
   - Removed the conservative `roots_exclude x roots1` premise/check from
     `TER_Let` / `TER_LetInfer` and the executable root checker.
   - Updated the regression example that expected `let x = &x` style
     initializer-root shadowing to be rejected.
   - Preserved the existing let-local escape checks for body results and
     surviving store roots.

2. Add the alpha-first root-evidence bridge.
   - Target files:
     - `rocq/theories/TypeSystem/AlphaRenaming.v`
     - `rocq/theories/TypeSystem/RootProvenance.v`
     - `rocq/theories/TypeSystem/EnvRootSoundness.v`
     - `rocq/theories/TypeSystem/TypeSafety.v`
   - Prove or expose a bridge that root-checks the alpha-renamed/freshened
     expression or function body.
   - The bridge should explain how source checker success maps to root evidence
     on the freshened core term when root evidence is needed.
   - Do not encode this by rejecting valid source shadowing patterns.
   - Do not delegate this step to a sub-agent until the exact theorem statement
     and proof route are fixed; it still requires uncertainty reduction.

3. Continue the ordinary-checker safety theorem.
   - Target files:
     - `rocq/theories/TypeSystem/TypeSafety.v`
     - `rocq/theories/TypeSystem/EnvRuntimeSafety.v`
   - Keep the main theorem focused on ordinary checker success:

     ```coq
     infer_full_env env f = infer_ok (T, Γ')
       -> initial_store_for_fn f s
       -> eval env s (fn_body f) s' v
       -> value_has_type env s' v (fn_ret f).
     ```

   - Use sidecar root evidence only for sublemmas that explicitly require
     reference provenance.
   - Done: added the executable alpha-normalized checker route:
     `alpha_normalize_global_env`, `check_program_env_alpha`, and extracted
     OCaml support. The CLI now checks `env_for_checker`, the alpha-normalized
     global environment, and uses a sidecar diagnostic map only for displaying
     original source names.
   - Done: added normalized structural soundness wrappers:
     `infer_full_env_alpha_structural_sound` and
     `check_program_env_alpha_checked_structural`. These make
     `alpha_normalize_global_env env` the explicit checked environment for the
     ordinary checker route.
   - Done: added normalized root-runtime wrapper theorems:
     `infer_full_env_roots_alpha_big_step_safe_ready` and
     `infer_full_env_roots_alpha_big_step_safe_direct_call_ready`. These expose
     the existing root-based runtime safety theorem over
     `alpha_normalize_global_env env`.
   - Done: added
     `infer_full_env_alpha_big_step_safe_with_root_sidecar`, the current
     intermediate theorem for the ordinary alpha route. It requires ordinary
     checker success on `alpha_normalize_global_env env`, plus explicit root
     sidecar checker success and root-summary evidence. This is not the final
     ordinary-checker-only theorem; it documents the exact sidecar evidence
     still needed by runtime cleanup.
   - Done: added Prop-level direct-call evidence wrappers
     `infer_full_env_roots_big_step_safe_direct_call_evidence` and
     `infer_full_env_roots_alpha_big_step_safe_direct_call_evidence`, plus
     `infer_full_env_alpha_big_step_safe_with_root_summary_bridge`. The alpha
     summary wrapper connects executable root-summary checks to Prop-level
     direct-call root evidence through `direct_call_callee_body_root_summary_bridge`.
   - Done: added the proof-only shadow summary layer and projection bridge in
     `TypeSafety.v`: `callee_body_root_shadow_ready_at`,
     `callee_body_root_shadow_summary`,
     `env_fns_root_shadow_summary_evidence`,
     `env_fns_root_summary_evidence_of_shadow`,
     `direct_call_callee_body_root_shadow_summary_bridge`, and
     `direct_call_callee_body_root_evidence_of_shadow_summary_bridge`. This
     records the shadow-summary route without changing the executable checker.
   - Done: added
     `infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge` in
     `EnvRuntimeSafety.v`, wiring shadow summary evidence into the existing
     direct-call runtime safety route.
   - Done: added the `_of_unique` route
     `direct_call_callee_body_root_shadow_summary_bridge_of_unique` and the
     corresponding `EnvRuntimeSafety.v` convenience wrapper, so preferred
     ordinary-alpha statements can derive direct-call shadow bridge evidence
     from `fn_env_unique_by_name` instead of requiring an explicit
     `direct_call_callee_body_root_shadow_summary_bridge` premise.
   - Done: the preferred ordinary-alpha theorem no longer has entry-level
     `infer_full_env_roots ...` root sidecar checker success as a premise.
     The theorem name is
     `infer_full_env_alpha_big_step_safe_with_shadow_summary_evidence`.
   - Done: added the ordinary structural route wrappers
     `typed_fn_env_structural_big_step_safe_ready`,
     `checked_fn_env_structural_big_step_safe_ready`, and
     `infer_full_env_alpha_big_step_safe_structural_ready`. These connect
     ordinary checker success on alpha-normalized core to structural
     preservation and `value_has_type` for `preservation_ready_expr`, without
     routing through `env_fns_root_shadow_summary_evidence`.
   - Done: added the direct-call sidecar packaging theorem
     `infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready`, plus
     `ordinary_alpha_direct_call_sidecar_ready` and
     `initial_root_runtime_ready_for_fn`. This keeps root/shadow evidence
     local to direct-call cleanup and provenance while avoiding full
     structural-to-shadow-root synthesis as the ordinary route.
   - Done: added the program-level wrapper
     `check_program_env_alpha_big_step_safe_with_direct_call_sidecar_ready`,
     which derives per-function `infer_full_env` success from
     `check_program_env_alpha env = true` and then uses the packaged
     direct-call sidecar theorem.
   - Done: decomposed the packaged direct-call sidecar predicates in
     `EnvRuntimeSafety.v`. `ordinary_alpha_root_shadow_sidecar_ready` now
     isolates root/shadow summary evidence, while
     `ordinary_alpha_direct_call_meta_ready` isolates function-name uniqueness
     and preservation readiness. The compatibility predicate
     `ordinary_alpha_direct_call_sidecar_ready` remains for existing public
     wrappers.
   - Done: added the Rocq-side top-level name validator route:
     `top_level_names_unique_b`, `check_program_env_alpha_validated`, and
     `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_ready`.
     This keeps `check_program_env_alpha` unchanged while letting the
     validated wrapper derive `fn_env_unique_by_name` for the
     alpha-normalized environment.
   - Done: added
     `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_env_ready`,
     which derives per-function direct-call readiness from
     `ordinary_alpha_direct_call_validated_sidecar_ready`, function membership,
     `env_fns_preservation_ready`, and `preservation_ready_direct_call_ready`.
   - Remaining ordinary-safety blocker: under the current ordinary-checker
     contract, root/shadow summary evidence and initial root/runtime readiness
     stay explicit. The validated wrapper absorbs per-function readiness, while
     preservation readiness still enters through the validated sidecar package.
     Reducing the remaining explicit evidence further requires a separate
     validator/theorem, not another proof-only wrapper.
   - Sidecar limitation: ordinary checker success still does not by itself
     produce `env_fns_root_shadow_summary_evidence` for the alpha-normalized
     function environment. Existing facts only project root/shadow-root typing
     to structural typing; full synthesis in the opposite direction remains
     incomplete and is no longer the next task.
   - The `If` branch-root gap belongs to that sidecar synthesis route:
     `TES_If` does not expose the `root_env_equiv R2 R3` evidence required by
     `TERS_If`. This is not a blocker for ordinary structural preservation,
     and the project should not strengthen `TES_If` or checker acceptance just
     to satisfy shadow/root synthesis.
   - Refined sidecar limitation: a general shadow-safe soundness theorem for
     the existing root checker is false for arbitrary core. In `ELet` /
     `ELetInfer`, the checker only tests `root_env_lookup x R1 = None` before
     extending the root environment, plus body-result escape checks. The
     shadow-safe constructors additionally require initializer-side
     `roots_exclude x roots1` and `root_env_excludes x R1`. This is
     intentionally not enforced before alpha-normalization because source-level
     `let x = &x` initializer shadowing is valid.
   - Done: added proof-only coverage/freshness prerequisites for the
     structural-to-shadow route: `root_env_covers_sctx` and basic coverage
     lemmas in `TypeSafety.v`, plus
     `alpha_rename_fn_def_body_local_store_names_fresh_params` in
     `AlphaRenaming.v`.
   - Done: added the alpha-renamed local-local freshness prerequisite in
     `AlphaRenaming.v`. The key wrappers are
     `alpha_rename_expr_local_store_names_in_used`,
     `alpha_rename_expr_local_store_names_nodup`,
     `alpha_rename_fn_def_body_local_store_names_nodup`, and
     `alpha_rename_fn_def_params_body_local_store_names_nodup`. These facts
     are proof-only and do not change checker behavior.
   - Deferred sidecar work: the alpha no-shadow facts may still help if local
     root/shadow evidence is needed for direct-call cleanup or provenance.
     Do not use them to restart full structural-to-shadow-root synthesis as
     the canonical ordinary-safety route.
   - Done: proved and focused-compiled
     `alpha_rename_typed_env_roots_shadow_safe_full_support_forward`, closing
     the old blockers around assembling the full shadow-safe
     `typed_env_roots` alpha-renaming theorem.
   - Done: added origin/current initial root-env support facts for this bridge:
     `initial_root_env_for_params_origin_names`,
     `initial_root_env_for_params_origin_no_shadow`,
     `initial_root_env_for_params_origin_sctx_keys_named`, and
     `initial_root_env_for_params_origin_sctx_roots_named`. These cover the
     parameter-renamed root environment used when cached callee summaries are
     transported to freshened call bodies.
   - Done: added and compiled the shadow-safe root substitution lemmas in
     `AlphaRenaming.v`: `typed_roots_shadow_safe_instantiate_fresh_mutual`
     plus wrappers for env, args, and fields. These give the bridge a
     compiled route for instantiating cached summary roots at freshened
     direct-call bodies.
   - Done: strengthened `TypeSafety.v` direct-call bridge facts
     `direct_call_callee_body_root_evidence`,
     `direct_call_callee_body_root_summary_bridge`, and
     `direct_call_callee_body_root_shadow_summary_bridge` so they carry the
     runtime call-site invariants needed for substitution freshness:
     `provenance_ready_args`, `store_typed`, `store_roots_within`,
     `store_no_shadow`, and `root_env_no_shadow`, in addition to the existing
     `root_env_store_roots_named`, `eval_args`, and `typed_args_roots`
     premises.
   - Done: added and compiled the `TypeSafety.v` helper
     `eval_args_root_subst_images_exclude_names_for_fresh_call`. This derives
     `root_subst_images_exclude_names` for freshened callee bodies from the
     runtime call-site invariants now carried by the direct-call bridge facts.
   - Done: direct-call bridge/evidence and alpha runtime wrappers now carry
     `root_env_store_keys_named`; `TypeSafety.v` has compiled helpers deriving
     freshened callee local key exclusion from `eval_args` plus
     `alpha_rename_fn_def` freshness:
     `root_env_store_keys_named_lookup_excludes_name`,
     `root_env_store_keys_named_excludes_names`, and
     `eval_args_root_keys_exclude_names_for_fresh_call`.
   - Done: added and compiled the shadow-safe tail-frame route in
     `TypeSafety.v`: root-env append/frame algebra,
     `root_env_tail_fresh_names`,
     `typed_roots_shadow_safe_tail_frame_mutual`,
     `typed_env_roots_shadow_safe_tail_frame`, and
     `eval_args_root_tail_fresh_names_for_fresh_call`. These facts transport
     shadow-safe callee body root typing over a caller tail once the freshened
     body-local names are absent from that tail.
   - Done: consumed the tail-frame theorem in the actual shadow-summary
     transport. Cached summary evidence is now transported to each freshened
     direct-call body by `direct_call_callee_body_root_shadow_summary_bridge_of_unique`
     instead of being assumed as an explicit premise.

4. Direct-call root evidence remains a supporting obligation.
   - Existing direct-call preservation work may continue, but it must be framed
     as support for ordinary checker runtime safety.
   - Cached root-polymorphic summaries with tagged roots remain the current
     intended proof shape:
     - `RStore x` is concrete runtime storage.
     - `RParam x` is symbolic parameter-value provenance.
   - `RParam` names stay tied to the original function parameters through
     alpha-renaming. Call-site instantiation must therefore build
     `root_subst_of_params` from the original parameters, not the freshened
     call-site parameters.
   - Done: added the root-env algebra helper showing that instantiating
     `initial_root_env_for_params_origin` with original-parameter substitutions
     yields the fresh/current parameter root environment, under the required
     argument-root length and original-parameter `NoDup` premises.
   - Done: added the `call_param_root_env` equivalence helper for the empty
     tail case, so the origin-summary instantiation helper now connects to the
     call-site root environment shape used by direct-call evidence.
   - Done: added `call_param_root_env_excludes_params`, with the necessary
     `root_env_no_shadow R_tail` premise. Without no-shadow, removing parameter
     keys can expose shadowed root-env entries, so the no-shadow invariant is
     part of the correct tail-exclusion statement.
   - Done: added the tail-frame theorem that transports shadow-safe callee-body
     root typing from the parameter-only root environment to the caller-tail
     shape used by `call_param_root_env`.
   - Done: generalized the root-aware alpha-renaming proof beyond the earlier
     var/place/borrow cases via
     `alpha_rename_typed_env_roots_shadow_safe_full_support_forward`, so an
     entire freshened callee body has the needed shadow-safe transport theorem.
   - Done: added root-env name/no-collision helper lemmas and
     `root_env_equiv_rename_lookup_none_forward`, preparing the let/let-infer
     cases of the full root-aware alpha-renaming theorem.
   - Done: added root-aware alpha-renaming helpers for `typed_args_roots` and
     `typed_fields_roots`, so call and struct cases can reuse the same
     traversal shape as the structural alpha-renaming proof.
   - Done: added `typed_env_roots` call/struct wrapper lemmas that lift the
     args/fields root-aware alpha-renaming helpers through `TER_Call` and
     `TER_Struct`, including `root_sets_union` rename equivalence for calls.
   - Done: added the let-body no-collision helper that derives collision
     safety for the pre-body root environment from the post-body environment
     with the let-bound key removed.
   - Done: added root-env rename/update and rename/remove equivalence helpers
     for replace/assign and let/let-infer result environments.
   - Done: added root-aware alpha-renaming wrappers for trivial expression
     constructors, function values, and drop expressions, with drop parameterized
     by the recursive inner-expression alpha-renaming evidence.
   - Done: added root-aware alpha-renaming wrappers for `TER_Replace_Path`
     and `TER_Assign_Path`, including path availability/restore transport and
     root-env update rename equivalence.
   - Done: added root-aware alpha-renaming wrappers for `TER_Let` and
     `TER_LetInfer`, preserving alpha-first shadowing behavior while
     transporting let-body root environments through renamed binder add/remove.
   - Done: factored the extended-rename remove helper
     `root_env_remove_shadow_safe_rename_body_ext_equiv`. This gives the
     let/let-infer body proof a direct equivalence for removing the fresh binder
     under `((x, xr) :: rho)`, while the existing outer-rho helper remains the
     final binder-removal bridge.
   - Done: added the root-aware alpha-renaming wrapper for `TER_If`, including
     branch context merge, branch root-env equivalence under renaming, and
     renamed branch-root union equivalence.
   - Done: fixed the former full-theorem assembly blocker where
     `alpha_rename_typed_env_roots_if_shadow_safe_support_forward` did not
     expose which `EIf` subexpression was being processed.
   - Done: refined the if wrapper callback so each recursive callback carries
     a concrete subexpression-size premise, then used that in the full
     `typed_env_roots_shadow_safe` alpha-renaming theorem.
   - Done: resolved the former full-theorem assembly blocker where let-body
     recursive hypotheses only returned equivalence under the extended rename
     `((x, xr) :: rho)`. Focused helper lemmas now derive the renamed
     result-side exclusion facts from the existing let premises and
     alpha-renaming freshness/no-collision facts.
   - Done: added weak `RStore`-only rename exclusion helpers for root sets and
     root environments. These deliberately do not require excluding `RParam x`,
     because alpha-renaming leaves `RParam` atoms unchanged.
   - Done: added proof-only shadow-safe root typing relations that mirror
     `typed_env_roots` / args / fields, with extra `TER_Let` and
     `TER_LetInfer` premises requiring initializer roots and the pre-body root
     environment to exclude the binder. Projection lemmas recover the ordinary
     root typing judgments.
   - Done: added a shadow-safe root support invariant in `AlphaRenaming.v`.
     The invariant states that every concrete `RStore z` appearing in a result
     root set or root environment is named by the corresponding structural
     context. This mirrors the existing `TypeSafety.v` support theorem, but is
     local to `AlphaRenaming.v` to avoid importing the runtime safety module
     into the alpha-renaming proof path.
   - Done: added helper lemmas deriving `roots_exclude` and
     `root_env_excludes` from the shadow-safe support invariant plus freshness
     from the renamed context. These are the local facts needed to turn
     `fresh_ident` context freshness into the let/let-infer escape checks on
     renamed result roots and surviving root environments.
   - Done: added the matching shadow-safe root-env key-support invariant and
     remove-after-let freshness helper in `AlphaRenaming.v`. This records that
     surviving root-env keys remain backed by structural context names, and
     that removing a no-shadow let-bound key really removes that key from the
     surviving root environment.
   - Done: added shadow-safe root-aware alpha-renaming wrappers for args,
     fields, trivial constructors, function values, drop, var/place, borrow,
     replace/assign, if, call, and struct. These wrappers preserve the existing
     alpha-renaming conclusions while returning `typed_*_roots_shadow_safe`
     evidence, so the full theorem can use shadow-safe support facts directly.
   - Done: assembled the full `typed_env_roots_shadow_safe` alpha-renaming
     theorem using the accumulated constructor wrappers, support-carrying
     callbacks, and root-env algebra helpers.
   - Done: used the shadow-safe support invariant in the `TER_Let` /
     `TER_LetInfer` cases to derive that the fresh alpha-renamed binder is
     absent from returned roots and surviving root environments.
   - Done: bypassed the former mismatch where the existing
     `alpha_rename_typed_env_roots_let_forward`
     and `alpha_rename_typed_env_roots_letinfer_forward` wrappers are phrased
     over ordinary `typed_env_roots`, while the support invariant is available
     for `typed_env_roots_shadow_safe`, by assembling the full theorem over
     `typed_*_roots_shadow_safe` with support-carrying wrappers.
   - Done: resolved the former narrowed blocker where the shadow-safe
     `TER_Let` / `TERS_LetInfer` wrappers needed renamed-side
     `root_env_sctx_roots_named` and `root_env_sctx_keys_named` support to prove
     the renamed initializer obligations from `fresh_ident` context freshness.
   - Done: added `root_env_sctx_keys_named_fresh_lookup_none` and
     `root_env_sctx_support_fresh_let_init`, which package the initializer-side
     support facts needed by shadow-safe `TER_Let` / `TERS_LetInfer`.
   - Done: added the explicit body-result no-collision route for concrete
     `RStore` roots under `((x, xr) :: rho)`. The route is factored through
     `ctx_alpha_lookup_rename_in_names`,
     `ctx_alpha_bound_no_collision_for`,
     `root_set_sctx_roots_named_bound_no_collision`,
     `root_env_sctx_roots_named_bound_no_collision`, and
     `root_env_sctx_keys_named_bound_no_collision`.
   - Done: added body-result transport helpers
     `roots_exclude_shadow_safe_rename_body` and
     `root_env_excludes_shadow_safe_rename_body`, so shadow-safe let wrappers
     can derive renamed `roots_exclude xr roots2r` and
     `root_env_excludes xr ...` from support invariants plus the original let
     premises.
   - Done: added shadow-safe `TER_Let` / `TERS_LetInfer` alpha-renaming
     wrappers. These mirror the ordinary let wrappers while preserving
     `typed_env_roots_shadow_safe` evidence and threading the renamed
     initializer/body exclusion obligations.
   - Done: added support-transport helpers for root-set/root-env support under
     `root_set_equiv`, `root_env_equiv`, `root_set_rename`, and
     `root_env_rename` under `ctx_alpha`.
   - Done: added the fixed let-body recursive-call helpers
     `root_env_sctx_keys_named_lookup_rename_fresh`,
     `rename_no_collision_on_cons_lookup_rename_fresh`,
     `root_env_add_shadow_safe_rename_no_collision_on`, and
     `root_env_add_shadow_safe_rename_equiv`. These package the no-collision
     and root-env add/rename equivalence facts needed for the support-carrying
     `TER_Let` / `TERS_LetInfer` cases.
   - Done: added and compiled
     `root_env_remove_shadow_safe_rename_no_collision_on`. This helper derives
     the let-body extended no-collision obligation from the removed result
     environment, so the body callback can recover the
     `((x, xr) :: rho)` no-collision fact after removing the let binder.
   - Done: added the body-result equivalence helpers
     `root_set_shadow_safe_rename_body_equiv` and
     `root_env_remove_shadow_safe_rename_body_equiv`. These convert body IH
     results under `((x, xr) :: rho)` back to the outer `rho` after the let
     binder is removed, using the original let escape premises.
   - Done: added head-binder no-collision helpers
     `root_env_sctx_keys_named_added_bound_no_collision` and
     `root_env_sctx_keys_named_added_no_collision_for_head`. These derive the
     `rename_no_collision_for ((x, xr) :: rho) x ...` obligation for a body
     root environment supported by the extended structural context.
   - Done: added support-carrying wrapper lemmas for trivial expressions,
     function values, and `drop`. These establish the callback shape that the
     full induction needs when recursive hypotheses require root-env key/root
     support premises.
   - Done: added support-carrying wrapper lemmas for `var`, `place`, `borrow`,
     `replace`, `assign`, `if`, args, fields, `call`, and `struct`. These
     thread `root_env_sctx_keys_named` and `root_env_sctx_roots_named` through
     the non-let recursive wrapper shape without changing the ordinary
     wrappers.
   - Done: added support-carrying wrapper lemmas for `TER_Let` and
     `TERS_LetInfer`. Their body callbacks receive the initializer-produced
     root-env/root-set rename equivalences and support facts, and still return
     the fresh renamed-binder lookup/exclusion facts needed by the shadow-safe
     let rules.
   - Done: updated the shadow-safe `TER_Let` and `TERS_LetInfer`
     support-carrying wrappers so their body callbacks receive the
     initializer-produced renamed-environment no-shadow fact, plus the
     original binder-side lookup, exclusion, and no-collision facts. This keeps
     the body callback from having to reconstruct facts that are already known
     at the let boundary.
   - Done: added full-induction setup helpers
     `ctx_alpha_add_fresh_inv` and
     `root_env_sctx_support_fresh_renamed_let_init`. These package the
     renamed-tail freshness and renamed initializer lookup/exclusion facts
     needed when constructing the `TER_Let` / `TERS_LetInfer` body callback
     inside the full support-carrying induction.
   - Done: added
     `root_env_remove_shadow_safe_rename_no_collision_on_same_bindings`. This
     generalizes the result-side extended no-collision helper from an
     `sctx_add`-shaped result context to any same-bindings actual result
     context `Σ2`.
   - Done: extended the shadow-safe `TER_Let` and `TERS_LetInfer`
     support-carrying wrapper callbacks with the body-result removed
     no-collision fact plus the original body-result roots/root-env escape
     premises. The full induction callback no longer has to recover these
     actual-result facts from generalized callback parameters.
   - Done: added focused support-stripping helpers
     `root_set_sctx_roots_named_strip_added_same_bindings`,
     `root_env_sctx_roots_named_remove_strip_added_same_bindings`, and
     `root_env_sctx_keys_named_remove_strip_added_same_bindings` for body
     results whose `RStore x` roots are excluded, so support facts over an
     actual result context `Σ2` with
     `sctx_same_bindings (sctx_add x T m Σ1) Σ2` can be reused over the
     binder-free context needed by the final let/letinfer escape obligations.
   - Done: refined
     `alpha_rename_typed_env_roots_if_shadow_safe_support_forward` so its
     callback carries a concrete subexpression-size premise. This lets the
     full local fuel induction discharge the `EIf` recursive calls without
     guessing which branch expression is being processed.
   - Done: proved
     `alpha_rename_typed_env_roots_shadow_safe_full_support_forward` using
     the support-carrying wrappers, including the shadow-safe `TER_Let` /
     `TERS_LetInfer` cases and the `EIf` size-premise callback.
   - Done: added and compiled
     `typed_roots_shadow_safe_instantiate_fresh_mutual` plus the env, args,
     and fields wrappers in `AlphaRenaming.v`. These are the substitution-side
     support needed before the shadow summary bridge can instantiate cached
     root-polymorphic summaries at freshened direct-call bodies.
   - Concrete `RStore fresh_param` roots must still be excluded from returned
     roots and surviving root environments before callee cleanup.

5. Defer unrelated expansion.
   - The syntactic `ECallExpr (EFn fname) args` direct-call-sugar case is now
     implemented by the direct-call-local route.
   - Do not start captured closures until the non-capturing function-value
     provenance route is stable.
   - Do not widen closure validators until the matching Prop preservation
     theorem exists for that closure phase.
   - Do not attempt small-step progress before preservation is stable.
