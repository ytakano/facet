# Type Safety Roadmap

This file is the active Codex-facing implementation guide. Historical notes,
completed proof inventory, and older milestone logs live in
`plan/type_safety_roadmap_history.md`.

## Purpose

The primary goal is to prove operational type safety for the user-facing,
ordinary checker pipeline.

Canonical target:

```coq
infer_full_env env f = infer_ok (T, Γ')
  -> initial_store_for_fn f s
  -> eval env s (fn_body f) s' v
  -> value_has_type env s' v (fn_ret f).
```

The root checker is not the language definition and is not a substitute for
ordinary checker safety. Root provenance remains auxiliary evidence used for
runtime reference safety, let-local escape checks, and direct-call cleanup
proofs. If a future design promotes the root checker to the canonical route,
that decision must be made explicitly and this file must be rewritten around
that theorem.

## Canonical Route

1. Prove preservation and runtime safety from the Prop-level ordinary typing
   rules used by checker soundness.
2. Connect ordinary checker soundness to the preservation theorem.
3. Use root provenance only when the operational proof needs reference-target
   or cleanup evidence that ordinary typing does not currently expose.
4. Keep root-checker success as a sidecar theorem unless the project explicitly
   changes the user-facing checker contract.

Do not make the root checker stricter than the ordinary checker to patch a
proof gap. If ordinary checker safety needs an invariant, expose that invariant
in the ordinary typing/checker route or prove that the existing checker already
establishes it.

## Fixed Design Decisions

- Big-step preservation comes before progress.
- Progress is deferred until a future small-step semantics exists.
- Checker soundness and operational type safety stay separate until the final
  checker-to-runtime theorem connects them.
- The ordinary checker is the primary accepted-program interface.
- Root provenance is a sidecar API:
  - `infer_core_env_roots`
  - `infer_env_roots`
  - `infer_full_env_roots`
- Updating the sidecar API requires updating its soundness theorem.
- Lifetime inference and root provenance inference are separate: lifetime
  inference determines lifetime substitution; root provenance determines which
  runtime roots flow through references.
- Runtime calls freshen callee function definitions against caller/captured
  store names before `bind_params`.
- The user-facing checker route should type-check alpha-normalized core.
  The verified operational target is the alpha-normalized core, not the
  pre-normalization frontend core.
- Root provenance should run on alpha-renamed, shadow-free core terms when root
  evidence is needed.
- `let x = &x` is not inherently unsafe. After alpha-renaming-before-checking,
  the internal shape is `let x_fresh = &x`, so initializer roots do not collide
  with the binder being introduced.
- Do not reject initializer roots merely because they mention the source binder
  name of a shadowing `let`.
- Reference `drop` does not release a borrow. Cases like `drop r; drop x` are
  deferred to future non-lexical lifetime / last-use analysis.
- Local annotation lifetime elision remains rejected until fresh local lifetime
  regions are designed.
- Same-argument-name parameters in one function are rejected.
- Duplicate-parameter and shadowing errors should stay distinguishable.

## Codex Quick Path

Start here when implementing the next slice. The detailed inventory below is
reference material, not the implementation order.

### Current Proof State

Available facts; do not re-prove or redesign these unless a compile failure
shows they are unusable.

- Ordinary checker alpha route exists:
  `alpha_normalize_global_env`, `check_program_env_alpha`,
  `infer_full_env_alpha_structural_sound`, and
  `check_program_env_alpha_checked_structural`.
- Direct-call root evidence plumbing exists:
  `direct_call_callee_body_root_evidence`,
  `direct_call_callee_body_root_summary_bridge`,
  `direct_call_callee_body_root_shadow_summary_bridge`,
  `infer_full_env_alpha_big_step_safe_with_root_summary_bridge`, and
  `infer_full_env_alpha_big_step_safe_with_root_shadow_summary_bridge`.
- Shadow-safe root typing and alpha-renaming support exists:
  `typed_env_roots_shadow_safe`,
  `typed_env_roots_shadow_safe_roots`,
  `alpha_rename_typed_env_roots_shadow_safe_full_support_forward`, and
  `typed_roots_shadow_safe_instantiate_fresh_mutual`.
- Call-site freshness and tail framing exist in `TypeSafety.v`:
  `eval_args_root_subst_images_exclude_names_for_fresh_call`,
  `eval_args_root_keys_exclude_names_for_fresh_call`,
  `eval_args_root_tail_fresh_names_for_fresh_call`,
  `root_env_tail_fresh_names`,
  `typed_roots_shadow_safe_tail_frame_mutual`, and
  `typed_env_roots_shadow_safe_tail_frame`.
- Function-level alpha-renaming packaging now exists in `AlphaRenaming.v`:
  `alpha_rename_fn_def_params_body`,
  `alpha_rename_fn_def_params_body_facts`,
  `ctx_alpha_no_collision_on`,
  `alpha_rename_fn_def_initial_support_facts`, and
  `alpha_rename_fn_def_static_fields`.
- The shadow-summary interface now carries callee parameter uniqueness:
  `callee_body_root_shadow_summary` includes
  `NoDup (ctx_names (params_ctx (fn_params fdef)))`.
- Call argument root-list length plumbing exists:
  `typed_args_roots_arg_roots_length` and `apply_lt_params_length`.

### Next Implementation Task

Prove the direct-call shadow-summary bridge without assuming transported callee
body evidence.

Completed prerequisite:

- The bridge needs to apply
  `alpha_rename_typed_env_roots_shadow_safe_full_support_forward` to a cached
  callee body summary.
- That theorem requires the source initial root environment to be no-shadow and
  no-collision:
  `root_env_no_shadow (initial_root_env_for_fn fdef)` and
  `rename_no_collision_on rho (root_env_names (initial_root_env_for_fn fdef))`.
- These follow from `NoDup (ctx_names (params_ctx (fn_params fdef)))`, and the
  helper `alpha_rename_fn_def_initial_support_facts` packages the proof.
- The cached summary now exposes that `NoDup` premise directly.

Current proof blocker:

- After alpha-renaming and instantiating the cached callee body summary, the
  bridge must still produce the final
  `roots_exclude_params (fn_params fcall) roots_body` and
  `root_env_excludes_params (fn_params fcall) R_body` fields required by
  `callee_body_root_shadow_ready_at`.
- This should be handled as proof plumbing from the existing cached
  `Hexclude_roots` / `Hexclude_env`, alpha-renaming support facts, root
  instantiate exclusion lemmas, and tail-frame exclusion lemmas.
- The remaining missing proof shape is specifically the alpha-renaming step for
  param-exclusion:
  from `roots_exclude_params (fn_params fdef) roots_body` and
  `root_env_excludes_params (fn_params fdef) R_body`, derive the corresponding
  facts for the alpha-renamed `fn_params fcall` after
  `alpha_rename_typed_env_roots_shadow_safe_full_support_forward`.
  Existing `roots_exclude_rename` / `root_env_excludes_rename` need
  no-collision between renamed parameter names and store roots in the output
  roots/env. If this cannot be obtained from current support facts, add an
  explicit proof-only invariant connecting body output roots/env names to
  parameter names plus expression-local names.
- Stop again if this requires a new semantic invariant. Do not weaken checker
  behavior or the alpha-renaming theorem.

Target theorem:

```coq
Lemma direct_call_callee_body_root_shadow_summary_bridge_of_unique :
  forall env,
    fn_env_unique_by_name env ->
    direct_call_callee_body_root_shadow_summary_bridge env.
```

Required proof route:

1. Use function-name uniqueness to recover the cached shadow summary for the
   runtime callee.
2. Destructure the strengthened summary to obtain both the cached body summary
   and `NoDup (ctx_names (params_ctx (fn_params fdef)))`.
3. Use `alpha_rename_fn_def_initial_support_facts` to obtain the parameter
   rename environment, body rename equation, `ctx_alpha`, used/disjoint facts,
   initial root no-shadow/support facts, and source no-collision.
4. Use `alpha_rename_fn_def_static_fields` to rewrite `fn_lifetimes`,
   `fn_outlives`, and return type facts for `fcall`.
5. Derive output root no-collision for the cached body result from typed output
   support and `ctx_alpha`; add a proof helper if needed.
6. Apply `alpha_rename_typed_env_roots_shadow_safe_full_support_forward` to the
   cached summary body.
7. Instantiate the renamed summary with
   `root_subst_of_params (fn_params fdef) arg_roots`.
8. Use
   `root_env_instantiate_initial_origin_equiv_call_param_root_env_empty` for
   the parameter-only root environment.
9. Use `typed_args_roots_arg_roots_length` plus `apply_lt_params_length` to
   discharge root-list length premises.
10. Use `eval_args_root_tail_fresh_names_for_fresh_call` and
   `typed_env_roots_shadow_safe_tail_frame` to add the caller tail.
11. Transport the cached return-root and output-root param-exclusion facts
   through alpha-renaming, root-substitution instantiation, and the caller-tail
   frame.
12. Finish with `call_param_root_env_app_tail`.

Stop and report if any step needs a semantic invariant rather than a proof-only
helper. Do not change checker behavior.

### After That

- Add an `EnvRuntimeSafety.v` convenience wrapper that derives the shadow bridge
  from `fn_env_unique_by_name` instead of requiring the bridge as a premise.
- Then return to the ordinary checker target over `alpha_normalize_global_env`.

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
     sidecar checker success and direct-call root evidence. This is not the
     final ordinary-checker-only theorem; it documents the exact root evidence
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
   - Remaining blocker: restate the main theorem over the alpha-normalized
     environment/body produced by `alpha_normalize_global_env`, then connect
     the existing raw `infer_full_env` soundness facts to that route.
   - Remaining blocker: ordinary checker success still does not by itself
     produce the `typed_env_roots` evidence required by direct-call cleanup;
     either prove that the ordinary alpha route establishes the needed sidecar
     root evidence, or keep the final theorem explicitly parameterized by that
     sidecar evidence until the bridge is proved.
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
   - Remaining blocker: consume the tail-frame theorem in the actual
     shadow-summary transport, so cached summary evidence can be transported to
     each freshened direct-call body without assuming the transported evidence
     as a premise.
   - Remaining blocker refinement: the tail-frame theorem is now available.
     The remaining bridge work is to package the cached callee summary through
     `alpha_rename_fn_def`: expose the parameter rename environment, body
     rename equation, ctx-alpha evidence, used-name facts, and output
     root-env no-collision/support premises required by
     `alpha_rename_typed_env_roots_shadow_safe_full_support_forward`, then
     instantiate the renamed summary and apply the tail frame.

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
   - Do not start `ECallExpr` until the direct-call and root-evidence route is
     stable.
   - Do not handle non-empty captured closure stores until a captured-store
     invariant is designed.
   - Do not attempt small-step progress before preservation is stable.

## Main Target Theorems

Long-term preservation target:

```coq
Theorem eval_preserves_typing :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    eval env s e s' v ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
```

Long-term ordinary-checker-to-runtime target:

```coq
Theorem infer_full_env_big_step_safe :
  forall env f T Γ' s s' v,
    ValidEnv env ->
    infer_full_env env f = infer_ok (T, Γ') ->
    initial_store_for_fn f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
```

Runtime reference target:

```coq
Theorem eval_no_dangling_refs :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    borrow_ok_env_structural env [] (ctx_of_sctx Σ) e [] ->
    eval env s e s' v ->
    refs_wf env s' v /\ store_refs_wf env s'.
```

Future small-step target:

```coq
Theorem step_progress :
  forall env Ω n Σ e T,
    store_typed env [] Σ ->
    typed_env_structural env Ω n Σ e T Σ ->
    terminal e \/ exists e' s', step env [] e s' e'.
```

`step_progress` must wait for `StepSemantics.v`.

## Sub-Agent Policy

Use sub-agents only after the design route is fixed and the task is
implementation-only.

Before spawning any sub-agent, state why the delegated task is
implementation-only. Example:

> This task is implementation-only because the canonical checker-safety route
> and target files are fixed; the worker is only reverting the temporary
> `roots_exclude x roots1` restriction and updating the corresponding tests.

Do not delegate:

- choosing between ordinary-checker safety and root-checker canonical safety
- deciding a new invariant
- comparing proof strategies
- investigating repository-wide design

Allowed delegation examples:

- reverting the known temporary root-checker restriction in fixed files
- updating focused regression tests after the expected behavior is fixed
- proving a named helper lemma whose statement and dependencies are already
  fixed by the main agent

## Required Checks

Before committing type-system work:

```sh
cd rocq && make
dune build
bash tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|Abort\.|DEBUG|idtac" rocq/theories
```

For roadmap-only edits, at minimum run:

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
