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

## Active Implementation Queue

Follow this order. Stop and report if a step exposes a missing invariant or a
false lemma.

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
   - Remaining blocker: state and prove the tail weakening theorem that
     transports callee-body root typing from the parameter-only root
     environment to `call_param_root_env` with the caller tail.
   - Remaining blocker: generalize the root-aware alpha-renaming proof beyond
     the existing var/place/borrow cases so an entire freshened callee body can
     be transported from cached summary evidence to call-site evidence.
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
   - Done: added the root-aware alpha-renaming wrapper for `TER_If`, including
     branch context merge, branch root-env equivalence under renaming, and
     renamed branch-root union equivalence.
   - Blocker found while assembling the full theorem: the plain recursive
     induction hypothesis for let bodies only returns equivalence under the
     extended rename `((x, xr) :: rho)`. The final `TER_Let` / `TER_LetInfer`
     reconstruction also needs to prove that the fresh binder `xr` is excluded
     from the renamed result roots and surviving root environment. Do not solve
     this by rejecting source shadowing. Add focused helper lemmas that derive
     these renamed-exclusion facts from the existing let premises
     `roots_exclude x roots2` and
     `root_env_excludes x (root_env_remove x R2)`, plus freshness/no-collision
     facts from alpha-renaming.
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
   - Remaining blocker: assemble the full `typed_env_roots`
     alpha-renaming theorem, using the accumulated constructor wrappers and
     root-env algebra helpers in the corresponding constructor cases.
   - Remaining blocker: use the new shadow-safe support invariant in the
     `TER_Let` / `TER_LetInfer` cases to derive that the fresh alpha-renamed
     binder is absent from returned roots and surviving root environments.
   - Remaining blocker: the existing `alpha_rename_typed_env_roots_let_forward`
     and `alpha_rename_typed_env_roots_letinfer_forward` wrappers are phrased
     over ordinary `typed_env_roots`, while the support invariant is available
     for `typed_env_roots_shadow_safe`. The full theorem should therefore be
     assembled directly over `typed_*_roots_shadow_safe`, or the wrappers should
     get shadow-safe variants that thread the shadow-safe body evidence through
     the recursive call.
   - Newly narrowed blocker: the shadow-safe `TER_Let` / `TERS_LetInfer`
     wrappers cannot be plain copies of the ordinary wrappers. They must either
     carry renamed-side `root_env_sctx_roots_named` and
     `root_env_sctx_keys_named` support through the wrapper, or the full theorem
     must use a stronger support-carrying induction. This is needed to prove the
     renamed initializer obligations
     `root_env_lookup xr Rr1 = None`, `roots_exclude xr roots1r`, and
     `root_env_excludes xr Rr1` from `fresh_ident` context freshness.
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
   - Remaining narrowed blocker: assemble the full theorem over
     `typed_*_roots_shadow_safe` as a support-carrying induction. The next
     proof obligation is the let-body recursive call: derive
     `rename_no_collision_on ((x, xr) :: rho)
       (root_env_names (root_env_add x roots1 R1))`
     from the existing outer no-collision facts, `root_env_lookup x R1 = None`,
     `root_env_excludes x R1`, and freshness of `xr`.
   - Done: added the fixed let-body recursive-call helpers
     `root_env_sctx_keys_named_lookup_rename_fresh`,
     `rename_no_collision_on_cons_lookup_rename_fresh`,
     `root_env_add_shadow_safe_rename_no_collision_on`, and
     `root_env_add_shadow_safe_rename_equiv`. These package the no-collision
     and root-env add/rename equivalence facts needed for the support-carrying
     `TER_Let` / `TERS_LetInfer` cases.
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
   - Remaining narrowed blocker: add the same support-carrying wrapper shape
     for the remaining recursive constructors, then assemble the full
     support-carrying induction over `typed_*_roots_shadow_safe`.
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
