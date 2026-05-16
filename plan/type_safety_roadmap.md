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
