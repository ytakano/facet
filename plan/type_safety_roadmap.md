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
proof gap. The ordinary safety route should prove structural preservation from
the existing structural rules and checker soundness. In particular, do not
strengthen `TES_If` or ordinary checker acceptance merely to manufacture
shadow/root sidecar evidence.

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

Start here. The detailed inventory below is history/reference, not the
implementation order.

### Current Goal

Make the ordinary-checker safety route understandable and implementable without
turning the root checker into the language definition.

Near-term working goal:

1. Keep `check_program_env_alpha` as the ordinary accepted-program checker.
2. Use executable safety validators only to discharge proof evidence that the
   current operational proof still needs.
3. Reduce the validator's false negatives until the safety-validator route has
   the same accepted program range as the ordinary checker, or until a specific
   gap is proven to require a checker contract decision.
4. Keep initial runtime readiness as a separate execution-state obligation; it
   is not part of program acceptance.

Do not claim ordinary-checker-only safety until the final theorem no longer
needs root-shadow summary evidence, preservation readiness sidecar evidence, or
initial runtime readiness beyond the agreed initial-store contract.

### Current Route

The active route is ordinary checker safety over alpha-normalized core:

1. The frontend/checker path checks `alpha_normalize_global_env env`.
2. Ordinary checker success gives structural typing.
3. Structural preservation proves `value_has_type`.
4. Root/shadow evidence is used only as sidecar evidence for direct-call
   cleanup/provenance.

Do not try to prove `typed_env_structural -> typed_env_roots_shadow_safe` as the
canonical route.

### Next Implementation Order

Follow this order before inventing new theorem shapes:

1. **List acceptance gaps with fixtures and Rocq examples.**
   Add small examples that pass the ordinary checker but fail the current
   safety-validator route. Include both `.facet` fixtures and small core-AST
   examples when parser/desugarer behavior would obscure the proof issue.
   Include the still-relevant `plan/review.md` safety cases in this matrix so
   validator widening does not re-open old ordinary-checker bugs.
   Current implementation note: `TypeChecker.v` now contains a core-AST gap
   matrix for ordinary-checker accepted shapes rejected by the current
   preservation-ready validator: annotated `ELet`, existing `ELetInfer`,
   `EDeref (EBorrow RShared ...)`, direct `ECall`, and
   `ECallExpr (EFn ...)`.
2. **Reduce `preservation_ready_expr_b` false negatives.**
   The current executable validator rejects broad syntax classes such as
   `ELet`, `ELetInfer`, direct `ECall`, `ECallExpr`, and `EDeref`. First make
   the structural preservation route cover ordinary accepted `let` and direct
   call cases where the proof already has the required facts. For `ELet` and
   `ELetInfer`, do not merely remove the validator rejection: first make the
   ordinary route account for let-local reference escape, either by proving the
   current checker already rejects it or by adding an executable ordinary
   checker-side escape check.
   Current implementation note: `provenance_ready_expr_b` now accepts `ELet`
   and `ELetInfer`, and the checker has an executable elaboration route that
   turns inferred lets into annotated `ELet`. Do not wire this into the
   existing root-shadow validator by simple substitution. The existing
   preservation-ready root-shadow validator remains unchanged. The additive
   provenance-only route is now represented by
   `callee_body_root_shadow_provenance_ready_at`,
   `callee_body_root_shadow_provenance_summary`, and
   `check_env_root_shadow_provenance_summary`; the program-level entrypoint
   is `check_program_env_alpha_validated_root_shadow_provenance_summary`.
   The Rocq examples currently show this provenance-only entrypoint accepts
   the annotated and inferred ready-gap `let` cases that the split
   preservation-ready validator rejects.
3. **Move the non-direct-call structural route toward no validator.**
   Prefer deriving or eliminating `preservation_ready_expr` obligations from
   ordinary typing/checker success over adding more executable checks.
4. **Localize direct-call cleanup and root evidence.**
   Root/shadow evidence should be required only for the direct-call cleanup and
   reference-provenance subproofs that actually need it. Avoid whole-program
   root-shadow validation when a narrower direct-call evidence package is
   enough.
   While doing this, keep `replace p e_new` target-conflict discipline visible:
   the ordinary checker must not allow `e_new` to consume or invalidate the
   place being replaced, and any proof route should use that fact directly
   rather than relying on a broad sidecar rejection.
5. **Handle the `if` root-environment gap last.**
   The known blocker is that ordinary `TES_If` does not expose
   `root_env_equiv R2 R3`, while root/shadow routes require it. Do not
   strengthen `TES_If` or ordinary checker acceptance just to manufacture this
   evidence.
6. **Treat initial readiness as a separate axis.**
   `initial_root_runtime_ready_for_fn` is about the starting store, not the
   accepted program. Reduce it only through an initial-store contract change or
   an executable initial-state validator such as `check_initial_root_runtime_ready`.

### Current Public Proof Wrappers

Use these wrappers before adding new theorem shapes:

- Non-direct-call structural route:
  `infer_full_env_alpha_big_step_safe_structural_ready`.
- Direct-call sidecar route:
  `infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready`.
- Program-level direct-call sidecar route:
  `check_program_env_alpha_big_step_safe_with_direct_call_sidecar_ready`.
- Validated program-level direct-call sidecar route:
  `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_ready`.
- Validated program-level direct-call sidecar route with environment-level
  preservation readiness:
  `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_env_ready`.
- Proof-only root-shadow validator-ready route:
  `check_program_env_alpha_validated_big_step_safe_with_root_shadow_validator_ready`.
- Executable root-shadow validator route:
  `check_program_env_alpha_validated_root_shadow_big_step_safe`.
- Executable root-shadow validator route with checked initial runtime state:
  `check_program_env_alpha_validated_root_shadow_big_step_safe_checked_initial`.
- Executable root-shadow validator entrypoint:
  `check_program_env_alpha_validated_root_shadow`.
- Executable split provenance/preservation root-shadow validator entrypoint:
  `check_program_env_alpha_validated_root_shadow_provenance`.
- Executable provenance-only root-shadow summary entrypoints:
  `check_fn_root_shadow_provenance_summary` and
  `check_env_root_shadow_provenance_summary`.
- Executable preservation readiness entrypoint:
  `check_env_preservation_ready`.
- Executable initial runtime readiness entrypoint:
  `check_initial_root_runtime_ready`.
- Executable provenance readiness entrypoints:
  `provenance_ready_expr_b`, `provenance_ready_args_b`, and
  `provenance_ready_fields_b`.
- Executable inferred-let elaboration entrypoints:
  `infer_core_env_elab`, `infer_env_elab`, `infer_full_env_elab`,
  `infer_program_env_alpha_elab`, and `check_program_env_alpha_elab`.
- Sidecar package predicates:
  `ordinary_alpha_root_shadow_sidecar_ready`,
  `ordinary_alpha_direct_call_meta_ready`,
  `ordinary_alpha_direct_call_sidecar_ready`,
  `ordinary_alpha_direct_call_validated_sidecar_ready`, and
  `initial_root_runtime_ready_for_fn`.
- Proof-only validator-ready package predicates:
  `env_fns_root_shadow_summary_check_ready`,
  `ordinary_alpha_root_shadow_validator_ready`, and
  `ordinary_alpha_direct_call_validated_root_shadow_validator_ready`.
- Proof-only provenance-summary package predicates:
  `callee_body_root_provenance_ready_at`,
  `callee_body_root_shadow_provenance_ready_at`,
  `callee_body_root_provenance_summary`,
  `callee_body_root_shadow_provenance_summary`,
  `env_fns_root_provenance_summary_evidence`,
  `env_fns_root_shadow_provenance_summary_evidence`, and
  `env_fns_root_shadow_provenance_summary_check_ready`.
- Direct-call bridge from uniqueness:
  `direct_call_callee_body_root_shadow_summary_bridge_of_unique`.

### Current Endpoint

The top-level name validator route is implemented. `check_program_env_alpha`
remains unchanged, and `check_program_env_alpha_validated` adds a Rocq-side
top-level-name uniqueness check over the alpha-normalized environment. The
sidecar root-shadow validator route is now executable and also runs on the
alpha-normalized environment.

The current strongest executable route is:

```coq
check_program_env_alpha_validated_root_shadow_provenance_big_step_safe_checked_initial
```

Current status:

- `ordinary_alpha_root_shadow_sidecar_ready` isolates
  `env_fns_root_shadow_summary_evidence`.
- `ordinary_alpha_direct_call_meta_ready` isolates function-name uniqueness and
  preservation readiness.
- `ordinary_alpha_direct_call_sidecar_ready` remains as the compatibility
  package used by existing public wrappers.
- `ordinary_alpha_direct_call_validated_sidecar_ready` removes function-name
  uniqueness from the explicit sidecar package; uniqueness is derived from
  `check_program_env_alpha_validated`. The `_env_ready` validated wrapper also
  absorbs per-function direct-call readiness from the package's
  environment-level preservation readiness.
- `check_program_env_alpha_validated_root_shadow` is the executable sidecar
  validator route. Its soundness derives
  `ordinary_alpha_direct_call_validated_root_shadow_validator_ready` through
  `check_program_env_alpha_validated_root_shadow_ready`.
- The root-shadow validator checks the alpha-normalized environment with
  `infer_env_roots_shadow_safe`, which mirrors the root checker and adds the
  initializer-side shadow-safe obligations for `ELet` / `ELetInfer`.
- The checker now also exposes an elaboration route for proof-facing execution:
  `infer_core_env_elab` recursively preserves checker behavior while replacing
  successful `ELetInfer` nodes with inferred-type `ELet` nodes, and
  `infer_program_env_alpha_elab` returns an alpha-normalized elaborated
  environment.
- The executable validator route absorbs root-shadow summary evidence and
  environment-level preservation readiness. It still keeps
  `initial_root_runtime_ready_for_fn` explicit.
- The additive provenance-only validator route is implemented for the
  root-shadow summary evidence that does not require `preservation_ready_expr`.
  Its checker soundness theorem is
  `check_env_root_shadow_provenance_summary_ready`, its program-level
  entrypoint is
  `check_program_env_alpha_validated_root_shadow_provenance_summary`, and the
  original preservation-ready root-shadow validator route is unchanged.
- The split validator route keeps provenance and preservation readiness as
  separate executable checks. `check_env_root_shadow_provenance_summary`
  supplies root/shadow provenance evidence, `check_env_preservation_ready`
  supplies `env_fns_preservation_ready`, and
  `check_program_env_alpha_validated_root_shadow_provenance_ready` recombines
  them into the existing validator-ready package for the current runtime safety
  theorem.
- `check_program_env_alpha_validated_root_shadow_big_step_safe_checked_initial`
  discharges `initial_root_runtime_ready_for_fn` from the executable
  `check_initial_root_runtime_ready f s`.
- `check_program_env_alpha_validated_root_shadow_provenance_big_step_safe_checked_initial`
  is the strongest split-validator theorem. It is less coupled internally than
  `check_program_env_alpha_validated_root_shadow`, but still rejects programs
  that fail executable preservation readiness.
- Initial runtime readiness remains a separate premise, now in executable form.
   - It cannot be derived from `initial_store_for_fn` alone.
   - Reason: `initial_root_env_for_fn` stores parameter origins as `RParam`,
     while runtime references require concrete `RStore` reachability.

The current sidecar contract is fixed. The remaining non-ordinary acceptance
inputs are:

- `check_program_env_alpha_validated_root_shadow_provenance env = true`, which
  is stricter than `check_program_env_alpha env = true` because preservation
  readiness is still a separate executable validator.
- `check_initial_root_runtime_ready f s = true`, which checks the initial
  execution state rather than the program.

Further reductions of the initial-state premise require a stronger
initial-store contract. Do not claim that initial runtime readiness is
eliminated merely because it has an executable validator.

Future work:

- Decide whether the OCaml CLI should expose the root-shadow sidecar validator
  as an optional diagnostic/check mode. The ordinary checker contract remains
  unchanged unless that is explicitly redesigned.
- Design an executable validator or strengthened setup invariant for
  `initial_root_runtime_ready_for_fn`.
- Bring the safety-validator route closer to the ordinary checker accepted
  range by following the Next Implementation Order above.
- Localize or eliminate the remaining `env_fns_preservation_ready` dependency.
  The split validator proves that root/shadow provenance evidence can be
  checked independently, but the current direct-call cleanup proof still calls
  preservation-ready typing preservation for callee bodies.

### Ordinary Checker Review Gates

`plan/review.md` is old, but its examples should stay as regression and proof
gates while the safety-validator route is widened to match the ordinary checker.

Already-fixed ordinary checker issues to preserve:

- Active-borrow access must be checked for ordinary reads/moves through `EVar`
  and `EPlace`, not only for `replace`, assignment, borrow, or dereference.
- Linear aggregate obligations must require every linear component path to be
  consumed; a single partial field move must not discharge the parent value.
- `&mut T` must be invariant in its referent type. Shared references may keep
  the intended compatible/covariant behavior, but unique references must not
  accept compatible-but-different inner types.
- Struct field mutability must be enforced for assignment and `replace`, not
  inferred only from the root binding mutability.
- Local type annotation lifetime elision must stay rejected until fresh local
  lifetime regions are designed.
- Generic trait syntax and validation must keep checking trait argument arity
  and bounds consistently.

Outstanding review-linked gates for the ordinary safety work:

- **Let-local reference escape.** The ordinary route must reject or prove safe
  examples shaped like `let r = let x = 1 in (&x); ...`. The current root-shadow
  safety route has initializer/body root exclusions, but that is sidecar
  evidence; the final ordinary checker theorem needs this handled by ordinary
  typing/checker facts or by an ordinary executable escape check.
- **Replace target self-use.** Existing path-state checks cover the direct
  self-move regression, but the final proof should make the intended rule
  explicit: while checking `replace p e_new`, `e_new` may not consume,
  overwrite, or borrow-conflict with `p` or a prefix/descendant of `p`. Add
  alias/borrow variants to the gap matrix if the current ordinary checker does
  not already reject them.

When reducing validator false negatives, rerun the relevant invalid fixtures
for these gates before treating a newly accepted syntax class as ordinary-safe.

### Do Not Do

- Do not strengthen `TES_If` or ordinary checker acceptance to satisfy
  root/shadow evidence.
- Do not restart full structural-to-shadow-root synthesis as the ordinary route.
- Do not make the root checker stricter than the ordinary checker to close a
  proof gap.
- Do not add an explicit `direct_call_callee_body_root_shadow_summary_bridge`
  premise to ordinary-facing statements; use `_of_unique`.

### Known Sidecar Gaps

- Ordinary checker success does not imply
  `env_fns_root_shadow_summary_evidence`.
- `check_program_env_alpha_validated` now implies `fn_env_unique_by_name` for
  the alpha-normalized environment.
- Ordinary checker success still does not imply `env_fns_preservation_ready`.
- The current executable safety validator is stricter than the ordinary checker.
  In particular, `preservation_ready_expr_b` currently rejects `ELet`,
  `ELetInfer`, `ECall`, `ECallExpr`, and `EDeref`.
- The provenance-only root-shadow summary validator accepts the annotated and
  inferred ready-gap let examples that the preservation-ready root-shadow
  validator rejects, but it is not yet wired into a final operational safety
  theorem.
- The abandoned synthesis route stops at `If`: `TES_If` lacks the
  `root_env_equiv R2 R3` evidence required by `TERS_If`.
- General root-checker-to-shadow-safe soundness is false for arbitrary core
  because source-level `let x = &x` initializer shadowing is valid before
  alpha-normalization.

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
