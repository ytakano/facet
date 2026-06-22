# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

The current implementation pass is focused on the trait-related type-safety
proof architecture, not on adding more trait surface features. The public
runtime theorem that must remain available is:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

This theorem must prove checked-initial big-step safety for the checker endpoint
that the CLI actually uses.

## Current State

- Traits, impls, associated types, trait methods, method-local type parameters,
  generic-trait impl remapping, associated type projections, and receiver-first
  UFCS method calls are parsed, lowered, and checked through the extracted Rocq
  checker. Impl method bodies are elaborated to hidden functions and checked even
  when uncalled. Dot syntax, associated type defaults, equality constraints, and
  `deriving` remain deferred.
- Supported method receivers are forms whose type is known before checker
  execution: parameters, typed literals, pure literal/unit locals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors, including generic instances. Field-bearing structs, payload
  enums, direct-call receivers, generic direct-call receivers, non-pure inferred
  locals, and call-initialized/general annotated locals remain gated.
- The OCaml CLI currently uses
  `infer_program_env_end2end_assoc_direct_receiver_mixed` as its only checker
  authority. Public checker soundness aliases target this endpoint.
- The required public checked-initial runtime theorem now targets the active
  mixed endpoint, `infer_program_env_end2end_assoc_direct_receiver_mixed`, and
  consumes the mixed endpoint's local runtime package rather than the older
  strict/exact endpoint.
- A diagnostic split endpoint exists:
  `infer_program_env_end2end_assoc_direct_receiver_split`, gated by
  `check_env_end2end_direct_receiver_split_ready`. It is not yet the active
  checker authority. `End2EndSafety.v` now has
  `direct_receiver_split_runtime_evidence_in_env`, which packages split-ready
  runtime facts, and the non-diagnostic theorem
  `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready`
  compiles with the same public preservation-premise shape as the active mixed
  theorem. The split-ready gate now uses the ready-body provider check instead
  of the synthetic route/exact-target sidecar, so the old no-target blocker is
  no longer the split-ready certificate itself. The active CLI endpoint still
  rejects valid no-target local-bounds callees because
  `infer_program_env_end2end_assoc_direct_receiver_mixed` retains the older
  synthetic route/exact-target gate.
- `End2EndSafety.v` now has an internal
  `assoc_direct_receiver_mixed_local_runtime_package` produced by
  `infer_program_env_end2end_assoc_direct_receiver_mixed_local_runtime_package`.
  This packages the active mixed endpoint's provable no-receiver local runtime
  evidence: ready-body-or-narrow summary provider plus alpha-body callback
  provider.
- `End2EndSafety.v` also has
  `mixed_ready_body_or_narrow_summary_provider_route_bridge_of_synthetic_summary_route_public_runtime_evidence`,
  which packages public runtime evidence plus a synthetic summary route premise
  into `mixed_ready_body_or_narrow_summary_provider_route_bridge`.
- The remaining proof surface issue is deriving that synthetic summary route
  premise internally, without adding it as a public premise or introducing more
  one-off wrapper theorem variants. A direct retarget attempt showed that the
  current public premise
  `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement` is
  weaker than the store-safe synthetic summary route evidence consumed by the
  mixed value/cleanup bridge.
- `CheckerRootSidecars.v` exposes the active mixed endpoint's
  checker-backed component certificate for selected no-capture direct-call
  callees under local bounds: synthetic route summaries, store-safe component
  summaries, and exact-body targets. `End2EndSafety.v` packages this in
  `assoc_direct_receiver_mixed_local_runtime_package` and derives the
  store-safe synthetic summary route evidence needed by the mixed route bridge.
- Two narrower checker building blocks now exist but are not yet promoted into
  the active endpoint.
  `check_env_root_shadow_synthetic_direct_call_ready_summary_when_direct` proves
  synthetic readiness only for bodies with a `direct_call_target_expr`, but a
  direct endpoint swap is still circular because the current route package asks
  for callee-level synthetic summary evidence.
  `check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_route_exact_target`
  is the next certificate boundary: its soundness lemma
  `check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_route_exact_target_package_in_local_bounds_family`
  packages ready-body exact-route evidence plus exact-target facts under local
  bounds without requiring synthetic direct-call evidence for no-target callees.
- The newer implementation roadmap is now treated as a phase map rather than a
  literal task list. Phase 1 is complete; the useful Phase 2 boundary is the
  existing local runtime package plus the remaining need to stop threading
  synthetic route evidence through the active mixed checker gate. Phase 4's
  split runtime theorem is already proved, but endpoint promotion remains
  blocked until the checker frontier accepts no-target local-bounds callees.

## Active Proof Plan

1. Retarget the public runtime theorem to the active mixed endpoint.
   - Completed: `infer_program_env_end2end_big_step_safe_checked_initial_ready`
     now targets `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Public premises remain no stronger than the current preservation packages.
   - Completed subtask: package the active mixed endpoint's provable local
     no-receiver runtime evidence in
     `assoc_direct_receiver_mixed_local_runtime_package`.
   - Completed subtask: package public runtime evidence plus explicit synthetic
     summary route evidence into
     `mixed_ready_body_or_narrow_summary_provider_route_bridge`.
   - Completed diagnostic subtask: the synthetic summary route evidence cannot
     be derived from the current public premises alone; it needs a local
     component certificate that combines route-summary readiness with
     exact-body-target evidence.
   - Completed implementation subtask: add the checker sidecar gate for the
     active mixed endpoint, package route-summary/exact-target evidence in
     `assoc_direct_receiver_mixed_local_runtime_package`, and derive the
     store-safe synthetic summary route evidence through the existing
     scoped-package lemmas.
   - Completed subtask: retarget the public theorem body to consume this
     package and make `infer_program_env_end2end_big_step_safe_checked_initial_ready`
     use `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Completed subtask: add the direct-target-only synthetic readiness checker
     `check_env_root_shadow_synthetic_direct_call_ready_summary_when_direct`
     plus its soundness projection. Keep the active endpoint on the older
     compile-proven synthetic route/exact-target sidecar until the route bridge
     can consume the narrowed certificate.
   - Completed diagnostic subtask: update `tests/diagnose_trait_gates.sh` to
     parse diagnostic gate output even when the checker exits nonzero on known
     rejected frontier cases; the diagnostic script now passes again.
   - Completed analysis subtask: a direct active-gate swap to
     `check_env_root_shadow_synthetic_direct_call_ready_summary_when_direct`
     is insufficient because the current route package demands callee-level
     synthetic summary evidence. The failure is at the route-package contract,
     not at the direct-target-only checker projection.
   - Completed implementation subtask: add the ready-body exact-route checker
     certificate
     `check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_route_exact_target`
     and prove its local-bounds package projection. This reuses the existing
     `store_safe_ready_body_exact_body_call_route_package_at` path and keeps the
     active endpoint unchanged while giving the next refactor a non-synthetic
     route package to consume.
   - Completed implementation attempt: directly refactoring
     `assoc_direct_receiver_mixed_local_runtime_package` to consume the
     ready-body exact-route projection does not compile while the active mixed
     endpoint exposes only the synthetic route sidecar. Adding
     `check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_ready_body_route_exact_target`
     as a global active mixed gate conjunct compiles, but it is too strong: the
     full regression suite rejects many existing valid function, lifetime,
     module, and trait programs with `ErrEndToEndSafetyGateFailed`.
   - Next implementation subtask: narrow the ready-body exact-route certificate
     to the no-receiver/direct-call component branch instead of making it a
     whole-environment active gate. The package consumer should be fed by a
     branch-scoped checker projection or a route-package field derived only when
     the component store-safe check selects the no-capture direct-call path.

2. Introduce an explicit runtime evidence package.
   - Status: partially complete. The current
     `assoc_direct_receiver_mixed_local_runtime_package` is the Phase 2 seed:
     it packages the active endpoint's checker-derived no-receiver runtime
     facts and is consumed by the public theorem.
   - Keep extending this package only when a runtime consumer actually needs
     more evidence: route selection, value/callback support, cleanup support,
     and local-bounds replay support may all belong in the final package.
   - Do not make the package route-only if that forces later theorem wrappers to
     reconstruct callback, cleanup, or local-bounds facts separately.
   - Target shape:

     ```text
     extracted checker accepts env
       -> checker certificate facts
       -> runtime evidence package
       -> checked-initial big-step safety
     ```

3. Close the direct-receiver local-bounds replay gap.
   - Earlier direct-receiver replay work is no longer the immediate blocker for
     the current frontier. The split theorem has a non-diagnostic safety proof,
     and the diagnostic split gate no longer carries the synthetic route
     sidecar.
   - The active blocker is narrower: the CLI still uses the mixed endpoint, and
     that endpoint's checker gate still requires the synthetic route/exact-target
     certificate for no-receiver component callees.
   - Prefer a route-package refactor or ready-body exact-route bridge over a
     broad global stability theorem.
   - Do not solve this by adding `check_env_end2end_direct_receiver_ready env' =
     true` as a final theorem premise.

4. Prove runtime safety for the split endpoint.
   - Target endpoint: `infer_program_env_end2end_assoc_direct_receiver_split`.
   - Target gate: `check_env_end2end_direct_receiver_split_ready`.
   - Completed subtask: package split-ready runtime facts in
     `direct_receiver_split_runtime_evidence_in_env` and prove the no-receiver
     branch consumer using that package.
   - Completed subtask: add a split-package consumer
     `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_runtime_evidence_and_direct_component_runtime_facts`,
     which uses the split combined captured/direct-component check without
     requiring full `check_env_end2end_direct_receiver_ready`.
   - Completed subtask: replace the direct consumer's explicit global runtime
     facts with the narrower theorem
     `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_runtime_evidence_and_local_runtime_facts`.
   - Completed correction: align the component branch with the split
     certificate by requiring `component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env`
     plus mixed route evidence instead of the stronger narrow-summary provider.
   - Completed subtask: derive `direct_receiver_method_body_runtime_facts_provider`
     from split evidence through a checker-backed sidecar requiring the ordinary
     provenance and preservation checks already used by the runtime facts lemmas.
   - Completed subtask: derive the split component summary provider from
     checker-backed ordinary provenance/preservation evidence, derive
     `component_body_local_bounds_mixed_ready_body_or_narrow_route_provider_in_env`
     through the existing summary-route bridge, and add the non-diagnostic
     theorem `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready`.
   - Completed subtask: add
     `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_exact_body_call_route_package`,
     which internalizes the abstract summary-route bridge through the existing
     exact-body route package.
   - Completed subtask: add the split checker-backed synthetic route/exact-target
     sidecar, derive split local route-summary/exact-target evidence, and make
     `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready`
     use the same public preservation-premise shape as the active mixed theorem.
   - Completed subtask: switch the diagnostic split-ready gate to the
     ready-body provider check while preserving the split runtime-safety theorem.
     This removes the synthetic route/exact-target sidecar from the split-ready
     certificate itself.
   - Status: the split theorem is proved. The remaining blocker is not the
     theorem premise shape; it is the checker frontier of the still-active mixed
     endpoint.
   - Completed diagnostic subtask: a direct-target-only checker certificate now
     proves synthetic readiness exactly at discovered direct-call targets, but a
     naive endpoint switch is circular because the ready-body route provider
     still depends on the synthetic route bridge it is meant to replace.
   - Completed implementation subtask: add a ready-body exact-route checker
     certificate and local-bounds package projection. This is the candidate
     replacement for the active mixed endpoint's synthetic route sidecar.
   - Completed implementation attempt: consuming the ready-body exact-route
     package from the mixed local runtime package is blocked by certificate
     scope, not just proof ordering. A global active gate for the ready-body
     exact-route checker rejects broad existing valid programs.
   - Next subtask: derive the ready-body exact-route package from a branch-scoped
     no-capture direct-call component certificate, then switch the local runtime
     package consumer. After that, rerun `tests/run.sh` and only promote the
     split endpoint if the checker frontier is clean.
   - Required theorem:

     ```coq
     infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready
     ```

   - The theorem must consume the split certificate directly and must not depend
     on the diagnostic assumption:

     ```coq
     check_env_root_shadow_direct_receiver_method_present env' = false \/
     check_env_end2end_direct_receiver_ready env' = true
     ```

5. Promote the split endpoint only after the proof and checker frontier close.
   - Switch the CLI from
     `infer_program_env_end2end_assoc_direct_receiver_mixed` to
     `infer_program_env_end2end_assoc_direct_receiver_split`.
   - Keep `--diagnose-trait-gates` diagnostic-only; it must not become an
     acceptance path.
   - Re-run Rocq extraction before relying on dune builds.
   - Do not promote while `tests/run.sh` rejects valid local-bounds/direct-call
     programs or `tests/diagnose_trait_gates.sh` reports the synthetic-summary
     no-target blocker.

6. Promote receiver tests conservatively.
   - Move only direct-receiver fixtures justified by the proved split endpoint
     from invalid to valid.
   - Do not bulk-promote field-bearing struct receivers, payload enum receivers,
     local inferred call receivers, call-initialized/general annotated locals, or
     dot syntax receivers.

## Unresolved Blockers

- The public runtime theorem retarget is complete for the active mixed endpoint.
  The earlier value/cleanup bridge gap is closed by deriving the required
  synthetic route evidence from the mixed endpoint's checker-backed local
  runtime package.
- The active mixed endpoint has a local runtime package with
  ready-body-or-narrow summary evidence, alpha-body callback evidence, and a
  checker-backed synthetic route-summary/exact-target certificate. A
  ready-body route exact-target checker and local-bounds projection exist, but a
  whole-environment active gate for that checker is too strong. The next proof
  step is a branch-scoped projection for no-capture direct-call components, not
  a global active-gate conjunct.
- The diagnostic split endpoint remains promising but cannot become the CLI
  authority yet. The no-receiver branch has a package-backed consumer, and the
  direct-receiver-present branch has a lower split-package consumer that avoids
  synthetic-summary runtime facts as explicit theorem premises. The required
  theorem
  `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready`
  now compiles with the same public preservation-premise shape as the active
  mixed theorem. The unresolved blocker is the checker certificate, not the
  public theorem premise shape: the split-ready gate no longer carries the
  synthetic route/exact-target sidecar, but the active mixed endpoint still does.
  The narrowed `when_direct` checker certificate is the next candidate for the
  active route certificate, but the existing route package still re-enters the
  synthetic route provider by asking for callee-level synthetic summary evidence.
  `sh tests/diagnose_trait_gates.sh` now passes and tracks this frontier.
  `sh tests/run.sh` still fails on valid direct-call/local-bounds programs
  because the active end-to-end gate remains closed.

## Unsupported Or Deferred Features

Do not add or expand these until the type-safety endpoint is stable:

```text
dot method syntax
associated type defaults
equality constraints
deriving
field-bearing struct receivers
payload enum receivers
generic direct-call receiver generalization
call-initialized local receiver generalization
new OCaml fallback logic
```

## Non-Negotiable Constraints

- Rocq definitions are the source of truth.
- Generated OCaml extraction artifacts must not be edited manually:
  `fixtures/TypeChecker.ml` and `fixtures/TypeChecker.mli` change only through
  Rocq extraction.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Do not weaken the public type-safety theorem by adding ad hoc public premises.
- Do not try to prove split readiness implies ordinary direct readiness; the
  split gate exists because ordinary direct readiness is too strong for some
  valid direct-receiver-method programs.
- No `Admitted`, `Axiom`, or `Abort` in the final proof path.
- Do not add more theorem variants of the form
  `...with_X_and_Y_and_Z_and_callback_and_bridge...`; package those facts into a
  runtime evidence record instead.

## Key Commands

Before completing type-system-related work, run the relevant checks from the
repository root unless noted:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/diagnose_trait_gates.sh
rg -n "Admitted\.|Axiom|Abort\." rocq/theories
```

When the CLI endpoint changes, regenerate extraction through `cd rocq && make`
before relying on `dune build` or CLI tests.

## Acceptance Criteria

The trait type-safety implementation is complete for this roadmap slice when:

1. Done: `infer_program_env_end2end_big_step_safe_checked_initial_ready` targets
   the active checker endpoint.
2. The CLI accept/reject path uses only an extracted Rocq endpoint.
3. The split endpoint has a non-diagnostic checked-initial runtime-safety theorem and a checker frontier that accepts valid no-target local-bounds callees.
4. No final runtime theorem depends on the diagnostic no-receiver/direct-ready
   case assumption.
5. Direct-receiver trait programs accepted by the CLI are covered by the public
   checked-initial big-step theorem.
6. Unsupported receiver shapes remain rejected.
7. `plan/trait_new_roadmap.md` and this file agree on the active endpoint,
   proved theorem, remaining blocked receiver forms, promoted test files, and
   deferred features.
