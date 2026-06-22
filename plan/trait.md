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
  `check_env_end2end_direct_receiver_split_ready`. Diagnostics show that it can
  accept direct-call receiver fixtures rejected by the active mixed endpoint, but
  it is not yet the active checker authority and does not yet have the required
  non-diagnostic runtime-safety theorem. `End2EndSafety.v` now has
  `direct_receiver_split_runtime_evidence_in_env`, which packages split-ready
  runtime facts and closes the no-receiver branch through
  `infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_when_no_receiver_with_runtime_evidence`.
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
- `CheckerRootSidecars.v` now exposes the active mixed endpoint's
  checker-backed component certificate for selected no-capture direct-call
  callees under local bounds: synthetic route summaries, store-safe component
  summaries, and exact-body targets. `End2EndSafety.v` packages this in
  `assoc_direct_receiver_mixed_local_runtime_package` and derives the
  store-safe synthetic summary route evidence needed by the mixed route bridge.

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
   - Next subtask: start the split endpoint runtime-safety proof using the same
     evidence-package style, without relying on the diagnostic no-receiver/direct-ready
     disjunction as a public premise.

2. Introduce an explicit runtime evidence package.
   - Extend the current local package only when a runtime consumer needs more
     evidence: route selection, value/callback support, cleanup support, and
     local-bounds replay support may all belong in the final package.
   - Do not make the final package route-only if that forces later theorem
     wrappers to reconstruct callback, cleanup, or local-bounds facts separately.
   - The intended shape is:

     ```text
     extracted checker accepts env
       -> checker certificate facts
       -> runtime evidence package
       -> checked-initial big-step safety
     ```

3. Close the direct-receiver local-bounds replay gap.
   - The known blocker is direct-receiver method evidence under local bounds, or
     an equivalent replay theorem that consumes the direct summary without
     reconstructing whole-environment generic provenance/preservation readiness.
   - Prefer a narrow replay-facing lemma over a broad global stability theorem.
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
   - Next subtask: derive the split route package from checker-backed local
     runtime evidence, so the split theorem has the same public premise shape as
     the active mixed endpoint before promotion.
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

5. Promote the split endpoint only after its proof closes.
   - Do not change the CLI active endpoint until the split endpoint has checker
     soundness, runtime evidence, and checked-initial runtime safety.
   - After the proof closes, switch the CLI from
     `infer_program_env_end2end_assoc_direct_receiver_mixed` to
     `infer_program_env_end2end_assoc_direct_receiver_split`.
   - `--diagnose-trait-gates` may remain diagnostic, but it must not become an
     acceptance path.

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
- The active mixed endpoint now has a local runtime package with
  ready-body-or-narrow summary evidence, alpha-body callback evidence, and a
  checker-backed route-summary/exact-target certificate. The package is threaded
  through the public runtime theorem for selected component local bounds.
- The diagnostic split endpoint remains promising but cannot become the CLI
  authority until it has a non-diagnostic checked-initial runtime-safety theorem.
  The no-receiver branch now has a package-backed consumer. The
  direct-receiver-present branch now has a lower split-package consumer that
  avoids synthetic-summary runtime facts as explicit theorem premises. The direct
  method body runtime provider is checker-backed by a sidecar over ordinary
  provenance and preservation checks; this is sound and keeps the proof moving,
  but it deliberately strengthens the diagnostic split gate until the route
  certificate is narrowed. A non-diagnostic split runtime theorem now exists and
  consumes the existing summary-route bridge. A concrete split theorem now
  internalizes that bridge through the existing exact-body route package. The
  remaining promotion blocker is deriving the route package from split
  checker-backed local runtime evidence, matching the active mixed endpoint's
  public premise shape before switching the CLI.

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
3. The split endpoint has a non-diagnostic checked-initial runtime-safety theorem.
4. No final runtime theorem depends on the diagnostic no-receiver/direct-ready
   case assumption.
5. Direct-receiver trait programs accepted by the CLI are covered by the public
   checked-initial big-step theorem.
6. Unsupported receiver shapes remain rejected.
7. `plan/trait_new_roadmap.md` and this file agree on the active endpoint,
   proved theorem, remaining blocked receiver forms, promoted test files, and
   deferred features.
