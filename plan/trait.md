# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Traits, impls, associated types, and trait methods are parsed, lowered into
  Rocq/extracted environments, and checked by the extracted checker for
  duplicate/missing/extra/mismatched associated items. Impl method bodies are
  elaborated to hidden functions and checked even when the method is not called.
- Method-local type parameters are supported for trait and impl methods,
  including method-local bounds and generic-trait impl remapping. Method-local
  lifetime generics remain deferred and are rejected by tests.
- Method calls use receiver-first prefix UFCS forms:
  `(<Ty as Trait>::method receiver args...)` and
  `(Trait::method receiver args...)`. Dot syntax remains rejected for this
  phase.
- Short UFCS currently accepts receiver types known before checker execution:
  function parameters, typed literals, immutable pure local literals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors whose store-safe argument evidence is checked in Rocq.
  Field-bearing struct literals, payload-bearing enum constructors, direct-call
  receivers, generic direct-call receivers, non-pure inferred locals, and
  general annotated locals remain gated.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries.
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only extracted checker authority, with no fallback acceptance path. Public
  checker soundness aliases target this assoc-base mixed endpoint. The public
  runtime theorem `infer_program_env_end2end_big_step_safe_checked_initial_ready`
  still targets the strict mixed endpoint.
- Direct-call receiver proof work has established the active mixed endpoint,
  branch splits for direct-ready/no-receiver cases, public wrappers for the main
  route families, no-receiver receiver-method target absence/collapse facts,
  exact-closure bridges for local-bounds routes, seen callees, direct-callee
  component checks, exact-body targets, unconditional Prop-level combined
  local-bounds summaries, no-receiver receiver-aware combined readiness,
  component-body/component-with-body-summary providers, extracted absence and
  synthetic proof endpoints, an assoc direct-receiver-base per-function gate,
  literal narrow-summary support, and an assoc direct-receiver-base mixed proof
  endpoint that combines the per-function gate with the existing mixed env gate.
  The direct-receiver method sidecar now accepts the basic UFCS direct receiver
  fixture, and the assoc direct-receiver-base endpoint accepts that fixture; the
  new base-mixed endpoint is proof infrastructure and is not the active CLI
  authority. Its proof facts now expose the no-receiver/direct-ready branch
  split and constructors from the base endpoint plus either branch condition. A
  separate assoc direct-receiver-base combined endpoint now records the base
  per-function gate plus the combined direct-receiver summary gate, without
  requiring the full env-level provenance, preservation, and component gates;
  its proof helpers expose Prop-level combined readiness, local-bounds-family
  providers, uniqueness, and a runtime bridge parameterized by separately
  supplied provenance, preservation, and synthetic-call summary evidence. A
  narrower direct-receiver-method-or-component summary now has checker and Prop
  readiness facts plus an assoc direct-receiver-base proof endpoint with
  uniqueness, soundness, readiness, local-bounds-family helpers, and a runtime
  bridge parameterized by the remaining provenance, preservation, and
  synthetic-call summary evidence; direct-receiver replay is discharged by a
  proven-provider variant. Selected raw, scoped-body-lift-ready, and
  scoped-expr-lift variants remain available for lower-level replay work. It
  remains proof infrastructure and is not the active or extracted authority.
- The remaining activation gap is proof-side and specific to the no-receiver
  branch. The active endpoint exposes only a combined captured-or-component
  summary there. Existing route wrappers need either plain synthetic summary
  evidence, a no-capture component/closure provider, an exact-body route
  package, or captured-summary absence for local-bounds-family functions. The
  current captured-summary checker can succeed on whole function bodies, so
  receiver-method target absence alone does not imply captured-summary absence.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding
     OCaml fallback logic or weakening the public theorem with a new premise.
   - Derive, from the active endpoint or existing public callbacks, one concrete
     no-receiver-branch provider strong enough for the existing active-endpoint
     wrappers: exact-body route-package, summary-at or store-safe
     evidence-at, store-safe or plain shadow summary evidence, checked
     component summary, component-body store-safe/summary evidence,
     local-bounds route evidence, an endpoint-derived not-captured/non-captured
     provider, exact non-captured provider evidence, an exact-body
     local-bounds/scoped package provider, or a behavior-preserving way to make
     the active mixed endpoint require the extracted absence gate only where it
     is needed.
   - Add positive direct-call receiver UFCS tests only after the active extracted
     checker accepts them through the verified endpoint. Keep existing
     direct-call receiver safety-gate tests invalid until that switch lands.

2. Extend receiver coverage conservatively.
   - Keep the canonical surface syntax as receiver-first prefix calls.
   - Add field-bearing struct literal, payload-bearing enum constructor,
     generic direct-call receiver, non-pure inferred local, and general
     annotated-local receivers only when Rocq checker summaries and safety
     proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- A trial switch to the strict direct-receiver endpoint rejected existing valid
  programs such as `tests/valid/assign/basic_assign.facet` with
  `ErrEndToEndSafetyGateFailed`. The assoc-base mixed endpoint avoids that gate
  for programs without direct receiver-method bodies and is now the active OCaml
  authority.
- Direct-call receiver activation is now blocked beyond the combined summary
  gate. The direct-receiver method sidecar is true for `main` in the basic
  direct-call receiver fixture, `infer_program_env_end2end_assoc_direct_receiver_base`
  accepts it, and the new base-combined endpoint isolates the combined summary
  gate. Its runtime bridge now identifies the remaining missing evidence as
  provenance, preservation, and synthetic-call summary readiness. The new
  direct-receiver-method-or-component endpoint consumes the narrow checker gate
  and now has a runtime bridge that avoids the captured-summary combined gate,
  but the bridge still takes provenance, preservation, and synthetic-call
  summary evidence as premises. Temporary diagnostics still show the full
  direct-ready env gate failing on `provenance=false`,
  `preservation=false`, and `component=false`, so the public runtime theorem
  still needs those facts derived from the active endpoint or replaced by a
  behavior-preserving direct-receiver branch provider.
- The strongest existing assoc-base paths remain proof endpoints, not behavior-
  compatible authorities. Temporary CLI swaps to the absence-mixed and
  synthetic-mixed endpoints rejected broad existing valid coverage with
  `ErrEndToEndSafetyGateFailed`; the assoc direct-receiver-base endpoint now
  accepts the basic direct-call receiver fixture but is not the active CLI
  authority.

## Key Decisions

- Rocq definitions are the source of truth. Generated OCaml extraction artifacts
  are regenerated from Rocq and are not edited manually.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Associated type defaults and equality constraints are out of scope for the
  current implementation pass.
- Dot method calls remain syntax-level rejected until they can desugar to the
  same receiver-first prefix form before Rocq checking.
- Future deriving must expand to ordinary impl declarations validated by the
  extracted checker; no parser-only generated acceptance path is allowed.

## Required Checks

For type-system or checker-facing implementation tasks, run:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
```

The final search must not introduce new proof holes or debug leftovers. Existing
legacy proof-script selector matches should be called out explicitly if they
remain unrelated to the change.
