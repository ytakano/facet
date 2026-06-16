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
  component-body/component-with-body-summary providers from component checks and
  from the direct-ready branch, and an extracted captured-summary absence gate
  with endpoint-local facts plus public and local-bounds branch wrappers
  consumable by exact/non-captured routes. Separate extracted stricter
  endpoints now cover two no-receiver branch shapes:
  `infer_program_env_end2end_assoc_direct_receiver_absent_mixed` requires
  captured-summary absence, and
  `infer_program_env_end2end_assoc_direct_receiver_synthetic_mixed` requires
  plain synthetic direct-call summary evidence. Both endpoints have checker
  soundness aliases, imply the active mixed endpoint, and have public runtime
  safety wrappers.
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
- The remaining direct-call receiver activation blocker is the no-receiver
  route/evidence source. The active mixed endpoint gives combined
  captured-or-component summaries. Existing active mixed case-split wrappers can
  use those summaries only with additional route-preservation or exact-body
  callbacks, and the final public theorem currently has no such extra premise.
  Existing public runtime wrappers still need one stronger input: exact-body
  route package, summary-at/store-safe evidence-at, store-safe/plain shadow
  summary evidence, checked component or closure summary, local-bounds route
  evidence, endpoint-derived not-captured evidence, exact non-captured evidence,
  or an exact-body scoped package.
- The strongest existing assoc-base paths are now stricter proof endpoints for
  captured-summary absence and synthetic-summary evidence on the no-receiver
  branch. The checker exposes the captured-summary absence gate, synthetic
  direct-call summary gate, endpoint-local local-bounds facts, public/local-
  bounds branch wrappers, and runtime safety wrappers for both stricter
  endpoints. Temporary CLI swaps to the absence-mixed endpoint and the
  synthetic-mixed endpoint both rejected broad existing valid coverage
  (`basic_assign`, assign/borrow/core/enum/function/lifetime/module/struct/
  trait, and type-safety-ready-gap cases) with `ErrEndToEndSafetyGateFailed`,
  so these are proof infrastructure rather than behavior-compatible authorities
  until a stricter endpoint is shown to preserve valid coverage. The active mixed
  endpoint still does not require either stronger gate in the no-receiver
  branch, so the public theorem cannot be retargeted to the active CLI
  authority yet. Current receiver-method target absence is insufficient because
  ordinary captured-call summaries are distinct from receiver-method summaries.

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
