# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Traits, impls, associated types, trait methods, method-local type parameters,
  generic-trait impl remapping, and associated type projections are parsed,
  lowered, and checked through the extracted Rocq checker. Associated
  projections in signature and surface type positions, plus explicit UFCS method
  targets, reject lifetime arguments in trait refs at checker boundaries. Impl
  method bodies are elaborated to hidden functions and checked even when
  uncalled.
- Method calls use receiver-first prefix UFCS forms:
  `(<Ty as Trait>::method receiver args...)` and
  `(Trait::method receiver args...)`. Generic trait arguments remain explicit
  through the former spelling; dot syntax remains rejected for this phase.
- Short UFCS currently accepts receiver types known before checker execution:
  function parameters, typed literals, annotated pure local literals after
  receiver-let elimination regardless of mutability, inferred pure local
  literal/unit receivers regardless of mutability, fieldless struct literals and
  payloadless enum constructors, including generic instances, as direct
  receivers or after local receiver-let elimination, with store-safe argument
  evidence checked in Rocq.
- Still-gated receiver forms are field-bearing struct literals and
  payload-bearing enum constructors, including generic instances, direct-call
  receivers, generic direct-call receivers, non-pure inferred locals, annotated
  locals initialized by calls, and other general annotated locals.
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only extracted checker authority, with no fallback acceptance path. Public
  checker soundness aliases target this assoc-base mixed endpoint. The public
  runtime theorem `infer_program_env_end2end_big_step_safe_checked_initial_ready`
  still targets the strict mixed endpoint.
- Proof infrastructure for direct-call receivers is concentrated around the
  active mixed endpoint, its retained direct-ready branch helper, the
  local-bounds route theorem, component-summary local-bounds route lemma,
  no-receiver component-body provider conversions,
  provider/body-summary/store-safe/check prefix theorems, and
  assoc-base check-provider helper path used by active public-path proofs.
  Obsolete helper chains and wrapper aliases around active-mixed,
  assoc-strict, receiver-method, assoc-base/direct-receiver-base, scoped-lift,
  and diagnostic routes have been pruned; the remaining self-only
  active-mixed compatibility/uniqueness helpers plus receiver-method
  exact-closure and package-at route helpers were also removed.
- Diagnostic endpoints remain available for `assoc_direct_receiver_base`,
  `assoc_direct_receiver_base_combined`, and assoc strict direct-receiver
  variants. They are useful for proving route fragments and checking sampled
  fixtures, but their unreferenced runtime wrapper aliases have been pruned and
  they are not active checker authorities because their gates reject either
  broad valid coverage or the direct-call receiver safety-gate fixtures.
- The remaining activation gap is proof-side. The canonical public runtime
  theorem still targets the strict mixed endpoint through the public prefix
  theorem; retargeting it
  to `infer_program_env_end2end_assoc_direct_receiver_mixed` requires deriving,
  from existing public premises, the no-receiver component summary/check
  provider and per-callee summary/evidence-at facts consumed by the retained
  mixed no-receiver prefix path. Receiver-method absence alone does not imply
  those component routes. A trial that strengthened the active no-receiver gate
  with the component body-summary check compiled and retargeted the theorem, but
  rejected broad existing valid coverage with `ErrEndToEndSafetyGateFailed`, so
  that gate strengthening was not adopted.
- Associated type defaults, equality constraints, and `deriving` are reserved
  for future surface forms. Provisional syntax for them is explicitly rejected
  with parser diagnostics.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` by deriving the
     exact-body target, pointwise package-at evidence, and component-check
     or component-summary provider required by the retained active-mixed
     no-receiver prefix path, without adding OCaml fallback logic or weakening
     the public theorem with a new premise.
   - Derive the summary-evidence route from the public prefix-route premises,
     or otherwise prove an equivalent public-premise-free lift for the active
     mixed no-receiver branch.
   - Continue replacing any remaining broad provenance/preservation premises
     with runtime routes that consume prefix evidence, exact-body package facts,
     and the component-only boolean bridge, without requiring Prop-to-bool
     completeness for component summaries.
   - Add positive direct-call receiver UFCS tests only after the active
     extracted checker accepts them through the verified endpoint. Keep existing
     direct-call receiver safety-gate tests invalid until that switch lands.

2. Extend receiver coverage conservatively.
   - Keep receiver-first prefix calls as the canonical surface syntax.
   - Add the remaining receiver forms only when Rocq checker summaries and
     safety proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- Assoc strict direct-receiver endpoint trials reject broad valid coverage with
  `ErrEndToEndSafetyGateFailed`. The rejected non-assoc strict direct-receiver,
  absence-mixed, synthetic-mixed, component-mixed, strict-branch, and
  direct-component runtime diagnostics, plus their now-unused ready-check
  helper booleans, have been removed; the base direct-component endpoint
  remains diagnostic proof infrastructure, not an active authority.
- The active mixed endpoint has routed lemmas for the known summary,
  exact-body/package, local-bounds, component-summary local-bounds,
  scoped-package, call-statement, component
  summary/check, component-body summary, non-captured, no-receiver
  Prop-provider prefix, and assoc-base callback paths. The canonical theorem
  still lacks the bridge from its public premises
  to the no-receiver provider/check and per-callee summary/evidence-at facts;
  only the retained direct-ready branch helper, local-bounds route theorem,
  no-receiver component-body provider conversions and provider/body-summary/store-safe/check
  prefix theorems, plus the assoc-base check-provider helper path, remain on
  that late proof surface.
  Strengthening the active no-receiver gate with the body-summary check
  is known to reject existing valid programs, so the bridge must come from a more precise proof route or broader
  checker summaries.
- The assoc direct-receiver-base endpoint accepts the basic direct-call receiver
  fixture, but it is not the active CLI authority and no longer has a
  retained runtime wrapper theorem. Its mixed wrapper preserves ordinary
  valid coverage but still rejects the direct-call receiver fixture because
  the direct-ready branch requires the global component gate.
- A diagnostic retarget to `assoc_direct_receiver_base_combined` accepted the
  short and explicit direct-call receiver UFCS safety-gate fixtures and
  preserved the current regression suite except for those two expected-invalid
  flips; its unreferenced runtime wrappers and the rejected broad,
  direct-component, and component-only summary ready-check diagnostics have
  been removed.

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

For docs-only roadmap maintenance, `git diff --check` is sufficient unless the
edit changes stated behavior or proof obligations. The final marker search must
not introduce new proof holes or debug leftovers when Rocq files are touched.
Existing legacy proof-script selector matches should be called out explicitly if
they remain unrelated to the change.
