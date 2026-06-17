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
  active mixed endpoint. It now has no-receiver/direct-ready branch splits,
  strict-to-active agreement, public-callback wrappers, exact-body/package and
  package-at bridges, active/strict public store-safe summary routes,
  prefix-evidence bridges, and component-summary/component-check routes for
  package, package-at-all, local-bounds, derived local-bounds, scoped-package,
  and call-statement variants. Recent cleanup has routed the package
  component-check wrapper, package component-body-summary provider wrapper,
  local-bounds exact-body static wrapper, local-bounds route branch,
  local-bounds component body-summary branch and store-static wrapper,
  active/strict public no-receiver component-body-summary boolean check routes,
  active/strict public no-receiver component-body-summary provider wrappers, strict branch provider/check wrappers, branch, public package, and public package-at-all exact-body summary-evidence wrappers, active and receiver-method public no-receiver exact-body wrappers, and provider/check routes,
  active/strict component-only same-result and derived wrappers, uncaptured exact-body package branch,
  exact-non-captured and
  exact-local-bounds provider branches, non-captured branch, non-captured
  component branch, and active/strict assoc-base branch callback routes through
  prefix evidence
  instead of broad store-static sidecars.
- Diagnostic endpoints remain available for `assoc_direct_receiver_base`,
  `assoc_direct_receiver_base_combined`, strict direct-receiver,
  absence-mixed, synthetic-mixed, and component-mixed variants. They are useful
  for proving route fragments and checking sampled fixtures, but they are not
  active checker authorities because their gates reject either broad valid
  coverage or the direct-call receiver safety-gate fixtures.
- The remaining activation gap is proof-side. The canonical public runtime
  theorem still targets the strict mixed endpoint; retargeting it to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` requires deriving,
  from existing public premises, the no-receiver component summary/check
  provider and per-callee summary/evidence-at facts consumed by the active
  mixed public corollaries. Receiver-method absence alone does not imply those
  component routes, so the provider/check paths remain diagnostic until that
  derivation is proved without a new public theorem premise.
- Associated type defaults, equality constraints, and `deriving` are reserved
  for future surface forms. Provisional syntax for them is explicitly rejected
  with parser diagnostics.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` by deriving the
     exact-body target, pointwise package-at evidence, and component-check
     or component-summary provider required by the active-mixed public
     corollaries, without adding OCaml fallback logic or weakening the public
     theorem with a new premise.
   - Derive the summary-evidence route from the public prefix-route premises,
     or otherwise prove an equivalent public-premise-free lift for the active
     mixed no-receiver branch.
   - Continue replacing over-broad provenance/preservation and remaining
     store-static sidecars with runtime routes that consume prefix evidence,
     exact-body package facts, and the component-only boolean bridge, without
     requiring Prop-to-bool completeness for component summaries.
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

- Strict direct-receiver, absence-mixed, synthetic-mixed, and component-mixed
  endpoint trials reject broad valid coverage with
  `ErrEndToEndSafetyGateFailed`; the component-mixed endpoint was rechecked
  against the current suite and still fails ordinary valid programs. The
  exported base direct-component ready-check endpoint is runtime-safe but still
  rejects both direct-call receiver safety-gate fixtures, so these remain
  proof/diagnostic infrastructure, not active authorities.
- The active mixed endpoint has enough routed lemmas for summary evidence,
  exact-body/package, package-at, package-at-all, local-bounds, local-bounds
  route branch, derived local-bounds, scoped-package, local-bounds component
  body-summary branch/store-static wrapper, active/strict public no-receiver
  component-body summary boolean check routes, active/strict public no-receiver
  component-body summary provider/check routes, uncaptured exact-body package branch,
  exact-non-captured and exact-local-bounds
  provider branches, component summary/check, component-body summary, branch
  shadow/not-captured/absent-captured, call-statement component-check,
  non-captured branch, non-captured component branch and active/strict
  assoc-base branch callbacks, and public-callback no-receiver provider/check
  variants. The canonical theorem
  still lacks the bridge from its public premises to the required
  provider/check and per-callee summary/evidence-at facts.
- The assoc direct-receiver-base endpoint accepts the basic direct-call receiver
  fixture and now has a runtime theorem under the existing global replay
  evidence, but it is not the active CLI authority and is not connected to the
  public runtime theorem without extra evidence. Its mixed wrapper preserves
  ordinary valid coverage but still rejects the direct-call receiver fixture
  because the direct-ready branch requires the global component gate; the
  exported direct-component ready-check wrapper also rejects those fixtures.
- A diagnostic retarget to `assoc_direct_receiver_base_combined` accepted the
  short and explicit direct-call receiver UFCS safety-gate fixtures and
  preserved the current regression suite except for those two expected-invalid
  flips. The exported `base_combined_summary_ready_checks` wrapper is proved
  runtime-safe under the summary-exact package route, but rejects those fixtures
  and representative valid programs because the global synthetic-summary check
  is too broad. Single-sidecar diagnostic retargets showed that both
  `base_combined_provenance_ready_checks` and
  `base_combined_preservation_ready_checks` reject the targeted direct-call
  receiver fixtures and representative valid programs, while
  `base_combined_component_only_summary_ready_checks` accepts all four sampled
  cases. That component-only endpoint now has a runtime theorem under explicit
  provenance/preservation evidence, and active mixed can reconstruct the endpoint
  on the no-receiver branch once the component body-summary check is known. It is
  still diagnostic because the canonical public premises do not yet imply that
  body-summary check or the needed per-callee evidence.

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
