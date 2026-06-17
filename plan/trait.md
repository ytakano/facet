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
- Proof infrastructure for direct-call receivers includes active-mixed branch
  splits, no-receiver/direct-ready bridges, local-bounds route helpers,
  exact-body route/package bridges, public-callback wrappers for the active
  mixed endpoint, active-mixed runtime theorems under the assoc-compatible
  store-safe synthetic direct-call route, active public-form store-safe summary
  route, and strict-public store-safe summary route, a public-prefix bridge
  that retargets
  the active mixed endpoint once the summary-evidence route is supplied, a
  strict-public runtime bridge through that active mixed prefix/summary route,
  strict-public exact-body/package, package-at, and component summary
  provider/check, component-only same-result, assoc-base non-captured
  provider, store-safe summary-evidence, component-check, component-body
  store-safe summary, component-body summary, component-body summary scoped
  provider branch, component-body summary boolean branch, branch shadow summary,
  branch not-captured, branch
  absent-captured summary, package-at component-body, and
  package-at component-check branch, call-statement component-check, and
  local-bounds component-check branch, and scoped-package component-check
  bridges through active mixed public routes, public-form
  exact-body/package-to-summary route
  conversions,
  and a runtime theorem for `assoc_direct_receiver_base` under
  the existing global replay evidence, exported verified
  `assoc_direct_receiver_base` diagnostic endpoints with direct-component,
  global-summary, per-component summary, and
  single-sidecar provenance/preservation/component-summary ready checks plus
  a component-only boolean evidence bridge, runtime theorem under explicit
  provenance/preservation evidence, active-to-base and strict-to-active checker
  agreement, and reconstructed same-result bridge into the active mixed
  public-callback route,
  proved-safe absent/synthetic/component mixed endpoints, explicit public
  exact-body/package, package-at, component-summary branch package-at,
  component-check branch package-at, no-capture scoped-package bridges,
  local-bounds derived exact-body public route bridges, branch bridges that
  remove the separate exact-body premise, accept package-at with-body-summary
  providers, convert component body-summary booleans into membership-scoped
  check providers, and expose public-callback no-receiver branch routes through
  scoped Prop providers, scoped check providers, unscoped provider wrappers, or
  booleans while preserving the direct-ready branch, plus a provider-based
  runtime bridge for `assoc_direct_receiver_base_combined` that
  can route direct receiver methods through scoped body-lift providers while
  routing no-capture components through component-body summary providers. The
  stronger endpoints remain proof diagnostics because their gates rejected broad
  existing valid coverage or the direct-call receiver fixtures when tried as
  active authorities.
- The remaining activation gap is proof-side: the strict public subset now
  implies active mixed checker success and has runtime bridges through the
  active mixed public-form store-safe summary, strict-public store-safe
  summary, prefix/summary, and exact-body/package routes, and
  exact-body/package facts now expose the public-form summary route directly,
  and strict public routing can consume the no-receiver component summary
  provider/check, component-only same-result, assoc-base non-captured provider,
  store-safe summary-evidence, component-check, component-body store-safe
  summary, component-body summary, component-body summary scoped provider
  branch, component-body summary boolean branch, branch shadow summary,
  branch not-captured,
  branch absent-captured summary, package-at component-body, package-at
  component-check, call-statement component-check, local-bounds component-check,
  and scoped-package component-check branches through active mixed; the canonical public theorem
  still needs those facts derived from existing public premises.
  The
  active no-capture component branch now has scoped-package, public derived
  exact-body, package-at with-body-summary provider bridges from component
  routes, and a public-callback boolean component body-summary branch bridge;
  it no longer needs a separate exact-body premise. Active mixed success now
  implies the broader base checker,
  and the component-only diagnostic endpoint can be reconstructed from active
  mixed no-receiver plus the body-summary check. The no-receiver branch also
  has public-callback routes that consume membership-scoped component
  body-summary Prop or check providers directly, with unscoped provider and
  boolean wrappers for existing diagnostics; the canonical theorem still needs
  one of those providers/checks derived without a new theorem premise. Receiver-method
  absence alone does not imply that component route, so those paths remain
  diagnostic rather than activation bridges.
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
   - Replace the over-broad provenance/preservation sidecars with a runtime
     route that consumes the component-only boolean evidence bridge plus static
     prefix/exact-body package facts, without requiring Prop-to-bool
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

- Strict direct-receiver, absence-mixed, synthetic-mixed, and component-mixed
  endpoint trials reject broad valid coverage with
  `ErrEndToEndSafetyGateFailed`; the component-mixed endpoint was rechecked
  against the current suite and still fails ordinary valid programs. The
  exported base direct-component ready-check endpoint is runtime-safe but still
  rejects both direct-call receiver safety-gate fixtures, so these remain
  proof/diagnostic infrastructure, not active authorities.
- The active mixed endpoint now has strict-to-active checker agreement,
  explicit public exact-body/package, public-form store-safe summary,
  strict-public store-safe summary, exact-body/package-to-summary route
  conversions, strict-public exact-body/package, package-at, component
  summary provider/check routes, component-only same-result routes, assoc-base
  non-captured provider routes, store-safe summary-evidence routes,
  component-check routes, component-body store-safe summary routes,
  component-body summary routes, component-body summary scoped provider branch
  routes, component-body summary boolean branch routes, branch shadow summary
  routes, branch not-captured routes, branch absent-captured summary routes, and package-at
  component-body branch routes, package-at component-check branch routes,
  call-statement component-check routes, local-bounds component-check branch
  routes, scoped-package component-check routes, component-summary branch package-at, component-check branch
  package-at, no-capture scoped-package, local-bounds derived
  exact-body public bridges, a branch bridge that derives the exact-body route
  from the component route instead of requiring a separate premise, branch
  bridges that consume package or package-at with-body-summary providers
  directly, and static
  local-bounds plus public-callback no-receiver branch wrappers that consume
  membership-scoped component body-summary Prop or check providers without
  treating them as unrestricted global Prop providers. The canonical theorem
  still lacks a proof that the required provider/check and per-callee
  summary/evidence-at facts follow from its existing public premises.
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
