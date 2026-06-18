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
  local-bounds route theorem, direct local-bounds sidecar bridge,
  ready-body local-bounds evidence and pointwise callee bridges,
  conditional and unconditional boolean wrappers, extracted no-receiver
  diagnostic check,
  public-shaped active-mixed conditional sidecar theorem,
  core mixed no-receiver summary-provider prefix route, and assoc-base
  check-provider helper path used by active public-path proofs. Obsolete
  active-mixed, assoc-strict, receiver-method, diagnostic, broad
  body-summary-provider, and single-use direct-ready helper detours have been
  pruned.
- Diagnostic endpoints remain available for the extracted no-receiver
  body-summary gate, `assoc_direct_receiver_base`,
  `assoc_direct_receiver_base_combined`, and assoc strict direct-receiver
  variants. They are useful for proving route fragments and checking sampled
  fixtures, but they are not active checker authorities because their gates
  reject either broad valid coverage or the direct-call receiver safety-gate
  fixtures. The no-receiver diagnostic sidecar now feeds the active-mixed
  runtime theorem through the direct local-bounds provider. Current trait/direct
  valid frontier: 100 accepted files, 96 no-receiver synthetic diagnostic ok,
  4 diagnostic fail, 100 component ready-body fallback diagnostic ok, and
  0 direct-receiver-method-present. The four synthetic failures are
  local-bounds synthetic direct-call-ready summary failures for
  `__facet_local_rec_0_id_local`, `id`, `accept_item`, and `callee`;
  the split reason is `no-direct-call-target` for all four. The ready-body
  fallback sidecar is sound into a local-bounds provider whose callees
  have either synthetic direct-call-ready summaries or ordinary root-shadow
  summaries. Shared ready-body summary and callee evidence-at facts
  now live below the direct-call route layer, with injections from
  synthetic and ordinary callee evidence. Ready-body route-package projections,
  synthetic route-package-to-callee evidence bridges, synthetic-to-ready-body
  route-package subsumption facts, ready-body exact-route reachability/provider helpers, package-at,
  reachable-provider, and reachable local-bounds-family projections,
  ready-body all-components package-at, checker-to-reachable-provider,
  reachable exact-target-provider adapters, ready-body exact-target
  body-step adapters, a ready-body checker-to-package and exact-target
  provider bridge, ready-body callback-at and local-bounds-family bridges,
  and the end-to-end sidecar provide
  alpha-renamed direct-target callee evidence plus store-safe target arguments.
  The next proof route must consume that synthetic-or-ordinary evidence in
  the active mixed callback path
  instead of requiring every local callee to have a synthetic direct-call
  target.
- The remaining activation gap is proof-side. The canonical public runtime
  theorem still targets the strict mixed endpoint through the public prefix
  theorem. Retargeting it to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` requires deriving,
  from existing public premises, the no-receiver local-bounds provider and
  per-callee summary/evidence-at facts consumed by the retained mixed
  no-receiver prefix path. Receiver-method absence alone does not imply those
  component routes, and strengthening the active no-receiver gate with the
  body-summary check is known to reject broad valid coverage.
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
   - Derive or eliminate the public-shaped theorem's remaining extracted
     no-receiver diagnostic check from public prefix-route premises, using the
     current `--diagnose-trait-gates`
     frontier (`tests/valid/function/local_let_rec_direct_call.facet`,
     `tests/valid/lifetime/hrt_direct_call_unchanged.facet`,
     `tests/valid/trait/assoc_projection_call_arg_compat.facet`, and
     `tests/valid/type_safety_ready_gap/direct_call.facet` still report
     no-receiver diagnostic `fail`; the split diagnostics show these are
     local-bounds synthetic direct-call-ready summary failures for a
     base component-store-safe function, not direct-receiver-method or base
     component-summary failures;
     the failing component functions are `main`, `caller`, `main`, and
     `main`, and the inner local-bounds failures are
     `__facet_local_rec_0_id_local`, `id`, `accept_item`, and `callee`, all
     classified as `no-direct-call-target`) while
     preserving active checker authority; the component ready-body fallback
     diagnostic now passes all 100 frontier files and has sound local-bounds,
     pointwise callee provider, shared ready-body route-package,
     pointwise ready-body callee-evidence injections, synthetic
     route-package-to-callee-evidence bridges, synthetic-to-ready-body
     route-package subsumption, ready-body exact-route reachability/provider helpers, package-at,
     reachable-provider, and reachable local-bounds-family projections,
     ready-body all-components package-at, checker-to-reachable-provider,
     reachable exact-target-provider adapters, ready-body exact-target
     body-step adapters, a ready-body checker-to-package and exact-target
     provider bridge, ready-body callback-at and local-bounds-family bridges,
     and alpha-renamed direct-target bridges,
     so the remaining gap is proof routing from that synthetic-or-ordinary
     evidence to the mixed
     no-receiver path.
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
  exact-body/package, local-bounds, scoped-package, call-statement, component
  summary/check, component-body summary, non-captured, no-receiver
  local-bounds provider, ready-body local-bounds provider,
  shared ready-body summary evidence-at, pointwise ready-body
  callee-evidence injections, route-package projections, synthetic
  route-package-to-callee-evidence bridges, synthetic-to-ready-body
  route-package subsumption, ready-body exact-route reachability/provider
  helpers, package-at and reachable-provider projections, ready-body
  all-components package-at, checker-to-reachable-provider, reachable
  exact-target-provider adapters, ready-body exact-target body-step
  adapters, a ready-body checker-to-package and exact-target provider bridge,
  ready-body callee helpers, ready-body callback-at and
  local-bounds-family bridges,
  end-to-end ready-body route-package bridge,
  and assoc-base callback paths. The
  canonical theorem still lacks the route from
  synthetic-or-ordinary local-bounds evidence into the mixed no-receiver proof
  path and the bridge from public premises to the needed provider/check and
  per-callee summary/evidence-at facts.
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
