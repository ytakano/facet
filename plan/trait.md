# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

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
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only checker authority. Public checker soundness aliases target this
  endpoint. The required public runtime theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`.
- The active no-receiver certificate is
  `check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check`.
  At each component-local callee it accepts synthetic-ready, ordinary-shadow, or
  narrow evidence; this is broad enough for the current valid suite.
- Runtime proof plumbing for the active endpoint now has named mixed route,
  cleanup, value-callback, alpha-callback, provider-bundle, combined route/value
  bridge adapters, and ready-body-route bridges to mixed route and value-callback
  providers. Endpoint and public wrappers expose the ready-body route path; the
  active local certificate packages summary, alpha-callback, route, and value
  providers through the combined bridge, including nested local-bounds-family
  extensions and an active branch-local argument order. It also has reusable
  local-certificate route bundles from global synthetic-branch routes,
  synthetic evidence-at routes, exact-body route packages, all-target synthetic
  summary evidence, separate synthetic/ordinary-shadow routes, and component
  mixed-route providers; the synthetic-branch, synthetic evidence-at, exact-body,
  all-target synthetic summary, and component mixed-route endpoints now flow
  through the ready-body route path. Scoped evidence-at remains stable through
  nested local bounds, and non-height synthetic evidence-at routes are bridged to
  heighted local-bounds routes. The combined bridge is packaged directly from
  synthetic-ready plus ordinary-shadow route premises.
- The active endpoint can currently be proved with either an explicit
  summary-route bridge, a mixed-ready-or-narrow route provider, a synthetic-branch
  route, synthetic evidence-at routes, all-target synthetic summary evidence, a
  ready-body route provider, or separate per-component synthetic and
  ordinary-shadow route providers. Public prefix and non-prefix wrappers expose
  the synthetic-branch, synthetic evidence-at, mixed-ready-or-narrow, ready-body,
  and synthetic-plus-shadow route-provider paths. A direct retarget attempt shows
  the exact remaining mismatch: the mixed-route bridge needs a store-safe
  synthetic summary route for synthetic branches, but the required public theorem
  only assumes the weaker synthetic prefix preservation premise. Diagnostic mode
  reports trait gates for active-endpoint rejections, including method-present
  functions, direct-receiver sub-gates, and the generic provenance/preservation
  functions that fail despite direct-receiver summary coverage, by inspecting
  extracted diagnostic endpoints without changing checker authority. Rocq now
  has a checker-side split certificate for ordinary provenance/preservation
  readiness or direct-receiver-method summary coverage, per-function case lemmas,
  and a no-receiver reduction lemma showing the split certificate recovers the
  old shadow-check path when no direct receiver method is present. `End2EndSafety`
  now exposes a diagnostic runtime wrapper that uses this reduction for the
  no-receiver branch. The split certificate is extracted and diagnostics show
  the blocked direct-call receiver fixture passes it while the authoritative
  checker still rejects. The proposed direct-receiver split end-to-end gate is
  named in Rocq, extracted, and also passes that fixture diagnostically. A
  diagnostic-only split endpoint now composes the direct-receiver base checker
  with this split gate and also accepts the blocked fixture, without changing
  the authoritative CLI endpoint. `End2EndSafety` proves this endpoint's base
  result, split-gate result, checker-soundness facts, endpoint uniqueness facts,
  combined-check bridge, no-receiver bridge to the base-mixed endpoint,
  exposed split provenance/preservation certificates, Prop-level runtime
  evidence packages, a paired per-callee split evidence package,
  replay-friendly in-environment consumer facts for concrete callees, and a
  conditional local-bounds bridge for paired evidence. Diagnostic
  no-receiver/direct-ready runtime wrappers and a case-dispatched runtime theorem
  over the proved branches exist; consuming the concrete paired evidence in the
  direct replay proof and active endpoint wiring remain.

## Remaining Tasks

1. Retarget the required public runtime theorem.
   - Move `infer_program_env_end2end_big_step_safe_checked_initial_ready` from
     `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`
     to `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Keep public premises no stronger than the current preservation packages.
   - Prove the missing internal branch-route adapter: under the active local
     certificate, synthetic-ready callees must obtain the store-safe synthetic
     summary route, ordinary-shadow callees use the ordinary-shadow route, and
     narrow callees use the proved narrow package.

2. Finish direct-call receiver activation.
   - Prove runtime soundness for the proposed gate
     `check_env_end2end_direct_receiver_split_ready` as used by diagnostic
     endpoint `infer_program_env_end2end_assoc_direct_receiver_split`: basic
     endpoint soundness, uniqueness, executable bridge facts, split
     provenance/preservation certificate facts, Prop-level and paired per-callee
     evidence packages, concrete callee consumer facts, a conditional
     local-bounds bridge, separate no-receiver/direct-ready runtime wrappers,
     and a case-dispatched runtime theorem are proved; the next step is proving
     or avoiding local-bounds stability for direct-receiver narrow summaries so
     split evidence can feed replay without whole-environment generic
     provenance/preservation readiness.
   - Replace the remaining blanket synthetic-route dependency with per-callee
     mixed evidence from the active endpoint certificate.
   - Wire the split certificate into the active endpoint only after the theorem
     is proved, then add positive direct-call receiver UFCS tests with Rocq,
     extraction, and CLI coverage.

3. Extend receiver coverage conservatively.
   - Keep receiver-first prefix calls as the canonical surface syntax.
   - Add remaining receiver forms only when Rocq checker summaries and safety
     proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

4. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- The required public runtime theorem is not yet retargeted. The active endpoint
  route/value path is available through public ready-body, mixed-ready-or-narrow,
  synthetic-branch, synthetic-evidence, synthetic-plus-shadow, combined bridge,
  exact-body, and all-target synthetic-summary wrappers. The remaining blocker is
  internal: the active certificate proves ready-body-or-narrow summary evidence,
  but the recursive route still needs store-safe synthetic branch routing for
  synthetic-ready callees, ordinary-shadow routing for shadow callees, and narrow
  package routing for narrow callees without adding any public premise.
- The stricter shadow-check certificate proves extra ordinary-shadow evidence and
  remains useful diagnostically, but it is too restrictive to become the active
  endpoint gate without rejecting current valid programs.
- Direct-call receiver safety-gate tests remain invalid. Diagnostics for the
  explicit function-call receiver case show `main` is the method-present function:
  the direct-receiver summary, direct-component, component-ready-body, and
  no-receiver mixed summary gates pass, while generic provenance/preservation
  readiness still fails for the raw receiver-call body and the strict ordinary
  component summary remains false. The extracted split certificate and proposed
  split end-to-end gate both pass this fixture and preserve the old no-receiver
  theorem path through an `End2EndSafety` wrapper, and the direct-ready runtime
  branch is now proved under the explicit direct-ready gate. A case-dispatched
  split theorem exists, and split provenance/preservation certificates now have
  Prop-level and paired per-callee evidence packages, concrete callee consumer
  facts, and a conditional local-bounds bridge. The remaining replay gap is
  direct-receiver narrow-summary stability under local bounds, or an equivalent
  replay theorem that consumes the direct summary without reconstructing generic
  provenance/preservation for the local-bounds environment. Until that is
  closed, the evidence is not threaded strongly enough to select the direct
  branch for the blocked fixture or to replace the active endpoint; no
  handwritten OCaml fallback logic is allowed. The diagnostic split endpoint
  demonstrates the
  candidate gate over the direct-receiver base environment only, with checker
  soundness and uniqueness inherited from the base endpoint plus proved
  no-receiver/direct-ready wrappers and case dispatch; it is not yet the active
  checker authority or a full split-certificate runtime-safety endpoint.

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
