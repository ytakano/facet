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
  `deriving` remain syntax-level deferred.
- Supported method receivers are forms whose type is known before checker
  execution: parameters, typed literals, pure literal/unit locals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors, including generic instances. Field-bearing structs, payload
  enums, direct-call receivers, generic direct-call receivers, non-pure inferred
  locals, and call-initialized/general annotated locals remain gated.
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only checker authority. That endpoint now requires both direct-receiver
  mixed readiness and the per-local mixed no-receiver certificate. Public checker
  soundness aliases already target this endpoint, but the public runtime theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`.
- The ready-body route alone stalled for the no-receiver branch, and the narrow
  route alone is too restrictive for the full accepted language. The current
  viable no-receiver certificate shape is per-local mixed evidence:
  `check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check`.
  For every component-local function it accepts synthetic-ready, ordinary shadow
  summary, or narrow evidence. This checker is extracted, has a Rocq soundness
  lemma to `component_body_local_bounds_ready_body_or_narrow_summary_provider_in_env`,
  and passes both the targeted trait/direct frontier (`100/100`) and the full
  valid suite (`0/222` failures). Older broader gates remain diagnostic only:
  env-wide `ready_body_or_narrow` and all-local-bounds narrow still fail the same
  four full-valid helper-function cases. The per-local mixed provider is now
  consumed by compiled runtime helpers at the exact component-local callee lookup,
  by a boolean-preserving captured/component env safety theorem, and by the active
  direct-receiver mixed diagnostic theorem. The certificate is now enforced by
  the active extracted endpoint without changing the accepted regression frontier,
  and an active-endpoint safety wrapper obtains that certificate directly from
  the endpoint. A stronger no-receiver local-mixed check with provenance and
  preservation shadow checks is defined, extracted, and proved to provide both
  the local mixed provider and ordinary shadow-summary evidence, but it remains
  diagnostic only: making it the active endpoint gate rejected many existing
  valid programs. A runtime diagnostic theorem now consumes this stronger
  certificate and derives the ordinary shadow route provider internally. Ordinary
  shadow summaries now lift through local-bounds families to ready-body callee
  evidence, and the ordinary shadow route bridge is derivable from the
  ready-body local-bounds route bridge plus root name/key preservation. The
  ordinary-shadow preservation core is now packaged as exact-input route
  theorems for single environments and local-bounds families, matching the route
  result shape when the call starts from exact `store_typed`. The
  ordinary-shadow preservation path now has prefix-store route theorems for
  single environments and local-bounds families. The active endpoint path now
  discharges the ordinary shadow route provider from the global prefix route
  package. A component-level mixed callee helper now consumes the active
  per-local certificate at the selected callee: synthetic-ready locals use the
  synthetic route family, ordinary-shadow locals use the prefix ordinary route,
  and narrow locals stay on the narrow safety branch. That helper is now lifted
  through a check-based env/root safety theorem and the active endpoint-local
  certificate wrapper, so ordinary-shadow routing is derived internally. The
  endpoint wrapper now passes one bundled mixed route provider, with projection
  lemmas for the synthetic and ordinary halves, instead of separate route
  callbacks. A reusable constructor derives the ordinary half from the existing
  provenance-ready route package. The target height-indexed mixed route shape is
  now named in Rocq as a value-safety route, with statement/family adapters and
  the closure-target summary premise needed by the narrow branch. The active provider bridges to its
  lookup-indexed mixed evidence-at predicate, and a direct-call `typed_env_roots` inversion lemma exposes the
  callee needed for dispatch. Component-local, env/root, and endpoint-local safety now have helpers
  that consume this mixed route interface directly, and a provider constructor
  lifts any proved global mixed route theorem into the component local-bounds
  provider expected by the endpoint wrapper. The global mixed value route theorem is now proved from the existing synthetic
  and ordinary-shadow route packages plus the narrow direct-call value lemma, and
  a constructor lifts those branch-route packages into the endpoint's mixed
  local-bounds provider. The endpoint path now consumes a single global synthetic branch-route theorem
  instead of a per-component synthetic callback, but the direct derivation is
  still blocked by the recursive evidence shape of the existing synthetic cleanup
  bridge. That bridge asks for synthetic-only evidence at each direct body target,
  while the active local certificate may classify that same target as synthetic,
  ordinary-shadow, or narrow. Small adapters now lift synthetic-only,
  ordinary-shadow, and narrow evidence into the mixed evidence-at predicate. A
  value-only mixed body-call callback is derivable from both global and scoped
  mixed route families, with env-family, local-bounds, component-provider, and endpoint-provider
  adapters for component-local recursion. The
  next proof target is a mixed cleanup bridge whose recursive body-call callback
  consumes that scoped value-only mixed callback rather than the old
  full-preservation synthetic callback and `fn_root_shadow_synthetic...` evidence.
  After that bridge yields a global mixed route without a synthetic-route public
  premise, retarget the endpoint and then the public runtime theorem.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Replace the remaining blanket synthetic-route callback with a per-callee
     ready-body route built from the active endpoint's mixed local evidence:
     synthetic-ready cases use the existing synthetic route, ordinary-shadow
     cases use the new prefix ordinary route, and narrow cases stay on the
     narrow branch.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Add positive direct-call receiver UFCS tests only after the verified active
     endpoint accepts them. Keep existing direct-call receiver safety-gate tests
     invalid until that switch lands.

2. Extend receiver coverage conservatively.
   - Keep receiver-first prefix calls as the canonical surface syntax.
   - Add remaining receiver forms only when Rocq checker summaries and safety
     proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- Retargeting the public runtime theorem to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` is still pending. The
  active endpoint now exposes the per-local certificate check and has a wrapper
  safety theorem. A stricter shadow-check certificate proves the extra ordinary
  shadow evidence and has diagnostic runtime theorems that derive the shadow
  route bridge from the ready-body route bridge, but it is too restrictive as an
  active gate. The component-level mixed callee helper is proved and lifted through
  the active endpoint-local certificate wrapper, with synthetic and ordinary
  route families bundled as one mixed provider. The ordinary half is derived by a
  reusable provenance-ready constructor; the synthetic half cannot be recovered
  by reusing the existing synthetic route theorem because that theorem requires
  recursive synthetic-only evidence. The replacement height-indexed mixed
  value-safety route interface, statement/family adapters, provider-to-evidence
  bridge, direct call typing inversion lemma, component/env-root/endpoint
  consumer helpers, route-provider constructor, global mixed value route theorem,
  and branch-package provider constructor are now defined. Evidence adapters now
  lift synthetic-only, ordinary-shadow, and narrow summaries into the mixed
  evidence-at predicate, and a value-only mixed body-call callback adapter is
  proved from both global and scoped mixed route families with env-family,
  local-bounds, component-provider, and endpoint-provider variants.
  Remaining endpoint work is to add a mixed cleanup bridge that accepts this
  scoped value-only mixed recursive body-target callback, use it to remove the
  global synthetic branch-route premise, then retarget the public runtime theorem
  without adding public premises or shrinking the accepted language.
- The standalone narrow and all-local-bounds narrow certificates are proven and
  useful diagnostics, but they are not broad enough to be blanket active endpoint
  gates by themselves.
- Direct-call receiver safety-gate tests must remain invalid until the verified
  active endpoint accepts those receiver forms through Rocq, extraction, and the
  OCaml CLI without handwritten fallback logic.

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
