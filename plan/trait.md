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
  single environments and local-bounds families. The remaining proof gap is
  wiring that ordinary route, together with the existing synthetic route, into
  the active endpoint's ready-body local-bounds bridge and then retargeting the
  public runtime theorem without adding a stricter checker gate.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Use the prefix-store ordinary-shadow local-bounds route together with the
     existing synthetic route to obtain the ready-body local-bounds route bridge
     from active-endpoint evidence, without depending on the stricter diagnostic
     shadow-check gate.
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
  active gate. The public theorem still needs the ready-body route bridge to be
  rebuilt from the accepted endpoint's existing synthetic and ordinary prefix
  routes, without adding public premises or shrinking the accepted language.
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
