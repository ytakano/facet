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
  its only checker authority. That endpoint enforces the direct-receiver mixed
  checks and the per-local mixed no-receiver certificate without changing the
  accepted regression frontier. Public checker soundness aliases target this
  endpoint, but the public runtime theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`.
- The active no-receiver certificate is per-local mixed evidence:
  `check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check`.
  At each component-local callee it accepts synthetic-ready, ordinary-shadow, or
  narrow evidence. This shape is broad enough for the current valid suite, unlike
  the older blanket narrow/all-local-bounds diagnostics.
- Runtime proof plumbing now has global and local-bounds mixed value routes,
  mixed cleanup routes, component providers, endpoint providers, and bridge
  adapters. Ordinary-shadow routes are derived from the provenance-ready package.
  Narrow direct calls now have a non-generic runtime package theorem over the
  post-cleanup result store, and the named narrow cleanup route is proved from
  that package.
- A concrete mixed cleanup callback is now derivable from the existing
  synthetic-ready full route, the ordinary-shadow full route family, and the
  proved narrow cleanup route. The active endpoint wrapper that assumes a global
  synthetic branch route now consumes both the mixed route provider and this
  cleanup provider path, there is an active-endpoint constructor from the
  exact-body-call route package, and the summary-to-route conversion is named as
  `mixed_ready_body_or_narrow_summary_provider_route_bridge`. That bridge now has
  a constructor from the existing synthetic and ordinary-shadow route packages,
  there is a local-bounds adapter from per-component synthetic/ordinary route
  families to the mixed ready-body-or-narrow route family, an active endpoint
  wrapper now consumes a combined component mixed-route provider directly, the
  older separate synthetic/shadow route-provider endpoint factors through that
  combined path, there are compiled active-endpoint public theorems for the
  combined component mixed-route provider route, mixed disjunction handling now
  has a bridge that needs only a per-target store-safe synthetic route plus the
  ordinary-shadow route family, the existing mixed value/cleanup bridge
  interface has a constructor from that per-target synthetic route, and active
  endpoint runtime theorems now expose either the store-safe or plain per-target
  synthetic prefix route as the only extra proof premise.

## Remaining Tasks

1. Retarget the required public runtime theorem.
   - Connect the active per-local certificate to route evidence: ordinary-shadow
     uses the prefix ordinary route, narrow uses the proved narrow package, and
     synthetic-ready must supply the per-target synthetic prefix route required
     by `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_synthetic_evidence_at_prefix_route`
     without rebuilding a recursive synthetic-only certificate.
   - Move the required theorem name
     `infer_program_env_end2end_big_step_safe_checked_initial_ready` from
     `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`
     to `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Keep the theorem premises no stronger than the current public preservation
     packages; the additive component-mixed-provider runtime theorem is only an
     intermediate route until the active certificate is connected without extra
     public obligations.

2. Finish direct-call receiver activation.
   - Replace the remaining blanket synthetic-route dependency with per-callee
     mixed evidence from the active endpoint certificate: synthetic-ready uses
     the synthetic route, ordinary-shadow uses the prefix ordinary route, and
     narrow uses the proved narrow cleanup/value package.
   - Add positive direct-call receiver UFCS tests only after the verified active
     endpoint accepts them. Keep existing safety-gate tests invalid until Rocq,
     extraction, and the OCaml CLI agree.

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

- The required public runtime theorem still has not been retargeted to the active
  endpoint. The cleanup side is wired through the active wrapper, an
  exact-body-call package constructor exists for the active endpoint, the
  summary-to-route bridge has a constructor from existing route packages, an
  additive active-endpoint prefix theorem compiles with that bridge as an
  explicit premise, a local mixed-route adapter now compiles, an endpoint
  wrapper now consumes the combined component mixed-route provider directly, the
  older separate route-provider endpoint factors through it, public prefix and
  non-prefix runtime theorems expose that combined-provider route, and an
  intermediate mixed-disjunction bridge, value/cleanup bridge constructor, and
  active-endpoint runtime theorems now only require per-target synthetic evidence
  for the synthetic branch. The remaining proof target is deriving that
  per-target synthetic prefix route from the active mixed certificate without
  assuming recursive synthetic-only evidence.
- The stricter shadow-check certificate proves extra ordinary-shadow evidence and
  remains useful diagnostically, but it is too restrictive to become the active
  endpoint gate without rejecting current valid programs.
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
