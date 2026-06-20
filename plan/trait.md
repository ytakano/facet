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
  extensions and an active branch-local argument order. Its scoped evidence-at
  form is also stable through nested local bounds.
- The active endpoint can currently be proved with either an explicit
  summary-route bridge, all-target synthetic summary evidence, or a ready-body
  route provider. The remaining gap is proving the ready-body route from the
  active branch-local mixed certificate without requiring recursive
  synthetic-only evidence for all callees.

## Remaining Tasks

1. Retarget the required public runtime theorem.
   - Move `infer_program_env_end2end_big_step_safe_checked_initial_ready` from
     `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`
     to `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Keep public premises no stronger than the current preservation packages.
   - Connect the active per-local certificate to route evidence: synthetic-ready
     uses the synthetic route, ordinary-shadow uses the ordinary-shadow route,
     and narrow uses the proved narrow package.

2. Finish direct-call receiver activation.
   - Replace the remaining blanket synthetic-route dependency with per-callee
     mixed evidence from the active endpoint certificate.
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

- The required public runtime theorem is not yet retargeted. The active endpoint
  route/value path is available, including public ready-body-route wrappers,
  combined summary/exact-body wrappers, and an active-certificate provider
  bundle through the combined bridge plus nested local-bounds stability for the
  active summary, alpha-callback, mixed route, mixed value, scoped evidence-at,
  and active branch-local provider-package forms.
  The public theorem still lacks a proof that this certificate yields the needed
  recursive ready-body route. That route must consume synthetic, ordinary-shadow,
  and narrow branches directly, including nested narrow calls.
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
