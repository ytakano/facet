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
  its only checker authority. Public checker soundness aliases already target
  this endpoint, but the public runtime theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`.
- The ready-body route alone stalled for the no-receiver branch, and the narrow
  route alone is too restrictive for the full accepted language. The current
  proof route is a combined no-receiver certificate:
  `check_env_root_shadow_no_receiver_component_ready_body_or_narrow_summary_provider_check`.
  It dispatches to the ready-body provider certificate when available and to the
  narrow store-safe certificate for the remaining targeted cases. The checker is
  extracted and regression-tracked in CLI diagnostics: on the targeted
  trait/direct frontier, `no-receiver-ready-body-or-narrow-summary=100/100`,
  while the narrower standalone certificate remains `no-receiver-narrow-summary=11/100`.
  The combined certificate has an active mixed diagnostic safety theorem, but
  still depends on the existing ready-body route bridge for the ready-body arm.

## Remaining Tasks

1. Close the combined certificate proof path.
   - Remove or discharge the ready-body route-bridge premise from the combined
     active mixed diagnostic theorem, or replace that arm with already-proven
     route/provider packages.
   - Keep the narrow arm as the fallback for the four full-valid ready-body
     blockers and for the targeted trait/direct frontier.

2. Finish direct-call receiver activation.
   - Promote only a certificate gate that preserves existing valid tests, most
     likely the combined ready-body-or-narrow gate after its bridge dependency is
     closed.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` after the active
     endpoint is covered by the proven certificate gate.
   - Add positive direct-call receiver UFCS tests only after the verified active
     endpoint accepts them. Keep existing direct-call receiver safety-gate tests
     invalid until that switch lands.

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

- Retargeting the public runtime theorem to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` is still pending. The
  combined ready-body-or-narrow certificate preserves the current diagnostic
  frontier, but its ready-body arm still carries the route-bridge premise.
- The narrow store-safe certificate is proven and useful as a fallback, but it is
  not broad enough to be a blanket active endpoint gate by itself.
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
