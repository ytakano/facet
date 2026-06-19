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
- The ready-body route is no longer the main proof strategy for the no-receiver
  branch. Diagnostics show the four full-valid no-receiver ready-body blockers
  (`type_forall_fn_value_pass_and_call.facet`, `hrt_call_twice.facet`,
  `hrt_item_bounds_as_value.facet`, and `hrt_pass_poly_identity.facet`) all have
  `narrow=ok`. The next safety route should promote narrow store-safe summaries
  through a diagnostic/certificate theorem before retargeting the public theorem.

## Remaining Tasks

1. Replace the stalled ready-body proof route with a narrow certificate route.
   - Define the no-receiver local-bounds certificate around existing narrow
     store-safe summaries and their runtime packages.
   - Prove checker soundness for the certificate without adding OCaml fallback
     logic or weakening public theorem statements.
   - Add a diagnostic theorem showing the active mixed endpoint plus the narrow
     certificate gives the needed no-receiver safety providers.

2. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` only after the
     narrow certificate route is sound.
   - Promote only proven certificate gates into the active endpoint.
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
  `infer_program_env_end2end_assoc_direct_receiver_mixed` still needs proof-side
  evidence for the mixed no-receiver callback path. The previous ready-body and
  ordinary shadow-summary bridge path stalled; do not keep extending it as the
  primary strategy.
- The current viable path is a narrow store-safe certificate: all known
  full-valid no-receiver ready-body blockers are covered by the narrow summary,
  but the certificate provider and theorem-level bridge from that summary to the
  mixed no-receiver safety argument still need to be built.
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
