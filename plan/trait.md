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
  branch. The four full-valid no-receiver blockers all have `narrow=ok`, and
  the narrow route now has env-level evidence, local-bounds lifting, a sound
  checker certificate, and a no-receiver diagnostic checker that provides
  `component_body_local_bounds_narrow_summary_provider_in_env` for the active
  mixed endpoint. That checker is extracted and regression-tracked in the CLI
  diagnostics (`no-receiver-narrow-summary=11/100` on the targeted trait/direct
  frontier). The provider also has local-bounds lookup,
  direct-call-target-shaped, mixed-endpoint, and component-summary conversion
  helpers that package a checked component with its local-bounds narrow callee
  evidence. The packaged narrow-callee component now has a direct big-step
  safety lemma and has been lifted through the non-strict, strict, and active
  mixed no-receiver diagnostic branches. A global promotion attempt for the
  narrow gate was rejected because it makes many existing valid no-receiver
  programs fail the end-to-end safety gate; the next proof step must either
  broaden the certificate coverage or apply the gate only to the targeted
  trait/direct frontier.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` only after the
     active endpoint has a certificate gate that preserves existing valid tests.
   - Do not promote `check_env_root_shadow_no_receiver_component_narrow_summary_provider_check`
     as a blanket no-receiver requirement; it is proven but too narrow for the
     full accepted language.
   - Add positive direct-call receiver UFCS tests only after the verified active
     endpoint accepts them. Keep existing direct-call receiver safety-gate tests
     invalid until that switch lands.

2. Build a selective or broader certificate gate.
   - Either classify and gate only the targeted trait/direct frontier where the
     narrow certificate applies, or broaden the certificate so ordinary valid
     no-receiver programs still pass.
   - Regenerate extraction and run the OCaml/CLI regression suite after any
     active gate change.

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
  previous ready-body and ordinary shadow-summary bridge path stalled; keep the
  proof on certificate routes instead of reviving that path.
- The active mixed no-receiver theorem now consumes the narrow store-safe
  certificate, but that certificate is not broad enough to be a blanket active
  endpoint gate. A selective frontier gate or a broader no-receiver certificate
  is needed before the public runtime theorem can move.
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
