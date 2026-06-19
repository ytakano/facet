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
- Diagnostic endpoints are proof-routing and fixture-sampling aids only. Current
  trait/direct valid frontier: 100 accepted files, 96 no-receiver synthetic ok,
  4 no-receiver synthetic fail, 100 component ready-body ok, 100 no-receiver
  ready-body ok, 18 shadow-provenance-summary ok, 17 preservation-ready ok, 17
  no-receiver ready-body plus shadow-checks ok, and 0
  direct-receiver-method-present.
- Ready-body fallback proof infrastructure now includes local-bounds provider
  contracts, synthetic/ordinary route-provider wrappers, Prop-level reachable route-package/exact-target
  adapters, ready-body and synthetic provider adapters from the
  combined no-receiver diagnostic, and mixed-route diagnostic theorems that avoid
  the abstract ready-body route bridge once synthetic and shadow route providers
  are supplied. The remaining gap is deriving those providers from the active
  mixed checker's public premises rather than diagnostic-only checks.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding
     OCaml fallback logic or weakening the public theorem with a new premise.
   - Promote the ready-body no-receiver diagnostic route from diagnostic-only
     proof plumbing to the public runtime theorem by deriving its synthetic and
     ordinary route providers from public premises.
   - Prove the ordinary shadow-summary local-bounds route bridge itself, expose
     the needed provenance/preservation checks from the active checker premises,
     then remove the remaining abstract ready-body route bridge from the public
     wiring without requiring Prop-to-bool completeness for component summaries.
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

- Retargeting the public runtime theorem to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` still needs proof-side
  evidence for the mixed no-receiver callback path. The active endpoint accepts
  broad valid coverage, but it does not expose enough provenance/preservation
  facts to derive the combined shadow-check diagnostic beyond 17/100 files.
- The ordinary shadow-summary local-bounds route bridge is still unproved.
  Existing lower-level route lemmas can consume shadow-route evidence or combine
  already-provided synthetic and shadow routes, but they do not construct the
  ordinary route from `env_fns_root_shadow_summary_evidence` alone.
- The ready-body route bridge cannot currently be derived from the public
  synthetic prefix theorem plus per-callee ready-body evidence: the public
  synthetic route requires whole-environment direct-call evidence, while the
  ready-body branch supplies only the current callee's synthetic evidence.
- Diagnostic checker retargeting experiments that accepted direct-call receiver
  safety-gate fixtures either rejected broader valid programs or relied on
  endpoints that are not the active CLI authority. In particular, promoting the
  no-receiver ready-body gate to the active mixed checker rejected
  `type_forall_fn_value_pass_and_call.facet`, `hrt_call_twice.facet`,
  `hrt_item_bounds_as_value.facet`, and `hrt_pass_poly_identity.facet`. Keep
  direct-call receiver safety-gate tests invalid until the verified active
  endpoint accepts them.

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
