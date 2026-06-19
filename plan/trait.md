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
- Diagnostic endpoints remain for proof routing and fixture sampling, not as
  active authorities. Current trait/direct valid frontier: 100 accepted files,
  96 no-receiver synthetic diagnostic ok, 4 no-receiver diagnostic fail,
  100 component ready-body fallback diagnostic ok, and
  0 direct-receiver-method-present. The four synthetic failures are
  `tests/valid/function/local_let_rec_direct_call.facet`,
  `tests/valid/lifetime/hrt_direct_call_unchanged.facet`,
  `tests/valid/trait/assoc_projection_call_arg_compat.facet`, and
  `tests/valid/type_safety_ready_gap/direct_call.facet`; each fails because a
  local-bounds synthetic direct-call-ready summary is missing for an ordinary
  callee with `no-direct-call-target`.
- Ready-body fallback proof infrastructure now supplies local-bounds providers,
  explicit ordinary/synthetic-to-ready evidence adapters, ordinary-summary-to-
  provenance bridges, synthetic-check-to-ready provider bridges, a named
  summary-family route bridge, route-package/reachability helpers, exact-target
  adapters, pointwise callee evidence, callback-at/local-bounds callback bridges,
  and checker-to-callback-at provider bridges. This gives synthetic-or-ordinary
  callee evidence plus store-safe target arguments for alpha-renamed direct
  targets.
- The remaining activation gap is proof-side. The retained mixed no-receiver
  path still consumes synthetic summary-route/local-bounds evidence, while the
  broad body-summary gate that would provide it rejects valid coverage.
  Retargeting the canonical public theorem to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` requires routing the
  ready-body fallback evidence into that mixed no-receiver callback path, then
  deriving the needed provider/check facts from the existing public premises.
- Associated type defaults, equality constraints, and `deriving` are reserved
  for future surface forms. Provisional syntax for them is explicitly rejected
  with parser diagnostics.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding
     OCaml fallback logic or weakening the public theorem with a new premise.
   - Replace the remaining synthetic no-receiver diagnostic dependency with a
     ready-body route that consumes synthetic-or-ordinary callee evidence,
     exact-body package facts, store-safe target arguments, and the
     component-only boolean bridge.
   - Prove the final bridge from public prefix-route premises to the
     no-receiver local-bounds provider and per-callee evidence required by the
     active mixed proof path, without requiring Prop-to-bool completeness for
     component summaries.
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
  `ErrEndToEndSafetyGateFailed`. Related rejected diagnostic endpoints and
  unused ready-check helper booleans have been removed; the base
  direct-component endpoint remains diagnostic proof infrastructure only.
- The active mixed endpoint has the needed direct-ready branch, assoc-base
  callback paths, component-body summary/check routes, and ready-body fallback
  bridges up through named evidence/provenance, synthetic-check, summary-family,
  and callback-at providers. It still lacks the lower preservation theorem route
  that lets the mixed no-receiver proof consume ready-body synthetic-or-ordinary
  evidence instead of requiring every local callee to have a synthetic direct-call
  target.
- The assoc direct-receiver-base endpoint accepts the basic direct-call receiver
  fixture, but it is not the active CLI authority and no longer has a retained
  runtime wrapper theorem. Its mixed wrapper preserves ordinary valid coverage
  but still rejects the direct-call receiver fixture because the direct-ready
  branch requires the global component gate.
- A diagnostic retarget to `assoc_direct_receiver_base_combined` accepted the
  short and explicit direct-call receiver UFCS safety-gate fixtures and
  preserved the current regression suite except for those two expected-invalid
  flips; its unreferenced runtime wrappers and rejected broad/component-only
  ready-check diagnostics have been removed.

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
