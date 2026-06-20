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
  can now report trait gates for active-endpoint rejections by inspecting the
  extracted direct-receiver base endpoint without changing checker authority.

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
   - Replace the remaining blanket synthetic-route dependency with per-callee
     mixed evidence from the active endpoint certificate.
   - Use `--diagnose-trait-gates` on rejected safety-gate cases to distinguish
     direct-receiver preservation/provenance failures from component summary
     failures. Add positive direct-call receiver UFCS tests only after the
     verified active endpoint accepts them through Rocq, extraction, and the CLI.

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
  explicit function-call receiver case show the direct-receiver marker is present
  and component/no-receiver summary gates pass, while provenance and preservation
  gates still fail; activation must close those Rocq obligations without
  handwritten OCaml fallback logic.

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
