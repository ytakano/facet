# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Trait and impl items are parsed, lowered into Rocq/extracted environments,
  and checked for duplicate, missing, extra, and mismatched associated types and
  methods. Impl method bodies are elaborated to hidden functions and checked by
  the extracted checker even when the method is not called.
- Method-local type parameters are supported for trait and impl methods,
  including method-local bounds and generic-trait impl remapping. Method-local
  lifetime generics remain deferred and are rejected by tests.
- Method calls use Facet's ordinary prefix call shape. Explicit UFCS is
  `(<Ty as Trait>::method receiver args...)`; short UFCS is
  `(Trait::method receiver args...)`; the receiver is always the first
  argument. Dot method-call syntax is intentionally rejected in this phase.
- Short UFCS currently accepts receiver types known before checker execution:
  function parameters, syntactically typed literals, immutable pure local
  literals after receiver-let elimination, fieldless struct literals, and
  payloadless enum constructors whose store-safe argument evidence is checked in
  Rocq. Field-bearing struct literals, payload-bearing enum constructors,
  direct-call receivers, generic direct-call receivers, non-pure inferred
  locals, and general annotated locals remain gated.
- Direct-call receiver support has Rocq-side runtime replay infrastructure for
  hidden receiver lets, direct receiver-method summaries, raw/hidden evaluation
  packaging, final-store matching, method-body replay, scoped live/consumed
  expression-lift providers, and boolean soundness for the direct-extended
  captured/direct-receiver-or-component summary gate.
- The extracted checker exports transitional strict and assoc strict
  direct-receiver endpoints, the strict mixed assoc direct-receiver endpoint
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`,
  and the assoc-base mixed endpoint
  `infer_program_env_end2end_assoc_direct_receiver_mixed`. The OCaml CLI now
  uses the assoc-base mixed endpoint as its single extracted checker authority.
  The assoc-base mixed endpoint runs the older assoc checker, then requires the
  direct-receiver safety gate only when an elaborated function body has a direct
  or generic direct receiver-method shape. Receiver-method target detection is
  restricted to synthetic impl method names, avoiding ordinary generic calls
  whose first argument happens to be a direct call.
- Required public checker soundness aliases now target the assoc-base mixed
  endpoint: `infer_program_env_end2end_sound` and
  `check_program_env_end2end_sound`. The required public runtime-safety theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  the strict mixed endpoint. The assoc-base mixed endpoint is exported, covered
  by assoc-boundary soundness wrappers, has a direct-ready runtime branch
  theorem, and is now the target of the public direct-ready, case-split route,
  and exact-body route-package mixed runtime wrappers. It also has a base-route
  bridge that can consume the non-strict assoc local-bounds route theorem
  `infer_program_env_end2end_assoc_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family`.
- Mixed endpoint success exposes the underlying assoc strict exact-closure
  success, checked-env uniqueness/readiness facts, no-receiver target
  contradictions for the no-method branch, collapse back to ordinary
  captured/component readiness there, branch runtime bridges for both
  direct-ready and no-receiver-method cases, a public case-split runtime
  wrapper over the mixed endpoint, an exact-body route-package wrapper for that
  mixed case split, a checked component-summary bridge for mixed component
  store-safe callbacks, the non-strict assoc local-bounds route theorem
  needed by the assoc-base mixed base-route bridge, and assoc-base mixed
  local-bounds callback wrappers, including prefix, store-static, and static
  variants, that route through that bridge when supplied the per-component
  local-bounds route callback.
- Runtime proof plumbing now has prefix-aware static-runtime callback shapes,
  store-typed-prefix root naming for direct places and borrows, a packaged
  leaf-or-borrow static prefix callback, context-name to store-name transport for
  rooted typing outputs, packaged static root-name/key transport through
  `typed_roots_ctx_roots_named_mutual`, same-store `store_roots_within` transport
  for root-env union updates, static-only `store_typed_prefix` stability for
  consumed paths, leaf/borrow prefix traversals for typed argument, field, and
  match-tail branch lists, struct/enum/match/if/drop/assign/replace compound prefix
  wrappers, an evaluated `let` root-name/key helper for prefix stores, a
  stronger prefix static callback shape that carries `store_typed_prefix`,
  a mutual typed-roots package proving that callback for preservation-ready
  expressions, prefix-facing route wrappers through the mixed static-component
  runtime wrapper, and legacy wrapper shapes that delegate through the prefix
  bridge. The mixed component callback route can now consume the checked
  component-summary boolean directly, and the assoc-base mixed local-bounds
  wrapper family can consume an explicit per-component local-bounds route
  callback in the same prefix/store-static/static shapes as the old final
  wrapper chain. A one-level active-endpoint branch-aware non-captured
  provider adapter now matches the public local-bounds-family callback shape
  and has prefix/store-static/static wrappers while preserving the explicit
  captured/non-captured evidence requirement.
  The remaining runtime theorem gap is deriving a concrete exact-closure or component-summary provider for the mixed endpoint from the public/static completeness chain without adding a premise, then retargeting the required public theorem. Assoc-base proof plumbing can now turn a global exact-closure provider, a branch-aware non-captured component provider, a non-captured-only callback, a non-captured exact-route callback, a captured-first component route callback, or a global exact-body route package into the local-bounds route callback needed by the mixed wrapper. The captured-first path follows the assoc runtime split: captured functions use the captured-call proof directly, only the uncaptured component branch asks for local-bounds route evidence, and direct-ready component checks now lift to the same local-bounds-family provider shape. The exact-body case-split wrapper and the strict/assoc-strict exact-body route-package wrappers now derive their store-safe evidence-at route from the exact-body route package rather than requiring that route as a separate premise. Prefix/store-static/static variants exist for these paths. Mixed endpoint facts now expose no-capture-branch exact-closure payloads in top-level form and exact/component local-bounds-family forms. The assoc-base mixed endpoint also has summary exact/call package wrappers, direct-call-route wrappers over those summary-call packages, summary-at exact-package wrappers, summary-at call-route wrappers including the component-summary provider bridge, alpha-route component-summary/closure-target/closure-check and branch-local strict-check wrappers, active alpha nested/evidence summary-provider delegates, an active exact-closure-provider delegate for the branch-local strict-check route, plus exact-body route-package wrappers for component-summary providers and checked component summaries, including prefix, store-static, and static forms that route through the summary-at/component-body-summary provider path; the assoc-base case-split exact-body package path and branch-local exact-body local-bounds package path also have store-static/static wrappers. Public-layer mixed summary-call aliases now expose the assoc-base mixed component-check, component-body-summary evidence, route, and store-safe body-summary wrappers next to the older core/assoc aliases; public-layer mixed exact-body route-package aliases now expose the provider and checked-component prefix/store-static/static variants as well. The direct public-prefix route is not itself enough to build the no-direct-ready evidence-at route because it requires global callee evidence, while the case-split wrapper needs route-local evidence-at facts for the no-receiver branch.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries.
- Assoc-aware checked core/env/full/end-to-end entrypoints are executable,
  exported, and covered by assoc-boundary soundness. The assoc-base mixed
  endpoint is also executable, exported, proved against the assoc boundary, and
  used by the OCaml CLI as the sole accept/reject checker authority.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget the required public runtime theorem name to the assoc-base
     mixed endpoint without adding OCaml fallback logic.
   - Add positive direct-call receiver UFCS tests only after the active extracted
     checker accepts them through the verified endpoint. Keep existing
     direct-call receiver safety-gate tests invalid until that switch lands.

2. Extend receiver coverage conservatively.
   - Keep the canonical surface syntax as receiver-first prefix calls.
   - Add field-bearing struct literal, payload-bearing enum constructor,
     generic direct-call receiver, non-pure inferred local, and general
     annotated-local receivers only when Rocq checker summaries and safety
     proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- A trial CLI switch to
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver`
  rejected many existing `tests/valid` programs with
  `ErrEndToEndSafetyGateFailed`. On `tests/valid/assign/basic_assign.facet`,
  the direct gate reports provenance=true, preservation=false,
  direct-or-component=true, component=false. The endpoint is verified but not
  broad enough to be the active CLI authority.
- The mixed endpoint avoids the final direct-receiver gate for programs
  without direct receiver-method bodies, and receiver-method target detection is
  no longer triggered by ordinary non-impl generic calls. The assoc-base mixed
  endpoint now avoids the strict exact-closure base that rejected existing valid
  direct-call and HRT/module programs, and the CLI switch to this endpoint
  passes the valid/invalid and FIR regression suites. The remaining activation
  blocker is proof-side: discharge the assoc-base mixed local-bounds route
  callback from the higher static/component callback wrapper chain without a
  new public premise, then retarget the required public runtime theorem to this
  assoc-base mixed endpoint. Current proof plumbing includes a generic adapter
  from non-store-safe evidence-at direct-call routes to store-safe evidence-at
  routes, using the existing store-safe-args-to-preservation-ready bridge, and
  a non-captured-only mixed wrapper that derives the component summary boolean
  from assoc-base mixed success, a captured-first mixed wrapper that only
  demands route evidence in the actual uncaptured component branch, and an
  exact-body route-package bridge into that captured-first path. Retargeting the
  public theorem directly through the assoc-base mixed case-split still needs a
  valid source of route-local evidence-at or component-branch route facts for
  the no-direct-ready branch; the public prefix route alone requires global
  callee evidence and is not sufficient.
- Verification note: `rocq compile -R theories Facet
  theories/TypeSystem/TypeSafetyDirectCallRoute.v` passes for the adapter, and
  targeted `timeout 300 rocq compile -R theories Facet -o
  /tmp/End2EndSafety.vo -noglob theories/TypeSystem/End2EndSafety.v` passes for
  the assoc-base mixed summary exact/call-package wrappers, direct-call-route
  wrappers over the summary-call packages, summary-at exact-package wrappers,
  summary-at call-route wrappers including the component-summary provider
  bridge, alpha-route component-summary/closure-target and branch-local
  strict-check wrappers, and exact-body route-package wrappers,
  including the checked component-summary
  summary-package variant and the exact-body store-static bridge, the
  strict/assoc-strict exact-body route-package premise cleanup, the
  non-captured-only mixed callback wrappers, the captured-first mixed route
  wrappers, and the captured-first exact-body route-package bridge.
  The first targeted profile found a pre-existing bottleneck at
  `EnvRuntimeCapturedSafety.v:755`, where `dependent destruction Htyped_shadow`
  took about 101.857 seconds. That branch now uses ordinary inversion. A
  follow-up profile found a later `dependent destruction Htyped_call` near
  `EnvRuntimeCapturedSafety.v:22534`, measured at about 189.006 seconds. That
  branch now also uses ordinary inversion, and
  `/tmp/EnvRuntimeCapturedSafety.after3.time` shows the largest completed
  command in the file at about 4.95 seconds. After both fixes, full
  `cd rocq && make` completed successfully.

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

## Required Checks

For type-system or checker-facing implementation tasks, run:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
```

The final search must not introduce new proof holes or debug leftovers. Existing
legacy proof-script selector matches should be called out explicitly if they
remain unrelated to the change.
