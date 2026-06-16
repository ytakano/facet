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
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries.
- Assoc-aware checked core/env/full/end-to-end entrypoints are executable,
  exported, and covered by assoc-boundary soundness. The OCaml CLI uses
  `infer_program_env_end2end_assoc_direct_receiver_mixed` as its only extracted
  checker authority, with no fallback acceptance path.
- Direct-call receiver support has Rocq-side runtime replay infrastructure for
  hidden receiver lets, direct receiver-method summaries, raw/hidden evaluation
  packaging, final-store matching, method-body replay, scoped live/consumed
  expression-lift providers, and boolean soundness for the direct-extended
  captured/direct-receiver-or-component summary gate.
- The required public checker soundness aliases target the assoc-base mixed
  endpoint: `infer_program_env_end2end_sound` and
  `check_program_env_end2end_sound`. The required public runtime-safety theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` still targets
  the strict mixed endpoint.
- The assoc-base mixed endpoint is exported, covered by assoc-boundary
  soundness, has branch runtime bridges for direct-ready and no-receiver-method
  cases, and has public-layer runtime wrappers for the major route families:
  case-split routes, exact-body route packages, summary exact/call packages,
  summary-at routes, call-statement routes, component-summary providers,
  checked component summaries, and exact-body scoped/local-bounds packages.
  These wrappers expose active-endpoint paths. A public-layer retarget
  candidate now proves runtime safety for the assoc-base mixed endpoint from the
  existing public premises plus one explicit store-safe evidence-at route
  premise; the required public theorem still lacks that premise. Public
  callback bridges now derive the summary exact-call package for the assoc-base
  mixed endpoint when global store-safe summary evidence, a checked component
  summary, or a component-body store-safe summary provider is available. The
  active mixed endpoint has a named lemma exposing its combined
  captured-or-component summary gate, but that gate is still weaker than the
  missing route evidence. The remaining viable routes are through global
  store-safe summary, component-body store-safe, or exact-body/local-bounds
  evidence providers. Branch-aware public wrappers now close the direct-ready
  branch with existing callbacks and require store-safe summary evidence, a
  checked component summary, or component-body store-safe summary evidence only
  for the no-receiver-method branch. The no-receiver branch now also exports
  reusable direct/generic receiver-method target absence facts through
  local-bounds environments.
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

- A trial switch to the strict direct-receiver endpoint rejected existing valid
  programs such as `tests/valid/assign/basic_assign.facet` with
  `ErrEndToEndSafetyGateFailed`. The assoc-base mixed endpoint avoids that gate
  for programs without direct receiver-method bodies and is now the active OCaml
  authority.
- The remaining direct-call receiver activation blocker is proof-side: retarget
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
  `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding a new
  public premise. Existing assoc-base wrappers can consume several explicit
  exact-closure, component-summary, exact-body package, branch-aware, and
  local-bounds provider shapes. The direct retarget candidate only needs a
  store-safe evidence-at route premise, and the public callbacks can now feed a
  summary-exact route when supplied with global store-safe summary evidence, the
  checked component summary, or component-body store-safe summary evidence. The
  active endpoint exposes the combined captured-or-component gate, and the
  direct-ready branch is closed by existing checks. The public theorem still
  lacks a concrete source for one stronger route fact in the
  no-receiver-method branch, now isolated as conditional store-safe summary
  evidence, a checked component summary, component-body store-safe summary
  evidence, or an equivalent exact-body/local-bounds provider. The branch does
  expose local-bounds receiver-target absence facts, but those facts are not yet
  connected to one of the stronger store/root-safe evidence providers.
  Static runtime preservation helps only after such a provider has supplied
  route-local evidence; it is not itself an evidence-at provider.
- The direct public-prefix route alone is insufficient because it requires
  global callee evidence, while the assoc-base mixed case split needs
  route-local evidence-at or component-branch route facts for the no-receiver
  branch.
- Verification note: targeted `End2EndSafety.v` compiles, full `cd rocq && make`
  has completed after the recorded proof-performance fixes in
  `EnvRuntimeCapturedSafety.v`, and the OCaml valid/invalid plus FIR regression
  suites pass with the assoc-base mixed endpoint.

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
