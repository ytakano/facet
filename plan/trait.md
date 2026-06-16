# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Traits, impls, associated types, and trait methods are parsed, lowered into
  Rocq/extracted environments, and checked by the extracted checker for
  duplicate/missing/extra/mismatched associated items. Impl method bodies are
  elaborated to hidden functions and checked even when the method is not called.
- Method-local type parameters are supported for trait and impl methods,
  including method-local bounds and generic-trait impl remapping. Method-local
  lifetime generics remain deferred and are rejected by tests.
- Method calls use receiver-first prefix UFCS forms:
  `(<Ty as Trait>::method receiver args...)` and
  `(Trait::method receiver args...)`. Dot method-call syntax is intentionally
  rejected in this phase.
- Short UFCS currently accepts receiver types known before checker execution:
  function parameters, typed literals, immutable pure local literals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors whose store-safe argument evidence is checked in Rocq.
  Field-bearing struct literals, payload-bearing enum constructors, direct-call
  receivers, generic direct-call receivers, non-pure inferred locals, and
  general annotated locals remain gated.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries.
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only extracted checker authority, with no fallback acceptance path. Public
  checker soundness aliases target this assoc-base mixed endpoint. The public
  runtime theorem `infer_program_env_end2end_big_step_safe_checked_initial_ready`
  still targets the strict mixed endpoint.
- Direct-call receiver proof work has established the active mixed endpoint,
  branch splits for direct-ready/no-receiver cases, public wrappers for the main
  route families, no-receiver receiver-method target absence/collapse facts, and
  exact-closure bridges for local-bounds routes, seen callees, direct-callee
  component checks, exact-body targets, and receiver-aware plus plain Prop-level
  combined readiness and summaries through local-bounds families.
- The remaining activation gap is proof-side: the active endpoint exposes a
  combined captured-or-component gate, including receiver-aware and plain
  Prop-level no-receiver readiness/evidence through local-bounds families, but
  still needs one concrete route/evidence
  source consumable by existing wrappers. Captured-call summaries do not convert
  to plain synthetic shadow-summary evidence. Exact-closure callee facts provide
  component/target facts, but route-summary packages also need recursive
  summary-evidence-at for each callee body; `seen [root]` cannot be promoted to
  full `seen []` exact closure because `seen` is the cycle cutoff.
  The strict mixed endpoint has static-component callback wrappers that close
  this route from `infer_program_env_end2end_assoc_strict_exact_closure`, but
  that proof does not retarget the active assoc-base endpoint used by the CLI.
  The strongest existing assoc-base path is the exact/non-captured branch
  wrapper, which would reduce activation to proving captured-summary absence
  through local-bounds-family environments in the no-receiver-method branch. The
  current captured-summary checker has a broad whole-body fallback, so this
  absence does not follow from receiver-method target absence alone.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding
     OCaml fallback logic or weakening the public theorem with a new premise.
   - Derive, from the active endpoint or existing public callbacks, one concrete
     no-receiver-branch provider strong enough for the existing active-endpoint
     wrappers: exact-body route-package, summary-at or store-safe
     evidence-at, store-safe or plain shadow summary evidence, checked
     component summary, component-body store-safe/summary evidence,
     local-bounds route evidence, an endpoint-derived not-captured/non-captured
     provider, exact non-captured provider evidence, or an exact-body
     local-bounds/scoped package provider.
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
- The remaining direct-call receiver activation blocker is proof-side. The
  active mixed endpoint exposes the combined captured-or-component gate, now
  pointwise and as receiver-aware/plain Prop readiness/evidence through
  local-bounds-family environments, and closes the direct-ready branch, but the
  public runtime theorem still lacks a concrete source for one route fact in the
  no-receiver-method branch. The available static-component
  route is tied to the strict exact-closure base endpoint, so the next proof step
  must derive an assoc-base route/evidence provider rather than reuse that
  strict wrapper. The exact/non-captured provider shape remains the cleanest
  existing assoc-base wrapper, but it now requires a new checker-side distinction
  or a stronger endpoint fact: for every local-bounds-family function, prove
  `check_fn_root_shadow_captured_call_store_safe_summary env' fdef = false`
  under the no-receiver-method branch. Existing branch wrappers can consume that
  fact once supplied; they do not derive it, and receiver-method target absence
  alone is insufficient because captured-summary checking can succeed on the
  whole function body.
- Receiver-method target absence is not enough: those targets are distinct from
  ordinary direct-call targets. Even after collapsing receiver-method summary
  checks and deriving boolean, Prop-level, and local-bounds direct-combined
  gates in the no-receiver branch, a route-local exact-body or store/root
  evidence provider is still required.

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
