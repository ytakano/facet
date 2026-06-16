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
  direct-receiver endpoints plus the mixed assoc direct-receiver endpoint,
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`.
  The mixed endpoint runs the assoc strict exact-closure checker, then requires
  the direct-receiver safety gate only when an elaborated function body has a
  direct or generic direct receiver-method shape.
- Required public checker soundness aliases target the mixed endpoint:
  `infer_program_env_end2end_sound` and `check_program_env_end2end_sound`. The
  required public runtime-safety theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` now also
  targets the mixed assoc direct-receiver endpoint.
- Mixed endpoint success exposes the underlying assoc strict exact-closure
  success, checked-env uniqueness/readiness facts, no-receiver target
  contradictions for the no-method branch, collapse back to ordinary
  captured/component readiness there, branch runtime bridges for both
  direct-ready and no-receiver-method cases, a public case-split runtime
  wrapper over the mixed endpoint, an exact-body route-package wrapper for that
  mixed case split, and a checked component-summary bridge for mixed component
  store-safe callbacks.
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
  component-summary boolean directly. The remaining runtime theorem gap is
  threading the packaged stronger callback through the higher combined wrapper
  chain so the required public theorem needs no new premise.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries.
- Assoc-aware checked core/env/full/end-to-end entrypoints are executable,
  exported, and covered by assoc-boundary soundness. The OCaml CLI still uses
  the older assoc-aware endpoint until the mixed endpoint has the required
  public runtime-safety theorem and can become the sole CLI authority.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Switch the OCaml accept/reject path to the extracted mixed endpoint now
     that all required public theorem names target it.
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
- The mixed endpoint avoids that gate for programs without direct
  receiver-method bodies. Its direct-ready/no-receiver branch runtimes, public
  case-split runtime wrapper, mixed exact-body route-package wrapper, checked
  component-summary bridge, stronger prefix static callback package, and public
  runtime-safety theorem are proven without widening the public theorem
  interface. The remaining activation blocker is switching the OCaml CLI
  authority to the mixed endpoint and then adding positive direct-call receiver
  UFCS tests that pass through that verified path.

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
