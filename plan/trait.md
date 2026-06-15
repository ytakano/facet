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
- Method calls use Facet's ordinary prefix call shape: `(callee args...)`.
  Explicit UFCS is `(<Ty as Trait>::method receiver args...)`; short UFCS is
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
- The extracted checker now exposes transitional strict and assoc strict
  direct-receiver endpoints:
  `infer_program_env_end2end_strict_exact_closure_direct_receiver` and
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver`. These
  wrap the existing strict exact-closure routes with executable env checks for
  provenance summary, preservation readiness, the direct-extended
  captured/direct-receiver-or-component gate, and the no-capture component gate.
  End-to-end safety wrappers discharge those executable premises from the new
  endpoints, including provider-free strict and assoc direct-receiver safety
  wrappers backed by theorem-level scoped body-lift providers.
- A mixed assoc direct-receiver endpoint,
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`,
  is exported. It runs the assoc strict exact-closure checker, then requires the
  direct-receiver safety gate only when an elaborated function body has a direct
  or generic direct receiver-method shape. It has checker-boundary soundness
  aliases, and the required public soundness aliases now target it. A runtime
  branch theorem covers mixed results whose checked env also passes the direct
  receiver gate. The mixed base-route theorem now uses env-local component
  route evidence for checked functions instead of global provider premises,
  and a static-runtime callback variant removes that route-evidence premise entirely.
  Direct `root_of_place` store-root naming helpers are proven for explicit
  store-name membership and for prefix-typed stores. Prefix-typed-place and
  preservation-ready borrow helpers now package store naming for direct place
  roots, direct borrow roots, borrowed place roots, and resolved place roots.
  A prefix-aware static-runtime callback shape is defined, with a bridge from
  the legacy callback, a direct-borrow instance, and prefix-shaped argument-root
  naming compatibility consumed by the current core route cleanup bridge branches.
  The argument-root helper now takes the prefix-aware callback directly. The
  first core cleanup route, the exact-body cleanup core/package-at routes,
  the exact-body package height route, the frame-scope exact-body package,
  package-at, reachable package-provider, and reachable package-and-target-provider
  routes, the from-typed-route frame bridge, the combined exact-body
  package and package-at-all routes, their exact-body and package-at-all
  projection wrappers, the frame-scope, statement, and height wrapper layers,
  and the first exact-body route-package layers, including per-function,
  reachable package-provider summary, reachable package-provider, and reachable
  package-and-target-provider variants, expose prefix-callback theorems while
  keeping legacy public shapes as wrappers. Higher route wrappers still bridge
  legacy static-runtime premises into the prefix chain.
  Mixed endpoint success now exposes the underlying assoc strict exact-closure
  success, checked-env name uniqueness, strict exact-closure readiness, and a
  direct-endpoint success
  fact when the checked env also passes the direct receiver gate. The mixed
  runtime wrappers now consume those reusable facts. The public runtime-safety
  theorem still needs a stronger static-runtime bridge before it can target the
  mixed endpoint.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration keeps
  surface raw expressions and normalizes associated projections only at core
  checker boundaries such as headers, expected types, annotations, explicit type
  arguments, closure/letrec signatures, and `RawCore` embedding.
- Assoc-aware checked core/env/full/end-to-end entrypoints are executable,
  exported, and covered by assoc-boundary soundness. The required public
  soundness theorem names target the assoc strict exact-closure mixed
  direct-receiver endpoint; the required public runtime-safety theorem still
  targets the non-mixed direct-receiver endpoint. Extraction is current, but the
  OCaml CLI still uses the older assoc-aware endpoint until the mixed endpoint
  has the required public runtime-safety theorem and can become the sole CLI
  authority.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Route the public runtime-safety theorem name through the mixed assoc
     direct-receiver endpoint, preserving the direct gate for actual direct
     receiver-method bodies.
   - Switch the OCaml accept/reject path to the extracted mixed endpoint once
     the required public theorem names target it.
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
  broad enough to be the active CLI authority. The mixed endpoint avoids this
  gate for programs without direct receiver-method bodies; its direct-ready
  runtime branch is proven, and a base-route mixed runtime theorem now
  recovers assoc strict exact-closure safety for that branch from
  env-local component route evidence. A mixed-ready case-split lemma and a
  static-runtime callback theorem are available, but the remaining public theorem
  bridge now has mixed-success base and direct-ready facts threaded through
  the reusable mixed runtime wrappers. It still needs to remove the extra
  static-runtime premise before the required public runtime-safety theorem
  can target the mixed endpoint without widening its interface. The attempted
  global static-runtime proof now has a concrete subgoal: direct place/borrow
  roots need either `In x (store_names s)` or a store-typing premise that
  connects typed-place context membership to the runtime store. The new
  prefix-typed-place and direct-borrow helpers cover that store-typing route
  locally, and a prefix-aware callback shape can carry the needed
  `store_typed_prefix` premise. Argument-root naming now consumes that
  prefix-aware callback shape directly, with route wrappers still bridging from
  the legacy callback. The public bridge still needs the remaining higher route
  and combined package callback chain to expose the prefix-aware callback shape
  directly.

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
