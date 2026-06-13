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
- Short UFCS accepts receiver types known before checker execution: function
  parameters, syntactically typed literals, immutable pure local literals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors whose store-safe argument evidence is checked in Rocq.
  Field-bearing struct literals, payload-bearing enum constructors, direct-call
  receivers, generic direct-call receivers, non-pure inferred locals, and
  general annotated locals remain gated. Direct-call receivers cannot be
  unlocked by OCaml desugaring alone: lowering the receiver through a hidden let
  still fails the extracted end-to-end safety gate. Rocq now has the direct and
  generic receiver-method path factored into executable sidecar/checker
  summaries, proof-side shape/view lemmas, hidden-let/body packages,
  replay bridge, inversion/strip/replay-prep, conditional body-strip,
  direct summary/body-replay wrapper packages, and direct receiver return-roots
  packaging, a generic value-roots-to-hidden-root-exclusion bridge,
  consumed-frame support, and a
  behavior-preserving split between the active captured-call core gate and its
  public base wrapper. Those summaries remain inactive until their dedicated
  runtime safety branch is proved.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration no
  longer rewrites the entire raw function AST with `normalize_assoc_raw_*`; it
  preserves surface raw expressions and normalizes only at core checker
  boundaries such as function headers, expected types, annotations, explicit
  type arguments, closure/letrec signatures, and `RawCore` embedding. Impl
  method signature validation and duplicate impl key detection compare through
  assoc-aware normalization.
- Rocq has env-aware associated compatibility helpers and checked wrapper
  boundaries for core, env, root, shadow-safe root, function-level, and
  end-to-end checker entrypoints. These wrappers preserve store/root naming,
  no-shadow, parameter root coverage, and final-store param-scope coverage
  without converting back to ordinary `typed_env_roots`. There is also a
  checked assoc-boundary wrapper for general function-value `ECallExpr` paths.
  That wrapper now lives in an executable checker module and is exported for
  extraction; the proof file only proves its checked assoc-boundary soundness.
  Assoc-aware checked core/env/full entrypoints are executable, exported, and
  covered by assoc-boundary soundness. The OCaml CLI uses the extracted
  assoc-aware end-to-end checker as its accept/reject authority, and the
  required end-to-end soundness and base checked-initial-ready theorem names
  point at that active path. The end-to-end safety module now has assoc-aware
  counterparts for the strict-exact closure checker path, sidecar readiness,
  shallow call-route big-step wrappers, component/provider local-bounds facts,
  seen/direct-callee bridges, component-body route/callback providers,
  reachable route package/target providers, callback-height big-step safety,
  provider-style route/callback/store-safe bundles, top-level callback
  wrappers, component-body and local-bounds route-package providers,
  route-package wrappers through prefix-scope consumers, branch-local and
  exact-body branch wrappers, component-body summary-provider wrappers, and
  summary-call-package wrappers. Ordinary baseline theorem names remain
  available under explicit ordinary names.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish UFCS receiver hardening.
   - Keep the canonical surface syntax as prefix calls with receiver-first
     arguments.
   - Add remaining receiver shapes only when the checker and safety proofs have
     store/root-safe summary evidence. Field-bearing struct literals,
     payload-bearing enum constructors, direct-call receivers, generic
     direct-call receivers, and non-pure locals are still gated.
   - Direct-call receivers are not an OCaml-only switch: existing store-safe
     argument facts assume arg evaluation preserves static root/store shape,
     and a hidden-let receiver lowering still lacks the runtime proof needed by
     the extracted end-to-end safety gate. The next proof step is to discharge
     receiver-call-specific freshness wiring for hidden root exclusion and
     consumed-frame/general replay obligations, then combine that result with the
     existing argument-strip,
     checked-body, direct summary/body-replay, return-roots, and hidden-let
     bridge packages. Only after the direct and generic receiver-method runtime
     safety branch is proved should the receiver-method summaries be enabled as
     outer alternatives on the public base checker gate.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

## Key Decisions

- Rocq definitions are the source of truth. Generated OCaml extraction artifacts
  are not edited manually.
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
