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
  general annotated locals remain gated by tests until store/root-safe checker
  evidence is available.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Associated
  projections are still normalized before ordinary compatibility checks.
- Rocq has env-aware associated compatibility helpers and checked wrapper
  boundaries for core, env, root, shadow-safe root, function-level, and
  end-to-end checker entrypoints. These wrappers preserve store/root naming,
  no-shadow, parameter root coverage, and final-store param-scope coverage
  without converting back to ordinary `typed_env_roots`. There is also a
  checked assoc-boundary wrapper for general function-value `ECallExpr` paths.
  That wrapper now lives in an executable checker module and is exported for
  extraction; the proof file only proves its checked assoc-boundary soundness.
  Assoc-aware checked core/env/full entrypoints are also executable, exported,
  and covered by assoc-boundary soundness. An assoc-aware end-to-end checker
  variant is exported and has program-level assoc-boundary soundness, now also
  surfaced from the end-to-end safety module for downstream consumers. That
  module can also derive the same sidecar readiness checks from the assoc-aware
  path, and the base big-step checked-initial-ready safety theorem has an
  assoc-aware counterpart. The OCaml CLI now uses the extracted assoc-aware
  end-to-end checker as its accept/reject authority. The required end-to-end
  soundness and base checked-initial-ready theorem names now point at that
  assoc-aware active path, while the old ordinary `typed_env_roots` path remains
  available under explicit ordinary names. The first shallow derived big-step
  safety wrappers, covering call-statement routes, summary exact-package
  component evidence, and the summary call-package store-safe provider step,
  also have assoc-aware counterparts.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Move associated compatibility through the checker call-site boundary.
   - Use the checked assoc-boundary wrappers for final-store scope and general
     function-value `ECallExpr` paths as the bridge into safety consumers; the
     latter is executable, extracted, and available through assoc-aware
     checked core/env/full entrypoints.
   - Bridge or generalize the remaining deeper derived big-step safety
     consumers that still require ordinary `checked_fn_env_roots_checked` so
     they can consume the assoc-boundary relation instead.
   - Remove pre-compatibility normalization only after raw elaboration expected-
     type paths use assoc compatibility. A direct removal currently rejects valid
     projection compatibility cases before checker execution, so this remains a
     raw-elaboration bridge task rather than a CLI switch.

2. Finish UFCS receiver hardening.
   - Keep the canonical surface syntax as prefix calls with receiver-first
     arguments.
   - Add remaining receiver shapes only when the checker and safety proofs have
     store/root-safe summary evidence. Field-bearing struct literals,
     payload-bearing enum constructors, direct-call receivers, generic
     direct-call receivers, and non-pure locals are still gated.
   - Direct-call receivers are not a checker-only switch: existing store-safe
     argument facts assume arg evaluation preserves static root/store shape,
     while direct calls need the separate direct-call route package.
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
