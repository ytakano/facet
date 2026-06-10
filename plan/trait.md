# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system, keeping Rocq as the
source of truth for accept/reject behavior. OCaml may parse and resolve names,
but trait solving, method resolution, associated type normalization, and final
validity checks belong in Rocq and the extracted checker.

## Current Status

Completed:

- Trait and impl item block syntax is accepted by the OCaml frontend while
  preserving marker forms: `trait Show;`, `trait Show {}`, `impl Show for T;`,
  and `impl Show for T {}`.
- Trait associated type declarations and impl associated type definitions are
  represented in Rocq/extracted environments and validated for duplicate,
  missing, and extra definitions.
- Associated type projections have syntax, lowering, core representation, type
  traversal support, extraction, OCaml validation, and printer coverage for the
  explicit form `<Ty as Trait>::Assoc`.
- Trait method signatures are lowered into Rocq `trait_method_sig` values and
  validated for duplicate names, parameter/return types, `Self`, associated
  projections, and lifetime elision in method inputs/outputs.
- Impl method definitions are lowered into `impl_methods`, preserved in the
  environment, checked for well-formed types, and validated for duplicate,
  missing, extra, and structurally mismatched method signatures against the
  selected trait.
- Explicit parenthesized UFCS method calls are accepted in the ordinary call
  shape as `(<Ty as Trait>::method receiver args...)`; called impl methods are
  lowered to hidden generic functions and checked through the extracted direct
  call path.

Key temporary limitations:

- Impl method signature matching is structural in the shared `Self` layout;
  substitution of concrete trait arguments for generic impls is still pending.
- Only explicitly called impl methods are hidden-function elaborated and
  type-checked; uncalled impl method bodies remain stored but not checked as
  standalone functions.
- Concrete associated type projection normalization through impl definitions is
  pending.
- `Self::Assoc` shorthand is pending; use explicit `<Self as Trait>::Assoc` in
  validated method signatures for now.

## Remaining Roadmap 1-3 Tasks

1. Complete substitution-aware impl method signature matching.
   - Instantiate trait method signatures with the impl's `Self`, trait args,
     lifetimes, and type parameters.
   - Validate receiver type, parameter arity/types, return type, and method
     lifetime elision after instantiation.
   - Keep substitution-aware generic receiver resolution pending; explicit UFCS
     targets are already lowered through hidden direct calls.

2. Harden UFCS trait method calls.
   - Add the shorter `(Trait::method receiver args...)` form after receiver
     type-directed resolution exists in Rocq.
   - Improve missing impl and missing method diagnostics; current failures are
     rejected through hidden direct-call lookup.
   - Support more safety-gate shapes for receiver expressions, including local
     struct receivers, without weakening the end-to-end checker.
   - Keep dot method-call syntax out of this phase.

3. Normalize associated type projections.
   - Normalize concrete projections through the selected impl definition.
   - Preserve generic projections such as `<T as Trait>::Assoc` under local
     bounds.
   - Keep associated type defaults and equality constraints deferred.

## Constraints and Checks

- Do not add handwritten OCaml checker fallback paths.
- Parser/desugar must not perform type-directed trait solving.
- Do not weaken linearity, affine discard, borrow, lifetime, or drop rules.
- Update Rocq rules/checker/proofs or record explicit proof gaps whenever
  executable checker behavior changes.

Required checks for implementation tasks:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
```

The final search must not report new proof holes or debug leftovers. Existing
legacy proof-script selector matches should be called out explicitly if they
remain unrelated to the change.
