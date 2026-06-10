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
- Impl method bodies are still kept only in the surface AST until method body
  checking and UFCS method resolution are introduced.

Key temporary limitations:

- Concrete associated type projection normalization through impl definitions is
  pending.
- `Self::Assoc` shorthand is pending; use explicit `<Self as Trait>::Assoc` in
  validated method signatures for now.

## Remaining Roadmap 1-3 Tasks

1. Validate and lower impl methods.
   - Lower impl method definitions into `impl_methods` only after their
     signatures can be matched against the selected trait method signatures.
   - Validate method names, arity, receiver type, return type, and absence of
     missing/extra/duplicate impl methods.
   - Keep method calls unresolved until UFCS resolution is added.

2. Add parenthesized UFCS trait method calls.
   - Match Facet's ordinary function call shape: `(callee arg...)`.
   - Use qualified method callees: `(Trait::method receiver args...)` and
     `(<Ty as Trait>::method receiver args...)`.
   - Treat the receiver as the first ordinary argument; do not introduce a dot
     method-call form in this phase.
   - Resolve calls through a unique impl or local bound in Rocq, then elaborate
     to an ordinary resolved call or an explicit resolved core trait-call form.
   - Reject missing impls, ambiguous impls, missing methods, wrong arity, and
     receiver usage violations.

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
