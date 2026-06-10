# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system, keeping Rocq as the
source of truth for accept/reject behavior. OCaml may parse and resolve names,
but trait solving, method resolution, associated type normalization, and final
validity checks belong in Rocq and the extracted checker.

## Current Status

Completed:

- Trait and impl item block syntax is accepted by the OCaml frontend while
  preserving existing marker forms: `trait Show;`, `trait Show {}`,
  `impl Show for T;`, and `impl Show for T {}`.
- Trait blocks can carry associated type declarations and method signatures in
  the surface AST.
- Impl blocks can carry associated type definitions and method bodies in the
  surface AST.
- Rocq `trait_def` and `impl_def` now have item fields. Associated type
  declarations/definitions are represented in the extracted environment.
- Impl associated type definitions are validated against the selected trait:
  missing, extra, and duplicate definitions are rejected.
- Associated type projections have syntax, lowering, core representation, type
  traversal support, extraction, OCaml validation, and printer coverage:
  `<Ty as Trait>::Assoc` and `Self::Assoc`.
- Method items are still kept only in the surface AST until method typing is
  introduced.

Key temporary limitation: associated type projections are represented and
validated structurally, but concrete projection normalization through impl
associated type definitions is still pending.

## Remaining Roadmap 1-3 Tasks

1. Lower and validate trait methods.
   - Add core representation for method signatures that can mention `Self` and
     associated type projections.
   - Lower trait method signatures from the surface AST into Rocq.
   - Validate method names, receiver types, arity, and `Self` use.
   - Keep method bodies unresolved until UFCS method resolution can target them.

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
