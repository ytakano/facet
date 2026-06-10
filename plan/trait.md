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
- Trait method signatures and impl method definitions are lowered into Rocq
  records, validated for duplicate/missing/extra/mismatched methods, and checked
  against substituted impl trait arguments.
- Method-local type parameter syntax is accepted in trait and impl methods as
  `fn name<T>(...) -> ... where T: Bound`; parameters, return types, and bounds
  are converted into the existing Rocq method/function generic fields and
  signature arity matching rejects non-generic impls for generic trait methods,
  and method-local bounds are matched structurally after trait-argument
  substitution.
- Explicit UFCS method calls can pass method-local type arguments as
  `(<Ty as Trait>::method<Arg> receiver args...)`; lowering prepends `Self` to
  those method arguments before calling the hidden generic impl method.
- Explicit parenthesized UFCS method calls are accepted in the ordinary call
  shape as `(<Ty as Trait>::method receiver args...)`; called impl methods are
  lowered to hidden generic functions and checked through the extracted direct
  call path; hidden method bodies substitute `Self` with the concrete impl
  target type before raw elaboration; unresolved explicit targets report
  source-level `Trait::method` names.
- Concrete associated type projections are normalized in converted env/raw/core
  types when a unique impl defines the associated type, allowing uses such as
  `<unrestricted isize as Iterator>::Item` to type-check as `isize`.

Key temporary limitations:

- Method-local lifetime generics are intentionally deferred beyond Roadmap 1-3;
  trait and impl method lifetime generics are rejected by regression tests for
  this phase.
- Only explicitly called impl methods are hidden-function elaborated and
  type-checked; uncalled impl method bodies remain stored but not checked as
  standalone functions.
- Associated projection normalization currently runs as an OCaml conversion pass
  using the extracted `impl_matches_b`; moving this into Rocq compatibility and
  proving the corresponding soundness rule remains pending.
- `Self::Assoc` shorthand is pending; use explicit `<Self as Trait>::Assoc` in
  validated method signatures for now.

## Remaining Roadmap 2-3 Tasks

1. Harden UFCS trait method calls.
   - Add the shorter `(Trait::method receiver args...)` form after receiver
     type-directed resolution exists in Rocq.
   - Support receiver-let/generic-call safety-gate shapes, including local struct
     receivers, by adding a Prop-level summary plus checker soundness and
     runtime safety branch; a checker-only clause is insufficient.
   - Keep dot method-call syntax out of this phase.

2. Move associated type normalization into Rocq compatibility.
   - Add a Prop-level rule or equivalence for concrete associated type
     projections and prove checker soundness for it.
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
