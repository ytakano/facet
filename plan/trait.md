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
- Explicit parenthesized UFCS method calls are accepted in the ordinary
  function-call shape as `(<Ty as Trait>::method receiver args...)`; the
  receiver is the first argument, so method calls stay aligned with
  `(function args...)` rather than dot syntax. Called impl methods are
  lowered to hidden generic functions and checked through the extracted direct
  call path; hidden method bodies substitute `Self` with the concrete impl
  target type before raw elaboration; unresolved explicit targets report
  source-level `Trait::method` names. The generic-direct runtime package
  interface is split into an earlier Rocq module so UFCS runtime safety can
  reuse it without a module cycle. Rocq now exposes extracted helpers for
  resolving a trait method target from `(trait, trait args, receiver type,
  method name)` against unique impls and matching impl methods.
- Concrete associated type projections are normalized by an extracted Rocq helper
  in converted env/raw/core types when a unique impl defines the associated
  type, allowing uses such as `<unrestricted isize as Iterator>::Item` to
  type-check as `isize`. In trait and impl items, `Self::Assoc` is accepted as
  shorthand for the current trait projection, including current trait type
  arguments.

Key temporary limitations:

- Method-local lifetime generics are intentionally deferred beyond Roadmap 1-3;
  trait and impl method lifetime generics are rejected by regression tests for
  this phase.
- Only explicitly called impl methods are hidden-function elaborated and
  type-checked; uncalled impl method bodies remain stored but not checked as
  standalone functions.
- Associated projection normalization still runs as a conversion pass, but the
  normalization algorithm itself is now extracted from Rocq; wiring it into
  Rocq compatibility and proving the corresponding soundness rule remains
  pending.

## Remaining Roadmap 2-3 Tasks

1. Harden UFCS trait method calls.
   - Add the shorter prefix-form method call `(Trait::method receiver args...)`
     by parsing it as a distinct method-call surface form, inferring the
     receiver type through the extracted checker, and using the extracted Rocq
     trait-method resolver to select the unique impl target. This keeps method
     calls aligned with `(function args...)`; do not introduce dot-call syntax.
   - Support receiver-let/generic-call safety-gate shapes, including local struct
     receivers, by adding a Prop-level summary plus checker soundness and
     runtime safety branch; a checker-only clause is insufficient. The reusable
     generic-direct runtime package interface is now available before
     `EnvRuntimeNarrowRuntimePackage.v`, so the next cut can add the Prop
     summary, checker soundness, and runtime branch.
   - Keep dot method-call syntax out of this phase.

2. Move associated type normalization into Rocq compatibility.
   - Use the extracted Rocq normalization helper as the compatibility/checker
     authority instead of relying on the conversion pass.
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
