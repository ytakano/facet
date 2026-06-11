# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system, keeping Rocq as the
source of truth for accept/reject behavior. OCaml may parse and resolve names,
but trait solving, method resolution, associated type normalization, and final
validity checks belong in Rocq and the extracted checker.

## Current Status

Completed:

- Trait and impl item syntax is accepted and lowered into Rocq/extracted
  environments. Trait associated types, impl associated type definitions,
  trait method signatures, and impl method bodies are validated for duplicate,
  missing, extra, and mismatched items. Associated type projections use the
  explicit form `<Ty as Trait>::Assoc` and have syntax, lowering, core
  representation, traversal, extraction, validation, and printer coverage.
- Method-local type parameter syntax is accepted in trait and impl methods as
  `fn name<T>(...) -> ... where T: Bound`; parameters, return types, and bounds
  are converted into the existing Rocq method/function generic fields and
  signature arity matching rejects non-generic impls for generic trait methods,
  and method-local bounds are matched structurally after trait-argument
  substitution, including the type-parameter index remapping needed when a
  concrete generic-trait impl has method-local type parameters. All impl
  method bodies are hidden-function elaborated and
  checked through the extracted checker even when the method is not called;
  the generated grammar documents method-local generics and bounds for trait
  and impl methods.
- Prefix UFCS method calls use the ordinary function-call shape, with the
  receiver as the first argument: `(<Ty as Trait>::method receiver args...)`
  and `(Trait::method receiver args...)`. Method-local type arguments use the
  same layout, for example `(<Ty as Trait>::method<Arg> receiver args...)`;
  lowering prepends the concrete `Self` type before calling the hidden generic
  impl method. Dot calls are intentionally rejected for Roadmap 1-3, and generated grammar
  output documents both short and explicit prefix UFCS forms.
  Called impl methods lower to hidden functions checked through the extracted
  direct-call path, hidden method bodies substitute `Self`, unresolved targets
  report source-level `Trait::method` names, and Rocq exposes extracted method
  resolution helpers for unique impl lookup. Short UFCS accepts receiver types
  known during raw lowering: function-parameter variables, syntactically typed
  literals, and immutable annotated or inferred pure local literals after
  receiver-let elimination. Struct, enum, direct-call, generic direct-call,
  and non-pure inferred local receivers remain at the documented safety-gate
  boundary with invalid tests. Regression coverage includes generic-trait
  explicit UFCS with method-local type args and bounds, extra method type args,
  pure local receivers in short and explicit UFCS, including method-local
  type arguments and bool/unit/float literal variants, and dot-syntax
  rejection.
  Generic trait arguments require the explicit `<Ty as Trait<...>>` spelling.
- Concrete associated type projections are normalized by extracted Rocq
  env/raw/core traversal helpers when a unique impl defines the associated
  type, allowing uses such as `<unrestricted isize as Iterator>::Item` to
  type-check as `isize` across value compatibility sites, aggregate fields and
  payloads, function/closure/method signatures, explicit and short UFCS
  method type arguments, generic call and aggregate type arguments, impl trait
  arguments, and trait-bound positions including trait, function, trait-own,
  and method-local bounds. Accepted cases and mismatch rejections are covered
  by regression tests.
  Global environment and raw function normalization now
  happen inside the extracted Rocq raw-elaboration entrypoint before hidden
  stubs and checked bodies are built; OCaml no longer runs an associated-type
  normalization pass. In trait and impl items, `Self::Assoc` is accepted as
  shorthand for the current trait projection, including current trait type
  arguments. Rocq now has an `AssocCompatibility` bridge that names env-aware
  compatibility and its executable boolean form over `normalize_assoc_ty`; a
  lightweight `CompatBoolSoundness` module proves the boolean compatibility
  soundness needed for normalized associated projections. `AssocCompatibility`
  is ordered before checker helpers, and `CheckerHrt` exposes env-aware
  `check_args_assoc` and `check_arg_tys_assoc` helpers. Checker call sites
  still use ordinary compatibility and are not yet wired to those helpers. The
  OCaml pre-elaboration validation defers impl method signature equality until
  after extracted Rocq normalization so it does not reject normalizable
  associated projections before the checker runs.
  Generic projections such as `<affine T as Iterator>::Item` are
  preserved under local trait bounds and covered by valid/invalid regression
  tests for same-parameter and mismatched-parameter compatibility.

Key temporary limitations:

- Method-local lifetime generics are intentionally deferred beyond Roadmap 1-3;
  trait and impl method lifetime generics are rejected by regression tests for
  this phase.
- Associated projection normalization still runs before ordinary compatibility
  checks inside the extracted Rocq raw elaborator. Wiring checker call sites to
  the env-aware helper layer and proving the corresponding soundness connection
  remain pending.
- Method calls intentionally use the same parenthesized prefix call shape as
  functions: `(callee args...)`. Short UFCS uses `(Trait::method receiver args...)`,
  and explicit UFCS uses `(<Ty as Trait>::method receiver args...)`; both treat
  the receiver as the first argument. This is the canonical Roadmap 1-3 method
  call surface; later receiver-oriented sugar must desugar to the same prefix
  shape before Rocq checking. Dot method-call syntax remains out of phase and
  is covered by rejection tests.

## Remaining Roadmap 1-3 Tasks

1. Harden UFCS trait method calls.
   - Continue extending short prefix UFCS only where the receiver type is known
     before checker execution. Function-parameter variables, including struct
     parameters, and syntactically typed literals are supported; generic trait
     arguments stay explicit through `<Ty as Trait<...>>`, and Roadmap 1-3 does
     not add a short form for them.
   - Support the remaining receiver-let/generic-call safety-gate shapes.
     Immutable annotated and inferred local receivers initialized by unrestricted
     unit, int, float, or bool literals are accepted in short and explicit
     UFCS by pure receiver-let elimination in raw lowering and covered by
     focused valid regression tests.
     Struct, enum, and direct function-call expression receivers now resolve in
     raw lowering but still hit the end-to-end safety gate. Direct-call
     receivers cannot be
     completed by a raw temporary-let rewrite alone, because let-bound direct
     calls still need store-safe summary evidence. Generic direct-call
     receivers, local inferred direct-call receivers, and annotated local
     struct receivers in short and explicit UFCS are covered by invalid tests
     for this boundary.
     General annotated local receivers still need a Prop-level summary plus
     checker soundness and runtime safety branch; a checker-only clause
     is insufficient. Non-pure inferred local receivers still fail earlier because
     short UFCS has no checker-backed receiver type inference and remain covered by an
     invalid regression test.
   - Keep method calls aligned with ordinary function calls by using the
     parenthesized prefix shape `(callee args...)`, with the receiver passed as
     the first argument for trait methods. Keep dot method-call syntax out of
     this phase; parser-level rejection is covered by regression tests.

2. Move associated type normalization into Rocq compatibility.
   - Replace pre-compatibility normalization with env-aware Rocq compatibility
     so associated projection equality is checked at the typing rule boundary;
     call-argument, let-annotation, struct-field, enum-payload,
     function-value-signature, closure-signature, and trait-method-signature
     compatibility have regression coverage for accepted concrete projections
     and rejected mismatches.
   - Wire compatibility at the typing-rule boundary before changing helper
     call sites. Helper-only wiring to `check_arg_tys_assoc` would make the
     executable checker accept cases that the current typing and env/roots
     relations cannot justify, so checker call sites must stay on ordinary
     compatibility until the bridge is proved.
   - Current helper coverage names the unchecked-to-checked boundary without
     expanding normalized compatibility proofs: checked argument and single-value
     relations; struct-field, enum-payload, function-body, trait-method
     signature, and trait-method-resolution facts; env/roots argument, field,
     payload, HRT, generic-call, direct-call, and function-value collector facts;
     normalized `if`, match, and core-shape witnesses; and env/roots
     function-body wrappers. These facts carry
     `ty_compatible_assoc_checked`/boolean witnesses and expose structural
     composition, arity, length, and inversion facts. Conditional bridge
     reductions now show `typed_args_assoc_checked` reduces to
     `typed_args_assoc`, and env/roots checked argument and field relations reduce to
     their ordinary relations once the corresponding isolated compatibility
     bridge assumptions are available.
   - Remaining blocker: prove the single-pair bridge from
     `ty_compatible_assoc_checked` to `ty_compatible_assoc`, prove an env/root
     bridge that avoids expanding normalized compatibility at each call site, or
     prove that normalized raw elaboration implies the ordinary
     `typed_args`/compatibility relations. Direct wrappers from
     `ty_compatible_assoc_b = true` to `ty_compatible_assoc` still stall during
     proof checking once `normalize_assoc_ty` is exposed. Keep carrying checked
     boolean witnesses until this bridge exists.
   - Keep associated type defaults and equality constraints deferred.

3. Keep Haskell-style deriving on the trait roadmap.
   - `deriving` is reserved for a future surface form. For now, provisional
     `struct ... deriving Trait { ... }` and
     `enum ... deriving Trait { ... }` syntax are caught by the parser and
     rejected with an explicit deferred error, and `deriving` cannot be used as
     an identifier. Once associated compatibility and UFCS are checker-backed,
     deriving should expand to ordinary impl declarations validated by the
     extracted checker rather than by OCaml fallback logic. Initial candidates
     are structural traits with deterministic generated bodies; traits with
     associated type defaults or equality constraints wait until those features
     exist.

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
