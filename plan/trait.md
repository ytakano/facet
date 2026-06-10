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
- Explicit UFCS method calls can pass method-local type arguments as
  `(<Ty as Trait>::method<Arg> receiver args...)`; lowering prepends `Self` to
  those method arguments before calling the hidden generic impl method.
- Explicit parenthesized UFCS method calls are accepted in the ordinary
  function-call shape as `(<Ty as Trait>::method receiver args...)`; the
  receiver is the first argument, and additional arguments follow it, so
  method calls stay aligned with `(function args...)` rather than dot
  syntax. This prefix parenthesized UFCS spelling is the canonical method-call surface
  for Roadmap 1-3; dot calls are not aliases during this phase. Called impl methods are
  lowered to hidden generic functions and checked through the extracted direct
  call path; hidden method bodies substitute `Self` with the concrete impl
  target type before raw elaboration; unresolved explicit targets report
  source-level `Trait::method` names. The generic-direct runtime package
  interface is split into an earlier Rocq module so UFCS runtime safety can
  reuse it without a module cycle. Rocq now exposes extracted helpers for
  resolving a trait method target from `(trait, trait args, receiver type,
  method name)` against unique impls and matching impl methods. The shorter
  prefix form `(Trait::method receiver args...)` is accepted when `receiver` is
  a variable whose type is known from the raw-lowering value context, currently
  function parameters including struct parameters, and when the receiver is a
  literal expression whose type is syntactically known during raw lowering.
  Struct literal, enum constructor, and direct function-call receivers are
  recognized by short-UFCS raw lowering, and the same expression-receiver
  shapes are parsed by explicit UFCS, but these expression receivers
  currently reach the end-to-end safety gate and remain covered by
  invalid regression tests, including generic direct-call receivers.
  Immutable annotated or inferred local receivers initialized with
  unrestricted unit, int, float, or bool literals are lowered by eliminating
  the pure receiver `let` when the local name is used only as the receiver,
  including calls with additional arguments, so `(Trait::method x arg ...)`
  reaches the checker as the same prefix call shape as `(Trait::method 1 arg ...)`.
  Short UFCS uses the same ordinary call layout for method-local type
  arguments and additional arguments, `(Trait::method<Arg> receiver arg ...)`.
  The generated grammar also documents explicit UFCS method-local type
  arguments in the prefix shape. Accepted variable and literal receiver
  calls, generic-trait explicit UFCS with method-local type arguments and
  accepted/rejected method-local bounds, plus ordinary and generic-trait
  explicit UFCS excess method type arguments are covered by regression
  tests, and dot syntax, including type-argument dot calls, is rejected
  for this phase.
  Concrete non-generic impl methods no longer keep an unused hidden `Self` type
  argument, so local struct receivers elaborate to the safety-gate boundary
  instead of failing raw lifetime unification. Generic trait arguments require
  the explicit `<Ty as Trait<...>>` UFCS spelling.
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
- Short method calls intentionally use the same parenthesized call syntax as
  functions: `(Trait::method receiver args...)`. Dot method-call syntax remains
  out of phase and is covered by rejection tests.

## Remaining Roadmap 2-3 Tasks

1. Harden UFCS trait method calls.
   - Continue extending short prefix UFCS only where the receiver type is known
     before checker execution. Function-parameter variables, including struct
     parameters, and syntactically typed literals are supported; generic trait
     arguments stay explicit through `<Ty as Trait<...>>`, and Roadmap 1-3 does
     not add a short form for them.
   - Support the remaining receiver-let/generic-call safety-gate shapes.
     Immutable annotated and inferred local receivers initialized by unrestricted
     unit, int, float, or bool literals are now accepted by pure receiver-let
     elimination in raw lowering and covered by valid regression tests.
     Struct, enum, and direct function-call expression receivers now resolve in raw lowering but
     still hit the end-to-end safety gate. Direct-call receivers cannot be
     completed by a raw temporary-let rewrite alone, because let-bound direct
     calls still need store-safe summary evidence. Generic direct-call
     receivers and annotated local struct receivers in short and explicit UFCS
     are covered by invalid tests for this boundary.
     General annotated local receivers still need a Prop-level summary plus
     checker soundness and runtime safety branch; a checker-only clause
     is insufficient. Non-pure inferred local receivers still fail earlier because
     short UFCS has no checker-backed receiver type inference and remain covered by an
     invalid regression test.
   - Keep dot method-call syntax out of this phase; parser-level rejection is
     covered by regression tests.

2. Move associated type normalization into Rocq compatibility.
   - Replace pre-compatibility normalization with env-aware Rocq compatibility
     so associated projection equality is checked at the typing rule boundary;
     call-argument, let-annotation, struct-field, enum-payload,
     function-value-signature, closure-signature, and trait-method-signature
     compatibility have regression coverage for accepted concrete projections
     and rejected mismatches.
   - Wire compatibility at the typing-rule boundary before changing helper
     call sites. Helper-only wiring to `check_arg_tys_assoc` makes the
     executable checker accept normalized associated compatibility while
     existing typing and env/root typing rules still require ordinary
     `typed_args` compatibility, so full soundness fails. The core
     `typed`/`typed_args` relation currently carries only `fenv`, not
     `global_env`, so the next implementation step is either an env-aware
     argument relation plus env/root bridge, or a proved bridge from
     normalized raw elaboration to ordinary `typed_args`; only after that
     should checker helpers switch to assoc-aware compatibility. Attempts to put
     assoc helper soundness in
     `EnvSoundnessFacts.v`, `CompatBoolSoundness.v`, or `CheckerSoundness.v`
     pulled in heavy dependencies or did not finish single-file compilation
     quickly, so a lighter proof-module split remains part of this step.
   - Keep associated type defaults and equality constraints deferred.

3. Keep Haskell-style deriving on the trait roadmap.
   - After associated compatibility and UFCS are checker-backed, add a
     `deriving` surface form that expands to ordinary impl declarations and
     is validated by the extracted checker rather than by OCaml fallback
     logic. Initial candidates are structural traits with deterministic
     generated bodies. Current syntax is intentionally rejected by regression
     tests; deriving for traits with associated type defaults or equality
     constraints waits until those features exist.

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
