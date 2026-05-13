# HRT Roadmap: Higher-Rank Lifetimes Full Implementation

## Summary

This roadmap defines the path to fully implement higher-rank lifetimes
for Facet. The target surface form is:

```facet
for<'a, 'b> fn(&'a T, &'b U) -> &'a T
```

The current implementation already has `TFn` and explicit outlives
constraints, but it does not yet have first-class function values,
function-typed parameters, variable-position calls, or lifetime binders
inside function types. Full HRT therefore needs to be implemented in
stages rather than as a parser-only extension.

## Goals

- Add higher-rank lifetime binders to function types.
- Support `for<'a> fn(...) -> ...` as a type.
- Preserve lifetime soundness without using `Axiom` or `Admitted`.
- Support passing polymorphic functions as values.
- Support calling function-typed variables after instantiating their
  higher-rank lifetime binders.
- Prevent bound lifetime leakage.
- Integrate HRT with explicit outlives constraints.

## Non-goals for the first complete milestone

- Closure capture.
- Higher-rank type variables.
- Lifetime elision inside HRT types.
- Full variance inference for arbitrary function subtyping.
- Trait-style lifetime bounds.

## Phase 0: Baseline and invariants

Before changing HRT-related definitions, preserve the current lifetime
checker baseline.

- Keep `Axiom` and `Admitted` out of `rocq/theories/TypeSystem`.
- Keep the v11 explicit outlives design as the foundation.
- Treat `fn_outlives` as item-level lifetime assumptions.
- Treat HRT bounds as type-level lifetime assumptions scoped under the
  HRT binder.
- Keep `&mut` affine-or-linear and maintain the existing replace-only
  policy for linear referents.

Expected validation:

- `cd rocq && make`
- `bash tests/run.sh`
- `bash tests/fir/run.sh`

## Phase 1: Type-level HRT representation

Add an explicit higher-rank lifetime binder to the core type language.

Recommended representation:

```coq
| TForall : nat -> outlives_ctx -> TypeCore A -> TypeCore A
```

The `nat` is the number of bound lifetime variables. The `outlives_ctx`
contains bounds between lifetimes in the scope extended by the bound
variables. The body is normally a `TFn`, but the representation should
not rely on that invariant unless the checker enforces it separately.

Tasks:

- Extend `TypeCore` with `TForall`.
- Extend type equality and usage computation over `TForall`.
- Extend lifetime substitution so outer substitutions do not capture or
  rewrite bound lifetimes incorrectly.
- Extend `wf_type_b` and related well-formedness predicates.
- Extend pretty-printing and extraction artifacts through the normal
  Rocq build.

Initial restriction:

- Accept only `TForall _ _ (TFn _ _)` at the surface syntax level.

## Phase 2: Parser and concrete syntax

Add parser support for higher-rank function types.

Target syntax:

```facet
for<'a> fn(&'a T) -> &'a T
for<'a, 'b> fn(&'a T, &'b U) -> &'a T
for<'a where 'a: 'static> fn(&'a T) -> &'static T
```

If the final `where` placement is too invasive, start with the simpler
syntax and add bounds in a follow-up:

```facet
for<'a> fn(&'a T) -> &'a T
```

Tasks:

- Parse `for<'a, ...> fn(...) -> ...`.
- Map bound lifetime names to local HRT indices.
- Reject duplicate bound lifetime names.
- Reject references to HRT-bound lifetimes outside the binder.
- Reject malformed HRT bodies that are not function types.
- Add valid and invalid parser/checker tests under `tests/`.

## Phase 3: Lifetime opening and closing

Define the operations needed to instantiate HRT types safely.

Tasks:

- Add an operation to open a `TForall` body with fresh or caller-chosen
  lifetime variables.
- Add an operation to substitute HRT-bound lifetimes with concrete
  caller lifetimes.
- Prove that opening preserves well-formedness when the instantiation
  satisfies the HRT bounds.
- Prove that opening commutes with ordinary lifetime substitution where
  required.
- Define and check the no-leak condition for HRT-bound lifetimes.

Key invariant:

- A lifetime bound by `for<'a>` must not appear in an inferred result
  type unless it has been substituted with a caller-visible lifetime.

## Phase 4: Compatibility and subtyping

Extend `ty_compatible` and `ty_compatible_b` with HRT-aware behavior.

Initial conservative rule:

- Two HRT function types are compatible when they have the same binder
  arity, compatible HRT bounds, and compatible opened bodies under a
  shared fresh lifetime context.

Instantiation rule:

- A value of type `for<'a> fn(&'a T) -> &'a T` may be used where a
  monomorphic function type is required if opening the HRT type with the
  required lifetimes yields a compatible function type.

Tasks:

- Add HRT cases to `ty_compatible`.
- Add boolean checker cases to `ty_compatible_b`.
- Prove the boolean cases sound.
- Keep function argument variance conservative at first.

Initial variance policy:

- Require same argument structure and use existing type compatibility
  for argument and return positions.
- Defer full contravariant argument subtyping until the first HRT
  milestone is stable.

## Phase 5: Function values

The existing `ECall` calls named function items directly. HRT needs
function values so polymorphic functions can be passed as arguments.

Tasks:

- Add an expression form for function item values, for example:

```coq
| EFn : ident -> expr
```

- Type `EFn f` as a function type derived from the function definition.
- If `f` has lifetime parameters, expose it as a `TForall`.
- Preserve existing direct `ECall f args` behavior for compatibility.
- Add tests for assigning and passing function item values.

Design point:

- `EFn f` should be a zero-capture function pointer, not a closure.
  This avoids adding environments to the operational semantics in the
  first HRT implementation.

## Phase 6: Function-typed calls

Add calls through function-typed expressions or variables.

Possible AST direction:

```coq
| ECallExpr : expr -> list expr -> expr
```

Tasks:

- Infer the callee expression.
- If the callee has `TFn args ret`, check arguments against `args`.
- If the callee has `TForall n bounds (TFn args ret)`, instantiate the
  HRT binders before checking arguments.
- Ensure instantiated lifetimes satisfy HRT bounds under the caller
  outlives context.
- Reject non-function callees.
- Reject calls whose inferred return type leaks an uninstantiated HRT
  lifetime.

Tests:

- Call a function-valued variable.
- Pass a polymorphic identity function and call it at two different
  lifetimes.
- Reject a monomorphic function where an HRT function is required.

## Phase 7: Checker integration

Integrate HRT into the executable checker.

Tasks:

- Extend `infer_core` with `EFn` and function-typed calls.
- Extend lifetime unification or instantiation to account for HRT
  binders.
- Reuse explicit outlives checking for HRT bounds.
- Add a checker error for non-function callees if the existing errors
  are too ambiguous.
- Keep existing direct function calls working unchanged.

Important behavior:

- Direct item calls can continue using item-level `fn_lifetimes` and
  `fn_outlives`.
- Function-value calls should use the type carried by the callee
  expression.
- HRT instantiation must happen at each call site, not when the function
  value is created.

## Phase 8: Operational semantics

Extend runtime semantics minimally for function values.

Tasks:

- Add values for function items.
- Evaluate `EFn f` to a function value.
- Evaluate function-typed calls by dispatching to the named function
  body.
- Avoid closure environments in the first implementation.
- Prove preservation/progress extensions needed by checker soundness.

Design constraint:

- Function item values are copyable only if their type usage allows it.
  Since they contain no runtime-owned resource, their usage should be
  determined by the function type, not by hidden captured state.

## Phase 9: Soundness proofs

Extend proof coverage without weakening the current no-axiom standard.

Tasks:

- Prove HRT well-formedness lemmas.
- Prove substitution/opening lemmas for HRT-bound lifetimes.
- Prove HRT cases for `ty_compatible_b_sound`.
- Prove checker soundness for `EFn`.
- Prove checker soundness for function-typed calls.
- Prove no-leak lemmas for instantiated HRT lifetimes.

Proof strategy:

- Keep the first HRT compatibility rule structurally conservative.
- Avoid adding general-purpose variance proofs until required.
- Prefer local lemmas around opening/substitution over broad rewrites of
  existing soundness proofs.

## Phase 10: Tests

Add tests under `tests/` in the existing style.

Valid tests:

- Parse and typecheck `for<'a> fn(&'a T) -> &'a T`.
- Pass a polymorphic identity function to a function expecting an HRT
  function.
- Call one HRT function value with arguments from different lifetimes.
- Use HRT bounds that are satisfied by caller outlives constraints.
- Preserve existing direct function call behavior.

Invalid tests:

- Use an HRT-bound lifetime outside its binder.
- Return a value whose type leaks an uninstantiated HRT lifetime.
- Pass `fn(&'x T) -> &'x T` where `for<'a> fn(&'a T) -> &'a T` is
  required.
- Instantiate an HRT function in a way that violates its bounds.
- Call a non-function value.

Suggested file names:

- `tests/valid/lifetime/hrt_parse_fn_type.facet`
- `tests/valid/lifetime/hrt_pass_poly_identity.facet`
- `tests/valid/lifetime/hrt_call_twice.facet`
- `tests/valid/lifetime/hrt_outlives_bound.facet`
- `tests/invalid/lifetime/hrt_lifetime_leak.facet`
- `tests/invalid/lifetime/hrt_monomorphic_as_poly.facet`
- `tests/invalid/lifetime/hrt_bound_unsatisfied.facet`
- `tests/invalid/lifetime/hrt_call_non_function.facet`

## Recommended implementation order

1. Add `TForall` and make the Rocq build compile.
2. Add parser support for `for<'a> fn(...) -> ...`.
3. Add well-formedness and substitution support.
4. Add conservative HRT compatibility.
5. Add `EFn` function item values.
6. Add calls through function-typed expressions.
7. Add HRT instantiation at call sites.
8. Extend soundness proofs.
9. Add the full valid and invalid test set.
10. Regenerate extraction through `cd rocq && make`.

## Risks

- Lifetime substitution under binders can easily become unsound if bound
  and free lifetimes share the same representation.
- Adding function values affects both typing and operational semantics.
- Full function subtyping variance can expand the proof burden
  substantially.
- If HRT bounds are added too early, parser and checker changes may
  become coupled to proof-heavy outlives work.

## Milestone split

### HRT v1

- `TForall`
- Parser support for `for<'a> fn(...) -> ...`
- Well-formedness
- Conservative compatibility
- No function values yet

### HRT v2

- Function item values
- Function-typed parameters
- Passing HRT functions as values

### HRT v3

- Calls through function-typed variables
- Per-call HRT instantiation
- No-leak checking

### HRT v4

- HRT outlives bounds
- Bound satisfaction checking
- Full soundness lemmas

### HRT v5

- More precise function variance
- Better diagnostics
- Larger integration tests
