# Function Generics Roadmap

## Status

Implemented:

- Function definitions carry `fn_type_params : nat` and
  `fn_bounds : list trait_bound` in Rocq and extracted OCaml.
- Surface functions accept mixed lifetime/type generics:
  `fn f<'a, T>(...) -> ...`.
- Function `where` clauses accept both lifetime constraints and trait bounds:
  `where 'a: 'b, T: Show`.
- De Bruijn conversion lowers function type params to existing `TParam nat`.
- Function type/bound validation rejects out-of-range type params and unknown
  trait bounds.
- Explicit generic direct calls are supported:
  `(f<affine isize> x)` lowers through `RawCallGeneric`/`ECallGeneric`,
  checks type-arg arity and instantiated function bounds, instantiates
  parameters and return types, and erases type args at runtime/FIR.
- Local trait-bound assumptions inside generic function bodies are supported.
  Function body checking/elaboration runs with `fn_bounds` installed as local
  trait assumptions, so `TParam i` can satisfy required traits without a
  concrete impl at definition time.
- Implicit type-argument inference from direct-call arguments is supported.
  Raw direct calls to generic functions infer type args from formal parameter
  types versus actual argument types, validate `fn_bounds`, and elaborate to
  `ECallGeneric`. Inference does not search trait impls.
- Expected-type inference for generic direct calls is supported. Raw
  elaboration uses annotated `let`, function return type, assignment/replace
  RHS type, and `if` branch expected type to solve remaining type args before
  emitting `ECallGeneric`.
- Expected-monomorphic generic item values are supported. When a generic
  function item is used at an expected concrete `fn(...) -> ...` type, raw
  elaboration infers type args, validates `fn_bounds`, generates a monomorphic
  wrapper, and exposes the wrapper through ordinary `EFn`/`TFn` function-value
  paths.

Not implemented yet:

- Type-polymorphic function values v1.

## Next Implementation Steps

Current facts:

- Monomorphic function values are already represented by `EFn` and `TFn`.
- Lifetime-polymorphic function values are represented by `TForall`, but only
  for lifetimes: surface syntax supports `for<'a> fn(...) -> ...`.
- There is no surface or core type syntax for type-polymorphic function values
  such as `for<T> fn(T) -> T`, and no type-level trait-bound representation for
  such values.
- Generic direct calls are already handled by raw elaboration to `ECallGeneric`;
  this should remain separate from first-class generic values.

1. Add type-polymorphic function values v1.
   - Support surface value types of the form
     `for<T, U> fn(...) -> ...` and
     `for<T, U> fn(...) -> ... where T: Trait`.
   - Do not support mixed `for<'a, T>` function-value types in v1. Existing
     lifetime-only `for<'a> fn(...) -> ...` remains unchanged.
   - Keep the current lifetime-only `TForall`; add a separate type-param
     forall representation instead of widening `TForall`.
   - Do not make `Types.v` depend on `Syntax.v`. Type-level trait bounds need
     a core-level structural representation, with conversion to existing
     `trait_bound` only in checker/program layers that already import
     `Syntax.v`.
   - Expose no-capture, type-generic function items as type-polymorphic values
     through `EFn` when they have type params and no lifetime params. Keep the
     existing expected-monomorphic wrapper path unchanged.
   - Extend value calls through `ECallExpr` so a `for<T>` function value infers
     type args from actual arguments, validates stored trait bounds, checks
     substituted parameters, and returns the substituted result type.
   - Type-arg inference for `for<T>` function values does not search trait
     impls and may fail when args do not determine all type params.
   - Update FIR/type pretty-printing; type args remain erased at runtime.
   - Stop if this requires weakening typing, ownership, trait-bound checks, or
     existing lifetime HRT soundness.

2. Later: mixed lifetime/type function-value polymorphism.
   - Add `for<'a, T>` only after v1 compiles and tests pass.
   - Revisit the interaction between lifetime HRT opening and type-arg
     inference before changing the existing `TForall` proof path.

Required checks:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|Abort\.|DEBUG|idtac" rocq/theories
```

The final `rg` exits with status 1 when there are no matches; that is success.
