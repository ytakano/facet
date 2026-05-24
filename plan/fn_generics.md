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
- Type-polymorphic function values v1 are supported.
  - Surface value types accept `for<T, U> fn(...) -> ...` and
    `for<T, U> fn(...) -> ... where T: Trait`.
  - Core types use a separate `TTypeForall` with core-level trait-bound refs,
    keeping lifetime-only `TForall` unchanged.
  - No-capture, type-generic function items with no lifetime params are exposed
    as first-class type-polymorphic values through `EFn`.
  - `ECallExpr` on `for<T>` values infers type args from actual arguments,
    validates stored trait bounds, checks substituted parameters, and returns
    the substituted result type.
  - Raw elaboration propagates expected argument types for monomorphic calls,
    so higher-order calls such as passing `id<T>` to a parameter of type
    `for<T> fn(...) -> ...` are supported.
  - Type args remain erased in FIR/runtime output.

Not implemented yet:

- Mixed lifetime/type function-value polymorphism.

## Next Implementation Steps

1. Later: mixed lifetime/type function-value polymorphism.
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
