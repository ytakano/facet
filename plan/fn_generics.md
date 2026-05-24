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

Not implemented yet:

- Generic function values.

## Next Implementation Steps

1. Add generic function values.
   - Decide representation for generic function values and closure values before
     exposing them through ordinary value calls.

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
