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

Not implemented yet:

- Local trait-bound assumptions inside generic function bodies.
- Implicit type-argument inference.
- Expected-return inference for zero-argument generic calls.
- Generic function values.

## Next Implementation Steps

1. Add local generic bound assumptions.
   - Extend trait checks so `TParam i` can satisfy required traits from
     `fn_bounds`.
   - Use this for generic function bodies that construct bounded structs or call
     bounded functions.

2. Add implicit inference.
   - Solve type args from formal parameter types versus actual argument types.
   - Report unresolved and conflicting type params as errors.
   - Do not infer a type solely from trait impl search.

3. Add expected-return inference.
   - Use annotated `let`, assignment, and return contexts to solve remaining
     type args.
   - Allow zero-argument generic calls only when the expected type uniquely
     solves all params.

4. Add generic function values.
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
