# Lifetime v11: Explicit Outlives Constraints

## Summary

v11 adds explicit function-level outlives constraints. A constraint `'a : 'b` means `'a` outlives `'b`, allowing values such as `&'a T` to be used where `&'b T` is expected.

Surface syntax uses a Rust-like `where` clause after the return type and before the function body:

```facet
fn f<'a, 'b>(r: unrestricted &'a unrestricted isize)
  -> unrestricted &'b unrestricted isize
  where 'a: 'b {
    r
}
```

## Key Changes

- Add `fn_outlives : list (lifetime * lifetime)` to function definitions.
- Add context-aware outlives checking: reflexive, `'static`, explicit constraints, and transitive closure over explicit constraints.
- Thread the current outlives context through type compatibility, expression typing, argument typing, and checker inference.
- At function calls, apply lifetime substitution to the callee constraints and require the substituted constraints to hold in the caller context.
- Reject malformed constraints whose lifetimes are not in the function lifetime parameter context.
- Extend the OCaml parser with `where 'a: 'b (, 'c: 'd)*`.

## Tests

- `tests/valid/lifetime/outlives_where_return.facet`: direct constraint allows returning `&'a T` as `&'b T`.
- `tests/valid/lifetime/outlives_transitive_return.facet`: transitive constraints allow `&'a T` as `&'c T`.
- `tests/valid/lifetime/outlives_call_constraint_satisfied.facet`: caller constraints satisfy callee substituted constraints.
- `tests/invalid/lifetime/outlives_missing_constraint.facet`: unrelated lifetimes remain incompatible.
- `tests/invalid/lifetime/outlives_call_constraint_missing.facet`: callee constraint must be satisfied after substitution.
- `tests/invalid/lifetime/outlives_constraint_unknown_lifetime.facet`: constraints may not mention undeclared lifetimes.

## Validation

- `cd rocq && make`
- `bash tests/run.sh`
- `bash tests/fir/run.sh`
- Accept fixture updates only from Rocq extraction.

## Assumptions

- v11 does not add lifetime elision.
- v11 does not add higher-rank lifetimes.
- v11 does not change borrow conflict rules.
- Existing built-in behavior that `'static` outlives every lifetime is preserved.
