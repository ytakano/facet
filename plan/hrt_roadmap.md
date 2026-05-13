# HRT Roadmap: Higher-Rank Lifetimes

## Summary

Facet now has the core higher-rank lifetime machinery in place. The
current design separates definition-site lifetime polymorphism from
type-site higher-rank function types:

```facet
fn id<'a>(r: unrestricted &'a unrestricted isize)
  -> unrestricted &'a unrestricted isize {
    r
}

fn accept(
  f: unrestricted for<'a> fn(unrestricted &'a unrestricted isize)
       -> unrestricted &'a unrestricted isize
) -> unrestricted () {
    ()
}
```

`fn id<'a>(...)` defines a lifetime-polymorphic function item. When the
function item is used as a value, the checker closes its item lifetimes
into a `TForall` function value type. `for<'a> fn(...) -> ...` is a type
syntax, not a function-definition syntax.

The implemented HRT surface syntax for type-level bounds is:

```facet
for<'a, 'b> fn(...) -> ... where 'a: 'b
```

This roadmap tracks what is done, what is currently in progress, and
what remains.

## Implemented

### HRT v1: Type-level representation

- Added `LBound nat` for lifetimes bound by higher-rank function types.
- Added `TForall nat outlives_ctx Ty`.
- Added parser support for `for<'a> fn(...) -> ...`.
- Added well-formedness, equality, lifetime substitution, no-capture
  handling, pretty-printing, and extraction support.
- Added conservative `TForall` compatibility for matching arity, bounds,
  and body structure.
- Added valid/invalid tests for parsing, duplicate bound lifetimes,
  unknown lifetimes, and bound lifetime escape.

### HRT v2: Function values

- Added `EFn ident` for zero-capture function item values.
- Function items with lifetime parameters are exposed as `TForall`
  function value types.
- Bare identifier resolution prefers local bindings; otherwise it can
  resolve to a function item value.
- Existing direct calls remain compatible when no local binding shadows
  the function name.

### HRT v3: Function-typed calls

- Added `ECallExpr expr (list expr)` for calls through function-typed
  expressions.
- Calls through `TFn` values are checked against parameter types.
- Calls through `TForall` values instantiate bound lifetimes per call
  site using argument types.
- The checker rejects calls whose return type or opened bounds still
  contain unresolved `LBound`.
- Added `ErrNotAFunction` for non-function callees.
- Added operational semantics, alpha-renaming, checker soundness, borrow
  soundness, and usage proof support for `EFn` / `ECallExpr`.

## Implemented

### HRT v4: Bounds

- HRT bounds use postfix syntax:

```facet
for<'a, 'b> fn(unrestricted &'a T) -> unrestricted &'b T where 'a: 'b
```

- Parser support resolves HRT-bound lifetimes as `LBound` and outer
  function lifetimes as `LVar`.
- `TForall n bounds body` stores HRT bounds in the core type.
- Function item `fn_outlives` constraints are closed into function value
  `TForall` bounds.
- Function-value calls open HRT bounds and check them against the caller
  outlives context.
- Bounds that still contain unresolved `LBound` after opening are treated
  as lifetime leaks.

### HRT v5a: Unused-bound generalization

- Allow conservative generalization from `TFn` to `TForall` only when the
  expected `TForall` has empty bounds and its body contains no `LBound`.
- This permits `fn(isize) -> isize` where
  `for<'a> fn(isize) -> isize` is expected.
- This still rejects monomorphic functions for HRT types whose bound
  lifetimes occur in argument or return positions.

### HRT v6: Variance improvement

- Function compatibility now uses contravariant argument types and
  covariant return types.
- `TForall` binder/bounds compatibility remains conservative: arity and
  stored bounds must still match structurally.
- Added tests for contravariant function arguments and covariant returns.

### HRT v7: Diagnostics improvement

- Added specific checker errors for unsatisfied HRT bounds, unresolved
  HRT-bound lifetimes, monomorphic functions used where used-bound HRT is
  required, and malformed HRT bodies.
- Keep existing errors as fallbacks for compatibility.

### HRT v8: HRT bounds syntax cleanup

- Normalize documentation and examples to postfix `where`:

```facet
for<'a, 'b> fn(...) -> ... where 'a: 'b
```

- Update grammar documentation to match the implemented syntax.
- Avoid the older roadmap example `for<'a where ...> fn(...) -> ...`
  unless that syntax is intentionally added as sugar later.

### HRT v9: Proof refinement

- The implementation is soundness-backed and uses no `Axiom` or
  `Admitted`, but several HRT facts are still embedded inside checker
  soundness proofs.
- Function variance and unused-bound generalization are covered by
  `ty_compatible_b_sound`.
- Dedicated helper lemmas now cover boolean outlives constraints,
  checker argument typing, contravariant function argument compatibility,
  unused-bound generalization, and opened-call no-leak splitting.
- Deeper wf/opening/substitution lemmas remain a future proof-quality
  cleanup, not a soundness blocker.

### HRT v10: FIR/runtime limitation cleanup

- Runtime semantics represents function values as closure objects.
- FIR lowering now has explicit `FICallValue` instructions for calls
  through function values.
- Calls through function-valued variables are emitted faithfully for
  zero-capture function values.
- Added FIR coverage for function-valued variable calls.

### HRT v11: Closure object foundation

- Function item values are represented as empty-capture closures.
- Dynamic `ECallExpr` dispatch evaluates the callee to a closure object
  and invokes the closure target.
- FIR printing exposes `closure f` values so dynamic call sites no longer
  look like static function item calls.

## Remaining Tasks

- Closure capture for function values.
- Full captured-environment typing and borrow semantics for closures.
- More granular proof cleanup for HRT wf/opening/substitution lemmas.
- Optional syntax sugar for function-definition-level `for<'a> fn f(...)`.

## Current Test Coverage

Valid HRT tests include:

- `tests/valid/lifetime/hrt_parse_fn_type.facet`
- `tests/valid/lifetime/hrt_pass_poly_identity.facet`
- `tests/valid/lifetime/hrt_call_function_param.facet`
- `tests/valid/lifetime/hrt_call_twice.facet`
- `tests/valid/lifetime/hrt_direct_call_unchanged.facet`
- `tests/valid/lifetime/hrt_bound_satisfied.facet`
- `tests/valid/lifetime/hrt_item_bounds_as_value.facet`
- `tests/valid/lifetime/hrt_monomorphic_as_unused_poly.facet`
- `tests/valid/lifetime/hrt_fn_variance.facet`

Invalid HRT tests include:

- `tests/invalid/lifetime/hrt_duplicate_lifetime.facet`
- `tests/invalid/lifetime/hrt_unknown_lifetime.facet`
- `tests/invalid/lifetime/hrt_bound_lifetime_escape.facet`
- `tests/invalid/lifetime/hrt_lifetime_leak.facet`
- `tests/invalid/lifetime/hrt_call_non_function.facet`
- `tests/invalid/lifetime/hrt_monomorphic_as_used_poly.facet`
- `tests/invalid/lifetime/hrt_bound_unsatisfied.facet`
- `tests/invalid/lifetime/hrt_bound_leak.facet`
- `tests/invalid/lifetime/hrt_bound_unknown_lifetime.facet`
- `tests/invalid/lifetime/hrt_fn_variance_arg.facet`

## Validation Baseline

For HRT changes, run:

```sh
cd rocq && make
bash tests/run.sh
bash tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\." rocq/theories/TypeSystem
```

The final `rg` command should produce no matches.

## Non-goals

- Closure capture.
- Higher-rank type variables.
- Trait-style lifetime bounds.
- Lifetime elision.
- Function-definition syntax of the form `for<'a> fn f(...)`.

These can be added later as independent extensions if needed.
