# Lifetime v10: `&mut` References Are Non-Unrestricted

## Summary

- v10 closes the remaining `EVar r` copy-aliasing hole by making `unrestricted &mut T` ill-formed.
- `&mut` references are allowed only as `affine &mut T` or `linear &mut T`.
- Borrow expressions produce `affine &mut T`; existing usage subtyping lets callers bind that value as `linear &mut T` when they want a must-use unique reference.

## Key Changes

- Add a reference usage well-formedness check: shared references keep the existing usage freedom, while unique references reject `UUnrestricted`.
- Change mutable borrow and mutable reborrow result types from `unrestricted &mut T` to `affine &mut T`.
- Keep `EVar` copy/consume behavior usage-based: affine and linear references are consumed when used as values.
- Add `expr_as_place` so `*r` and `**rr` are typed, checked, and evaluated as place dereferences, not as by-value moves of `r`.
- Preserve the existing borrow conflict checks for reborrows and write-through-reference.

## Tests

- Update existing valid/invalid tests from `unrestricted &mut` to `affine &mut` unless the test is specifically about malformed `unrestricted &mut`.
- Add invalid tests for `unrestricted &mut` in local annotations, parameters, and return types.
- Add valid coverage for binding an `affine &mut` value to a `linear &mut` annotation.
- Keep existing nested deref, replace, assign, reborrow, and FIR tests as regressions.

## Validation

- `cd rocq && make`
- `bash tests/run.sh`
- `bash tests/fir/run.sh`
- Accept fixture updates only from Rocq extraction.

## Assumptions

- `linear &mut T` is well-formed.
- `&mut` expression results remain affine by default.
- Shared references are unchanged.
- Explicit outlives constraints, lifetime elision, and higher-rank lifetimes remain future work.
