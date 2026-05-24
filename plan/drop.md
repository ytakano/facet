# Affine Auto Drop Lowering

## Status

Implemented.

- Rocq raw elaboration inserts explicit `EDrop` operations for live affine
  bindings at `RawLet` and `RawLetInfer` scope exit.
- Generated drops preserve the body result with typed internal `ELet`
  bindings, avoiding borrow-check gaps around generated `ELetInfer`.
- Linear values are not auto-dropped and remain normal checker obligations.
- Affine structs are dropped structurally in stable field order, skipping moved
  or consumed paths.
- `replace` still returns the old value and does not immediately drop it.
- `assign` lowers through `FIReplace` and structurally drops the old value,
  including mutable-reference targets such as `*r` and `**rr`.

## Validation

Regression coverage lives in `tests/fir/run.sh` and focused fixtures under
`tests/fir/` for:

- scope-end affine scalar and struct drops;
- partially moved affine struct drops;
- direct affine struct assignment old-value drops;
- mutable-reference affine scalar and struct assignment old-value drops;
- `replace` not immediately dropping its returned old value.

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
