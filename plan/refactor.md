# Refactoring Plan

## Goal

Refactor Facet for maintainability while preserving semantics, trusted
boundaries, extraction, and CLI checker authority.

The OCaml CLI must continue to accept or reject programs only through the
extracted `infer_program_env_end2end` path. Generated files under `fixtures/`
must not be edited manually.

## Baseline

Known-good commands, run serially:

```sh
dune build
cd rocq && make
sh tests/run.sh
sh tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

Do not run `tests/run.sh` and `tests/fir/run.sh` concurrently; both invoke
Dune and can conflict on the Dune lock.

## Progress

Done:

- Added `rocq/tools/unused_graph.v`, a `coq-dpdgraph` driver for checker and
  public soundness roots.
- Added `rocq/tools/unused-allowlist.txt` for protected public/checker roots.
- Added `rocq/tools/unused-classification.md` with the first `dpdusage`
  candidate batch.
- Deleted private unused helper `field_names_unique_b` after source, fixture,
  build, and proof-hole checks.
- Verified:

```sh
cd rocq
opam exec -- rocq compile -R theories Facet tools/unused_graph.v
opam exec -- dpdusage unused-analysis.dpd >/tmp/facet-unused.raw
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 1: Unused Rocq Artifact Workflow

Next small task:

1. Pick the next small `INVESTIGATE` helper group from
   `rocq/tools/unused-classification.md`.
2. Inspect source references, dynamic uses, extraction exposure, and proof
   automation risk.
3. Delete only if the group is clearly private and dead; otherwise reclassify
   it precisely.
4. Run:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

Commit after the batch passes.

## Phase 2: Split `TypeChecker.v`

Target: keep `TypeChecker.v` as the facade and extraction boundary while moving
implementation groups into focused modules.

Proposed order:

1. `CheckerBase.v`: equality, compatibility, context helpers, infer result
   and error types.
2. `CheckerTraits.v`: trait refs, impl lookup, type-argument inference, generic
   call helpers.
3. `CheckerOrdinary.v`: `infer_core`, `infer_env`, `infer_full_env`.
4. `CheckerState.v`: `sctx`, binding-state helpers, structural checker.
5. `CheckerElab.v`: raw elaboration and wrapper adapters.
6. `CheckerRoots.v`: root/provenance readiness, root-aware checker,
   end-to-end checker entrypoints.
7. `TypeChecker.v`: re-exports plus extraction block.

Rules:

- Prefer move-only edits.
- Preserve exported names.
- Update `rocq/_CoqProject` in dependency order.
- Keep extraction targets available from `TypeChecker.v`.
- Commit after each compiling sub-split.

Verification per sub-split:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 3: Split `EnvRuntimeBaseSafety.v`

Target: break the largest proof file into dependency-ordered proof clusters.

Proposed modules:

- `EnvRuntimeInitialFacts.v`
- `EnvRuntimeFunctionValueCallFacts.v`
- `EnvRuntimeGenericDirectCallFacts.v`
- `EnvRuntimeCapturedCallFacts.v`
- `EnvRuntimeBaseSafety.v` as compatibility facade

Commit after each moved proof group with:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 4: Split `AlphaShadowProvenance.v`

Target: separate root/sctx naming facts from typed-root and provenance alpha
proofs, coordinated with `plan/refactor_renaming.md`.

Proposed modules:

- `AlphaRootEnvFacts.v`
- `AlphaTypedRoots.v`
- `AlphaShadowProvenance.v` as compatibility facade

Commit after each moved proof group with:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 5: Small OCaml Cleanup

Tasks:

- Remove or justify `[@@warning "-34"]` in `ocaml/main.ml`.
- Audit reachable `failwith` in `ocaml/debruijn.ml`, `ocaml/parser.mly`, and
  `ocaml/fir.ml`.
- Do not add any handwritten OCaml checker fallback.

Verification:

```sh
dune build
sh tests/run.sh
sh tests/fir/run.sh
```

## Completion Criteria

- Repeatable `dpdgraph`/`dpdusage` workflow exists and has been used for any
  Rocq deletion.
- `TypeChecker.v` is a small facade/extraction boundary.
- `EnvRuntimeBaseSafety.v` and `AlphaShadowProvenance.v` are split or explicitly
  documented as intentionally aggregated.
- All baseline commands pass serially.
