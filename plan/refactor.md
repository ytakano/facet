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
- Added `rocq/tools/unused-classification.md`; first-pass candidates are
  classified with no remaining `INVESTIGATE` entries.
- Deleted private unused helpers `field_names_unique_b`, `trait_impl_error`,
  `infer_call_type_args`, `infer_args`,
  `infer_type_forall_call_no_env`, and
  `duplicate_param_name_none_nodup_params_ctx_suffix` after source, fixture,
  build, and proof-hole checks.
- Reclassified protected candidates: extraction roots, raw elaboration
  constructor, public/proof-facing facts, regression examples, automation
  artifacts, and executable checker helpers with real callers.
- Started `TypeChecker.v` splitting by moving equality and depth helpers to
  `CheckerBase.v` while keeping `TypeChecker.v` as the facade.
- Moved compatibility helpers to `CheckerBase.v` while keeping `TypeChecker.v`
  as the facade.
- Moved capture/ref-free type predicates and soundness lemmas to
  `CheckerBase.v` while keeping `TypeChecker.v` as the facade.
- Moved decidable context operations to `CheckerBase.v` while keeping
  `TypeChecker.v` as the facade.
- Moved function lookup and lifetime well-formedness helpers to
  `CheckerBase.v` while keeping `TypeChecker.v` as the facade.
- Moved checker error helpers to `CheckerBase.v` while keeping `TypeChecker.v`
  as the facade.
- Moved generic checker result helpers to `CheckerBase.v` while keeping
  `TypeChecker.v` as the facade.
- Moved trait and type-argument helpers to `CheckerTraits.v` while keeping
  `TypeChecker.v` as the facade.
- Moved HRT lifetime substitution and call-argument helpers to
  `CheckerHrt.v` while keeping `TypeChecker.v` as the facade.
- Moved closure capture helpers to `CheckerClosure.v` while keeping
  `TypeChecker.v` as the facade.
- Verified:

```sh
cd rocq
opam exec -- rocq compile -R theories Facet tools/unused_graph.v
opam exec -- dpdusage unused-analysis.dpd >/tmp/facet-unused.raw
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 1: Unused Rocq Artifact Workflow

Status: complete for the first pass. Re-run this workflow before any future
Rocq artifact deletion.

Completed checks:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Phase 2: Split `TypeChecker.v`

Next small task:

1. Check dependencies before moving ordinary `infer_place` and field/variant
   helper slice into the next checker module.
2. Run full verification and commit.

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
