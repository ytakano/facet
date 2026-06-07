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
- Moved ordinary place, field, branch, and parameter helpers to
  `CheckerOrdinary.v` while keeping `TypeChecker.v` as the facade.
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

Progress:

- Split env-aware place and HRT call helpers into `CheckerEnvHelpers.v`.
- Split ordinary `infer_core` checker body into `CheckerCore.v`.
- Split env-aware `infer_core_env_fuel` checker body into `CheckerEnvCore.v`.
- Split `sctx`/binding-state/field-path state helpers into `CheckerState.v`.
- Split ordinary state checker body into `CheckerStateCore.v`.
- Split elab helpers and elab state checker body into `CheckerElabCore.v`.
- Split root helpers and ordinary root-aware checker body into `CheckerRootsCore.v`.
- Split shadow-safe root checker body and checked wrappers into
  `CheckerRootsShadow.v`.
- Split function-level and program-level checker wrappers plus nodup lemmas into
  `CheckerProgram.v`.
- Split basic regression examples into `CheckerExamplesBasic.v`.
- Split borrow conflict checker into `CheckerBorrow.v`.
- Split combined type + borrow checker wrappers into `CheckerFull.v`.
- Split alpha-normalization and elab program wrappers into
  `CheckerAlphaElabProgram.v`.
- Split root-shadow sidecar summaries and program end-to-end checker wrappers
  into `CheckerRootSidecars.v`.
- Split large root-sidecar regression examples into
  `CheckerExamplesRootSidecars.v`.
- Split raw elaboration and extraction-adjacent definitions into
  `CheckerRawElab.v`.

Status: complete.

Final verification passed:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
git diff --check
git diff -- fixtures/TypeChecker.ml fixtures/TypeChecker.mli
```

Target: keep `TypeChecker.v` as the facade and extraction boundary while moving
implementation groups into focused modules.

Final structure:

1. `CheckerBase.v` through `CheckerProgram.v`: executable checker layers.
2. `CheckerExamplesBasic.v` and `CheckerExamplesRootSidecars.v`: Rocq regression examples.
3. `CheckerBorrow.v`, `CheckerFull.v`, `CheckerAlphaElabProgram.v`, and
   `CheckerRootSidecars.v`: borrow, full, alpha/elab, and end-to-end wrappers.
4. `CheckerRawElab.v`: raw syntax and elaboration entrypoints.
5. `TypeChecker.v`: re-exports plus extraction block.

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
- `EnvRuntimeNarrowCheckerFacts.v`
- `EnvRuntimeFunctionValueRuntimeFacts.v`
- `EnvRuntimeLocalBoundsBridgeFacts.v`
- `EnvRuntimeNarrowRuntimePackage.v`
- `EnvRuntimeDirectCallStoreSafeFacts.v`
- `EnvRuntimeCheckedPrefixRuntimePackage.v`
- `EnvRuntimeFinalStoreScopeFacts.v`
- `EnvRuntimeCapturedCallFacts.v`
- `EnvRuntimeGenericDirectRuntimePackage.v`
- `EnvRuntimeGenericDirectAlphaRuntimeFacts.v`
- `EnvRuntimeGenericDirectHiddenFrameFacts.v`
- `EnvRuntimeGenericDirectFuelRuntimeFacts.v`
- `EnvRuntimeCapturedCallSummaryFacts.v`
- `EnvRuntimeTopLevelSafetyFacts.v`
- `EnvRuntimeBaseSafety.v` as compatibility facade

Commit after each moved proof group with:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

Progress:

- Move initial store/type-param/root helper facts to `EnvRuntimeInitialFacts.v`.
- Split function-value call argument safety/helper facts into
  `EnvRuntimeFunctionValueCallFacts.v`.
- Split narrow summary definitions and alpha-renaming/substitution helper facts
  into `EnvRuntimeNarrowSummaryFacts.v`.
- Split generic direct-call instantiation and fresh-renaming facts into
  `EnvRuntimeGenericDirectCallFacts.v`.
- Split narrow summary checker and runtime target helper facts into
  `EnvRuntimeNarrowCheckerFacts.v`.
- Split function-value call runtime preservation facts into
  `EnvRuntimeFunctionValueRuntimeFacts.v`.
- Split local-bounds and direct-call provenance bridge facts into
  `EnvRuntimeLocalBoundsBridgeFacts.v`.
- Split the narrow summary runtime package induction into
  `EnvRuntimeNarrowRuntimePackage.v`.
- Split direct-call store-safe bridge and prefix runtime facts into
  `EnvRuntimeDirectCallStoreSafeFacts.v`.
- Split checked and prefix runtime package proofs into
  `EnvRuntimeCheckedPrefixRuntimePackage.v`.
- Split final-store, frame-scope, and param-scope preservation proofs into
  `EnvRuntimeFinalStoreScopeFacts.v`.
- Split captured-call summary, checker, instantiated-fuel, and bridge foundation
  facts into `EnvRuntimeCapturedCallFacts.v`.
- Split generic direct-call cleanup, runtime package, and prefix-named
  value proof into `EnvRuntimeGenericDirectRuntimePackage.v`.
- Split generic direct-call alpha-renaming and runtime typed-args/package facts
  into `EnvRuntimeGenericDirectAlphaRuntimeFacts.v`.
- Split hidden-frame generic direct-call runtime helper facts into
  `EnvRuntimeGenericDirectHiddenFrameFacts.v`.
- Split fuel-based generic direct-call runtime facts into
  `EnvRuntimeGenericDirectFuelRuntimeFacts.v`.
- Split captured-call store-safe summary and checker facts into
  `EnvRuntimeCapturedCallSummaryFacts.v`.
- Move runtime structural helper facts and top-level safety theorems into
  `EnvRuntimeTopLevelSafetyFacts.v`, leaving `EnvRuntimeBaseSafety.v` as a
  pure compatibility facade.

Next small task: continue Phase 4 `AlphaShadowProvenance.v` alpha-preservation split.

## Phase 4: Split `AlphaShadowProvenance.v`

Target: separate root/sctx naming facts from typed-root and provenance alpha
proofs, coordinated with `plan/refactor_renaming.md`.

Proposed modules:

- `AlphaRootEnvFacts.v`
- `AlphaTypedRoots.v`
- `AlphaShadowProvenance.v` as compatibility facade

Progress:

- Split root/sctx naming, root-env rename/equiv, and no-collision helper facts into
  `AlphaRootEnvFacts.v`.
- Split typed-root shadow-safe mutual naming theorems into
  `AlphaTypedRoots.v`.
- Moved base typed-root alpha-preservation lemmas for trivial, fn, drop,
  replace, assign, var, place, and borrow expressions into `AlphaTypedRoots.v`.
- Moved root-env remove/params/no-collision helper facts used by typed-root
  let preservation into `AlphaTypedRoots.v`.
- Moved root-env name subset helpers and non-shadow-safe let/letinfer
  alpha-preservation lemmas into `AlphaTypedRoots.v`.
- Moved shadow-safe let/letinfer alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved shadow-safe support let/letinfer alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved non-shadow-safe if alpha-preservation lemma into `AlphaTypedRoots.v`.
- Moved var shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved place shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved borrow shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved replace shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved assign shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved if shadow-safe and support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved args/fields typed-root alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved root-env lookup/name subset helpers into `AlphaRootEnvFacts.v` and
  match-tail shadow-safe alpha-preservation into `AlphaTypedRoots.v`.
- Moved call/struct non-support alpha-preservation lemmas into
  `AlphaTypedRoots.v`.
- Moved call support alpha-preservation lemmas into `AlphaTypedRoots.v`.

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
