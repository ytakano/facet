# Context Window Refactor Roadmap

## Summary

The closure and captured-call proof work is now materially more context-window
friendly. The main closure proof entrypoints have been split into focused
modules with compatibility export surfaces, so a continuation no longer needs
to reload the original large captured-call, runtime-args, closure-wrapper, or
call-frame files wholesale.

The remaining problem is no longer the already-completed split history. The
current risks are large foundational files and stale or overly detailed notes
outside the reconciled roadmap.

## Current Evaluation

- Optimized for closure implementation work: yes.
- The highest-value closure files now have small public aggregators:
  `TypeSafetyCapturedCall.v`, `TypeSafetyClosureRuntimeArgs.v`,
  `TypeSafetyClosureWrappers.v`, `TypeSafetyClosureCleanup.v`,
  `TypeSafetyCallFrame.v`, and several preservation wrappers are compatibility
  export surfaces.
- Focused proof slices are mostly under 900 lines, with the largest active
  closure-related slices around `TypeSafetyClosureRuntimeArgsFacts.v`,
  `TypeSafetyClosureRuntimeArgsLet.v`, `TypeSafetyClosureWrappersCleanup.v`,
  `TypeSafetyCapturedCallMake.v`, and `TypeSafetyCapturedCallLet.v`.
- Not fully optimized for repository-wide proof work: large shared foundations
  remain, especially `TypeChecker.v`, `TypeSafetyRootsReady.v`,
  `TypeSafetyHiddenFrameBase.v`, and `TypeSafetyRootEnvParams.v`.
- `plan/type_safety_roadmap.md` is still the active proof-intent document. Its
  captured-call subset-bridge status and module-ownership guidance have been
  reconciled with the current split; when future text conflicts with code,
  inspect the code and update the roadmap separately.

## Remaining Bottlenecks

- `TypeChecker.v` is still large and should not be split casually. Any checker
  modularization must preserve Rocq as the source of truth and regenerate
  extracted OCaml through `cd rocq && make`.
- `TypeSafetyRootsReady.v` and `TypeSafetyHiddenFrameBase.v` are still large,
  but both need careful ownership design before another split. Do not delegate
  their boundary selection to sub-agents.
- `TypeSafetyRootEnvParams.v` is a likely future target only when an active
  proof needs a narrower root-env helper boundary.
- The direct with-env captured-call subset bridge is no longer a roadmap/status
  discrepancy. It exists as
  `captured_call_callee_body_root_shadow_provenance_instantiated_bridge_with_result_subset`
  and is used by captured-call make/let routes. Exact `ELet` evidence should
  still wait for explicit returned-root, store-root, and no-shadow package
  coverage.

## Operating Rules

- Read `plan/type_safety_roadmap.md` first for the active proof task.
- Use this file only to decide whether another context-window refactor is
  justified.
- Do not start another split only because a file is large. Split only when a
  current proof task exposes a stable ownership boundary or compile-time
  measurement identifies a concrete bottleneck.
- Keep compatibility export surfaces and public theorem names stable.
- Keep theorem strengthening, checker widening, and file movement in separate
  commits.
- Use sub-agents only for implementation-only work with fixed symbols, target
  files, constraints, and checks. Do not delegate uncertainty reduction,
  invariant design, checker contract changes, or repository-wide investigation.
- Keep planning files compact. Remove completed blow-by-blow history once it no
  longer helps the next task.

## Next Refactor Candidates

1. If the next proof repeatedly opens `TypeSafetyRootsReady.v`, design a split
   around a stable fact cluster first, then implement it as a separate
   proof-organization refactor.
2. If the next proof repeatedly opens `TypeSafetyHiddenFrameBase.v`, first map
   dependencies around capture roots, copied capture stores, empty root envs,
   frame readiness, and hidden-store stripping support.
3. Split `TypeSafetyRootEnvParams.v` only when an active proof needs a narrower
   root-env helper boundary.

## Checks

For roadmap-only edits:

```sh
git diff --check
```

For later Rocq refactors, start with focused checks near the touched modules,
then run the full type-system pipeline when behavior or checker extraction is
affected:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\.|Abort\.|DEBUG|idtac" rocq/theories
```

The final `rg` command exits with status 1 when there are no matches; that is a
successful result.
