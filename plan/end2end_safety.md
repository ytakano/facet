# End-to-end safety roadmap

## Goal

CLI acceptance uses only the extracted Rocq `infer_program_env_end2end`
checker. `ErrNotImplemented` and `ErrEndToEndSafetyGateFailed` reject; they
never fall back to an OCaml checker.

Required theorem names stay intact:

- `infer_program_env_end2end_sound`
- `check_program_env_end2end_sound`
- `infer_program_env_end2end_big_step_safe_checked_initial_ready`

## Current baseline

Final status: full Rocq, OCaml, CLI, and FIR verification pass. CLI acceptance
uses the extracted end-to-end checker; fallback checker acceptance remains
disabled. The direct mixed parameter-call case is intentionally invalid until
elaborated to a wrapper or explicit generic call.

Completed work: direct generic calls, nested generic direct-call fuel runtime
packages, resolved reborrow/write roots, checked narrow/rootless paths, OCaml
CLI end-to-end entrypoint enforcement, function-value/generic wrapper
specialization, FIR suffix-resilient smoke checks, and extraction fixture
updates.

## Active tasks

1. Done: compact roadmap to the final baseline.
2. Done: add checked/rootless empty-struct constructor summaries.
3. Done: accept no-bounds empty `EStruct` direct generic constructor bodies.
4. Done: accept empty generic constructor bodies in wrapper contexts.
5. Done: accept generated generic function-value wrappers whose bodies are
   explicit `ECallGeneric` direct calls.
6. Done: add elaborated generic function-value calls with inferred type args
   present at runtime, backed by instantiated callee summaries.
7. Done: accept supported mixed `TForall (... TTypeForall (... TFn ...))`
   function-value calls; direct mixed parameter calls remain intentionally
   invalid until elaborated to a wrapper or explicit generic call.
8. Done: final verification and roadmap closeout.
   Checks: `cd rocq && make`, proof-hole scan, `dune build`,
   `sh tests/run.sh`, `sh tests/fir/run.sh`.

## Required checks

After each Rocq/extraction slice:

- focused Rocq target for touched files
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build` when extraction/checker artifacts change
- targeted CLI tests for the changed construct

Before roadmap completion:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

## Constraints

- Do not duplicate type-checking logic in OCaml.
- Do not edit generated extraction artifacts manually.
- Do not weaken theorem statements or add proof holes.
- Keep each completed task committed with this roadmap updated.
