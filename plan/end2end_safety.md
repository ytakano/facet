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

Latest `sh tests/run.sh` baseline (2026-06-03): invalid tests pass; 13 valid
tests fail, all generic expected/function-value safety-gate cases:

- `generic_expected_annotated_let_zero_arg.facet`
- `generic_expected_assignment_rhs.facet`
- `generic_expected_if_branches.facet`
- `generic_expected_return_zero_arg.facet`
- `generic_item_expected_fn_bound_satisfied.facet`
- `generic_item_expected_fn_call.facet`
- `generic_item_pass_monomorphic_hof.facet`
- `mixed_forall_fn_value_annotated_let.facet`
- `mixed_forall_fn_value_pass_and_call.facet`
- `mixed_forall_fn_value_trait_bound_call.facet`
- `type_forall_fn_value_annotated_let.facet`
- `type_forall_fn_value_bound_call.facet`
- `type_forall_fn_value_pass_and_call.facet`

Completed work: direct generic calls, nested generic direct-call fuel runtime
packages, resolved reborrow/write roots, checked narrow/rootless paths, OCaml
CLI end-to-end entrypoint enforcement, and extraction fixture updates.

## Active tasks

1. Done: compact roadmap to current baseline and remaining slices.
2. Todo: accept generic direct constructor results used by expected-type
   generic item expressions, including zero-arg `make<T>()` wrappers.
3. Todo: accept generated generic function-value wrappers whose bodies are
   explicit `ECallGeneric` direct calls.
4. Todo: accept `TTypeForall (... TFn ...)` function-value calls through the
   end-to-end store-safe summary.
5. Todo: accept mixed `TForall (... TTypeForall (... TFn ...))`
   function-value calls through the same safety path.
6. Todo: final full verification and roadmap closeout.

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
