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

Latest targeted baseline after task 5 (2026-06-03): invalid tests were previously
passing; 7 valid tests still fail, all higher-order generic function-value
safety-gate cases:

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
2. Done: add checked/rootless empty-struct constructor summaries.
   Checks: `make EnvRuntimeBaseSafety.vo`, `make TypeChecker.vo`,
   `dune build`, proof-hole scan. Direct generic constructor tests still fail
   at the callee-body bridge.
3. Done: accept no-bounds empty `EStruct` direct generic constructor bodies in
   the ordinary narrow summary.
   Checks: `make EnvRuntimeBaseSafety.vo`, `dune build`, proof-hole scan,
   `generic_expected_return_zero_arg.facet` passes.
4. In progress: accept empty generic constructor bodies in wrapper contexts.
   - Done: annotated-let return wrapper.
     Checks: `make EnvRuntimeBaseSafety.vo`, `make EnvRuntimeCapturedSafety.vo`,
     `dune build`, proof-hole scan,
     `generic_expected_annotated_let_zero_arg.facet` passes.
   - Done: if branches.
     Checks: `make EnvRuntimeBaseSafety.vo`, `make EnvRuntimeCapturedSafety.vo`,
     `dune build`, proof-hole scan, `generic_expected_if_branches.facet`
     passes.
   - Done: assignment RHS.
     Checks: `make EnvRuntimeBaseSafety.vo`, `make EnvRuntimeCapturedSafety.vo`,
     `cd rocq && make`, `dune build`, proof-hole scan,
     `generic_expected_assignment_rhs.facet` plus prior wrapper targets pass.
     At that point `sh tests/run.sh` still failed only the 9 function-value tasks.
5. In progress: accept generated generic function-value wrappers whose bodies
   are explicit `ECallGeneric` direct calls.
   - Done: checker/spec branch is binder-aware and rejects wrapper-call args
     that mention the temporary wrapper binder.
     Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: add hidden-frame stripping helper for alpha-renamed callee
     bodies; params/body locals are fresh from the hidden binder.
     Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: add hidden-frame generic-call argument decomposition; it strips
     call args without summarizing the hidden closure frame.
     Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: add hidden-frame expression-body strip for generic-call bodies.
     Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: require ready instantiated nested bodies for generic-direct wrapper
     safety; extraction updated `fixtures/TypeChecker.ml`.
     Check: `make EnvRuntimeBaseSafety.vo`.
   - Blocker narrowed: generic hidden-frame strip cannot apply to calls because
     `preservation_ready_expr` excludes `ECall`/`ECallGeneric`.
   - Todo: extend the call-specific helper through generic-direct callee body
     execution; its base case must avoid requiring closure-target summaries
     for the hidden frame.
   - Todo: rerun targeted CLI tests after captured proof compiles.
6. Todo: accept `TTypeForall (... TFn ...)` function-value calls through the
   end-to-end store-safe summary.
7. Todo: accept mixed `TForall (... TTypeForall (... TFn ...))`
   function-value calls through the same safety path.
8. Todo: final full verification and roadmap closeout.

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
