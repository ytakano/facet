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
   - Done: refactor the hidden-frame generic-call package helper so it
     strips the outer arguments and delegates alpha-renamed body packaging; it
     no longer requires `store_function_closure_targets_summary` for the hidden
     local closure frame. Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: add store-safe typed-arg free-var support plus hidden-frame
     freshness/value-typing transport helpers. Check: `make EnvRuntimeBaseSafety.vo`.
   - Done: wrap stripped nested generic-direct packages back into the
     outer hidden-frame package after parameter cleanup.
     Check: `make EnvRuntimeCapturedSafety.vo`.
6. In progress: add an explicit elaborated generic function-value call
   node so inferred type args are present at runtime.
   - Done: add `ECallExprGeneric` syntax/traversal/FIR plumbing; checker
     accept paths still reject it as `ErrNotImplemented`.
     Checks: `cd rocq && make`, `dune build`, proof-hole scan.
     `sh tests/run.sh` still fails the 8 known generic function-value/local
     safety-gate cases; `sh tests/fir/run.sh` remains red on existing
     safety-gate and brittle FIR name-suffix expectations.
   - Done: type-check pure `TTypeForall (... TFn ...)` calls to
     `ECallExprGeneric` and regenerate extraction.
     Checks: `cd rocq && make`, `dune build`, proof-hole scan.
     Targeted valid pure function-value tests now fail at the expected
     end-to-end safety gate, not raw elaboration.
   - Done: prove pure `TTypeForall` root/shadow-safe checker packages
     for `ECallExprGeneric`; extraction updated.
     Checks: `make EnvRootSoundness.vo`, `cd rocq && make`, `dune build`,
     proof-hole scan. Targeted pure valid tests still fail at the end-to-end
     summary/evaluator gate.
   - Done: add `ECallExprGeneric` evaluator and thread impossible
     evaluator cases through readiness/preservation proofs.
     Check: `cd rocq && make`.
   - Done: add checker/spec support for pure type-generic
     function-value call summary recognition.
     Checks: `make EnvRuntimeShadowCheckerFacts.vo`, `dune build`,
     proof-hole scan.
   - Done: gate type-generic call summaries to lbound-free type args;
     extraction updated. Checks: `make EnvRuntimeShadowCheckerFacts.vo`,
     `dune build`, proof-hole scan.
   - Done: add closed type-argument helper proofs for type-generic
     function-value call runtime signatures.
     Check: `make TypeSafetyDirectCallWrappers.vo`.
   - Done: add `ECallExprGeneric` route helper for pure type-generic
     function values. Check: `make TypeSafetyDirectCallWrappers.vo`,
     proof-hole scan.
   - Done: add function-signature substitution-stability evidence;
     boundedness alone is insufficient because omitted struct/enum type
     args are filled from the active type-arg list.
     Check: `make EnvStructuralRules.vo`, proof-hole scan.
   - Done: add environment-level signature substitution-stability
     projections for non-generic global call blockers.
     Check: `make EnvStructuralRules.vo`, proof-hole scan.
   - Done: add compatibility fuel monotonicity proof support for boolean
     substitution transport.
     Check: `make EnvStructuralRules.vo`, proof-hole scan.
   - Todo: prove boolean compatibility substitution transport, then roots-shadow
     type-substitution preservation for arbitrary bodies or an equivalent
     closed-type-arg `callee_body_root_shadow_provenance_summary` lemma.
   - Todo: use that lemma to finish the end-to-end store-safe summary
     package for pure `TTypeForall (... TFn ...)` `ECallExprGeneric` callees.
7. Todo: accept mixed `TForall (... TTypeForall (... TFn ...))`
   through `ECallExprGeneric` after task 6 compiles.
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
