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
   - Done: expose generic `ECallExprGeneric` final-store equality
     cleanup for pure `TTypeForall (... TFn ...)` calls.
     Check: `make TypeSafetyDirectCallWrappers.vo`, proof-hole scan.
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
   - Done: add equality boolean reflexivity/same-core proof support for
     compatibility substitution transport.
     Check: `make EnvStructuralRules.vo`, proof-hole scan.
   - Done: add equality substitution transport over type-parameter
     substitution.
     Check: `make CheckerSoundness.vo`, proof-hole scan.
   - Done: add reflexive boolean support facts for compatibility substitution
     transport.
     Check: `make CheckerSoundness.vo`, proof-hole scan.
   - Done: add structural lbound-closed preservation for type-parameter
     substitution.
     Check: `make EnvStructuralRules.vo`, proof-hole scan.
   - Done: add same-core boolean compatibility support for substituted type
     parameters.
     Check: `make CheckerSoundness.vo`, proof-hole scan.
   - Done: gate type-generic function-value summary type args away from
     top-level `TForall`, which blocks compatibility transport.
     Checks: `make EnvRuntimeShadowCheckerFacts.vo`, `dune build`,
     proof-hole scan.
   - Done: prove boolean compatibility substitution transport under the
     lbound-free, no-top-level-`TForall` type-arg gate.
     Check: `make CheckerSoundness.vo`, proof-hole scan.
   - Done: prove provenance readiness is preserved by type-parameter
     substitution for expressions, args, fields, and match branches.
     Check: `make TypeSafetyProvenanceReady.vo`, proof-hole scan.
   - Done: add roots-shadow type-substitution leaf/package helpers.
     Check: `make AlphaRoots.vo`, proof-hole scan.
   - Done: package lifetime-equivalence bridges for type-parameter
     substitution under lifetime substitution in generic call signatures.
     Check: `make TypeSafetyDirectCallWrappers.vo`, proof-hole scan.
   - Done: add roots-shadow `ECallGeneric` substitution bridge with result
     lifetime-equivalence witness. Check: `make AlphaRoots.vo`, proof-hole scan.
   - Done: add roots-shadow `ECallExprGeneric` type-forall
     substitution bridge that packages substituted args/callee plus result
     lifetime-equivalence. Check: `make AlphaRoots.vo`, proof-hole scan.
   - Done: package original `ECallExprGeneric` roots-shadow typings into
     substituted existential result form with lifetime-equivalence evidence.
     Check: `make AlphaRoots.vo`, proof-hole scan.
   - Done: add exact boolean-compatible `ECallExprGeneric`
     type-substitution package, avoiding an unsound lifetime-equivalence to
     compatibility bridge. Check: `make AlphaRoots.vo`.
   - Done: identify the runtime package blocker precisely: closure lookup
     yields only unsubstituted callee provenance, while `ECallExprGeneric`
     needs either provenance for `fn_subst_type_params type_args fdef`
     or an instantiated narrow summary.
   - Done: narrow the substitution obligation: callee provenance bodies are
     `provenance_ready_expr`, which excludes call forms.
   - Done: add leaf-subset provenance-ready type-substitution package.
     Check: `make TypeSafetyCheckedRoots.vo`, proof-hole scan.
   - Done: add atomic deref-borrow roots-shadow type-substitution helper.
     Check: `make AlphaRoots.vo`.
   - Done: widen the leaf-subset substitution package to include
     deref-borrow atoms. Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EFn` roots-shadow type-substitution package with
     explicit function-value compatibility premise.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EDrop` provenance-ready wrapper substitution package
     with explicit inner transport premise.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EIf` wrapper substitution package with explicit
     condition, branch, merge, and result transport premises.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EAssign` wrapper substitution package with explicit
     RHS and assignment compatibility transport premises.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EReplace` wrapper substitution package with explicit
     RHS, restore-path, and replacement compatibility premises.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `ELetInfer` wrapper substitution package with explicit
     bound/body/check transport premises.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add annotated `ELet` wrapper substitution package with
     explicit annotation/body/check transport premises.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add leaf-subset args/fields type-substitution packages for
     structured provenance-ready bodies. Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add leaf-subset struct/enum expression package helpers with
     explicit result compatibility premises. Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add match-branch lookup preservation facts under
     type-parameter substitution. Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add match-tail roots-shadow type-substitution package.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add match payload parameter substitution and name facts.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add match payload root-env cleanup facts for applied type params.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add specialized match-tail package for applied type params.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add `EMatch` roots-shadow type-substitution package.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add general args/fields provenance-ready type-substitution packages.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add general struct/enum provenance-ready type-substitution packages.
     Check: `make TypeSafetyCheckedRoots.vo`.
   - Done: add premise-heavy dispatch umbrella for roots-shadow
     type-substitution over full `provenance_ready_expr`.
     Check: `make TypeSafetyCheckedRoots.vo`, proof-hole scan.
   - Done: add exact struct/enum instance type-substitution equality facts.
     Check: `make TypeSafetyCheckedRoots.vo`, proof-hole scan.
   - Blocked: runtime `ECallExprGeneric (EVar ...)` branch needs a
     route for `fn_subst_type_params type_args fcall`; closure lookup gives
     only unsubstituted callee provenance. The umbrella is a dispatcher, and
     `EMatch` needs exact substituted branch/core facts, not just compatible
     existentials.
   - Blocked: the closed substitution route must be gate-aware and
     exact-context; arbitrary `type_args` lack compatibility transport, and
     existential output contexts cannot feed struct/enum/match/wrapper premises.
   - Blocked: boolean compatibility transport would require transitivity
     plus boolean outlives completeness; prefer instantiated narrow summaries
     over proving a broad transport stack here.
   - Blocked: adding instantiated summaries to the narrow checker needs
     definition-order work; the instantiated checker currently depends on the
     narrow checker and is defined later.
   - Done: factor an early fuel-param instantiated body checker and
     arity-filtered all-callee gate for `ECallExprGeneric` summaries.
     Check: `make TypeChecker.vo`, proof-hole scan.
   - Done: align the all-callee gate fuel with its body inference fuel.
     Check: `make TypeChecker.vo`, proof-hole scan.
   - Done: check instantiated callee bodies in the function body env.
     Check: `make TypeChecker.vo`.
   - Done: finish the pure empty-bounds `TTypeForall (... TFn ...)`
     runtime package using instantiated body summaries and local-bounds body
     env witnesses. Checks: `make EnvRuntimeBaseSafety.vo`,
     `make EnvRuntimeShadowCheckerFacts.vo`, `make TypeChecker.vo`, proof-hole
     scan.
   - Done: run the end-to-end gate on the elaborated env returned by
     `infer_program_env_alpha_elab`; `type_forall_fn_value_pass_and_call.facet`
     passes. Checks: `make EnvRuntimeCapturedSafety.vo`,
     `make End2EndSafety.vo`, `dune build`, touched-file proof-hole scan.
   - Done: elaborate `let f = id in f<T>(...)` to checked direct generic
     calls when `f` is not used in args; pure annotated/bound local cases pass.
     Checks: `make TypeChecker.vo`, `make End2EndSafety.vo`, `dune build`,
     proof-hole scan, three pure targeted CLI tests.
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
