# End-to-end safety roadmap

## Goal

CLI acceptance uses only the extracted Rocq `infer_program_env_end2end`
checker.  `ErrNotImplemented` is a rejection, never a fallback to another
checker.  Parser/de Bruijn correctness is outside this roadmap.

Required theorem names stay intact:

- `infer_program_env_end2end_sound`
- `check_program_env_end2end_sound`
- `infer_program_env_end2end_big_step_safe_checked_initial_ready`

## Status

| Task | Status |
|------|--------|
| T1: `ECallExpr` `TFn`/`TClosure` in roots checker | done |
| T2c: `TTypeForall` in roots checker | done |
| T2d: `TForall` in roots checker | done |
| T3: switch OCaml CLI to `infer_program_env_end2end` | done |
| T4: CI entrypoint enforcement | done |
| T2a: `ECallGeneric` safety gate | blocked: generic runtime instantiation |
| T2e/T2g/T2b: function-value and captured-call gates | done except generic/type-forall cases under T2a |
| T2f: deref/reborrow/ref-write roots coverage | in progress |

## Current baseline

Latest full `sh tests/run.sh` baseline (2026-06-01): 18 valid-test
failures; invalid tests pass.

- Generic/function-value gates remain `ErrEndToEndSafetyGateFailed`.
- Reborrow valid tests pass, including `nested_shared_reborrow.facet`.
- Generic/type-forall function cases remain under blocked T2a.

## Active T2f slices

1. Done: add concrete `place_resolved_roots` indirect none/self/one-hop facts.
2. Done: canonicalize singleton store-root resolution and prove same-length equivalence transport.
3. Done: prove no-shadow domain/length wrapper for resolved-root equivalence.
4. Done: prove resolved-root rename transport in Alpha/Shadow contexts under scoped collision invariants.
5. Done: add concrete instantiate facts for stable singleton store chains.
6. Done: add semantic singleton-result instantiate and resolved-root namedness
   helpers.
7. Done: add no-shadow equivalent transport for resolved singleton instantiate.
8. Done: prove non-shadow resolved-root rename transport without namedness.
9. Done: add store-name collision weakening/transport helpers for resolved
   root alpha support.
10. Done: add non-shadow resolved borrow/deref Prop rules and alpha
    support; keep shadow-safe rules out for now.
11. Blocked: resolved shadow-safe Prop rules need call-frame tail stability;
    appending outer roots can change `place_resolved_roots`.
12. Done: route indirect borrow and immediate deref-borrow roots through
   `place_resolved_roots` for singleton stores; keep raw-root fallback.
13. Done: route non-shadow `EAssign`/`EReplace` through resolved
    singleton `PDeref` roots; shadow-safe unchanged.
14. Done: invalid rejections preserved for linear refs, immutable writes,
    borrow conflicts, unresolved roots, and ambiguous roots.
15. Done: add stable depth-based resolved write target and route
    non-shadow indirect `EAssign`/`EReplace` through target root lookup.
16. Done: route shadow-safe resolved `EAssign`/`EReplace` through target root lookup; full Rocq/extraction and OCaml build pass.
17. Done: align resolved write Prop rules with checker-enforced target mutability.
18. Done: add direct resolved write runtime target helper.
19. Done: add one-hop indirect resolved write target helper.
20. Done: add explicit direct-parent shape for resolved writes.
21. Done: narrow resolved write checker and Prop rules to direct-parent shape.
22. Done: close direct-parent resolved assign/replace prefix branches.
23. Done: rebuild dependent safety chain and remove stale proof fallout.
24. Done: run extraction consumers and CLI regression checks.
25. Done: choose proof path and add generalized nested resolved-write shape.
26. Done: route resolved write rules and checker through generalized shape.
27. Done: prove mutable-chain tail transport for shadow-safe resolved writes.
28. Done: identify needed invariant: recursive resolved writes require
    writable deref prefixes, not mutable targets alone.
29. Done: re-narrow resolved write chain to the proven direct-parent fragment.
30. Done: verify full Rocq build, proof-hole scan, OCaml build, and targeted direct/nested CLI cases.
31. Done: add writable-prefix resolved write chain guard and checker soundness.
32. Done: prove reusable runtime target helpers and writable-chain tail transport.
33. Done: prove writable-prefix nested resolved write preservation branches.
34. Done: verify nested resolved write CLI regressions; annotations unnecessary because unannotated replace/assign now pass.
35. Done: isolate reborrow gate to missing narrow store-safe EBorrow leaf.
36. Done: route shadow-safe EBorrow through resolved singleton roots and prove checker soundness.
37. Done: add tail-stable resolved EBorrow invariant and checker soundness.
38. Done: prove direct EBorrow narrow-summary runtime package and gate.
39. Done: add unique direct-parent resolved EBorrow narrow-summary runtime package.
40. Done: add EUnit leaf to narrow summaries for reborrow tails.
41. Done: add literal assignment leaf needed by resolved reborrow CLI regressions.
42. Done: isolate remaining direct reborrow gate to auto-drop tail `EDrop (EPlace _)`/`EVar` leaves.
43. Done: add auto-drop tail narrow leaves for resolved reborrow regressions.
    - T43a done: non-function `EVar` narrow leaf; Rocq/extraction and OCaml build pass.
    - T43b done: direct `EDrop (EPlace _)` leaf; three direct reborrow valid cases pass.
44. Done: widen resolved unique `EBorrow` narrow leaf from direct-parent to writable-chain; Rocq/extraction and OCaml build pass.
45. Done: route resolved unique `EBorrow` roots to the writable target root for nested reborrows; Rocq/extraction, OCaml build, and reborrow CLI checks pass.
46. Blocked: pruning ref-free deref/borrow result roots needs a
    store-typing-aware roots-readiness theorem; current
    `eval_preserves_roots_ready_mutual` cannot prove empty roots for
    statically ref-free values in arbitrary stores.
47. In progress: typed rootless readiness path.
    - T47a done: add typed rooted eval statement and rootless value
      projection for capture-ref-free result types.
    - T47b blocked: checker root pruning reaches
      `TypeSafetyRootsReadyMutual.v`; rootless constructors require a
      typed roots-ready theorem, not the current untyped mutual theorem.
48. In progress: checked rootless end-to-end path.
    - T48a done: add checked roots relation and typed rootless
      roots-ready expression theorem.
    - T48b1 done: add checked shadow-safe inferencer wrapper
      that prunes capture-free result roots after conservative success.
    - T48b2 done: add checked let constructors for capture-free
      results without final root exclusion.
    - T48b3 done: add recursive checked let inferencer and
      shadow-safe soundness.
    - T48b4 done: route end-to-end inference through checked roots;
      remaining nested reborrow failure is the store-safe gate.
    - T48c1 done: add checked narrow store-safe summary relation
      and executable checked narrow checker wrapper.
    - T48c2 done: restrict checked narrow fallback to top-level
      unchecked inference failures; TypeChecker compiles.
    - T48c3 done: prove checked narrow store-safe checker
      soundness; EnvRuntimeBaseSafety compiles.
    - T48c4 done: prove checked narrow runtime package.
    - T48c5 done: route normal store-safe gate through checked narrow;
      EnvRuntimeCapturedSafety compiles.
    - T48c6 done: use checked function-level roots companion in the
      normal store-safe gate; EnvRuntimeCapturedSafety and dune build pass.
    - T48c7 done: prove direct `EDeref (EBorrow RShared p)` checked narrow
      leaf for capture-ref-free results; EnvRuntimeBaseSafety and dune build pass.
    - T48c8 done: prove typed `eval_place` target theorem and widen shared
      deref-borrow checked leaf to indirect places; full Rocq build passes.
    - T48c9a done: add/prove checked-let bound-expression path for
      capture-ref-free bound values with nonempty ordinary roots; full Rocq
      build and dune build pass.
    - T48c9b done: route ordinary-success `ELet`/`ELetInfer` through the
      recursive checked summary branch; full Rocq build, dune build, proof-hole
      scan, and reborrow CLI checks pass.
    - T48c10 done: remeasured baseline after reborrow fix: 18 valid
      failures, all generic/function-value gate failures under T2a.
    - T2a1 blocked: direct `ECallGeneric` store-safe summary needs a
      generic direct-call runtime theorem; existing direct-call wrappers require
      `fn_type_params fdef = 0`. Needed shape: from typed generic args,
      `Datatypes.length type_args = fn_type_params fdef`, instantiated callee
      body narrow summary, and `Eval_CallGeneric`, prove result value type and
      root/shadow/store preservation.
    - T2a2a done: prove generic direct-call roots typing bridge using
      `T_Call_Generic`; `TypeSafetyDirectCallWrappers.vo` and proof-hole scan pass.
    - T2a2b blocked: generic direct-call runtime/store bridge needs a
      parametric runtime typing theorem. Current runtime evaluates the
      unsubstituted body with `fn_params fcall`; caller arguments are typed at
      `apply_type_params type_args (fn_params fdef)`, and no sound lemma converts
      concrete argument values to unsubstituted `TParam` parameter types.
    - T2a2c done: choose static type-substitution transport. Do not change
      runtime semantics and do not make `value_has_type` accept arbitrary
      `TParam`; instead transport body typing/store-safe summaries to
      `apply_type_params type_args (fn_params fcall)` and substituted return.
    - T2a2d1 done: add expression/parameter type-substitution utilities;
      `Program.v` focused compile and proof-hole scan pass. Sub-agent spawn was
      unavailable because the agent thread limit was reached.
    - T2a2d1b done: add parameter-context type-substitution helpers;
      `TypingRules.v` focused compile and proof-hole scan pass.
    - T2a2d1c done: prove partial type-substitution overlay composition
      and struct/enum field-instantiation transport helpers; `Program.v` and
      `TypingRules.v` focused compiles plus proof-hole scan pass.
    - T2a2d1d done: add substituted-context lookup/mutability helpers;
      `TypingRules.v` focused compile and proof-hole scan pass.
    - T2a2d1e done: add substituted `sctx` add/remove/params/path and
      consume/restore transport helpers; `EnvStructuralRules.v` focused compile
      and proof-hole scan pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1f done: prove conditional non-function type-substitution helper;
      `EnvRuntimeBaseSafety.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1g done: lift non-function type-substitution to parameters;
      `EnvRuntimeBaseSafety.v` focused compile and proof-hole scan pass.
    - T2a2d1h done: prove type substitution preserves outer usage;
      `Program.v` focused compile and proof-hole scan pass.
    - T2a2d1i done: add whole-path linear-obligation coverage helpers;
      `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1j done: add empty-obligation inversion and whole-path coverage
      helpers; `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1k done: add path-prefix transitivity and obligation-refinement
      helpers; `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1l done: add prefix and append closure for obligation refinement;
      `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1m done: add empty-list and whole-path base cases for obligation
      refinement; `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1n done: prove `TParam` linear-obligation substitution refinement;
      `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1o done: add struct-field obligation-list refinement helper;
      `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2 next: prove typing/root transport for substituted generic
      function bodies and narrow store-safe summaries.

Resolved writes accept direct-parent pathless writes and writable recursive
deref-chain prefixes. Resolved unique borrows accept writable recursive
deref-chain prefixes and return the resolved target root.

## Required checks

After each Rocq/extraction slice:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- targeted CLI tests for the changed construct

Before roadmap completion:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

## Acceptance criteria

- No OCaml fallback checker path accepts programs.
- No `Admitted`, `Axiom`, proof-hole, or weakened theorem is introduced.
- Generated OCaml fixtures are updated only by Rocq extraction.
- All T2f valid programs pass and matching invalid programs still reject.
