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
    - T2a2d1p done: add mapped type-argument `nth_error` helper;
      `Program.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1q done: add fuel-indexed type-argument obligation-refinement
      relation and map/nil/refl helpers; `EnvRuntimeRootCheckFacts.v`
      focused compile and proof-hole scan pass. Sub-agent spawn remains
      unavailable due thread limit.
    - T2a2d1r done: prove empty type-parameter substitution identity;
      `Program.v` focused compile and proof-hole scan pass. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d1s done: strengthen type-argument obligation refinement to
      cover substituted argument cores under any outer usage;
      `EnvRuntimeRootCheckFacts.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1t done: add mapped-pair type-argument refinement helper;
      `EnvRuntimeRootCheckFacts.v` focused compile and proof-hole scan pass.
      Broad generic obligation refinement needs a no-collapse invariant for
      struct field obligations because empty field obligation lists normalize
      to whole-path `[[]]`.
    - T2a2d1u done: add normalized linear-struct obligation refinement helper
      with explicit no-collapse premise; `EnvRuntimeRootCheckFacts.v` focused
      compile and proof-hole scan pass. Sub-agent spawn remains unavailable due
      thread limit.
    - T2a2d1v done: add empty-reflection helpers for normalized struct-field
      obligation lists; `EnvRuntimeRootCheckFacts.v` focused compile and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d1w done: broad obligation refinement from generic to substituted
      bodies is false: a linear `TParam` field instantiated with unrestricted
      type changes field obligation `[f]` to normalized whole obligation `[[]]`.
      Use typing/eval substitution transport instead of forcing this theorem.
    - T2a2d1x done: add mapped expression type-substitution `nth_error`
      helper; `Program.v` focused compile and proof-hole scan pass. Sub-agent
      spawn remains unavailable due thread limit.
    - T2a2d1y done: add empty-substitution identity lemmas for type and
      parameter lists; `Program.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1z done: add empty-substitution identity lemmas for expressions;
      `Program.v` focused compile and proof-hole scan pass. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d1aa done: add empty-substitution identity lemmas for parameter
      and typing contexts; `TypingRules.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1ab done: add composition lemmas for parameter and typing-context
      type substitution; `TypingRules.v` focused compile and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1ac done: add lifetime-substitution usage/core helper lemmas;
      `Types.v` focused compile and proof-hole scan pass. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d1ad done: add mapped lifetime-substitution `nth_error` helper;
      `Types.v` focused compile and proof-hole scan pass. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d1ae done: prove lifetime/type-parameter substitution
      commutation for types; `Program.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1af done: prove lifetime/type-parameter substitution
      commutation for params; `TypingRules.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1ag done: add structural lifetime substitution for typing
      contexts and prove type-parameter commutation; `TypingRules.v` make
      target and proof-hole scan pass. Sub-agent spawn remains unavailable
      due thread limit.
    - T2a2d1ah done: prove `apply_lt_ctx` lookup transport for type,
      state, and mutability queries; `TypingRules.v` make target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d1ai done: prove lifetime substitution transport for
      parameter-to-context conversion; `TypingRules.v` make target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d1aj done: prove `apply_lt_ctx` transport for
      `ctx_add_params`/`sctx_add_params`; `EnvStructuralRules.v` make target
      and proof-hole scan pass. Sub-agent spawn remains unavailable due
      thread limit.
    - T2a2d1ak done: full `cd rocq && make` and proof-hole scan pass
      after substitution-transport helper chain.
    - T2a2d1al done: add lifetime-first generic direct-call roots wrapper;
      `TypeSafetyDirectCallWrappers.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d1am done: add lifetime-first generic direct-call shadow-safe
      wrapper; `TypeSafetyDirectCallWrappers.v` make target and proof-hole
      scan pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2a done: add generic direct-call target recognizer;
      `TypeChecker.v` make target and proof-hole scan pass. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d2b done: add Prop-level generic direct-narrow captured-call
      summary; `EnvRuntimeBaseSafety.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2c done: include generic direct-narrow summary in captured-call
      store-safe aggregate; `EnvRuntimeBaseSafety.v` make target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2d done: wire generic direct-narrow captured-call checker
      branch and prove soundness; `EnvRuntimeBaseSafety.v`, proof-hole scan,
      and `dune build` pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2e done: add valid regression for generic direct call with
      variable argument; targeted CLI passes, full `tests/run.sh` still has
      existing generic/function-value safety-gate failures. Sub-agent spawn
      remains unavailable due thread limit.
    - T2a2d2f done: isolate remaining literal generic direct-call gap to
      missing generic direct-call runtime package; `preservation_ready_expr`
      has no call constructors, so a narrow leaf alone is insufficient.
    - T2a2d2g done: prove `params_alpha` transport through type-parameter
      substitution; `AlphaEnvStructural.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2h done: prove generic alpha-renamed call-bind parameter
      premises; `TypeSafetyCallFrameParams.v` make target and proof-hole scan
      pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2i done: package generic direct-call argument bind readiness;
      `TypeSafetyDirectCallWrappers.v` make target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2j done: prove type-parameter substitution leaves initial
      parameter root environments unchanged; `RootProvenance.v` make target
      and proof-hole scan pass. Sub-agent spawn remains unavailable due
      thread limit.
    - T2a2d2k done: prove lifetime substitution leaves initial parameter
      root environments unchanged; `RootProvenance.v` make target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2l done: make `Eval_CallGeneric` bind instantiated parameters;
      `OperationalSemantics.v`, `TypeChecker.v`, `TypeSafetyDirectCallWrappers.v`
      targets and proof-hole scan pass. Sub-agent spawn remains unavailable
      due thread limit.
    - T2a2d2m done: add root-env/call-param identities for type/lifetime
      instantiated params; `TypeSafetyCallFrameRootEnv.v` target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2n done: package instantiated generic argument frame typing,
      naming, and closure-target facts; `EnvRuntimeBaseSafety.v` target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2o done: add `store_remove_params` identities for type/lifetime
      instantiated params; `OperationalSemantics.v` target and proof-hole scan
      pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2p done: strengthen generic argument-frame package with
      roots/shadow/coverage/scope facts; `EnvRuntimeBaseSafety.v` target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2q done: add runtime-accurate generic argument frame package for
      type-instantiated params; `EnvRuntimeBaseSafety.v` target and proof-hole
      scan pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2r done: make generic-call runtime evaluate the type-substituted
      body while binding type-instantiated params; `OperationalSemantics.v` and
      `TypeSafetyDirectCallWrappers.v` targets plus proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2s done: prove type substitution preserves expression-local store
      names; `RootProvenance.v` target and proof-hole scan pass. Sub-agent
      spawn remains unavailable due thread limit.
    - T2a2d2t done: prove type substitution preserves store-safe function
      value call arguments; `EnvRuntimeBaseSafety.v` target and proof-hole
      scan pass. Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2u done: prove inverse store-safe argument transport from
      type-substituted arguments; `EnvRuntimeBaseSafety.v` target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2v done: prove tail freshness transport for type-substituted
      expressions; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2w done: prove reverse tail freshness transport from
      type-substituted expressions; `EnvRuntimeBaseSafety.v` target and
      proof-hole scan pass. Sub-agent spawn remains unavailable due thread
      limit.
    - T2a2d2x done: add narrow-summary tail-frame helper for substituted
      expressions; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      Sub-agent spawn remains unavailable due thread limit.
    - T2a2d2y blocked: generic direct-call runtime theorem needs
      type-parameter substitution transport for `typed_env_roots_shadow_safe`
      and `expr_root_shadow_store_safe_narrow_summary`; no existing support
      lemma covers substituted function bodies. Sub-agent delegation succeeded
      but returned no patch after identifying the same proof-transport gap.
    - T2a2d2z done: prove narrow-summary return values carry
      closure-target summaries without restricting generic type arguments;
      `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
    - T2a2d2aa done: add type-substitution lookup helpers for state
      contexts and parameter freshness checks; `EnvStructuralRules.v` target
      and proof-hole scan pass.
    - T2a2d2ab done: add consumed-binding `sctx_check_ok` and mutability
      lookup helpers for type-substituted contexts; `EnvStructuralRules.v`
      target and proof-hole scan pass. Sub-agent worker implemented this slice.
    - T2a2d2ac done: add `PVar` place and shadow-safe `EVar`
      type-substitution transport; `EnvStructuralRules.v` and `AlphaRoots.v`
      targets pass.
    - T2a2d2ad done: prove substituted `EVar` narrow runtime leaf;
      `EnvRuntimeBaseSafety.v` target passes.
    - T2a2d2ae blocked locally: unconditional `ty_compatible_b` transport
      through type substitution is false for `TForall`/`LBound`; do not use it.
    - T2a2d2af done: add substituted `EUnit`/literal shadow-safe
      transports and runtime leaves; `AlphaRoots.v` and
      `EnvRuntimeBaseSafety.v` targets pass.
    - T2a2d2ag blocked locally: unconditional place type-substitution
      transport is insufficient for field places because struct field
      instantiation needs `compose_type_params`; do not narrow to `PVar`.
    - T2a2d2ah done: add bounded type-parameter support and
      arity/boundedness-premised field-place type-substitution transports;
      `EnvStructuralRules.v` target passes without narrowing accepted generic
      programs. Sub-agent patch was fixed locally before commit.
    - T2a2d2ai blocked: bounded field-place transports are correct but
      their arity/boundedness premises are not derivable from current
      checker/typing evidence because field-place inference does not check
      struct type-arg length; do not add that guard or narrow acceptance.
    - T2a2d2aj in progress: prove the generic branch by an operational
      runtime argument that preserves current fallback semantics for
      under-applied struct type arguments, instead of using general place
      type-substitution transport.
      - T2a2d2aj1 done: align `TStruct`/`TEnum` type-parameter
        substitution with compose fallback semantics; `Program.v` target and
        proof-hole scan pass.
      - T2a2d2aj2 done: repair field-place substitution transports for
        compose fallback semantics; `EnvStructuralRules.v` target and
        proof-hole scan pass.
      - T2a2d2aj3 done: repair lifetime-equivalence transport for
        fallback-aware type-parameter substitution; `RuntimeTyping.v` target
        and proof-hole scan pass.
      - T2a2d2aj4 done: verify fallback-semantics fallout through
        `EnvRuntimeBaseSafety.v`; target and proof-hole scan pass.
      - T2a2d2ak done: add safe place/borrow/drop/typed-args
        type-substitution transports without generic compatibility widening;
        `AlphaRoots.v` target and proof-hole scan pass.
      - T2a2d2al done: verify new substitution transports through
        `EnvRuntimeBaseSafety.v`; target and proof-hole scan pass.
      - T2a2d2am done: captured generic branch skeleton type-checks up
        to the missing `eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named`;
        keep branch unwired until that base theorem is proved.
      - T2a2d2an blocked: proving that theorem by substituted-body
        narrow-summary transport reintroduces false general `ty_compatible_b`
        substitution for `ELet`/`EAssign`; do not narrow accepted generic
        programs or add closed-type-argument guards.
      - T2a2d2ao done: generic direct-call gate checks the runtime-instantiated
        callee body/context/return; `TypeChecker.v` target and proof-hole
        scan pass, extraction fixtures updated.
      - T2a2d2ap done: generic direct-call summary/soundness carries the
        instantiated callee body/context/return; `EnvRuntimeBaseSafety.v`
        target and proof-hole scan pass; sub-agent spawn unavailable.
      - T2a2d2aq done: added subst-type-param name/ctx-alpha helper
        transports for the generic runtime bridge; `EnvRuntimeBaseSafety.v`
        target and proof-hole scan pass; sub-agent closed.
      - T2a2d2ar done: proved alpha-renaming commutes with type-argument
        substitution for expressions; `EnvRuntimeBaseSafety.v` target and
        proof-hole scan pass.
      - T2a2d2as1 done: added root/exclusion and function-level
        type-argument substitution helpers for the instantiated generic
        summary bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2as2 done: bridged instantiated generic callee summaries
        through the type-substituted direct-call summary path;
        `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2z done: proved generic direct-call runtime value
        theorem for instantiated bodies and apply-type-param bind/remove;
        `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2aa done: wired captured generic direct-call store-safe
        branch into the final captured safety theorem;
        `EnvRuntimeCapturedSafety.v` target and proof-hole scan pass.
      - T2a2d2ab1 done: widened generic direct-call gate for
        unit/literal args and caller local bounds; `EnvRuntimeBaseSafety.v`,
        `dune build`, proof-hole scan, and top-level generic CLI checks pass;
        nested instantiated generic callee summaries remain.
      - T2a2d2ab2 done: add fuel-indexed nested generic instantiated summary checker/soundness; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass; sub-agent closed after local completion.
      - T2a2d2ab3a done: add fuel-summary local-bounds transport; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3b done: add fuel-summary expression/generic case splitter; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3c done: add generic direct-call body cleanup helper; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3d done: add zero-fuel instantiated summary expression bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3e done: factor expression-only generic direct-call value theorem for fuel wrapper reuse; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3f done: add generic direct-call runtime package record hook; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3g done: add zero-fuel generic direct-call value bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3h done: add expression generic direct-call runtime package theorem; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3i blocked: recursive fuel generic-direct bridge needs a dedicated outer frame-scope/cleanup invariant for `ECallGeneric`; do not narrow accepted generic calls or route through general provenance preservation.
      - T2a2d2ab3j done: expose expression generic direct-call exact final args-store package; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k done: add alpha/type-parameter runtime target helper for generic direct calls; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k2 done: add runtime eval transport for alpha/type-parameter generic direct-call target; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k3 done: add generic call typed-args inversion helper; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k4 done: factor safe generic-call argument runtime package; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k5 done: add zero-fuel generic-call exact package bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k6 done: add alpha-renamed generic-call runtime typed-args transport; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k7 done: add generic-call runtime typed-args call-frame bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass; sub-agent closed.
      - T2a2d2ab3k8a done: expose nested callee capture/outlives evidence from the generic-call runtime typed-args frame bridge; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.
      - T2a2d2ab3k8b done: expose alpha-renamed generic-call runtime typing for call-frame instantiation; `EnvRuntimeBaseSafety.v` target and proof-hole scan pass.

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
