# let rec Roadmap

## Status

In progress.

Done:

- Roadmap captured in this file.
- Baseline tests lock current top-level recursive function values.
- `rec` and `and` are reserved words in the OCaml frontend.
- Parser and named AST accept local `let rec` groups, including shared explicit
  capture lists.
- Raw AST includes `RawLetRec`; raw elaboration supports non-capturing
  groups and explicit-capture groups using synthetic function definitions.
- OCaml raw lowering keeps recursive function names separate from ordinary
  value scope and emits direct raw references/calls to local-rec ids.
- Rocq raw elaboration accepts non-capturing local rec groups and lowers them
  into synthetic no-capture function definitions plus direct calls.
- Local-rec raw lowering now emits reserved `__facet_local_rec_*` synthetic
  function names and rejects user top-level `__facet_*` names.
- Explicit-capture local rec groups lower rec references to closure values and
  reuse existing closure capture checking for non-recursive captured calls.
- FIR regression coverage locks synthetic local-rec function emission, direct
  calls, and captured closure construction/calls.

Next:

- Design and prove the direct-call store-safe sidecar for recursive call
  graphs before enabling actual self-recursive or mutually recursive direct
  calls. They currently type-check far enough to reach
  `ErrEndToEndSafetyGateFailed`, because the store-safe sidecar only accepts
  direct calls whose callee body is already narrow-store-safe. A simple
  fuel-unfolding extension is not enough for true cycles: it can cover finite
  forward direct-call chains, but self/mutual cycles bottom out at fuel 0 and
  also make the current proof search too expensive.
- After that proof design lands, extend local-rec semantics from direct calls
  in the `in` expression to same-group direct calls and actual recursive calls.

This roadmap adds local recursion in stages, ending with a safe v1 for
explicit-capture recursive closures. The first implementation should avoid a
new core `ELetRec` expression. Surface `let rec` should be lowered through raw
elaboration into synthetic `fn_def`s plus the existing callable forms:

- `EFn` / `ECall` for non-capturing recursive functions.
- `EMakeClosure` / `ECallExpr` for explicit-capture recursive closures.

The Rocq definitions and extracted checker remain the source of truth. The
OCaml parser and de Bruijn conversion may represent the surface syntax, but
must not duplicate type-checking logic or add fallback acceptance paths.

## Surface Syntax

Use an `fn`-like local group syntax:

```facet
let rec f(x: T) -> R {
  body
}
and g(x: T) -> R {
  body
}
in expr
```

For captured recursive closures, use one explicit capture list shared by the
whole group:

```facet
let rec [c1, c2]
  f(x: T) -> R {
    body
  }
and
  g(x: T) -> R {
    body
  }
in expr
```

V1 restrictions:

- Each recursive item is a function with explicit parameter and return types.
- Recursive non-function values are rejected.
- Local-rec generics and `where` clauses are rejected.
- Per-function capture lists are rejected; the group has one capture list.
- Captures are explicit. A rec body may not use an outer local variable unless
  it appears in the group capture list.
- Captured-rec v1 supports only the current safe closure capture discipline:
  immutable, unconsumed, unrestricted captures that are ref-free, or shared
  references whose lifetimes outlive the closure environment.
- Mutable captures, unique-reference captures, affine captures, linear
  captures, borrow-capture syntax, mutable environment write-back, and
  consuming closure calls are future work.

## Semantics

Top-level function self-recursion and mutual recursion are intended behavior.
Global raw elaboration already installs function stubs before checking bodies;
tests should lock this down before local `let rec` is added.

For a local non-capturing rec group:

- Allocate a fresh synthetic `fn_def` name for each local rec function.
- Type-check every body in an environment containing stubs for all synthetic
  functions in the group.
- Inside the group body and the `in` expression, references to rec names lower
  to `EFn synthetic`; calls lower to `ECall synthetic args`.
- The generated function values have ordinary unrestricted `fn(...) -> ...`
  types.
- Local value bindings and parameters shadow rec function names in the normal
  lexical order.
- The synthetic names are lexical implementation details and are not
  source-callable outside the `let rec` expression.

For an explicit-capture recursive closure group:

- Use `closure_elab_capture_params` to compute the shared `fn_captures` for
  each synthetic function.
- Type-check each synthetic body under `params_ctx (captures ++ params)`, as
  current closure elaboration does.
- Inside the group body and the `in` expression, references to rec names lower
  to `EMakeClosure synthetic captures`; calls lower to
  `ECallExpr (EMakeClosure synthetic captures) args`.
- Recursive calls rebuild closure values from the current captured frame rather
  than constructing cyclic runtime closure values.
- Runtime behavior reuses existing captured-call semantics:
  `copy_capture_store_as`, hidden captured frames, argument binding, callee
  alpha-renaming, and cleanup via `store_remove_params`.

## Implementation Steps

1. Baseline tests and direct-call gate.
   - Done: add valid tests for top-level recursive function values.
   - Next: add valid tests for direct top-level self-recursion and mutual
     recursion, then extend the store-safe sidecar so those no-capture direct
     calls pass the extracted end-to-end checker.
   - Keep direct top-level recursion no-capture only.

2. Parser and named AST.
   - Done: reserve `rec` and `and` in the lexer/parser token set.
   - Done: add a named AST node for local recursive groups with optional shared
     capture list, function names, params, returns, and bodies.
   - Done: update grammar printing to include both non-capturing and capturing
     forms.
   - Done: parser validation remains syntactic; semantic checks stay in
     de Bruijn validation, raw elaboration, and the extracted checker.

3. Name resolution and raw AST.
   - Done: add raw `RawLetRec captures rec_fns body` and lower parsed groups
     to it.
   - Done: de Bruijn conversion assigns stable source idents to rec function
     names and rejects duplicate names in the group.
   - Maintain a local rec-name environment separate from ordinary value scope
     so that calls can lower differently from normal variables.
   - When an ordinary local binding or parameter shadows a rec name, resolve to
     the ordinary value first.
   - Done: make OCaml raw lowering distinguish recursive function names from
     ordinary values.
   - Done: implement raw elaboration for non-capturing rec groups.
   - Done: make generated local-rec function names collision-proof against
     user top-level names and sibling/nested local rec groups.
   - Next: enable recursive bodies after the direct-call safety gate accepts
     recursion.
   - For non-capturing groups, lower rec references to direct function items.
     For captured groups, lower rec references to closure construction using
     the shared capture ids.

4. Rocq raw elaboration.
   - Done: `CheckerRawElab.v` has `RawLetRec` and allocates all synthetic
     names before checking any body.
   - Done: group stubs are appended before body elaboration so the group is
     in scope while each rec body is elaborated.
   - Done: `[]` captures create no-capture `MkFnDef` entries and use the
     existing full-env path.
   - Done: non-empty captures reuse closure capture checking and create one
     captured synthetic `fn_def` per rec function.
   - Done: the `in` expression elaborates with completed synthetic functions
     available and returns the synthetic functions as extras.

5. Checker, typing, borrow, and safety alignment.
   - Prefer reusing existing `EFn`, `ECall`, `EMakeClosure`, and `ECallExpr`
     typing/checker rules. Do not add a new core typing rule unless raw
     elaboration proves insufficient.
   - Done: non-recursive local-rec call sites reuse the existing extracted
     checker authority; no OCaml fallback checker was added.
   - Next: replace the current acyclic direct-call store-safe sidecar with a
     verified recursive-call graph summary, or another proof structure that can
     justify self/mutual direct-call cycles without depending on finite fuel
     unfolding of the same cycle. Split this proof work into three small
     commits: boolean checker summary for no-capture direct-call components,
     soundness from the boolean summary to the Prop summary, then the big-step
     safety theorem change that uses evaluation induction for direct calls.
   - Done: add the no-capture direct-call component boolean summary in
     `CheckerRootSidecars.v`; it is intentionally not connected to the
     end-to-end gate until the Prop soundness and safety theorem work lands.
   - Done: prove the boolean no-capture direct-call component summary sound
     against a matching Prop summary in `EnvRuntimeCapturedCallSummaryFacts.v`;
     it is still intentionally not wired into the gate.
   - Done: add the env-level ready lemma for that component summary, preparing
     the later gate connection without changing current accept/reject behavior.
   - Done: add local-bounds lifting for the no-capture direct-call component
     summary, matching the existing summary lifting style.
   - Next: derive the `direct_call_callee_body_root_evidence` bridge from the
     recursive direct-call component summaries, then use the existing direct-call
     route theorem instead of adding an ad hoc safety path.
   - The recursive-call proof must still route through the existing end-to-end
     program theorems:
     `infer_program_env_end2end_sound`,
     `check_program_env_end2end_sound`, and
     `infer_program_env_end2end_big_step_safe_checked_initial_ready`.
   - If any theorem must be narrowed or a proof gap is introduced, record that
     explicitly before claiming the feature complete.
   - Preserve existing closure safety invariants for captured frames, root
     provenance, alpha-renaming, and parameter cleanup.

6. FIR and diagnostics.
   - Render synthetic local-rec functions consistently with existing synthetic
     closure functions.
   - Keep diagnostic names mapped back to source rec names where practical.
   - Ensure generated synthetic names cannot collide with user-visible
     top-level names.

## Test Plan

Valid tests:

- Top-level self-recursion.
- Top-level mutual recursion.
- Basic non-capturing local rec group called from the `in` body.
- Local rec function used as a first-class `fn` value in the `in` body.
- Shadowing where a local binding hides a rec function name.
- Non-capturing local self-recursion.
- Non-capturing local mutual recursion.
- Same-group non-recursive forward direct call.
- Captured local rec closure with an immutable unrestricted capture, called
  from the `in` body.
- Captured recursive closure with an immutable unrestricted capture.
- Captured mutual recursive closures sharing one capture list.
- Captured same-group non-recursive forward direct call.
- Shadowing where a parameter hides a rec function name.

Invalid tests:

- Done: current top-level direct self/mutual recursion safety-gate failures,
  until the recursive direct-call proof lands and these move to valid tests.
- Done: duplicate function names in one rec group.
- Done: missing parameter or return annotation.
- Done: local-rec generic parameters or `where` clause.
- Done: rec body uses an outer local variable not listed in the capture list.
- Done: unknown capture name.
- Done: duplicate capture name.
- Done: mutable capture.
- Done: affine capture.
- Done: linear capture.
- Done: explicit type arguments on a local rec function value.
- Done: user-defined top-level names starting with reserved `__facet_`.
- Done: actual local recursive body calls remain rejected by the current
  end-to-end safety gate until the recursive direct-call proof lands.
- Recursive non-function binding is not representable in the v1 parser syntax.
- Unique-reference capture coverage remains under the closure test suite.

FIR tests:

- Done: non-capturing local rec emits synthetic functions and direct calls.
- Done: captured local rec emits synthetic captured functions and closure calls.

Required checks for implementation PRs:

- `cd rocq && make`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh` when FIR output changes

## Future Work

- Local-rec generics and local `where` clauses.
- Per-function capture lists.
- Borrow-capture syntax such as `closure [&x]` or `let rec [&x]`.
- Mutable recursive closures with environment write-back, corresponding to
  `FnMut`-like behavior.
- Affine and linear captured recursive closures with consuming calls,
  corresponding to `FnOnce`-like behavior.
- More precise diagnostics for synthetic local-rec functions.
