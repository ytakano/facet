# let rec Roadmap

## Status

In progress.

Done:

- Roadmap captured in this file.
- Baseline tests lock current top-level recursive function values.
- `rec` and `and` are reserved words in the OCaml frontend.
- Parser and named AST accept local `let rec` groups, including shared explicit
  capture lists, but conversion fails with `let rec is not implemented yet`.

Next:

- Make direct top-level self-recursive and mutually recursive calls pass the
  end-to-end safety gate. They currently type-check far enough to reach
  `ErrEndToEndSafetyGateFailed`, because the store-safe sidecar only accepts
  direct calls whose callee body is already narrow-store-safe.
- Add raw AST/de Bruijn lowering for local rec groups.

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
   - Done: conversion currently rejects the parsed node with
     `let rec is not implemented yet`; parser validation remains syntactic only.

3. Name resolution and raw AST.
   - Add a raw expression for recursive groups, for example
     `RawLetRec captures rec_fns body`.
   - In de Bruijn conversion, assign stable source idents to rec function names
     and reject duplicate names in the group.
   - Maintain a local rec-name environment separate from ordinary value scope
     so that calls can lower differently from normal variables.
   - When an ordinary local binding or parameter shadows a rec name, resolve to
     the ordinary value first.
   - For non-capturing groups, lower rec references to direct function items.
     For captured groups, lower rec references to closure construction using
     the shared capture ids.

4. Rocq raw elaboration.
   - Extend `CheckerRawElab.v` with the raw rec-group form and an elaboration
     helper that allocates all synthetic names before checking any body.
   - Build group stubs first, append them to the current environment, then
     elaborate every rec body with the full group available.
   - For `[]` captures, create `MkFnDef` entries with `fn_captures = []` and
     check them with the existing full-env path.
   - For non-empty captures, reuse the current `RawClosure` capture machinery
     and create one captured synthetic `fn_def` per rec function.
   - Elaborate the `in` expression with the completed synthetic functions
     available and return the synthetic functions as extras.

5. Checker, typing, borrow, and safety alignment.
   - Prefer reusing existing `EFn`, `ECall`, `EMakeClosure`, and `ECallExpr`
     typing/checker rules. Do not add a new core typing rule unless raw
     elaboration proves insufficient.
   - Ensure checker soundness still routes through the existing end-to-end
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
- Non-capturing local self-recursion.
- Non-capturing local mutual recursion.
- Local rec function used as a first-class `fn` value in the `in` body.
- Captured recursive closure with an immutable unrestricted capture.
- Captured mutual recursive closures sharing one capture list.
- Shadowing where a parameter or local binding hides a rec function name.

Invalid tests:

- Duplicate function names in one rec group.
- Recursive non-function binding.
- Missing parameter or return annotation.
- Local-rec generic parameters or `where` clause.
- Rec body uses an outer local variable not listed in the capture list.
- Unknown capture name.
- Duplicate capture name.
- Mutable capture.
- Unique-reference capture.
- Affine capture.
- Linear capture.
- Explicit type arguments on a local rec function value, unless a later
  generic-rec roadmap adds that feature.

FIR tests:

- Non-capturing local rec emits synthetic functions and direct calls.
- Captured local rec emits synthetic captured functions and closure values.

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
