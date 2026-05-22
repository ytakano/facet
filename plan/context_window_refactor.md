# Context Window Refactor Roadmap

## Summary

Current Rocq proof work is becoming infeasible because each continuation often
requires reloading large proof files, long theorem statements, and historical
roadmap context. The immediate goal is to make closure and captured-call proof
work continue within the context window by reducing the amount of code and proof
state an agent must read for each step.

Do not start with a broad checker split into Hindley-Milner, usage, and
reference checkers. That split may be useful later, but it is too coarse as an
immediate fix because usage, borrowing, root provenance, closure capture, and
runtime safety currently cross theorem boundaries.

## Current Bottlenecks

- Large files repeatedly enter context: `TypeChecker.v`,
  `TypeSafetyCapturedCall.v`, `TypeSafetyClosureRuntimeArgs.v`, and
  `EnvRuntimeSafety.v`.
- Large theorem statements return deeply nested conjunctions, forcing agents to
  reread destruct shapes and proof obligations.
- Root, capture, store, and shadow facts are spread across proof modules, so
  finding one bridge often requires opening unrelated preservation files.
- Roadmap files contain useful history, but active tasks need a smaller
  continuation surface: current target, known blocker, next lemma, and last
  passing checks.

## Roadmap

### Current Status

- Completed first proof-interface compression slice:
  `TypeSafetyCapturedCall.v` now uses existing mutual statement aliases for the
  repeated frame-scope, prefix-root, and param-scope preservation hypotheses in
  the captured-call bridge cores.
- Added compact rooted eval result package definitions in
  `TypeSafetyClosureRuntimeArgs.v` for future theorem-result rewiring.
- Completed second proof-interface deduplication slice:
  closure cleanup cores now use the shared mutual statement aliases, and
  `TypeSafetyDirectCallSetup.v` no longer duplicates those alias definitions.
- Added preservation package bridge definitions:
  roots-ready and typed-prefix roots-ready statements now have package forms and
  conversion lemmas, while the existing public statement aliases remain
  unchanged.
- Rewired runtime-args captured-call cores to consume the roots-ready package
  statement; public wrappers and captured-call bridge callers convert existing
  plain statements at the boundary.
- Rewired the first typed-prefix cleanup core:
  `eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core`
  now consumes the typed-prefix package statement directly, and its two callers
  convert plain statements at the boundary.
- Rewired the first captured body-context cleanup core:
  `eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the captured expression body-context cleanup core:
  `eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the captured body cleanup core:
  `eval_captured_call_body_cleanup_preserves_value_and_refs_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the captured expression cleanup core:
  `eval_captured_call_expr_cleanup_preserves_value_and_refs_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the captured params body cleanup core:
  `eval_captured_call_body_cleanup_preserves_value_and_refs_params_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the captured params expression cleanup core:
  `eval_captured_call_expr_cleanup_preserves_value_and_refs_params_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the captured params-erased body cleanup core:
  `eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the hidden-frame erased cleanup core:
  `eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the hidden-frame erased subset cleanup core:
  `eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the hidden cleanup package core:
  `eval_let_make_closure_captured_call_hidden_cleanup_package_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the make-closure cleanup core:
  `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core`
  now consumes the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the make-closure auto cleanup core:
  `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the instantiated captured-call bridge core:
  `eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the captured-call callee-components bridge core:
  `eval_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the let captured-call callee-components bridge core:
  `eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the direct-call body cleanup/provenance cores:
  `eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core`
  and `eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core`
  now consume the typed-prefix package statement directly, with plain callers
  converting at the boundary.
- Rewired the direct-call roots-ready route core:
  `eval_preserves_typing_direct_call_roots_ready_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the direct-call roots-provenance route core:
  `eval_preserves_typing_direct_call_roots_provenance_ready_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Rewired the direct-call callee-summary route core:
  `eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary_with_preservation_core`
  now consumes the typed-prefix package statement directly, with its plain
  wrapper converting at the boundary.
- Extracted the first capture fact module:
  `TypeSafetyCaptureFacts.v` now owns the reusable capture/root helper lemmas
  that were previously at the top of `TypeSafetyCapturedCall.v`.
- Extracted the captured-call evidence module:
  `TypeSafetyCapturedCallEvidence.v` now owns the reusable alpha-renaming and
  captured callee-body root-shadow provenance bridge lemmas.
- Extracted the closure runtime-args facts module:
  `TypeSafetyClosureRuntimeArgsFacts.v` now owns the helper lemma cluster from
  `bind_params_head_fresh_in_tail` through the make-closure captured-call
  frame params readiness bridge.
- Extracted the roots-ready package interface:
  `TypeSafetyRootedPackages.v` now owns the rooted result records, package
  statements, conversion lemmas, and readiness bridge used by runtime args.
- Last focused check:
  `cd rocq && make theories/TypeSystem/TypeSafetyRootedPackages.vo theories/TypeSystem/TypeSafetyClosureRuntimeArgs.vo theories/TypeSystem/TypeSafetyClosure.v`.
- Next task: continue Phase 3 by looking for the next stable helper cluster
  that can move out of a large preservation file without changing theorem
  statements.

### Phase 1: Compact Continuation Notes

- Keep `plan/type_safety_roadmap.md` focused on the active proof path.
- Move historical or completed detail into `plan/type_safety_roadmap_history.md`
  or another archive note when it is no longer needed for the next task.
- For each active proof task, record only:
  - target theorem or lemma;
  - exact blocker;
  - relevant helper lemmas;
  - last passing focused commands;
  - files that should not be edited.
- Avoid long proof transcripts, full error logs, and repeated explanations in
  planning files.

### Phase 2: Small Preservation Packages

- Replace recurring long nested conjunction results with small record/package
  types where the same evidence is passed repeatedly.
- Prioritize packages for closure and captured-call preservation evidence:
  final store typing, returned value typing, returned root bound, store root
  bound, store no-shadow, root-env no-shadow, and cleanup store equality.
- Keep compatibility wrappers for existing public theorem names while internal
  cores return the compact package.
- Do not weaken any safety property to make a package smaller; the package must
  expose the same facts or stronger facts.

### Phase 3: Narrow Root/Capture Fact Modules

- Move reusable root, capture, store-subset, and no-store bridge facts into
  narrow fact modules that can be imported without loading large preservation
  proofs.
- Prefer modules with stable ownership such as root-set facts, capture-store
  facts, and closure-cleanup facts.
- The next high-value bridge is the direct with-env captured-call subset fact:
  instantiated body return roots must be shown within
  `root_sets_union (arg_roots ++ capture_store_root_sets captured)`.
- Keep checker contracts unchanged until the supporting proof bridge compiles.

### Phase 4: Measured Proof File Splits

- Split a proof file only when a stable ownership boundary is already clear.
- Keep aggregators and wrapper modules so downstream imports continue to work.
- Do not combine theorem strengthening with file movement in the same commit.
- Before splitting, record the measured reason: file size, repeated import
  pressure, or a specific recurring context bottleneck.

### Phase 5: Checker Modularization Later

- Reconsider checker-level modularization only after proof APIs and fact modules
  are smaller.
- Base any checker split on the actual `_CoqProject` dependency graph and
  theorem dependencies, not only conceptual categories.
- If checker modularization proceeds, preserve Rocq as the source of truth and
  regenerate extracted OCaml through `cd rocq && make`.
- Do not duplicate type-checking logic in OCaml.

## Operating Rules

- Follow `plan/implementation.md` for context-efficient work.
- Search with `rg` before reading whole files.
- Read only the relevant symbol range first; keep `sed` ranges around 80 lines
  unless a larger range has a stated purpose.
- Summarize long build logs and proof errors instead of pasting them into the
  conversation or roadmap.
- Reuse previously established facts rather than rediscovering them.
- Use sub-agents only for implementation-only tasks with fixed statements,
  target files, constraints, and tests.
- Do not delegate invariant design, uncertainty reduction, checker contract
  changes, or repository-wide investigation.

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
