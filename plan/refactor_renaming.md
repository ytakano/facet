# Refactoring Roadmap: AlphaRenaming Aggregator Completion

## Current status

Completed and committed:

- Removed stale `--debug-alpha` documentation.
- Split expression-size facts into `ExprFacts.v`.
- Split core alpha-renaming facts into focused modules:
  `AlphaCore.v`, `AlphaCtx.v`, `AlphaPlace.v`, `AlphaExpr.v`, and
  `AlphaFn.v`.
- Renamed the conservative expression name collector to `expr_names`, with
  `free_vars_expr` retained as a compatibility alias.
- Strengthened `expr_alpha` for `EStruct` with `fields_alpha`.
- Strengthened `expr_alpha` for `EMatch` with `binders_alpha` and
  `branches_alpha`.
- Added unfold-friendly traversal helpers in `Renaming.v`:
  `alpha_rename_exprs`, `alpha_rename_fields`, `alpha_rename_payloads`, and
  `alpha_rename_branches`.
- Moved lookup, context-operation, and typed-place alpha facts out of the
  aggregator.

Deferred by request:

- Phase 2, the OCaml CLI program-level acceptance gate, is intentionally not
  part of the current work.

Current caveat:

- `AlphaRenaming.v` is still not a pure compatibility aggregator. It still
  contains schemes, relations, definitions, theorems, and many proof blocks.
  The target state is for `AlphaRenaming.v` to contain only `Require Export`
  lines for the focused alpha modules.

## Next task: move expression-renaming soundness

Move expression-level executable-renamer soundness out of `AlphaRenaming.v`.

Targets:

- `rocq/theories/TypeSystem/AlphaExpr.v`
- `rocq/theories/TypeSystem/AlphaRenaming.v`

Move these groups together:

- `alpha_rename_call_args_sound`
- `alpha_rename_struct_fields_sound`
- `alpha_rename_idents_binders_alpha`
- `alpha_rename_idents_range`
- `alpha_rename_idents_branch_body_disjoint`
- `alpha_rename_match_branches_sound`
- `alpha_rename_expr_sound`

Constraints:

- Do not change theorem statements.
- Do not change `alpha_rename_expr` output.
- Keep imports minimal in `AlphaExpr.v`; only add dependencies that these
  proofs actually need.
- `AlphaRenaming.v` must continue to `Require Export AlphaExpr`, so existing
  downstream imports remain valid.

Acceptance criteria:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

Commit when this task passes.

## Follow-up task: split typing and structural alpha proofs

Create focused modules for typed and structural preservation proof groups, then
move the corresponding blocks out of `AlphaRenaming.v`.

Proposed modules:

- `AlphaTyping.v`
- `AlphaEnvStructural.v`

Move these groups by dependency order, in separate commits:

1. `ctx_same_bindings` and typed same-binding/merge helpers needed by typing
   preservation.
2. `alpha_rename_typed_args_env_structural_forward` and
   `alpha_rename_typed_fields_env_structural_forward`.
3. `alpha_rename_typed_match_tail_env_structural_forward`.
4. `alpha_rename_typed_env_structural_forward` and related typed preservation
   wrappers.

Constraints:

- Prefer moving proof blocks without changing statements.
- Add the new modules to `rocq/_CoqProject` before `AlphaRenaming.v`.
- Re-export the new modules from `AlphaRenaming.v`.
- Do not make downstream files import the new modules directly in this phase.

Acceptance criteria for each commit:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Follow-up task: split roots, shadow, and provenance proofs

Move root/shadow/provenance alpha proof groups out of `AlphaRenaming.v` after
`AlphaTyping.v` and `AlphaEnvStructural.v` are stable.

Proposed modules:

- `AlphaRoots.v`
- `AlphaShadowProvenance.v`

Move these groups by dependency order, in separate commits:

1. root-env and root-set rename/equiv helpers.
2. `typed_env_roots_shadow_safe` and its mutual induction schemes.
3. shadow-safe instantiation and support lemmas.
4. captured-call, closure, and provenance-specific alpha preservation lemmas.
5. final alpha-renaming wrappers for functions and full syntax.

Constraints:

- Preserve theorem names and statements.
- Keep `AlphaRenaming.v` as the only compatibility import surface during the
  migration.
- If a proof group has hidden dependencies on previous sections, move the
  dependency first rather than duplicating helpers.

Acceptance criteria for each commit:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

## Final task: make `AlphaRenaming.v` a pure aggregator

After all proof groups are moved, reduce `AlphaRenaming.v` to exports only.

Target shape:

```coq
From Facet.TypeSystem Require Export
  ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn
  AlphaTyping AlphaEnvStructural AlphaRoots AlphaShadowProvenance.
```

Acceptance criteria:

- `AlphaRenaming.v` has no `Lemma`, `Theorem`, `Definition`, `Fixpoint`,
  `Inductive`, `Scheme`, or `Combined Scheme` declarations.
- Existing downstream files that import `AlphaRenaming` still compile.
- `cd rocq && make` passes.
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories` has no matches.
- `dune build` passes after the final Rocq build.

## General constraints

- Generated OCaml files under `fixtures/` must only be changed by
  `cd rocq && make`; never edit them manually.
- Keep commits small: one moved proof group or one new module per commit.
- Ignore the existing unstaged `plan/review.md` unless explicitly asked to edit
  it.
