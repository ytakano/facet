# Refactoring Roadmap: Renaming and Alpha Relations

## Current status

Completed and committed:

- Removed stale `--debug-alpha` documentation.
- Split general expression-size facts into `ExprFacts.v`.
- Split core alpha-renaming facts into focused modules:
  `AlphaCore.v`, `AlphaCtx.v`, `AlphaPlace.v`, `AlphaExpr.v`, and
  `AlphaFn.v`.
- Kept `AlphaRenaming.v` as the compatibility aggregator.
- Renamed the conservative expression name collector to `expr_names`, with
  `free_vars_expr` retained as a compatibility alias.
- Moved lookup, context-operation, and typed-place alpha facts out of the
  aggregator.

Deferred by request:

- Phase 2, the OCaml CLI program-level acceptance gate, is intentionally not
  part of the current work.

Current caveat:

- `expr_alpha` is still too weak for compound expressions. `EStruct` does not
  require field expressions to be alpha-related, and `EMatch` does not yet
  specify how branch binders extend the rename environment.

## Next task: strengthen `EStruct` alpha

Do this before touching match branches, because struct fields have no binder
scoping issue.

Targets:

- `rocq/theories/TypeSystem/AlphaExpr.v`
- `rocq/theories/TypeSystem/AlphaRenaming.v`

Implementation steps:

1. Add a structural `fields_alpha` relation in `AlphaExpr.v`.
2. Change the `EA_Struct` constructor to require `fields_alpha ρ fields fieldsr`.
3. Add or update helper lemmas in `AlphaRenaming.v` so
   `alpha_rename_expr_sound` constructs `fields_alpha` for `EStruct`.
4. Keep `alpha_rename_expr` output unchanged.
5. Run:

   ```sh
   cd rocq && make
   rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
   ```

Commit when this task passes.

## Later task: specify `EMatch` branch alpha

Do not implement this until the branch-binder relation is explicit.

Open design point:

- Each branch has `(variant, binders, body)`.
- The branch body must be related under an environment extended from original
  binders to renamed binders.
- The plan must decide whether `branches_alpha` mirrors executable
  `alpha_rename_idents` and its `used` state, or stays as a pure relation over
  binder lists and bodies.

Expected shape after the design is fixed:

```coq
Inductive branches_alpha : rename_env ->
    list (string * list ident * expr) ->
    list (string * list ident * expr) -> Prop := ...
```

Acceptance criteria for the later task:

- `EA_Match` requires `expr_alpha` for the scrutinee.
- `EA_Match` requires `branches_alpha` for branches.
- `alpha_rename_expr_sound` proves the match case without weakening the
  relation.
- `cd rocq && make` passes with no `Axiom`, `Admitted.`, or `Abort.` in
  `rocq/theories`.

## Cleanup task: traversal helpers

After `EStruct` and `EMatch` are both strengthened, consider extracting shared
accumulator traversals from `alpha_rename_expr` and its proofs.

Possible helpers:

- `alpha_rename_exprs`
- `alpha_rename_fields`
- `alpha_rename_payloads`
- `alpha_rename_branches`

Constraints:

- Preserve `alpha_rename_expr` output exactly.
- Keep helper definitions unfold-friendly for Rocq proofs.
- Regenerate extracted OCaml only through `cd rocq && make`; never edit
  `fixtures/TypeChecker.ml` or `.mli` manually.
