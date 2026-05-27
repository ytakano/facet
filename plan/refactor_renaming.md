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

## Later task: strengthen `EMatch` branch alpha

Use a pure alpha relation for branch binders. Do not put the executable
renamer's `used` state, `binder_seed`, or `fresh_ident` behavior into the
relation. Those details belong in helper lemmas proving that
`alpha_rename_expr` produces the relation.

Design:

- Each branch has `(variant, binders, body)`.
- Variant names must match structurally.
- Binder lists must have the same length and order.
- The branch body is related under an environment extended from original
  binders to renamed binders.
- Freshness/capture avoidance should be expressed as a binder relation, not by
  threading `used` through `branches_alpha`.

Expected shape:

```coq
Inductive binders_alpha :
    rename_env -> list ident -> list ident -> rename_env -> Prop :=
  | BA_Nil : forall ρ,
      binders_alpha ρ [] [] ρ
  | BA_Cons : forall ρ x xr xs xsr ρ_branch,
      (* freshness condition for xr against the extended range *)
      binders_alpha ρ xs xsr ρ_branch ->
      binders_alpha ρ (x :: xs) (xr :: xsr) ((x, xr) :: ρ_branch).

Inductive branches_alpha : rename_env ->
    list (string * list ident * expr) ->
    list (string * list ident * expr) -> Prop :=
  | BrA_Nil : forall ρ,
      branches_alpha ρ [] []
  | BrA_Cons : forall ρ variant binders bindersr body bodyr rest restr ρ_branch,
      binders_alpha ρ binders bindersr ρ_branch ->
      expr_alpha ρ_branch body bodyr ->
      branches_alpha ρ rest restr ->
      branches_alpha ρ
        ((variant, binders, body) :: rest)
        ((variant, bindersr, bodyr) :: restr).
```

`EA_Match` should become:

```coq
| EA_Match : forall ρ scrut scrutr branches branchesr,
    expr_alpha ρ scrut scrutr ->
    branches_alpha ρ branches branchesr ->
    expr_alpha ρ
      (EMatch scrut branches)
      (EMatch scrutr branchesr)
```

Implementation steps:

1. Add `binders_alpha` and `branches_alpha` in `AlphaExpr.v`.
2. Add a helper lemma connecting `alpha_rename_idents` to `binders_alpha`.
3. Add a helper lemma connecting the match-branch traversal in
   `alpha_rename_expr` to `branches_alpha`.
4. Strengthen `EA_Match` and update `alpha_rename_expr_sound`.
5. Keep `alpha_rename_expr` output unchanged.

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
