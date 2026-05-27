# Refactoring Roadmap: Renaming, Alpha, and Checker Entry Points

## Review assessment

`plan/review.md` is broadly accurate against the current tree. The main
findings are valid:

- `rocq/theories/TypeSystem` has no obvious `Axiom`, `Admitted.`, or `Abort.`
  holes.
- `AlphaRenaming.v` is a large dependency hub rather than a focused alpha
  renaming module.
- `expr_alpha` is too weak for `EStruct` and `EMatch`: it does not require
  field expressions, scrutinees, or branches to be alpha-related.
- `free_vars_expr` is a conservative name collector, not semantic free
  variables.
- The OCaml CLI acceptance path does not currently use the strongest
  program-level Rocq endpoint as the gate.
- Agent-facing docs mention `--debug-alpha`, but the CLI option parser does
  not implement it.

One caveat: line numbers in `plan/review.md` should be treated as
commit-specific evidence, not stable references. The roadmap below preserves
the review's conclusions but phrases work in terms of symbols and behavior.

## Phase 1: Fix documentation drift

Remove or implement stale `--debug-alpha` documentation. The default action is
to remove the documented command until the feature is actually implemented.

Targets:

- `CLAUDE.md`
- `.github/copilot-instructions.md`
- Any other docs found by searching for `debug-alpha`

Acceptance criteria:

- No docs advertise a CLI flag that `ocaml/main.ml` rejects.
- `dune exec ocaml/main.exe -- --generate-grammar` and normal file checking
  still work.

## Phase 2: Align CLI acceptance with the public checker endpoint

Make the OCaml CLI decide success using the program-level Rocq checker:

```ocaml
check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
```

Use per-function `infer_full_env_roots` only for diagnostics after the
program-level gate has decided acceptance. Do not accept a program through an
`ErrNotImplemented` fallback in the default path.

Targets:

- `ocaml/main.ml`
- Tests under `tests/valid`, `tests/invalid`, and `tests/fir` if acceptance
  changes expose gaps

Constraints:

- FIR emission must only run after the program-level gate succeeds.
- If an ordinary checker fallback remains, hide it behind an explicit unsafe
  diagnostic flag rather than using it for normal acceptance.
- Do not duplicate type-checking logic in OCaml.

Acceptance criteria:

- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

## Phase 3: Split `AlphaRenaming.v` without semantic changes

Break `AlphaRenaming.v` into focused modules while preserving existing import
behavior. This phase must be a compatibility refactor only.

Proposed modules:

```text
ExprFacts.v
AlphaCore.v
AlphaCtx.v
AlphaPlace.v
AlphaExpr.v
AlphaFn.v
AlphaTyping.v
AlphaEnvStructural.v
AlphaRoots.v
AlphaShadowProvenance.v
```

Keep `AlphaRenaming.v` as an aggregator:

```coq
From Facet.TypeSystem Require Export
  ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn
  AlphaTyping AlphaEnvStructural AlphaRoots AlphaShadowProvenance.
```

Targets:

- `rocq/theories/TypeSystem/AlphaRenaming.v`
- New modules listed above
- `rocq/_CoqProject`

Constraints:

- Do not change theorem, lemma, or definition statements.
- Do not require downstream files to change imports in this phase.
- Move proof blocks only as needed to make module dependencies explicit.

Acceptance criteria:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`

## Phase 4: Move general expression facts out of alpha-renaming

Move `expr_size` and its size-decrease lemmas to `ExprFacts.v`. These facts are
general structural facts about expressions and are already used by checker and
runtime soundness files.

Targets:

- `ExprFacts.v`
- Imports in files that use `expr_size` directly

Constraints:

- Keep lemma names and statements stable.
- Avoid making unrelated soundness files depend on the full alpha-renaming
  aggregator when they only need expression-size facts.

Acceptance criteria:

- `cd rocq && make`

## Phase 5: Strengthen `expr_alpha` for structs and matches

Introduce structural relations for fields and match branches, then strengthen
the `EStruct` and `EMatch` constructors of `expr_alpha`.

Required shape:

```coq
Inductive fields_alpha : rename_env ->
    list (string * expr) -> list (string * expr) -> Prop := ...

Inductive branches_alpha : rename_env ->
    list (string * list ident * expr) ->
    list (string * list ident * expr) -> Prop := ...
```

`EA_Struct` must require `fields_alpha`.

`EA_Match` must require:

- `expr_alpha` for the scrutinee
- `branches_alpha` for branches

Targets:

- `AlphaExpr.v`
- `AlphaTyping.v`
- `AlphaEnvStructural.v`
- Any proof files that destruct or construct `expr_alpha`

Constraints:

- Do not change `alpha_rename_expr` output.
- Prove `alpha_rename_expr_sound` through helper lemmas for fields and
  branches.
- Keep branch binder scoping explicit in the relation; do not use an
  over-permissive constructor to recover old behavior.

Acceptance criteria:

- `cd rocq && make`
- Add focused Rocq examples or lemmas showing unrelated struct fields and
  unrelated match scrutinees/branches are not accepted by the strengthened
  relation.

## Phase 6: Rename conservative name collection

Rename the current `free_vars_expr` implementation to a name that reflects its
actual behavior, such as `expr_names` or `expr_name_occurrences`.

Migration strategy:

```coq
Definition free_vars_expr := expr_names.
```

Keep the compatibility alias temporarily, then migrate call sites in small
batches.

Targets:

- `Renaming.v`
- Alpha-renaming proofs that use name-disjointness facts
- Runtime and type-safety files that currently refer to `free_vars_expr`

Constraints:

- Do not introduce a semantic free-variable function unless a proof needs it.
- If a semantic free-variable function is later needed, give it a distinct
  name such as `free_vars_expr_semantic`.
- Preserve current fresh-name behavior during the rename.

Acceptance criteria:

- `cd rocq && make`

## Phase 7: Deduplicate traversal helpers

Extract repeated list traversals from `alpha_rename_expr` and its proofs.

Add helpers such as:

```coq
Fixpoint map_accum {A B : Type}
    (f : list ident -> A -> B * list ident)
    (used : list ident)
    (xs : list A)
    : list B * list ident := ...
```

Then define focused helpers:

- `alpha_rename_exprs`
- `alpha_rename_fields`
- `alpha_rename_payloads`
- `alpha_rename_branches`

Targets:

- `Renaming.v`
- `AlphaExpr.v`

Constraints:

- Preserve `alpha_rename_expr` output exactly.
- Keep helper definitions unfold-friendly for existing Rocq proofs.
- Treat `EMatch` branches specially because binders extend the rename
  environment.

Acceptance criteria:

- `cd rocq && make`
- Extraction still succeeds as part of the Rocq build.

## Required checks before completion

For proof or checker changes:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

For CLI, parser, or frontend-visible behavior:

```sh
dune build
sh tests/run.sh
sh tests/fir/run.sh
```

Generated files under `fixtures/` must come from Rocq extraction, not manual
edits.

## Implementation order

Recommended order:

1. Fix stale `--debug-alpha` docs.
2. Align CLI acceptance with the program-level Rocq endpoint.
3. Split `AlphaRenaming.v` as a compatibility refactor.
4. Move `expr_size` and related lemmas into `ExprFacts.v`.
5. Strengthen `expr_alpha` for `EStruct` and `EMatch`.
6. Rename `free_vars_expr` to a conservative name-collection API.
7. Deduplicate alpha-renaming traversals.

Keep phases 2 and 3 in separate changes. CLI acceptance behavior and proof-file
module movement fail in different ways, and mixing them makes regressions hard
to diagnose.
