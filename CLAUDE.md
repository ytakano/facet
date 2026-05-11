# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Facet** is a Rocq (formerly Coq) formalization of a small programming language with a type system featuring **affine**, **linear**, and **unrestricted** usage qualifiers. The project proves type soundness—that the type checker agrees with the operational semantics regarding variable consumption.

Key concepts:
- **UUnrestricted**: can be used unlimited times (copy semantics)
- **UAffine**: used at most once (move on use, optional drop)
- **ULinear**: used exactly once (must consume or explicitly drop)
- **Usage subtyping order**: `unrestricted <: affine <: linear`

## Build and Development Commands

All Rocq commands run from the `rocq/` directory:

```bash
# Build all theories and extract OCaml
cd rocq && make

# Compile a single file (preserves Facet namespace)
cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeChecker.v

# Regenerate Makefile after editing _CoqProject
cd rocq && rocq makefile -f _CoqProject -o Makefile

# Check one file without full rebuild
cd rocq && rocq check -R theories Facet theories/TypeSystem/TypeChecker.v

# Print compiled object (verify no syntax errors)
rocq print TypeChecker
```

### Docker Development Environment

```bash
sh docker/build.sh       # build image
sh docker/up_docker.sh   # start container
sh docker/exec_zsh.sh    # attach shell
sh docker/down_docker.sh # stop container
sh docker/rebuild.sh     # rebuild from scratch
```

Run these commands from the repository root. The Docker environment has Rocq 9.1.1 pre-installed.

## Architecture

### Module Structure

All sources live in `rocq/theories/TypeSystem/` under namespace `Facet.TypeSystem`. Compilation order (defined in `rocq/_CoqProject`) is critical:

1. **Types.v** (42 lines) — Core type definitions
   - `usage`: ULinear, UAffine, UUnrestricted
   - `TypeCore`: TUnits, TIntegers, TFloats, TNamed, TFn, TRef
   - `Ty`: wrapper combining usage + TypeCore
   - Projections: `ty_usage`, `ty_core`

2. **Syntax.v** (69 lines) — Abstract syntax tree
   - `ident`: (string * nat) pair; identified by string name and de Bruijn-like index
   - `expr`: EUnit, ELit, EVar, ELet, ECall, EReplace, EDrop
   - `param`: parameter definition with mutability, name, type
   - `fn_def`: function definition (name, params, return type, body)

3. **OperationalSemantics.v** (169 lines) — Big-step evaluation
   - `value`: VUnit, VInt, VFloat
   - `store_entry`: tracks variable name, type, value, and `se_used` flag
   - `store`: list of entries (runtime variable state)
   - `eval fenv s e s' v`: expression e with functions fenv evaluates to v, transforming store s → s'
   - Key rules: Eval_Var_Copy (unrestricted), Eval_Var_Consume (linear/affine), Eval_Replace, Eval_Drop, Eval_Call
   - `eval_args`: left-to-right argument evaluation

4. **TypingRules.v** (190 lines) — Inductive typing judgements
   - `ctx_entry`: (variable, type, consumed flag)
   - `ctx`: list of ctx_entry
   - `typed fenv Γ e T`: Prop-level proof that expression e has type T under function environment and context Γ
   - Context helpers: ctx_lookup, ctx_consume, ctx_add, ctx_remove, ctx_is_ok
   - Defines usage constraints at typing level (parallel to OperationalSemantics constraints)

5. **TypeChecker.v** (416 lines) — Executable type inference + OCaml extraction
   - Decidable mirrors of TypingRules helpers with `_b` suffix (ctx_lookup_b, ctx_consume_b, etc.)
   - `infer_result`: structured error reporting (OK vs Err variants)
   - `infer_core`: main recursive inference function; handles alpha renaming to avoid capture
   - `infer`: top-level entry point
   - `infer_args`: separate copy for use in proofs (not the inline `go` helper)
   - **Extraction target**: generates `fixtures/TypeChecker.ml` and `fixtures/TypeChecker.mli`

6. **AlphaRenaming.v** (1381 lines) — Alpha-equivalence proofs
   - Proves that fresh variable renaming preserves typing and semantics
   - Lemmas about renaming contexts, expressions, and functions
   - Critical for soundness: type checker performs alpha renaming to avoid variable capture during inference

7. **CheckerSoundness.v** (327 lines) — Checker ↔ Typing correspondence
   - Proves `infer` is sound and complete: `infer fenv Γ e` returns `OK T` iff `typed fenv Γ e T`
   - Bridges decidable `_b` operations to Prop-level TypingRules definitions
   - Uses alpha renaming lemmas from AlphaRenaming.v

8. **CheckerUsageSoundness.v** (199 lines) — Usage soundness theorems
   - Proves typing respects usage constraints (linear variables are consumed exactly once)
   - Relates static TypingRules constraints to runtime OperationalSemantics behavior

### Key Design Patterns

**Parallel decidable/Prop implementations**: 
- `TypingRules.v` defines inductive rules (`typed`, `ctx_lookup`, etc.) at Prop level
- `TypeChecker.v` provides boolean mirrors (`_b` suffix) for computation
- `CheckerSoundness.v` proves they agree (e.g., lemmas like `ctx_lookup_b_eq`)

**Context threading**:
- Both `TypingRules` and `OperationalSemantics` thread context/store left-to-right through expressions
- `ELet` and `ECall` manage entry/exit and consumption tracking

**Alpha renaming in the type checker**:
- `infer_core` calls `alpha_rename_for_infer` to rename free variables before processing function bodies
- Prevents capture of type variables in nested scopes

**Out of scope**:
- `ELetInfer`, `TRef`, `TFn` type inference, mutability checking, borrowing/ownership

## Key Files and Their Roles

| File | Purpose |
|------|---------|
| `rocq/_CoqProject` | Declares library mapping (-R theories Facet) and compilation order |
| `rocq/Makefile` | Generated by `rocq makefile`; runs `rocq compile` on all files |
| `fixtures/TypeChecker.ml` | **Generated** OCaml extraction from TypeChecker.v; do not edit manually |
| `fixtures/TypeChecker.mli` | **Generated** OCaml interface; updated by make |
| `plan/first_step.md` | Design notes on the core type system and expected behavior |
| `plan/alpha_renaming_lemmnas.md` | Notes on alpha-renaming lemma reorganization |
| `plan/simple_lifetime_and_borowwing/` | Future design sketches (borrowing, lifetime not yet implemented) |
| `.github/copilot-instructions.md` | Full developer guidelines (mirrors much of this file) |

## Important Conventions

**Rocq imports**: Use `From Facet.TypeSystem Require Import ...` for local modules; standard `Stdlib` for Rocq library.

**Decidable naming**: Decidable (boolean) versions of context helpers use `_b` suffix:
- `ctx_lookup_b` ↔ `ctx_lookup`
- `ctx_consume_b` ↔ `ctx_consume`
- Correspondences proven in CheckerSoundness.v (e.g., `ctx_lookup_b_eq`)

**OCaml extraction**: Ends with:
```rocq
Extraction Language OCaml.
Extraction "../fixtures/TypeChecker.ml" infer.
```
Running `make` in `rocq/` regenerates fixtures automatically.

**Termination in type checker**: The `infer` function uses an inline `let fix go` for argument processing so Rocq's termination checker sees structural recursion clearly. A separate `infer_args` definition exists for theorem statements.

**Runtime vs. static**:
- `OperationalSemantics.store` with `se_used` flag: runtime consumption tracking
- `TypingRules.ctx` with `consumed` bool: static consumption tracking
- Both must agree (proven in CheckerUsageSoundness.v)

## Testing and Validation

**Primary test**: Successful Rocq compilation.
```bash
cd rocq && make
```

**Validation checklist**:
1. All `.v` files compile (no errors, no admitted theorems in core files)
2. `CheckerSoundness.v` compiles (proves checker correctness)
3. `CheckerUsageSoundness.v` compiles (proves usage constraints hold)
4. `fixtures/TypeChecker.ml` is regenerated and matches expected interface
5. No incomplete proofs (`Admitted`) in soundness files

**Common issues**:
- **Compilation fails after editing `_CoqProject`**: Regenerate Makefile: `cd rocq && rocq makefile -f _CoqProject -o Makefile`
- **Fixtures not updating**: Run `make clean && make` in `rocq/` to force full rebuild
- **Alpha-renaming lemmas not found**: Verify `AlphaRenaming.v` compiles before soundness proofs

## Commit Conventions

- Use short imperative subjects: `add docker files`, `prove affine values used at most once`
- Describe type-system or proof impact in the body
- List commands run (e.g., `cd rocq && make`)
- Call out regenerated artifacts: `fixtures/TypeChecker.ml`
- Link planning notes or design docs when relevant
