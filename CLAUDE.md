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

### Rocq (all commands run from `rocq/`)

```bash
# Build all theories and extract OCaml
cd rocq && make

# Compile a single file (preserves Facet namespace)
cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeChecker.v

# Regenerate Makefile after editing _CoqProject
cd rocq && rocq makefile -f _CoqProject -o Makefile

# Check one file without full rebuild
cd rocq && rocq check -R theories Facet theories/TypeSystem/TypeChecker.v
```

### OCaml (run from repo root)

```bash
# Build the OCaml frontend (requires Rocq make to have run first)
dune build

# Type-check a .facet source file
dune exec ocaml/main.exe -- path/to/file.facet

# Emit Flat IR alongside type checking
dune exec ocaml/main.exe -- --emit-fir output.fir path/to/file.facet

# Print the language grammar
dune exec ocaml/main.exe -- --generate-grammar

# Differential-test alpha-renaming path against direct path
dune exec ocaml/main.exe -- --debug-alpha path/to/file.facet

# Run all .facet tests (expect exit 0 for valid/, exit 1 for invalid/)
for f in tests/valid/**/*.facet; do dune exec ocaml/main.exe -- "$f" || echo "FAIL: $f"; done
for f in tests/invalid/**/*.facet; do dune exec ocaml/main.exe -- "$f" && echo "FAIL (expected error): $f"; done
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

The project has two distinct build pipelines that must run in order: Rocq `make` first (produces `fixtures/TypeChecker.ml`), then `dune build` (compiles the OCaml frontend against that extracted code).

### Rocq Module Structure

All sources live in `rocq/theories/TypeSystem/` under namespace `Facet.TypeSystem`. Compilation order (defined in `rocq/_CoqProject`) is critical:

1. **Types.v** — Core type definitions
   - `usage`: ULinear, UAffine, UUnrestricted
   - `TypeCore`: TUnits, TIntegers, TFloats, TBooleans, TNamed, TFn, TRef
   - `Ty`: wrapper combining usage + TypeCore
   - Projections: `ty_usage`, `ty_core`

2. **Syntax.v** — Abstract syntax tree
   - `ident`: (string * nat) pair; identified by string name and de Bruijn-like index
   - `expr`: EUnit, ELit, EVar, ELet, ELetInfer, ECall, EReplace, EDrop, EIf
   - `param`: parameter definition with mutability, name, type
   - `fn_def`: function definition (name, params, return type, body)

3. **OperationalSemantics.v** — Big-step evaluation
   - `value`: VUnit, VInt, VFloat
   - `store_entry`: tracks variable name, type, value, and `se_used` flag
   - `store`: list of entries (runtime variable state)
   - `eval fenv s e s' v`: expression e with functions fenv evaluates to v, transforming store s → s'
   - Key rules: Eval_Var_Copy (unrestricted), Eval_Var_Consume (linear/affine), Eval_Replace, Eval_Drop, Eval_Call
   - `eval_args`: left-to-right argument evaluation

4. **TypingRules.v** — Inductive typing judgements
   - `ctx_entry`: (variable, type, consumed flag)
   - `ctx`: list of ctx_entry
   - `typed fenv Γ e T`: Prop-level proof that expression e has type T under function environment and context Γ
   - Context helpers: ctx_lookup, ctx_consume, ctx_add, ctx_remove, ctx_is_ok
   - Defines usage constraints at typing level (parallel to OperationalSemantics constraints)

5. **TypeChecker.v** — Executable type inference + OCaml extraction
   - Decidable mirrors of TypingRules helpers with `_b` suffix (ctx_lookup_b, ctx_consume_b, etc.)
   - `infer_result`: structured error reporting (OK vs Err variants)
   - `infer_core`: main recursive inference function; handles alpha renaming to avoid capture
   - `infer`: top-level entry point
   - `infer_args`: separate copy for use in proofs (not the inline `go` helper)
   - **Extraction target**: generates `fixtures/TypeChecker.ml` and `fixtures/TypeChecker.mli`

6. **AlphaRenaming.v** — Alpha-equivalence proofs
   - Proves that fresh variable renaming preserves typing and semantics
   - Lemmas about renaming contexts, expressions, and functions
   - Critical for soundness: type checker performs alpha renaming to avoid variable capture during inference

7. **CheckerSoundness.v** — Checker ↔ Typing correspondence
   - Proves `infer` is sound and complete: `infer fenv Γ e` returns `OK T` iff `typed fenv Γ e T`
   - Bridges decidable `_b` operations to Prop-level TypingRules definitions
   - Uses alpha renaming lemmas from AlphaRenaming.v

8. **CheckerUsageSoundness.v** — Usage soundness theorems
   - Proves typing respects usage constraints (linear variables are consumed exactly once)
   - Relates static TypingRules constraints to runtime OperationalSemantics behavior

### OCaml Frontend

The OCaml pipeline turns `.facet` source files into typed, linearity-checked programs. It lives in `ocaml/` and is built with dune; `fixtures/` wraps the extracted `TypeChecker.ml` as a dune library.

Pipeline stages:
1. **`lexer.ml`** (sedlex) — tokenizes `.facet` source
2. **`parser.mly`** (Menhir) — produces `Ast.named_fn_def list` using string names
3. **`ast.ml`** — named AST (`named_expr`) before de Bruijn conversion
4. **`debruijn.ml`** — converts string names to `TypeChecker.ident = (string * nat)` pairs; handles shadowing by incrementing an index counter per name
5. **`main.ml`** — calls `TypeChecker.infer` on each function, reports errors
6. **`fir.ml`** — optional Flat IR lowering: converts `expr` tree to linear instruction list (`fir_instr`) with explicit labels, gotos, and `if`/`goto` branches

`ELetInfer` (type-inferred let) and `EIf` are implemented in the OCaml frontend and FIR but have no Rocq soundness proofs yet.

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
- `infer_direct` in `TypeChecker.v` is the non-renaming path; `--debug-alpha` in the OCaml frontend runs both and reports any disagreement (differential testing)

**Out of scope (Rocq formalization)**:
- `TRef`, `TFn` type inference, mutability checking, borrowing/ownership
- `ELetInfer`, `EIf` soundness proofs (implemented in OCaml, not yet proven)

## Key Files and Their Roles

| File | Purpose |
|------|---------|
| `rocq/_CoqProject` | Declares library mapping (-R theories Facet) and compilation order |
| `rocq/Makefile` | Generated by `rocq makefile`; runs `rocq compile` on all files |
| `fixtures/TypeChecker.ml` | **Generated** OCaml extraction from TypeChecker.v; do not edit manually |
| `fixtures/TypeChecker.mli` | **Generated** OCaml interface; updated by make |
| `fixtures/dune` | Wraps extracted OCaml as `type_checker` library for dune |
| `ocaml/fir.ml` | Flat IR lowering from `expr` tree to linear instruction list |
| `ocaml/grammar.ml` | Embedded EBNF grammar string; printed by `--generate-grammar` |
| `plan/` | Design notes: `if_expression.md`, `let_type_infer.md`, `typed_ir.md`, `alpha_renaming_lemmnas.md`; `simple_lifetime_and_borowwing/` for future work |

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

**Facet source tests**: `tests/valid/` contains programs that must type-check cleanly (exit 0); `tests/invalid/` contains programs that must produce a type error (exit 1). Subdirectories group by error category (e.g., `linear_affine_error/`, `shadowing_error/`, `if_expression/`). There is no automated test runner; invoke the OCaml frontend per file as shown in the OCaml commands section above.

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
- **`dune build` fails with missing `TypeChecker`**: Run `cd rocq && make` first to regenerate `fixtures/TypeChecker.ml`

## Commit Conventions

- Use short imperative subjects: `add docker files`, `prove affine values used at most once`
- Describe type-system or proof impact in the body
- List commands run (e.g., `cd rocq && make`)
- Call out regenerated artifacts: `fixtures/TypeChecker.ml`
- Link planning notes or design docs when relevant
