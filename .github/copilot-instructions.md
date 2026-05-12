# Copilot Instructions for Facet

## Project Overview

Facet is a Rocq (formerly Coq) formalization of a programming language type system featuring **affine**, **linear**, and **unrestricted** types. The project proves a type checker sound with respect to the operational semantics. An OCaml frontend (built with dune) type-checks `.facet` source files using the extracted checker.

## Build Commands

**Two pipelines must run in order**: Rocq `make` first (produces `fixtures/TypeChecker.ml`), then `dune build`.

### Rocq (run from `rocq/`)

```bash
# Build all theories and regenerate extracted OCaml
cd rocq && make

# Compile a single .v file (preserves Facet namespace)
cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeChecker.v

# Check one file without writing .vo outputs
cd rocq && rocq check -R theories Facet theories/TypeSystem/TypeChecker.v

# Regenerate the Makefile after editing _CoqProject
cd rocq && rocq makefile -f _CoqProject -o Makefile

# Force full rebuild (e.g., if fixtures are stale)
cd rocq && make clean && make
```

### OCaml (run from repo root)

```bash
# Build the OCaml frontend (requires Rocq make to have run first)
dune build

# Type-check a single .facet file
dune exec ocaml/main.exe -- path/to/file.facet

# Emit Flat IR alongside type checking
dune exec ocaml/main.exe -- --emit-fir output.fir path/to/file.facet

# Print the embedded EBNF grammar
dune exec ocaml/main.exe -- --generate-grammar

# Differential-test alpha-renaming path against direct path
dune exec ocaml/main.exe -- --debug-alpha path/to/file.facet

# Run all tests (valid/ expects exit 0; invalid/ expects exit 1)
for f in tests/valid/**/*.facet; do dune exec ocaml/main.exe -- "$f" || echo "FAIL: $f"; done
for f in tests/invalid/**/*.facet; do dune exec ocaml/main.exe -- "$f" && echo "FAIL (expected error): $f"; done
```

### Docker Development Environment (from repo root)

```bash
sh docker/build.sh       # build image
sh docker/up_docker.sh   # start container (Rocq 9.1.1 pre-installed)
sh docker/exec_zsh.sh    # attach shell
sh docker/down_docker.sh # stop container
sh docker/rebuild.sh     # rebuild from scratch
```

## Architecture

### Rocq Module Structure

`rocq/_CoqProject` declares the library mapping and **compilation order** — do not reorder entries:

```
rocq/theories/TypeSystem/   ← namespace: Facet.TypeSystem
  Types.v                   ← Core type definitions (usage, Ty, TypeCore)
  Syntax.v                  ← AST (expr, fn_def, param, ident)
  OperationalSemantics.v    ← Big-step eval with runtime store
  TypingRules.v             ← Inductive typing judgements + context helpers
  TypeChecker.v             ← Decidable infer function; OCaml extraction target
  AlphaRenaming.v           ← Proofs that fresh renaming preserves typing/semantics
  CheckerSoundness.v        ← Soundness theorems (infer ↔ typed)
  CheckerUsageSoundness.v   ← Usage constraints: linear vars consumed exactly once
```

### OCaml Frontend Pipeline

```
lexer.ml (sedlex) → parser.mly (Menhir) → ast.ml → debruijn.ml → main.ml
                                                                      ↓
                                                              TypeChecker.infer
                                                              (extracted from Rocq)
```

`debruijn.ml` converts string names to `TypeChecker.ident = (string * nat)` pairs, incrementing the nat index per name to handle shadowing. `fir.ml` optionally lowers the `expr` tree to a linear instruction list with explicit labels and gotos.

### Type System Concepts

**Usage qualifiers** (subtyping order: `unrestricted <: affine <: linear`):
- `UUnrestricted` — used any number of times (copy semantics)
- `UAffine` — used **at most once** (move on use, drop optional)
- `ULinear` — used **exactly once** (must be consumed or explicitly `drop`ped)

**Typing context** (`ctx` in TypingRules): list of `(ident * Ty * bool)` triples — the `bool` marks whether a binding has been consumed. Context threads through expressions left-to-right.

**Two parallel implementations**: `TypingRules.v` has inductive `Prop`-level rules; `TypeChecker.v` has the computable mirror. `CheckerSoundness.v` proves they agree.

**Key expressions**:
- `EReplace (PVar x) e_new` — replaces x's value in place; x is **not** consumed, the new value is.
- `EDrop e` — consumes e and returns unit; satisfies a linear variable's usage requirement.
- `ECall fname args` — arguments consumed left-to-right; linear return values must be used.

**Not yet formalized in Rocq**: `ELetInfer`, `EIf` soundness; `TRef`, `TFn` type inference; mutability; borrowing/ownership.

## Key Conventions

- **Rocq imports**: `From Facet.TypeSystem Require Import ...` for local modules; `Stdlib` for Rocq library.
- **`_b` suffix**: decidable (boolean) mirrors of context helpers (e.g., `ctx_lookup_b` ↔ `ctx_lookup`). Correspondences proven in `CheckerSoundness.v` via lemmas like `ctx_lookup_b_eq`.
- **Generated files**: `fixtures/TypeChecker.ml` and `fixtures/TypeChecker.mli` are extracted by Rocq — never edit manually. Always run `cd rocq && make` first, then `dune build`.
- **Termination trick**: `infer` uses an inline `let fix go` for argument processing so Rocq's termination checker sees structural recursion. A separate top-level `infer_args` exists for use in theorem statements.
- **Runtime vs. static tracking**: `OperationalSemantics.store` uses `se_used` flag; `TypingRules.ctx` uses `consumed` bool. Both must agree (proven in `CheckerUsageSoundness.v`).
- **Alpha renaming**: `infer_core` renames free variables before processing function bodies to prevent capture. `--debug-alpha` runs both paths and reports disagreements.
- **Rocq style**: two-space indentation in matches and proof scripts; short section comments for major blocks.
- **Commits**: short imperative subjects (`add docker files`); call out regenerated `fixtures/TypeChecker.ml`.

## Troubleshooting

| Symptom | Fix |
|---|---|
| Compilation fails after editing `_CoqProject` | `cd rocq && rocq makefile -f _CoqProject -o Makefile` then `make` |
| `fixtures/TypeChecker.ml` not updating | `cd rocq && make clean && make` |
| `dune build` fails with missing `TypeChecker` | Run `cd rocq && make` first |
| Alpha-renaming lemmas not found | Verify `AlphaRenaming.v` compiles before soundness files |
| Incomplete proofs (`Admitted`) in soundness files | Do not ship; core files must have no `Admitted` |
