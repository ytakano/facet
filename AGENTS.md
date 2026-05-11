# Repository Guidelines

## Project Structure & Module Organization

Facet is a Rocq formalization of a small type system with affine, linear, and unrestricted usage. Main sources are in `rocq/theories/TypeSystem/` under the `Facet.TypeSystem` namespace:

- `Types.v`, `Syntax.v`: core type and AST definitions.
- `OperationalSemantics.v`, `TypingRules.v`: runtime semantics and inductive typing rules.
- `TypeChecker.v`: executable checker and OCaml extraction entry point.
- `CheckerSoundness.v`: proofs relating the checker to the rules.

`rocq/_CoqProject` declares the library mapping and file order. `fixtures/TypeChecker.ml` and `.mli` are generated extraction artifacts; do not edit them manually. Docker setup scripts live in `docker/`, and planning notes live in `plan/`.

## Build, Test, and Development Commands

Run Rocq commands from `rocq/` unless noted:

- `cd rocq && make`: compile all theories and regenerate extracted OCaml fixtures.
- `cd rocq && rocq makefile -f _CoqProject -o Makefile`: regenerate the Rocq Makefile after changing `_CoqProject`.
- `cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeChecker.v`: compile one theory file while preserving the project namespace.
- `sh docker/build.sh`, `sh docker/up_docker.sh`, `sh docker/exec_zsh.sh`, `sh docker/down_docker.sh`: build, start, attach to, and stop the Docker environment from the repository root.

## Coding Style & Naming Conventions

Follow the existing Rocq style: two-space indentation in matches and proof scripts, short section comments for major blocks, and descriptive lemma/function names. Imports should use `From Facet.TypeSystem Require Import ...` for local modules and standard `Stdlib` imports for Rocq libraries. Boolean/decidable mirrors in `TypeChecker.v` use a `_b` suffix, such as `ctx_lookup_b`, and should correspond clearly to `Prop`-level definitions in `TypingRules.v`.

## Testing Guidelines

The primary test is successful Rocq compilation. Run `cd rocq && make` before submitting changes. When changing `_CoqProject`, regenerate `Makefile` first, then rebuild. For checker changes, confirm that `CheckerSoundness.v` still compiles and that extraction updates `fixtures/TypeChecker.ml` as expected.

## Commit & Pull Request Guidelines

The current history uses short imperative commit messages, for example `add docker files`; keep subjects concise and action-oriented. Pull requests should describe the type-system or proof impact, list the commands run, and call out regenerated artifacts such as `fixtures/TypeChecker.ml`. Link related issues or design notes when available.

## Agent-Specific Instructions

Respect generated files: edit Rocq sources first and let `make` update extraction outputs. Avoid broad rewrites of proof files unless required by the change, and keep module order consistent with `_CoqProject`.
