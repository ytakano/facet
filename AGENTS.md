# Repository Guidelines

## Project Structure & Module Organization

Facet is a Rocq formalization of a small type system with affine, linear, and unrestricted usage, plus an OCaml frontend for `.facet` programs. Rocq sources are in `rocq/theories/TypeSystem/` under the `Facet.TypeSystem` namespace:

- `Lifetime.v`, `Types.v`, `Syntax.v`: lifetime, core type, and AST definitions.
- `OperationalSemantics.v`, `TypingRules.v`: runtime semantics and inductive typing rules.
- `TypeChecker.v`: executable checker and OCaml extraction entry point.
- `WFType.v`, `AlphaRenaming.v`, `CheckerSoundness.v`, `CheckerUsageSoundness.v`, `BorrowCheckSoundness.v`: well-formedness, alpha-renaming, checker, usage, and borrow-check soundness proofs.

`rocq/_CoqProject` declares the library mapping and file order. `fixtures/TypeChecker.ml` and `.mli` are generated extraction artifacts; do not edit them manually. The OCaml frontend lives in `ocaml/` and is built with dune; `fixtures/dune` wraps the extracted checker as a library. `.facet` regression cases live under `tests/valid/`, `tests/invalid/`, and `tests/fir/`. Docker setup scripts live in `docker/`, design notes in `design/`, and planning notes in `plan/`.

## Build, Test, and Development Commands

Run Rocq commands from `rocq/` unless noted:

- `cd rocq && make`: compile all theories and regenerate extracted OCaml fixtures.
- `cd rocq && rocq makefile -f _CoqProject -o Makefile`: regenerate the Rocq Makefile after changing `_CoqProject`.
- `cd rocq && rocq compile -R theories Facet theories/TypeSystem/TypeChecker.v`: compile one theory file while preserving the project namespace.
- `dune build`: build the OCaml frontend from the repository root after Rocq extraction is current.
- `dune exec ocaml/main.exe -- path/to/file.facet`: type-check one `.facet` source file.
- `dune exec ocaml/main.exe -- --emit-fir output.fir path/to/file.facet`: type-check and emit Flat IR.
- `dune exec ocaml/main.exe -- --generate-grammar`: print the language grammar.
- `sh tests/run.sh`: run valid/invalid `.facet` regression tests.
- `sh tests/fir/run.sh`: run FIR emission smoke tests.
- `sh docker/build.sh`, `sh docker/up_docker.sh`, `sh docker/exec_zsh.sh`, `sh docker/down_docker.sh`: build, start, attach to, and stop the Docker environment from the repository root.

## Coding Style & Naming Conventions

Follow the existing Rocq style: two-space indentation in matches and proof scripts, short section comments for major blocks, and descriptive lemma/function names. Imports should use `From Facet.TypeSystem Require Import ...` for local modules and standard `Stdlib` imports for Rocq libraries. Boolean/decidable mirrors in `TypeChecker.v` use a `_b` suffix, such as `ctx_lookup_b`, and should correspond clearly to `Prop`-level definitions in `TypingRules.v`.

For OCaml code, follow the existing dune project style and keep parser, AST, de Bruijn conversion, FIR lowering, and CLI behavior in their current modules. Prefer updating tests in `tests/valid/`, `tests/invalid/`, or `tests/fir/` when changing user-visible language behavior.

## Testing Guidelines

The primary test is successful Rocq compilation. Run `cd rocq && make` before submitting changes. When changing `_CoqProject`, regenerate `Makefile` first, then rebuild. For checker changes, confirm that `CheckerSoundness.v`, `CheckerUsageSoundness.v`, and `BorrowCheckSoundness.v` still compile and that extraction updates `fixtures/TypeChecker.ml` as expected.

For frontend or language-surface changes, run `dune build`, `sh tests/run.sh`, and, when FIR output is affected, `sh tests/fir/run.sh`. The valid tests should exit 0; invalid tests should be rejected by the checker.

## Commit & Pull Request Guidelines

The current history uses short imperative commit messages, for example `add docker files`; keep subjects concise and action-oriented. Pull requests should describe the type-system or proof impact, list the commands run, and call out regenerated artifacts such as `fixtures/TypeChecker.ml`. Link related issues or design notes when available.

## Agent-Specific Instructions

Respect generated files: edit Rocq sources first and let `make` update extraction outputs. Avoid broad rewrites of proof files unless required by the change, and keep module order consistent with `_CoqProject`. Keep Rocq and OCaml pipelines in order: run Rocq extraction before relying on dune builds that consume `fixtures/TypeChecker.ml`.

When a Rocq compile is slow, times out, appears OOM-killed, or clearly regresses, use the `rocq-compile-time-profiler` skill before continuing proof edits. Prefer targeted profiling first, for example `rocq compile -time-file /tmp/name.txt -R theories Facet -o /tmp/File.vo -noglob theories/TypeSystem/File.v` under an appropriate `timeout`, so tracked `.vo`/`.glob` outputs are not churned while diagnosing the bottleneck. Avoid repeated full `make` runs until the specific slow file or proof command has been identified.

When a Rocq proof path stalls, stop expanding the same proof indefinitely. Treat a proof path as stalled if the same theorem or proof obligation has no substantive progress after two focused work sessions, if three or more helper lemmas fail to close the same obligation, if the proof effort starts pushing toward weaker theorem statements or extra public premises, or if diagnostics show an existing narrower verified summary/certificate already covers the target programs. In that case, reframe the safety argument around the smallest existing verified checker summary, certificate, or runtime package that proves the required property. Prove a diagnostic or certificate theorem first, then promote the check into the public endpoint only after the certificate route is sound.

# Sub-agent policy

Use sub-agents only for implementation tasks.

Allowed:
- Implementing isolated features
- Refactoring code
- Writing tests
- Fixing concrete bugs after the main agent has identified the issue

Not allowed:
- Research
- Design investigation
- Reading papers or docs to decide an approach
- Comparing alternatives
- Architectural decisions
- Summarizing repository-wide findings

For investigation, analysis, design, and planning, the main agent must do the work itself and report the reasoning before assigning implementation work to any sub-agent.

When delegating to a sub-agent, provide a narrow implementation task with:
- target files
- expected behavior
- tests to run
- constraints

# Facet development rules

## Source of truth

The Rocq definitions are the source of truth for the core type system.

The extracted OCaml checker is the implementation of the verified checker.

Generated OCaml files must not be edited manually.

## Trusted boundary

Trusted:
- Rocq kernel
- accepted Rocq proofs
- extraction mechanism, subject to configured extraction mappings

Less trusted:
- parser
- desugarer
- OCaml CLI
- pretty printer
- test harness
- generated witness files, if any

## Required checks

Before completing a type-system-related change, run:

- Rocq build
- extraction
- OCaml build
- OCaml test suite
- end-to-end CLI tests

## Rule

Do not duplicate type-checking logic in OCaml.

The OCaml CLI accept/reject path must use the extracted Rocq
`infer_program_env_end2end` entrypoint as its only checker authority. Do not add
fallback acceptance paths to `infer_full_env`, `infer_full_env_roots`,
`check_program_env`, or handwritten OCaml checker logic. `ErrNotImplemented`
from the extracted end-to-end checker is a rejection, not a signal to retry with
another checker.

When extending the language, typing rules, executable checker, borrow/root
rules, desugaring-to-core translation, or extraction boundary, preserve or
extend the end-to-end checker soundness and type-safety theorems. The required
program-level theorem names are `infer_program_env_end2end_sound`,
`check_program_env_end2end_sound`, and
`infer_program_env_end2end_big_step_safe_checked_initial_ready`.
