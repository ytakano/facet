---
name: facet-ocaml-integration
description: Use when changing OCaml CLI, parser integration, extracted checker invocation, error reporting, or test harness code.
---

## Required workflow

1. Identify whether the change is:
   - parser
   - desugar
   - checker invocation
   - error reporting
   - CLI behavior
   - test harness
2. Do not duplicate checker logic in OCaml.
3. Convert parser output into the verified core AST explicitly.
4. Preserve checker failure as failure.
5. Preserve checker success as success only when all frontend phases succeeded.
6. Add an end-to-end test using the CLI.
7. Add a minimal regression test if the change fixes a bug.

## Hard constraints

- OCaml wrapper must not accept a program rejected by the extracted checker.
- Error pretty-printing must not change checker result.
- Parser recovery must not fabricate valid core terms silently.
