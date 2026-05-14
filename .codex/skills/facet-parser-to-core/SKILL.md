---
name: facet-parser-to-core
description: Use when changing surface syntax, parser, desugaring, elaboration to core AST, or source-to-core translation.
---

## Required workflow

1. Identify the surface syntax being changed.
2. Identify the target core AST form.
3. State whether the translation is:
   - purely syntactic desugaring
   - name resolution
   - type-directed elaboration
   - ownership/drop elaboration
4. If the translation is type-directed, do not hide it inside the parser.
5. Add tests for:
   - accepted surface syntax
   - rejected malformed syntax
   - produced core form
   - checker result after translation

## Hard constraints

- Parser must not perform type checking implicitly.
- Desugar must not insert ownership-sensitive operations unless specified.
- Drop insertion must be a named elaboration phase, not a parser side effect.
