# Module Roadmap to Package/Crate Root

## Goal

M6 の到達点は、Facet のモジュール機構を「単一ファイル内の名前空間」から「package/crate root を起点に複数ファイルを組み立てる言語機能」へ拡張すること。

この段階でも Rocq 側の core AST と verified checker は flat なプログラムを受け取る。モジュール、ファイル探索、可視性、import 解決は OCaml frontend の責務とし、CLI の accept/reject は引き続き extracted `infer_program_env_end2end` に委ねる。

## Target Model

- **crate root**: 1 つのコンパイル単位の入口。CLI に渡した `.facet` ファイルを既定の crate root とする。
- **package root**: crate root から相対ファイル module を探索する基準ディレクトリ。明示指定がない場合は crate root の親ディレクトリ。
- **core root**: `core::...` を提供する標準ライブラリ root。既定は repository/runtime の `core/`、明示指定は `--core-dir DIR`。
- **module path**: `foo::bar::Baz` のような canonical path。flatten 後は既存 checker が扱える一意な名前へ変換する。
- **source module**: inline `mod foo { ... }` または file module `mod foo;` で導入される名前空間。

## Scope by Milestone

### M1: Inline Module Baseline

Status: implemented in the current module plan.

- Parse inline `mod name { ... }`.
- Flatten module-local functions, structs, enums, and traits into canonical names.
- Resolve explicit qualified paths before de Bruijn conversion.
- Keep Rocq checker input flat.

### M2: Qualified Path Validation

Status: implemented in the current module plan.

- Reject unresolved qualified function calls, type paths, enum constructors, struct literals, and trait bounds before raw elaboration.
- Preserve the original unresolved path in diagnostics.
- Keep unqualified local behavior compatible with existing tests.

### M3: Visibility

Status: in progress in the current module plan.

- Parse `pub` on modules, functions, structs, enums, and traits.
- Default visibility is private.
- Private items are visible from their defining module and descendant modules.
- Public items are visible by explicit path from outside their defining module subtree.
- Do not add re-export semantics yet.

Completion criteria:

- Public sibling access works by explicit path.
- Private sibling access is rejected.
- Child modules can access parent private helpers.
- `core::option::Option` and `core::result::Result` remain publicly accessible.

### M4: Imports

M4 introduces ergonomic local names without changing the canonical path model.

#### M4.1 Named Imports

- Parse `use path;`.
- Allow imported type/function/constructor names to be used unqualified in the importing module.
- Resolve imports module-locally before flattening.
- Reject ambiguous local names.
- Reject imports of private items outside the visibility boundary.
- No glob imports.
- No aliases.
- No re-exports.

#### M4.2 Import Aliases

- Parse `use path as Name;`.
- Allow aliasing for functions, types, enum variants, structs, and traits where the existing syntax can use the target kind.
- Reject alias collisions with local items and other imports.
- Keep diagnostics based on both the alias and the canonical target path.

Completion criteria:

- Existing explicit qualified paths continue to work.
- Imported names lower to the same canonical flat names as explicit paths.
- Parser remains syntax-only; it must not duplicate type checking.

### M5: File Modules

M5 turns modules into a multi-file source organization feature.

#### M5.1 File Module Declarations

- Parse `mod foo;`.
- Load `foo.facet` or `foo/mod.facet` relative to the declaring file.
- The loaded file contributes items under the declaring module path.
- Reject missing module files.
- Reject duplicate inline/file modules with the same name in one module.
- Reject file module cycles with a path-aware diagnostic.

#### M5.2 Source Map and Diagnostics

- Track each loaded file path in parser and resolver diagnostics.
- Report module load errors with the declaring file and module name.
- Preserve existing single-file CLI behavior.

Completion criteria:

- `main.facet` can declare `mod math;` and use `math::id`.
- Nested file modules work from both `foo.facet` and `foo/mod.facet`.
- Cycles such as `a -> b -> a` are rejected deterministically.

### M6: Package/Crate Root

M6 defines the project boundary and makes module loading predictable.

#### M6.1 CLI Roots

- Add `--core-dir DIR` as the explicit replacement for environment-only core selection.
- Keep `FACET_CORE_DIR` as a fallback or developer convenience if desired.
- Add `--package-root DIR` for resolving file modules.
- Default `--package-root` to the crate root file's parent directory.
- Treat the CLI source file as the crate root.

#### M6.2 Crate Namespace Rules

- Reserve `core` as the built-in root namespace.
- Forbid user-defined top-level `mod core`.
- Keep the user crate's own root implicit for now; paths like `foo::bar` refer to crate-local modules unless rooted at `core`.
- Do not add external package dependencies yet.

#### M6.3 Rooted Module Loading

- Resolve all file module paths under the package root.
- Reject attempts to escape the package root through symlinks or `..` after canonicalization.
- Maintain a module load table keyed by canonical file path and module path.
- Detect duplicate module ownership clearly.

#### M6.4 Build Inputs

- Keep the CLI shape simple:

```text
facet [--core-dir DIR] [--package-root DIR] path/to/main.facet
```

- Do not introduce a manifest file before M7.
- Do not introduce dependency resolution before M7.
- Do not introduce multiple named crates before M7.

Completion criteria:

- A package with `main.facet`, `math.facet`, and `util/mod.facet` type-checks from any current working directory when `--package-root` is provided.
- The same package type-checks without `--package-root` when invoked through its crate root file.
- `core::option::Option` and `core::result::Result` resolve independently of the package root.
- File modules cannot escape the package root.

## Implementation Order

1. Finish M3 visibility enforcement and tests.
2. Add import AST nodes and parser support without resolver behavior.
3. Implement M4.1 named import resolution against canonical module paths.
4. Add M4.2 aliases.
5. Add `mod foo;` AST and parser support.
6. Implement file loading with cycle detection.
7. Add source path tracking to parser/resolver errors.
8. Add `--core-dir` and `--package-root`.
9. Enforce package-root containment for file modules.
10. Add package-root regression fixtures.

## Non-Goals Before M7

- Manifest files such as `Facet.toml`.
- External dependency packages.
- Multiple named crates in one build.
- `pub use` re-exports.
- Glob imports.
- Prelude injection.
- Semantic standard traits such as `Copy`, `Clone`, or `Drop`.
- Moving module semantics into Rocq core.

## Risks

- File loading can accidentally become a second compiler pipeline. Keep it as source collection plus name resolution only.
- Import resolution can drift into type-directed lookup. Keep import lookup syntactic and kind-aware only where the surface grammar already requires it.
- Root containment must use canonical paths to avoid accepting package escapes.
- Diagnostics need source-file context before multi-file tests become maintainable.

## Verification

For M4 through M6 frontend work:

- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh` when canonical names or FIR output can change

Run `cd rocq && make` only if Rocq sources, extraction mappings, or generated checker artifacts are changed. The intended M4-M6 work should not require Rocq changes.
