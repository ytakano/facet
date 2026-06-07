---
name: rocq-unused-artifact-cleanup
description: Use when finding and removing unused Rocq/Coq theorems, lemmas, definitions, inductives, hints, instances, or helper artifacts from a Rocq project.
---

# Rocq Unused Artifact Cleanup

Use this skill when asked to mechanically find and remove unused or dead Rocq artifacts such as:

* `Theorem`
* `Lemma`
* `Definition`
* `Fixpoint`
* `Inductive`
* `Record`
* local helper lemmas
* proof-only definitions
* unused checker/helper functions
* unused instances or hints

The goal is to remove genuinely dead internal artifacts without breaking public APIs, extraction targets, proof automation, or documentation/search affordances.

## Required workflow

### 1. Establish a clean baseline

Before removing anything, run the normal project build.

```sh
dune build
```

or, if the project does not use dune:

```sh
make
```

Do not begin deletion if the baseline build already fails. First report the existing failure.

### 2. Generate a dependency graph

Prefer `coq-dpdgraph` / `dpdgraph` when available.

Create or update a small dependency graph driver file, for example:

```coq
Require dpdgraph.dpdgraph.

From PROJECT Require Module1.
From PROJECT Require Module2.
From PROJECT Require Module3.

Set DependGraph File "unused-analysis.dpd".

Print FileDependGraph
  PROJECT.Module1
  PROJECT.Module2
  PROJECT.Module3.
```

Use `Require`, not `Import` or `Export`, in the dependency graph driver unless the project specifically requires otherwise.

Then run the driver with the project’s normal Rocq flags, for example:

```sh
rocq compile -Q theories PROJECT tools/unused_graph.v
```

or through the project’s build system if it already supports this.

### 3. Collect unused candidates

Run:

```sh
dpdusage unused-analysis.dpd > unused.raw.txt
```

Optionally inspect low-reference artifacts too:

```sh
dpdusage -threshold 1 unused-analysis.dpd > low-usage.raw.txt
```

Treat this output as **candidates only**, not as proof that deletion is safe.

### 4. Identify protected roots

Before deleting anything, classify protected artifacts.

Never delete artifacts merely because they have no incoming dependency if they are:

* public API definitions
* top-level soundness, completeness, correctness, safety, or refinement theorems
* final theorems cited by documentation
* extraction targets
* executable checkers
* codecs, parsers, serializers, or generated-entry functions
* examples intentionally exposed for users
* tutorial or documentation-facing lemmas
* `Hint Resolve`, `Hint Constructors`, `Hint Unfold`, or `Hint Extern` targets
* typeclass `Instance`s
* `Existing Instance`s
* canonical structures
* notation support definitions
* Ltac helper definitions used dynamically
* module interface artifacts
* compatibility shims
* deprecated-but-public aliases
* artifacts referenced only from comments, papers, READMEs, or external users

Maintain a local allowlist such as:

```text
tools/unused-allowlist.txt
```

Each allowlist entry should include a short reason.

Example:

```text
typing_soundness              # public theorem
check_program_sound           # extraction root
wf_ty_dec                     # executable checker dependency
expr_eqb_spec                 # proof automation / Search helper
```

### 5. Classify each candidate

For each unused candidate, classify it as one of:

```text
DELETE_NOW
KEEP_PUBLIC_API
KEEP_EXTRACTION_ROOT
KEEP_AUTOMATION
KEEP_DOCUMENTATION
KEEP_FUTURE_WORK
INVESTIGATE
```

Prefer deletion only for private/internal artifacts with no incoming references.

Good deletion candidates include:

* helper lemmas created during proof development but never used
* duplicate lemmas subsumed by stronger lemmas
* old definitions replaced by newer versions
* local checker variants no longer called
* obsolete examples not used in tests or docs
* internal compatibility functions for removed syntax

### 6. Delete in small batches

Remove candidates in small batches, preferably by module.

After each batch, run:

```sh
dune build
```

or the project’s normal build command.

If the build fails, either:

1. restore the removed artifact, or
2. replace the dependency with the intended newer artifact if the deleted one was only a stale alias.

Do not perform large blind deletions across unrelated modules.

### 7. Check proof automation separately

If the removed artifact was a hint, instance, rewrite lemma, or Ltac helper, run affected files explicitly.

Search for dynamic uses:

```sh
grep -R "Hint Resolve .*NAME\|Hint Constructors .*NAME\|Hint Unfold .*NAME\|Hint Extern .*NAME" theories
grep -R "Existing Instance .*NAME\|Instance .*NAME" theories
grep -R "autorewrite.*NAME\|rewrite.*NAME\|eauto.*NAME\|auto.*NAME" theories
grep -R "Ltac .*NAME\|NAME" theories
```

Remember that proof automation dependencies may not always appear as ordinary direct references in the same way as explicit theorem applications.

### 8. Check extraction targets

If the project uses extraction, run extraction after deletion.

Examples:

```sh
dune build @extract
```

or:

```sh
make extract
```

Then run the extracted-language tests if available:

```sh
dune test
```

or project-specific OCaml/Haskell/Rust tests.

Do not delete definitions involved in extraction unless the extracted checker/application still builds and tests pass.

### 9. Update documentation and allowlists

If a deleted artifact appears in documentation, tutorials, comments, diagrams, or design notes, update those references.

Search:

```sh
grep -R "ARTIFACT_NAME" .
```

Do not leave stale references.

If an artifact is intentionally kept despite being unused, add it to the allowlist with a reason.

### 10. Produce a cleanup report

At the end, summarize:

```text
Deleted:
- Module.Name1: reason
- Module.Name2: reason

Kept despite unused:
- Module.Name3: public API
- Module.Name4: extraction root
- Module.Name5: automation hint

Verification:
- dune build: pass
- extraction: pass/fail/not applicable
- tests: pass/fail/not applicable

Notes:
- Any candidates that need human review
```

## Hard constraints

* Do not delete top-level soundness, completeness, correctness, type-safety, preservation, progress, refinement, or schedulability theorems solely because no later theorem refers to them.
* Do not delete extraction roots or executable checker entry points solely because proof files do not refer to them.
* Do not delete public API artifacts solely because they are internally unused.
* Do not delete hints, instances, canonical structures, notations, or Ltac helpers without checking automation and dynamic usage.
* Do not silently replace a theorem with a weaker theorem.
* Do not weaken statements just to make cleanup easier.
* Do not change semantics, typing rules, checker behavior, or extraction behavior during unused-artifact cleanup unless explicitly asked.
* Do not batch-delete across many unrelated modules without intermediate builds.
* Do not treat `dpdusage` output as authoritative deletion permission.
* Do not leave the project in a state where documentation references deleted artifacts.

## Recommended command checklist

```sh
# Baseline
dune build

# Generate dependency graph
rocq compile -Q theories PROJECT tools/unused_graph.v

# Find unused candidates
dpdusage unused-analysis.dpd > unused.raw.txt

# Optional low-reference scan
dpdusage -threshold 1 unused-analysis.dpd > low-usage.raw.txt

# Search for textual references
grep -R "CANDIDATE_NAME" .

# Build after each deletion batch
dune build

# Run extraction if applicable
dune build @extract

# Run tests if applicable
dune test
```

## Deletion policy

Prefer this order:

1. private helper lemmas
2. duplicate lemmas
3. obsolete internal definitions
4. obsolete examples
5. obsolete checker variants
6. obsolete compatibility aliases

Avoid deleting:

1. public theorems
2. public definitions
3. extraction roots
4. theorem statements used as project milestones
5. documentation-facing artifacts
6. proof automation artifacts
7. typeclass instances
8. notation support definitions

## Suggested commit message

```text
Remove unused Rocq artifacts

- Generate dependency graph with dpdgraph
- Remove unused private helper lemmas/definitions
- Keep public API, extraction roots, and automation artifacts
- Verify with full Rocq build and extraction/tests where applicable
```
