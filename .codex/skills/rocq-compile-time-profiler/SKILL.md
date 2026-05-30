---
name: rocq-compile-time-profiler
description: Use when Rocq compilation is slow or has regressed; profile theorem/lemma compile times first, identify bottlenecks, then optimize without weakening proofs.
---

# Rocq Compile-Time Profiling Skill

Use this skill when a Rocq build, file, theorem, lemma, or proof script compiles slowly, or when a change appears to increase Rocq compile time.

## Goal

Do not optimize Rocq proofs blindly.

When compile time is long, first measure compile time, identify the specific slow theorem, lemma, definition, tactic block, or module dependency, and only then apply a targeted fix.

## Required workflow

1. Reproduce the slow build using the project's normal build command.

   * Prefer the command already documented in `README`, `AGENTS.md`, `dune-project`, `Makefile`, `_CoqProject`, or CI config.
   * Record the exact command used.

2. Capture a baseline timing.

   * Measure wall-clock time for the relevant build target.
   * If possible, measure the specific `.v` file rather than rebuilding the whole project.
   * Save enough output to compare before and after the fix.

3. Profile theorem/lemma-level compile time.

   * Use Rocq/Coq compiler timing support when available, for example compiler flags such as `-time`.
   * If the project uses Dune, Make, or another wrapper, find the supported way to pass compiler timing flags.
   * Identify slow commands around `Theorem`, `Lemma`, `Definition`, `Program`, `Instance`, `Proof`, `Qed`, `Defined`, or heavy tactic invocations.
   * If command-level timing is too coarse, temporarily add local timing instrumentation such as `Time` around suspected proof commands.
   * Remove temporary timing instrumentation before finalizing the change unless the project explicitly wants to keep it.

4. Confirm the bottleneck before editing.

   * Rank the slowest theorem/lemma/proof sections by compile time.
   * Distinguish between:

     * a slow proof script,
     * a slow `Qed`/proof checking phase,
     * a slow typeclass search,
     * a slow rewrite/simplification tactic,
     * a slow dependency import,
     * a slow opaque/transparent unfolding issue,
     * a slow generated obligation.
   * Do not claim a bottleneck unless timing data supports it.

5. Apply targeted optimizations.
   Prefer small, local changes such as:

   * replacing broad `auto`, `eauto`, `lia`, `nia`, `firstorder`, or large rewrite databases with more specific proof steps;
   * reducing unnecessary unfolding, simplification, or repeated normalization;
   * introducing intermediate lemmas only when they reduce repeated work;
   * making expensive helper lemmas opaque when appropriate;
   * avoiding unnecessary imports or moving heavy imports out of common files;
   * replacing fragile tactic search with direct proof terms or narrower tactics;
   * splitting large proofs when that improves checking time and maintainability.

6. Preserve proof meaning.

   * Do not weaken theorem or lemma statements just to improve compile time.
   * Do not replace proofs with `Admitted`, `Axiom`, or unsound assumptions.
   * Do not change public APIs, theorem names, or statement shapes unless required by the task.
   * Do not silently change transparency/opacity if downstream computation or extraction may rely on it.

7. Rebuild and compare.

   * Run the same timing command used for the baseline.
   * Confirm that the targeted theorem/lemma/file improved or that the regression was removed.
   * Run the normal project build after the optimization.
   * If extraction is affected, run the relevant extraction and extracted-code tests.

8. Report results.
   Include:

   * baseline build command;
   * profiling command;
   * identified bottleneck theorem/lemma/file;
   * before/after timing when available;
   * summary of the optimization;
   * any remaining slow proofs or unresolved timing risks.

## Decision rule

Only perform this profiling workflow when Rocq compile time is long, has clearly regressed, or the user explicitly asks for compile-time optimization.

For ordinary small Rocq edits with normal compile time, use the normal proof-editing workflow and do not add profiling overhead.
