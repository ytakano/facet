---
name: rocq-coqhammer-decomposition
description: Use when direct `hammer.` fails or times out on a Rocq/Coq theorem, and the proof should be split into helper lemmas that can be proved recursively with CoqHammer or simple tactics.
---

# Rocq CoqHammer Decomposition Skill

## Purpose

Use this skill to prove hard Rocq/Coq theorems by combining:

1. high-level lemma decomposition,
2. temporary conditional checking with `Admitted` in scratch work only,
3. CoqHammer-driven solving of small local obligations,
4. recursive decomposition of remaining hard sublemmas,
5. final kernel-checked proofs with no new `Admitted`.

The central rule is:

> Do not ask CoqHammer to solve a large proof plan.
> Decompose the theorem until each leaf is small enough for CoqHammer, simple induction, `lia`, `auto`, or local rewriting.

## When to use

Use this skill when:

* `hammer.` fails on the original theorem.
* The theorem mentions multiple interacting definitions.
* The proof likely needs intermediate lemmas.
* The proof requires both planning and local automation.
* An LLM-generated proof has the right idea but fails with missing lemmas, bad scopes, or tactic errors.
* The proof is longer than a few straightforward tactics.

Do not use this skill for tiny goals where `lia`, `auto`, `eauto`, `constructor`, `congruence`, or direct rewriting is enough.

## Required imports

Prefer project-local conventions. If the project already imports Hammer modules elsewhere, follow that style.

Common imports:

```coq
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
```

Use:

```coq
hammer.
```

as an exploratory tactic.

Use stable reconstructed tactics such as `sauto`, `best`, or ordinary Rocq tactics in committed proofs when possible.

## Environment checks

Before relying on CoqHammer, check whether external provers are available:

```sh
command -v vampire || true
command -v eprover || true
command -v cvc4 || true
command -v z3_tptp || true
```

At least one external first-order prover should be available. More provers usually improve success.

Inside Rocq, optionally check:

```coq
Hammer_version.
```

For debugging only:

```coq
Set Hammer Debug.
hammer.
Unset Hammer Debug.
```

For scratch exploration only, short bounded timeouts are preferred:

```coq
Set Hammer ATPLimit 30.
Set Hammer ReconstrLimit 10.
```

Do not introduce large unbounded hammer calls into committed proof files.

## Core workflow

### 1. Inspect the theorem

Before proving, identify:

* the main conclusion shape: equality, inequality, implication, conjunction, existential, preservation, progress, invariant, etc.;
* the definitions mentioned in the goal;
* the hypotheses that look semantically important;
* existing lemmas near the relevant definitions;
* whether the proof likely needs induction, inversion, rewriting, arithmetic, or map/list/set reasoning.

Use commands such as:

```coq
Check name.
Print name.
Search pattern.
Locate notation.
```

Be careful with overloaded notations such as `<=`, `<`, `+`, `=`, and set/list membership. Add scopes such as `%nat` when needed.

### 2. Try the hammer fast path

First try a small direct proof:

```coq
Proof.
  intros.
  hammer.
Qed.
```

If this works, replace the exploratory proof with the reconstructed or stable proof when possible.

If it fails, do not repeatedly call `hammer` on the same large goal. Move to decomposition.

### 3. Build a lemma decomposition plan

Create a compact proof plan before writing the final proof.

A decomposition candidate must contain:

* helper lemma statements;
* a target proof showing the parent theorem follows from those helpers;
* an estimate of which helpers are easy leaves and which need further decomposition.

Good helper lemmas should:

* mention fewer definitions than the parent theorem;
* isolate one semantic fact;
* be reusable but not overly general;
* avoid unnecessary hypotheses;
* have conclusions that are easy for automation to use;
* be named according to the local project style.

Bad helper lemmas:

* are almost identical to the parent theorem;
* simply restate the target with renamed variables;
* add unrealistic assumptions;
* require more complex reasoning than the original theorem;
* depend circularly on the parent theorem;
* hide the entire proof in a single huge statement.

### 4. Validate the parent proof conditionally

Use temporary `Admitted` only in a scratch file, temporary branch, or local uncommitted edit.

The goal is to check:

> If these helper lemmas are available, does the parent theorem close?

Example scratch shape:

```coq
Lemma helper_1 : ...
Admitted.

Lemma helper_2 : ...
Admitted.

Theorem target : ...
Proof.
  intros.
  ...
  apply helper_1.
  ...
  apply helper_2.
Qed.
```

A decomposition candidate is valid only if:

* every helper statement parses and type-checks;
* the target proof closes using the helpers;
* no helper is syntactically or semantically circular;
* no final committed file contains the temporary `Admitted`.

After validation, remove or replace every temporary admission.

### 5. Rank candidate decompositions

If several decompositions are possible, prefer the one whose hardest helper is easiest.

Use this heuristic score:

```text
candidate difficulty = difficulty of the hardest helper lemma
```

Prefer helpers that:

* have a short normalized goal after `intros`;
* have few hypotheses;
* mention one or two definitions;
* are first-order;
* are mostly equality, order, list, set, map, or arithmetic facts;
* look solvable by `hammer`, `sauto`, `best`, `lia`, `congruence`, `auto`, or one simple induction.

Avoid candidates where any helper:

* requires several nested inductions;
* requires higher-order reasoning;
* requires inventing a major invariant;
* needs large unfolding of recursive definitions;
* has many disjunctions, existentials, dependent equalities, or complex pattern matches;
* introduces a bottleneck harder than the parent theorem.

When unsure, create a tiny scratch proof:

```coq
Lemma candidate_helper : ...
Proof.
  repeat intro.
  hammer.
Abort.
```

Do not leave this in committed code.

### 6. Prove leaves first

For each helper lemma, try this order:

1. existing project lemmas;
2. `hammer`;
3. stable Hammer tactics such as `sauto` or `best`;
4. domain-specific tactics such as `lia`;
5. small manual steps, then `hammer`;
6. simple induction or case analysis, then `hammer` on each leaf;
7. further lemma decomposition.

Typical pattern:

```coq
Lemma helper : ...
Proof.
  intros.
  (* maybe unfold one definition or destruct one case *)
  hammer.
Qed.
```

For induction-shaped goals:

```coq
Lemma helper : ...
Proof.
  intros.
  induction x as [| x IH].
  - simpl. hammer.
  - simpl. hammer.
Qed.
```

For equality goals:

```coq
Proof.
  intros.
  apply Nat.le_antisymm.
  - ...
  - ...
Qed.
```

For conjunctions and iff:

```coq
Proof.
  intros.
  split.
  - ...
  - ...
Qed.
```

For map/list/set preservation, split the proof into lookup, membership, cardinality, and extensionality lemmas.

### 7. Recursively decompose failed helpers

If `hammer` fails on a helper:

1. identify which definitions interact;
2. introduce smaller helper lemmas that isolate each interaction;
3. conditionally validate the helper using temporary `Admitted`;
4. prove the new leaves;
5. return to the failed helper.

Keep recursion bounded. If the proof tree grows too large, stop and reassess the theorem statement, existing abstractions, or missing library lemmas.

### 8. Commit only final checked proofs

Before committing:

* remove every new `Admitted`;
* remove every new `Axiom`;
* remove scratch files;
* ensure no `Abort` proof fragments remain in committed modules;
* run the full Rocq build;
* check that the final theorem is proved by `Qed`, not by trust assumptions.

Acceptable final proof styles:

```coq
Proof.
  ...
Qed.
```

Avoid committing:

```coq
Admitted.
```

unless the project explicitly uses admitted interfaces and the user asked for that.

## CoqHammer usage guidelines

### Good uses

Use CoqHammer after reducing the goal to a local fact:

```coq
Proof.
  intros.
  simpl in *.
  hammer.
Qed.
```

Use CoqHammer after a structural split:

```coq
Proof.
  intros.
  split.
  - hammer.
  - hammer.
Qed.
```

Use CoqHammer after induction setup:

```coq
Proof.
  intros.
  induction xs as [| x xs IH].
  - simpl. hammer.
  - simpl. hammer.
Qed.
```

Use CoqHammer for:

* equality chaining;
* simple order facts;
* set/list/map membership facts;
* lookup preservation;
* rewriting with existing lemmas;
* combining hypotheses;
* closing first-order obligations.

### Bad uses

Do not expect CoqHammer to invent:

* the main induction principle;
* the proof architecture;
* a missing invariant;
* a chain of custom intermediate lemmas;
* a complex dependent pattern match;
* a large preservation or progress proof in one call.

Do not spam `hammer.` repeatedly without changing the proof state.

## Stable proof policy

When `hammer.` succeeds, prefer to keep the proof stable.

Recommended order:

1. Use the reconstructed proof script printed by CoqHammer if available.
2. Use `sauto` or `best` if stable and fast.
3. Use a short manual proof if it is clearer and more robust.
4. Keep `hammer.` only if the project accepts it and the build is reproducible.

If a `hammer.` call is slow or flaky, replace it with the reconstructed proof or a smaller lemma.

## Lemma design patterns

### Equality preservation

For goals of the form:

```coq
f (transform x) = f x
```

try helpers:

```coq
transform_preserves_lookup
transform_preserves_membership
transform_preserves_measure
```

### Bound or maximum/minimum goals

For goals involving `max`, `min`, `max_deg`, `list_max`, or bounds:

```coq
measure_transform_le
measure_ge_element
element_preserved_by_transform
```

Then combine with antisymmetry or transitivity.

### Type-safety goals

For preservation/progress-style proofs, split into:

```coq
canonical_forms_*
substitution_*
weakening_*
context_invariance_*
step_preserves_*
value_or_step_*
```

Use CoqHammer mainly for local inversion, weakening side conditions, environment lookup facts, and arithmetic side goals.

### Scheduler or operational-semantics goals

Split into:

```coq
enabled_preserved
service_decomposition
remaining_cost_step
deadline_or_priority_order
admissibility_preserved
selected_job_in_ready_set
```

Use CoqHammer for local set/list/order facts after the semantic case split has been done manually.

### Map/list/set goals

Split into:

```coq
find_after_add_eq
find_after_add_neq
mem_after_remove
elements_membership
cardinal_remove_notin
```

These are often excellent CoqHammer leaves.

## Difficulty heuristic checklist

Before choosing a helper lemma, run this mental check after `intros`.

A helper is likely easy if:

* the goal is short;
* the context is small;
* few definitions need unfolding;
* the statement is first-order;
* it mainly uses equality, implication, conjunction, membership, or arithmetic;
* one existing lemma almost matches it.

A helper is likely hard if:

* it mentions many recursive functions;
* it has nested pattern matching;
* it needs a custom induction hypothesis;
* it contains many existentials or disjunctions;
* it mixes several semantic concepts;
* it requires unfolding half the development.

Prefer decompositions where no helper is a hard bottleneck.

## Scratch-file discipline

If using temporary admitted helpers, place them in a clearly temporary area, for example:

```text
_tmp/ProofScratch.v
scratch/TargetProofScratch.v
```

or keep them as uncommitted local edits.

Never import scratch modules into committed development code.

Before finishing, run:

```sh
grep -R "Admitted\|admit\|Axiom" .
```

Then inspect every match. Existing project-level admitted items may be allowed, but newly introduced ones are not.

Also check for accidental trust holes:

```sh
grep -R "Unshelve.*admit\|admit\." .
```

## Build workflow

Use the repository’s normal build command. Examples:

```sh
make
dune build
opam exec -- dune build
coq_makefile -f _CoqProject -o Makefile && make
```

After each nontrivial proof change:

1. run the smallest relevant file build;
2. run the relevant directory build;
3. run the full build before finalizing.

If compilation becomes slow, identify the slow lemma or tactic and replace large automation calls with smaller lemmas or reconstructed proofs.

## Failure recovery

When proof search stalls:

1. Print the current goal.
2. Identify the largest definition interaction.
3. Add one helper lemma that removes that interaction.
4. Validate the parent proof with the helper admitted.
5. Prove the helper separately.
6. If the helper is still hard, split it again.

If no useful decomposition is visible, switch from decomposition to sequential proof engineering:

* unfold one definition at a time;
* rewrite with known equations;
* destruct the key discriminant;
* perform the necessary induction manually;
* use `hammer` only on resulting local leaves.

## Hard constraints

* Do not weaken the theorem.
* Do not change definitions just to make the proof easier unless explicitly asked.
* Do not introduce new axioms.
* Do not commit new `Admitted`.
* Do not hide unfinished goals with `Unshelve. all: admit.`
* Do not introduce circular helper lemmas.
* Do not keep unused helper lemmas.
* Do not leave slow, flaky hammer calls if a stable proof can be produced.
* Do not make large unrelated refactors while proving.
* Do not silently change notation scopes or imports in ways that affect other files.

## Final checklist

Before reporting success:

* The target theorem closes with `Qed`.
* All new helper lemmas close with `Qed`.
* No new `Admitted`, `admit`, or `Axiom` remains.
* The proof does not depend on scratch files.
* CoqHammer calls are stable or replaced by reconstructed proofs.
* The proof tree is understandable from lemma names.
* The relevant Rocq build passes.
* Any added helper lemma is used or intentionally part of the local proof API.
