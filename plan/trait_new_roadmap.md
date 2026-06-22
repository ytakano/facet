# Implementation Roadmap: Trait Type Safety Proof

## Objective

Complete the type-safety proof path for trait-related programs by aligning the verified end-to-end theorem with the checker endpoint actually used by the CLI, then promoting the direct-receiver split certificate only after it has a complete runtime-safety proof.

The immediate goal is **not** to add more trait surface features. The immediate goal is to make the proof architecture match the checker architecture.

The required public theorem that must remain available is:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

This theorem must eventually prove type safety for the active accepted-program endpoint.

---

## Current Situation

The OCaml CLI currently uses:

```ocaml
infer_program_env_end2end_assoc_direct_receiver_mixed
```

as the authoritative checker endpoint.

The public checked-initial runtime theorem now targets the active mixed endpoint:

```coq
infer_program_env_end2end_assoc_direct_receiver_mixed
```

The mismatch with the older strict/exact endpoint has been fixed. The remaining proof work is the split endpoint runtime-safety theorem.

There is also a diagnostic split endpoint:

```coq
infer_program_env_end2end_assoc_direct_receiver_split
```

with gate:

```coq
check_env_end2end_direct_receiver_split_ready
```

This split endpoint is promising, and it appears to accept programs that the active mixed endpoint rejects, but it is still diagnostic. Do **not** make it the active checker authority until its runtime-safety theorem is complete. Current progress: `direct_receiver_split_runtime_evidence_in_env` packages split-ready runtime facts, the no-receiver branch has a package-backed runtime consumer, and the direct-receiver-present branch has a lower package consumer that avoids explicit global provenance, preservation, and synthetic-summary runtime facts. The remaining split proof gap is deriving `direct_receiver_method_body_runtime_facts_provider` and `component_body_local_bounds_narrow_summary_provider_in_env` from the split certificate.

---

## Non-Negotiable Constraints

1. **Rocq definitions are the source of truth.**

2. **Do not manually edit extracted files:**

   ```text
   fixtures/TypeChecker.ml
   fixtures/TypeChecker.mli
   ```

   These must only change through Rocq extraction.

3. **Do not add handwritten OCaml checker fallbacks.**

   The CLI must accept programs only through an extracted Rocq checker endpoint.

4. **Do not weaken the public type-safety theorem by adding ad hoc public premises.**

   In particular, do not make the final theorem require external assumptions such as:

   ```coq
   check_env_root_shadow_direct_receiver_method_present env' = false \/
   check_env_end2end_direct_receiver_ready env' = true
   ```

   That is a diagnostic bridge, not a final proof architecture.

5. **Do not try to prove:**

   ```coq
   check_env_end2end_direct_receiver_split_ready env = true ->
   check_env_end2end_direct_receiver_ready env = true
   ```

   This is the wrong direction. The split gate exists precisely because the ordinary direct-ready gate is too strong for some valid direct-receiver-method programs.

6. **No `Admitted`, `Axiom`, or `Abort` in the final proof path.**

---

# Phase 0: Freeze Feature Work

## Goal

Stop expanding the language surface until the type-safety endpoint is stable.

## Do Not Work On Yet

Do not add or expand:

```text
dot method syntax
associated type defaults
equality constraints
deriving
field-bearing struct receivers
payload enum receivers
generic direct-call receiver generalization
call-initialized local receiver generalization
new OCaml fallback logic
```

These are follow-up features. They will only make the proof surface larger.

## Allowed Work

Only work on:

```text
rocq/theories/TypeSystem/CheckerRootSidecars.v
rocq/theories/TypeSystem/End2EndSafety.v
rocq/theories/TypeSystem/EnvRuntimeCapturedSafety.v
rocq/_CoqProject, only if a new proof file is truly necessary
ocaml/main.ml, only after the final split endpoint is proved
tests/valid/trait/*
tests/invalid/trait/*
tests/diagnose_trait_gates.sh
plan/trait.md
```

---

# Phase 1: Retarget the Public Type-Safety Theorem to the Active Mixed Endpoint

## Goal

Make the public theorem:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

target the endpoint currently used by the CLI:

```coq
infer_program_env_end2end_assoc_direct_receiver_mixed
```

instead of:

```coq
infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
```

This is not merely a syntactic endpoint substitution. If the existing
mixed-endpoint wrappers only close under extra route, callback, cleanup, or
diagnostic premises, introduce the smallest internal evidence adapter needed in
this phase. Do not expose those facts as new public theorem assumptions.

## Target Shape

The public theorem should have this shape:

```coq
Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
```

Do not add stronger public assumptions.

## Implementation Steps

1. Search existing mixed-endpoint wrappers before writing new theorem variants:

   ```sh
   rg -n "infer_program_env_end2end_assoc_direct_receiver_mixed.*big_step_safe_checked_initial_ready" rocq/theories/TypeSystem/End2EndSafety.v
   rg -n "direct_receiver_mixed.*route_provider|direct_receiver_mixed.*branch|direct_receiver_mixed.*value" rocq/theories/TypeSystem/End2EndSafety.v
   ```

2. Prefer reusing existing wrappers over creating another long theorem chain.

3. If the proof still fails because runtime evidence is not packaged
   correctly, introduce exactly one internal adapter lemma rather than adding
   another public theorem shape.

   Suggested internal lemma name:

   ```coq
   Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_runtime_route_evidence :
     forall env env',
       infer_program_env_end2end_assoc_direct_receiver_mixed env =
         infer_ok env' ->
       env_runtime_route_evidence env'.
   ```

   Keep the `runtime_route_evidence` name for continuity if that is least
   disruptive, but the payload
   must be strong enough for the runtime proof. In practice this may include
   route facts, value-callback facts, cleanup facts, or local-bounds replay
   facts. Do not make the record route-only if the consumer theorem needs more.

   If this adapter requires definitions planned for Phase 2, pull forward the
   minimum definitions now. Phase 2 can then generalize and clean them up.

4. The active mixed endpoint should cover two cases:

   ```coq
   check_env_root_shadow_direct_receiver_method_present env' = false
   ```

   or:

   ```coq
   check_env_end2end_direct_receiver_ready env' = true
   ```

   This case split may be used internally, but it must not become a new public theorem premise.

5. If the proof starts requiring another theorem named like
   `...with_X_and_Y_and_Z_and_callback_and_bridge`, stop and package those facts
   into the internal evidence adapter instead.

## Phase 1 Definition of Done

Status: complete.

The public theorem:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

now targets:

```coq
infer_program_env_end2end_assoc_direct_receiver_mixed
```

not:

```coq
infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
```

Then run:

```sh
cd rocq && make
dune build
sh tests/run.sh
```

Also verify:

```sh
rg -n "Admitted\.|Axiom|Abort\." rocq/theories
```

returns no new proof holes.

---

# Phase 2: Introduce Explicit Runtime Evidence Packages

## Goal

Stop passing checker facts through large boolean gate chains and route-provider
theorem variants. Package the accepted runtime route, value/callback support,
cleanup support, and local-bounds replay support into a small Prop-level
evidence layer.

The current proof is growing because it repeatedly reconstructs the same facts from booleans such as:

```coq
check_env_root_shadow_provenance_summary_or_direct_receiver_method
check_env_preservation_ready_or_direct_receiver_method
check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check
check_env_end2end_direct_receiver_split_ready
```

Instead, the proof should convert booleans to a reusable Prop-level evidence package once.

The important boundary is not the word "route"; it is the consumer-facing
runtime package. If the runtime theorem needs more than a branch route, the
record must carry that stronger package directly.

## Suggested Definitions

Add a small evidence layer in `End2EndSafety.v`, or in a new file only if `End2EndSafety.v` becomes too hard to manage.

Suggested conceptual shape:

```coq
Inductive callee_runtime_route_evidence
    (env : global_env) (fdef : fn_def) : Prop :=
| RouteSyntheticReady :
    (* existing synthetic-ready route/replay facts *) ->
    callee_runtime_route_evidence env fdef

| RouteOrdinaryShadow :
    (* ordinary root-shadow provenance/preservation and replay facts *) ->
    callee_runtime_route_evidence env fdef

| RouteNarrow :
    (* existing narrow-summary replay package *) ->
    callee_runtime_route_evidence env fdef

| RouteDirectReceiverMethod :
    (* direct-receiver-method summary and replay facts *) ->
    callee_runtime_route_evidence env fdef.
```

Then define:

```coq
Record env_runtime_route_evidence (env : global_env) : Prop := {
  route_evidence_for_fn :
    forall fdef,
      In fdef (env_fns env) ->
      callee_runtime_route_evidence env fdef
}.
```

The exact payloads should reuse existing checked facts. Do not invent a parallel type-safety proof.

If an inductive with per-branch constructors is awkward, use records instead.
The design criterion is simple:
`runtime_route_evidence_big_step_safe_checked_initial_ready` should consume this
package without reconstructing a long sequence of boolean gate facts or bridge
callbacks.

## Required Lemmas

For the active mixed endpoint:

```coq
Lemma infer_program_env_end2end_assoc_direct_receiver_mixed_runtime_route_evidence :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    env_runtime_route_evidence env'.
```

For the runtime proof:

```coq
Theorem runtime_route_evidence_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    env_runtime_route_evidence env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
```

Then make the public mixed theorem a thin wrapper:

```coq
Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready :
  ... ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_mixed env =
      infer_ok env' ->
    ... ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros ...
  eapply runtime_route_evidence_big_step_safe_checked_initial_ready; eauto.
  eapply infer_program_env_end2end_assoc_direct_receiver_mixed_runtime_route_evidence; eauto.
Qed.
```

## Why This Phase Matters

The split certificate is per-function and route-sensitive. The runtime proof currently wants whole-environment ordinary readiness in too many places. The evidence layer is the boundary between:

```text
checker booleans
```

and:

```text
runtime proof consumers
```

Without this boundary, every new direct-receiver case creates another bridge theorem.

This phase is a cleanup and strengthening pass over the Phase 1 adapter. Phase
1 may introduce the minimal version; Phase 2 should make the package explicit,
stable, and reusable by both the mixed endpoint and the future split endpoint.

## Phase 2 Definition of Done

The public theorem no longer directly destructs large boolean gates throughout the runtime proof.

There should be a clear two-step structure:

```text
accepted checker endpoint
  -> env_runtime_route_evidence / env runtime package
  -> checked-initial big-step safety
```

Run:

```sh
cd rocq && make
```

---

# Phase 3: Close the Local-Bounds Direct-Receiver Gap

## Goal

Make direct-receiver-method evidence usable under local bounds without reconstructing full ordinary provenance and preservation readiness.

The known blocker is:

```text
direct-receiver narrow-summary stability under local bounds
```

or an equivalent replay theorem that consumes the direct summary without needing whole-environment generic readiness for the local-bounds environment.

## Preferred Direction

Prefer this approach:

```text
Generate or consume direct-receiver evidence directly in the local-bounds environment.
```

Avoid this approach unless it is much easier:

```text
Prove a very broad global stability theorem for every direct-receiver summary.
```

In other words, do not force:

```coq
direct_receiver_summary env f
```

to become:

```coq
direct_receiver_summary (global_env_with_local_bounds env bounds) f
```

by a giant generic stability lemma unless the existing definitions make that natural.

Instead, add a replay-facing lemma that gives exactly the evidence needed by runtime replay at the point where local bounds are introduced.

## Search Targets

Use:

```sh
rg -n "global_env_with_local_bounds" rocq/theories/TypeSystem/End2EndSafety.v rocq/theories/TypeSystem/EnvRuntimeCapturedSafety.v
rg -n "direct_receiver.*local_bounds|local_bounds.*direct_receiver" rocq/theories/TypeSystem
rg -n "narrow_summary.*local_bounds|local_bounds.*narrow_summary" rocq/theories/TypeSystem
```

Find the exact obligation where the direct-receiver branch loses enough evidence to select the direct replay route.

## Add One Narrow Lemma

Add one targeted lemma with a name following the existing style.

Suggested conceptual shape:

```coq
Lemma direct_receiver_method_runtime_route_evidence_at_local_bounds :
  forall env bounds fdef,
    (* existing direct-receiver-method summary/certificate facts *) ->
    (* lookup / membership facts for fdef *) ->
    callee_runtime_route_evidence
      (global_env_with_local_bounds env bounds)
      fdef.
```

Or, if the existing replay theorem wants a more specific package:

```coq
Lemma direct_receiver_method_replay_package_at_local_bounds :
  forall env bounds fdef,
    (* existing direct-receiver-method summary facts *) ->
    (* local-bounds lookup facts *) ->
    (* exact replay package required by EnvRuntimeCapturedSafety *).
```

Keep this lemma narrow. Do not prove a broad theorem unless necessary.

## Forbidden Escape Hatch

Do not solve this by adding the following as a final theorem premise:

```coq
check_env_end2end_direct_receiver_ready env' = true
```

That would make the split endpoint useless for the cases it was designed to accept.

## Phase 3 Definition of Done

The direct-receiver branch of the split runtime proof can proceed without assuming whole-environment ordinary readiness.

Specifically, the proof should not require the final theorem to assume:

```coq
check_env_root_shadow_provenance_summary env' = true
```

and:

```coq
check_env_preservation_ready env' = true
```

for direct-receiver-method functions already covered by the split certificate.

Run:

```sh
cd rocq && make
```

---

# Phase 4: Prove Runtime Safety for the Split Endpoint

## Goal

Turn the diagnostic split endpoint into a real runtime-safety endpoint.

Target endpoint:

```coq
infer_program_env_end2end_assoc_direct_receiver_split
```

Target gate:

```coq
check_env_end2end_direct_receiver_split_ready
```

## Target Theorem

Add or complete:

```coq
Theorem infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env env' f s s' v,
    infer_program_env_end2end_assoc_direct_receiver_split env =
      infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
```

This theorem must consume the split certificate directly.

## Reuse Existing Diagnostic Theorems

Before writing new proof machinery, inspect and reuse the existing diagnostic wrappers:

```sh
rg -n "direct_receiver_split.*big_step_safe_checked_initial_ready" rocq/theories/TypeSystem/End2EndSafety.v
rg -n "direct_receiver_split.*branch_bundle" rocq/theories/TypeSystem/End2EndSafety.v
rg -n "direct_receiver_split.*ready_case" rocq/theories/TypeSystem/End2EndSafety.v
```

Likely useful existing shapes include:

```coq
infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_direct_ready_branch_bundle

infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_branch_bundles_diagnostic

infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready_with_ready_case_diagnostic
```

The work is to remove the diagnostic-only external case assumption and replace it with evidence produced from:

```coq
check_env_end2end_direct_receiver_split_ready env' = true
```

## Required Split Evidence Lemma

Add:

```coq
Lemma infer_program_env_end2end_assoc_direct_receiver_split_runtime_route_evidence :
  forall env env',
    infer_program_env_end2end_assoc_direct_receiver_split env =
      infer_ok env' ->
    env_runtime_route_evidence env'.
```

This lemma should internally use:

```coq
check_env_root_shadow_provenance_summary_or_direct_receiver_method
check_env_preservation_ready_or_direct_receiver_method
check_env_root_shadow_no_receiver_component_ready_body_or_local_narrow_summary_provider_check_with_direct_receiver_splits
```

and existing per-function case lemmas.

## Phase 4 Definition of Done

The split endpoint has a non-diagnostic checked-initial runtime theorem.

The final split theorem must not require:

```coq
check_env_root_shadow_direct_receiver_method_present env' = false \/
check_env_end2end_direct_receiver_ready env' = true
```

Run:

```sh
cd rocq && make
```

---

# Phase 5: Promote the Split Endpoint Only After the Proof Closes

## Goal

Make the split endpoint the active checker authority only after Phase 4 is complete.

## Preconditions

Do not touch the CLI active endpoint until all of these exist and compile:

```coq
infer_program_env_end2end_assoc_direct_receiver_split_sound

infer_program_env_end2end_assoc_direct_receiver_split_runtime_route_evidence

infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready
```

and the public checked-initial theorem can be retargeted safely if desired.

## CLI Change

Only after the split runtime theorem is proved, change `ocaml/main.ml` from:

```ocaml
infer_program_env_end2end_assoc_direct_receiver_mixed env_for_checker
```

to:

```ocaml
infer_program_env_end2end_assoc_direct_receiver_split env_for_checker
```

Keep `--diagnose-trait-gates` useful, but it must remain diagnostic. It must not become an acceptance path.

## Extraction

Run:

```sh
cd rocq && make
```

This should regenerate:

```text
fixtures/TypeChecker.ml
fixtures/TypeChecker.mli
```

Then run:

```sh
dune build
```

## Phase 5 Definition of Done

The CLI uses the extracted split endpoint as its only checker authority.

No handwritten OCaml fallback accepts programs rejected by the extracted checker.

---

# Phase 6: Update Trait Receiver Tests Conservatively

## Goal

Move only the direct-receiver cases justified by the proved split endpoint from invalid safety-gate fixtures to valid fixtures.

## Candidate Test Files

Look at currently invalid trait receiver safety-gate tests such as:

```text
tests/invalid/trait/method_call_explicit_ufcs_fn_receiver_safety_gate.facet
tests/invalid/trait/method_call_short_ufcs_fn_receiver_safety_gate.facet
tests/invalid/trait/method_call_explicit_ufcs_generic_direct_fn_receiver_safety_gate.facet
tests/invalid/trait/method_call_short_ufcs_generic_direct_fn_receiver_safety_gate.facet
```

Promote only the cases covered by the proof.

Do not bulk-promote all receiver forms.

Keep these deferred unless separately proved:

```text
struct literal receiver with fields
enum payload receiver
generic enum payload receiver
local inferred call receiver
local struct receiver
dot syntax receiver
```

## Required Test Commands

Run:

```sh
dune build
sh tests/run.sh
sh tests/diagnose_trait_gates.sh
```

Also run targeted checks:

```sh
dune exec ocaml/main.exe -- tests/valid/trait/<new-valid-case>.facet
dune exec ocaml/main.exe -- --diagnose-trait-gates tests/valid/trait/<new-valid-case>.facet
```

## Phase 6 Definition of Done

The promoted direct-receiver trait tests pass through the extracted Rocq endpoint.

Previously invalid non-covered receiver forms remain rejected.

---

# Phase 7: Clean Up Proof Surface

## Goal

Prevent `End2EndSafety.v` from accumulating more one-off bridge theorem variants.

## Cleanup Rules

After the evidence-based path is working:

1. Keep the public theorem names stable.

2. Mark diagnostic-only wrappers clearly with `_diagnostic`.

3. Avoid introducing more theorem names of the form:

   ```text
   ...with_X_and_Y_and_Z_and_callback_and_bridge...
   ```

   If a theorem name needs five concepts, the proof needs a record.

4. Consolidate repeated checker facts into records such as:

   ```coq
   env_runtime_route_evidence
   direct_receiver_split_branch_bundle_in_env
   no_receiver_runtime_route_bundle_in_env
   ```

5. Update `plan/trait.md` with:

   * active endpoint,
   * proved runtime theorem,
   * remaining unsupported receiver forms,
   * exact test files promoted from invalid to valid.

## Phase 7 Definition of Done

The final proof path is easy to describe as:

```text
extracted checker accepts env
  -> checker certificate facts
  -> runtime evidence package
  -> checked-initial big-step safety
```

not:

```text
extracted checker accepts env
  -> 20 unrelated bridge lemmas
  -> diagnostic case assumption
  -> safety
```

The second one is how proofs become archaeology.

---

# Recommended PR Sequence

## PR 1: Active Mixed Endpoint Alignment

Scope:

```text
End2EndSafety.v
plan/trait.md
```

Deliverables:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

targets:

```coq
infer_program_env_end2end_assoc_direct_receiver_mixed
```

and, if needed, a minimal internal runtime evidence adapter proving that the
active mixed endpoint supplies the package consumed by the public theorem. Do
not add public route, callback, cleanup, or diagnostic premises.

Commands:

```sh
cd rocq && make
dune build
sh tests/run.sh
```

---

## PR 2: Runtime Evidence Package Layer

Scope:

```text
End2EndSafety.v
possibly EnvRuntimeCapturedSafety.v
possibly a new Rocq file only if necessary
```

Deliverables:

```coq
callee_runtime_route_evidence
env_runtime_route_evidence
runtime_route_evidence_big_step_safe_checked_initial_ready
infer_program_env_end2end_assoc_direct_receiver_mixed_runtime_route_evidence
```

The package must include whatever runtime consumers need: route selection,
value/callback support, cleanup support, and local-bounds replay support. A
route-only package is not sufficient if it forces later wrappers to reconstruct
those facts separately.

Commands:

```sh
cd rocq && make
```

---

## PR 3: Direct-Receiver Local-Bounds Replay

Scope:

```text
End2EndSafety.v
EnvRuntimeCapturedSafety.v
CheckerRootSidecars.v only if a missing checker-side fact is truly needed
```

Deliverable:

A narrow lemma allowing direct-receiver-method evidence to feed runtime replay under local bounds, without requiring whole-environment ordinary readiness.

Commands:

```sh
cd rocq && make
```

---

## PR 4: Split Endpoint Runtime Safety

Scope:

```text
End2EndSafety.v
CheckerRootSidecars.v
```

Deliverables:

```coq
infer_program_env_end2end_assoc_direct_receiver_split_runtime_route_evidence

infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready
```

Commands:

```sh
cd rocq && make
```

---

## PR 5: Endpoint Promotion and Tests

Scope:

```text
ocaml/main.ml
fixtures/TypeChecker.ml, regenerated only
fixtures/TypeChecker.mli, regenerated only
tests/valid/trait/*
tests/invalid/trait/*
plan/trait.md
```

Deliverables:

* CLI uses the extracted split endpoint.
* Covered direct-receiver trait tests move to valid.
* Unsupported receiver forms remain invalid.

Commands:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/diagnose_trait_gates.sh
```

---

# Final Acceptance Criteria

The implementation is complete when all of the following are true:

1. The public theorem:

   ```coq
   infer_program_env_end2end_big_step_safe_checked_initial_ready
   ```

   targets the active checker endpoint.

2. The CLI accept/reject path uses only an extracted Rocq endpoint.

3. The split endpoint has a non-diagnostic runtime-safety theorem.

4. No final runtime theorem depends on the diagnostic assumption:

   ```coq
   check_env_root_shadow_direct_receiver_method_present env' = false \/
   check_env_end2end_direct_receiver_ready env' = true
   ```

5. Direct-receiver trait programs accepted by the CLI are covered by the checked-initial big-step type-safety theorem.

6. Unsupported receiver shapes are still rejected.

7. These commands pass:

   ```sh
   cd rocq && make
   dune build
   sh tests/run.sh
   sh tests/diagnose_trait_gates.sh
   rg -n "Admitted\.|Axiom|Abort\." rocq/theories
   ```

8. `plan/trait.md` accurately states:

   * active endpoint,
   * proved theorem,
   * remaining blocked receiver forms,
   * promoted test files,
   * deferred features.

---

# Implementation Priority Summary

Do the work in this order:

```text
1. Retarget public safety theorem to active mixed endpoint, adding the minimal internal evidence adapter needed to close it.
2. Generalize that adapter into a Prop-level runtime evidence package carrying route, value/callback, cleanup, and local-bounds replay facts as needed.
3. Solve direct-receiver local-bounds replay.
4. Prove non-diagnostic split endpoint runtime safety.
5. Promote split endpoint to CLI authority.
6. Promote only proved receiver tests.
7. Document remaining unsupported forms.
```

Do **not** start with the split endpoint activation.
Do **not** add new trait syntax.
Do **not** add OCaml fallback logic.
Do **not** try to coerce split readiness back into ordinary direct readiness.

The proof should be refactored around runtime evidence packages, not expanded by adding more bridge theorem variants.
