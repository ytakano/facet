# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

The current implementation pass is focused on the trait-related type-safety
proof architecture, not on adding more trait surface features. The public
runtime theorem that must remain available is:

```coq
infer_program_env_end2end_big_step_safe_checked_initial_ready
```

This theorem must prove checked-initial big-step safety for the checker endpoint
that the CLI actually uses.

## Current State

- Traits, impls, associated types, trait methods, method-local type parameters,
  generic-trait impl remapping, associated type projections, and receiver-first
  UFCS method calls are parsed, lowered, and checked through the extracted Rocq
  checker. Impl method bodies are elaborated to hidden functions and checked even
  when uncalled. Dot syntax, associated type defaults, equality constraints, and
  `deriving` remain deferred.
- Supported method receivers are forms whose type is known before checker
  execution: parameters, typed literals, pure literal/unit locals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors, including generic instances. Field-bearing structs, payload
  enums, direct-call receivers, generic direct-call receivers, non-pure inferred
  locals, and call-initialized/general annotated locals remain gated.
- The OCaml CLI currently uses
  `infer_program_env_end2end_assoc_direct_receiver_mixed` as its only checker
  authority. Public checker soundness aliases target this endpoint.
- The required public checked-initial runtime theorem still targets the older
  `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`
  endpoint. This mismatch must be fixed before promoting any direct-receiver
  split endpoint.
- A diagnostic split endpoint exists:
  `infer_program_env_end2end_assoc_direct_receiver_split`, gated by
  `check_env_end2end_direct_receiver_split_ready`. Diagnostics show that it can
  accept direct-call receiver fixtures rejected by the active mixed endpoint, but
  it is not yet the active checker authority and does not yet have the required
  non-diagnostic runtime-safety theorem.
- The proof surface in `End2EndSafety.v` has accumulated many route, callback,
  cleanup, bridge, branch-bundle, and diagnostic theorem variants. The next proof
  step is to package the checker-derived runtime facts once and consume that
  package from the public theorem, instead of adding more one-off wrappers.

## Active Proof Plan

1. Retarget the public runtime theorem to the active mixed endpoint.
   - Move `infer_program_env_end2end_big_step_safe_checked_initial_ready` from
     `infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed`
     to `infer_program_env_end2end_assoc_direct_receiver_mixed`.
   - Keep public premises no stronger than the current preservation packages.
   - If existing mixed-endpoint wrappers only close under extra route, callback,
     cleanup, or diagnostic premises, add the smallest internal runtime evidence
     adapter needed to close the public theorem. Do not expose these facts as
     public theorem premises.

2. Introduce an explicit runtime evidence package.
   - Convert checker booleans and endpoint gates into Prop-level evidence once.
   - The package must be strong enough for runtime consumers: route selection,
     value/callback support, cleanup support, and local-bounds replay support may
     all belong in the package.
   - Do not make the package route-only if that forces later theorem wrappers to
     reconstruct callback, cleanup, or local-bounds facts separately.
   - The intended shape is:

     ```text
     extracted checker accepts env
       -> checker certificate facts
       -> runtime evidence package
       -> checked-initial big-step safety
     ```

3. Close the direct-receiver local-bounds replay gap.
   - The known blocker is direct-receiver method evidence under local bounds, or
     an equivalent replay theorem that consumes the direct summary without
     reconstructing whole-environment generic provenance/preservation readiness.
   - Prefer a narrow replay-facing lemma over a broad global stability theorem.
   - Do not solve this by adding `check_env_end2end_direct_receiver_ready env' =
     true` as a final theorem premise.

4. Prove runtime safety for the split endpoint.
   - Target endpoint: `infer_program_env_end2end_assoc_direct_receiver_split`.
   - Target gate: `check_env_end2end_direct_receiver_split_ready`.
   - Required theorem:

     ```coq
     infer_program_env_end2end_assoc_direct_receiver_split_big_step_safe_checked_initial_ready
     ```

   - The theorem must consume the split certificate directly and must not depend
     on the diagnostic assumption:

     ```coq
     check_env_root_shadow_direct_receiver_method_present env' = false \/
     check_env_end2end_direct_receiver_ready env' = true
     ```

5. Promote the split endpoint only after its proof closes.
   - Do not change the CLI active endpoint until the split endpoint has checker
     soundness, runtime evidence, and checked-initial runtime safety.
   - After the proof closes, switch the CLI from
     `infer_program_env_end2end_assoc_direct_receiver_mixed` to
     `infer_program_env_end2end_assoc_direct_receiver_split`.
   - `--diagnose-trait-gates` may remain diagnostic, but it must not become an
     acceptance path.

6. Promote receiver tests conservatively.
   - Move only direct-receiver fixtures justified by the proved split endpoint
     from invalid to valid.
   - Do not bulk-promote field-bearing struct receivers, payload enum receivers,
     local inferred call receivers, call-initialized/general annotated locals, or
     dot syntax receivers.

## Unresolved Blockers

- The public runtime theorem is still not retargeted. A direct proof attempt via
  the existing mixed value/cleanup bridge fails because that bridge needs
  store-safe synthetic summary evidence, while the public theorem currently only
  assumes the weaker synthetic direct-call prefix preservation premise.
- The next Rocq subtask is to introduce the smallest internal runtime evidence
  adapter for the active mixed endpoint, then make the public theorem consume
  that package without adding public route, callback, cleanup, or diagnostic
  premises.
- The diagnostic split endpoint remains promising but cannot become the CLI
  authority until it has a non-diagnostic checked-initial runtime-safety theorem.

## Unsupported Or Deferred Features

Do not add or expand these until the type-safety endpoint is stable:

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

## Non-Negotiable Constraints

- Rocq definitions are the source of truth.
- Generated OCaml extraction artifacts must not be edited manually:
  `fixtures/TypeChecker.ml` and `fixtures/TypeChecker.mli` change only through
  Rocq extraction.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Do not weaken the public type-safety theorem by adding ad hoc public premises.
- Do not try to prove split readiness implies ordinary direct readiness; the
  split gate exists because ordinary direct readiness is too strong for some
  valid direct-receiver-method programs.
- No `Admitted`, `Axiom`, or `Abort` in the final proof path.
- Do not add more theorem variants of the form
  `...with_X_and_Y_and_Z_and_callback_and_bridge...`; package those facts into a
  runtime evidence record instead.

## Key Commands

Before completing type-system-related work, run the relevant checks from the
repository root unless noted:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/diagnose_trait_gates.sh
rg -n "Admitted\.|Axiom|Abort\." rocq/theories
```

When the CLI endpoint changes, regenerate extraction through `cd rocq && make`
before relying on `dune build` or CLI tests.

## Acceptance Criteria

The trait type-safety implementation is complete for this roadmap slice when:

1. `infer_program_env_end2end_big_step_safe_checked_initial_ready` targets the
   active checker endpoint.
2. The CLI accept/reject path uses only an extracted Rocq endpoint.
3. The split endpoint has a non-diagnostic checked-initial runtime-safety theorem.
4. No final runtime theorem depends on the diagnostic no-receiver/direct-ready
   case assumption.
5. Direct-receiver trait programs accepted by the CLI are covered by the public
   checked-initial big-step theorem.
6. Unsupported receiver shapes remain rejected.
7. `plan/trait_new_roadmap.md` and this file agree on the active endpoint,
   proved theorem, remaining blocked receiver forms, promoted test files, and
   deferred features.
