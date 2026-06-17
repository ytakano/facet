# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Traits, impls, associated types, trait methods, method-local type parameters,
  generic-trait impl remapping, and associated type projections are parsed,
  lowered, and checked through the extracted Rocq checker. Associated
  projections and explicit UFCS method targets reject lifetime arguments in
  trait refs at checker boundaries. Impl method bodies are elaborated to hidden
  functions and checked even when uncalled.
- Method calls use receiver-first prefix UFCS forms:
  `(<Ty as Trait>::method receiver args...)` and
  `(Trait::method receiver args...)`. Dot syntax remains rejected for this
  phase.
- Short UFCS currently accepts receiver types known before checker execution:
  function parameters, typed literals, immutable pure local literals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors whose store-safe argument evidence is checked in Rocq.
- Still-gated receiver forms are field-bearing struct literals,
  payload-bearing enum constructors, direct-call receivers, generic direct-call
  receivers, non-pure inferred locals, and general annotated locals.
- The OCaml CLI uses `infer_program_env_end2end_assoc_direct_receiver_mixed` as
  its only extracted checker authority, with no fallback acceptance path. Public
  checker soundness aliases target this assoc-base mixed endpoint. The public
  runtime theorem `infer_program_env_end2end_big_step_safe_checked_initial_ready`
  still targets the strict mixed endpoint.
- Proof infrastructure for direct-call receivers now includes active-mixed
  branch splits, no-receiver/direct-ready bridges, receiver-method absence
  facts, local-bounds route helpers, exact-body route/package bridges, and
  proof-only endpoints for stronger gates. These endpoints are useful for proof
  diagnostics but are not behavior-compatible replacements for the active CLI
  authority.
- The remaining activation gap is proof-side: the active mixed no-receiver
  branch exposes only receiver-method absence plus a disjunctive
  captured-or-component summary. Existing runtime paths still need either
  global synthetic direct-call summary evidence, a full component-summary check,
  or strict exact readiness. Those stronger gates rejected broad existing valid
  coverage when tried as active authorities.
- Associated type defaults, equality constraints, and `deriving` are reserved
  for future surface forms. Provisional syntax for them is explicitly rejected
  with parser diagnostics.

## Remaining Tasks

1. Finish direct-call receiver activation.
   - Retarget `infer_program_env_end2end_big_step_safe_checked_initial_ready` to
     `infer_program_env_end2end_assoc_direct_receiver_mixed` without adding
     OCaml fallback logic or weakening the public theorem with a new premise.
   - Derive a behavior-compatible no-receiver evidence provider, or an
     equivalent public-premise-free lift, from the active mixed endpoint.
   - Add positive direct-call receiver UFCS tests only after the active
     extracted checker accepts them through the verified endpoint. Keep existing
     direct-call receiver safety-gate tests invalid until that switch lands.

2. Extend receiver coverage conservatively.
   - Keep receiver-first prefix calls as the canonical surface syntax.
   - Add the remaining receiver forms only when Rocq checker summaries and
     safety proofs provide store/root-safe evidence for each shape.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Maintain assoc-aware trait behavior.
   - Preserve assoc-aware normalization at checker boundaries rather than by
     rewriting whole raw ASTs.
   - Keep parser/desugar name resolution separate from trait solving and final
     checker authority.

## Unresolved Blockers

- Strict direct-receiver, absence-mixed, synthetic-mixed, and component-mixed
  endpoint trials rejected broad existing valid coverage with
  `ErrEndToEndSafetyGateFailed`; they remain proof/diagnostic infrastructure,
  not active authorities.
- The active mixed no-receiver branch does not currently imply the evidence
  required by available runtime paths. Receiver-method target absence does not
  imply captured-summary absence, and disjunctive captured-or-component summary
  evidence does not provide component synthetic route evidence for captured
  functions.
- The assoc direct-receiver-base endpoint accepts the basic direct-call receiver
  fixture, but it is not the active CLI authority and has not been connected to
  the public runtime theorem without stronger gates.

## Key Decisions

- Rocq definitions are the source of truth. Generated OCaml extraction artifacts
  are regenerated from Rocq and are not edited manually.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Associated type defaults and equality constraints are out of scope for the
  current implementation pass.
- Dot method calls remain syntax-level rejected until they can desugar to the
  same receiver-first prefix form before Rocq checking.
- Future deriving must expand to ordinary impl declarations validated by the
  extracted checker; no parser-only generated acceptance path is allowed.

## Required Checks

For type-system or checker-facing implementation tasks, run:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
```

For docs-only roadmap maintenance, `git diff --check` is sufficient unless the
edit changes stated behavior or proof obligations. The final marker search must
not introduce new proof holes or debug leftovers when Rocq files are touched.
Existing legacy proof-script selector matches should be called out explicitly if
they remain unrelated to the change.
