# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Trait and impl items are parsed, lowered into Rocq/extracted environments,
  and checked for duplicate, missing, extra, and mismatched associated types and
  methods. Impl method bodies are elaborated to hidden functions and checked by
  the extracted checker even when the method is not called.
- Method-local type parameters are supported for trait and impl methods,
  including method-local bounds and generic-trait impl remapping. Method-local
  lifetime generics remain deferred and are rejected by tests.
- Method calls use the ordinary Facet prefix call shape: `(callee args...)`.
  Explicit UFCS is `(<Ty as Trait>::method receiver args...)`; short UFCS is
  `(Trait::method receiver args...)`. The receiver is always the first
  argument. Dot method-call syntax is intentionally rejected in this phase.
- Short UFCS accepts receiver types known before checker execution: function
  parameters, syntactically typed literals, and immutable pure local literals
  after receiver-let elimination. Struct, enum, direct-call, generic direct-call,
  non-pure inferred local, and general annotated local receivers remain gated by
  tests until store/root-safe checker evidence is available.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested.
- Associated projections are still normalized by extracted Rocq raw/global-env
  normalization before ordinary compatibility checks. OCaml no longer performs
  a separate associated-type normalization pass.
- Rocq has an env-aware associated compatibility layer:
  `ty_compatible_assoc`, `ty_compatible_assoc_b`, and
  `ty_compatible_assoc_checked`. The checked-to-Prop bridge is proved via
  `ty_compatible_assoc_checked_sound` while keeping `normalize_assoc_ty` opaque
  at proof boundaries.
- `AssocCallTypingBoundary`, `AssocEnvCallTypingBoundary`, and
  `AssocEnvCallStructuralBoundary` define lightweight Prop-level call
  boundaries around associated-compatible argument typing for direct,
  function-value, explicit generic function-value, HRT/type-forall/mixed-forall,
  make-closure, and root-aware call paths, so future checker-facing wiring has
  targets that mention `global_env` without changing `typed` yet. Direct,
  generic direct-call, non-generic function-value, explicit generic
  function-value, HRT, inferred/elaborating type-forall, and mixed-forall
  helper results now bridge to the env/root structural call boundary, and
  root direct, generic direct, function-value, explicit generic function-value,
  type-forall, mixed-forall, HRT, and make-closure helper results also lift
  into the checked root wrapper.
- Helper-level associated compatibility soundness is available for
  `check_args_assoc`, `check_arg_tys_assoc`, `infer_args_collect`, direct calls,
  function-value calls, explicit generic function-value calls,
  HRT/type-forall/mixed-forall calls, trait method signatures and resolution,
  values, function bodies, struct fields, enum
  payloads, env/root argument collectors, field collectors, and payload
  collectors. Env/root associated call boundaries also preserve store binding
  shape, and the roots boundary projects to the env-structural boundary. A
  checker-facing wrapper boundary now admits either existing structural typing
  or an associated call boundary while preserving the same store-shape
  invariants. Core, expression, function-level, root, shadow-safe root,
  and checked shadow-safe root checker soundness have entry theorems into
  these wrappers for the current checker behavior, including function-level
  checked full-env roots and end-to-end program entrypoints. Function-level
  checked assoc root boundaries, end-to-end program entries, and checked
  function environments now project to structural assoc boundaries for
  safety-side consumers. Assoc root argument, call, root, and checked-root
  boundaries now preserve `root_env_no_shadow`, matching another invariant that
  root-safety consumers require. Assoc root value and argument typing now bridge
  to the `root_env_ctx_roots_named` / root-set named invariants used by
  roots-ready proofs. Ordinary
  compatibility is not treated as an implicit proof of associated
  compatibility; call-site wiring must dispatch through the env-aware assoc
  helpers at each checker path being proved. The ctx/env checker's top-level
  direct/generic direct calls, function-value calls, explicit generic
  function-value calls, HRT calls, inferred type-forall calls, and
  mixed-forall calls now dispatch through the env-aware associated call
  helpers; root/shadow checker call sites remain on ordinary compatibility.
  A direct root checker wiring attempt reaches the expected proof boundary:
  assoc-compatible calls no longer prove the primary `typed_env_roots` relation,
  so wiring must wait until preservation/root safety consumes the checked assoc
  wrapper instead of the ordinary roots relation.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  deriving syntax is rejected explicitly, and `deriving` is reserved as a
  keyword.

## Remaining Tasks

1. Move associated compatibility through the checker call-site boundary.
   - Use the proved env/root assoc call boundaries and checker-facing wrapper
     boundaries as the target for assoc-aware call-site soundness. Do not widen
     the primary `typed_env_structural` or `typed_env_roots` relations until
     preservation and root-safety obligations are explicitly covered.
   - Wire checker call sites from ordinary `check_args` / `check_arg_tys` to
     the env-aware assoc helpers only after the consuming soundness theorem no
     longer requires the primary ordinary compatibility relation.
   - Preserve the required end-to-end checker soundness theorem names:
     `infer_program_env_end2end_sound`, `check_program_env_end2end_sound`, and
     `infer_program_env_end2end_big_step_safe_checked_initial_ready`.
   - Remove pre-compatibility normalization once checker-facing assoc
     compatibility is the accepted path and tests still cover accepted concrete
     projections and rejected mismatches.

2. Finish UFCS receiver hardening.
   - Keep the canonical surface syntax as prefix calls with receiver-first
     arguments.
   - Add remaining receiver shapes only when the checker and safety proofs have
     store/root-safe summary evidence. Do not add checker-only acceptance paths.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

3. Keep deriving deferred but well specified.
   - Future deriving should expand to ordinary impl declarations validated by
     the extracted checker.
   - Start with structural traits whose generated bodies are deterministic.
   - Defer deriving for traits with associated type defaults or equality
     constraints until those features exist.

## Key Decisions

- Rocq definitions are the source of truth. Generated OCaml extraction artifacts
  are not edited manually.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Associated type defaults and equality constraints are out of scope for the
  current implementation pass.
- Dot method calls remain syntax-level rejected until they can desugar to the
  same receiver-first prefix form before Rocq checking.

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

The final search must not introduce new proof holes or debug leftovers. Existing
legacy proof-script selector matches should be called out explicitly if they
remain unrelated to the change.
