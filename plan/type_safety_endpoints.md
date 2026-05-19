# Type Safety Public Wrappers And Endpoints

This file holds detailed theorem/API endpoint names split out of
`plan/type_safety_roadmap.md`. Use it when an implementation task needs an
existing public wrapper name. The active task order remains in the roadmap.

### Current Public Proof Wrappers

Use these wrappers before adding new theorem shapes:

- Non-direct-call structural route:
  `infer_full_env_alpha_big_step_safe_structural_ready`.
- Direct-call sidecar route:
  `infer_full_env_alpha_big_step_safe_with_direct_call_sidecar_ready`.
- Program-level direct-call sidecar route:
  `check_program_env_alpha_big_step_safe_with_direct_call_sidecar_ready`.
- Validated program-level direct-call sidecar route:
  `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_ready`.
- Validated program-level direct-call sidecar route with environment-level
  preservation readiness:
  `check_program_env_alpha_validated_big_step_safe_with_direct_call_sidecar_env_ready`.
- Proof-only root-shadow validator-ready route:
  `check_program_env_alpha_validated_big_step_safe_with_root_shadow_validator_ready`.
- Executable root-shadow validator route:
  `check_program_env_alpha_validated_root_shadow_big_step_safe`.
- Executable root-shadow validator route with checked initial runtime state:
  `check_program_env_alpha_validated_root_shadow_big_step_safe_checked_initial`.
- Executable root-shadow validator entrypoint:
  `check_program_env_alpha_validated_root_shadow`.
- Executable split provenance/preservation root-shadow validator entrypoint:
  `check_program_env_alpha_validated_root_shadow_provenance`.
- Executable provenance-only root-shadow summary entrypoints:
  `check_fn_root_shadow_provenance_summary` and
  `check_env_root_shadow_provenance_summary`.
- Executable direct-call-local provenance summary entrypoints:
  `check_fn_root_shadow_direct_call_provenance_summary`,
  `check_env_root_shadow_direct_call_provenance_summary`, and
  `check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary`.
- Executable non-capturing function-value provenance summary entrypoint:
  `check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary`.
- Executable non-capturing function-value route with checked initial runtime
  state:
  `check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary_big_step_safe_checked_initial_ready`.
- Executable provenance-summary route with checked initial runtime state:
  `check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready`.
- Executable direct-call-local provenance-summary route with checked initial
  runtime state:
  `check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready`.
- Executable preservation readiness entrypoint:
  `check_env_preservation_ready`.
- Executable initial runtime readiness entrypoint:
  `check_initial_root_runtime_ready`.
- Executable provenance readiness entrypoints:
  `provenance_ready_expr_b`, `provenance_ready_args_b`, and
  `provenance_ready_fields_b`.
- Executable inferred-let elaboration entrypoints:
  `infer_core_env_elab`, `infer_env_elab`, `infer_full_env_elab`,
  `infer_program_env_alpha_elab`, and `check_program_env_alpha_elab`.
- Sidecar package predicates:
  `ordinary_alpha_root_shadow_sidecar_ready`,
  `ordinary_alpha_direct_call_meta_ready`,
  `ordinary_alpha_direct_call_sidecar_ready`,
  `ordinary_alpha_direct_call_validated_sidecar_ready`, and
  `initial_root_runtime_ready_for_fn`.
- Proof-only validator-ready package predicates:
  `env_fns_root_shadow_summary_check_ready`,
  `ordinary_alpha_root_shadow_validator_ready`, and
  `ordinary_alpha_direct_call_validated_root_shadow_validator_ready`.
- Proof-only provenance-summary package predicates:
  `callee_body_root_provenance_ready_at`,
  `callee_body_root_shadow_provenance_ready_at`,
  `callee_body_root_provenance_summary`,
  `callee_body_root_shadow_provenance_summary`,
  `callee_body_root_shadow_direct_call_provenance_summary`,
  `env_fns_root_provenance_summary_evidence`,
  `env_fns_root_shadow_provenance_summary_evidence`, and
  `env_fns_root_shadow_provenance_summary_check_ready`.
- Proof-only direct-call-local provenance-summary package predicate:
  `env_fns_root_shadow_direct_call_provenance_summary_check_ready`.
- Direct-call bridges from uniqueness:
  `direct_call_callee_body_root_shadow_summary_bridge_of_unique` and
  `direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique`.

### Current Endpoints

The top-level name validator route is implemented. `check_program_env_alpha`
remains unchanged, and `check_program_env_alpha_validated` adds a Rocq-side
top-level-name uniqueness check over the alpha-normalized environment. The
sidecar root-shadow validator route is now executable and also runs on the
alpha-normalized environment.

There are two current executable runtime-safety endpoints:

```coq
(* General provenance-summary sidecar route. *)
check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready

(* Direct-call-local provenance-summary sidecar route. *)
check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready
```

Use the general route for ordinary non-direct-call validator work. Use the
direct-call-local route only when the caller body is handled by the localized
direct-call sidecar package.

Current status:

- `ordinary_alpha_root_shadow_sidecar_ready` isolates
  `env_fns_root_shadow_summary_evidence`.
- `ordinary_alpha_direct_call_meta_ready` isolates function-name uniqueness and
  preservation readiness.
- `ordinary_alpha_direct_call_sidecar_ready` remains as the compatibility
  package used by existing public wrappers.
- `ordinary_alpha_direct_call_validated_sidecar_ready` removes function-name
  uniqueness from the explicit sidecar package; uniqueness is derived from
  `check_program_env_alpha_validated`. The `_env_ready` validated wrapper also
  absorbs per-function direct-call readiness from the package's
  environment-level preservation readiness.
- `check_program_env_alpha_validated_root_shadow` is the executable sidecar
  validator route. Its soundness derives
  `ordinary_alpha_direct_call_validated_root_shadow_validator_ready` through
  `check_program_env_alpha_validated_root_shadow_ready`.
- The root-shadow validator checks the alpha-normalized environment with
  `infer_env_roots_shadow_safe`, which mirrors the root checker and adds the
  initializer-side shadow-safe obligations for `ELet` / `ELetInfer`.
- The checker now also exposes an elaboration route for proof-facing execution:
  `infer_core_env_elab` recursively preserves checker behavior while replacing
  successful `ELetInfer` nodes with inferred-type `ELet` nodes, and
  `infer_program_env_alpha_elab` returns an alpha-normalized elaborated
  environment.
- The executable validator route absorbs root-shadow summary evidence and
  environment-level preservation readiness. It still keeps
  `initial_root_runtime_ready_for_fn` explicit.
- The additive provenance-only validator route is implemented for the
  root-shadow summary evidence that does not require `preservation_ready_expr`.
  Its checker soundness theorem is
  `check_env_root_shadow_provenance_summary_ready`, its program-level
  entrypoint is
  `check_program_env_alpha_validated_root_shadow_provenance_summary`, and the
  original preservation-ready root-shadow validator route is unchanged.
- The split validator route keeps provenance and preservation readiness as
  separate executable checks. `check_env_root_shadow_provenance_summary`
  supplies root/shadow provenance evidence, `check_env_preservation_ready`
  supplies `env_fns_preservation_ready`, and
  `check_program_env_alpha_validated_root_shadow_provenance_ready` recombines
  them into the existing validator-ready package for the current runtime safety
  theorem.
- The prefix-store provenance-only direct-call route is now implemented.
  `TypeSafety.v` has `eval_preserves_typing_roots_ready_prefix_mutual`,
  and direct-call cleanup uses it to avoid requiring
  `preservation_ready_expr` for callee bodies. The public runtime theorem
  `eval_preserves_typing_direct_call_roots_provenance_ready` consumes
  root-shadow provenance summary evidence without `env_fns_preservation_ready`.
- The executable direct-call-local provenance route is implemented. A caller
  body that is exactly direct `ECall fname args` can be accepted by
  `check_fn_root_shadow_direct_call_provenance_summary` when the arguments are
  `preservation_ready_args`, the callee has the existing provenance summary,
  and the caller has its local root-shadow exclusions. This deliberately does
  not make general `ECall` or `ECallExpr` part of ordinary/provenance readiness.
  The checked-initial theorem is
  `check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready`.
- `check_program_env_alpha_validated_root_shadow_big_step_safe_checked_initial`
  discharges `initial_root_runtime_ready_for_fn` from the executable
  `check_initial_root_runtime_ready f s`.
- `check_program_env_alpha_validated_root_shadow_provenance_big_step_safe_checked_initial`
  is the strongest split-validator theorem. It is less coupled internally than
  `check_program_env_alpha_validated_root_shadow`, but still rejects programs
  that fail executable preservation readiness.
- `check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready`
  is the strongest provenance-summary theorem. It no longer needs executable
  preservation readiness for callee bodies or the caller expression, but it
  still requires checked initial runtime readiness.
- Initial runtime readiness remains a separate premise, now in executable form.
   - It cannot be derived from `initial_store_for_fn` alone.
   - Reason: `initial_root_env_for_fn` stores parameter origins as `RParam`,
     while runtime references require concrete `RStore` reachability.

The current sidecar contract is fixed. The remaining non-ordinary acceptance
inputs are:

- `check_program_env_alpha_validated_root_shadow_provenance_summary env = true`,
  which is stricter than `check_program_env_alpha env = true` because
  root-shadow provenance summary evidence is still a separate executable
  validator.
- `check_initial_root_runtime_ready f s = true`, which checks the initial
  execution state rather than the program.

Further reductions of the initial-state premise require a stronger
initial-store contract. Do not claim that initial runtime readiness is
eliminated merely because it has an executable validator.

Future work:

- Decide whether the OCaml CLI should expose the root-shadow sidecar validator
  as an optional diagnostic/check mode. The ordinary checker contract remains
  unchanged unless that is explicitly redesigned.
- Design an executable validator or strengthened setup invariant for
  `initial_root_runtime_ready_for_fn`.
- Bring the safety-validator route closer to the ordinary checker accepted
  range by following the Next Implementation Order above.
- Continue narrowing the executable safety validator's false negatives against
  the ordinary-checker accepted fixtures in `tests/valid/type_safety_ready_gap/`.
  The provenance-summary route no longer needs the callee-body
  `env_fns_preservation_ready` dependency or the caller
  `preservation_direct_call_ready_expr` premise.
- General `ECallExpr` work must proceed through the staged order in
  `Next Implementation Order`: first-class functions without captures, MVP
  immutable unrestricted closures, captured references/lifetimes, borrow
  capture syntax, mutable environments, then affine/linear captures.
