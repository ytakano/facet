# Unused Artifact Classification

First batch source: `dpdusage unused-analysis.dpd`.

First-pass candidates are classified below. Deletions are recorded only after
separate source, fixture, build, and proof-hole checks.

## KEEP_EXTRACTION_ROOT

OCaml extraction roots from `TypeChecker.v`:

`infer_core_env_roots`, `infer_env_roots`, `infer_full_env_roots`, `infer_env`,
`infer_full_env`, `infer_full`, `check_program_env`, `infer_core_env_elab`,
`infer_env_elab`, `infer_full_env_elab`, `infer_program_env_alpha_elab`,
`check_program_env_alpha_elab`, `elaborate_raw_expr`,
`elaborate_raw_global_env`, `alpha_normalize_global_env`,
`check_program_env_alpha`, `check_program_env_alpha_validated`,
`preservation_ready_expr_b`, `preservation_ready_args_b`,
`preservation_ready_fields_b`, `provenance_ready_expr_b`,
`provenance_ready_args_b`, `provenance_ready_fields_b`,
`infer_core_env_state_fuel_roots_shadow_safe`,
`infer_core_env_roots_shadow_safe`, `infer_env_roots_shadow_safe`,
`check_fn_root_shadow_summary`, `check_env_root_shadow_summary`,
`check_fn_root_shadow_provenance_summary`,
`check_env_root_shadow_provenance_summary`, `direct_call_ready_expr_b`,
`check_fn_root_shadow_direct_call_provenance_summary`,
`check_env_root_shadow_direct_call_provenance_summary`,
`check_env_preservation_ready`,
`check_program_env_alpha_validated_root_shadow`,
`check_program_env_alpha_validated_root_shadow_provenance_summary`,
`check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary`,
`check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary`,
`check_program_env_alpha_validated_root_shadow_provenance`,
`infer_fn_env_end2end`, `infer_program_env_end2end`,
`check_program_env_end2end`.

## KEEP_PUBLIC_API

Public soundness and safety theorem roots:

`infer_program_env_end2end_sound`, `check_program_env_end2end_sound`,
`infer_program_env_end2end_big_step_safe_checked_initial_ready`.

Other public theorem candidates from the first batch:

`check_program_env_alpha_checked_structural`, `infer_affine_value_at_most_once`,
`infer_checked_fn_linear_usage`, `infer_direct_sound`, `check_program_sound`,
`check_make_closure_captures_exact_ctx_sound`, `borrow_check_complete`,
`borrow_ok_args_mut`, `borrow_check_sound`, `capture_ref_free_ty_b_sound`.

Raw elaboration / OCaml interface constructor:

`MkRawFnDef`.

Checker/proof-facing closure and writable-chain facts:

`check_make_closure_captures_sctx`,
`place_resolved_write_mutable_chain_b_sound`,
`place_resolved_write_mutable_chain_shape`,
`place_resolved_write_mutable_chain_instantiate`,
`place_resolved_write_mutable_chain_equiv`.

Executable and proof-facing checker helpers with real callers:

`params_names_nodup_b`, `top_level_names_unique_b_fn_names_nodup`,
`infer_core_env_fuel`.

Proof-facing checker and root-shadow facts with real proof callers:

`check_expr_root_shadow_store_safe_summary`, `root_env_*`,
`match_payload_params_names`, `usage_sub_bool_complete`, `ctx_remove_b_eq`,
`ctx_add_b_eq`, `ty_core_eqb_subst_type_params_ty`, and related
`CheckerSoundness` helper facts.

## KEEP_DOCUMENTATION

TypeChecker example and ready-gap matrix entries ending in accepts, rejects, or
ok-style names document checker behavior and regression intent. Examples:

`ready_gap_matrix_*_accepts`, `ready_gap_matrix_*_rejects`,
`*_checker_accepts`, `*_checker_rejects`, `*_summary_accepts`,
`*_summary_rejects`, `*_validator_rejects`, `infer_core_env_*_ok`,
`infer_core_env_*_accepted`, `infer_core_env_*_rejected`,
`*_ready_gap_let`, `*_shared_ref_capture_*`, `*_moved_field_*`,
`*_usage_after_args`, `*_linear_not_generated`.

Borrow checker behavioral regression examples:

`borrow_check_env_prefix_fields_conflict`,
`borrow_check_env_sibling_fields_do_not_conflict`.

## KEEP_AUTOMATION

Generated induction, recursion, and scheme artifacts:

`raw_expr_ind`, `raw_expr_rec`, `raw_expr_sind`, `infer_error_ind`,
`infer_error_rec`, `infer_error_sind`, `capture_ref_free_ty_ind`,
`capture_ref_free_ty_sind`, `path_borrow_entry_ind`,
`path_borrow_entry_rec`, `path_borrow_entry_sind`, `infer_result_ind`,
`infer_result_rec`, `infer_result_sind`,
`place_resolved_write_mutable_chain_ind`,
`place_resolved_write_mutable_chain_sind`.

## KEEP_FUTURE_WORK

Exploratory checker examples or behavioral matrix entries may become tests or
documentation anchors before any deletion pass:

`capture_ref_free_ty_b_rejects_closure_value`,
`capture_ref_free_ty_b_rejects_ref_struct`,
`capture_ref_free_ty_b_accepts_plain_struct`,
`ty_ref_free_b_rejects_closure_value`,
`ty_compatible_b_*`, `supported_type_generic_function_value_call_callee_ty_b`.

## INVESTIGATE

No first-pass candidates remain in INVESTIGATE.

## DELETE_NOW / Deleted

`field_names_unique_b`: deleted. Private checker helper with no callers beyond
self-recursion and no extracted fixture occurrence.

`trait_impl_error`: deleted. Private wrapper around
`trait_impl_error_with_args`, no callers outside classification, no fixture
occurrence.

`infer_call_type_args`: deleted. Private wrapper superseded by
`infer_call_type_args_expected`, no callers outside classification, no fixture
occurrence.

`infer_args`: deleted. Old top-level argument checker superseded by
`infer_args_collect`, with no callers outside classification and no fixture
occurrence.

`infer_type_forall_call_no_env`: deleted. Unused no-env variant superseded
by env-aware helpers, no callers, no fixture occurrence.

`duplicate_param_name_none_nodup_params_ctx_suffix`: deleted. Unused suffix
variant; the base and prefix lemmas cover current callers.
