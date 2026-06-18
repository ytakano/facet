From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerAssocRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull CheckerAlphaElabProgram CheckerRootSidecars CheckerExamplesRootSidecars CheckerRawElab.
Export CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerAssocRootsShadow CheckerProgram CheckerExamplesBasic CheckerBorrow CheckerFull CheckerAlphaElabProgram CheckerRootSidecars CheckerExamplesRootSidecars CheckerRawElab.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
Extraction "../fixtures/TypeChecker.ml"
  infer_core_env_roots infer_env_roots infer_full_env_roots
  infer_env infer_full_env check_program_env
  infer_core_env_elab infer_env_elab infer_full_env_elab
  infer_program_env_alpha_elab check_program_env_alpha_elab
  elaborate_raw_expr elaborate_raw_global_env
  alpha_normalize_global_env normalize_assoc_ty normalize_assoc_global_env
  normalize_assoc_raw_fn resolve_trait_method_impl
  resolve_trait_method_def check_program_env_alpha
  check_program_env_alpha_validated
  preservation_ready_expr_b preservation_ready_args_b
  preservation_ready_fields_b
  provenance_ready_expr_b provenance_ready_args_b
  provenance_ready_fields_b
  infer_core_env_state_fuel_roots_shadow_safe
  infer_core_env_roots_shadow_safe infer_env_roots_shadow_safe
  infer_fn_value_call_expr_assoc_shadow_safe
  infer_core_env_roots_shadow_safe_checked_assoc
  infer_env_roots_shadow_safe_checked_assoc infer_full_env_roots_checked_assoc
  check_fn_root_shadow_summary check_env_root_shadow_summary
  check_fn_root_shadow_captured_call_store_safe_summary_absent
  check_env_root_shadow_captured_call_store_safe_summary_absent
  check_fn_root_shadow_provenance_summary
  check_env_root_shadow_provenance_summary
  direct_call_ready_expr_b
  check_fn_root_shadow_direct_call_provenance_summary
  check_env_root_shadow_direct_call_provenance_summary
  check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
  check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary
  check_env_root_shadow_no_receiver_component_body_summary_provider_check
  check_env_preservation_ready
  check_program_env_alpha_validated_root_shadow
  check_program_env_alpha_validated_root_shadow_provenance_summary
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
  check_program_env_alpha_validated_root_shadow_provenance
  infer_fn_env_end2end infer_program_env_end2end check_program_env_end2end
  infer_fn_env_end2end_assoc infer_program_env_end2end_assoc
  check_program_env_end2end_assoc
  infer_fn_env_end2end_assoc_direct_receiver_base
  infer_program_env_end2end_assoc_direct_receiver_base
  check_program_env_end2end_assoc_direct_receiver_base
  infer_fn_env_end2end_strict_exact_closure
  infer_program_env_end2end_strict_exact_closure
  check_program_env_end2end_strict_exact_closure
  infer_fn_env_end2end_assoc_strict_exact_closure
  infer_program_env_end2end_assoc_strict_exact_closure
  check_program_env_end2end_assoc_strict_exact_closure
  check_env_end2end_direct_receiver_ready
  check_fn_root_shadow_direct_receiver_method_present
  check_env_root_shadow_direct_receiver_method_present
  check_env_end2end_direct_receiver_mixed_ready
  infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver
  check_program_env_end2end_assoc_strict_exact_closure_direct_receiver
  infer_program_env_end2end_assoc_direct_receiver_mixed
  check_program_env_end2end_assoc_direct_receiver_mixed
  infer_program_env_end2end_assoc_direct_receiver_base_mixed
  check_program_env_end2end_assoc_direct_receiver_base_mixed
  infer_program_env_end2end_assoc_direct_receiver_base_combined
  check_program_env_end2end_assoc_direct_receiver_base_combined
  infer_program_env_end2end_assoc_direct_receiver_base_direct_component
  check_program_env_end2end_assoc_direct_receiver_base_direct_component
  infer_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed
  check_program_env_end2end_assoc_strict_exact_closure_direct_receiver_mixed.
