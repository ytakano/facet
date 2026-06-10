From Facet.TypeSystem Require Import Syntax RootProvenance RuntimeTyping
  TypeSafetyRootFacts TypeSafetyHiddenFrameBaseCore EnvRuntimeShadowSummaryFacts.

Record generic_direct_call_runtime_package
    (env : global_env) (s s' : store) (ret : value)
    (Sigma_args : sctx) (R_args : root_env) (arg_roots : list root_set)
    (ret_ty : Ty) : Prop := {
  generic_direct_call_package_store :
    store_typed_prefix env s' Sigma_args;
  generic_direct_call_package_value :
    value_has_type env s' ret ret_ty;
  generic_direct_call_package_preserved :
    store_ref_targets_preserved env s s';
  generic_direct_call_package_roots :
    store_roots_within R_args s';
  generic_direct_call_package_value_roots :
    value_roots_within (root_sets_union arg_roots) ret;
  generic_direct_call_package_shadow :
    store_no_shadow s';
  generic_direct_call_package_root_shadow :
    root_env_no_shadow R_args;
  generic_direct_call_package_roots_named :
    root_env_store_roots_named R_args s';
  generic_direct_call_package_keys_named :
    root_env_store_keys_named R_args s';
  generic_direct_call_package_closure_summary :
    store_function_closure_targets_summary env s'
}.
