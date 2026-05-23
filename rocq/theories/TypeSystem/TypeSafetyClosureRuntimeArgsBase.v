From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootedPackages.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_make_closure_captured_call_runtime_args_ready_core :
  forall env Ω captured fdef fcall used' s_args vs R_args Σ_args
      arg_roots,
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)).
Proof.
  intros env Ω captured fdef fcall used' s_args vs R_args Σ_args
    arg_roots Hrename Hframe_params_ready Hstore_args Hargs_fdef_frame
    Hvalue_roots.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready
      env captured (empty_root_env_for_store captured) s_args R_args
      (fn_params fcall) vs Ω arg_roots Hframe_ready Hnodup_fcall
      Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - split; assumption.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_in_frame_core :
  forall env Ω captured Rcap fdef fcall used' s_args vs R_args Σ_args
      arg_roots,
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    captured_call_frame_params_ready_in_frame env captured
      Rcap s_args R_args (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
    captured_call_frame_params_ready_in_frame env captured
      Rcap s_args R_args (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ R_args)).
Proof.
  intros env Ω captured Rcap fdef fcall used' s_args vs R_args Σ_args
    arg_roots Hrename Hframe_params_ready Hstore_args Hargs_fdef_frame
    Hvalue_roots.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready_in_frame
      env captured Rcap s_args R_args (fn_params fcall) vs Ω arg_roots
      Hframe_ready Hnodup_fcall Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - split; assumption.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_core :
  forall env Ω fname captured fdef fcall used' s_args_hidden s_args vs
      R_args Σ_args arg_roots x T,
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω s_args vs (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
    ~ In x (store_names s_args) ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)).
Proof.
  intros env Ω fname captured fdef fcall used' s_args_hidden s_args vs
    R_args Σ_args arg_roots x T Hhidden Hrename Hframe_hidden
    Hframe_params_ready Hstore_args Hargs_fdef_sargs Hvalue_roots
    Hfresh_s_args.
  assert (Hshadow_hidden_frame :
    store_no_shadow (captured ++ s_args_hidden)).
  { unfold captured_call_frame_ready in Hframe_hidden.
    destruct Hframe_hidden as [_ [_ [Hshadow_hidden_frame _]]].
    exact Hshadow_hidden_frame. }
  pose proof
    (captured_hidden_frame_args_values_have_types
      env captured s_args_hidden s_args Ω vs (fn_params fdef) x T
      (VClosure fname captured) Hhidden Hshadow_hidden_frame Hfresh_s_args
      Hargs_fdef_sargs) as Hargs_fdef_hidden.
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready
      env captured (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_params fcall) vs Ω arg_roots
      Hframe_hidden Hnodup_fcall Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - exact Hframe_params_ready.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_in_frame_core :
  forall env Ω fname captured Rcap fdef fcall used' s_args_hidden s_args vs
      R_args Σ_args arg_roots x T hidden_roots,
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    captured_call_frame_ready_in_frame env captured Rcap s_args_hidden
      (root_env_add x hidden_roots R_args) ->
    captured_call_frame_params_ready_in_frame env captured Rcap
      s_args_hidden (root_env_add x hidden_roots R_args)
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω s_args vs (fn_params fdef) ->
    Forall2 value_roots_within arg_roots vs ->
    ~ In x (store_names s_args) ->
    captured_call_frame_params_ready_in_frame env captured Rcap
      s_args_hidden (root_env_add x hidden_roots R_args)
      (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ root_env_add x hidden_roots R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ root_env_add x hidden_roots R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (Rcap ++ root_env_add x hidden_roots R_args)).
Proof.
  intros env Ω fname captured Rcap fdef fcall used' s_args_hidden s_args vs
    R_args Σ_args arg_roots x T hidden_roots Hhidden Hrename Hframe_hidden
    Hframe_params_ready Hstore_args Hargs_fdef_sargs Hvalue_roots
    Hfresh_s_args.
  assert (Hshadow_hidden_frame :
    store_no_shadow (captured ++ s_args_hidden)).
  { unfold captured_call_frame_ready_in_frame in Hframe_hidden.
    destruct Hframe_hidden as [_ [_ [Hshadow_hidden_frame _]]].
    exact Hshadow_hidden_frame. }
  pose proof
    (captured_hidden_frame_args_values_have_types
      env captured s_args_hidden s_args Ω vs (fn_params fdef) x T
      (VClosure fname captured) Hhidden Hshadow_hidden_frame Hfresh_s_args
      Hargs_fdef_sargs) as Hargs_fdef_hidden.
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh_fcall :
    params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (captured_call_bind_params_call_param_root_env_ready_in_frame
      env captured Rcap s_args_hidden
      (root_env_add x hidden_roots R_args)
      (fn_params fcall) vs Ω arg_roots Hframe_hidden Hnodup_fcall
      Hfresh_fcall Hargs_fcall Hvalue_roots)
    as [Hroots_bind [Hshadow_bind [Hrn_bind Hcover_bind]]].
  split.
  - exact Hframe_params_ready.
  - split; [exact Hstore_args |].
    split; [exact Hargs_fcall |].
    split; [exact Hvalue_roots |].
    split; [exact Hroots_bind |].
    split; [exact Hshadow_bind |].
    split; [exact Hrn_bind | exact Hcover_bind].
Qed.
