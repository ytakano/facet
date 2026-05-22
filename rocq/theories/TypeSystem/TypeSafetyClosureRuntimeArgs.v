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

Lemma eval_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_package_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args vs R_args Σ_args arg_roots env_lt captured_tys,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    captured_call_frame_params_ready_in_frame env captured
      (capture_store_root_env captured) s_args R_args
      (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++ R_args)).
Proof.
  intros Htyping Hroots_mutual Hnames Hkeys env Ω n R Σ args fname
    captures captured fdef fcall used' s s_args vs R_args Σ_args
    arg_roots env_lt captured_tys Hstore Hroots Hshadow Hrn Hnamed Hkeys0
    Heval_make Hlookup Heval_args Hrename Hcheck Hnodup_caps Hready_args
    Htyped_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (proj1 (proj2 Htyping)
              env s args s_args vs Heval_args Ω n Σ
              (fn_params fdef) Σ_args Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (fn_params fdef) Σ_args R_args arg_roots Htyped_args))
    as [Hstore_args [Hargs_fdef_sargs Hpres_args]].
  pose proof (proj1 (proj2 Hroots_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hroots
              Hshadow Hrn Htyped_args) as Hrooted_args.
  pose proof (rooted_args_store_roots _ _ _ _ Hrooted_args)
    as Hroots_args'.
  pose proof (rooted_args_value_roots _ _ _ _ Hrooted_args)
    as Hvalue_roots.
  pose proof (rooted_args_store_no_shadow _ _ _ _ Hrooted_args)
    as Hshadow_args.
  pose proof (rooted_args_root_env_no_shadow _ _ _ _ Hrooted_args)
    as Hrn_args.
  pose proof (proj1 (proj2 Hnames)
              env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hnamed Htyped_args) as Hnames_args'.
  pose proof (proj1 (proj2 Hkeys)
              env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hkeys0 Htyped_args) as Hkeys_args'.
  destruct Hnames_args' as [Hnamed_args _].
  dependent destruction Heval_make.
  assert (Hsame : fdef0 = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef0.
  pose proof
    (check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store
      env Ω s Σ captures (fn_captures fdef) env_lt captured_tys
      Hstore Hcheck) as Hfresh_caps.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s_args vs Heval_args Hready_args)
    as Hargs_names.
  assert (Hstore_disj :
    forall x, In x (store_names captured) -> ~ In x (store_names s_args)).
  { intros x Hin_captured Hin_args.
    rewrite (copy_capture_store_as_store_names captures (fn_captures fdef)
               s captured H0) in Hin_captured.
    rewrite Hargs_names in Hin_args.
    exact (Hfresh_caps x Hin_captured Hin_args). }
  assert (Hpres_tail :
    store_ref_targets_preserved env s_args (captured ++ s_args)).
  { apply store_ref_targets_preserved_app_right.
    intros x Hin.
    apply store_lookup_not_in_names.
    intros Hin_captured.
    eapply Hstore_disj; eassumption. }
  assert (Hpres : store_ref_targets_preserved env s (captured ++ s_args)).
  { eapply store_ref_targets_preserved_trans; eassumption. }
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready_auto_with_env
      env Ω s Σ fname captures captured fdef fcall used' args s_args vs
      R_args env_lt captured_tys Hstore Hpres
      (Eval_MakeClosure env s fname captures captured fdef Hlookup H0)
      Hlookup Hrename Hcheck Hnodup_caps Hready_args Heval_args
      Hroots_args' Hshadow_args Hrn_args Hnamed_args Hkeys_args')
    as Hframe_params_ready.
  pose proof (proj1 Hframe_params_ready) as Hframe_ready.
  pose proof
    (captured_call_frame_args_values_have_types_in_frame
      env captured (capture_store_root_env captured) s_args R_args Ω vs
      (fn_params fdef) Hframe_ready Hargs_fdef_sargs)
    as Hargs_fdef_frame.
  exact (eval_make_closure_captured_call_runtime_args_ready_in_frame_core
    env Ω captured (capture_store_root_env captured) fdef fcall used'
    s_args vs R_args Σ_args arg_roots Hrename Hframe_params_ready
    Hstore_args Hargs_fdef_frame Hvalue_roots).
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_parts_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args vs R_args Σ_args arg_roots captured_tys,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
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
  intros Htyping_expr Htyping_args Htyping_fields Hroots_expr Hroots_args
    Hroots_fields Hnames_expr Hnames_args Hnames_fields Hkeys_expr
    Hkeys_args Hkeys_fields env Ω n R Σ args fname captures captured fdef
    fcall used' s s_args vs R_args Σ_args arg_roots captured_tys Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Heval_make Hlookup Heval_args Hrename
    Hcheck Hnodup_caps Hready_args Htyped_args.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (Htyping_args env s args s_args vs Heval_args Ω n Σ
              (fn_params fdef) Σ_args Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (fn_params fdef) Σ_args R_args arg_roots Htyped_args))
    as [Hstore_args [Hargs_fdef_sargs _]].
  destruct (Hroots_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hroots
              Hshadow Hrn Htyped_args)
    as [Hroots_args' [Hvalue_roots [Hshadow_args Hrn_args]]].
  pose proof (Hnames_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hnamed Htyped_args) as Hnames_args'.
  pose proof (Hkeys_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hkeys Htyped_args) as Hkeys_args'.
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready_auto
      env Ω s Σ fname captures captured fdef fcall used' args s_args vs
      R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck
      Hnodup_caps Hready_args Heval_args Hroots_args' Hshadow_args Hrn_args
      (proj1 Hnames_args') Hkeys_args') as Hframe_params_ready.
  pose proof (proj1 Hframe_params_ready) as Hframe_ready.
  pose proof
    (captured_call_frame_args_values_have_types
      env captured (empty_root_env_for_store captured) s_args R_args Ω vs
      (fn_params fdef) Hframe_ready Hargs_fdef_sargs)
    as Hargs_fdef_frame.
  exact (eval_make_closure_captured_call_runtime_args_ready_core
    env Ω captured fdef fcall used' s_args vs R_args Σ_args arg_roots
    Hrename Hframe_params_ready Hstore_args Hargs_fdef_frame Hvalue_roots).
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_parts_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots captured_tys x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
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
  intros Htyping_expr Htyping_args Htyping_fields Hroots_expr Hroots_args
    Hroots_fields Hnames_expr Hnames_args Hnames_fields Hkeys_expr
    Hkeys_args Hkeys_fields env Ω n R Σ args fname captures captured fdef
    fcall used' s s_args_hidden s_args vs R_args Σ_args arg_roots
    captured_tys x T Hstore Hroots Hshadow Hrn Hnamed Hkeys Hlookup Hcopy
    Hhidden Heval_args Hrename Hcheck Hnodup_caps Hready_args Htyped_args
    Hfresh_s Hfresh_captured.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (Htyping_args env s args s_args vs Heval_args Ω n Σ
              (fn_params fdef) Σ_args Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (fn_params fdef) Σ_args R_args arg_roots Htyped_args))
    as [Hstore_args [Hargs_fdef_sargs _]].
  destruct (Hroots_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hroots
              Hshadow Hrn Htyped_args)
    as [Hroots_args' [Hvalue_roots [Hshadow_args Hrn_args]]].
  pose proof (Hnames_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hnamed Htyped_args) as Hnames_args'.
  pose proof (Hkeys_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hkeys Htyped_args) as Hkeys_args'.
  destruct Hnames_args' as [Hnamed_args Harg_roots_named].
  assert (Hfresh_s_args : ~ In x (store_names s_args)).
  { eapply eval_args_store_names_fresh; eassumption. }
  assert (Hlookup_args_x : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hclosure_roots : value_roots_within [] (VClosure fname captured)).
  { eapply copied_captured_closure_roots_empty;
      [ exact Hstore | exact Hlookup | exact Hnodup_caps | exact Hcopy
      | exact Hcheck ]. }
  pose proof
    (copy_capture_store_as_captured_call_frame_ready
      Ω env s Σ captures (fn_captures fdef) captured captured_tys args
      s_args vs R_args Hstore Hnodup_caps Hcheck Hcopy Hready_args
      Heval_args Hroots_args' Hshadow_args Hrn_args Hnamed_args Hkeys_args')
    as Hframe_ready.
  assert (Hframe_hidden :
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args)).
  { subst s_args_hidden.
    eapply captured_call_frame_ready_store_add_right; eassumption. }
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready
      env Ω s Σ fname captures captured fdef fcall used'
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) captured_tys Hstore
      (Eval_MakeClosure env s fname captures captured fdef Hlookup Hcopy)
      Hlookup Hrename Hcheck Hframe_hidden)
    as Hframe_params_ready.
  exact (eval_let_make_closure_captured_call_runtime_args_ready_core
    env Ω fname captured fdef fcall used' s_args_hidden s_args vs R_args
    Σ_args arg_roots x T Hhidden Hrename Hframe_hidden
    Hframe_params_ready Hstore_args Hargs_fdef_sargs Hvalue_roots
    Hfresh_s_args).
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_parts_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') ->
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s') ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots env_lt
      captured_tys x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
    captured_call_frame_params_ready_in_frame env captured
      (capture_store_root_env captured) s_args_hidden
      (root_env_add x (root_sets_union (capture_store_root_sets captured))
        R_args) (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x
            (root_sets_union (capture_store_root_sets captured)) R_args)).
Proof.
  intros Htyping_expr Htyping_args Htyping_fields Hroots_expr Hroots_args
    Hroots_fields Hnames_expr Hnames_args Hnames_fields Hkeys_expr
    Hkeys_args Hkeys_fields env Ω n R Σ args fname captures captured fdef
    fcall used' s s_args_hidden s_args vs R_args Σ_args arg_roots env_lt
    captured_tys x T Hstore Hroots Hshadow Hrn Hnamed Hkeys Hlookup Hcopy
    Hhidden Heval_args Hrename Hcheck Hnodup_caps Hready_args Htyped_args
    Hfresh_s Hfresh_captured.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  destruct (Htyping_args env s args s_args vs Heval_args Ω n Σ
              (fn_params fdef) Σ_args Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (fn_params fdef) Σ_args R_args arg_roots Htyped_args))
    as [Hstore_args [Hargs_fdef_sargs Hpres_args]].
  destruct (Hroots_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hroots
              Hshadow Hrn Htyped_args)
    as [Hroots_args' [Hvalue_roots [Hshadow_args Hrn_args]]].
  pose proof (Hnames_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hnamed Htyped_args) as Hnames_args'.
  pose proof (Hkeys_args env s args s_args vs Heval_args Ω n R Σ
              (fn_params fdef) Σ_args R_args arg_roots Hprov_args Hstore
              Hroots Hshadow Hrn Hkeys Htyped_args) as Hkeys_args'.
  destruct Hnames_args' as [Hnamed_args Harg_roots_named].
  assert (Hfresh_s_args : ~ In x (store_names s_args)).
  { eapply eval_args_store_names_fresh; eassumption. }
  assert (Hlookup_args_x : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  pose proof
    (check_make_closure_captures_exact_sctx_with_env_params_fresh_in_store
      env Ω s Σ captures (fn_captures fdef) env_lt captured_tys
      Hstore Hcheck) as Hfresh_caps.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s_args vs Heval_args Hready_args)
    as Hargs_names.
  assert (Hstore_disj :
    forall y, In y (store_names captured) -> ~ In y (store_names s_args)).
  { intros y Hin_captured Hin_args.
    rewrite (copy_capture_store_as_store_names captures (fn_captures fdef)
               s captured Hcopy) in Hin_captured.
    rewrite Hargs_names in Hin_args.
    exact (Hfresh_caps y Hin_captured Hin_args). }
  assert (Hroot_disj :
    forall y,
      root_env_lookup y (capture_store_root_env captured) = None \/
      root_env_lookup y R_args = None).
  { intros y.
    destruct (root_env_lookup y (capture_store_root_env captured))
      as [roots_cap |] eqn:Hlookup_cap.
    - right.
      eapply root_env_store_keys_named_lookup_excludes_name.
      + exact Hkeys_args'.
      + intros Hin_args.
        eapply Hstore_disj.
        * rewrite <- capture_store_root_env_names.
          eapply root_env_lookup_some_in_names. exact Hlookup_cap.
        * exact Hin_args.
    - left. reflexivity. }
  assert (Hpres_tail :
    store_ref_targets_preserved env s_args (captured ++ s_args)).
  { apply store_ref_targets_preserved_app_right.
    intros y Hin.
    apply store_lookup_not_in_names.
    intros Hin_captured.
    eapply Hstore_disj; eassumption. }
  assert (Hpres_frame : store_ref_targets_preserved env s (captured ++ s_args)).
  { eapply store_ref_targets_preserved_trans; eassumption. }
  pose proof
    (copy_capture_store_as_captured_call_frame_ready_with_env
      Ω env s Σ captures (fn_captures fdef) captured env_lt captured_tys
      s_args R_args Hstore Hpres_frame Hnodup_caps Hcheck Hcopy
      Hroots_args' Hshadow_args Hrn_args Hnamed_args Hkeys_args'
      Hstore_disj Hroot_disj) as Hframe_ready.
  pose proof
    (copy_capture_store_as_captured_values_canonical_roots_with_env
      Ω env s Σ captures (fn_captures fdef) captured env_lt captured_tys
      Hstore Hcopy Hcheck) as Hcaptured_values.
  assert (Hclosure_roots :
    value_roots_within
      (root_sets_union (capture_store_root_sets captured))
      (VClosure fname captured)).
  { eapply captured_closure_roots_within_capture_store_root_sets.
    exact Hcaptured_values. }
  assert (Htyped_cap_frame :
    Forall2 (store_entry_typed env (captured ++ s_args))
      captured (sctx_of_store captured)).
  { unfold captured_call_frame_ready_in_frame,
      captured_store_runtime_ready_in_frame in Hframe_ready.
    exact (proj1 (proj1 Hframe_ready)). }
  assert (Hcapture_roots_named_frame :
    root_set_store_roots_named
      (root_sets_union (capture_store_root_sets captured))
      (captured ++ s_args)).
  { eapply capture_store_root_sets_union_store_roots_named_in_store_runtime.
    exact Htyped_cap_frame. }
  assert (Hcapture_roots_named_hidden :
    root_set_store_roots_named
      (root_sets_union (capture_store_root_sets captured))
      (captured ++ s_args_hidden)).
  { eapply root_set_store_roots_named_weaken_store.
    - exact Hcapture_roots_named_frame.
    - intros y Hin.
      subst s_args_hidden.
      rewrite store_names_app in *.
      apply in_app_or in Hin as [Hin | Hin].
      + apply in_or_app. left. exact Hin.
      + apply in_or_app. right. simpl. right. exact Hin. }
  assert (Hframe_hidden :
    captured_call_frame_ready_in_frame env captured
      (capture_store_root_env captured) s_args_hidden
      (root_env_add x (root_sets_union (capture_store_root_sets captured))
        R_args)).
  { subst s_args_hidden.
    eapply captured_call_frame_ready_in_frame_store_add_right_roots;
      eassumption. }
  assert (Hpres_args_hidden :
    store_ref_targets_preserved env s_args s_args_hidden).
  { subst s_args_hidden.
    apply store_add_fresh_ref_targets_preserved.
    apply store_lookup_not_in_names. exact Hfresh_s_args. }
  assert (Hpres_hidden_tail :
    store_ref_targets_preserved env s_args_hidden
      (captured ++ s_args_hidden)).
  { apply store_ref_targets_preserved_app_right.
    intros y Hin_hidden.
    apply store_lookup_not_in_names.
    intros Hin_captured.
    subst s_args_hidden.
    rewrite store_names_add in Hin_hidden.
    simpl in Hin_hidden.
    destruct Hin_hidden as [Hyx | Hin_args].
    - subst y. contradiction.
    - eapply Hstore_disj; eassumption. }
  assert (Hpres_hidden :
    store_ref_targets_preserved env s (captured ++ s_args_hidden)).
  { eapply store_ref_targets_preserved_trans.
    - exact Hpres_args.
    - eapply store_ref_targets_preserved_trans; eassumption. }
  assert (Hcaptured_params_typed :
    captured_params_store_typed_in_frame env captured s_args_hidden
      (fn_captures fcall)).
  { rewrite (alpha_rename_fn_def_captures
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename).
    eapply copy_capture_store_exact_with_env_params_store_typed_in_frame.
    - exact Hstore.
    - exact Hpres_hidden.
    - exact Hcopy.
    - exact Hcheck. }
  pose proof (conj Hframe_hidden Hcaptured_params_typed)
    as Hframe_params_ready.
  exact (eval_let_make_closure_captured_call_runtime_args_ready_in_frame_core
    env Ω fname captured (capture_store_root_env captured) fdef fcall used'
    s_args_hidden s_args vs R_args Σ_args arg_roots x T
    (root_sets_union (capture_store_root_sets captured))
    Hhidden Hrename Hframe_hidden Hframe_params_ready Hstore_args
    Hargs_fdef_sargs Hvalue_roots Hfresh_s_args).
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_package_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args vs R_args Σ_args arg_roots captured_tys,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
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
  intros Htyping Hroots_pkg Hnames Hkeys.
  destruct Hroots_pkg as [Hroot_expr [Hroot_args Hroot_fields]].
  assert (Hroot_expr_plain :
    forall env s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_roots_within R' s' /\
        value_roots_within roots v /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a e_a s_b v_a Heval Ω_a n_a R_a Σ_a T_a Σ_b
      R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_expr env_a s_a e_a s_b v_a Heval Ω_a n_a R_a
      Σ_a T_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalue Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_args_plain :
    forall env s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_roots_within R' s' /\
        Forall2 value_roots_within roots vs /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_args env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a
      Σ_a ps_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_fields_plain :
    forall env s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_roots_within R' s' /\
        value_fields_roots_within roots values /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a fields_a defs_a s_b values_a Heval Ω_a n_a lts_a
      args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_fields env_a s_a fields_a defs_a s_b values_a Heval
      Ω_a n_a lts_a args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots
      Hshadow Hrn Htyped) as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  eapply
    (eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_parts_core
      (proj1 Htyping)
      (proj1 (proj2 Htyping))
      (proj2 (proj2 Htyping))
      Hroot_expr_plain
      Hroot_args_plain
      Hroot_fields_plain
      (proj1 Hnames)
      (proj1 (proj2 Hnames))
      (proj2 (proj2 Hnames))
      (proj1 Hkeys)
      (proj1 (proj2 Hkeys))
      (proj2 (proj2 Hkeys)));
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_package_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots captured_tys x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
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
  intros Htyping Hroots_pkg Hnames Hkeys.
  destruct Hroots_pkg as [Hroot_expr [Hroot_args Hroot_fields]].
  assert (Hroot_expr_plain :
    forall env s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_roots_within R' s' /\
        value_roots_within roots v /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a e_a s_b v_a Heval Ω_a n_a R_a Σ_a T_a Σ_b
      R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_expr env_a s_a e_a s_b v_a Heval Ω_a n_a R_a
      Σ_a T_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalue Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_args_plain :
    forall env s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_roots_within R' s' /\
        Forall2 value_roots_within roots vs /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_args env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a
      Σ_a ps_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_fields_plain :
    forall env s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_roots_within R' s' /\
        value_fields_roots_within roots values /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a fields_a defs_a s_b values_a Heval Ω_a n_a lts_a
      args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_fields env_a s_a fields_a defs_a s_b values_a Heval
      Ω_a n_a lts_a args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots
      Hshadow Hrn Htyped) as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  eapply
    (eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_parts_core
      (proj1 Htyping)
      (proj1 (proj2 Htyping))
      (proj2 (proj2 Htyping))
      Hroot_expr_plain
      Hroot_args_plain
      Hroot_fields_plain
      (proj1 Hnames)
      (proj1 (proj2 Hnames))
      (proj2 (proj2 Hnames))
      (proj1 Hkeys)
      (proj1 (proj2 Hkeys))
      (proj2 (proj2 Hkeys)));
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_package_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots env_lt captured_tys
      x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
    let hidden_roots := root_sets_union (capture_store_root_sets captured) in
    captured_call_frame_params_ready_in_frame env captured
      (capture_store_root_env captured) s_args_hidden
      (root_env_add x hidden_roots R_args) (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x hidden_roots R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x hidden_roots R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (capture_store_root_env captured ++
          root_env_add x hidden_roots R_args)).
Proof.
  intros Htyping Hroots_pkg Hnames Hkeys.
  destruct Hroots_pkg as [Hroot_expr [Hroot_args Hroot_fields]].
  assert (Hroot_expr_plain :
    forall env s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_roots_within R' s' /\
        value_roots_within roots v /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a e_a s_b v_a Heval Ω_a n_a R_a Σ_a T_a Σ_b
      R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_expr env_a s_a e_a s_b v_a Heval Ω_a n_a R_a
      Σ_a T_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalue Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_args_plain :
    forall env s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_roots_within R' s' /\
        Forall2 value_roots_within roots vs /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_args env_a s_a args_a s_b vs_a Heval Ω_a n_a R_a
      Σ_a ps_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  assert (Hroot_fields_plain :
    forall env s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_roots_within R' s' /\
        value_fields_roots_within roots values /\
        store_no_shadow s' /\
        root_env_no_shadow R').
  { intros env_a s_a fields_a defs_a s_b values_a Heval Ω_a n_a lts_a
      args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hroot_fields env_a s_a fields_a defs_a s_b values_a Heval
      Ω_a n_a lts_a args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots
      Hshadow Hrn Htyped) as [Hroots' Hvalues Hshadow' Hrn'].
    repeat split; assumption. }
  eapply
    (eval_let_make_closure_captured_call_runtime_args_ready_auto_with_env_with_preservation_parts_core
      (proj1 Htyping)
      (proj1 (proj2 Htyping))
      (proj2 (proj2 Htyping))
      Hroot_expr_plain
      Hroot_args_plain
      Hroot_fields_plain
      (proj1 Hnames)
      (proj1 (proj2 Hnames))
      (proj2 (proj2 Hnames))
      (proj1 Hkeys)
      (proj1 (proj2 Hkeys))
      (proj2 (proj2 Hkeys)));
    eassumption.
Qed.
