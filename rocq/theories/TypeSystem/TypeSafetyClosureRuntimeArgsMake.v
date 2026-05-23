From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosureRuntimeArgsBase.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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

