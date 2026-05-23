From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeShadowCheckerFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma root_sets_union_app_stores_subset_union :
  forall arg_roots cap_roots capture_roots,
    root_set_stores_subset (root_sets_union cap_roots) capture_roots ->
    root_set_stores_subset
      (root_sets_union (arg_roots ++ cap_roots))
      (root_set_union (root_sets_union arg_roots) capture_roots).
Proof.
  intros arg_roots.
  induction arg_roots as [| roots arg_roots IH];
    intros cap_roots capture_roots Hsubset.
  - simpl. exact Hsubset.
  - simpl. unfold root_set_stores_subset in *.
    intros z Hin.
    apply root_set_union_in_inv in Hin.
    destruct Hin as [Hin | Hin].
    + apply root_set_union_in_l.
      apply root_set_union_in_l. exact Hin.
    + pose proof (IH cap_roots capture_roots Hsubset z Hin) as Htail.
      apply root_set_union_in_inv in Htail.
      destruct Htail as [Htail | Htail].
      * apply root_set_union_in_l.
        apply root_set_union_in_r. exact Htail.
      * apply root_set_union_in_r. exact Htail.
Qed.

Lemma eval_make_closure_captured_call_expr_shadow_package_with_callee_components :
  forall env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
      env_lt captured_tys T_body Γ_out R_body roots_body capture_roots,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (ECallExpr (EMakeClosure fname captures) args) s' ret ->
    typed_env_roots_shadow_safe env Ω n R Σ
      (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    capture_root_bound R captures (fn_captures fdef) = Some capture_roots ->
    store_typed env s' Σ' /\
    value_has_type env s' ret T /\
    store_roots_within R' s' /\
    value_roots_within (root_set_union roots capture_roots) ret /\
    store_no_shadow s' /\
    root_env_no_shadow R'.
Proof.
  intros env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
    env_lt captured_tys T_body Γ_out R_body roots_body capture_roots
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_expr Htyped Hunique Hin
    Hfname Hcaptures Hnodup_caps Hready_args Hnodup_binding Hprov_callee
    Htyped_callee Hcompat_callee Hexclude_roots_callee Hexclude_env_callee
    Hcapture_bound.
  dependent destruction Heval_expr.
  pose proof Heval_expr1 as Heval_make.
  dependent destruction Heval_expr1.
  dependent destruction Htyped.
  repeat match goal with
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      lazymatch f_runtime with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_callee" in
          assert (Hsame : f_runtime = fdef)
            by (eapply lookup_fn_unique_by_name;
                [ exact Hlookup | exact Hin | exact Hfname | exact Hunique ]);
          subst f_runtime
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_typed : fn_name ?f_typed = ?fname_call |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite Hname_typed; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : ?fname_call = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite <- Hname_eq; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name ?f_typed = fn_name fdef |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | exact Hname_eq ]);
          subst f_typed
      end
  end.
  match goal with
  | Htyped_args_shadow : typed_args_roots_shadow_safe env Ω n R Σ args
      (fn_params fdef) ?Sigma_args ?R_args ?arg_roots,
    Hlookup : lookup_fn ?fname_call (env_fns env) = Some fdef,
    Hcopy : copy_capture_store_as captures (fn_captures fdef) s =
      Some ?captured,
    Heval_args : eval_args env s args ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names (?captured ++ ?s_args))
      fdef = (?fcall, ?used'),
    Heval_body : eval env
      (bind_params (fn_params ?fcall) ?vs (?captured ++ ?s_args))
      (fn_body ?fcall) ?s_body ret |- _ =>
      pose proof (typed_args_roots_shadow_safe_roots
        env Ω n R Σ args (fn_params fdef) Sigma_args R_args arg_roots
        Htyped_args_shadow) as Htyped_args_roots;
      destruct
        (eval_make_closure_captured_call_expr_package_with_callee_components
          env Ω n R Σ args fname_call captures captured fdef fcall used'
          s s_args s_body vs ret R_args Sigma_args arg_roots env_lt
          captured_tys T_body Γ_out R_body roots_body Hstore Hroots
          Hshadow Hrn Hnamed Hkeys
          (Eval_MakeClosure env s fname_call captures captured fdef
            Hlookup Hcopy)
          Hlookup Heval_args Hrename Heval_body Hcaptures Hnodup_caps
          Hready_args Htyped_args_roots Hnodup_binding Hprov_callee
          Htyped_callee Hcompat_callee Hexclude_roots_callee
          Hexclude_env_callee)
        as [_ [Hstore_final [Hv [Hrefs Hrooted]]]];
      pose proof (capture_store_root_sets_bound_from_capture_root_bound
        R s captures (fn_captures fdef) captured capture_roots
        Hcopy Hroots Hcapture_bound) as Hcapture_subset;
      pose proof (root_sets_union_app_stores_subset_union
        arg_roots (capture_store_root_sets captured) capture_roots
        Hcapture_subset) as Hret_subset;
      destruct Hrooted as [Hroots_final Hvalue_roots Hshadow_final Hrn_final];
      repeat split;
        try exact Hstore_final;
        try (rewrite apply_lt_ty_nil_ts in Hv; exact Hv);
        try exact Hroots_final;
        try exact Hshadow_final;
        try exact Hrn_final;
      eapply direct_call_value_roots_within_store_subset;
        [ exact Hvalue_roots | exact Hret_subset ]
  end.
Qed.

Lemma eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components :
  forall env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
      env_lt captured_tys T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (ECallExpr (EMakeClosure fname captures) args) s' ret ->
    typed_env_roots_shadow_safe env Ω n R Σ
      (ECallExpr (EMakeClosure fname captures) args) T Σ' R' roots ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures
      (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    store_typed env s' Σ' /\
    value_has_type env s' ret T.
Proof.
  intros env Ω n R Σ args fname captures fdef s s' ret T Σ' R' roots
    env_lt captured_tys T_body Γ_out R_body roots_body Hstore Hroots
    Hshadow Hrn Hnamed Hkeys Heval_expr Htyped Hunique Hin Hfname Hcaptures
    Hnodup_caps Hready_args Hnodup_binding Hprov_callee Htyped_callee
    Hcompat_callee Hexclude_roots_callee Hexclude_env_callee.
  dependent destruction Heval_expr.
  pose proof Heval_expr1 as Heval_make.
  dependent destruction Heval_expr1.
  dependent destruction Htyped.
  repeat match goal with
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      lazymatch f_runtime with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_callee" in
          assert (Hsame : f_runtime = fdef)
            by (eapply lookup_fn_unique_by_name;
                [ exact Hlookup | exact Hin | exact Hfname | exact Hunique ]);
          subst f_runtime
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_typed : fn_name ?f_typed = ?fname_call |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite Hname_typed; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : ?fname_call = fn_name ?f_typed |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin
                | rewrite <- Hname_eq; exact Hfname ]);
          subst f_typed
      end
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name ?f_typed = fn_name fdef |- _ =>
      lazymatch f_typed with
      | fdef => fail
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | exact Hname_eq ]);
          subst f_typed
      end
  end.
  match goal with
  | Htyped_args_shadow : typed_args_roots_shadow_safe env Ω n R Σ args
      (fn_params fdef) ?Sigma_args ?R_args ?arg_roots,
    Hlookup : lookup_fn ?fname_call (env_fns env) = Some fdef,
    Hcopy : copy_capture_store_as captures (fn_captures fdef) s =
      Some ?captured,
    Heval_args : eval_args env s args ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names (?captured ++ ?s_args))
      fdef = (?fcall, ?used'),
    Heval_body : eval env
      (bind_params (fn_params ?fcall) ?vs (?captured ++ ?s_args))
      (fn_body ?fcall) ?s_body ret |- _ =>
      pose proof (typed_args_roots_shadow_safe_roots
        env Ω n R Σ args (fn_params fdef) Sigma_args R_args arg_roots
        Htyped_args_shadow) as Htyped_args_roots;
      destruct
        (eval_make_closure_captured_call_expr_preserves_typing_with_callee_components
          env Ω n R Σ args fname_call captures captured fdef fcall used'
          s s_args s_body vs ret R_args Sigma_args arg_roots env_lt
          captured_tys T_body Γ_out R_body roots_body Hstore Hroots
          Hshadow Hrn Hnamed Hkeys
          (Eval_MakeClosure env s fname_call captures captured fdef
            Hlookup Hcopy)
          Hlookup Heval_args Hrename Heval_body Hcaptures Hnodup_caps
          Hready_args Htyped_args_roots Hnodup_binding Hprov_callee
          Htyped_callee Hcompat_callee Hexclude_roots_callee
          Hexclude_env_callee) as [_ [Hstore_final Hv]]
  end.
  split.
  - exact Hstore_final.
  - rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
Qed.

Lemma eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\ value_has_type env s' ret T.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Heval Hunique.
  - destruct (proj1 eval_preserves_typing_roots_ready_mutual
        env s e s' ret Heval Ω n R Σ T Σ' R' roots
        H Hstore Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e T Σ' R' roots H0))
      as [Hstore' [Hv _]].
    split; assumption.
  - subst synthetic_body.
    assert (Heval_call : eval env s (ECall fname args) s' ret).
    { unfold direct_call_target_expr in H.
      destruct e; try discriminate.
      - inversion H; subst. exact Heval.
      - destruct e; try discriminate.
        inversion H; subst.
        apply eval_call_expr_fn_as_call. exact Heval. }
    destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
        env s s' ret fname args Heval_call Ω n R Σ T Σ' R' roots
        fcallee H1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ (ECall fname args) T Σ' R' roots H6)
        Hunique H2 H3 H4)
      as [Hstore' [Hv _]].
    split; assumption.
  - assert (Hnodup_caps :
        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
    { rewrite params_ctx_app, ctx_names_app in H5.
      eapply NoDup_app_right_ts. exact H5. }
    eapply eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components;
      eauto.
  - dependent destruction Heval.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary1 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique) as [Hstore2 Hv].
      split.
      * eapply store_typed_ctx_merge_left; eassumption.
      * eapply value_has_type_if_left_result. exact Hv.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary2 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique) as [Hstore3 Hv].
      assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3).
      { eapply typed_env_structural_branch_type_eq.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary1.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary2. }
      split.
      * eapply store_typed_ctx_merge_right; eassumption.
      * eapply value_has_type_if_right_result.
        -- exact Hv.
        -- exact H2.
Unshelve.
  all: eauto.
Qed.

Lemma eval_expr_root_shadow_captured_call_provenance_summary_exact_package :
  forall env Ω n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_captured_call_provenance_summary_exact
      env Ω n R Σ e T Σ' R' roots ret_roots ->
    forall s s' ret,
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      eval env s e s' ret ->
      fn_env_unique_by_name env ->
      store_typed env s' Σ' /\
      value_has_type env s' ret T /\
      store_roots_within R' s' /\
      value_roots_within ret_roots ret /\
      store_no_shadow s'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary; intros s s' ret Hstore Hroots Hshadow Hrn Hnamed
    Hkeys Heval Hunique.
  - destruct (proj1 eval_preserves_typing_roots_ready_mutual
        env s e s' ret Heval Ω n R Σ T Σ' R' roots
        H Hstore Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e T Σ' R' roots H0))
      as [Hstore' [Hv _]].
    destruct (proj1 eval_preserves_roots_ready_mutual
        env s e s' ret Heval Ω n R Σ T Σ' R' roots
        H Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e T Σ' R' roots H0))
      as [Hroots' [Hvalue_roots [Hshadow' Hrn']]].
    repeat split; assumption.
  - subst synthetic_body.
    assert (Heval_call : eval env s (ECall fname args) s' ret).
    { unfold direct_call_target_expr in H.
      destruct e; try discriminate.
      - inversion H; subst. exact Heval.
      - destruct e; try discriminate.
        inversion H; subst.
        apply eval_call_expr_fn_as_call. exact Heval. }
    destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
        env s s' ret fname args Heval_call Ω n R Σ T Σ' R' roots
        fcallee H1 Hstore Hroots Hshadow Hrn Hnamed Hkeys
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ (ECall fname args) T Σ' R' roots H6)
        Hunique H2 H3 H4)
      as [Hstore' [Hv [_ [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]].
    repeat split; assumption.
  - assert (Hnodup_caps :
        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
    { rewrite params_ctx_app, ctx_names_app in H5.
      eapply NoDup_app_right_ts. exact H5. }
    destruct (eval_make_closure_captured_call_expr_shadow_package_with_callee_components
        env Ω n R Σ args fname captures fcallee s s' ret T Σ' R' roots
        env_lt captured_tys T_body Γ_out R_body roots_body capture_roots)
      as [Hstore' [Hv [Hroots' [Hvalue_roots [Hshadow' _]]]]]; eauto.
  - dependent destruction Heval.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool true) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary1 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique)
        as [Hstore2 [Hv [Hroots2 [Hvalue_roots Hshadow2]]]].
      repeat split.
      * eapply store_typed_ctx_merge_left; eassumption.
      * eapply value_has_type_if_left_result. exact Hv.
      * exact Hroots2.
      * eapply (proj1 value_roots_within_weaken).
        -- exact Hvalue_roots.
        -- intros x Hin. apply root_set_union_in_l. exact Hin.
      * exact Hshadow2.
    + destruct (proj1 eval_preserves_typing_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hstore1 [_ _]].
      destruct (proj1 eval_preserves_roots_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hroots Hshadow Hrn
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hroots1 [_ [Hshadow1 Hrn1]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hnamed
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as [Hnamed1 _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          env s e1 s1 (VBool false) Heval1 Ω n R Σ T_cond Σ1 R1
          roots_cond H Hstore Hroots Hshadow Hrn Hkeys
          (typed_env_roots_shadow_safe_roots
            env Ω n R Σ e1 T_cond Σ1 R1 roots_cond H0))
        as Hkeys1.
      destruct (IHHsummary2 s1 s2 v Hstore1 Hroots1 Hshadow1 Hrn1
          Hnamed1 Hkeys1 Heval2 Hunique)
        as [Hstore3 [Hv [Hroots3 [Hvalue_roots Hshadow3]]]].
      assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3).
      { eapply typed_env_structural_branch_type_eq.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary1.
        - eapply typed_env_roots_structural.
          eapply typed_env_roots_shadow_safe_roots.
          eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
          exact Hsummary2. }
      repeat split.
      * eapply store_typed_ctx_merge_right; eassumption.
      * eapply value_has_type_if_right_result.
        -- exact Hv.
        -- exact H2.
      * eapply store_roots_within_equiv.
        -- apply root_env_equiv_sym. exact H4.
        -- exact Hroots3.
      * eapply (proj1 value_roots_within_weaken).
        -- exact Hvalue_roots.
        -- intros x Hin. apply root_set_union_in_r. exact Hin.
      * exact Hshadow3.
Unshelve.
  all: eauto.
Qed.
