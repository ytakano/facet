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
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | exact Hname_eq ]);
          subst f_typed
      end
  end.
  match goal with
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      let Hsame := fresh "Hsame_typed_callee" in
      assert (Hsame : f_typed = fdef)
        by (eapply Hunique;
            [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
      subst f_typed
  | _ => idtac
  end.
  repeat match goal with
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      lazymatch f_runtime with
      | fdef => fail 1
      | _ =>
          let Hsame := fresh "Hsame_callee" in
          assert (Hsame : f_runtime = fdef)
            by (eapply lookup_fn_unique_by_name;
                [ exact Hlookup | exact Hin | exact Hfname | exact Hunique ]);
          subst f_runtime
      end
  end.
  match goal with
  | Hlookup : lookup_fn (fn_name fdef) (env_fns env) = Some ?f_runtime |- _ =>
      let Hsame := fresh "Hsame_callee" in
      assert (Hsame : f_runtime = fdef)
        by (eapply lookup_fn_unique_by_name;
            [ exact Hlookup | exact Hin | reflexivity | exact Hunique ]);
      subst f_runtime
  | _ => idtac
  end.
  match goal with
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      let Hsame := fresh "Hsame_typed_callee" in
      assert (Hsame : f_typed = fdef)
        by (eapply Hunique;
            [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
      subst f_typed
  | _ => idtac
  end.
  repeat match goal with
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime |- _ =>
      lazymatch f_runtime with
      | fdef => fail 1
      | _ =>
          let Hsame := fresh "Hsame_callee" in
          assert (Hsame : f_runtime = fdef)
            by (eapply lookup_fn_unique_by_name;
                [ exact Hlookup | exact Hin | exact Hfname | exact Hunique ]);
          subst f_runtime
      end
  end.
  match goal with
  | Hlookup : lookup_fn (fn_name fdef) (env_fns env) = Some ?f_runtime |- _ =>
      let Hsame := fresh "Hsame_callee" in
      assert (Hsame : f_runtime = fdef)
        by (eapply lookup_fn_unique_by_name;
            [ exact Hlookup | exact Hin | reflexivity | exact Hunique ]);
      subst f_runtime
  | _ => idtac
  end.
  match goal with
  | Htyped_args_shadow : typed_args_roots_shadow_safe env Ω n R Σ args
      (apply_lt_params ?sigma (fn_params fdef)) ?Sigma_args ?R_args
      ?arg_roots,
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
        env Ω n R Σ args (apply_lt_params sigma (fn_params fdef))
        Sigma_args R_args arg_roots
        Htyped_args_shadow) as Htyped_args_roots;
      destruct
        (eval_make_closure_captured_call_expr_package_with_callee_components
          env Ω n R Σ args fname_call captures captured fdef fcall used' sigma
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
        try exact Hv;
        try exact Hroots_final;
        try exact Hshadow_final;
        try exact Hrn_final;
      eapply direct_call_value_roots_within_store_subset;
        [ exact Hvalue_roots | exact Hret_subset ]
  end.
  (* TERS_CallExpr_Fn with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
  end.
  (* TERS_CallExpr_Closure with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
  end.
  (* TERS_CallExpr_TypeForall with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
  end.
  (* TERS_CallExpr_MixedForall with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
  end.
  (* TERS_CallExpr_Forall_Fn with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
  end.
  (* TERS_CallExpr_Forall_Closure with EMakeClosure: impossible, guard violated *)
  exfalso.
  match goal with
  | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
      exact (H fn cs eq_refl)
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
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef) (fn_lifetimes fdef)
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
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
      | fdef => fail 1
      | _ =>
          let Hsame := fresh "Hsame_typed_callee" in
          assert (Hsame : f_typed = fdef)
            by (eapply Hunique;
                [ exact Hin_typed | exact Hin | exact Hname_eq ]);
          subst f_typed
      end
  end.
  match goal with
  | Hin_typed : In ?f_typed (env_fns env),
    Hname_eq : fn_name fdef = fn_name ?f_typed |- _ =>
      let Hsame := fresh "Hsame_typed_callee" in
      assert (Hsame : f_typed = fdef)
        by (eapply Hunique;
            [ exact Hin_typed | exact Hin | symmetry; exact Hname_eq ]);
      subst f_typed
  | _ => idtac
  end.
  eapply
    TypeSafetyClosureWrappersCapturedCall
      .eval_make_closure_captured_call_expr_preserves_typing_with_callee_components;
    try eassumption.
  - eapply typed_args_roots_shadow_safe_roots; eassumption.
  - (* TERS_CallExpr_Fn with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
  - (* TERS_CallExpr_Closure with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
  - (* TERS_CallExpr_TypeForall with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
  - (* TERS_CallExpr_MixedForall with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
  - (* TERS_CallExpr_Forall_Fn with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
  - (* TERS_CallExpr_Forall_Closure with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | H : forall fname' caps', EMakeClosure ?fn ?cs <> EMakeClosure fname' caps' |- _ =>
        exact (H fn cs eq_refl)
    end.
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
      store_no_shadow s' /\
      root_env_no_shadow R'.
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
	    { match goal with
	      | Hnodup : NoDup (ctx_names
	          (params_ctx (fn_params fcallee ++ fn_captures fcallee))) |- _ =>
	          rewrite params_ctx_app, ctx_names_app in Hnodup;
	          eapply NoDup_app_right_ts; exact Hnodup
	      end. }
    destruct (eval_make_closure_captured_call_expr_shadow_package_with_callee_components
        env Ω n R Σ args fname captures fcallee s s' ret T Σ' R' roots
        env_lt captured_tys T_body Γ_out R_body roots_body capture_roots)
      as [Hstore' [Hv [Hroots' [Hvalue_roots [Hshadow' Hrn']]]]]; eauto.
    repeat split; assumption.
	  - assert (Hnodup_caps :
	        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
	    { match goal with
	      | Hnodup : NoDup (ctx_names
	          (params_ctx (fn_params fcallee ++ fn_captures fcallee))) |- _ =>
	          rewrite params_ctx_app, ctx_names_app in Hnodup;
	          eapply NoDup_app_right_ts; exact Hnodup
	      end. }
    rename x into x_hidden.
    assert (Hfresh_s : ~ In x_hidden (store_names s)).
    { apply store_lookup_none_not_in_store_names.
      eapply store_roots_within_lookup_none; eassumption. }
    dependent destruction H17.
    { pose proof (lookup_fn_in_unique_by_name env (fn_name fdef) fdef
                    H17 eq_refl Hunique) as Hlookup_direct.
      pose proof (lookup_fn_in_unique_by_name env (fn_name fdef) fcallee
                    H5 H6 Hunique) as Hlookup_callee.
      rewrite Hlookup_direct in Hlookup_callee.
      inversion Hlookup_callee; subst fdef.
  		pose proof (typed_args_roots_shadow_safe_roots env Ω n R Σ args
  		                  (apply_lt_params σ (fn_params fcallee))
  		                  Σ' R' arg_roots H20)
  		    as Htyped_args_roots.
      destruct
        (eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components_with_preservation_core
          eval_preserves_typing_ready_mutual
          eval_preserves_roots_ready_mutual
          eval_preserves_root_names_ready_mutual
          eval_preserves_root_keys_named_ready_mutual
          eval_preserves_frame_scope_roots_ready_mutual
          (eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package
            eval_preserves_typing_roots_ready_prefix_mutual)
          eval_preserves_param_scope_roots_ready_mutual
  	        env Ω n R Σ m x_hidden T_hidden args (fn_name fcallee) captures fcallee σ s s' ret
  	        R' Σ' arg_roots env_lt captured_tys T_body Γ_out R_body
          roots_body Hstore Hroots Hshadow Hrn Hnamed Hkeys H Heval H8
          Hnodup_caps H4 Htyped_args_roots H9 H10 H11 H12 H13 H14
          Hlookup_direct Hfresh_s H1 H2 H3)
        as [Hstore' [Hv [captured_final [Hcopy Hrooted]]]].
      pose proof (capture_store_root_sets_bound_from_capture_root_bound
        R s captures (fn_captures fcallee) captured_final capture_roots
        Hcopy Hroots H15) as Hcap_subset.
      destruct Hrooted as [Hroots' Hvalue_roots Hshadow' Hrn'].
      repeat split.
      + exact Hstore'.
  	    + eapply VHT_Compatible.
        * exact Hv.
        * apply ty_compatible_b_sound. exact H22.
      + exact Hroots'.
      + eapply value_roots_within_store_subset.
        * exact Hvalue_roots.
        * eapply root_sets_union_app_stores_subset_union.
          exact Hcap_subset.
      + exact Hshadow'.
      + exact Hrn'. }
    (* TERS_CallExpr_Fn with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
    (* TERS_CallExpr_Closure with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
    (* TERS_CallExpr_TypeForall with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
    (* TERS_CallExpr_MixedForall with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
    (* TERS_CallExpr_Forall_Fn with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
    (* TERS_CallExpr_Forall_Closure with EMakeClosure: impossible, guard violated *)
    exfalso.
    match goal with
    | Hn : forall fn cs, EMakeClosure ?fname ?caps <> EMakeClosure fn cs |- _ =>
        exact (Hn fname caps eq_refl)
    end.
  - dependent destruction Heval.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
        env s e1 s1 v1 Heval1 Ω n R Σ T1 Σ1 R1 roots1 H Hstore
        Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e1 T1 Σ1 R1 roots1 H0))
      as [Hstore1 [Hv1 _]].
    destruct (proj1 eval_preserves_roots_ready_mutual
        env s e1 s1 v1 Heval1 Ω n R Σ T1 Σ1 R1 roots1 H
        Hroots Hshadow Hrn
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e1 T1 Σ1 R1 roots1 H0))
      as [Hroots1_runtime [Hv1_roots [Hshadow1 Hrn1]]].
    destruct (proj1 eval_preserves_root_names_ready_mutual
        env s e1 s1 v1 Heval1 Ω n R Σ T1 Σ1 R1 roots1 H
        Hstore Hroots Hshadow Hrn Hnamed
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e1 T1 Σ1 R1 roots1 H0))
      as [Hnamed1 Hroots1_named].
    pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
        env s e1 s1 v1 Heval1 Ω n R Σ T1 Σ1 R1 roots1 H
        Hstore Hroots Hshadow Hrn Hkeys
        (typed_env_roots_shadow_safe_roots
          env Ω n R Σ e1 T1 Σ1 R1 roots1 H0))
      as Hkeys1.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_pres :
      store_ref_targets_preserved env s1 (store_add x T_hidden v1 s1))
      by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
    assert (Hstore_add :
      store_typed env (store_add x T_hidden v1 s1)
        (sctx_add x T_hidden m Σ1)).
    { eapply store_typed_add_compatible.
      - exact Hstore1.
      - exact Hv1.
      - apply ty_compatible_b_sound. exact H1.
      - exact Hadd_pres. }
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow : store_no_shadow (store_add x T_hidden v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hadd_named :
      root_env_store_roots_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_roots_named_add_env_store_add; eassumption).
    assert (Hadd_keys :
      root_env_store_keys_named (root_env_add x roots1 R1)
        (store_add x T_hidden v1 s1))
      by (eapply root_env_store_keys_named_add_env_store_add; eassumption).
    destruct (IHHsummary (store_add x T_hidden v1 s1) s2 v2
        Hstore_add Hadd_roots Hadd_shadow Hadd_rn Hadd_named Hadd_keys
        Heval2 Hunique)
      as [Hstore2 [Hv2 [Hroots2_runtime [Hvalue_roots [Hshadow2 Hrn2]]]]].
    assert (Hremove_names :
      forall se, In se (store_remove x s2) -> se_name se <> x)
      by (apply store_no_shadow_remove_no_name; exact Hshadow2).
    assert (Hroots_removed :
      store_roots_within (root_env_remove x R2) (store_remove x s2))
      by (eapply store_remove_roots_within; eassumption).
    assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2)).
    { eapply store_roots_exclude_root.
      - exact Hroots_removed.
      - exact H8.
      - exact Hremove_names. }
    repeat split.
    + eapply store_typed_remove_excluding_root; eassumption.
    + eapply value_has_type_runtime_rootless_store_any.
      * exact Hv2.
      * apply capture_ref_free_ty_b_runtime_rootless. exact H5.
    + exact Hroots_removed.
    + exact Hvalue_roots.
    + apply store_no_shadow_remove. exact Hshadow2.
    + apply root_env_no_shadow_remove. exact Hrn2.
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
        as [Hstore2 [Hv [Hroots2 [Hvalue_roots [Hshadow2 Hrn2]]]]].
      repeat split.
      * eapply store_typed_ctx_merge_left; eassumption.
      * eapply value_has_type_if_left_result. exact Hv.
      * exact Hroots2.
      * eapply (proj1 value_roots_within_weaken).
        -- exact Hvalue_roots.
        -- intros x Hin. apply root_set_union_in_l. exact Hin.
      * exact Hshadow2.
      * exact Hrn2.
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
        as [Hstore3 [Hv [Hroots3 [Hvalue_roots [Hshadow3 Hrn3]]]]].
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
      * rewrite H4. exact Hroots3.
      * eapply (proj1 value_roots_within_weaken).
        -- exact Hvalue_roots.
        -- intros x Hin. apply root_set_union_in_r. exact Hin.
      * exact Hshadow3.
      * rewrite H4. exact Hrn3.
Unshelve.
  all: eauto.
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
  intros env Ω n R Σ e T Σ' R' roots ret_roots Hsummary
    s s' ret Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval Hunique.
  destruct (eval_expr_root_shadow_captured_call_provenance_summary_exact_package
    env Ω n R Σ e T Σ' R' roots ret_roots Hsummary s s' ret
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval Hunique)
    as [Hstore' [Hv _]].
  split; assumption.
Qed.

