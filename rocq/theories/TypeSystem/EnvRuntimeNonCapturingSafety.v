From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeDirectSafety.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma eval_local_unrestricted_fn_value_call_as_synthetic_call :
  forall env s s' v m x T fname args,
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EFn fname) (ECallExpr (EVar x) args)) s' v ->
    eval env s
      (ELet m x T (EFn fname) (ECall fname args)) s' v.
Proof.
  intros env s s' v m x T fname args Husage Heval.
  inversion Heval; subst; clear Heval.
  match goal with
  | Hfn : eval _ _ (EFn _) _ _ |- _ =>
      inversion Hfn; subst
  end.
  match goal with
  | Hcall : eval _ _ (ECallExpr (EVar _) _) _ _ |- _ =>
      inversion Hcall; subst; clear Hcall
  end.
  match goal with
  | Hcallee : eval _ _ (EVar _) _ _ |- _ =>
      inversion Hcallee; subst; clear Hcallee
  end.
  - match goal with
    | Hlookup : store_lookup _ (store_add _ _ _ _) = Some _ |- _ =>
        simpl in Hlookup; rewrite ident_eqb_refl in Hlookup;
        inversion Hlookup; subst; clear Hlookup
    end.
    repeat match goal with
    | Hclosure : VClosure _ _ = VClosure _ _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    | Hclosure : VClosure _ _ = _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    | Hclosure : _ = VClosure _ _ |- _ =>
        inversion Hclosure; subst; clear Hclosure
    end.
    simpl in *.
    eapply Eval_Let.
    + match goal with
      | Hfn : eval _ _ (EFn _) _ _ |- _ => exact Hfn
      end.
    + match goal with
      | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?fdef_fn,
        Hcaps_fn : fn_captures ?fdef_fn = [],
        Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?fdef,
        Hargs : eval_args env _ args _ _,
        Hrename : alpha_rename_fn_def ?used_names ?fdef = (?fcall, ?used'),
        Hbody : eval env (bind_params _ _ _) _ _ _ |- _ =>
          assert (Hsame : fdef_fn = fdef)
            by (eapply lookup_fn_deterministic; eassumption);
          subst fdef;
          assert (Hcaps_call : fn_captures fcall = [])
            by (rewrite (alpha_rename_fn_def_captures
                  used_names fdef_fn fcall used' Hrename);
                exact Hcaps_fn);
          rewrite Hcaps_call;
          simpl;
          eapply Eval_Call;
          [ exact Hlookup | exact Hcaps_fn | exact Hargs | exact Hrename | exact Hbody ]
      end.
  - match goal with
    | Hlookup : store_lookup _ (store_add _ _ _ _) = Some _ |- _ =>
        simpl in Hlookup; rewrite ident_eqb_refl in Hlookup;
        inversion Hlookup; subst; clear Hlookup
    end.
    match goal with
    | Hconsume : needs_consume _ = true |- _ =>
        simpl in Hconsume; unfold needs_consume in Hconsume;
        simpl in Hconsume; rewrite Husage in Hconsume;
        discriminate
    end.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  unfold check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hsummary_check].
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (check_env_root_shadow_non_capturing_call_provenance_summary_ready
      (alpha_normalize_global_env env) Hsummary_check)
    as Hsummary.
  pose proof (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hdirect_or_prov | Hlocal_summary].
  - destruct Hdirect_or_prov as [Hprov_summary | Hdirect_summary].
    + destruct Hprov_summary as [Hnodup Hbody_summary].
      unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
	      destruct Hbody_summary as
	        (T_body & Γ_out & R_body & roots_body &
	          Hprov_body & Htyped_shadow & Hcompat & _ & _).
	      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	      pose (body_env :=
	        global_env_with_local_bounds (alpha_normalize_global_env env)
	          (fn_bounds f)).
	      assert (Hstore_body_env :
	          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	      { subst body_env.
	        eapply store_typed_global_env_with_local_bounds. exact Hstore. }
	      assert (Heval_body_env : eval body_env s (fn_body f) s' v).
	      { subst body_env.
	        eapply eval_global_env_with_local_bounds. exact Heval. }
	      destruct (proj1 eval_preserves_typing_roots_ready_mutual
	          body_env s (fn_body f) s' v Heval_body_env
	          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	          (sctx_of_ctx (fn_body_ctx f))
	          T_body (sctx_of_ctx Γ_out) R_body roots_body
	          Hprov_body Hstore_body_env Hroots Hstore_shadow Hroot_shadow
	          (typed_env_roots_shadow_safe_roots
	            body_env (fn_outlives f) (fn_lifetimes f)
	            (initial_root_env_for_fn f)
	            (sctx_of_ctx (fn_body_ctx f))
	            (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
	            Htyped_shadow))
	        as [_ [Hv _]].
	      assert (Hv_env :
	          value_has_type (alpha_normalize_global_env env) s' v T_body).
	      { subst body_env.
	        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	      eapply VHT_Compatible.
	      * exact Hv_env.
	      * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hdirect_summary as
        (fname & args & raw_body & synthetic_body & fcallee & T_body &
          Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
	          Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
	          Hnodup & Htyped_shadow & Hcompat & _ & _).
	      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	      rewrite Hbody in Heval.
	      pose (body_env :=
	        global_env_with_local_bounds (alpha_normalize_global_env env)
	          (fn_bounds f)).
	      assert (Hstore_body_env :
	          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	      { subst body_env.
	        eapply store_typed_global_env_with_local_bounds. exact Hstore. }
	      assert (Heval_body_env : eval body_env s raw_body s' v).
	      { subst body_env.
	        eapply eval_global_env_with_local_bounds. exact Heval. }
	      assert (Htyped_call :
	        typed_env_roots_shadow_safe body_env
	          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	          (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
	          T_body (sctx_of_ctx Γ_out) R_body roots_body).
	      { rewrite <- Hsynthetic. exact Htyped_shadow. }
	      assert (Heval_call :
	        eval body_env s (ECall fname args) s' v).
	      { unfold direct_call_target_expr in Htarget.
	        destruct raw_body; try discriminate.
	        - inversion Htarget; subst. exact Heval_body_env.
	        - destruct raw_body; try discriminate.
	          inversion Htarget; subst.
	          apply eval_call_expr_fn_as_call. exact Heval_body_env. }
	      assert (Hcallee_summary_body :
	          callee_body_root_shadow_provenance_summary body_env fcallee).
	      { subst body_env.
	        apply
	          callee_body_root_shadow_provenance_summary_global_env_with_local_bounds.
	        exact Hcallee_summary. }
	      destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
	          body_env s s' v fname args Heval_call
	          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
	          (sctx_of_ctx (fn_body_ctx f))
	          T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
	          Hready_args Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
	          (typed_env_roots_shadow_safe_roots
	            body_env (fn_outlives f) (fn_lifetimes f)
	            (initial_root_env_for_fn f)
	            (sctx_of_ctx (fn_body_ctx f))
	            (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body roots_body
	            Htyped_call)
	          Hunique Hin_callee Hname_callee Hcallee_summary_body)
	        as [_ [Hv _]].
	      assert (Hv_env :
	          value_has_type (alpha_normalize_global_env env) s' v T_body).
	      { subst body_env.
	        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	      eapply VHT_Compatible.
	      * exact Hv_env.
	      * apply ty_compatible_b_sound. exact Hcompat.
  - destruct Hlocal_summary as
      (fname & args & raw_body & synthetic_body & fcallee & T_body &
        Γ_out & R_body & roots_body & Hbody & Htarget & Hready_args &
        Hin_callee & Hname_callee & Hcallee_summary & Hnodup &
        Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
	    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	    rewrite Hbody in Heval.
	    pose (body_env :=
	      global_env_with_local_bounds (alpha_normalize_global_env env)
	        (fn_bounds (fn_with_body f synthetic_body))).
	    assert (Hstore_body_env :
	        store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	    { subst body_env.
	      eapply store_typed_global_env_with_local_bounds. exact Hstore. }
	    assert (Heval_body_env : eval body_env s raw_body s' v).
	    { subst body_env.
	      eapply eval_global_env_with_local_bounds. exact Heval. }
	    unfold local_fn_value_call_target_expr in Htarget.
	    destruct raw_body as
	      [| lit | z | m x T e1 e2 | m x e1 e2 | fname_alias
		       | fname_make captures_make | p | fname_direct args_direct
		       | fname_generic tys_generic args_generic | callee args_call
	       | sname lts tys fields
	         | enum_name variant_name lts_enum tys_enum payloads | scrut_match branches_match
		       | p e_new | p e_new | rk p | e | e | e1 e2 e3];
      try discriminate.
	    + destruct e1 as
	        [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12 | fname_value
		         | fname_make1 captures_make1 | p1 | fname1 args1
		         | fname_generic1 tys_generic1 args_generic1 | callee1 args1
	         | sname1 lts1 tys1 fields1
	           | enum_name1 variant_name1 lts_enum1 tys_enum1 payloads1 | scrut_match1 branches_match1
		         | p1 e_new1 | p1 e_new1 | rk1 p1 | e1 | e1 | e11 e12 e13];
        try discriminate.
	      destruct e2 as
	        [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22 | fname2
		         | fname_make2 captures_make2 | p2 | fname2 args2
		         | fname_generic2 tys_generic2 args_generic2 | callee2 args2
	         | sname2 lts2 tys2 fields2
	           | enum_name2 variant_name2 lts_enum2 tys_enum2 payloads2 | scrut_match2 branches_match2
		         | p2 e_new2 | p2 e_new2 | rk2 p2 | e2 | e2 | e21 e22 e23];
        try discriminate.
	      destruct callee2 as
	        [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2 | fnamec
		         | fname_makec captures_makec | pc | fnamec argsc
		         | fname_genericc tys_genericc args_genericc | calleec argsc
	         | snamec ltsc tysc fieldsc
	           | enum_namec variant_namec lts_enumc tys_enumc payloadsc | scrut_matchc branches_matchc
		         | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
        try discriminate.
      destruct (ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted)
        eqn:Halias; try discriminate.
      inversion Htarget; subst; clear Htarget.
      apply andb_true_iff in Halias as [Hname_eq Husage_eq].
      apply ident_eqb_eq in Hname_eq. subst y.
      apply usage_eqb_true in Husage_eq.
	      match goal with
	      | He : eval body_env ?s0
	          (ELet ?m0 ?x0 ?T0 (EFn ?fname0)
	            (ECallExpr (EVar ?x0) ?args0)) ?sfinal ?vfinal |- _ =>
	          assert (Heval_synthetic :
	            eval body_env s0
	              (ELet m0 x0 T0 (EFn fname0) (ECall fname0 args0))
	              sfinal vfinal)
          by (eapply eval_local_unrestricted_fn_value_call_as_synthetic_call;
              [ exact Husage_eq | exact He ])
      end.
      inversion Heval_synthetic; subst; clear Heval_synthetic.
      match goal with
      | Hfn : eval _ _ (EFn _) _ _ |- _ =>
          inversion Hfn; subst; clear Hfn
      end.
      dependent destruction Htyped_shadow.
      match goal with
      | Hfn_typed : typed_env_roots_shadow_safe _ _ _ _ _ (EFn _) _ _ _ _ |- _ =>
          dependent destruction Hfn_typed
      end.
	      match goal with
	      | Htyped_call_shadow :
	          typed_env_roots_shadow_safe ?env0 ?Ω0 ?n0 ?R0 ?Σ0
	            (ECall ?fname0 ?args0) ?T0 ?Σ' ?R' ?roots |- _ =>
	          pose proof (typed_env_roots_shadow_safe_roots
	            env0 Ω0 n0 R0 Σ0 (ECall fname0 args0) T0 Σ' R' roots
	            Htyped_call_shadow)
	            as Htyped_call
	      end.
      assert (Hfresh_store : store_lookup x0 s1 = None)
        by (eapply store_roots_within_lookup_none; eassumption).
	      assert (Hadd_pres :
	        store_ref_targets_preserved body_env s1
	          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
	        by (apply store_add_fresh_ref_targets_preserved;
	            exact Hfresh_store).
	      assert (Hv_closure_actual :
	        value_has_type body_env s1
	          (VClosure (fn_name fcallee) []) (fn_value_ty fdef))
	        by (eapply VHT_ClosureIn; [exact H | exact x | eassumption]).
	      assert (Hv_closure :
	        value_has_type body_env s1
	          (VClosure (fn_name fcallee) []) T)
	      by (eapply VHT_Compatible;
	          [ exact Hv_closure_actual
	          | apply ty_compatible_b_sound; exact H0 ]).
	      assert (Hstore_add :
	        store_typed body_env
	          (store_add x0 T (VClosure (fn_name fcallee) []) s1)
	          (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f))))
	      by (eapply store_typed_add;
	          [ exact Hstore_body_env | exact Hv_closure | exact Hadd_pres ]).
      assert (Hroots_add :
        store_roots_within (root_env_add x0 [] (initial_root_env_for_fn f))
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (eapply store_add_roots_within;
          [ exact Hroots | eassumption | constructor ]).
      assert (Hshadow_add :
        store_no_shadow
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (apply store_no_shadow_add; assumption).
      assert (Hrn_add :
        root_env_no_shadow (root_env_add x0 [] (initial_root_env_for_fn f)))
      by (apply root_env_no_shadow_add; assumption).
      assert (Hempty_named : root_set_store_roots_named [] s1)
        by (intros z Hin_empty; contradiction).
      assert (Hnamed_add :
        root_env_store_roots_named
          (root_env_add x0 [] (initial_root_env_for_fn f))
          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
      by (eapply root_env_store_roots_named_add_env_store_add;
          eassumption).
	      assert (Hkeys_add :
	        root_env_store_keys_named
	          (root_env_add x0 [] (initial_root_env_for_fn f))
	          (store_add x0 T (VClosure (fn_name fcallee) []) s1))
	      by (eapply root_env_store_keys_named_add_env_store_add;
	          exact Hkeys).
	      assert (Hcallee_summary_body :
	        callee_body_root_shadow_provenance_summary body_env fcallee).
	      { subst body_env.
	        apply
	          callee_body_root_shadow_provenance_summary_global_env_with_local_bounds.
	        exact Hcallee_summary. }
	      destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
	          body_env
	          (store_add x0 T (VClosure (fn_name fcallee) []) s1) s2 v
	          (fn_name fcallee) args H8
	          (fn_outlives f) (fn_lifetimes f)
	          (root_env_add x0 [] (initial_root_env_for_fn f))
	          (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f)))
	          T2 Σ2 R2 roots2 fcallee
	          Hready_args Hstore_add Hroots_add Hshadow_add Hrn_add
	          Hnamed_add Hkeys_add Htyped_call Hunique Hin_callee
	          eq_refl Hcallee_summary_body)
	        as [_ [Hv_inner [_ [_ [Hv_roots _]]]]].
      assert (Hexclude_v : value_refs_exclude_root x0 v)
        by (eapply value_roots_exclude_root; eassumption).
	      assert (Hv_removed :
	        value_has_type body_env (store_remove x0 s2)
	          v T2)
	        by (eapply value_has_type_store_remove_excluding_root; eassumption).
	      assert (Hv_removed_env :
	          value_has_type (alpha_normalize_global_env env)
	            (store_remove x0 s2) v T2).
	      { subst body_env.
	        eapply value_has_type_clear_global_env_local_bounds.
	        exact Hv_removed. }
	      eapply VHT_Compatible.
	      * exact Hv_removed_env.
      * apply ty_compatible_b_sound. exact Hcompat.
    + inversion Heval.
Qed.
