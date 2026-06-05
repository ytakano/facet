From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeDirectSafety.
From Facet.TypeSystem Require Import TypeSafetyDirectCallWrappers.
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


Lemma infer_core_env_roots_shadow_safe_evar_lookup_core :
  forall env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st,
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_out, R_out, roots) ->
    sctx_lookup x (sctx_of_ctx Γ) = Some (T_lookup, st) ->
    ty_core T_infer = ty_core T_lookup.
Proof.
  intros env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st
    Hinfer Hlookup.
  unfold infer_core_env_roots_shadow_safe in Hinfer.
  cbn in Hinfer.
  unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
  cbn in Hinfer.
  rewrite Hlookup in Hinfer.
  destruct (binding_available_b st []) eqn:Havailable; try discriminate.
  destruct (root_env_lookup x R) as [roots0 |] eqn:Hroot; try discriminate.
  destruct (usage_eqb (ty_usage T_lookup) UUnrestricted) eqn:Husage.
  - inversion Hinfer; subst. reflexivity.
  - destruct (sctx_consume_path (sctx_of_ctx Γ) x []) as [Σc | err]
      eqn:Hconsume; try discriminate.
    inversion Hinfer; subst. reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_evar_infer_core :
  forall env Ω n R Γ x T_typed Σ_out R_out roots_typed
      T_infer Γ_infer R_infer roots_infer,
    typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ) (EVar x)
      T_typed Σ_out R_out roots_typed ->
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_infer, R_infer, roots_infer) ->
    ty_core T_infer = ty_core T_typed.
Proof.
  intros env Ω n R Γ x T_typed Σ_out R_out roots_typed
    T_infer Γ_infer R_infer roots_infer Htyped Hinfer.
  dependent destruction Htyped.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core; eassumption.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core; eassumption.
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
  destruct Hfn_summary as [Hdirect_or_prov | [Hlocal_summary | Hvar_summary]].
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
	        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
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
	        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
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
	      eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
	    assert (Heval_body_env : eval body_env s raw_body s' v).
	    { subst body_env.
	      eapply eval_global_env_with_local_bounds. exact Heval. }
	    unfold local_fn_value_call_target_expr in Htarget.
	    destruct raw_body as
	      [| lit | z | m x T e1 e2 | m x e1 e2 | fname_alias
		       | fname_make captures_make | p | fname_direct args_direct
		       | fname_generic tys_generic args_generic | callee args_call
         | callee_generic tys_call args_call_generic
	       | sname lts tys fields
	         | enum_name variant_name lts_enum tys_enum payloads | scrut_match branches_match
		       | p e_new | p e_new | rk p | e | e | e1 e2 e3];
      try discriminate.
	    + destruct e1 as
	        [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12 | fname_value
		         | fname_make1 captures_make1 | p1 | fname1 args1
		         | fname_generic1 tys_generic1 args_generic1 | callee1 args1
           | callee_generic1 tys_call1 args_call_generic1
	         | sname1 lts1 tys1 fields1
	           | enum_name1 variant_name1 lts_enum1 tys_enum1 payloads1 | scrut_match1 branches_match1
		         | p1 e_new1 | p1 e_new1 | rk1 p1 | e1 | e1 | e11 e12 e13];
        try discriminate.
	      destruct e2 as
	        [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22 | fname2
		         | fname_make2 captures_make2 | p2 | fname2 args2
		         | fname_generic2 tys_generic2 args_generic2 | callee2 args2
           | callee_generic2 tys_call2 args_call_generic2
	         | sname2 lts2 tys2 fields2
	           | enum_name2 variant_name2 lts_enum2 tys_enum2 payloads2 | scrut_match2 branches_match2
		         | p2 e_new2 | p2 e_new2 | rk2 p2 | e2 | e2 | e21 e22 e23];
        try discriminate.
	      destruct callee2 as
	        [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2 | fnamec
		         | fname_makec captures_makec | pc | fnamec argsc
		         | fname_genericc tys_genericc args_genericc | calleec argsc
           | callee_genericc tys_callc args_call_genericc
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
  - destruct Hvar_summary as
      (x & args & T_callee & Γ_callee & R_callee & roots_callee &
        T_body & Γ_out & R_body & roots_body &
        Hbody & Hready_args & Hinfer_callee & Hcallee_shape & Hnodup &
        Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    pose (body_env :=
      global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)).
    assert (Hstore_body_env :
        store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hstore_summary_body :
        store_function_closure_targets_summary body_env s).
    { subst body_env.
      apply store_function_closure_targets_summary_global_env_with_local_bounds.
      eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
    set (callee_var := x).
    assert (Heval_body_env : eval body_env s (ECallExpr (EVar callee_var) args) s' v).
    { subst body_env.
      eapply eval_global_env_with_local_bounds. exact Heval. }
    dependent destruction Heval_body_env.
    match goal with
    | Hcallee_eval : eval body_env s (EVar callee_var) ?s_fn (VClosure ?fname ?captured) |- _ =>
        rename Hcallee_eval into Heval_callee
    end.
    match goal with
    | Hlookup_runtime : lookup_fn ?fname (env_fns body_env) = Some ?fdef_runtime |- _ =>
        rename Hlookup_runtime into Hlookup_runtime
    end.
    rewrite Hbody in Htyped_shadow.
    dependent destruction Htyped_shadow.
    * match goal with
      | Htyped_callee_shadow : typed_env_roots_shadow_safe _ _ _ _ _ _ (MkTy _ (TFn _ _)) _ _ _ |- _ =>
          pose proof (typed_env_roots_shadow_safe_roots _ _ _ _ _ _ _ _ _ _
            Htyped_callee_shadow) as Htyped_callee_roots
      end.
      destruct (proj1 eval_preserves_typing_roots_ready_mutual
          body_env s (EVar x) s_fn (VClosure fname captured) Heval_callee
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) (MkTy u (TFn param_tys ret0))
          Σ1 R1 roots_callee0
          (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Htyped_callee_roots)
        as [_ [Hv_callee _]].
      pose proof
        (value_has_type_closure_captured_nil body_env s_fn fname captured _
          Hv_callee) as Hcaptured_nil.
      subst captured.
      assert (Hcallee_summary_runtime :
          callee_body_root_shadow_provenance_summary body_env fdef).
      { inversion Heval_callee; subst.
        - match goal with
          | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se,
            Hsummary_store : store_function_closure_targets_summary body_env ?s_lookup |- _ =>
              pose proof
                (store_function_closure_targets_summary_lookup body_env s_lookup x_lookup se
                  Hsummary_store Hlookup_store) as Hvalue_summary
          end.
          match goal with
          | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
              rewrite Hvalue_eq in Hvalue_summary
          | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
              rewrite <- Hvalue_eq in Hvalue_summary
          | _ => idtac
          end.
          simpl in Hvalue_summary.
          destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary_target).
          assert (fdef_summary = fdef) as ->
            by (eapply lookup_fn_deterministic; eassumption).
          exact Hsummary_target.
        - match goal with
          | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se,
            Hsummary_store : store_function_closure_targets_summary body_env ?s_lookup |- _ =>
              pose proof
                (store_function_closure_targets_summary_lookup body_env s_lookup x_lookup se
                  Hsummary_store Hlookup_store) as Hvalue_summary
          end.
          match goal with
          | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
              rewrite Hvalue_eq in Hvalue_summary
          | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
              rewrite <- Hvalue_eq in Hvalue_summary
          | _ => idtac
          end.
          simpl in Hvalue_summary.
          destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary_target).
          assert (fdef_summary = fdef) as ->
            by (eapply lookup_fn_deterministic; eassumption).
          exact Hsummary_target. }
      simpl in *.
      destruct (eval_call_expr_tfn_components_preserve_typing_with_callee_summary
        body_env s s_fn s_args s_body (EVar callee_var) args fname [] fdef fcall
        vs ret used' Heval_callee H1 H2 H3 Heval_body_env2
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f)) Σ1 R1 (sctx_of_ctx Γ_out) R'
        roots_callee0 arg_roots u param_tys ret0
        Hready_args (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow
        Hroot_shadow Hnamed Hkeys Htyped_shadow H0 Hunique
        Hcallee_summary_runtime)
      as [_ [Hv _]].
      assert (Hv_env :
          value_has_type (alpha_normalize_global_env env)
            (store_remove_params (fn_captures fcall)
               (store_remove_params (fn_params fcall) s_body))
            ret ret0).
      { subst body_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
      eapply VHT_Compatible.
      + exact Hv_env.
      + apply ty_compatible_b_sound. exact Hcompat.
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x (MkTy u (TClosure env_lt param_tys ret0))
          Σ1 R1 roots_callee0 T_callee Γ_callee R_callee roots_callee
          Htyped_shadow Hinfer_callee) as Hcore.
      simpl in Hcore.
      destruct Hcallee_shape as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape]; rewrite Hcore in Hshape; discriminate.
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x (MkTy u (TTypeForall type_params bounds body_ty))
          Σ1 R1 roots_callee0 T_callee Γ_callee R_callee roots_callee
          Htyped_shadow Hinfer_callee) as Hcore.
      simpl in Hcore.
      destruct Hcallee_shape as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape];
        [ rewrite Hcore in Hshape; discriminate
        | rewrite Hcore in Hshape; inversion Hshape; subst;
          simpl in Hbody_shape; discriminate ].
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x
          (MkTy u (TForall m bounds (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
          Σ1 R1 roots_callee0 T_callee Γ_callee R_callee roots_callee
          Htyped_shadow Hinfer_callee) as Hcore.
      simpl in Hcore.
      destruct Hcallee_shape as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape];
        [ rewrite Hcore in Hshape; discriminate
        | rewrite Hcore in Hshape; inversion Hshape; subst;
          simpl in Hbody_shape; discriminate ].
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x (MkTy u (TForall m bounds body_ty))
          Σ1 R1 roots_callee0 T_callee Γ_callee R_callee roots_callee
          Htyped_shadow Hinfer_callee) as Hcore.
      simpl in Hcore.
      match goal with
      | Htyped_callee_shadow : typed_env_roots_shadow_safe _ _ _ _ _ _
          (MkTy _ (TForall _ _ _)) _ _ _ |- _ =>
          pose proof (typed_env_roots_shadow_safe_roots _ _ _ _ _ _ _ _ _ _
            Htyped_callee_shadow) as Htyped_callee_roots
      end.
      destruct (proj1 eval_preserves_typing_roots_ready_mutual
          body_env s (EVar x) s_fn (VClosure fname captured) Heval_callee
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) (MkTy u (TForall m bounds body_ty))
          Σ1 R1 roots_callee0
          (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Htyped_callee_roots)
        as [Hstore_fn [Hv_callee [_ [Hroots_fn [_ [Hshadow_fn Hrn_fn]]]]]].
      destruct (proj1 eval_preserves_root_names_ready_mutual
          body_env s (EVar x) s_fn (VClosure fname captured) Heval_callee
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) (MkTy u (TForall m bounds body_ty))
          Σ1 R1 roots_callee0
          (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Hnamed Htyped_callee_roots) as [Hnamed_fn _].
      pose proof (proj1 eval_preserves_root_keys_named_ready_mutual
          body_env s (EVar x) s_fn (VClosure fname captured) Heval_callee
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) (MkTy u (TForall m bounds body_ty))
          Σ1 R1 roots_callee0
          (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Hkeys Htyped_callee_roots) as Hkeys_fn.
      pose proof
        (value_has_type_closure_captured_nil body_env s_fn fname captured _
          Hv_callee) as Hcaptured_nil.
      subst captured.
      destruct
        (value_has_type_empty_closure_tforall_tfn_components
          body_env s_fn fname fdef u m bounds body_ty param_tys ret0 σ
          Hv_callee H5 Hunique H0)
        as [Htype_params [Hcaps_fdef Hbridge]].
      pose proof (typed_args_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f) R1 Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys))
        (sctx_of_ctx Γ_out) R' arg_roots H4) as Htyped_args.
      pose proof (preservation_ready_args_implies_provenance_ready_closure
                    args Hready_args) as Hprov_args.
      assert (Hcallee_summary_runtime :
          callee_body_root_shadow_provenance_summary body_env fdef).
      { inversion Heval_callee; subst.
        - match goal with
          | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se,
            Hsummary_store : store_function_closure_targets_summary body_env ?s_lookup |- _ =>
              pose proof
                (store_function_closure_targets_summary_lookup body_env s_lookup x_lookup se
                  Hsummary_store Hlookup_store) as Hvalue_summary
          end.
          match goal with
          | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
              rewrite Hvalue_eq in Hvalue_summary
          | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
              rewrite <- Hvalue_eq in Hvalue_summary
          | _ => idtac
          end.
          simpl in Hvalue_summary.
          destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary_target).
          assert (fdef_summary = fdef) as ->
            by (eapply lookup_fn_deterministic; eassumption).
          exact Hsummary_target.
        - match goal with
          | Hlookup_store : store_lookup ?x_lookup ?s_lookup = Some ?se,
            Hsummary_store : store_function_closure_targets_summary body_env ?s_lookup |- _ =>
              pose proof
                (store_function_closure_targets_summary_lookup body_env s_lookup x_lookup se
                  Hsummary_store Hlookup_store) as Hvalue_summary
          end.
          match goal with
          | Hvalue_eq : se_val _ = VClosure _ _ |- _ =>
              rewrite Hvalue_eq in Hvalue_summary
          | Hvalue_eq : VClosure _ _ = se_val _ |- _ =>
              rewrite <- Hvalue_eq in Hvalue_summary
          | _ => idtac
          end.
          simpl in Hvalue_summary.
          destruct Hvalue_summary as (fdef_summary & Hlookup_summary & Hsummary_target).
          assert (fdef_summary = fdef) as ->
            by (eapply lookup_fn_deterministic; eassumption).
          exact Hsummary_target. }
      assert (Hcallee_route :
        callee_body_root_shadow_provenance_ready_at_result_subset body_env fcall
          (call_param_root_env (fn_params fcall) arg_roots R')
          (root_sets_union arg_roots)).
      { eapply
          direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_tfn_with_result_subset;
          eassumption. }
      destruct
        (eval_evar_call_expr_lifetime_forall_tfn_components_preserve_typing_with_callee_summary_route
          body_env s s_fn s_args s_body x args fname [] fdef fcall vs ret used'
          Heval_callee H5 H6 H7 Heval_body_env2
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) Σ1 R1 (sctx_of_ctx Γ_out) R'
          roots_callee0 arg_roots u m bounds body_ty param_tys ret0 σ
          Hready_args Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Htyped_shadow H0 H4 Htype_params Hcaps_fdef Hbridge Hcallee_route)
        as [_ [Hv _]].
      assert (Hv_env :
          value_has_type (alpha_normalize_global_env env)
            (store_remove_params (fn_captures fcall)
               (store_remove_params (fn_params fcall) s_body))
            ret (open_bound_ty σ ret0)).
      { subst body_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
      eapply VHT_Compatible.
      + exact Hv_env.
      + apply ty_compatible_b_sound. exact Hcompat.
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x (MkTy u (TForall m bounds body_ty))
          Σ1 R1 roots_callee0 T_callee Γ_callee R_callee roots_callee
          Htyped_shadow Hinfer_callee) as Hcore.
      simpl in Hcore.
      destruct Hcallee_shape as
        [Tshape params_shape ret_shape Hshape
        | Tshape m_shape bounds_shape body_shape params_shape ret_shape
            Hshape Hbody_shape];
        [ rewrite Hcore in Hshape; discriminate
        | rewrite Hcore in Hshape; inversion Hshape; subst;
          rewrite H0 in Hbody_shape; discriminate ].
Qed.
