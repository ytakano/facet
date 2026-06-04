From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeNonCapturingSafety.
From Facet.TypeSystem Require Import TypeSafetyDirectCallWrappers
  TypeSafetyBasePreservationControl.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Theorem callee_body_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_captured_call_provenance_summary env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hfn_summary Hinitial Hstore Heval.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hnoncapturing | Hcaptured_summary].
  - destruct Hnoncapturing as [Hdirect_or_prov | [Hlocal_summary | Hvar_summary]].
    + destruct Hdirect_or_prov as [Hprov_summary | Hdirect_summary].
      * destruct Hprov_summary as [Hnodup Hbody_summary].
        unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
	        destruct Hbody_summary as
	          (T_body & Γ_out & R_body & roots_body &
	            Hprov_body & Htyped_shadow & Hcompat & _ & _).
	        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
	          as Hroot_shadow.
	        pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
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
	              body_env (fn_outlives f)
	              (fn_lifetimes f) (initial_root_env_for_fn f)
	              (sctx_of_ctx (fn_body_ctx f))
	              (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
	              Htyped_shadow))
	          as [_ [Hv _]].
	        assert (Hv_env : value_has_type env s' v T_body).
	        { subst body_env.
	          eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	        eapply VHT_Compatible.
	        -- exact Hv_env.
	        -- apply ty_compatible_b_sound. exact Hcompat.
      * destruct Hdirect_summary as
          (fname & args & raw_body & synthetic_body & fcallee & T_body &
            Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
            Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
            Hnodup & Htyped_shadow & Hcompat & _ & _).
	        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
	          as Hroot_shadow.
	        rewrite Hbody in Heval.
	        pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
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
	              body_env (fn_outlives f)
	              (fn_lifetimes f) (initial_root_env_for_fn f)
	              (sctx_of_ctx (fn_body_ctx f))
	              (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body
	              roots_body Htyped_call)
	            Hunique Hin_callee Hname_callee Hcallee_summary_body)
	          as [_ [Hv _]].
	        assert (Hv_env : value_has_type env s' v T_body).
	        { subst body_env.
	          eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	        eapply VHT_Compatible.
	        -- exact Hv_env.
	        -- apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hlocal_summary as
        (fname & args & raw_body & synthetic_body & fcallee & T_body &
          Γ_out & R_body & roots_body & Hbody & Htarget & Hready_args &
          Hin_callee & Hname_callee & Hcallee_summary & Hnodup &
          Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
	      pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
	        as Hroot_shadow.
	      rewrite Hbody in Heval.
	      pose (body_env :=
	        global_env_with_local_bounds env
	          (fn_bounds (fn_with_body f synthetic_body))).
	      assert (Hstore_body_env :
	          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	      { subst body_env.
	        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
	      assert (Hunique_body_env : fn_env_unique_by_name body_env).
	      { subst body_env. exact Hunique. }
	      assert (Hin_callee_body : In fcallee (env_fns body_env)).
	      { subst body_env. exact Hin_callee. }
	      assert (Hunique_body_env_expanded :
	          fn_env_unique_by_name
	            (global_env_with_local_bounds env (fn_bounds f))).
	      { exact Hunique. }
	      assert (Hin_callee_body_expanded :
	          In fcallee
	            (env_fns (global_env_with_local_bounds env (fn_bounds f)))).
	      { exact Hin_callee. }
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
      * destruct e1 as
          [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
	           | fname_value | fname_make1 captures_make1 | p1
	           | fname1 args1 | fname_generic1 tys_generic1 args_generic1
	           | callee1 args1 | sname1 lts1 tys1 fields1
	             | enum_name1 variant_name1 lts_enum1 tys_enum1 payloads1 | scrut_match1 branches_match1
	           | p1 e_new1 | p1 e_new1 | rkc1 p1 | e1 | e1 | e11 e12 e13];
          try discriminate.
        destruct e2 as
          [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
	           | fname2 | fname_make2 captures_make2 | p2
	           | fname2 args2 | fname_generic2 tys_generic2 args_generic2
	           | callee2 args2 | sname2 lts2 tys2 fields2
	             | enum_name2 variant_name2 lts_enum2 tys_enum2 payloads2 | scrut_match2 branches_match2
	           | p2 e_new2 | p2 e_new2 | rkc2 p2 | e2 | e2 | e21 e22 e23];
          try discriminate.
        destruct callee2 as
          [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
	           | fnamec | fname_makec captures_makec | pc
	           | fnamec argsc | fname_genericc tys_genericc args_genericc
	           | calleec argsc | snamec ltsc tysc fieldsc
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
	            value_has_type env (store_remove x0 s2) v T2).
	        { subst body_env.
	          eapply value_has_type_clear_global_env_local_bounds.
	          exact Hv_removed. }
	        eapply VHT_Compatible.
	        -- exact Hv_removed_env.
        -- apply ty_compatible_b_sound. exact Hcompat.
      * inversion Heval.
    + destruct Hvar_summary as
      (x & args & T_callee & Γ_callee & R_callee & roots_callee &
        T_body & Γ_out & R_body & roots_body &
        Hbody & Hready_args & Hinfer_callee & Hcallee_shape & Hnodup &
        Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    pose (body_env :=
      global_env_with_local_bounds env
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
          (sctx_of_ctx (fn_body_ctx f)) (MkTy u (TFn param_tys ret))
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
        vs ret0 used' Heval_callee H1 H2 H3 Heval_body_env2
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f)) Σ1 R1 (sctx_of_ctx Γ_out) R'
        roots_callee0 arg_roots u param_tys ret
        Hready_args (ProvReady_Var x) Hstore_body_env Hroots Hstore_shadow
        Hroot_shadow Hnamed Hkeys Htyped_shadow H0 Hunique
        Hcallee_summary_runtime)
      as [_ [Hv _]].
      assert (Hv_env :
          value_has_type env
            (store_remove_params (fn_captures fcall)
               (store_remove_params (fn_params fcall) s_body))
            ret0 ret).
      { subst body_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
      eapply VHT_Compatible;
        [ exact Hv_env | apply ty_compatible_b_sound; exact Hcompat ].
    * pose proof
        (typed_env_roots_shadow_safe_evar_infer_core
          body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (fn_body_ctx f) x (MkTy u (TClosure env_lt param_tys ret))
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
          body_env s_fn fname fdef u m bounds body_ty param_tys ret σ
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
          body_env s s_fn s_args s_body x args fname [] fdef fcall vs ret0 used'
          Heval_callee H5 H6 H7 Heval_body_env2
          (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) Σ1 R1 (sctx_of_ctx Γ_out) R'
          roots_callee0 arg_roots u m bounds body_ty param_tys ret σ
          Hready_args Hstore_body_env Hroots Hstore_shadow Hroot_shadow
          Htyped_shadow H0 H4 Htype_params Hcaps_fdef Hbridge Hcallee_route)
        as [_ [Hv _]].
      assert (Hv_env :
          value_has_type env
            (store_remove_params (fn_captures fcall)
               (store_remove_params (fn_params fcall) s_body))
            ret0 (open_bound_ty σ ret)).
      { subst body_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
      eapply VHT_Compatible;
        [ exact Hv_env | apply ty_compatible_b_sound; exact Hcompat ].
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
  - destruct Hcaptured_summary as [Hbase_captured | Hcaptured_summary].
    + destruct Hbase_captured as [Hbase_captured Hready_body].
      destruct Hbase_captured as
        [Hnodup_binding
         (T_body & Γ_out & R_body & roots_body & Hprov_body &
          Htyped_shadow & Hcompat & _ & _)].
      pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
      assert (Hstore_body_env :
          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
      { subst body_env.
        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
      assert (Heval_body_env : eval body_env s (fn_body f) s' v).
      { subst body_env.
        eapply eval_global_env_with_local_bounds. exact Heval. }
      destruct (proj1 eval_preserves_typing_ready_mutual
          body_env s (fn_body f) s' v Heval_body_env
          (fn_outlives f) (fn_lifetimes f)
          (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Γ_out)
          Hready_body Hstore_body_env
          (typed_env_roots_structural
            body_env (fn_outlives f) (fn_lifetimes f)
            (initial_root_env_for_params (fn_params f ++ fn_captures f))
            (sctx_of_ctx (fn_body_ctx f)) (fn_body f) T_body
            (sctx_of_ctx Γ_out) R_body roots_body
            (typed_env_roots_shadow_safe_roots
              body_env (fn_outlives f) (fn_lifetimes f)
              (initial_root_env_for_params (fn_params f ++ fn_captures f))
              (sctx_of_ctx (fn_body_ctx f)) (fn_body f) T_body
              (sctx_of_ctx Γ_out) R_body roots_body Htyped_shadow)))
        as [_ [Hv _]].
      eapply VHT_Compatible.
      * subst body_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hcaptured_summary as
        [Hcaptured_summary | [Hif_summary | Hlocal_captured_summary]].
      * destruct Hcaptured_summary as
	      (fname & captures & args & fcallee & env_lt & captured_tys &
	        T_body & Γ_out & R_body & roots_body &
	        Hbody & Htarget & Hready_args & Hin_callee & Hname_callee &
	        Hdisjoint & Hcaptures & Hcallee_summary &
	        Hnodup & Htyped_shadow & Hcompat & _ & _).
	      pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
	        as Hroot_shadow.
	      pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
	      assert (Hstore_body_env :
	          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	      { subst body_env.
	        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
	      assert (Heval_body_env :
	          eval body_env s (ECallExpr (EMakeClosure fname captures) args) s' v).
	      { subst body_env.
	        rewrite <- Hbody.
	        eapply eval_global_env_with_local_bounds. exact Heval. }
	      rewrite Hbody in Htyped_shadow.
	      destruct Hcallee_summary as
	        [Hnodup_binding
	         (T_callee & Γ_callee & R_callee & roots_callee &
	          Hprov_callee & Htyped_callee & Hcompat_callee &
	          Hexclude_roots_callee & Hexclude_env_callee)].
	      assert (Hnodup_caps :
	        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
	      { rewrite params_ctx_app, ctx_names_app in Hnodup_binding.
	        eapply NoDup_app_right_ts. exact Hnodup_binding. }
	      assert (Hcaptures_body :
	          check_make_closure_captures_exact_sctx_with_env body_env
	            (fn_outlives f) (sctx_of_ctx (fn_body_ctx f)) captures
	            (fn_captures fcallee) = infer_ok (env_lt, captured_tys)).
	      { subst body_env.
	        rewrite
	          check_make_closure_captures_exact_sctx_with_env_global_env_with_local_bounds.
	        exact Hcaptures. }
	      assert (Hcallee_summary_body :
	          callee_body_root_shadow_captured_callee_provenance_summary
	            body_env fcallee).
	      { subst body_env.
	        apply
	          callee_body_root_shadow_captured_callee_provenance_summary_global_env_with_local_bounds.
	        split.
	        - exact Hnodup_binding.
	        - exists T_callee, Γ_callee, R_callee, roots_callee.
	          repeat split;
	            try exact Hprov_callee;
	            try exact Htyped_callee;
	            try exact Hcompat_callee;
	            try exact Hexclude_roots_callee;
	            try exact Hexclude_env_callee. }
	      destruct Hcallee_summary_body as
	        [_ (T_callee_body & Γ_callee_body & R_callee_body &
	            roots_callee_body & Hprov_callee_body & Htyped_callee_body &
	            Hcompat_callee_body & Hexclude_roots_callee_body &
	            Hexclude_env_callee_body)].
	      destruct
	        (eval_make_closure_captured_call_expr_shadow_preserves_typing_with_callee_components
	          body_env (fn_outlives f) (fn_lifetimes f)
	          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
	          args fname captures fcallee s s' v T_body (sctx_of_ctx Γ_out)
	          R_body roots_body env_lt captured_tys T_callee_body
	          Γ_callee_body R_callee_body roots_callee_body
	          Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
	          Heval_body_env Htyped_shadow Hunique Hin_callee Hname_callee
	          Hcaptures_body Hnodup_caps Hready_args Hnodup_binding
	          Hprov_callee_body Htyped_callee_body Hcompat_callee_body
	          Hexclude_roots_callee_body Hexclude_env_callee_body) as [_ Hv].
	      assert (Hv_env : value_has_type env s' v T_body).
	      { subst body_env.
	        eapply value_has_type_clear_global_env_local_bounds. exact Hv. }
	      eapply VHT_Compatible.
	      -- exact Hv_env.
	      -- apply ty_compatible_b_sound. exact Hcompat.
      * destruct Hif_summary as
        (T_body & Γ_out & R_body & roots_body & ret_roots & Hnodup &
          Hexpr_summary & Hcompat & _ & _).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
      destruct
        (eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing
          env (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
          (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
          ret_roots Hexpr_summary s s' v
          (initial_store_for_fn_store_typed env f s Hstore) Hroots Hstore_shadow
          Hroot_shadow Hnamed Hkeys Heval Hunique) as [_ Hv].
      eapply VHT_Compatible.
      -- exact Hv.
      -- apply ty_compatible_b_sound. exact Hcompat.
      * destruct Hlocal_captured_summary as
        (fname & captures & args & m & x & T & direct_body & let_body &
          fcallee & env_lt & captured_tys & T_direct & Γ_direct & R_direct &
          roots_direct & T_let & Γ_let & R_let & roots_let &
          Hbody & Htarget & Hdirect & Hlet & Husage & Hnot_caps &
          Hfresh_cap_names & Hfree_args & Hlocal_args & Hready_args &
          Hin_callee & Hname_callee & Hdisjoint &
          Hcaptures & Hcallee_summary & Hnodup & Htyped_direct &
	          Hcompat_direct & _ & _ & Htyped_let).
	      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	      pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
	      assert (Hstore_body_env :
	          store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
	      { subst body_env.
	        eapply store_typed_global_env_with_local_bounds.
        eapply initial_store_for_fn_store_typed. exact Hstore. }
		      pose proof (lookup_fn_in_unique_by_name
		                    env fname fcallee
		                    Hin_callee Hname_callee Hunique) as Hlookup_callee.
		      rewrite Hbody in Heval.
		      assert (Heval_body_env :
		          eval body_env s
		            (ELet m x T (EMakeClosure fname captures)
		              (ECallExpr (EVar x) args)) s' v).
		      { subst body_env.
		        eapply eval_global_env_with_local_bounds.
		        exact Heval. }
		      rewrite Hlet in Htyped_let.
		      rewrite Hdirect in Htyped_let.
		      rewrite Hdirect in Htyped_direct.
		      dependent destruction Htyped_direct.
		      { repeat match goal with
		      | Hlookup_typed : lookup_fn ?fname0 (env_fns ?env_typed) = Some ?f_typed,
		        Hname_callee0 : fn_name fcallee = ?fname0,
		        Hunique_typed : fn_env_unique_by_name ?env_typed,
		        Hin_callee_typed : In fcallee (env_fns ?env_typed) |- _ =>
		          lazymatch f_typed with
		          | fcallee => fail
		          | _ =>
		              let Hsame := fresh "Hsame_typed_callee" in
		              assert (Hsame : f_typed = fcallee)
		                by (eapply lookup_fn_unique_by_name;
		                    [ exact Hlookup_typed | exact Hin_callee_typed
		                    | exact Hname_callee0 | exact Hunique_typed ]);
		              subst f_typed
		          end
		      | Hin_typed : In ?f_typed (env_fns ?env_typed),
		        Hname_typed : fn_name ?f_typed = ?fname0,
		        Hname_callee0 : fn_name fcallee = ?fname0,
		        Hunique_typed : fn_env_unique_by_name ?env_typed,
		        Hin_callee_typed : In fcallee (env_fns ?env_typed) |- _ =>
		          lazymatch f_typed with
		          | fcallee => fail
		          | _ =>
		              let Hsame := fresh "Hsame_typed_callee" in
		              assert (Hsame : f_typed = fcallee)
		                by (eapply Hunique_typed;
		                    [ exact Hin_typed | exact Hin_callee_typed
		                    | rewrite Hname_typed; symmetry; exact Hname_callee0 ]);
		              subst f_typed
		          end
		      | Hin_typed : In ?f_typed (env_fns ?env_typed),
		        Hname_eq : fn_name fcallee = fn_name ?f_typed,
		        Hunique_typed : fn_env_unique_by_name ?env_typed,
		        Hin_callee_typed : In fcallee (env_fns ?env_typed) |- _ =>
		          lazymatch f_typed with
		          | fcallee => fail
		          | _ =>
		              let Hsame := fresh "Hsame_typed_callee" in
		              assert (Hsame : f_typed = fcallee)
		                by (eapply Hunique_typed;
		                    [ exact Hin_typed | exact Hin_callee_typed
		                    | symmetry; exact Hname_eq ]);
		              subst f_typed
		          end
		      | Hin_typed : In ?f_typed (env_fns ?env_typed),
		        Hname_eq : fn_name ?f_typed = fn_name fcallee,
		        Hunique_typed : fn_env_unique_by_name ?env_typed,
		        Hin_callee_typed : In fcallee (env_fns ?env_typed) |- _ =>
		          lazymatch f_typed with
		          | fcallee => fail
		          | _ =>
		              let Hsame := fresh "Hsame_typed_callee" in
		              assert (Hsame : f_typed = fcallee)
		                by (eapply Hunique_typed;
		                    [ exact Hin_typed | exact Hin_callee_typed
		                    | exact Hname_eq ]);
		              subst f_typed
		          end
		      end.
	      match goal with
		      | Htyped_args_shadow : typed_args_roots_shadow_safe
		          ?env_args (fn_outlives f)
		          (fn_lifetimes f) (initial_root_env_for_fn f)
		          (sctx_of_ctx (fn_body_ctx f)) args
		          (apply_lt_params ?sigma ?params)
		          ?Sigma_args ?R_args ?arg_roots |- _ =>
		          pose proof (typed_args_roots_shadow_safe_roots
		            env_args (fn_outlives f)
		            (fn_lifetimes f) (initial_root_env_for_fn f)
		            (sctx_of_ctx (fn_body_ctx f)) args
		            (apply_lt_params sigma params)
		            Sigma_args R_args arg_roots Htyped_args_shadow)
		            as Htyped_args_roots
      end.
		      dependent destruction Htyped_let.
      match goal with
      | Hmake : typed_env_roots_shadow_safe _ _ _ ?R0 ?Σ0
          (EMakeClosure _ _) _ ?Σ1 ?R1 ?roots1 |- _ =>
          assert (Σ1 = Σ0 /\ R1 = R0 /\ roots1 = []) as Hmake_frame
      end.
      { match goal with
        | Hmake : typed_env_roots_shadow_safe _ _ _ _ _
            (EMakeClosure _ _) _ _ _ _ |- _ =>
            inversion Hmake; subst; repeat split
        end. }
      destruct Hmake_frame as [-> [-> ->]].
			      assert (Hfresh_store_lookup : store_lookup x0 s = None).
		      { match goal with
		        | Hlookup_x : root_env_lookup ?x (initial_root_env_for_fn f) = None
		            |- store_lookup ?x s = None =>
		            eapply store_roots_within_lookup_none; eassumption
		        end. }
	      assert (Hfresh_s : ~ In x0 (store_names s)).
	      { apply store_lookup_none_not_in_store_names.
	        exact Hfresh_store_lookup. }
	      destruct Hcallee_summary as
	        [Hnodup_binding
	         (T_callee & Γ_callee & R_callee & roots_callee &
	          Hprov_callee & Htyped_callee & Hcompat_callee &
	          Hexclude_roots_callee & Hexclude_env_callee)].
	      assert (Hnodup_caps :
	        NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
	      { rewrite params_ctx_app, ctx_names_app in Hnodup_binding.
	        eapply NoDup_app_right_ts. exact Hnodup_binding. }
	      assert (Hcaptures_body :
	          check_make_closure_captures_exact_sctx_with_env body_env
	            (fn_outlives f) (sctx_of_ctx (fn_body_ctx f)) captures
	            (fn_captures fcallee) = infer_ok (env_lt, captured_tys)).
	      { subst body_env.
	        rewrite
	          check_make_closure_captures_exact_sctx_with_env_global_env_with_local_bounds.
	        exact Hcaptures. }
	      assert (Hsame_fdef : fdef = fcallee).
	      { eapply Hunique.
	        - exact H.
	        - exact Hin_callee.
	        - symmetry. exact Hname_callee. }
	      subst fdef.
	      assert (Hlookup_callee_body :
	          lookup_fn (fn_name fcallee) (env_fns body_env) = Some fcallee).
	      { subst body_env. exact Hlookup_callee. }
	      assert (Hcallee_summary_body :
	          callee_body_root_shadow_captured_callee_provenance_summary
	            body_env fcallee).
	      { subst body_env.
	        apply
	          callee_body_root_shadow_captured_callee_provenance_summary_global_env_with_local_bounds.
	        split.
	        - exact Hnodup_binding.
	        - exists T_callee, Γ_callee, R_callee, roots_callee.
	          repeat split;
	            try exact Hprov_callee;
	            try exact Htyped_callee;
	            try exact Hcompat_callee;
	            try exact Hexclude_roots_callee;
	            try exact Hexclude_env_callee. }
	      destruct Hcallee_summary_body as
	        [_ (T_callee_body & Γ_callee_body & R_callee_body &
	            roots_callee_body & Hprov_callee_body & Htyped_callee_body &
	            Hcompat_callee_body & Hexclude_roots_callee_body &
	            Hexclude_env_callee_body)].
		      destruct
		        (eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components
		          body_env (fn_outlives f)
		          (fn_lifetimes f) (initial_root_env_for_fn f)
		          (sctx_of_ctx (fn_body_ctx f)) m x0 T args (fn_name fcallee) captures
		          fcallee _ s s' v _ _ _ env_lt captured_tys
		              T_callee_body Γ_callee_body R_callee_body roots_callee_body
		              Hstore_body_env Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
		              Husage Heval_body_env Hcaptures_body Hnodup_caps Hready_args
		              Htyped_args_roots Hnodup_binding Hprov_callee_body
		              Htyped_callee_body Hcompat_callee_body
		              Hexclude_roots_callee_body Hexclude_env_callee_body
		              Hlookup_callee_body Hfresh_s Hfresh_cap_names Hfree_args
		              Hlocal_args)
		        as [_ Hv].
		      eapply VHT_Compatible.
		      * match goal with
		        | Hret : apply_lt_ty _ (fn_ret fcallee) = fn_ret fcallee |- _ =>
		            rewrite Hret in Hv;
		            subst body_env;
		            eapply value_has_type_clear_global_env_local_bounds;
		            exact Hv
		        | _ =>
		            subst body_env;
		            eapply value_has_type_clear_global_env_local_bounds;
		            exact Hv
		        end.
      * apply ty_compatible_b_sound. exact Hcompat_direct. }
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
Qed.

Theorem env_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_provenance_summary_check_ready env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  eapply callee_body_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact (Hsummary (fn_name f) f Hlookup).
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.


Lemma store_remove_mark_used_store_add_same :
  forall x T v s,
    store_remove x (store_mark_used x (store_add x T v s)) = s.
Proof.
  intros x T v s.
  unfold store_add. simpl. rewrite ident_eqb_refl. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_let_bound_generic_direct_call_roots :
  forall env Omega n R Sigma m x T_hidden fname type_args args T_body
      Sigma_out R_out roots,
    typed_env_roots_shadow_safe env Omega n R Sigma
      (ELet m x T_hidden (ECallGeneric fname type_args args) (EVar x))
      T_body Sigma_out R_out roots ->
    exists T_call Sigma_call R_call roots_call,
      typed_env_roots_shadow_safe env Omega n R Sigma
        (ECallGeneric fname type_args args) T_call Sigma_call R_call
        roots_call /\
      ty_compatible_b Omega T_call T_hidden = true /\
      roots_exclude x roots_call.
Proof.
  intros env Omega n R Sigma m x T_hidden fname type_args args T_body
    Sigma_out R_out roots Htyped.
  dependent destruction Htyped.
  exists T1, Σ1, R1, roots1.
  repeat split; assumption.
Qed.

Lemma let_bound_generic_direct_call_target_expr_shape :
  forall raw_body fname type_args args T_hidden synthetic_body,
    let_bound_generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, T_hidden, synthetic_body) ->
    exists m x,
      raw_body =
        ELet m x T_hidden (ECallGeneric fname type_args args) (EVar x) /\
      synthetic_body =
        ELet m x T_hidden (ECallGeneric fname type_args args) (EVar x).
Proof.
  intros raw_body fname type_args args T_hidden synthetic_body Htarget.
  unfold let_bound_generic_direct_call_target_expr in Htarget.
  destruct raw_body as
    [| | | m x T_ann e1 e2 | | | | | | | | | | | | | | | |];
    try discriminate.
  destruct e1 as
    [| | | | | | | | | callee type_args0 args0 | | | | | | | | | |];
    try discriminate.
  destruct e2 as
    [| | y | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct (ident_eqb x y) eqn:Hsame; try discriminate.
  apply ident_eqb_eq in Hsame. subst y.
  inversion Htarget; subst; clear Htarget.
  exists m, x. split; reflexivity.
Qed.

Lemma eval_let_bound_generic_direct_call_inv :
  forall env s m x T_hidden fname type_args args s' v,
    eval env s
      (ELet m x T_hidden (ECallGeneric fname type_args args) (EVar x))
      s' v ->
    exists s_call v_call s_var,
      eval env s (ECallGeneric fname type_args args) s_call v_call /\
      eval env (store_add x T_hidden v_call s_call) (EVar x) s_var v /\
      s' = store_remove x s_var.
Proof.
  intros env s m x T_hidden fname type_args args s' v Heval.
  inversion Heval; subst; clear Heval.
  exists s1, v1, s2. repeat split; assumption.
Qed.

Lemma if_literal_generic_direct_call_target_expr_shape :
  forall raw_body b fname_then type_args_then args_then fname_else
      type_args_else args_else synthetic_body,
    if_literal_generic_direct_call_target_expr raw_body =
      Some (b, fname_then, type_args_then, args_then,
        fname_else, type_args_else, args_else, synthetic_body) ->
    raw_body = EIf (ELit (LBool b))
      (ECallGeneric fname_then type_args_then args_then)
      (ECallGeneric fname_else type_args_else args_else) /\
    synthetic_body = EIf (ELit (LBool b))
      (ECallGeneric fname_then type_args_then args_then)
      (ECallGeneric fname_else type_args_else args_else).
Proof.
  intros raw_body b fname_then type_args_then args_then fname_else
    type_args_else args_else synthetic_body Htarget.
  unfold if_literal_generic_direct_call_target_expr in Htarget.
  destruct raw_body as
    [| | | | | | | | | | | | | | | | | | | cond e_then e_else];
    try discriminate.
  destruct cond as
    [| lit | | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct lit as [| | b0]; try discriminate.
  destruct e_then as
    [| | | | | | | | | fname_t type_args_t args_t | | | | | | | | | |];
    try discriminate.
  destruct e_else as
    [| | | | | | | | | fname_e type_args_e args_e | | | | | | | | | |];
    try discriminate.
  destruct (ident_eqb fname_t fname_e && ty_list_eqb type_args_t type_args_e)
    eqn:Heq; try discriminate.
  destruct args_t; try discriminate.
  destruct args_e; try discriminate.
  inversion Htarget; subst; clear Htarget.
  split; reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_if_literal_generic_direct_call_roots :
  forall env Omega n R Sigma b fname_then type_args_then args_then fname_else
      type_args_else args_else T_body Sigma_out R_out roots,
    typed_env_roots_shadow_safe env Omega n R Sigma
      (EIf (ELit (LBool b))
        (ECallGeneric fname_then type_args_then args_then)
        (ECallGeneric fname_else type_args_else args_else))
      T_body Sigma_out R_out roots ->
    exists T_then Sigma_then R_then roots_then T_else Sigma_else R_else
        roots_else,
      typed_env_roots_shadow_safe env Omega n R Sigma
        (ECallGeneric fname_then type_args_then args_then)
        T_then Sigma_then R_then roots_then /\
      typed_env_roots_shadow_safe env Omega n R Sigma
        (ECallGeneric fname_else type_args_else args_else)
        T_else Sigma_else R_else roots_else /\
      ty_core T_then = ty_core T_else /\
      T_body = MkTy (usage_max (ty_usage T_then) (ty_usage T_else))
        (ty_core T_then).
Proof.
  intros env Omega n R Sigma b fname_then type_args_then args_then fname_else
    type_args_else args_else T_body Sigma_out R_out roots Htyped.
  dependent destruction Htyped.
  dependent destruction Htyped1.
  exists T2, Σ2, R2, roots2, T3, Σ3, R3, roots3.
  repeat split; assumption || reflexivity.
Qed.

Theorem env_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_summary_check_ready env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hsummary (fn_name f) f Hlookup) as
    [Hold | [Hdirect | [Hgeneric | [Hlet | [Hif | Hnarrow]]]]].
  - eapply callee_body_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hold.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct Hdirect as
      (fname & args & raw_body & synthetic_body & fcallee & T_body &
        Gamma_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
        Hsafe_args & Hin_callee & Hname_callee & Hcallee_summary &
        Hnodup & Htyped_shadow & Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    rewrite Hbody in Heval.
    pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
    assert (Hstore_body_env :
      store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env. apply store_typed_prefix_exact.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hsummary_store_body_env :
      store_function_closure_targets_summary body_env s).
    { subst body_env.
      apply store_function_closure_targets_summary_global_env_with_local_bounds.
      eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
    assert (Heval_body_env : eval body_env s raw_body s' v).
    { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
    assert (Htyped_call_shadow :
      typed_env_roots_shadow_safe body_env
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
        T_body (sctx_of_ctx Gamma_out) R_body roots_body).
    { rewrite <- Hsynthetic. exact Htyped_shadow. }
    assert (Heval_call : eval body_env s (ECall fname args) s' v).
    { unfold direct_call_target_expr in Htarget.
      destruct raw_body; try discriminate.
      - inversion Htarget; subst. exact Heval_body_env.
      - destruct raw_body; try discriminate.
        inversion Htarget; subst.
        apply eval_call_expr_fn_as_call. exact Heval_body_env. }
    assert (Hcallee_summary_body :
      callee_body_root_shadow_store_safe_narrow_summary body_env fcallee).
    { subst body_env.
      apply callee_body_root_shadow_store_safe_narrow_summary_global_env_with_local_bounds.
      - exact Hunique.
      - exact Hcallee_summary. }
    assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_args. }
    pose proof (typed_env_roots_shadow_safe_roots
      body_env (fn_outlives f) (fn_lifetimes f)
      (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
      (ECall fname args) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      Htyped_call_shadow) as Htyped_call.
    dependent destruction Htyped_call.
    assert (fdef = fcallee) as ->.
    { eapply Hunique.
      - exact H.
      - exact Hin_callee.
      - exact (eq_sym Hname_callee). }
    pose proof
      (eval_direct_call_store_safe_narrow_summary_value_prefix_named
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        (fn_name fcallee) args σ _ _ _ s s' v fcallee
        Hsafe_args_body Hcallee_summary_body Hstore_body_env Hroots
        Hshadow Hrn Hnamed Hkeys Hsummary_store_body_env Heval_call
        Hunique Hin_callee Hname_callee H1 H2 H3 H4) as Hv_body.
    assert (Hv_env :
      value_has_type env s' v (apply_lt_ty σ (fn_ret fcallee))).
    { subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
    eapply VHT_Compatible.
    + exact Hv_env.
    + apply ty_compatible_b_sound. exact Hcompat.
  - destruct Hgeneric as
      (fname & type_args & args & raw_body & synthetic_body & fcallee &
        T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
        Hsynthetic & Hsafe_args & Hin_callee & Hname_callee & Htype_params &
        Hbounds & Hcallee_summary & Hnodup & Htyped_shadow & Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    rewrite Hbody in Heval.
    pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
    assert (Hstore_body_env :
      store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env. apply store_typed_prefix_exact.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hsummary_store_body_env :
      store_function_closure_targets_summary body_env s).
    { subst body_env.
      apply store_function_closure_targets_summary_global_env_with_local_bounds.
      eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
    assert (Heval_body_env : eval body_env s raw_body s' v).
    { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
    assert (Htyped_call_shadow :
      typed_env_roots_shadow_safe body_env
        (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (ECallGeneric fname type_args args)
        T_body (sctx_of_ctx Gamma_out) R_body roots_body).
    { rewrite <- Hsynthetic. exact Htyped_shadow. }
    assert (Heval_call : eval body_env s
      (ECallGeneric fname type_args args) s' v).
    { unfold generic_direct_call_target_expr in Htarget.
      destruct raw_body; try discriminate.
      inversion Htarget; subst. exact Heval_body_env. }
    assert (Hcallee_summary_body :
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        body_env 10000 fcallee type_args).
    { subst body_env.
      eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
      - exact Hunique.
      - exact Hcallee_summary. }
    assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_args. }
    pose proof (typed_env_roots_shadow_safe_roots
      body_env (fn_outlives f) (fn_lifetimes f)
      (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
      (ECallGeneric fname type_args args) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Htyped_call_shadow) as Htyped_call.
    dependent destruction Htyped_call.
    assert (fdef = fcallee) as ->.
    { eapply Hunique.
      - exact H.
      - exact Hin_callee.
      - exact (eq_sym Hname_callee). }
    pose proof
      (eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel
        body_env (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        (fn_name fcallee) type_args args σ _ _ _ s s' v fcallee 10000
        Hsafe_args_body Hcallee_summary_body Hstore_body_env Hroots
        Hshadow Hrn Hnamed Hkeys Hsummary_store_body_env Heval_call
        Hunique Hin_callee Hname_callee H1 H4 H5) as Hv_body.
    assert (Hv_env :
      value_has_type env s' v
        (apply_lt_ty σ
          (subst_type_params_ty type_args (fn_ret fcallee)))).
    { subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
    eapply VHT_Compatible.
    + exact Hv_env.
    + apply ty_compatible_b_sound. exact Hcompat.
  - destruct Hlet as
      (fname & type_args & args & T_hidden & raw_body & synthetic_body &
        fcallee & T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
        Hsafe_args & Hin_callee & Hname_callee & Htype_params & Hbounds &
        Hcallee_summary & Hnodup & Htyped_shadow & Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    rewrite Hbody in Heval.
    pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
    assert (Hstore_body_env :
      store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env. apply store_typed_prefix_exact.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hsummary_store_body_env :
      store_function_closure_targets_summary body_env s).
    { subst body_env.
      apply store_function_closure_targets_summary_global_env_with_local_bounds.
      eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
    assert (Heval_body_env : eval body_env s raw_body s' v).
    { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
    assert (Hcallee_summary_body :
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        body_env 10000 fcallee type_args).
    { subst body_env.
      eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
      - exact Hunique.
      - exact Hcallee_summary. }
    assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_args. }
    set (call_fname := fname) in *.
    set (call_type_args := type_args) in *.
    set (call_args := args) in *.
    destruct (let_bound_generic_direct_call_target_expr_shape
      raw_body call_fname call_type_args call_args T_hidden synthetic_body Htarget)
      as (m & x & Hraw_shape & Hsynthetic_shape).
    rewrite Hraw_shape in Heval_body_env.
    rewrite Hsynthetic_shape in Htyped_shadow.
    destruct (eval_let_bound_generic_direct_call_inv
      body_env s m x T_hidden call_fname call_type_args call_args s' v
      Heval_body_env) as
      (s_call & v_call & s_var & Heval_call & Hvar & Hfinal_store).
    rewrite Hfinal_store.
    destruct (typed_env_roots_shadow_safe_let_bound_generic_direct_call_roots
      body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) m x T_hidden call_fname call_type_args call_args T_body
      (sctx_of_ctx Gamma_out) R_body roots_body Htyped_shadow)
      as (T_call & Sigma_call & R_call & roots_call & Htyped_call_shadow &
          Hcall_compat & _).
    pose proof (typed_env_roots_shadow_safe_roots
      body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f))
      (ECallGeneric call_fname call_type_args call_args) T_call Sigma_call R_call
      roots_call Htyped_call_shadow) as Htyped_call.
    dependent destruction Htyped_call.
    assert (fdef = fcallee) as ->.
    { eapply Hunique.
      - exact H.
      - exact Hin_callee.
      - exact (eq_sym Hname_callee). }
    destruct (eval_generic_direct_call_store_safe_narrow_summary_exact_package_prefix_named_fuel
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (fn_name fcallee) call_type_args
      call_args σ _ _ _ s s_call v_call fcallee 10000
      Hsafe_args_body Hcallee_summary_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Hsummary_store_body_env Heval_call Hunique Hin_callee
      Hname_callee H1 H4 H5) as [Hpkg _].
    pose proof (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg)
      as Hv_body.
    assert (Hv_env :
      value_has_type env s_call v_call
        (apply_lt_ty σ
          (subst_type_params_ty call_type_args (fn_ret fcallee)))).
    { eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
    dependent destruction Hvar;
      match goal with
      | Hlookup : store_lookup ?x (store_add ?x ?T ?vcall ?scall) = Some _ |- _ =>
          rewrite store_lookup_store_add_same in Hlookup;
          inversion Hlookup; subst; clear Hlookup
      end;
      try rewrite store_remove_store_add_same;
      try rewrite store_remove_mark_used_store_add_same;
      try (eapply VHT_Compatible;
        [ eapply VHT_Compatible;
          [ exact Hv_env | apply ty_compatible_b_sound; exact Hcall_compat ]
        | apply ty_compatible_b_sound; exact Hcompat ]).
  - destruct Hif as
      (b & fname_then & type_args_then & args_then & fname_else &
        type_args_else & args_else & raw_body & synthetic_body & fthen &
        felse & T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
        Hsafe_then & Hsafe_else & Hin_then & Hname_then & Hin_else &
        Hname_else & Htype_params_then & Htype_params_else & Hbounds_then &
        Hbounds_else & Hthen_summary & Helse_summary & Hnodup & Htyped_shadow &
        Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    rewrite Hbody in Heval.
    pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
    assert (Hstore_body_env :
      store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env. apply store_typed_prefix_exact.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hsummary_store_body_env :
      store_function_closure_targets_summary body_env s).
    { subst body_env.
      apply store_function_closure_targets_summary_global_env_with_local_bounds.
      eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
    assert (Heval_body_env : eval body_env s raw_body s' v).
    { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
    assert (Hthen_summary_body :
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        body_env 10000 fthen type_args_then).
    { subst body_env.
      eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
      - exact Hunique.
      - exact Hthen_summary. }
    assert (Helse_summary_body :
      callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
        body_env 10000 felse type_args_else).
    { subst body_env.
      eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
      - exact Hunique.
      - exact Helse_summary. }
    assert (Hsafe_then_body : store_safe_function_value_call_args body_env args_then).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_then. }
    assert (Hsafe_else_body : store_safe_function_value_call_args body_env args_else).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_else. }
    set (runtime_env := body_env) in *.
    set (start_store := s) in *.
    set (then_fname := fname_then) in *.
    set (then_type_args := type_args_then) in *.
    set (then_args := args_then) in *.
    set (else_fname := fname_else) in *.
    set (else_type_args := type_args_else) in *.
    set (else_args := args_else) in *.
    destruct (if_literal_generic_direct_call_target_expr_shape
      raw_body b then_fname then_type_args then_args else_fname
      else_type_args else_args synthetic_body Htarget)
      as [Hraw_shape Hsynthetic_shape].
    rewrite Hraw_shape in Heval_body_env.
    rewrite Hsynthetic_shape in Htyped_shadow.
    destruct (typed_env_roots_shadow_safe_if_literal_generic_direct_call_roots
      body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) b then_fname then_type_args then_args
      else_fname else_type_args else_args T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Htyped_shadow)
      as (T_then & Sigma_then & R_then & roots_then & T_else & Sigma_else &
          R_else & roots_else & Htyped_then_shadow & Htyped_else_shadow &
          Hbranches_core & Hif_type).
    destruct b.
    + inversion Heval_body_env; subst; clear Heval_body_env;
        match goal with
        | Hlit : eval _ _ (ELit (LBool true)) _ _ |- _ =>
            inversion Hlit; subst; clear Hlit
        end.
      pose proof (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (ECallGeneric then_fname then_type_args then_args) T_then
        Sigma_then R_then roots_then Htyped_then_shadow) as Htyped_call.
      dependent destruction Htyped_call.
      assert (fdef = fthen) as ->.
      { eapply Hunique.
        - exact H.
        - exact Hin_then.
        - match goal with
          | Hname : fn_name fdef = fn_name fthen |- _ => exact Hname
          | Hname : fn_name fthen = fn_name fdef |- _ => exact (eq_sym Hname)
          end. }
      set (runtime_env := global_env_with_local_bounds env (fn_bounds f)) in *.
      pose proof
        (eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel
          runtime_env (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
          (fn_name fthen) then_type_args then_args σ Σ' R' arg_roots start_store s' v fthen 10000
          Hsafe_then_body Hthen_summary_body Hstore_body_env Hroots
          Hshadow Hrn Hnamed Hkeys Hsummary_store_body_env H6
          Hunique Hin_then eq_refl H1 H4 H5) as Hv_body.
      assert (Hv_env :
        value_has_type env s' v
          (apply_lt_ty σ
            (subst_type_params_ty then_type_args (fn_ret fthen)))).
      { subst runtime_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
      pose proof (value_has_type_if_left_result env s' v
        (apply_lt_ty σ
          (subst_type_params_ty then_type_args (fn_ret fthen)))
        T_else Hv_env) as Hv_if.
      exact (value_has_type_compatible env s' (fn_outlives f) v _ _
        Hv_if (ty_compatible_b_sound _ _ _ Hcompat)).
    + inversion Heval_body_env; subst; clear Heval_body_env;
        match goal with
        | Hlit : eval _ _ (ELit (LBool false)) _ _ |- _ =>
            inversion Hlit; subst; clear Hlit
        end.
      pose proof (typed_env_roots_shadow_safe_roots
        body_env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
        (sctx_of_ctx (fn_body_ctx f))
        (ECallGeneric else_fname else_type_args else_args) T_else
        Sigma_else R_else roots_else Htyped_else_shadow) as Htyped_call.
      dependent destruction Htyped_call.
      assert (fdef = felse) as ->.
      { eapply Hunique.
        - exact H.
        - exact Hin_else.
        - match goal with
          | Hname : fn_name fdef = fn_name felse |- _ => exact Hname
          | Hname : fn_name felse = fn_name fdef |- _ => exact (eq_sym Hname)
          end. }
      set (runtime_env := global_env_with_local_bounds env (fn_bounds f)) in *.
      pose proof
        (eval_generic_direct_call_store_safe_narrow_summary_value_prefix_named_fuel
          runtime_env (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
          (fn_name felse) else_type_args else_args σ Σ' R' arg_roots start_store s' v felse 10000
          Hsafe_else_body Helse_summary_body Hstore_body_env Hroots
          Hshadow Hrn Hnamed Hkeys Hsummary_store_body_env H6
          Hunique Hin_else eq_refl H1 H4 H5) as Hv_body.
      assert (Hv_env :
        value_has_type env s' v
          (apply_lt_ty σ
            (subst_type_params_ty else_type_args (fn_ret felse)))).
      { subst runtime_env.
        eapply value_has_type_clear_global_env_local_bounds. exact Hv_body. }
      pose proof (value_has_type_if_right_result env s' v T_then
        (apply_lt_ty σ
          (subst_type_params_ty else_type_args (fn_ret felse)))
        Hv_env Hbranches_core) as Hv_if.
      exact (value_has_type_compatible env s' (fn_outlives f) v _ _
        Hv_if (ty_compatible_b_sound _ _ _ Hcompat)).
  - destruct Hnarrow as
      (T_body & Gamma_out & R_body & roots_body & ret_roots & Hnodup &
        Hnarrow & Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    destruct (expr_root_shadow_store_safe_narrow_summary_checked_runtime_package
      env (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (fn_body f) T_body
      (sctx_of_ctx Gamma_out) R_body roots_body ret_roots Hnarrow
      s s' v
      (initial_store_for_fn_store_typed env f s Hstore)
      Hroots Hshadow Hrn Hnamed Hkeys
      (initial_store_for_fn_closure_targets_summary env f s Hstore)
      Heval Hunique)
      as [_ [Hv _]].
    eapply VHT_Compatible.
    + exact Hv.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  unfold check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hvalidated Hsummary_check].
  eapply env_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready;
    eauto.
  - apply check_program_env_alpha_validated_unique. exact Hvalidated.
  - apply check_env_root_shadow_captured_call_provenance_summary_ready.
    exact Hsummary_check.
Qed.

Theorem check_program_env_alpha_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    check_program_env_alpha env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns (alpha_normalize_global_env env)) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f s s' v Hcheck Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready;
    eauto.
  - apply check_program_env_alpha_unique. exact Hcheck.
  - apply check_env_root_shadow_captured_call_provenance_summary_ready.
    apply check_program_env_alpha_captured_summary. exact Hcheck.
Qed.

Theorem check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready :
  forall env env' f s s' v,
    check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary env = true ->
    infer_program_env_alpha_elab env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
Proof.
  intros env env' f s s' v Hcheck Helab Hinitial Hin Hstore Heval.
  unfold
    check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    in Hcheck.
  apply andb_true_iff in Hcheck as [Hunique_b Hsummary_check].
  eapply env_root_shadow_captured_call_provenance_summary_big_step_safe_checked_initial_ready;
    eauto.
  - eapply infer_program_env_alpha_elab_unique_by_name; eassumption.
  - rewrite Helab in Hsummary_check.
    apply check_env_root_shadow_captured_call_provenance_summary_ready.
    exact Hsummary_check.
Qed.

Theorem infer_full_env_alpha_big_step_safe_with_root_sidecar :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env (alpha_normalize_global_env env) f = infer_ok (T, Γ') ->
    infer_full_env_roots (alpha_normalize_global_env env) f R0 =
      infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn (alpha_normalize_global_env env) f s ->
    preservation_direct_call_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    root_env_store_roots_named R0 s ->
    root_env_store_keys_named R0 s ->
    fn_env_unique_by_name (alpha_normalize_global_env env) ->
    env_fns_preservation_ready (alpha_normalize_global_env env) ->
    direct_call_callee_body_root_check_evidence
      (global_env_with_local_bounds (alpha_normalize_global_env env)
        (fn_bounds f)) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready
    Hcallee_roots Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_ready;
    eassumption.
Qed.
