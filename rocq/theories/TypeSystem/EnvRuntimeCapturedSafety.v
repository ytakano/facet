From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeNonCapturingSafety.
From Facet.TypeSystem Require Import TypeSafetyDirectCallWrappers
  TypeSafetyBasePreservationControl.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.


Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_ready :
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary.
Proof.
  intros env fname fdef fcall used used' fname_body args_body
    [Hcomponent Hbody_summary] _Hin _Hname Hrename Htarget.
  split.
  - pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds.
    eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
    exact Hbody_summary.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds;
      eassumption.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_component_body_summary_ready :
  forall env,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider
      env
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary.
Proof.
  intros env.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_scoped_package.
  exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_ready.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider :
  forall component_ready,
    (forall env fname fdef fcall used used' fname_body args_body
        synthetic_body,
      component_ready env fdef ->
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds fcall)) fname_body) ->
    (forall env fdef,
      component_ready env fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env fdef) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      component_ready.
Proof.
  intros component_ready Hsummary_at Hcomponent_summary env fname fdef
    fcall used used' fname_body args_body Hcomponent Hin Hname Hrename
    Htarget.
  split.
  - eapply Hsummary_at; eassumption.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds;
      eauto.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_route_summary_at_provider :
  forall env component_ready,
    (forall fname fdef fcall used used' fname_body args_body
        synthetic_body,
      component_ready env fdef ->
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds fcall)) fname_body) ->
    (forall fdef,
      component_ready env fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env fdef) ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider
      env component_ready.
Proof.
  intros env component_ready Hsummary_at Hcomponent_summary fname fdef
    fcall used used' fname_body args_body Hcomponent Hin Hname Hrename
    Htarget.
  split.
  - eapply Hsummary_at; eassumption.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds;
      eauto.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready :
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    (fun env fdef =>
      fn_env_unique_by_name env /\
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        env fdef /\
      check_fn_root_shadow_no_capture_direct_call_component_exact_closure
        env fdef = true).
Proof.
  eapply
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider.
  - intros env fname fdef fcall used used' fname_body args_body
      synthetic_body (Hunique & Hcomponent & Hexact) Hin _Hname Hrename
      Htarget ftarget Hlookup.
    destruct (direct_call_target_expr_alpha_rename_fn_def_inv
                used fdef fcall used' fname_body args_body synthetic_body
                Hrename Htarget) as (args0 & Htarget_original).
    pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds in Hlookup.
    rewrite Hbounds.
    eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
    eapply (component_body_no_capture_direct_call_component_target_in_of_exact_closure_check
      env fdef fname_body args0 (ECall fname_body args0) ftarget).
    + exact Hunique.
    + exact Hin.
    + exact Hcomponent.
    + exact Hexact.
    + exact Htarget_original.
    + exact Hlookup.
  - intros env fdef (_Hunique & Hcomponent & _Hexact). exact Hcomponent.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_summary_at_check_provider :
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_at_check_in_provider env ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider
      env
      (fun env0 fdef =>
        env0 = env /\
        In fdef (env_fns env) /\
        check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
          env fdef = true).
Proof.
  intros env Hunique Hsummary_provider.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_route_summary_at_provider.
  - intros fname fdef fcall used used' fname_body args_body
      synthetic_body (_Henv & Hin & Hcomponent_check) _Hin Hname Hrename
      Htarget.
    destruct (direct_call_target_expr_alpha_rename_fn_def_inv
                used fdef fcall used' fname_body args_body synthetic_body
                Hrename Htarget) as (args0 & Htarget_original).
    pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds.
    eapply Hsummary_provider; eassumption.
  - intros fdef (_Henv & _Hin & Hcomponent_check).
    eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
    exact Hcomponent_check.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_summary_at_check_provider_local_bounds_family :
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_at_check_in_provider env ->
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
      (fun env0 fdef =>
        exists bounds,
          env0 = global_env_with_local_bounds env bounds /\
          In fdef (env_fns env) /\
          check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
            env fdef = true).
Proof.
  intros env Hunique Hsummary_provider.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider.
  - intros env0 fname fdef fcall used used' fname_body args_body
      synthetic_body (bounds & -> & Hin & Hcomponent_check) _Hin _Hname
      Hrename Htarget.
    destruct (direct_call_target_expr_alpha_rename_fn_def_inv
                used fdef fcall used' fname_body args_body synthetic_body
                Hrename Htarget) as (args0 & Htarget_original).
    pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds.
    eapply Hsummary_provider; eassumption.
  - intros env0 fdef (bounds & -> & _Hin & Hcomponent_check).
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_global_env_with_local_bounds.
    + exact Hunique.
    + eapply check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound.
      exact Hcomponent_check.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_exact_closure_component_ready :
  forall env,
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider
      env
      (fun env fdef =>
        fn_env_unique_by_name env /\
        callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
          env fdef /\
        check_fn_root_shadow_no_capture_direct_call_component_exact_closure
          env fdef = true).
Proof.
  intros env.
  eapply store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_in_provider_of_scoped_package.
  exact store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready.
Qed.

Lemma store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_provider :
  (forall env, component_body_synthetic_direct_call_ready_summary_provider env) ->
  store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary.
Proof.
  intros Hprovider.
  eapply
    store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider.
  - intros env fname fdef fcall used used' fname_body args_body
      synthetic_body Hcomponent _Hin _Hname Hrename _Htarget.
    pose proof (alpha_rename_fn_def_bounds used fdef fcall used' Hrename)
      as Hbounds.
    rewrite Hbounds.
    eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
    eapply Hprovider. exact Hcomponent.
  - intros env fdef Hcomponent. exact Hcomponent.
Qed.

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
           | callee_generic tys_call args_call_generic
	         | sname lts tys fields
	           | enum_name variant_name lts_enum tys_enum payloads | scrut_match branches_match
	         | p e_new | p e_new | rk p | e | e | e1 e2 e3];
        try discriminate.
      * destruct e1 as
          [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
	           | fname_value | fname_make1 captures_make1 | p1
	           | fname1 args1 | fname_generic1 tys_generic1 args_generic1
	           | callee1 args1 | callee_generic1 tys_call1 args_call_generic1
             | sname1 lts1 tys1 fields1
	             | enum_name1 variant_name1 lts_enum1 tys_enum1 payloads1 | scrut_match1 branches_match1
	           | p1 e_new1 | p1 e_new1 | rkc1 p1 | e1 | e1 | e11 e12 e13];
          try discriminate.
        destruct e2 as
          [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
	           | fname2 | fname_make2 captures_make2 | p2
	           | fname2 args2 | fname_generic2 tys_generic2 args_generic2
	           | callee2 args2 | callee_generic2 tys_call2 args_call_generic2
             | sname2 lts2 tys2 fields2
	             | enum_name2 variant_name2 lts_enum2 tys_enum2 payloads2 | scrut_match2 branches_match2
	           | p2 e_new2 | p2 e_new2 | rkc2 p2 | e2 | e2 | e21 e22 e23];
          try discriminate.
        destruct callee2 as
          [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
	           | fnamec | fname_makec captures_makec | pc
	           | fnamec argsc | fname_genericc tys_genericc args_genericc
	           | calleec argsc | callee_genericc tys_callc args_call_genericc
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
    [| | | m x T_ann e1 e2 | | | | | | | | | | | | | | | | |];
    try discriminate.
  destruct e1 as
    [| | | | | | | | | callee type_args0 args0 | | | | | | | | | | |];
    try discriminate.
  destruct e2 as
    [| | y | | | | | | | | | | | | | | | | | |]; try discriminate.
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
    [| | | | | | | | | | | | | | | | | | | | cond e_then e_else];
    try discriminate.
  destruct cond as
    [| lit | | | | | | | | | | | | | | | | | | |]; try discriminate.
  destruct lit as [| | b0]; try discriminate.
  destruct e_then as
    [| | | | | | | | | fname_t type_args_t args_t | | | | | | | | | | |];
    try discriminate.
  destruct e_else as
    [| | | | | | | | | fname_e type_args_e args_e | | | | | | | | | | |];
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


Lemma eval_call_as_generic_nil :
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    eval env s (ECallGeneric fname [] args) s' v.
Proof.
  intros env s fname args s' v Heval.
  inversion Heval; subst; clear Heval.
  rewrite <- (apply_type_params_nil (fn_params fcall)).
  eapply Eval_CallGeneric; try eassumption.
  rewrite apply_type_params_nil.
  rewrite subst_type_params_expr_nil.
  assumption.
Qed.

Lemma callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary_instantiated_nil :
  forall env fdef,
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10001 fdef [].
Proof.
  intros env fdef Hsummary.
  eapply callee_body_root_shadow_captured_call_generic_direct_instantiated_nil_fuel.
  exact Hsummary.
Qed.

Lemma generic_direct_call_target_expr_subst_not_preservation_ready :
  forall type_args raw_body fname call_type_args args synthetic_body,
    generic_direct_call_target_expr raw_body =
      Some (fname, call_type_args, args, synthetic_body) ->
    preservation_ready_expr (subst_type_params_expr type_args raw_body) ->
    False.
Proof.
  intros type_args raw_body fname call_type_args args synthetic_body Htarget Hready.
  unfold generic_direct_call_target_expr in Htarget.
  destruct raw_body; try discriminate.
  inversion Htarget; subst; clear Htarget.
  simpl in Hready.
  dependent destruction Hready.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    (forall bounds,
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
        (global_env_with_local_bounds env bounds)) ->
    eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary Hbridge_bounds Hpackage
    Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hsummary_body :
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      body_env).
  { subst body_env.
    eapply env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    exact Hsummary. }
  destruct Hpackage as [Hprefix _].
  destruct
    (Hprefix body_env s fname args s' v Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hsafe_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_prefix [Hv_body [_Hpres [_Hroots_ready
        [_Hvroots [_Hshadow_ready _Hrn_ready]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_body.
  - subst body_env. apply Hbridge_bounds.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_evidence :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    (forall bounds,
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
        (global_env_with_local_bounds env bounds)) ->
    eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary_body_evidence Hbridge_bounds
    Hpackage Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_body :
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
      body_env).
  { subst body_env. exact Hsummary_body_evidence. }
  destruct Hpackage as [Hprefix _].
  destruct
    (Hprefix body_env s fname args s' v Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_prefix [Hv_body [_Hpres [_Hroots_ready
        [_Hvroots [_Hshadow_ready _Hrn_ready]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_body.
  - subst body_env. apply Hbridge_bounds.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_evidence :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fcall,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall))) ->
    eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary_at Hbody_evidence Hpackage
    Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  destruct Hpackage as [Hprefix _].
  destruct
    (Hprefix body_env s fname args s' v Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_prefix [Hv_body [_Hpres [_Hroots_ready
        [_Hvroots [_Hshadow_ready _Hrn_ready]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env. exact Hbody_evidence.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.


Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_call_route_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fcall fname_body args_body synthetic_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall)) fname_body) ->
    (forall fcall fcall_inner,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall))
          (fn_bounds fcall_inner))) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Hsummary_body_at Hbody_evidence Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_at_call_route_final_roots_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
      Hroot_names Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_body [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env. exact Hsummary_body_at.
  - subst body_env. exact Hbody_evidence.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_prefix_scope_call_route_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fcall fname_body args_body synthetic_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall)) fname_body) ->
    (forall fcall fcall_inner fname_body args_body synthetic_body,
      direct_call_target_expr (fn_body fcall_inner) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall))
          (fn_bounds fcall_inner)) fname_body) ->
    (forall fcall fcall_inner,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall))
          (fn_bounds fcall_inner))) ->
    (forall fcall fcall_inner fcall_inner2,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds
              (global_env_with_local_bounds env (fn_bounds f))
              (fn_bounds fcall))
            (fn_bounds fcall_inner))
          (fn_bounds fcall_inner2))) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Hsummary_body_at Hnested_summary_body_at Hbody_evidence
    Hnested_body_evidence Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_at_prefix_scope_call_route_final_roots_core
      Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
      Hroot_names Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_body [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env. exact Hsummary_body_at.
  - subst body_env. exact Hnested_summary_body_at.
  - subst body_env. exact Hbody_evidence.
  - subst body_env. exact Hnested_body_evidence.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_summary_at_call_route_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef) ->
    (forall fdef fcall used used' fname_body args_body synthetic_body,
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall)) fname_body) ->
    (forall fcall fcall_inner,
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence
        (global_env_with_local_bounds
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall))
          (fn_bounds fcall_inner))) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Htarget_component Hsummary_body_at Hbody_evidence Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_summary_at_call_route_final_roots_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
      Hroot_names Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_body [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env.
    intros fdef_call fcall used used' fname_body args_body synthetic_body_nested
      Hin_call Hname_call Hrename Htarget_body.
    eapply Hsummary_body_at.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * eapply lookup_fn_in_unique_by_name; eassumption.
    + exact Hrename.
    + exact Htarget_body.
  - subst body_env. exact Hbody_evidence.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_nested_evidence_at_call_route_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef) ->
    (forall fdef fcall used used' fname_body args_body synthetic_body,
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall)) fname_body) ->
    (forall fdef fcall used used',
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      forall fcall_inner,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds
            (global_env_with_local_bounds
              (global_env_with_local_bounds env (fn_bounds f))
              (fn_bounds fcall))
            (fn_bounds fcall_inner))) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Htarget_component Hsummary_body_at Hbody_evidence Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_nested_evidence_call_route_final_roots_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
      Hroot_names Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_body [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env.
    intros fdef_call fcall used used' fname_body args_body synthetic_body_nested
      Hin_call Hname_call Hrename Htarget_body.
    eapply Hsummary_body_at.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * eapply lookup_fn_in_unique_by_name; eassumption.
    + exact Hrename.
    + exact Htarget_body.
  - subst body_env.
    intros fdef_call fcall used used' Hin_call Hname_call Hrename.
    eapply Hbody_evidence.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * eapply lookup_fn_in_unique_by_name; eassumption.
    + exact Hrename.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef) ->
    (forall fdef fcall used used' fname_body args_body synthetic_body,
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      alpha_rename_fn_def used fdef = (fcall, used') ->
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds
          (global_env_with_local_bounds env (fn_bounds f))
          (fn_bounds fcall)) fname_body) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Htarget_component Hsummary_body_at Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  assert (Hstore_body_prefix :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { eapply store_typed_prefix_exact. exact Hstore_body_env. }
  destruct
    (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_prefix_store_final_roots_core
      Hscope_synthetic eval_preserves_typing_ready_prefix_mutual
      eval_preserves_typing_roots_ready_prefix_mutual Hroots_ready Hroot_names
      Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hsafe_args_body Hstore_body_prefix Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [Hstore_body_prefix' [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env.
    intros fdef_call fcall used used' fname_body args_body synthetic_body_nested
      Hin_call Hname_call Hrename Htarget_body.
    eapply Hsummary_body_at.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * eapply lookup_fn_in_unique_by_name; eassumption.
    + exact Hrename.
    + exact Htarget_body.
  - intros fdef_call fcall used used' s_args s_body vs ret R_args arg_roots
      fname_body args_body T_body0 Gamma_out0 R_body0 roots_body0 Hin_call
      Hname_call Hrename Htarget_body Hready_body Htyped_body Hunique_body
      Hsummary_body Hevidence_body Hstore_bind Hroots_bind Hshadow_bind
      Hrn_bind Hnamed_bind Hkeys_bind Heval_nested.
    assert (Hsafe_args_body_nested :
      store_safe_function_value_call_args
        (global_env_with_local_bounds body_env (fn_bounds fcall)) args_body).
    { subst body_env.
      eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds.
      - eapply Htarget_component.
        + rewrite Hbody. exact Htarget.
        + eapply lookup_fn_in_unique_by_name; eassumption.
      - exact Hrename.
      - exact Htarget_body. }
    eapply Hsynthetic_route; try eassumption.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall)) fname_body) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hsummary_at
    Htarget_component Hsummary_body_at Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  assert (Hstore_body_prefix :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { eapply store_typed_prefix_exact. exact Hstore_body_env. }
  destruct
    (eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_prefix_store_final_roots_core
      Hscope_synthetic eval_preserves_typing_ready_prefix_mutual
      eval_preserves_typing_roots_ready_prefix_mutual Hroots_ready Hroot_names
      Hroot_keys body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hsafe_args_body Hstore_body_prefix Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [Hstore_body_prefix' [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env.
    intros fdef_call fcall used used' fname_body args_body synthetic_body_nested
      Hin_call Hname_call Hrename Htarget_body.
    pose proof (lookup_fn_in_unique_by_name
      (global_env_with_local_bounds env (fn_bounds f)) fname fdef_call
      Hin_call Hname_call
      ltac:(unfold fn_env_unique_by_name in *; simpl; exact Hunique))
      as Hlookup_call.
    eapply Hsummary_body_at.
    + rewrite Hbody. exact Htarget.
    + exact Hlookup_call.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * exact Hlookup_call.
    + exact Hrename.
    + exact Htarget_body.
  - intros fdef_call fcall used used' s_args s_body vs ret R_args arg_roots
      fname_body args_body T_body0 Gamma_out0 R_body0 roots_body0 Hin_call
      Hname_call Hrename Htarget_body Hready_body Htyped_body Hunique_body
      Hsummary_body Hevidence_body Hstore_bind Hroots_bind Hshadow_bind
      Hrn_bind Hnamed_bind Hkeys_bind Heval_nested.
    assert (Hlookup_call :
      lookup_fn fname (env_fns body_env) = Some fdef_call).
    { subst body_env.
      eapply lookup_fn_in_unique_by_name; eassumption. }
    assert (Hsafe_args_body_nested :
      store_safe_function_value_call_args
        (global_env_with_local_bounds body_env (fn_bounds fcall)) args_body).
    { subst body_env.
      eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds.
      - eapply Htarget_component.
        + rewrite Hbody. exact Htarget.
        + exact Hlookup_call.
      - exact Hrename.
      - exact Htarget_body. }
    eapply Hsynthetic_route; try eassumption.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    (forall fname args synthetic_body,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
        (global_env_with_local_bounds env (fn_bounds f)) fname) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef) ->
    (forall fname args synthetic_body fdef,
      direct_call_target_expr (fn_body f) = Some (fname, args, synthetic_body) ->
      lookup_fn fname
        (env_fns (global_env_with_local_bounds env (fn_bounds f))) =
        Some fdef ->
      callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
        (global_env_with_local_bounds env (fn_bounds f)) fdef ->
      forall fcall used used' fname_body args_body synthetic_body_nested,
        alpha_rename_fn_def used fdef = (fcall, used') ->
        direct_call_target_expr (fn_body fcall) =
          Some (fname_body, args_body, synthetic_body_nested) ->
        fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
          (global_env_with_local_bounds
            (global_env_with_local_bounds env (fn_bounds f))
            (fn_bounds fcall)) fname_body) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hsummary_at
    Htarget_component Hsummary_body_at Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hready_args_body : preservation_ready_args args).
  { eapply store_safe_function_value_call_args_preservation_ready.
    exact Hsafe_args_body. }
  assert (Hsummary_target :
    fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at
      body_env fname).
  { subst body_env. eapply Hsummary_at. rewrite Hbody. exact Htarget. }
  assert (Hstore_body_prefix :
    store_typed_prefix body_env s (sctx_of_ctx (fn_body_ctx f))).
  { eapply store_typed_prefix_exact. exact Hstore_body_env. }
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_prefix_store_final_roots_core
      Hscope_synthetic eval_preserves_typing_ready_prefix_mutual
      eval_preserves_typing_roots_ready_prefix_mutual Hroots_ready Hroot_names
      Hroot_keys Hstatic body_env s s' v fname args Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hready_args_body Hstore_body_prefix Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [Hstore_body_prefix' [Hv_body [_Hpres_body [_Hroots_body
        [_Hvroots_body [_Hshadow_body _Hrn_body]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_target.
  - subst body_env.
    intros fdef_call fcall used used' fname_body args_body synthetic_body_nested
      Hin_call Hname_call Hrename Htarget_body.
    pose proof (lookup_fn_in_unique_by_name
      (global_env_with_local_bounds env (fn_bounds f)) fname fdef_call
      Hin_call Hname_call
      ltac:(unfold fn_env_unique_by_name in *; simpl; exact Hunique))
      as Hlookup_call.
    eapply Hsummary_body_at.
    + rewrite Hbody. exact Htarget.
    + exact Hlookup_call.
    + eapply Htarget_component.
      * rewrite Hbody. exact Htarget.
      * exact Hlookup_call.
    + exact Hrename.
    + exact Htarget_body.
  - intros fdef_call fcall used used' s_args s_body vs ret R_args arg_roots
      fname_body args_body T_body0 Gamma_out0 R_body0 roots_body0 Hin_call
      Hname_call Hrename Htarget_body Hready_body Htyped_body Hunique_body
      Hsummary_body Hevidence_body Hstore_bind Hroots_bind Hshadow_bind
      Hrn_bind Hnamed_bind Hkeys_bind Heval_nested.
    assert (Hlookup_call :
      lookup_fn fname (env_fns body_env) = Some fdef_call).
    { subst body_env.
      eapply lookup_fn_in_unique_by_name; eassumption. }
    assert (Hsafe_args_body_nested :
      store_safe_function_value_call_args
        (global_env_with_local_bounds body_env (fn_bounds fcall)) args_body).
    { subst body_env.
      eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds.
      - eapply Htarget_component.
        + rewrite Hbody. exact Htarget.
        + exact Hlookup_call.
      - exact Hrename.
      - exact Htarget_body. }
    eapply Hsynthetic_route; try eassumption.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_store_safe_summary_evidence :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    (forall bounds,
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge
        (global_env_with_local_bounds env bounds)) ->
    eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary_body_evidence Hbridge_bounds
    Hpackage Hcomponent Hinitial Hstore Heval.
  destruct Hcomponent as
    (fname & args & raw_body & synthetic_body & fcallee & T_body &
      Gamma_out & R_body & roots_body & _Hcaptures & Hbody & Htarget &
      Hsynthetic & Hsafe_args & _Hin_callee & _Hname_callee &
      _Hcallee_captures & Hnodup & Htyped_shadow & Hcompat & _Hroots &
      _Henv).
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hshadow [Hnamed Hkeys]]].
  pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
  rewrite Hbody in Heval.
  pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
  assert (Hstore_body_env :
    store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
  { subst body_env.
    eapply store_typed_global_env_with_local_bounds.
    eapply initial_store_for_fn_store_typed. exact Hstore. }
  assert (Heval_body_env : eval body_env s raw_body s' v).
  { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
  assert (Htyped_call_shadow :
    typed_env_roots_shadow_safe body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { rewrite <- Hsynthetic. exact Htyped_shadow. }
  assert (Htyped_call :
    typed_env_roots body_env
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
      T_body (sctx_of_ctx Gamma_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_roots. exact Htyped_call_shadow. }
  assert (Heval_call : eval body_env s (ECall fname args) s' v).
  { unfold direct_call_target_expr in Htarget.
    destruct raw_body; try discriminate.
    - inversion Htarget; subst. exact Heval_body_env.
    - destruct raw_body; try discriminate.
      inversion Htarget; subst.
      apply eval_call_expr_fn_as_call. exact Heval_body_env. }
  assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
  { subst body_env.
    apply store_safe_function_value_call_args_global_env_with_local_bounds.
    exact Hsafe_args. }
  assert (Hsummary_body :
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      body_env).
  { subst body_env. exact Hsummary_body_evidence. }
  destruct Hpackage as [Hprefix _].
  destruct
    (Hprefix body_env s fname args s' v Heval_call
      (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
      (sctx_of_ctx (fn_body_ctx f)) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hsafe_args_body Hstore_body_env Hroots Hshadow Hrn
      Hnamed Hkeys Htyped_call)
    as [_Hstore_prefix [Hv_body [_Hpres [_Hroots_ready
        [_Hvroots [_Hshadow_ready _Hrn_ready]]]]]].
  - unfold fn_env_unique_by_name in *; subst body_env; simpl. exact Hunique.
  - exact Hsummary_body.
  - subst body_env. apply Hbridge_bounds.
  - eapply VHT_Compatible.
    + subst body_env.
      eapply value_has_type_clear_global_env_local_bounds. exact Hv_body.
    + apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hsummary Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact Hsummary.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_final_roots_and_cleanup;
      eassumption.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready :
  forall env f s s' v,
    fn_env_unique_by_name env ->
    callee_body_root_shadow_captured_call_store_safe_summary env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hunique Hsummary Hinitial Hstore Heval.
  destruct Hsummary as
    [Hold | [Hdirect | [Hgeneric | [Hlet | [Hif | [Hlocal | Hnarrow]]]]]].
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
        Hbounds & Hcallee_ready & Hcallee_summary & Hnodup &
        Htyped_shadow & Hcompat & _ & _).
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
          Hcall_compat & Hexclude_call).
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
          (fn_name fthen) then_type_args then_args σ Σ' R' arg_roots s s' v fthen 10000
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
          (fn_name felse) else_type_args else_args σ Σ' R' arg_roots s s' v felse 10000
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
  - destruct Hlocal as
      (x_local & fname & args & raw_body & synthetic_body & fcallee &
        T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
        Hsafe_args & Hnot_free_args & Hnot_local_args & Hin_callee &
        Hname_callee & Hcallee_summary & Hnodup & Htyped_shadow &
        Hcompat & _ & _).
    destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
      [Hroots [Hshadow [Hnamed Hkeys]]].
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hrn.
    rewrite Hbody in Heval.
    pose (body_env := global_env_with_local_bounds env (fn_bounds f)).
    assert (Hstore_body_env :
      store_typed body_env s (sctx_of_ctx (fn_body_ctx f))).
    { subst body_env.
      eapply store_typed_global_env_with_local_bounds.
      eapply initial_store_for_fn_store_typed. exact Hstore. }
    assert (Hsafe_args_body : store_safe_function_value_call_args body_env args).
    { subst body_env.
      apply store_safe_function_value_call_args_global_env_with_local_bounds.
      exact Hsafe_args. }
    assert (Heval_body_env : eval body_env s raw_body s' v).
    { subst body_env. eapply eval_global_env_with_local_bounds. exact Heval. }
    unfold local_fn_value_call_target_expr_with_binder in Htarget.
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
        [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
         | fname_value | fname_make1 captures_make1 | p1
         | fname1 args1 | fname_generic1 tys_generic1 args_generic1
         | callee1 args1 | callee_generic1 tys_call1 args_call_generic1
         | sname1 lts1 tys1 fields1
           | enum_name1 variant_name1 lts_enum1 tys_enum1 payloads1 | scrut_match1 branches_match1
         | p1 e_new1 | p1 e_new1 | rkc1 p1 | e1 | e1 | e11 e12 e13];
        try discriminate.
      destruct e2 as
        [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
         | fname2 | fname_make2 captures_make2 | p2
         | fname2 args2 | fname_generic2 tys_generic2 args_generic2
         | callee2 args2 | callee_generic2 tys_call2 args_call_generic2
         | sname2 lts2 tys2 fields2
           | enum_name2 variant_name2 lts_enum2 tys_enum2 payloads2 | scrut_match2 branches_match2
         | p2 e_new2 | p2 e_new2 | rkc2 p2 | e2 | e2 | e21 e22 e23];
        try discriminate.
      destruct callee2 as
        [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
         | fnamec | fname_makec captures_makec | pc
         | fnamec argsc | fname_genericc tys_genericc args_genericc
         | calleec argsc | callee_genericc tys_callc args_call_genericc
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
          (ELet ?m0 ?x_local ?T0 (EFn ?fname0)
            (ECallExpr (EVar ?x_local) ?args0)) ?sfinal ?vfinal |- _ =>
          assert (Heval_synthetic :
            eval body_env s0
              (ELet m0 x_local T0 (EFn fname0) (ECall fname0 args0))
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
          typed_env_roots_shadow_safe ?env0 ?Omega0 ?n0 ?R0 ?Sigma0
            (ECall ?fname0 ?args0) ?T0 ?Sigma' ?R' ?roots |- _ =>
          pose proof (typed_env_roots_shadow_safe_roots
            env0 Omega0 n0 R0 Sigma0 (ECall fname0 args0) T0 Sigma' R' roots
            Htyped_call_shadow)
            as Htyped_call
      end.
      dependent destruction Htyped_call.
      assert (Hfresh_store : store_lookup x_local s1 = None)
        by (eapply store_roots_within_lookup_none; eassumption).
      assert (Hadd_pres :
        store_ref_targets_preserved body_env s1
          (store_add x_local T (VClosure (fn_name fcallee) []) s1))
        by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
      assert (Hv_closure_actual :
        value_has_type body_env s1
          (VClosure (fn_name fcallee) []) (fn_value_ty fdef))
        by (eapply VHT_ClosureIn with
              (fname := fn_name fcallee) (fdef := fdef);
            [ exact H | exact x1 | eassumption ]).
      assert (Hv_closure :
        value_has_type body_env s1
          (VClosure (fn_name fcallee) []) T)
        by (eapply VHT_Compatible;
            [ exact Hv_closure_actual
            | apply ty_compatible_b_sound; exact H0 ]).
      assert (Hstore_add :
        store_typed body_env
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f))))
        by (eapply store_typed_add;
            [ exact Hstore_body_env | exact Hv_closure | exact Hadd_pres ]).
      assert (Hroots_add :
        store_roots_within (root_env_add x_local [] (initial_root_env_for_fn f))
          (store_add x_local T (VClosure (fn_name fcallee) []) s1))
        by (eapply store_add_roots_within;
            [ exact Hroots | eassumption | constructor ]).
      assert (Hshadow_add :
        store_no_shadow
          (store_add x_local T (VClosure (fn_name fcallee) []) s1))
        by (apply store_no_shadow_add; assumption).
      assert (Hrn_add :
        root_env_no_shadow (root_env_add x_local [] (initial_root_env_for_fn f)))
        by (apply root_env_no_shadow_add; assumption).
      assert (Hempty_named : root_set_store_roots_named [] s1)
        by (intros z Hin_empty; contradiction).
      assert (Hnamed_add :
        root_env_store_roots_named
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (store_add x_local T (VClosure (fn_name fcallee) []) s1))
        by (eapply root_env_store_roots_named_add_env_store_add;
            eassumption).
      assert (Hkeys_add :
        root_env_store_keys_named
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (store_add x_local T (VClosure (fn_name fcallee) []) s1))
        by (eapply root_env_store_keys_named_add_env_store_add;
            exact Hkeys).
      assert (Hcallee_summary_body :
        callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
          body_env 10001 fcallee []).
      { subst body_env.
        eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
        - exact Hunique.
        - eapply callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary_instantiated_nil.
          exact Hcallee_summary. }
      pose proof (eval_call_as_generic_nil body_env
        (store_add x_local T (VClosure (fn_name fcallee) []) s1)
        (fn_name fcallee) args s2 v H8) as Heval_call_generic.
      assert (Hstore_add_prefix :
        store_typed_prefix body_env
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f))))
        by (apply store_typed_prefix_exact; exact Hstore_add).
      assert (Hsummary_store_body_env :
        store_function_closure_targets_summary body_env s1).
      { subst body_env.
        apply store_function_closure_targets_summary_global_env_with_local_bounds.
        eapply initial_store_for_fn_closure_targets_summary. exact Hstore. }
      assert (Hfresh_names : ~ In x_local (store_names s1)).
      { apply store_lookup_none_not_in_store_names. exact Hfresh_store. }
      assert (Hrefs_base : store_refs_exclude_root x_local s1).
      { eapply store_roots_within_named_fresh_refs_exclude_root;
          eassumption. }
      assert (Hrel_hidden :
        store_hidden_frame_rel x_local T (VClosure (fn_name fcallee) [])
          (store_add x_local T (VClosure (fn_name fcallee) []) s1) s1)
        by apply store_hidden_frame_rel_here.
      assert (Hfdef1_eq : fdef1 = fcallee).
      { eapply Hunique.
        - exact H11.
        - exact Hin_callee.
        - exact x. }
      subst fdef1.
      assert (Hpkg_body :
        generic_direct_call_runtime_package body_env s1
          (store_remove x_local s2) v (sctx_remove x_local Σ')
          (root_env_remove x_local R') arg_roots
          (apply_lt_ty σ (fn_ret fcallee))).
      { refine (eval_generic_direct_call_hidden_frame_package_from_stripped_body
          body_env x_local T (VClosure (fn_name fcallee) [])
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          s1 s2 (fn_name fcallee) [] args v (sctx_remove x_local Σ')
          (root_env_remove x_local R') arg_roots
          (apply_lt_ty σ (fn_ret fcallee)) Hrel_hidden
          (store_safe_function_value_call_args_preservation_ready body_env args
            Hsafe_args_body)
          Hnot_free_args Hnot_local_args Hrefs_base Heval_call_generic _).
        intros fdef_outer fcall_outer used_outer s_args_hidden s_args_base
          vs_outer s_body_hidden Hlookup_outer Hcaps_outer Hrel_args_outer
          Heval_args_hidden Heval_args_base Hrefs_args_base Hvs_refs_outer
          Hrename_outer Heval_body_hidden Hfinal_hidden.
        assert (fdef_outer = fcallee) as ->.
        { eapply lookup_fn_unique_by_name;
            [ exact Hlookup_outer | exact Hin_callee | reflexivity
            | exact Hunique ]. }
        destruct Hcallee_summary as
          (fname_nested & type_args_nested & args_static & raw_body_nested &
            synthetic_body_nested & fcallee_nested & T_body_nested &
            Gamma_nested & R_nested & roots_nested & Hbody_nested &
            Htarget_nested & Hsynthetic_nested & Hsafe_nested & Hin_nested &
            Hname_nested & Harity_nested & Hbounds_nested & Hready_nested &
            Hsummary_nested & Hnodup_nested & Htyped_nested & Hcompat_nested &
            Hexcl_roots_nested & Hexcl_env_nested).
        assert (Hbody_nested_nil :
          raw_body_nested = subst_type_params_expr [] (fn_body fcallee)).
        { rewrite subst_type_params_expr_nil. symmetry. exact Hbody_nested. }
        assert (Hsafe_nested_body :
          store_safe_function_value_call_args body_env args_static).
        { subst body_env.
          apply store_safe_function_value_call_args_global_env_with_local_bounds.
          exact Hsafe_nested. }
        assert (Hnodup_nested_nil :
          NoDup (ctx_names
            (params_ctx (apply_type_params [] (fn_params fcallee))))).
        { rewrite apply_type_params_nil. exact Hnodup_nested. }
        assert (Hexcl_roots_nested_nil :
          roots_exclude_params (apply_type_params [] (fn_params fcallee))
            roots_nested).
        { rewrite apply_type_params_nil. exact Hexcl_roots_nested. }
        assert (Htyped_nested_body :
          typed_env_roots_shadow_safe
            (global_env_with_local_bounds body_env
              (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
            (fn_outlives fcallee) (fn_lifetimes fcallee)
            (initial_root_env_for_fn fcallee)
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcallee)))
            synthetic_body_nested T_body_nested (sctx_of_ctx Gamma_nested)
            R_nested roots_nested).
        { subst body_env.
          rewrite subst_type_params_trait_bounds_nil.
          rewrite subst_type_params_ctx_nil.
          exact Htyped_nested. }
        pose proof (preservation_ready_args_implies_provenance_ready_closure
          args (store_safe_function_value_call_args_preservation_ready
            body_env args Hsafe_args_body)) as Hprov_args_outer.
        assert (Htyped_outer_args_nil :
          typed_args_roots body_env (fn_outlives f) (fn_lifetimes f)
            (root_env_add x_local [] (initial_root_env_for_fn f))
            (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f))) args
            (apply_lt_params σ (apply_type_params [] (fn_params fcallee)))
            Σ' R' arg_roots).
        { subst body_env. rewrite apply_type_params_nil. exact H15. }
        destruct (generic_direct_call_target_alpha_rename_subst_type_params_runtime_typed_args_call_frame
          body_env (fn_outlives f) (fn_lifetimes f)
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f))) _ _ _ args
          [] σ fcallee fcall_outer used_outer fname_nested type_args_nested
          args_static raw_body_nested synthetic_body_nested T_body_nested
          Gamma_nested R_nested roots_nested
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          s_args_hidden vs_outer
          Hbody_nested_nil Htarget_nested Hsynthetic_nested Hsafe_nested_body
          Hcaps_outer Hrename_outer Hnodup_nested_nil Htyped_nested_body
          Hexcl_roots_nested_nil Htyped_outer_args_nil Hsafe_args_body Heval_args_hidden Hprov_args_outer
          Hstore_add_prefix Hroots_add Hshadow_add Hrn_add Hnamed_add Hkeys_add)
          as (args_runtime & fcallee_runtime & sigma_nested &
              nested_arg_roots & Sigma_nested & R_nested_runtime &
              Hbody_runtime & Hsafe_runtime & Htyped_runtime &
              Hin_runtime & Hname_runtime & Hcaps_runtime & Houtlives_runtime &
              Hret_runtime & Hexcl_runtime_roots & Hnested_roots_subset).
        pose proof (store_hidden_frame_rel_name_in x_local T
          (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
          Hrel_args_outer) as Hused_outer.
        destruct (alpha_rename_fn_def_used_name_fresh_params_and_body_locals
          (store_names s_args_hidden) fcallee fcall_outer used_outer []
          x_local Hrename_outer Hused_outer)
          as [Hnotin_outer_params Hnotin_outer_body_locals].
        assert (Hnot_free_runtime :
          ~ In x_local (args_free_vars_ts args_runtime)).
        { intro Hin_runtime_free.
          apply Hnotin_outer_params.
          assert (Hsafe_runtime_bounds :
            store_safe_function_value_call_args
              (global_env_with_local_bounds body_env
                (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
              args_runtime).
          { apply store_safe_function_value_call_args_global_env_with_local_bounds.
            exact Hsafe_runtime. }
          pose proof (store_safe_function_value_call_args_typed_roots_free_vars_ctx_names
            (global_env_with_local_bounds body_env
              (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
            (fn_outlives fcallee) (fn_lifetimes fcallee)
            (call_param_root_env (apply_type_params [] (fn_params fcall_outer))
              arg_roots R')
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
            args_runtime
            (apply_lt_params sigma_nested
              (apply_type_params type_args_nested (fn_params fcallee_runtime)))
            Sigma_nested R_nested_runtime nested_arg_roots
            Hsafe_runtime_bounds Htyped_runtime x_local Hin_runtime_free)
            as Hin_ctx.
          rewrite subst_type_params_ctx_nil in Hin_ctx.
          rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall_outer) in Hin_ctx.
          - unfold sctx_of_ctx in Hin_ctx.
            rewrite apply_type_params_nil.
            exact Hin_ctx.
          - rewrite <- Hcaps_outer.
            eapply alpha_rename_fn_def_captures. exact Hrename_outer. }
        assert (Hnot_local_runtime :
          ~ In x_local (args_local_store_names args_runtime)).
        { intro Hin_runtime_local.
          apply Hnotin_outer_body_locals.
          rewrite Hbody_runtime. simpl. exact Hin_runtime_local. }
        assert (Heval_nested_hidden :
          eval body_env
            (bind_params (apply_type_params [] (fn_params fcall_outer))
              vs_outer s_args_hidden)
            (ECallGeneric fname_nested type_args_nested args_runtime)
            s_body_hidden v).
        { rewrite <- Hbody_runtime. exact Heval_body_hidden. }
        pose (ps_outer := apply_type_params [] (fn_params fcall_outer)).
        assert (Hrel_bind_outer :
          store_hidden_frame_rel x_local T (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)).
        { subst ps_outer.
          eapply store_hidden_frame_rel_bind_params; eassumption. }
        assert (Hrefs_bind_outer :
          store_refs_exclude_root x_local
            (bind_params ps_outer vs_outer s_args_base)).
        { subst ps_outer.
          eapply bind_params_refs_exclude_root; eassumption. }
        assert (fcallee_runtime = fcallee_nested) as ->.
        { eapply Hunique.
          - exact Hin_runtime.
          - exact Hin_nested.
          - rewrite Hname_runtime. exact (eq_sym Hname_nested). }
        assert (Hsummary_nested_body :
          callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
            body_env 10000 fcallee_nested type_args_nested).
        { subst body_env.
          eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
          - exact Hunique.
          - exact Hsummary_nested. }
        assert (Hstore_bind_prefix :
          store_typed_prefix body_env (bind_params ps_outer vs_outer s_args_base)
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))).
        { subst ps_outer.
          rewrite subst_type_params_ctx_nil.
          rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall_outer).
          - rewrite apply_type_params_nil.
            eapply bind_params_store_typed_prefix.
            + eapply alpha_rename_fn_def_params_nodup_ctx_names.
              exact Hrename_outer.
            + eapply store_hidden_frame_rel_params_fresh_in_store_base.
              * exact Hrel_args_outer.
              * eapply alpha_rename_fn_def_params_fresh_in_store.
                exact Hrename_outer.
            + pose proof (alpha_rename_fn_def_shape
                (store_names s_args_hidden) fcallee fcall_outer used_outer
                Hrename_outer) as Hshape_outer.
              destruct Hshape_outer as [_ [_ Hparams_alpha_outer]].
              eapply eval_args_values_have_types_params_alpha.
              * exact Hparams_alpha_outer.
              * eapply eval_args_values_have_types_apply_lt_params_inv.
                destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
                  body_env
                  (store_add x_local T (VClosure (fn_name fcallee) []) s1)
                  args s_args_hidden vs_outer Heval_args_hidden
                  (fn_outlives f) (fn_lifetimes f)
                  (root_env_add x_local [] (initial_root_env_for_fn f))
                  (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f)))
                  (apply_lt_params σ (apply_type_params [] (fn_params fcallee)))
                  Σ' R' arg_roots Hprov_args_outer Hstore_add_prefix Hroots_add
                  Hshadow_add Hrn_add Htyped_outer_args_nil)
                  as [_ [Hargs_values_outer _]].
                rewrite apply_type_params_nil in Hargs_values_outer.
                rewrite <- (store_hidden_frame_rel_remove_base x_local T
                  (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
                  Hrel_args_outer).
                eapply eval_args_values_have_types_store_remove_excluding_root;
                  eassumption.
          - rewrite <- Hcaps_outer.
            eapply alpha_rename_fn_def_captures. exact Hrename_outer. }
        assert (Hsummary_bind_base :
          store_function_closure_targets_summary body_env
            (bind_params ps_outer vs_outer s_args_base)).
        { subst ps_outer.
          rewrite apply_type_params_nil.
          eapply store_safe_function_value_call_args_bind_params_summary
            with (args := args) (s := s1); eassumption. }
        assert (Hunique_body_env : fn_env_unique_by_name body_env).
        { subst body_env. unfold fn_env_unique_by_name in *. simpl. exact Hunique. }
        destruct (proj1 (proj2 eval_preserves_typing_roots_ready_prefix_mutual)
          body_env
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          args s_args_hidden vs_outer Heval_args_hidden
          (fn_outlives f) (fn_lifetimes f)
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f)))
          (apply_lt_params σ (apply_type_params [] (fn_params fcallee)))
          Σ' R' arg_roots Hprov_args_outer Hstore_add_prefix Hroots_add
          Hshadow_add Hrn_add Htyped_outer_args_nil)
          as [Hstore_args_hidden [Hargs_values_outer_sigma
              [Hpres_args_hidden [Hroots_args_hidden
              [Harg_roots_outer_values [Hshadow_args_hidden Hrn_args_hidden]]]]]].
        pose proof (alpha_rename_fn_def_shape
          (store_names s_args_hidden) fcallee fcall_outer used_outer
          Hrename_outer) as Hshape_outer_bind.
        destruct Hshape_outer_bind as [_ [_ Hparams_alpha_outer_bind]].
        assert (Hargs_values_outer_fcall :
          eval_args_values_have_types body_env (fn_outlives f) s_args_hidden
            vs_outer ps_outer).
        { subst ps_outer.
          rewrite apply_type_params_nil.
          eapply eval_args_values_have_types_params_alpha.
          - exact Hparams_alpha_outer_bind.
          - eapply eval_args_values_have_types_apply_lt_params_inv.
            rewrite apply_type_params_nil in Hargs_values_outer_sigma.
            exact Hargs_values_outer_sigma. }
        assert (Hnodup_outer_bind : NoDup (ctx_names (params_ctx ps_outer))).
        { subst ps_outer.
          rewrite apply_type_params_nil.
          eapply alpha_rename_fn_def_params_nodup_ctx_names.
          exact Hrename_outer. }
        assert (Hfresh_outer_bind : params_fresh_in_store ps_outer s_args_hidden).
        { subst ps_outer.
          rewrite apply_type_params_nil.
          eapply alpha_rename_fn_def_params_fresh_in_store.
          exact Hrename_outer. }
        destruct (eval_args_bind_params_call_param_root_env_ready
          body_env
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          args s_args_hidden vs_outer (fn_outlives f) (fn_lifetimes f)
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f)))
          (apply_lt_params σ (apply_type_params [] (fn_params fcallee)))
          Σ' R' arg_roots ps_outer Heval_args_hidden Hprov_args_outer
          Htyped_outer_args_nil Hroots_add Hshadow_add Hrn_add
          Hnodup_outer_bind Hfresh_outer_bind Hargs_values_outer_fcall)
          as [Hroots_bind_hidden [Hshadow_bind_hidden [Hrn_bind_outer _]]].
        destruct (store_safe_function_value_call_args_typed_roots_store_named
          body_env (fn_outlives f) (fn_lifetimes f)
          (root_env_add x_local [] (initial_root_env_for_fn f))
          (sctx_add x_local T m (sctx_of_ctx (fn_body_ctx f)))
          args (apply_lt_params σ (apply_type_params [] (fn_params fcallee)))
          Σ' R' arg_roots
          (store_add x_local T (VClosure (fn_name fcallee) []) s1)
          s_args_hidden vs_outer Hsafe_args_body Htyped_outer_args_nil
          Heval_args_hidden Hnamed_add Hkeys_add)
          as [Hnamed_args_hidden [Harg_roots_named_hidden Hkeys_args_hidden]].
        assert (Hnamed_bind_hidden :
          root_env_store_roots_named (call_param_root_env ps_outer arg_roots R')
            (bind_params ps_outer vs_outer s_args_hidden)).
        { eapply root_env_store_roots_named_call_param_bind_params;
            eassumption. }
        assert (Hkeys_bind_hidden :
          root_env_store_keys_named (call_param_root_env ps_outer arg_roots R')
            (bind_params ps_outer vs_outer s_args_hidden)).
        { eapply root_env_store_keys_named_call_param_bind_params;
            eassumption. }
        assert (Hroots_bind_outer_base :
          store_roots_within (call_param_root_env ps_outer arg_roots R')
            (bind_params ps_outer vs_outer s_args_base)).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            Hrel_bind_outer).
          apply store_remove_roots_within_same_env.
          exact Hroots_bind_hidden. }
        assert (Hshadow_bind_outer_base :
          store_no_shadow (bind_params ps_outer vs_outer s_args_base)).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            Hrel_bind_outer).
          apply store_no_shadow_remove.
          exact Hshadow_bind_hidden. }
        assert (Harg_roots_exclude_x : Forall (roots_exclude x_local) arg_roots).
        { apply roots_exclude_root_sets_union_inv. exact H6. }
        assert (Htail_excludes_x : root_env_excludes x_local R').
        { unfold root_env_excludes in *.
          intros y roots Hlookup_root Hneq.
          eapply H7.
          - rewrite root_env_lookup_remove_neq by (intro Heq; apply Hneq; symmetry; exact Heq). exact Hlookup_root.
          - exact Hneq. }
        assert (Houter_call_excludes_x :
          root_env_excludes x_local (call_param_root_env ps_outer arg_roots R')).
        { pose (p_hidden := MkParam m x_local T).
          assert (Hroots_protected :
            Forall (roots_exclude_params [p_hidden]) arg_roots).
          { eapply Forall_impl.
            - intros roots Hroot z Hin_protected.
              simpl in Hin_protected. destruct Hin_protected as [Hz | Hnil].
              + subst z. exact Hroot.
              + contradiction.
            - exact Harg_roots_exclude_x. }
          assert (Htail_protected : root_env_excludes_params [p_hidden] R').
          { intros z Hin_protected. simpl in Hin_protected.
            destruct Hin_protected as [Hz | Hnil].
            - subst z. exact Htail_excludes_x.
            - contradiction. }
          assert (Htail_excludes_removed :
            root_env_excludes x_local (root_env_remove_params ps_outer R')).
          { eapply root_env_excludes_remove_params; eassumption. }
          assert (Htail_protected_removed :
            root_env_excludes_params [p_hidden]
              (root_env_remove_params ps_outer R')).
          { intros z Hin_protected. simpl in Hin_protected.
            destruct Hin_protected as [Hz | Hnil].
            - subst z. exact Htail_excludes_removed.
            - contradiction. }
          pose proof (root_env_add_params_roots_preserves_excludes_params
            ps_outer arg_roots [p_hidden]
            (root_env_remove_params ps_outer R') Hroots_protected
            Htail_protected_removed) as Hprotected.
          unfold call_param_root_env.
          unfold root_env_excludes_params in Hprotected. simpl in Hprotected.
          specialize (Hprotected x_local (or_introl eq_refl)).
          exact Hprotected. }
        assert (Hroots_bind_outer_base_removed :
          store_roots_within
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (bind_params ps_outer vs_outer s_args_base)).
        { eapply store_roots_within_remove_env.
          - exact Hroots_bind_outer_base.
          - intros se Hin_store_base.
            rewrite <- (store_hidden_frame_rel_remove_base x_local T
              (VClosure (fn_name fcallee) [])
              (bind_params ps_outer vs_outer s_args_hidden)
              (bind_params ps_outer vs_outer s_args_base)
              Hrel_bind_outer) in Hin_store_base.
            eapply (store_no_shadow_remove_no_name x_local
              (bind_params ps_outer vs_outer s_args_hidden));
              eassumption. }
        assert (Hnamed_bind_outer_base_removed :
          root_env_store_roots_named
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (bind_params ps_outer vs_outer s_args_base)).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            Hrel_bind_outer).
          eapply root_env_store_roots_named_store_remove_excluding.
          - intros y roots Hlookup_root_removed.
            destruct (ident_eqb y x_local) eqn:Hyx.
            + apply ident_eqb_eq in Hyx. subst y.
              rewrite root_env_lookup_remove_eq_no_shadow in Hlookup_root_removed
                by exact Hrn_bind_outer. discriminate.
            + unfold root_env_excludes in Houter_call_excludes_x.
              eapply Houter_call_excludes_x.
              * replace (root_env_lookup y
                  (root_env_remove x_local
                    (call_param_root_env ps_outer arg_roots R')))
                  with (root_env_lookup y
                    (call_param_root_env ps_outer arg_roots R'))
                  in Hlookup_root_removed.
                -- exact Hlookup_root_removed.
                -- symmetry. apply root_env_lookup_remove_neq.
                   intro Heq. subst y. rewrite ident_eqb_refl in Hyx. discriminate.
              * intro Heq. subst y. rewrite ident_eqb_refl in Hyx. discriminate.
          - eapply root_env_store_roots_named_remove_env; eassumption.
          - intros z Hin_store_name Hneq. apply store_names_remove_keeps_other; assumption. }
        assert (Hkeys_bind_outer_base_removed :
          root_env_store_keys_named
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (bind_params ps_outer vs_outer s_args_base)).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            Hrel_bind_outer).
          eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
        assert (Hargs_values_outer_base_type :
          eval_args_values_have_types body_env (fn_outlives f) s_args_base
            vs_outer (apply_type_params [] (fn_params fcallee))).
        { eapply eval_args_values_have_types_apply_lt_params_inv.
          rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          eapply eval_args_values_have_types_store_remove_excluding_root;
            eassumption. }
        pose proof (alpha_rename_fn_def_shape (store_names s_args_hidden)
          fcallee fcall_outer used_outer Hrename_outer) as Hshape_outer_final.
        destruct Hshape_outer_final as [_ [Hret_alpha_outer Hparams_alpha_outer_final]].
        assert (Hargs_values_outer_base_fcall :
          eval_args_values_have_types body_env (fn_outlives f) s_args_base
            vs_outer ps_outer).
        { subst ps_outer.
          rewrite apply_type_params_nil.
          eapply eval_args_values_have_types_params_alpha.
          - exact Hparams_alpha_outer_final.
          - rewrite apply_type_params_nil in Hargs_values_outer_base_type.
            exact Hargs_values_outer_base_type. }
        assert (Hfresh_outer_base : params_fresh_in_store ps_outer s_args_base).
        { eapply store_hidden_frame_rel_params_fresh_in_store_base;
            eassumption. }
        assert (Hframe_scope_outer_start :
          store_frame_scope ps_outer (sctx_of_ctx (params_ctx ps_outer))
            (bind_params ps_outer vs_outer s_args_base) s_args_base).
        { eapply store_frame_scope_bind_params.
          exact Hargs_values_outer_base_fcall. }
        assert (Hframe_fresh_outer_start :
          store_frame_static_fresh (sctx_of_ctx (params_ctx ps_outer))
            s_args_base).
        { eapply params_fresh_in_store_frame_static_fresh.
          exact Hfresh_outer_base. }
        assert (Hcover_outer_removed :
          root_env_covers_params ps_outer
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))).
        { eapply root_env_covers_params_remove_non_param.
          - apply call_param_root_env_covers_params.
            + exact Hnodup_outer_bind.
            + rewrite (Forall2_length Harg_roots_outer_values).
              eapply eval_args_values_have_types_length.
              exact Hargs_values_outer_base_fcall.
          - exact Hnotin_outer_params. }
        assert (Hnested_bundle :
          generic_direct_call_runtime_package body_env
            (bind_params ps_outer vs_outer s_args_base)
            (store_remove x_local s_body_hidden) v
            Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots
            (apply_lt_ty sigma_nested
              (subst_type_params_ty type_args_nested (fn_ret fcallee_nested))) /\
          exists vs_inner s_inner_base,
            eval_args
              (global_env_with_local_bounds body_env
                (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
              (bind_params ps_outer vs_outer s_args_base) args_runtime
              s_inner_base vs_inner /\
            typed_args_roots
              (global_env_with_local_bounds body_env
                (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
              (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local
                (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              args_runtime
              (apply_lt_params sigma_nested
                (apply_type_params type_args_nested (fn_params fcallee_nested)))
              Sigma_nested (root_env_remove x_local R_nested_runtime)
              nested_arg_roots /\
            provenance_ready_args args_runtime /\
            store_remove x_local s_body_hidden = s_inner_base /\
            store_hidden_frame_rel x_local T (VClosure (fn_name fcallee) [])
              s_body_hidden (store_remove x_local s_body_hidden)).
        { split.
          - refine (eval_generic_direct_call_hidden_frame_package_from_stripped_body
            body_env x_local T (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            s_body_hidden fname_nested type_args_nested args_runtime v
            Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots
            (apply_lt_ty sigma_nested
              (subst_type_params_ty type_args_nested (fn_ret fcallee_nested)))
            Hrel_bind_outer
            (store_safe_function_value_call_args_preservation_ready body_env
              args_runtime Hsafe_runtime)
            Hnot_free_runtime Hnot_local_runtime Hrefs_bind_outer
            Heval_nested_hidden _).
          intros fdef_inner fcall_inner used_inner s_inner_hidden s_inner_base
            vs_inner s_inner_body_hidden Hlookup_inner Hcaps_inner
            Hrel_inner_args Heval_inner_hidden Heval_inner_base
            Hrefs_inner_base Hvs_inner_refs Hrename_inner Heval_inner_body_hidden
            Hfinal_inner_hidden.
          assert (fdef_inner = fcallee_nested) as ->.
          { eapply lookup_fn_unique_by_name;
              [ exact Hlookup_inner | exact Hin_nested | exact Hname_nested
              | exact Hunique ]. }
          assert (Hready_inner :
            preservation_ready_expr
              (subst_type_params_expr type_args_nested (fn_body fcall_inner))).
          { destruct (alpha_rename_fn_def_params_body
              (store_names s_inner_hidden) fcallee_nested fcall_inner used_inner
              Hrename_inner) as (rho_inner & used_inner_params & _ & Hbody_inner).
            eapply alpha_rename_preservation_ready_expr.
            - eapply alpha_rename_expr_subst_type_params_expr.
              exact Hbody_inner.
            - exact Hready_nested. }
          assert (Hbody_inner_not_free :
            ~ In x_local (free_vars_expr
              (subst_type_params_expr type_args_nested (fn_body fcall_inner)))).
          { eapply callee_body_root_shadow_store_safe_narrow_summary_alpha_renamed_ready_body_free_vars_hidden_seed_excludes.
            - exact Hsummary_nested_body.
            - exact Hcaps_runtime.
            - exact Hrename_inner.
            - exact Hrel_inner_args.
            - exact Hready_inner. }
          destruct (eval_generic_direct_call_hidden_frame_expr_body_strip
            body_env x_local T (VClosure (fn_name fcallee) [])
            (bind_params ps_outer vs_outer s_args_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            s_body_hidden fname_nested type_args_nested args_runtime v
            fcallee_nested fcall_inner used_inner s_inner_hidden s_inner_base
            vs_inner s_inner_body_hidden Hrel_bind_outer
            (store_safe_function_value_call_args_preservation_ready body_env
              args_runtime Hsafe_runtime)
            Hnot_free_runtime Hnot_local_runtime Hrefs_bind_outer
            Heval_nested_hidden Hlookup_inner Hcaps_inner Hrel_inner_args
            Heval_inner_base Hrefs_inner_base Hvs_inner_refs Hrename_inner
            Heval_inner_body_hidden Hfinal_inner_hidden Hready_inner
            Hbody_inner_not_free)
            as (s_inner_body_base & s_inner_final_base & Hrel_inner_body &
                Heval_inner_body_base & Hrefs_inner_body & Hv_inner_refs &
                Hinner_final_eq & Hrel_inner_final & Hremove_inner).
          pose (inner_env := global_env_with_local_bounds body_env
            (subst_type_params_trait_bounds [] (fn_bounds fcallee))).
          assert (Hunique_inner_env : fn_env_unique_by_name inner_env).
          { subst inner_env. unfold fn_env_unique_by_name in *. simpl.
            exact Hunique_body_env. }
          assert (Hsummary_nested_inner_env :
            callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
              inner_env 10000 fcallee_nested type_args_nested).
          { subst inner_env.
            eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
            - exact Hunique_body_env.
            - exact Hsummary_nested_body. }
          assert (Hsummary_inner_inst :
            callee_body_root_shadow_store_safe_narrow_summary_instantiated
              inner_env fcallee_nested type_args_nested).
          { eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_ready.
            - exact Hsummary_nested_inner_env.
            - exact Hready_nested. }
          assert (Hsafe_runtime_inner :
            store_safe_function_value_call_args inner_env args_runtime).
          { subst inner_env.
            eapply store_safe_function_value_call_args_global_env_with_local_bounds.
            exact Hsafe_runtime. }
          assert (Hstore_bind_prefix_inner :
            store_typed_prefix inner_env
              (bind_params ps_outer vs_outer s_args_base)
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))).
          { subst inner_env.
            eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
            exact Hstore_bind_prefix. }
          assert (Heval_inner_base_inner :
            eval_args inner_env (bind_params ps_outer vs_outer s_args_base)
              args_runtime s_inner_base vs_inner).
          { subst inner_env.
            eapply eval_args_global_env_with_local_bounds.
            exact Heval_inner_base. }
          assert (Heval_inner_body_base_inner :
            eval inner_env
              (bind_params (apply_type_params type_args_nested
                 (fn_params fcall_inner)) vs_inner s_inner_base)
              (subst_type_params_expr type_args_nested (fn_body fcall_inner))
              s_inner_body_base v).
          { subst inner_env.
            eapply direct_call_eval_global_env_with_local_bounds.
            exact Heval_inner_body_base. }
          assert (Hsummary_bind_inner :
            store_function_closure_targets_summary inner_env
              (bind_params ps_outer vs_outer s_args_base)).
          { subst inner_env.
            apply store_function_closure_targets_summary_global_env_with_local_bounds.
            exact Hsummary_bind_base. }
          assert (Hsummary_inner_args_body :
            store_function_closure_targets_summary body_env s_inner_base).
          { eapply store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary;
              eassumption. }
          assert (Htyped_runtime_base :
            typed_args_roots inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local
                (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              args_runtime
              (apply_lt_params sigma_nested
                (apply_type_params type_args_nested (fn_params fcallee_nested)))
              Sigma_nested (root_env_remove x_local R_nested_runtime)
              nested_arg_roots).
          { eapply store_safe_function_value_call_args_typed_roots_remove_unused_key;
              eassumption. }
          destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
            inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
            args_runtime
            (apply_lt_params sigma_nested
              (apply_type_params type_args_nested
                (fn_params fcallee_nested)))
            Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots
            (bind_params ps_outer vs_outer s_args_base) s_inner_base vs_inner
            Hsafe_runtime_inner Htyped_runtime_base Heval_inner_base_inner
            Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
            Hshadow_bind_outer_base
            (root_env_no_shadow_remove _ _ Hrn_bind_outer)
            Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
            Hsummary_bind_inner)
            as (Hstore_inner_args & Hargs_values_inner_sigma &
                Hpres_inner_args & Hroots_inner_args &
                Harg_roots_inner_values & Hshadow_inner_args &
                Hrn_inner_args & Hnamed_inner_args & Hkeys_inner_args &
                Hsummary_inner_args_store).
          pose proof (typed_args_roots_params_of_tys_map_param_ty
            inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
            args_runtime
            (apply_lt_params sigma_nested
              (apply_type_params type_args_nested (fn_params fcallee_nested)))
            Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots Htyped_runtime_base)
            as Htyped_inner_param_tys.
          pose proof (runtime_tfn_signature_bridge_apply_lt_params
            sigma_nested
            (apply_type_params type_args_nested (fn_params fcallee_nested))
            (subst_type_params_ty type_args_nested (fn_ret fcallee_nested)))
            as Hbridge_inner.
          assert (Hprov_runtime : provenance_ready_args args_runtime).
          { apply preservation_ready_args_implies_provenance_ready_closure.
            eapply store_safe_function_value_call_args_preservation_ready.
            exact Hsafe_runtime_inner. }
          assert (Hinner_seed_names :
            forall y, In y (store_names s_inner_base) ->
              In y (store_names s_inner_hidden)).
          { intros y Hy.
            eapply store_hidden_frame_rel_store_names_base_subset;
              eassumption. }
          destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed
            inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
            Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots args_runtime
            type_args_nested fcallee_nested fcall_inner
            (map param_ty
              (apply_lt_params sigma_nested
                (apply_type_params type_args_nested
                  (fn_params fcallee_nested))))
            (apply_lt_ty sigma_nested
              (subst_type_params_ty type_args_nested (fn_ret fcallee_nested)))
            (bind_params ps_outer vs_outer s_args_base) s_inner_base vs_inner
            used_inner (store_names s_inner_hidden) Hsummary_inner_inst Hcaps_runtime Hbridge_inner
            Hsafe_runtime_inner Htyped_inner_param_tys Heval_inner_base_inner
            Hprov_runtime Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
            Hshadow_bind_outer_base (root_env_no_shadow_remove _ _ Hrn_bind_outer)
            Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
            Hinner_seed_names Hrename_inner)
            as (T_inner_body & Sigma_inner_out & R_inner_body &
                roots_inner_body & ret_roots_inner & Hsummary_inner_body &
                Hcompat_inner_body & Hexcl_inner_roots & Hexcl_inner_env &
                Hinner_roots_subset).
          destruct (generic_direct_call_args_bind_type_params_runtime_package_seed
            inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
            args_runtime type_args_nested sigma_nested fcallee_nested
            fcall_inner used_inner (store_names s_inner_hidden)
            (bind_params ps_outer vs_outer s_args_base)
            s_inner_base vs_inner Sigma_nested (root_env_remove x_local R_nested_runtime)
            nested_arg_roots Hsafe_runtime_inner Heval_inner_base_inner
            Htyped_runtime_base Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
            Hshadow_bind_outer_base (root_env_no_shadow_remove _ _ Hrn_bind_outer)
            Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
            Hunique_inner_env Hsummary_bind_inner Hinner_seed_names Hrename_inner)
            as (Hstore_inner_bind & Hroots_inner_bind &
                Hshadow_inner_bind & Hrn_inner_bind & Hcover_inner_bind &
                Hnamed_inner_bind & Hkeys_inner_bind & Hsummary_inner_bind &
                Hframe_inner_start).
          pose (ps_inner := apply_type_params type_args_nested
            (fn_params fcall_inner)).
          fold ps_inner in Hstore_inner_bind, Hroots_inner_bind,
            Hshadow_inner_bind, Hrn_inner_bind, Hcover_inner_bind,
            Hnamed_inner_bind, Hkeys_inner_bind, Hsummary_inner_bind,
            Hframe_inner_start.
          pose (inner_body_env := global_env_with_local_bounds inner_env
            (subst_type_params_trait_bounds type_args_nested (fn_bounds fcall_inner))).
          assert (Hunique_inner_body_env : fn_env_unique_by_name inner_body_env).
          { subst inner_body_env. unfold fn_env_unique_by_name in *. simpl.
            exact Hunique_inner_env. }
          assert (Hstore_inner_bind_body_env :
            store_typed_prefix inner_body_env
              (bind_params ps_inner vs_inner s_inner_base)
              (sctx_of_ctx (params_ctx ps_inner))).
          { subst inner_body_env.
            eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
            exact Hstore_inner_bind. }
          assert (Heval_inner_body_base_body_env :
            eval inner_body_env
              (bind_params ps_inner vs_inner s_inner_base)
              (subst_type_params_expr type_args_nested (fn_body fcall_inner))
              s_inner_body_base v).
          { subst inner_body_env.
            eapply direct_call_eval_global_env_with_local_bounds.
            exact Heval_inner_body_base_inner. }
          assert (Hsummary_inner_bind_body_env :
            store_function_closure_targets_summary inner_body_env
              (bind_params ps_inner vs_inner s_inner_base)).
          { subst inner_body_env.
            apply store_function_closure_targets_summary_global_env_with_local_bounds.
            exact Hsummary_inner_bind. }
          destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
            inner_body_env (fn_outlives fcall_inner) (fn_lifetimes fcall_inner)
            (call_param_root_env ps_inner nested_arg_roots
              (root_env_remove x_local R_nested_runtime))
            (sctx_of_ctx (params_ctx ps_inner))
            (subst_type_params_expr type_args_nested (fn_body fcall_inner))
            T_inner_body Sigma_inner_out R_inner_body roots_inner_body
            ret_roots_inner Hsummary_inner_body
            (bind_params ps_inner vs_inner s_inner_base) s_inner_body_base v
            Hstore_inner_bind_body_env Hroots_inner_bind Hshadow_inner_bind
            Hrn_inner_bind Hnamed_inner_bind Hkeys_inner_bind
            Hsummary_inner_bind_body_env Heval_inner_body_base_body_env
            Hunique_inner_body_env)
            as [Hstore_inner_body [Hv_inner_body [Hpres_inner_body
              [Hroots_inner_body [Hret_roots_inner [Hrootset_inner_body
                [Hshadow_inner_body [Hrn_inner_body [Hnamed_inner_body
                  [Hkeys_inner_body Hsummary_inner_body_store]]]]]]]]]].
          pose proof (alpha_rename_fn_def_shape (store_names s_inner_hidden)
                fcallee_nested fcall_inner used_inner Hrename_inner)
            as Hshape_inner.
          destruct Hshape_inner as [_ [Hret_alpha_inner Hparams_alpha_inner]].
          assert (Hargs_values_inner_type :
            eval_args_values_have_types inner_env (fn_outlives fcallee)
              s_inner_base vs_inner
              (apply_type_params type_args_nested
                (fn_params fcallee_nested))).
          { eapply eval_args_values_have_types_apply_lt_params_inv.
            exact Hargs_values_inner_sigma. }
          assert (Hargs_values_fcall_inner_type :
            eval_args_values_have_types inner_env (fn_outlives fcallee)
              s_inner_base vs_inner ps_inner).
          { subst ps_inner.
            eapply eval_args_values_have_types_params_alpha.
            - apply params_alpha_apply_type_compat. exact Hparams_alpha_inner.
            - exact Hargs_values_inner_type. }
          assert (Hfresh_inner : params_fresh_in_store ps_inner s_inner_base).
          { subst ps_inner.
            eapply store_hidden_frame_rel_params_fresh_in_store_base.
            - exact Hrel_inner_args.
            - unfold params_fresh_in_store.
              rewrite params_ctx_apply_type_params.
              rewrite ctx_names_subst_type_params_ctx.
              eapply alpha_rename_fn_def_params_fresh_in_store.
              exact Hrename_inner. }
          assert (Hframe_scope_inner_start :
            store_frame_scope ps_inner (sctx_of_ctx (params_ctx ps_inner))
              (bind_params ps_inner vs_inner s_inner_base) s_inner_base).
          { eapply store_frame_scope_bind_params.
            exact Hargs_values_fcall_inner_type. }
          assert (Hframe_fresh_inner_start :
            store_frame_static_fresh (sctx_of_ctx (params_ctx ps_inner))
              s_inner_base).
          { eapply params_fresh_in_store_frame_static_fresh.
            exact Hfresh_inner. }
          destruct (expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named
            inner_body_env (fn_outlives fcall_inner) (fn_lifetimes fcall_inner)
            (call_param_root_env ps_inner nested_arg_roots
              (root_env_remove x_local R_nested_runtime))
            (sctx_of_ctx (params_ctx ps_inner))
            (subst_type_params_expr type_args_nested (fn_body fcall_inner))
            T_inner_body Sigma_inner_out R_inner_body roots_inner_body
            ret_roots_inner Hsummary_inner_body
            (bind_params ps_inner vs_inner s_inner_base) s_inner_body_base v
            ps_inner s_inner_base Hstore_inner_bind_body_env Hroots_inner_bind
            Hshadow_inner_bind Hrn_inner_bind Hnamed_inner_bind
            Hkeys_inner_bind Hsummary_inner_bind_body_env
            Heval_inner_body_base_body_env Hunique_inner_body_env
            Hcover_inner_bind Hframe_scope_inner_start
            Hframe_fresh_inner_start)
            as [_ [_ [_ [_ [Hframe_inner_body _]]]]].
          assert (Hsame_inner :
            sctx_same_bindings (sctx_of_ctx (params_ctx ps_inner))
              Sigma_inner_out).
          { eapply typed_env_structural_same_bindings.
            eapply typed_env_roots_structural.
            eapply typed_env_roots_shadow_safe_roots.
            eapply expr_root_shadow_store_safe_narrow_summary_typed.
            exact Hsummary_inner_body. }
          assert (Hscope_inner_body :
            store_param_scope ps_inner s_inner_body_base s_inner_base).
          { eapply store_frame_scope_param_scope. exact Hframe_inner_body. }
          assert (Hremoved_inner_exact : s_inner_final_base = s_inner_base).
          { rewrite Hinner_final_eq.
            eapply store_remove_params_store_frame_scope_exact.
            - exact Hsame_inner.
            - exact Hscope_inner_body.
            - exact Hframe_inner_body. }
          assert (Hv_inner_ret :
            value_has_type inner_env s_inner_body_base v
              (subst_type_params_ty type_args_nested (fn_ret fcallee_nested))).
          { rewrite Hret_alpha_inner.
            eapply value_has_type_compatible.
            - eapply direct_call_value_has_type_clear_global_env_local_bounds.
              exact Hv_inner_body.
            - apply ty_compatible_b_sound with (Ω := fn_outlives fcall_inner).
              exact Hcompat_inner_body. }
          assert (Hv_inner_final :
            value_has_type inner_env s_inner_final_base v
              (apply_lt_ty sigma_nested
                (subst_type_params_ty type_args_nested
                  (fn_ret fcallee_nested)))).
          { rewrite Hinner_final_eq.
            apply value_has_type_apply_lt_ty.
            eapply value_has_type_store_remove_params_excluding.
            - exact Hv_inner_ret.
            - eapply value_roots_exclude_params.
              + exact Hret_roots_inner.
              + exact Hexcl_inner_roots. }
          rewrite Hremove_inner.
          rewrite Hremoved_inner_exact.
          constructor.
          + eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
            exact Hstore_inner_args.
          + rewrite <- Hremoved_inner_exact.
            eapply direct_call_value_has_type_clear_global_env_local_bounds.
            exact Hv_inner_final.
          + eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
            exact Hpres_inner_args.
          + exact Hroots_inner_args.
          + eapply direct_call_value_roots_within_store_subset.
            * rewrite <- Hremoved_inner_exact.
              exact Hret_roots_inner.
            * exact Hinner_roots_subset.
          + exact Hshadow_inner_args.
          + exact Hrn_inner_args.
          + exact Hnamed_inner_args.
          + exact Hkeys_inner_args.
          + exact Hsummary_inner_args_body.
          - destruct (eval_generic_direct_call_hidden_frame_args_strip
              body_env x_local T (VClosure (fn_name fcallee) [])
              (bind_params ps_outer vs_outer s_args_hidden)
              (bind_params ps_outer vs_outer s_args_base)
              s_body_hidden fname_nested type_args_nested args_runtime v
              Hrel_bind_outer
              (store_safe_function_value_call_args_preservation_ready body_env
                args_runtime Hsafe_runtime)
              Hnot_free_runtime Hnot_local_runtime Hrefs_bind_outer
              Heval_nested_hidden)
              as (fdef_inner & fcall_inner & used_inner & s_inner_hidden &
                  s_inner_base & vs_inner & s_inner_body_hidden &
                  Hlookup_inner & Hcaps_inner & Hrel_inner_args &
                  Heval_inner_hidden & Heval_inner_base & Hrefs_inner_base &
                  Hvs_inner_refs & Hrename_inner & Heval_inner_body_hidden &
                  Hfinal_inner_hidden).
            assert (fdef_inner = fcallee_nested) as ->.
            { eapply lookup_fn_unique_by_name;
                [ exact Hlookup_inner | exact Hin_nested | exact Hname_nested
                | exact Hunique ]. }
            assert (Hready_inner :
              preservation_ready_expr
                (subst_type_params_expr type_args_nested (fn_body fcall_inner))).
            { destruct (alpha_rename_fn_def_params_body
                (store_names s_inner_hidden) fcallee_nested fcall_inner used_inner
                Hrename_inner) as (rho_inner & used_inner_params & _ & Hbody_inner).
              eapply alpha_rename_preservation_ready_expr.
              + eapply alpha_rename_expr_subst_type_params_expr.
                exact Hbody_inner.
              + exact Hready_nested. }
            assert (Hbody_inner_not_free :
              ~ In x_local (free_vars_expr
                (subst_type_params_expr type_args_nested (fn_body fcall_inner)))).
            { eapply callee_body_root_shadow_store_safe_narrow_summary_alpha_renamed_ready_body_free_vars_hidden_seed_excludes.
              + exact Hsummary_nested_body.
              + exact Hcaps_runtime.
              + exact Hrename_inner.
              + exact Hrel_inner_args.
              + exact Hready_inner. }
            destruct (eval_generic_direct_call_hidden_frame_expr_body_strip
              body_env x_local T (VClosure (fn_name fcallee) [])
              (bind_params ps_outer vs_outer s_args_hidden)
              (bind_params ps_outer vs_outer s_args_base)
              s_body_hidden fname_nested type_args_nested args_runtime v
              fcallee_nested fcall_inner used_inner s_inner_hidden s_inner_base
              vs_inner s_inner_body_hidden Hrel_bind_outer
              (store_safe_function_value_call_args_preservation_ready body_env
                args_runtime Hsafe_runtime)
              Hnot_free_runtime Hnot_local_runtime Hrefs_bind_outer
              Heval_nested_hidden Hlookup_inner Hcaps_inner Hrel_inner_args
              Heval_inner_base Hrefs_inner_base Hvs_inner_refs Hrename_inner
              Heval_inner_body_hidden Hfinal_inner_hidden Hready_inner
              Hbody_inner_not_free)
              as (s_inner_body_base & s_inner_final_base & Hrel_inner_body &
                  Heval_inner_body_base & Hrefs_inner_body & Hv_inner_refs &
                  Hinner_final_eq & Hrel_inner_final & Hremove_inner).
            pose (inner_env := global_env_with_local_bounds body_env
              (subst_type_params_trait_bounds [] (fn_bounds fcallee))).
            assert (Hunique_inner_env : fn_env_unique_by_name inner_env).
            { subst inner_env. unfold fn_env_unique_by_name in *. simpl.
              exact Hunique_body_env. }
            assert (Hsummary_nested_inner_env :
              callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
                inner_env 10000 fcallee_nested type_args_nested).
            { subst inner_env.
              eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel_global_env_with_local_bounds.
              - exact Hunique_body_env.
              - exact Hsummary_nested_body. }
            assert (Hsummary_inner_inst :
              callee_body_root_shadow_store_safe_narrow_summary_instantiated
                inner_env fcallee_nested type_args_nested).
            { eapply callee_body_root_shadow_store_safe_narrow_summary_instantiated_of_fuel_ready.
              - exact Hsummary_nested_inner_env.
              - exact Hready_nested. }
            assert (Hsafe_runtime_inner :
              store_safe_function_value_call_args inner_env args_runtime).
            { subst inner_env.
              eapply store_safe_function_value_call_args_global_env_with_local_bounds.
              exact Hsafe_runtime. }
            assert (Hstore_bind_prefix_inner :
              store_typed_prefix inner_env
                (bind_params ps_outer vs_outer s_args_base)
                (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))).
            { subst inner_env.
              eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
              exact Hstore_bind_prefix. }
            assert (Heval_inner_base_inner :
              eval_args inner_env (bind_params ps_outer vs_outer s_args_base)
                args_runtime s_inner_base vs_inner).
            { subst inner_env.
              eapply eval_args_global_env_with_local_bounds.
              exact Heval_inner_base. }
            assert (Heval_inner_body_base_inner :
              eval inner_env
                (bind_params (apply_type_params type_args_nested
                   (fn_params fcall_inner)) vs_inner s_inner_base)
                (subst_type_params_expr type_args_nested (fn_body fcall_inner))
                s_inner_body_base v).
            { subst inner_env.
              eapply direct_call_eval_global_env_with_local_bounds.
              exact Heval_inner_body_base. }
            assert (Hsummary_bind_inner :
              store_function_closure_targets_summary inner_env
                (bind_params ps_outer vs_outer s_args_base)).
            { subst inner_env.
              apply store_function_closure_targets_summary_global_env_with_local_bounds.
              exact Hsummary_bind_base. }
            assert (Hsummary_inner_args_body :
              store_function_closure_targets_summary body_env s_inner_base).
            { eapply store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary;
                eassumption. }
            assert (Htyped_runtime_base :
              typed_args_roots inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
                (root_env_remove x_local
                  (call_param_root_env ps_outer arg_roots R'))
                (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
                args_runtime
                (apply_lt_params sigma_nested
                  (apply_type_params type_args_nested (fn_params fcallee_nested)))
                Sigma_nested (root_env_remove x_local R_nested_runtime)
                nested_arg_roots).
            { eapply store_safe_function_value_call_args_typed_roots_remove_unused_key;
                eassumption. }
            destruct (store_safe_function_value_call_args_eval_runtime_package_prefix_named
              inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              args_runtime
              (apply_lt_params sigma_nested
                (apply_type_params type_args_nested
                  (fn_params fcallee_nested)))
              Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots
              (bind_params ps_outer vs_outer s_args_base) s_inner_base vs_inner
              Hsafe_runtime_inner Htyped_runtime_base Heval_inner_base_inner
              Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
              Hshadow_bind_outer_base
              (root_env_no_shadow_remove _ _ Hrn_bind_outer)
              Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
              Hsummary_bind_inner)
              as (Hstore_inner_args & Hargs_values_inner_sigma &
                  Hpres_inner_args & Hroots_inner_args &
                  Harg_roots_inner_values & Hshadow_inner_args &
                  Hrn_inner_args & Hnamed_inner_args & Hkeys_inner_args &
                  Hsummary_inner_args_store).
            pose proof (typed_args_roots_params_of_tys_map_param_ty
              inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              args_runtime
              (apply_lt_params sigma_nested
                (apply_type_params type_args_nested (fn_params fcallee_nested)))
              Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots Htyped_runtime_base)
              as Htyped_inner_param_tys.
            pose proof (runtime_tfn_signature_bridge_apply_lt_params
              sigma_nested
              (apply_type_params type_args_nested (fn_params fcallee_nested))
              (subst_type_params_ty type_args_nested (fn_ret fcallee_nested)))
              as Hbridge_inner.
            assert (Hprov_runtime : provenance_ready_args args_runtime).
            { apply preservation_ready_args_implies_provenance_ready_closure.
              eapply store_safe_function_value_call_args_preservation_ready.
              exact Hsafe_runtime_inner. }
            assert (Hinner_seed_names :
              forall y, In y (store_names s_inner_base) ->
                In y (store_names s_inner_hidden)).
            { intros y Hy.
              eapply store_hidden_frame_rel_store_names_base_subset;
                eassumption. }
            destruct (generic_direct_call_callee_body_root_shadow_store_safe_narrow_summary_bridge_of_summary_tfn_with_result_subset_prefix_named_seed
              inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              Sigma_nested (root_env_remove x_local R_nested_runtime) nested_arg_roots args_runtime
              type_args_nested fcallee_nested fcall_inner
              (map param_ty
                (apply_lt_params sigma_nested
                  (apply_type_params type_args_nested
                    (fn_params fcallee_nested))))
              (apply_lt_ty sigma_nested
                (subst_type_params_ty type_args_nested (fn_ret fcallee_nested)))
              (bind_params ps_outer vs_outer s_args_base) s_inner_base vs_inner
              used_inner (store_names s_inner_hidden) Hsummary_inner_inst Hcaps_runtime Hbridge_inner
              Hsafe_runtime_inner Htyped_inner_param_tys Heval_inner_base_inner
              Hprov_runtime Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
              Hshadow_bind_outer_base (root_env_no_shadow_remove _ _ Hrn_bind_outer)
              Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
              Hinner_seed_names Hrename_inner)
              as (T_inner_body & Sigma_inner_out & R_inner_body &
                  roots_inner_body & ret_roots_inner & Hsummary_inner_body &
                  Hcompat_inner_body & Hexcl_inner_roots & Hexcl_inner_env &
                  Hinner_roots_subset).
            destruct (generic_direct_call_args_bind_type_params_runtime_package_seed
              inner_env (fn_outlives fcallee) (fn_lifetimes fcallee)
              (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
              (sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)))
              args_runtime type_args_nested sigma_nested fcallee_nested
              fcall_inner used_inner (store_names s_inner_hidden)
              (bind_params ps_outer vs_outer s_args_base)
              s_inner_base vs_inner Sigma_nested (root_env_remove x_local R_nested_runtime)
              nested_arg_roots Hsafe_runtime_inner Heval_inner_base_inner
              Htyped_runtime_base Hstore_bind_prefix_inner Hroots_bind_outer_base_removed
              Hshadow_bind_outer_base (root_env_no_shadow_remove _ _ Hrn_bind_outer)
              Hnamed_bind_outer_base_removed Hkeys_bind_outer_base_removed
              Hunique_inner_env Hsummary_bind_inner Hinner_seed_names Hrename_inner)
              as (Hstore_inner_bind & Hroots_inner_bind &
                  Hshadow_inner_bind & Hrn_inner_bind & Hcover_inner_bind &
                  Hnamed_inner_bind & Hkeys_inner_bind & Hsummary_inner_bind &
                  Hframe_inner_start).
            pose (ps_inner := apply_type_params type_args_nested
              (fn_params fcall_inner)).
            fold ps_inner in Hstore_inner_bind, Hroots_inner_bind,
              Hshadow_inner_bind, Hrn_inner_bind, Hcover_inner_bind,
              Hnamed_inner_bind, Hkeys_inner_bind, Hsummary_inner_bind,
              Hframe_inner_start.
            pose (inner_body_env := global_env_with_local_bounds inner_env
              (subst_type_params_trait_bounds type_args_nested (fn_bounds fcall_inner))).
            assert (Hunique_inner_body_env : fn_env_unique_by_name inner_body_env).
            { subst inner_body_env. unfold fn_env_unique_by_name in *. simpl.
              exact Hunique_inner_env. }
            assert (Hstore_inner_bind_body_env :
              store_typed_prefix inner_body_env
                (bind_params ps_inner vs_inner s_inner_base)
                (sctx_of_ctx (params_ctx ps_inner))).
            { subst inner_body_env.
              eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
              exact Hstore_inner_bind. }
            assert (Heval_inner_body_base_body_env :
              eval inner_body_env
                (bind_params ps_inner vs_inner s_inner_base)
                (subst_type_params_expr type_args_nested (fn_body fcall_inner))
                s_inner_body_base v).
            { subst inner_body_env.
              eapply direct_call_eval_global_env_with_local_bounds.
              exact Heval_inner_body_base_inner. }
            assert (Hsummary_inner_bind_body_env :
              store_function_closure_targets_summary inner_body_env
                (bind_params ps_inner vs_inner s_inner_base)).
            { subst inner_body_env.
              apply store_function_closure_targets_summary_global_env_with_local_bounds.
              exact Hsummary_inner_bind. }
            destruct (expr_root_shadow_store_safe_narrow_summary_runtime_package_prefix_named
              inner_body_env (fn_outlives fcall_inner) (fn_lifetimes fcall_inner)
              (call_param_root_env ps_inner nested_arg_roots
                (root_env_remove x_local R_nested_runtime))
              (sctx_of_ctx (params_ctx ps_inner))
              (subst_type_params_expr type_args_nested (fn_body fcall_inner))
              T_inner_body Sigma_inner_out R_inner_body roots_inner_body
              ret_roots_inner Hsummary_inner_body
              (bind_params ps_inner vs_inner s_inner_base) s_inner_body_base v
              Hstore_inner_bind_body_env Hroots_inner_bind Hshadow_inner_bind
              Hrn_inner_bind Hnamed_inner_bind Hkeys_inner_bind
              Hsummary_inner_bind_body_env Heval_inner_body_base_body_env
              Hunique_inner_body_env)
              as [Hstore_inner_body [Hv_inner_body [Hpres_inner_body
                [Hroots_inner_body [Hret_roots_inner [Hrootset_inner_body
                  [Hshadow_inner_body [Hrn_inner_body [Hnamed_inner_body
                    [Hkeys_inner_body Hsummary_inner_body_store]]]]]]]]]].
            pose proof (alpha_rename_fn_def_shape (store_names s_inner_hidden)
                  fcallee_nested fcall_inner used_inner Hrename_inner)
              as Hshape_inner.
            destruct Hshape_inner as [_ [Hret_alpha_inner Hparams_alpha_inner]].
            assert (Hargs_values_inner_type :
              eval_args_values_have_types inner_env (fn_outlives fcallee)
                s_inner_base vs_inner
                (apply_type_params type_args_nested
                  (fn_params fcallee_nested))).
            { eapply eval_args_values_have_types_apply_lt_params_inv.
              exact Hargs_values_inner_sigma. }
            assert (Hargs_values_fcall_inner_type :
              eval_args_values_have_types inner_env (fn_outlives fcallee)
                s_inner_base vs_inner ps_inner).
            { subst ps_inner.
              eapply eval_args_values_have_types_params_alpha.
              - apply params_alpha_apply_type_compat. exact Hparams_alpha_inner.
              - exact Hargs_values_inner_type. }
            assert (Hfresh_inner : params_fresh_in_store ps_inner s_inner_base).
            { subst ps_inner.
              eapply store_hidden_frame_rel_params_fresh_in_store_base.
              - exact Hrel_inner_args.
              - unfold params_fresh_in_store.
                rewrite params_ctx_apply_type_params.
                rewrite ctx_names_subst_type_params_ctx.
                eapply alpha_rename_fn_def_params_fresh_in_store.
                exact Hrename_inner. }
            assert (Hframe_scope_inner_start :
              store_frame_scope ps_inner (sctx_of_ctx (params_ctx ps_inner))
                (bind_params ps_inner vs_inner s_inner_base) s_inner_base).
            { eapply store_frame_scope_bind_params.
              exact Hargs_values_fcall_inner_type. }
            assert (Hframe_fresh_inner_start :
              store_frame_static_fresh (sctx_of_ctx (params_ctx ps_inner))
                s_inner_base).
            { eapply params_fresh_in_store_frame_static_fresh.
              exact Hfresh_inner. }
            destruct (expr_root_shadow_store_safe_narrow_summary_preserves_frame_scope_prefix_named
              inner_body_env (fn_outlives fcall_inner) (fn_lifetimes fcall_inner)
              (call_param_root_env ps_inner nested_arg_roots
                (root_env_remove x_local R_nested_runtime))
              (sctx_of_ctx (params_ctx ps_inner))
              (subst_type_params_expr type_args_nested (fn_body fcall_inner))
              T_inner_body Sigma_inner_out R_inner_body roots_inner_body
              ret_roots_inner Hsummary_inner_body
              (bind_params ps_inner vs_inner s_inner_base) s_inner_body_base v
              ps_inner s_inner_base Hstore_inner_bind_body_env Hroots_inner_bind
              Hshadow_inner_bind Hrn_inner_bind Hnamed_inner_bind
              Hkeys_inner_bind Hsummary_inner_bind_body_env
              Heval_inner_body_base_body_env Hunique_inner_body_env
              Hcover_inner_bind Hframe_scope_inner_start
              Hframe_fresh_inner_start)
              as [_ [_ [_ [_ [Hframe_inner_body _]]]]].
            assert (Hsame_inner :
              sctx_same_bindings (sctx_of_ctx (params_ctx ps_inner))
                Sigma_inner_out).
            { eapply typed_env_structural_same_bindings.
              eapply typed_env_roots_structural.
              eapply typed_env_roots_shadow_safe_roots.
              eapply expr_root_shadow_store_safe_narrow_summary_typed.
              exact Hsummary_inner_body. }
            assert (Hscope_inner_body :
              store_param_scope ps_inner s_inner_body_base s_inner_base).
            { eapply store_frame_scope_param_scope. exact Hframe_inner_body. }
            assert (Hremoved_inner_exact : s_inner_final_base = s_inner_base).
            { rewrite Hinner_final_eq.
              eapply store_remove_params_store_frame_scope_exact.
              - exact Hsame_inner.
              - exact Hscope_inner_body.
              - exact Hframe_inner_body. }
            exists vs_inner, s_inner_base.
            repeat split.
            + exact Heval_inner_base_inner.
            + exact Htyped_runtime_base.
            + exact Hprov_runtime.
            + rewrite Hremove_inner.
              exact Hremoved_inner_exact.
            + rewrite Hremove_inner.
              exact Hrel_inner_final. }
        destruct Hnested_bundle as
          [Hpkg_nested_body
            (vs_inner & s_inner_base_outer & Heval_inner_base_outer &
             Htyped_runtime_base & Hprov_runtime & Hremove_inner_outer &
             Hrel_inner_final_outer)].
        assert (Hbody_ctx_outer_params :
          sctx_of_ctx (subst_type_params_ctx [] (fn_body_ctx fcall_outer)) =
          sctx_of_ctx (params_ctx ps_outer)).
        { subst ps_outer.
          rewrite subst_type_params_ctx_nil.
          rewrite (fn_body_ctx_eq_params_ctx_when_no_captures fcall_outer).
          - rewrite apply_type_params_nil. reflexivity.
          - rewrite <- Hcaps_outer.
            eapply alpha_rename_fn_def_captures. exact Hrename_outer. }
        assert (Htyped_runtime_base_params :
          typed_args_roots
            (global_env_with_local_bounds body_env
              (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
            (fn_outlives fcallee) (fn_lifetimes fcallee)
            (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
            (sctx_of_ctx (params_ctx ps_outer)) args_runtime
            (apply_lt_params sigma_nested
              (apply_type_params type_args_nested (fn_params fcallee_nested)))
            Sigma_nested (root_env_remove x_local R_nested_runtime)
            nested_arg_roots).
        { rewrite <- Hbody_ctx_outer_params. exact Htyped_runtime_base. }
        destruct (proj1 (proj2 eval_preserves_frame_scope_roots_ready_mutual)
          (global_env_with_local_bounds body_env
            (subst_type_params_trait_bounds [] (fn_bounds fcallee)))
          (bind_params ps_outer vs_outer s_args_base) args_runtime
          s_inner_base_outer vs_inner Heval_inner_base_outer
          (fn_outlives fcallee) (fn_lifetimes fcallee)
          (root_env_remove x_local (call_param_root_env ps_outer arg_roots R'))
          (sctx_of_ctx (params_ctx ps_outer))
          (apply_lt_params sigma_nested
            (apply_type_params type_args_nested (fn_params fcallee_nested)))
          Sigma_nested (root_env_remove x_local R_nested_runtime)
          nested_arg_roots ps_outer s_args_base Hprov_runtime Htyped_runtime_base_params
          Hcover_outer_removed Hroots_bind_outer_base_removed
          Hshadow_bind_outer_base (root_env_no_shadow_remove _ _ Hrn_bind_outer)
          Hframe_scope_outer_start Hframe_fresh_outer_start)
          as [_ [_ [_ [_ [Hframe_scope_outer_body _]]]]].
        assert (Hsame_outer :
          sctx_same_bindings (sctx_of_ctx (params_ctx ps_outer)) Sigma_nested).
        { eapply typed_args_env_structural_same_bindings.
          eapply typed_args_roots_structural. exact Htyped_runtime_base_params. }
        assert (Hscope_outer_body :
          store_param_scope ps_outer s_inner_base_outer s_args_base).
        { eapply store_frame_scope_param_scope. exact Hframe_scope_outer_body. }
        assert (Houter_removed_exact : store_remove x_local s2 = s_args_base).
        { rewrite Hfinal_hidden.
          change (store_remove x_local (store_remove_params ps_outer s_body_hidden) =
            s_args_base).
          rewrite (store_remove_params_store_remove_commute ps_outer x_local
            s_body_hidden Hnotin_outer_params).
          rewrite Hremove_inner_outer.
          eapply store_remove_params_store_frame_scope_exact.
          - exact Hsame_outer.
          - exact Hscope_outer_body.
          - exact Hframe_scope_outer_body. }
        assert (Hstore_args_clean :
          store_typed_prefix body_env s_args_base (sctx_remove x_local Σ')).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          eapply store_typed_prefix_remove_excluding_root.
          - exact Hstore_args_hidden.
          - rewrite (store_hidden_frame_rel_remove_base x_local T
              (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
              Hrel_args_outer).
            exact Hrefs_args_base. }
        assert (Hpres_add_args_hidden :
          store_ref_targets_preserved body_env s1 s_args_hidden).
        { eapply store_ref_targets_preserved_trans.
          - exact Hadd_pres.
          - exact Hpres_args_hidden. }
        assert (Hpres_args_clean :
          store_ref_targets_preserved body_env s1 s_args_base).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          eapply store_ref_targets_preserved_remove_after_absent_root;
            eassumption. }
        assert (Hbase_no_x : forall se, In se s_args_base -> se_name se <> x_local).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          apply store_no_shadow_remove_no_name. exact Hshadow_args_hidden. }
        assert (Hroots_args_base : store_roots_within R' s_args_base).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          apply store_remove_roots_within_same_env.
          exact Hroots_args_hidden. }
        assert (Hroots_args_clean :
          store_roots_within (root_env_remove x_local R') s_args_base).
        { eapply store_roots_within_remove_env.
          - exact Hroots_args_base.
          - exact Hbase_no_x. }
        assert (Hshadow_args_clean : store_no_shadow s_args_base).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          apply store_no_shadow_remove. exact Hshadow_args_hidden. }
        assert (Hrn_args_clean : root_env_no_shadow (root_env_remove x_local R')).
        { apply root_env_no_shadow_remove. exact Hrn_args_hidden. }
        assert (Hnamed_args_removed_env :
          root_env_store_roots_named (root_env_remove x_local R') s_args_hidden).
        { eapply root_env_store_roots_named_remove_env; eassumption. }
        assert (Hnamed_args_clean :
          root_env_store_roots_named (root_env_remove x_local R') s_args_base).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          eapply root_env_store_roots_named_store_remove_excluding.
          - intros y roots Hlookup_removed.
            assert (Hyx : y <> x_local).
            { intro Heq. subst y.
              rewrite root_env_lookup_remove_eq_no_shadow in Hlookup_removed
                by exact Hrn_args_hidden.
              discriminate. }
            assert (Hxy : x_local <> y).
            { intro Heq. apply Hyx. symmetry. exact Heq. }
            eapply Htail_excludes_x.
            + rewrite <- (root_env_lookup_remove_neq x_local y R' Hxy).
              exact Hlookup_removed.
            + exact Hyx.
          - exact Hnamed_args_removed_env.
          - intros z Hin_z Hneq.
            apply store_names_remove_keeps_other; assumption. }
        assert (Hkeys_args_clean :
          root_env_store_keys_named (root_env_remove x_local R') s_args_base).
        { rewrite <- (store_hidden_frame_rel_remove_base x_local T
            (VClosure (fn_name fcallee) []) s_args_hidden s_args_base
            Hrel_args_outer).
          eapply root_env_store_keys_named_remove_env_store_remove; eassumption. }
        assert (Hsummary_args_clean :
          store_function_closure_targets_summary body_env s_args_base).
        { eapply (store_safe_function_value_call_args_eval_preserves_store_function_closure_targets_summary
            body_env args s1 s_args_base vs_outer); eassumption. }
        rewrite Houter_removed_exact.
        constructor.
        - exact Hstore_args_clean.
        - rewrite <- Houter_removed_exact.
          assert (Hv_nested_body_env :
            value_has_type body_env (store_remove x_local s_body_hidden) v
              (apply_lt_ty sigma_nested
                (subst_type_params_ty type_args_nested
                  (fn_ret fcallee_nested)))).
          { exact (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg_nested_body). }
          assert (Hv_outer_body :
            value_has_type body_env (store_remove x_local s_body_hidden) v
              T_body_nested).
          { rewrite Hret_runtime. exact Hv_nested_body_env. }
          assert (Hv_outer_ret :
            value_has_type body_env (store_remove x_local s_body_hidden) v
              (fn_ret fcallee)).
          { eapply value_has_type_compatible.
            - exact Hv_outer_body.
            - apply ty_compatible_b_sound with (Ω := fn_outlives fcallee).
              exact Hcompat_nested. }
          rewrite Hret_alpha_outer in Hv_outer_ret.
          rewrite Hfinal_hidden.
          change (value_has_type body_env
            (store_remove x_local (store_remove_params ps_outer s_body_hidden)) v
            (apply_lt_ty σ (fn_ret fcallee))).
          rewrite (store_remove_params_store_remove_commute ps_outer x_local
            s_body_hidden Hnotin_outer_params).
          apply value_has_type_apply_lt_ty.
          rewrite Hret_alpha_outer.
          eapply value_has_type_store_remove_params_excluding.
          + exact Hv_outer_ret.
          + eapply value_roots_exclude_params.
            * exact (generic_direct_call_package_value_roots
                _ _ _ _ _ _ _ _ Hpkg_nested_body).
            * exact Hexcl_runtime_roots.
        - exact Hpres_args_clean.
        - exact Hroots_args_clean.
        - eapply direct_call_value_roots_within_store_subset.
          + exact (generic_direct_call_package_value_roots
              _ _ _ _ _ _ _ _ Hpkg_nested_body).
          + exact Hnested_roots_subset.
        - exact Hshadow_args_clean.
        - exact Hrn_args_clean.
        - exact Hnamed_args_clean.
        - exact Hkeys_args_clean.
        - exact Hsummary_args_clean. }
      pose proof (generic_direct_call_package_value _ _ _ _ _ _ _ _ Hpkg_body)
        as Hv_body.
      assert (Hv_removed_body :
        value_has_type body_env (store_remove x_local s2) v
          (apply_lt_ty σ (fn_ret fcallee))).
      { exact Hv_body. }
      assert (Hv_env :
        value_has_type env (store_remove x_local s2) v
          (apply_lt_ty σ (fn_ret fcallee))).
      { subst body_env.
        eapply value_has_type_clear_global_env_local_bounds.
        exact Hv_removed_body. }
      eapply VHT_Compatible.
      * exact Hv_env.
      * apply ty_compatible_b_sound. exact Hcompat.
    + inversion Heval.
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
  eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact (Hsummary (fn_name f) f Hlookup).
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined Hsynthetic_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_mutual;
      eassumption.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual;
    try eassumption.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary_evidence.
    exact Hcomponent_check.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_synthetic_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_roots_ready_mutual.
  - exact eval_preserves_root_names_ready_mutual.
  - exact eval_preserves_root_keys_named_ready_mutual.
  - exact eval_preserves_frame_scope_roots_ready_mutual.
  - exact eval_preserves_param_scope_roots_ready_mutual.
  - exact Hunique.
  - exact Hcombined_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hsummary Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact Hsummary.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_final_roots_and_cleanup;
      eassumption.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined Hsynthetic_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual;
      eassumption.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual;
    try eassumption.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary_evidence.
    exact Hcomponent_check.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_synthetic_route :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_synthetic env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_mutual.
  - exact Hsynthetic_call_route.
  - exact Hscope_synthetic.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_roots_ready_mutual.
  - exact eval_preserves_root_names_ready_mutual.
  - exact eval_preserves_root_keys_named_ready_mutual.
  - exact eval_preserves_frame_scope_roots_ready_mutual.
  - exact eval_preserves_param_scope_roots_ready_mutual.
  - exact Hunique.
  - exact Hcombined_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique Hsummary
    Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact Hsummary.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_plain_summary_exact_package.
    exact Hpackage.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hsummary_body Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_evidence.
  - exact Hunique.
  - exact Hsummary_body.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - exact Hpackage.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env (fn_bounds f)) ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hsummary_body Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_store_safe_summary_evidence.
  - exact Hunique.
  - exact Hsummary_body.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_plain_summary_exact_package.
    exact Hpackage.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique Hcombined
    Hsynthetic_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package;
      eassumption.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique Hcombined
    Hbody_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_store_safe_summary_evidence.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hpackage.
    + exact Hunique.
    + apply Hbody_summary. exact Hcomponent.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_provider
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique Hcombined
    Hbody_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_summary_evidence.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hpackage.
    + exact Hunique.
    + apply Hbody_summary. exact Hcomponent.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_store_safe_synthetic_direct_call_ready_summary_provider
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hcombined_check Hbody_summary Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Lemma component_body_synthetic_direct_call_ready_body_env_evidence_provider_of_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hsummary f_component
    _Hcomponent fcall.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds env (fn_bounds f_component))
    (fn_bounds fcall)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    exact Hsummary.
Qed.

Lemma component_body_synthetic_direct_call_ready_body_env_evidence_provider_of_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hprovider f_component Hcomponent
    fcall.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds env (fn_bounds f_component))
    (fn_bounds fcall)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply Hprovider. exact Hcomponent.
Qed.


Lemma component_body_synthetic_direct_call_ready_nested_summary_at_in_provider_of_summary_evidence :
  forall env,
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env.
Proof.
  intros env Hsummary f_component _Hin _Hcomponent fcall fname args
    synthetic_body _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  exact Hsummary.
Qed.

Lemma component_body_synthetic_direct_call_ready_nested_summary_at_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env.
Proof.
  intros env Hprovider f_component _Hin Hcomponent fcall fname args
    synthetic_body _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env.
Proof.
  intros env Hprovider f_component _Hin Hcomponent fdef fcall used used'
    fname args synthetic_body _Hfdef_component _Hrename _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider_of_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hsummary f_component _Hin
    _Hcomponent fcall fcall_inner.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds
      (global_env_with_local_bounds env (fn_bounds f_component))
      (fn_bounds fcall))
    (fn_bounds fcall_inner)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    exact Hsummary.
Qed.

Lemma component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider_of_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hprovider f_component _Hin
    Hcomponent fcall fcall_inner.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds
      (global_env_with_local_bounds env (fn_bounds f_component))
      (fn_bounds fcall))
    (fn_bounds fcall_inner)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider_of_provider :
  forall env,
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider env.
Proof.
  intros env Hprovider f_component _Hin Hcomponent fcall fcall_inner fname
    args synthetic_body _Htarget.
  eapply fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_env.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
  eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider_of_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hprovider f_component _Hin
    Hcomponent fcall fcall_inner fcall_inner2.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds
      (global_env_with_local_bounds
        (global_env_with_local_bounds env (fn_bounds f_component))
        (fn_bounds fcall))
      (fn_bounds fcall_inner))
    (fn_bounds fcall_inner2)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    eapply Hprovider. exact Hcomponent.
Qed.

Lemma component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider_of_provider :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    component_body_synthetic_direct_call_ready_summary_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hprovider f_component _Hin
    Hcomponent fdef fcall used used' _Hfdef_component _Hrename fcall_inner.
  eapply (direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary
    Hroot_names Hroot_keys
    (global_env_with_local_bounds
      (global_env_with_local_bounds env (fn_bounds f_component))
      (fn_bounds fcall))
    (fn_bounds fcall_inner)).
  - unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
    eapply Hprovider. exact Hcomponent.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpackage env f s s' v Hunique Hcombined Hsummary_at_provider
    Hbody_evidence_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_evidence.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + eapply Hbody_evidence_provider. exact Hcomponent.
    + exact Hpackage.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_in_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpackage env f s s' v Hunique Hcombined Hsummary_at_provider
    Hbody_evidence_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_evidence.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + eapply Hbody_evidence_provider; eassumption.
    + exact Hpackage.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Hnested_summary_provider Hnested_body_provider
    Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_call_route_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fcall fname_body args_body synthetic_body Htarget.
      eapply Hnested_summary_provider; eassumption.
    + intros fcall fcall_inner.
      eapply Hnested_body_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Hnested_summary_provider Hnested_body_provider
    Hnested2_summary_provider Hnested2_body_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_prefix_scope_call_route_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_summary_at.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fcall fname_body args_body synthetic_body Htarget.
      eapply Hnested_summary_provider; eassumption.
    + intros fcall fcall_inner fname_body args_body synthetic_body Htarget.
      eapply Hnested2_summary_provider; eassumption.
    + intros fcall fcall_inner.
      eapply Hnested_body_provider; eassumption.
    + intros fcall fcall_inner fcall_inner2.
      eapply Hnested2_body_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Hnested_summary_provider Hnested_body_provider
    Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_summary_at Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Hnested_summary_provider Hnested_body_provider
    Hnested2_summary_provider Hnested2_body_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_summary_at.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Hnested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hnested2_summary_provider.
  - exact Hnested2_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider
    Hnested_body_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_summary_at_call_route_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply Htarget_provider; eassumption.
    + intros fdef fcall used used' fname_body args_body synthetic_body
        Hfdef_component Hrename Htarget_body.
      eapply Halpha_nested_summary_provider; eassumption.
    + intros fcall fcall_inner.
      eapply Hnested_body_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider
    Hnested_body_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Hnested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_nested_evidence_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider
    Halpha_nested_body_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_nested_evidence_at_call_route_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply Htarget_provider; eassumption.
    + intros fdef fcall used used' fname_body args_body synthetic_body
        Hfdef_component Hrename Htarget_body.
      eapply Halpha_nested_summary_provider; eassumption.
    + intros fdef fcall used used' Hfdef_component Hrename.
      eapply Halpha_nested_body_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_nested_evidence_at_call_route_with_component_body_nested_in_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider
    Halpha_nested_body_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_nested_evidence_at_call_route_with_component_body_nested_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Halpha_nested_body_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.
Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_summary_in_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply Htarget_provider; eassumption.
    + intros fdef fcall used used' fname_body args_body synthetic_body
        Hfdef_component Hrename Htarget_body.
      eapply Halpha_nested_summary_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_summary_in_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Htarget_provider Halpha_nested_summary_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_summary_in_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_nested_summary_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply Htarget_provider; eassumption.
    + intros fname_component args_component synthetic_component fdef Htarget_component
        Hlookup_component Hfdef_component fcall used used' fname_body args_body
        synthetic_body Hrename Htarget_body ftarget Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply Halpha_lookup_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hcombined
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_non_store_safe.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      eapply Hsummary_at_provider; eassumption.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply Htarget_provider; eassumption.
    + intros fname_component args_component synthetic_component fdef Htarget_component
        Hlookup_component Hfdef_component fcall used used' fname_body args_body
        synthetic_body Hrename Htarget_body ftarget Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply Halpha_lookup_provider; eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_lookup_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_lookup_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_ready
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hstrict Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hstrict (fn_name f) f Hlookup) as [Hcaptured | Hcomponent_branch].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct Hcomponent_branch as [Hcomponent_check [Hcomponent Hexact_check]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      pose proof Hcomponent as Hcomponent_summary.
      destruct Hcomponent_summary as
        (fname0 & args0 & raw_body0 & synthetic_body0 & fcallee & T_body0 &
          Gamma_out0 & R_body0 & roots_body0 & _Hcaptures0 & Hbody0 &
          Htarget0 & _Hsynthetic0 & _Hsafe_args0 & Hin_callee & Hname_callee &
          _Hcallee_captures0 & _Hnodup0 & _Htyped0 & _Hcompat0 & _Hroots0 &
          _Henv0).
      rewrite Hbody0 in Htarget.
      rewrite Htarget0 in Htarget. injection Htarget as <- <- <-.
      intros fdef Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * rewrite Hbody0. exact Htarget0.
      * exact Hlookup_target.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * exact Htarget.
      * exact Hlookup_target.
    + intros fname_component args_component synthetic_component fdef Htarget_component
        Hlookup_component Hfdef_component fcall used used' fname_body args_body
        synthetic_body Hrename Htarget_body ftarget Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_ready
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hstrict Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hstrict (fn_name f) f Hlookup) as [Hcaptured | Hcomponent_branch].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - destruct Hcomponent_branch as [Hcomponent_check [Hcomponent Hexact_check]].
    eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_non_store_safe.
    + exact Hsynthetic_route.
    + exact Hscope_synthetic.
    + exact Htyping_ready.
    + exact Hroots_ready.
    + exact Hroot_names.
    + exact Hroot_keys.
    + exact Hstatic.
    + exact Hunique.
    + intros fname args synthetic_body Htarget.
      pose proof Hcomponent as Hcomponent_summary.
      destruct Hcomponent_summary as
        (fname0 & args0 & raw_body0 & synthetic_body0 & fcallee & T_body0 &
          Gamma_out0 & R_body0 & roots_body0 & _Hcaptures0 & Hbody0 &
          Htarget0 & _Hsynthetic0 & _Hsafe_args0 & Hin_callee & Hname_callee &
          _Hcallee_captures0 & _Hnodup0 & _Htyped0 & _Hcompat0 & _Hroots0 &
          _Henv0).
      rewrite Hbody0 in Htarget.
      rewrite Htarget0 in Htarget. injection Htarget as <- <- <-.
      intros fdef Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * rewrite Hbody0. exact Htarget0.
      * exact Hlookup_target.
    + intros fname args synthetic_body fdef Htarget Hlookup_target.
      eapply component_body_no_capture_direct_call_component_target_in_of_exact_closure_check.
      * exact Hunique.
      * exact Hin.
      * exact Hcomponent.
      * exact Hexact_check.
      * exact Htarget.
      * exact Hlookup_target.
    + intros fname_component args_component synthetic_component fdef Htarget_component
        Hlookup_component Hfdef_component fcall used used' fname_body args_body
        synthetic_body Hrename Htarget_body ftarget Hlookup_target.
      eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_of_no_capture_direct_call_component.
      eapply component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_exact_closure_check;
        eassumption.
    + exact Hcomponent.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
Qed.

Theorem check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hstrict_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    exact Hstrict_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hstrict_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hunique.
  - eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    exact Hstrict_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence :
  eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env f s s' v Hunique Hstrict_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hunique.
  - eapply env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready_of_strict_exact_closure.
    eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    exact Hstrict_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_lookup_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  preservation_ready_expr_static_runtime_named_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_no_capture_direct_call_component_target_in_provider env ->
    component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hstatic env f s s' v Hunique Hstrict_check
    Hsummary_at_provider Htarget_provider Halpha_lookup_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe.
  - exact Hsynthetic_route.
  - exact Hscope_synthetic.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hstatic.
  - exact Hunique.
  - eapply env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready_of_strict_exact_closure.
    eapply check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_strict_ready.
    exact Hstrict_check.
  - exact Hsummary_at_provider.
  - exact Htarget_provider.
  - exact Halpha_lookup_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.


Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_in_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_in_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_in_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpackage env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Hbody_evidence_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_in_evidence.
  - exact Hpackage.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Hbody_evidence_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_evidence :
  eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_at_provider env ->
    component_body_synthetic_direct_call_ready_body_env_evidence_provider env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpackage env f s s' v Hunique Hcombined_check
    Hsummary_at_provider Hbody_evidence_provider Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_exact_package_with_component_body_summary_at_evidence.
  - exact Hpackage.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hsummary_at_provider.
  - exact Hbody_evidence_provider.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    component_body_synthetic_direct_call_ready_summary_provider
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hcombined_check Hbody_summary Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence.
  - exact Hroot_names.
  - exact Hroot_keys.
  - exact Hpackage.
  - exact Hunique.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - exact Hbody_summary.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package;
    try eassumption.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary_evidence.
    exact Hcomponent_check.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_store_safe_summary_evidence :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hroot_names Hroot_keys Hpackage env f s s' v Hunique
    Hcombined_check Hsynthetic_summary Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package;
    try eassumption.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
  exact Hcombined_check.
Qed.

Theorem callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env f ->
    check_initial_root_runtime_ready f s = true ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hsummary Hcomponent Hinitial Hstore Heval.
  eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready.
  - exact Hunique.
  - exact Hsummary.
  - intros bounds.
    eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
    + exact Hroot_names.
    + exact Hroot_keys.
    + unfold fn_env_unique_by_name in *; simpl. exact Hunique.
  - eapply eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_routes_final_roots_and_cleanup;
      eassumption.
  - exact Hcomponent.
  - exact Hinitial.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready
      env ->
    env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence
      env ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined Hsynthetic_summary Hinitial Hin Hstore Heval.
  pose proof (lookup_fn_in_unique_by_name env
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  destruct (Hcombined (fn_name f) f Hlookup) as [Hcaptured | Hcomponent].
  - eapply callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready.
    + exact Hunique.
    + exact Hcaptured.
    + exact Hinitial.
    + exact Hstore.
    + exact Heval.
  - eapply callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual;
      eassumption.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual;
    try eassumption.
  - eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready.
    exact Hcombined_check.
  - eapply check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary_evidence.
    exact Hcomponent_check.
Qed.

Theorem check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_routes :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  forall env f s s' v,
    fn_env_unique_by_name env ->
    check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary
      env = true ->
    check_env_root_shadow_no_capture_direct_call_component_store_safe_summary
      env = true ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env) ->
    initial_store_for_fn env f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hsynthetic_call_route Hscope_call env f s s' v Hunique
    Hcombined_check Hcomponent_check Hinitial Hin Hstore Heval.
  eapply check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_call_statement_routes_mutual.
  - exact Hsynthetic_call_route.
  - exact Hscope_call.
  - exact eval_preserves_typing_ready_mutual.
  - exact eval_preserves_roots_ready_mutual.
  - exact eval_preserves_root_names_ready_mutual.
  - exact eval_preserves_root_keys_named_ready_mutual.
  - exact eval_preserves_frame_scope_roots_ready_mutual.
  - exact eval_preserves_param_scope_roots_ready_mutual.
  - exact Hunique.
  - exact Hcombined_check.
  - exact Hcomponent_check.
  - exact Hinitial.
  - exact Hin.
  - exact Hstore.
  - exact Heval.
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
