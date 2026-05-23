From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeNonCapturingSafety.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

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
  pose proof (check_program_env_alpha_validated_unique env Hvalidated)
    as Hunique.
  pose proof
    (check_env_root_shadow_captured_call_provenance_summary_ready
      (alpha_normalize_global_env env) Hsummary_check)
    as Hsummary.
  pose proof (lookup_fn_in_unique_by_name (alpha_normalize_global_env env)
    (fn_name f) f Hin eq_refl Hunique) as Hlookup.
  pose proof (Hsummary (fn_name f) f Hlookup) as Hfn_summary.
  destruct (check_initial_root_runtime_ready_sound f s Hinitial) as
    [Hroots [Hstore_shadow [Hnamed Hkeys]]].
  destruct Hfn_summary as [Hnoncapturing | Hcaptured_summary].
  - destruct Hnoncapturing as [Hdirect_or_prov | Hlocal_summary].
    + destruct Hdirect_or_prov as [Hprov_summary | Hdirect_summary].
      * destruct Hprov_summary as [Hnodup Hbody_summary].
        unfold callee_body_root_shadow_provenance_ready_at in Hbody_summary.
        destruct Hbody_summary as
          (T_body & Γ_out & R_body & roots_body &
            Hprov_body & Htyped_shadow & Hcompat & _ & _).
        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
          as Hroot_shadow.
        destruct (proj1 eval_preserves_typing_roots_ready_mutual
            (alpha_normalize_global_env env) s (fn_body f) s' v Heval
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            T_body (sctx_of_ctx Γ_out) R_body roots_body
            Hprov_body Hstore Hroots Hstore_shadow Hroot_shadow
            (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) (initial_root_env_for_fn f)
              (sctx_of_ctx (fn_body_ctx f))
              (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_shadow))
          as [_ [Hv _]].
        eapply VHT_Compatible.
        -- exact Hv.
        -- apply ty_compatible_b_sound. exact Hcompat.
      * destruct Hdirect_summary as
          (fname & args & raw_body & synthetic_body & fcallee & T_body &
            Γ_out & R_body & roots_body & Hbody & Htarget & Hsynthetic &
            Hready_args & Hin_callee & Hname_callee & Hcallee_summary &
            Hnodup & Htyped_shadow & Hcompat & _ & _).
        pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
          as Hroot_shadow.
        rewrite Hbody in Heval.
        assert (Htyped_call :
          typed_env_roots_shadow_safe (alpha_normalize_global_env env)
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f)) (ECall fname args)
            T_body (sctx_of_ctx Γ_out) R_body roots_body).
        { rewrite <- Hsynthetic. exact Htyped_shadow. }
        assert (Heval_call :
          eval (alpha_normalize_global_env env) s (ECall fname args) s' v).
        { unfold direct_call_target_expr in Htarget.
          destruct raw_body; try discriminate.
          - inversion Htarget; subst. exact Heval.
          - destruct raw_body; try discriminate.
            inversion Htarget; subst.
            apply eval_call_expr_fn_as_call. exact Heval. }
        destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
            (alpha_normalize_global_env env) s s' v fname args Heval_call
            (fn_outlives f) (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f))
            T_body (sctx_of_ctx Γ_out) R_body roots_body fcallee
            Hready_args Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
            (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) (initial_root_env_for_fn f)
              (sctx_of_ctx (fn_body_ctx f))
              (ECall fname args) T_body (sctx_of_ctx Γ_out) R_body
              roots_body Htyped_call)
            Hunique Hin_callee Hname_callee Hcallee_summary)
          as [_ [Hv _]].
        eapply VHT_Compatible.
        -- exact Hv.
        -- apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hlocal_summary as
        (fname & args & raw_body & synthetic_body & fcallee & T_body &
          Γ_out & R_body & roots_body & Hbody & Htarget & Hready_args &
          Hin_callee & Hname_callee & Hcallee_summary & Hnodup &
          Htyped_shadow & Hcompat & Hexclude_roots & Hexclude_env).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup)
        as Hroot_shadow.
      rewrite Hbody in Heval.
      unfold local_fn_value_call_target_expr in Htarget.
      destruct raw_body as
        [| lit | z | m x T e1 e2 | m x e1 e2 | fname_alias
         | fname_make captures_make | p | fname_direct args_direct
         | callee args_call | sname lts tys fields
         | p e_new | p e_new | rk p | e | e | e1 e2 e3];
        try discriminate.
      * destruct e1 as
          [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
           | fname_value | fname_make1 captures_make1 | p1
           | fname1 args1 | callee1 args1 | sname1 lts1 tys1 fields1
           | p1 e_new1 | p1 e_new1 | rkc1 p1 | e1 | e1 | e11 e12 e13];
          try discriminate.
        destruct e2 as
          [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
           | fname2 | fname_make2 captures_make2 | p2
           | fname2 args2 | callee2 args2 | sname2 lts2 tys2 fields2
           | p2 e_new2 | p2 e_new2 | rkc2 p2 | e2 | e2 | e21 e22 e23];
          try discriminate.
        destruct callee2 as
          [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
           | fnamec | fname_makec captures_makec | pc
           | fnamec argsc | calleec argsc | snamec ltsc tysc fieldsc
           | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
          try discriminate.
        destruct (ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted)
          eqn:Halias; try discriminate.
        inversion Htarget; subst; clear Htarget.
        apply andb_true_iff in Halias as [Hname_eq Husage_eq].
        apply ident_eqb_eq in Hname_eq. subst y.
        apply usage_eqb_true in Husage_eq.
        match goal with
        | He : eval ?env0 ?s0
            (ELet ?m0 ?x0 ?T0 (EFn ?fname0)
              (ECallExpr (EVar ?x0) ?args0)) ?sfinal ?vfinal |- _ =>
            assert (Heval_synthetic :
              eval env0 s0
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
            typed_env_roots_shadow_safe _ _ _ (root_env_add _ _ _)
              (sctx_add _ _ _ _) (ECall _ _) _ _ _ _ |- _ =>
            pose proof (typed_env_roots_shadow_safe_roots
              (alpha_normalize_global_env env) (fn_outlives f)
              (fn_lifetimes f) _ _ _ _ _ _ _ Htyped_call_shadow)
              as Htyped_call
        end.
        assert (Hfresh_store : store_lookup x0 s1 = None)
          by (eapply store_roots_within_lookup_none; eassumption).
        assert (Hadd_pres :
          store_ref_targets_preserved (alpha_normalize_global_env env) s1
            (store_add x0 T (VClosure (fn_name fcallee) []) s1))
          by (apply store_add_fresh_ref_targets_preserved;
              exact Hfresh_store).
        assert (Hv_closure_actual :
          value_has_type (alpha_normalize_global_env env) s1
            (VClosure (fn_name fcallee) []) (fn_value_ty fdef))
          by (eapply VHT_ClosureIn; [exact H | exact x]).
        assert (Hv_closure :
          value_has_type (alpha_normalize_global_env env) s1
            (VClosure (fn_name fcallee) []) T)
        by (eapply VHT_Compatible;
            [ exact Hv_closure_actual
            | apply ty_compatible_b_sound; exact H0 ]).
        assert (Hstore_add :
          store_typed (alpha_normalize_global_env env)
            (store_add x0 T (VClosure (fn_name fcallee) []) s1)
            (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f))))
        by (eapply store_typed_add;
            [ exact Hstore | exact Hv_closure | exact Hadd_pres ]).
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
        match goal with
        | Heval_call : eval _ _ (ECall (fn_name fcallee) args) s2 v |- _ =>
            destruct (eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary
                (alpha_normalize_global_env env)
                (store_add x0 T (VClosure (fn_name fcallee) []) s1) s2 v
                (fn_name fcallee) args Heval_call
                (fn_outlives f) (fn_lifetimes f)
                (root_env_add x0 [] (initial_root_env_for_fn f))
                (sctx_add x0 T m (sctx_of_ctx (fn_body_ctx f)))
                T2 Σ2 R2 roots2 fcallee
                Hready_args Hstore_add Hroots_add Hshadow_add Hrn_add
                Hnamed_add Hkeys_add Htyped_call Hunique Hin_callee
                eq_refl Hcallee_summary)
              as [_ [Hv_inner [_ [_ [Hv_roots _]]]]]
        end.
        assert (Hexclude_v : value_refs_exclude_root x0 v)
          by (eapply value_roots_exclude_root; eassumption).
        assert (Hv_removed :
          value_has_type (alpha_normalize_global_env env) (store_remove x0 s2)
            v T2)
          by (eapply value_has_type_store_remove_excluding_root; eassumption).
        eapply VHT_Compatible.
        -- exact Hv_removed.
        -- apply ty_compatible_b_sound. exact Hcompat.
      * inversion Heval.
  - destruct Hcaptured_summary as
      [Hcaptured_summary | [Hif_summary | Hlocal_captured_summary]].
    + destruct Hcaptured_summary as
      (fname & captures & args & fcallee & env_lt & captured_tys &
        T_body & Γ_out & R_body & roots_body &
        Hbody & Htarget & Hready_args & Hin_callee & Hname_callee &
        Hcallee_lts & Hdisjoint & Hcaptures & Hcallee_summary &
        Hnodup & Htyped_shadow & Hcompat & _ & _).
    pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
    rewrite Hbody in Heval.
    rewrite Hbody in Htyped_shadow.
    dependent destruction Heval.
    pose proof Heval1 as Heval_make.
    dependent destruction Heval1.
    dependent destruction Htyped_shadow.
    repeat match goal with
    | Hlookup : lookup_fn ?fname_call
        (env_fns (alpha_normalize_global_env env)) =
        Some ?f_runtime |- _ =>
        lazymatch f_runtime with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_callee" in
            assert (Hsame : f_runtime = fcallee)
              by (eapply lookup_fn_unique_by_name;
                  [ exact Hlookup | exact Hin_callee | exact Hname_callee
                  | exact Hunique ]);
            subst f_runtime
        end
    | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
      Hname_typed : fn_name ?f_typed = ?fname_call |- _ =>
        lazymatch f_typed with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_typed_callee" in
            assert (Hsame : f_typed = fcallee)
              by (eapply Hunique;
                  [ exact Hin_typed | exact Hin_callee
                  | rewrite Hname_typed; exact Hname_callee ]);
            subst f_typed
        end
    end.
    match goal with
    | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
      Hname_eq : fn_name fcallee = fn_name ?f_typed |- _ =>
        lazymatch f_typed with
        | fcallee => fail
        | _ =>
            let Hsame := fresh "Hsame_typed_callee" in
            assert (Hsame : f_typed = fcallee)
              by (eapply Hunique;
                  [ exact Hin_typed | exact Hin_callee
                  | symmetry; exact Hname_eq ]);
            subst f_typed
        end
    end.
    destruct Hcallee_summary as
      [Hnodup_binding
       (T_callee & Γ_callee & R_callee & roots_callee &
        Hprov_callee & Htyped_callee & Hcompat_callee &
        Hexclude_roots_callee & Hexclude_env_callee)].
    assert (Hnodup_caps :
      NoDup (ctx_names (params_ctx (fn_captures fcallee)))).
    { rewrite params_ctx_app, ctx_names_app in Hnodup_binding.
      eapply NoDup_app_right_ts. exact Hnodup_binding. }
    match goal with
    | Hlookup : lookup_fn ?fname_call
        (env_fns (alpha_normalize_global_env env)) =
        Some fcallee,
      Hcopy : copy_capture_store_as captures (fn_captures fcallee) s =
        Some captured,
      Htyped_args_shadow : typed_args_roots_shadow_safe
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args (fn_params fcallee) ?Sigma_args ?R_args ?arg_roots,
      Heval_args : eval_args (alpha_normalize_global_env env) s args s_args vs,
      Hrename : alpha_rename_fn_def (store_names (captured ++ s_args))
        fcallee = (fcall, used'),
      Heval_body : eval (alpha_normalize_global_env env)
        (bind_params (fn_params fcall) vs (captured ++ s_args))
        (fn_body fcall) s_body ?ret |- _ =>
      pose proof (typed_args_roots_shadow_safe_roots
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args (fn_params fcallee) Sigma_args R_args arg_roots
        Htyped_args_shadow)
        as Htyped_args_roots;
      destruct (eval_make_closure_captured_call_expr_preserves_typing_with_callee_components
        (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
        (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
        args fname_call captures captured fcallee fcall used' s s_args s_body vs ret
        R_args Sigma_args arg_roots env_lt captured_tys T_callee Γ_callee
        R_callee roots_callee
        Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
        (Eval_MakeClosure (alpha_normalize_global_env env) s fname_call captures
          captured fcallee Hlookup Hcopy)
        Hlookup Heval_args Hrename Heval_body Hcaptures Hnodup_caps Hready_args
        Htyped_args_roots Hnodup_binding Hprov_callee Htyped_callee Hcompat_callee
        Hexclude_roots_callee Hexclude_env_callee)
      as [_ [_ Hv]]
	    end.
	    eapply VHT_Compatible.
	    * rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
	    * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hif_summary as
        (T_body & Γ_out & R_body & roots_body & ret_roots & Hnodup &
          Hexpr_summary & Hcompat & _ & _).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
      destruct
        (eval_expr_root_shadow_captured_call_provenance_summary_exact_preserves_typing
          (alpha_normalize_global_env env) (fn_outlives f) (fn_lifetimes f)
          (initial_root_env_for_fn f) (sctx_of_ctx (fn_body_ctx f))
          (fn_body f) T_body (sctx_of_ctx Γ_out) R_body roots_body
          ret_roots Hexpr_summary s s' v Hstore Hroots Hstore_shadow
          Hroot_shadow Hnamed Hkeys Heval Hunique) as [_ Hv].
      eapply VHT_Compatible.
      * exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat.
    + destruct Hlocal_captured_summary as
        (fname & captures & args & m & x & T & direct_body & let_body &
          fcallee & env_lt & captured_tys & T_direct & Γ_direct & R_direct &
          roots_direct & T_let & Γ_let & R_let & roots_let &
          Hbody & Htarget & Hdirect & Hlet & Husage & Hnot_caps &
          Hfresh_cap_names & Hfree_args & Hlocal_args & Hready_args &
          Hin_callee & Hname_callee & Hcallee_lts & Hdisjoint &
          Hcaptures & Hcallee_summary & Hnodup & Htyped_direct &
          Hcompat_direct & _ & _ & Htyped_let).
      pose proof (initial_root_env_for_fn_no_shadow f Hnodup) as Hroot_shadow.
	      pose proof (lookup_fn_in_unique_by_name
	                    (alpha_normalize_global_env env) fname fcallee
	                    Hin_callee Hname_callee Hunique) as Hlookup_callee.
	      rewrite Hbody in Heval.
	      rewrite Hlet in Htyped_let.
	      rewrite Hdirect in Htyped_let.
	      rewrite Hdirect in Htyped_direct.
	      dependent destruction Htyped_direct.
	      repeat match goal with
	      | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
	        Hname_typed : fn_name ?f_typed = ?fname0,
	        Hname_callee0 : fn_name fcallee = ?fname0 |- _ =>
	          lazymatch f_typed with
	          | fcallee => fail
	          | _ =>
	              let Hsame := fresh "Hsame_typed_callee" in
	              assert (Hsame : f_typed = fcallee)
	                by (eapply Hunique;
	                    [ exact Hin_typed | exact Hin_callee
	                    | rewrite Hname_typed; symmetry; exact Hname_callee0 ]);
	              subst f_typed
	          end
	      | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
	        Hname_eq : fn_name fcallee = fn_name ?f_typed |- _ =>
	          lazymatch f_typed with
	          | fcallee => fail
	          | _ =>
	              let Hsame := fresh "Hsame_typed_callee" in
	              assert (Hsame : f_typed = fcallee)
	                by (eapply Hunique;
	                    [ exact Hin_typed | exact Hin_callee
	                    | symmetry; exact Hname_eq ]);
	              subst f_typed
	          end
	      | Hin_typed : In ?f_typed (env_fns (alpha_normalize_global_env env)),
	        Hname_eq : fn_name ?f_typed = fn_name fcallee |- _ =>
	          lazymatch f_typed with
	          | fcallee => fail
	          | _ =>
	              let Hsame := fresh "Hsame_typed_callee" in
	              assert (Hsame : f_typed = fcallee)
	                by (eapply Hunique;
	                    [ exact Hin_typed | exact Hin_callee
	                    | exact Hname_eq ]);
	              subst f_typed
	          end
	      end.
      match goal with
      | Htyped_args_shadow : typed_args_roots_shadow_safe
          (alpha_normalize_global_env env) (fn_outlives f)
          (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
          ?Sigma_args ?R_args ?arg_roots |- _ =>
          pose proof (typed_args_roots_shadow_safe_roots
            (alpha_normalize_global_env env) (fn_outlives f)
            (fn_lifetimes f) (initial_root_env_for_fn f)
            (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
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
      match goal with
      | Htyped_args_roots : typed_args_roots
          (alpha_normalize_global_env env) (fn_outlives f)
          (fn_lifetimes f) (initial_root_env_for_fn f)
          (sctx_of_ctx (fn_body_ctx f)) args (fn_params fcallee)
          ?Sigma_args ?R_args ?arg_roots |- _ =>
          destruct
	            (eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components
	              (alpha_normalize_global_env env) (fn_outlives f)
	              (fn_lifetimes f) (initial_root_env_for_fn f)
	              (sctx_of_ctx (fn_body_ctx f)) m x0 T args (fn_name fcallee) captures
	              fcallee s s' v R_args Sigma_args arg_roots env_lt captured_tys
              T_callee Γ_callee R_callee roots_callee
              Hstore Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys
              Husage Heval Hcaptures Hnodup_caps Hready_args
              Htyped_args_roots Hnodup_binding Hprov_callee Htyped_callee
              Hcompat_callee Hexclude_roots_callee Hexclude_env_callee
              Hlookup_callee Hfresh_s Hfresh_cap_names Hfree_args
              Hlocal_args)
            as [_ Hv]
      end.
      eapply VHT_Compatible.
      * rewrite apply_lt_ty_nil_ts in Hv. exact Hv.
      * apply ty_compatible_b_sound. exact Hcompat_direct.
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
    direct_call_callee_body_root_check_evidence (alpha_normalize_global_env env) ->
    eval (alpha_normalize_global_env env) s (fn_body f) s' v ->
    value_has_type (alpha_normalize_global_env env) s' v (fn_ret f).
Proof.
  intros env f R0 T Γ' R' roots s s' v _ Hroots_infer Hstore Hready
    Hroots Hstore_shadow Hroot_shadow Hnamed Hkeys Hunique Hfns_ready
    Hcallee_roots Heval.
  eapply infer_full_env_roots_alpha_big_step_safe_direct_call_ready;
    eassumption.
Qed.
