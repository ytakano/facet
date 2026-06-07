From Facet.TypeSystem Require Import Types Syntax PathState Program Renaming TypingRules RootProvenance TypeChecker EnvStructuralRules.
From Facet.TypeSystem Require Export ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn AlphaTyping AlphaEnvStructural AlphaRoots.
From Facet.TypeSystem Require Export AlphaRootEnvFacts.
From Facet.TypeSystem Require Export AlphaTypedRoots.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.


Lemma alpha_rename_fn_def_typed_structural_forward :
  forall env used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    typed_fn_env_structural env f ->
    typed_fn_env_structural env fr.
Proof.
  intros env used f fr used' Hrename Hnodup Htyped.
  destruct f as [fname lifetimes outs captures ps ret body].
  unfold alpha_rename_fn_def in Hrename. simpl in Hrename.
  destruct (alpha_rename_params []
    (param_names ps ++ param_names captures ++ free_vars_expr body ++ used) ps)
    as [[psr ρ] used1] eqn:Hps.
  destruct (alpha_rename_expr ρ used1 body) as [bodyr used2] eqn:Hbody.
  injection Hrename as <- <-.
  unfold typed_fn_env_structural in *. simpl in *.
  destruct Htyped as [T_body [Γ_out [Htyped_body [Hcompat Hparams]]]].
  unfold fn_body_ctx, fn_body_params in Htyped_body.
  simpl in Htyped_body.
  destruct (alpha_rename_typed_env_structural_forward
    (global_env_with_local_bounds env fn_bounds) outs lifetimes ρ
    (sctx_of_ctx (params_ctx (ps ++ captures)))
    (sctx_of_ctx (params_ctx (psr ++ captures)))
    body bodyr used1 used2 T_body (sctx_of_ctx Γ_out))
    as [Σr_out [Htyped_body_r Hctx_out_r]].
  - eapply alpha_rename_params_ctx_alpha_stable_tail. exact Hps.
  - intros x Hin.
    change (ctx_names (sctx_of_ctx (params_ctx (psr ++ captures))))
      with (ctx_names (params_ctx (psr ++ captures))) in Hin.
    rewrite params_ctx_app in Hin.
    rewrite ctx_names_app in Hin.
    rewrite !params_ctx_names_param_names in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_captures].
    + eapply alpha_rename_params_names_in_used.
      * exact Hps.
      * rewrite params_ctx_names_param_names. exact Hin_params.
    + eapply alpha_rename_params_used_extends.
      * exact Hps.
      * apply in_or_app. right.
        apply in_or_app. left. exact Hin_captures.
  - intros x Hin.
    eapply alpha_rename_params_range_in_used_nil.
    + exact Hps.
    + exact Hin.
  - intros x Hfree Hrange.
    eapply alpha_rename_params_range_fresh_used_nil.
    + exact Hps.
    + exact Hrange.
    + apply in_or_app. right.
      apply in_or_app. right.
      apply in_or_app. left. exact Hfree.
  - exact Hbody.
  - exact Htyped_body.
  - exists T_body, Σr_out. repeat split.
    + exact Htyped_body_r.
    + exact Hcompat.
    + eapply alpha_rename_params_params_ok_env_b_forward.
      * exact Hps.
      * exact Hnodup.
      * intros x Hin.
        apply in_or_app. left. exact Hin.
      * exact Hctx_out_r.
      * exact Hparams.
Qed.
