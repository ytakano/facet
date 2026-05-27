From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyParamScopeReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma typed_match_tail_roots_lookup_frame_ready :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss
      name vdef e,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants
      expected_core R_out Σs Ts rootss ->
    lookup_enum_variant name variants = Some vdef ->
    lookup_expr_branch name branches = Some e ->
    exists T Σv_payload Rv_payload Σv Rv roots ps binders R_payload,
      R_payload = root_env_add_params_roots_same ps roots_scrut R /\
      params_names_nodup_b ps = true /\
      root_env_lookup_params_none_b ps R = true /\
      lookup_expr_branch_binders name branches = Some binders /\
      match_payload_params_opt binders lts args vdef = Some ps /\
      typed_env_roots env Ω n R_payload (sctx_add_params ps Σ) e T
        Σv_payload Rv_payload roots /\
      Rv = root_env_remove_match_params ps Rv_payload /\
      Σv = sctx_remove_params ps Σv_payload /\
      ty_core T = expected_core /\
      root_env_equiv Rv R_out /\
      In Σv Σs /\
      In roots rootss.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss
    name vdef e Htail.
  induction Htail as
    [lts args R roots_scrut Σ branches expected_core R_out
    |R R_payload Rv_payload Rv Σ branches v rest e0 T
       Σv_payload Σv R_out roots Σs Ts rootss expected_core
       binders ps lts args roots_scrut
       Hbinders Hparams Hnodup Hctx_none Hroot_none Hlookup Hpayload
       Htyped Hparams_ok Hroots_excl Hremove Henv_excl Hctx_remove
       Hcore Hequiv Htail IHtail];
    intros Hvariant Hbranch.
  - simpl in Hvariant. discriminate.
  - simpl in Hvariant.
    destruct (String.eqb name (enum_variant_name v)) eqn:Hname.
    + apply String.eqb_eq in Hname. subst name.
      rewrite Hlookup in Hbranch. inversion Hbranch; subst e.
      inversion Hvariant; subst vdef.
      exists T, Σv_payload, Rv_payload, Σv, Rv, roots, ps, binders, R_payload.
      repeat split; simpl; auto.
      eapply match_payload_params_opt_infer_ok. exact Hparams.
    + destruct (IHtail Hvariant Hbranch) as
        [T' [Σpayload' [Rpayload' [Σ' [Rv' [roots' [ps' [binders'
        [Rbranch' Hrest]]]]]]]]].
      destruct Hrest as [HRpayload' Hrest].
      destruct Hrest as [Hnodup' Hrest].
      destruct Hrest as [Hroot_none' Hrest].
      destruct Hrest as [Hbinders' Hrest].
      destruct Hrest as [Hparams' Hrest].
      destruct Hrest as [Htyped' Hrest].
      destruct Hrest as [Hremove' Hrest].
      destruct Hrest as [Hctx_remove' Hrest].
      destruct Hrest as [Hcore' Hrest].
      destruct Hrest as [Hequiv' [HinΣ Hin]].
      exists T', Σpayload', Rpayload', Σ', Rv', roots', ps', binders', Rbranch'.
      repeat split; simpl; auto.
Qed.

Definition frame_scope_roots_ready_result
    (ps : list param) (R : root_env) (Σ : sctx) (s : store)
    (frame : store) : Prop :=
  root_env_covers_params ps R /\
  store_roots_within R s /\
  store_no_shadow s /\
  root_env_no_shadow R /\
  store_frame_scope ps Σ s frame /\
  store_frame_static_fresh Σ frame.

Definition frame_scope_roots_ready_expr_preservation : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame.

Theorem eval_preserves_frame_scope_roots_ready_args_fields_from_expr :
  frame_scope_roots_ready_expr_preservation ->
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame).
Proof.
  intros Hexpr.
  split.
  - intros env s args s' vs Heval.
    induction Heval as [s | s s1 s2 e es v vs Heval_e Heval_rest IHrest];
      intros Ω n R Σ params Σ' R' roots ps frame Hready Htyped
        Hcover Hroots Hshadow Hrn Hscope Hfresh.
    + inversion Htyped; subst.
      repeat split; assumption.
    + dependent destruction Hready.
      dependent destruction Htyped.
      match goal with
      | Hready_e : provenance_ready_expr _,
        Hready_rest : provenance_ready_args _,
        Htyped_e : typed_env_roots env Ω n R Σ _ ?T_e ?Σ1 ?R1 ?roots_e,
        Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 _ ?params_rest
          ?Σ2 ?R2 ?roots_rest |- _ =>
          destruct (Hexpr env s e s1 v Heval_e Ω n R Σ T_e Σ1 R1
                      roots_e ps frame Hready_e Htyped_e Hcover Hroots
                      Hshadow Hrn Hscope Hfresh)
            as [Hcover1 [Hroots1 [Hshadow1 [Hrn1 [Hscope1 Hfresh1]]]]];
          exact (IHrest Ω n R1 Σ1 params_rest Σ2 R2 roots_rest ps frame
                   Hready_rest Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                   Hscope1 Hfresh1)
      end.
  - intros env s fields defs s' values Heval.
    induction Heval as
      [s | s s1 s2 fields f rest e v values Hlookup_expr Heval_field
        Heval_rest IHrest];
      intros Ω n lts args R Σ Σ' R' roots ps frame Hready Htyped
        Hcover Hroots Hshadow Hrn Hscope Hfresh.
    + inversion Htyped; subst.
      repeat split; assumption.
    + pose proof (provenance_ready_fields_lookup fields (field_name f) e
                    Hready Hlookup_expr) as Hready_field.
      destruct (typed_fields_roots_cons_inv_ts env Ω n lts args R Σ
                  fields f rest Σ' R' roots Htyped)
        as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
      rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
      rewrite Hlookup_typed in Hlookup_expr.
      inversion Hlookup_expr; subst e_field.
      destruct (Hexpr env s e s1 v Heval_field Ω n R Σ T_field Σ1
                  R1 roots_field ps frame Hready_field Htyped_field
                  Hcover Hroots Hshadow Hrn Hscope Hfresh)
        as [Hcover1 [Hroots1 [Hshadow1 [Hrn1 [Hscope1 Hfresh1]]]]].
      exact (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest ps frame
               Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
               Hscope1 Hfresh1).
Qed.

Lemma store_param_prefix_update_state_same_frame :
  forall ps s_param frame x f s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_state x f s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x f s' Hprefix.
  revert x f s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x f s' Hnotin Hupdate.
  - rewrite store_update_state_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_state x f s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_mark_used_same_frame :
  forall ps s_param frame x,
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_param_prefix ps (store_mark_used x s_param) frame.
Proof.
  intros ps s_param frame x Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hnotin.
  - rewrite store_mark_used_not_in_names; [constructor | exact Hnotin].
  - simpl. destruct (ident_eqb x (param_name p)); constructor.
    + exact Hprefix.
    + apply IH. exact Hnotin.
Qed.

Lemma store_param_prefix_update_val_same_frame :
  forall ps s_param frame x v_new s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_val x v_new s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x v_new s' Hprefix.
  revert x v_new s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x v_new s' Hnotin Hupdate.
  - rewrite store_update_val_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_val x v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_update_path_same_frame :
  forall ps s_param frame x path v_new s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_path x path v_new s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x path v_new s' Hprefix.
  revert x path v_new s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x path v_new s' Hnotin Hupdate.
  - rewrite store_update_path_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + destruct (value_update_path v path v_new) as [v' |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_remove_non_param_same_frame :
  forall ps s_param frame x,
    store_param_prefix ps s_param frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names frame) ->
    store_param_prefix ps (store_remove x s_param) frame.
Proof.
  intros ps s_param frame x Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hnotin_param Hnotin_frame.
  - rewrite store_remove_not_in_names; [constructor | exact Hnotin_frame].
  - simpl in Hnotin_param.
    simpl. destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin_param. left. reflexivity.
    + constructor. apply IH.
      * intros Hin. apply Hnotin_param. right. exact Hin.
      * exact Hnotin_frame.
Qed.

Lemma store_frame_scope_update_state :
  forall ps Σ s_param frame x f s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_state x f s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x f s' HinΣ Hfresh Hscope.
  revert x f s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x f s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_state_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_state x f s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2.
      * exact Hnotin.
      * exact Hin_se.
      * eapply IH.
        -- exact Hfresh.
        -- exact HinΣ.
        -- exact Htail.
Qed.

Lemma store_frame_scope_mark_used :
  forall ps Σ s_param frame x,
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_frame_scope ps Σ (store_mark_used x s_param) frame.
Proof.
  intros ps Σ s_param frame x HinΣ Hfresh Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_mark_used_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
  - simpl.
    destruct (ident_eqb x (se_name se)).
    + econstructor; eassumption.
    + econstructor 2.
      * exact Hnotin.
      * exact Hin_se.
      * exact (IH Hfresh).
Qed.

Lemma store_frame_scope_update_val :
  forall ps Σ s_param frame x v_new s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_val x v_new s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x v_new s' HinΣ Hfresh Hscope.
  revert x v_new s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x v_new s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_val_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_val x v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2; try eassumption.
      eapply IH; eassumption.
Qed.

Lemma store_frame_scope_update_path :
  forall ps Σ s_param frame x path v_new s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_path x path v_new s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path v_new s' HinΣ Hfresh Hscope.
  revert x path v_new s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x path v_new s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_path_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + destruct (value_update_path (se_val se) path v_new) as [v' |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2; try eassumption.
      eapply IH; eassumption.
Qed.

Lemma store_frame_scope_restore_path :
  forall ps Σ s_param frame x path s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_restore_path x path s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path s' HinΣ Hfresh Hscope Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_frame_scope_update_state; eassumption.
Qed.

Lemma store_frame_scope_consume_path :
  forall ps Σ s_param frame x path s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_consume_path x path s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path s' HinΣ Hfresh Hscope Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_frame_scope_update_state; eassumption.
Qed.

Lemma store_frame_scope_remove_non_param :
  forall ps Σ s_param frame x,
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_frame_scope ps Σ (store_remove x s_param) frame.
Proof.
  intros ps Σ s_param frame x HinΣ Hfresh Hscope Hnotin.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_remove_non_param_same_frame.
    + exact Hprefix.
    + exact Hnotin.
    + apply Hfresh. exact HinΣ.
  - simpl. destruct (ident_eqb x (se_name se)) eqn:Heq.
    + exact Hscope_tail.
    + econstructor 2.
      * exact Hse_notin.
      * exact Hin_se.
      * apply IH. exact Hfresh.
Qed.

Lemma store_frame_scope_remove_context_absent :
  forall ps Σ s frame x,
    ~ In x (store_names s) ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps (sctx_remove x Σ) s frame.
Proof.
  intros ps Σ s frame x Hnotin Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor. exact Hprefix.
  - simpl in Hnotin.
    econstructor 2.
    + exact Hse_notin.
    + apply ctx_names_remove_preserve_neq.
      * intros Heq. subst x. apply Hnotin. left. reflexivity.
      * exact Hin_se.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_frame_scope_remove_non_param_sctx_remove :
  forall ps Σ s frame x,
    In x (ctx_names Σ) ->
    store_no_shadow s ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_frame_scope ps (sctx_remove x Σ) (store_remove x s) frame.
Proof.
  intros ps Σ s frame x HinΣ Hshadow Hfresh Hscope Hnotin.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_remove_non_param_same_frame.
    + exact Hprefix.
    + exact Hnotin.
    + apply Hfresh. exact HinΣ.
  - simpl in Hshadow.
    inversion Hshadow as [| ? ? Hhead_notin Htail_shadow]; subst.
    simpl. destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply store_frame_scope_remove_context_absent.
      * apply ident_eqb_eq in Heq. subst x. exact Hhead_notin.
      * exact Hscope_tail.
    + econstructor 2.
      * exact Hse_notin.
      * apply ctx_names_remove_preserve_neq.
        -- apply ident_eqb_neq in Heq. exact Heq.
        -- exact Hin_se.
      * apply IH.
        -- exact Htail_shadow.
        -- exact Hfresh.
Qed.

Lemma store_frame_scope_bind_params_non_params_names :
  forall ps_keep ps_store ps_ctx vs Σ s frame,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    Datatypes.length vs = Datatypes.length ps_store ->
    (forall x,
      In x (ctx_names (params_ctx ps_store)) ->
      ~ In x (ctx_names (params_ctx ps_keep))) ->
    store_frame_scope ps_keep Σ s frame ->
    store_frame_scope ps_keep (sctx_add_params ps_ctx Σ)
      (bind_params ps_store vs s) frame.
Proof.
  induction ps_store as [| p_store ps_store IH];
    intros ps_ctx vs Σ s frame Hnames Hlen Hdisjoint Hscope;
    destruct ps_ctx as [| p_ctx ps_ctx]; simpl in Hnames; try discriminate.
  - destruct vs; simpl in Hlen; try discriminate. simpl. exact Hscope.
  - destruct vs as [| v vs']; simpl.
    + simpl in Hlen. discriminate.
      + inversion Hnames as [[Hhead Htail]].
      simpl in Hlen. inversion Hlen as [Hlen_tail].
      eapply store_frame_scope_add_weaken.
      * apply Hdisjoint. simpl. left. reflexivity.
      * simpl. rewrite Hhead. left. reflexivity.
      * intros y Hy. simpl. right. exact Hy.
      * apply IH.
        -- exact Htail.
        -- exact Hlen_tail.
        -- intros x Hin Hkeep.
           apply (Hdisjoint x); [simpl; right; exact Hin | exact Hkeep].
        -- exact Hscope.
Qed.

Lemma store_frame_static_fresh_add_params :
  forall ps Σ frame,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      ~ In x (store_names frame)) ->
    store_frame_static_fresh Σ frame ->
    store_frame_static_fresh (sctx_add_params ps Σ) frame.
Proof.
  induction ps as [| p ps IH]; intros Σ frame Hfresh_params Hfresh; simpl.
  - exact Hfresh.
  - apply store_frame_static_fresh_add.
    + apply IH.
      * intros x Hin. apply Hfresh_params. simpl. right. exact Hin.
      * exact Hfresh.
    + apply Hfresh_params. simpl. left. reflexivity.
Qed.

Lemma store_frame_static_fresh_remove_params :
  forall ps Σ frame,
    store_frame_static_fresh Σ frame ->
    store_frame_static_fresh (sctx_remove_params ps Σ) frame.
Proof.
  induction ps as [| p ps IH]; intros Σ frame Hfresh; simpl.
  - exact Hfresh.
  - apply IH. apply store_frame_static_fresh_remove. exact Hfresh.
Qed.

Lemma store_frame_scope_remove_non_param_sctx_remove_frame_fresh :
  forall ps Σ s frame x,
    store_no_shadow s ->
    ~ In x (store_names frame) ->
    store_frame_scope ps Σ s frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_frame_scope ps (sctx_remove x Σ) (store_remove x s) frame.
Proof.
  intros ps Σ s frame x Hshadow Hnot_frame Hscope Hnotin.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_remove_non_param_same_frame; eassumption.
  - simpl in Hshadow.
    inversion Hshadow as [| ? ? Hhead_notin Htail_shadow]; subst.
    simpl. destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply store_frame_scope_remove_context_absent.
      * apply ident_eqb_eq in Heq. subst x. exact Hhead_notin.
      * exact Hscope_tail.
    + econstructor 2.
      * exact Hse_notin.
      * apply ctx_names_remove_preserve_neq.
        -- apply ident_eqb_neq in Heq. exact Heq.
        -- exact Hin_se.
      * apply IH.
        -- exact Htail_shadow.
        -- exact Hnot_frame.
Qed.

Lemma store_frame_scope_remove_params_non_params_names :
  forall ps_keep ps_store ps_ctx Σ s frame,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    store_no_shadow s ->
    (forall x,
      In x (ctx_names (params_ctx ps_store)) ->
      ~ In x (store_names frame)) ->
    (forall x,
      In x (ctx_names (params_ctx ps_store)) ->
      ~ In x (ctx_names (params_ctx ps_keep))) ->
    store_frame_scope ps_keep Σ s frame ->
    store_frame_scope ps_keep (sctx_remove_params ps_ctx Σ)
      (store_remove_params ps_store s) frame.
Proof.
  induction ps_store as [| p_store ps_store IH];
    intros ps_ctx Σ s frame Hnames Hshadow Hnot_frame Hdisjoint Hscope;
    destruct ps_ctx as [| p_ctx ps_ctx]; simpl in Hnames; try discriminate.
  - simpl. exact Hscope.
  - inversion Hnames as [[Hhead Htail]].
    simpl.
    rewrite <- Hhead.
    apply IH.
    + exact Htail.
    + apply store_no_shadow_remove. exact Hshadow.
    + intros x Hin.
      apply Hnot_frame. simpl. right. exact Hin.
    + intros x Hin Hkeep.
      apply (Hdisjoint x); [simpl; right; exact Hin | exact Hkeep].
    + eapply store_frame_scope_remove_non_param_sctx_remove_frame_fresh.
      * exact Hshadow.
      * apply Hnot_frame. simpl. left. reflexivity.
      * exact Hscope.
      * apply Hdisjoint. simpl. left. reflexivity.
Qed.


Lemma store_param_prefix_lookup_param_or_frame :
  forall ps s_param frame x se,
    store_param_prefix ps s_param frame ->
    store_lookup x s_param = Some se ->
    In x (ctx_names (params_ctx ps)) \/
    store_lookup x frame = Some se.
Proof.
  intros ps s_param frame x se Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hlookup.
  - right. exact Hlookup.
  - simpl in Hlookup.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      left. simpl. left. reflexivity.
    + destruct (IH Hlookup) as [Hin | Hframe].
      * left. simpl. right. exact Hin.
      * right. exact Hframe.
Qed.

Lemma store_frame_scope_lookup_absent_in_frame :
  forall ps Σ s frame x,
    store_frame_scope ps Σ s frame ->
    store_lookup x s = None ->
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names frame).
Proof.
  intros ps Σ s frame x Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin _ Hscope_tail IH];
    intros Hlookup Hnotparam.
  - intros Hin_frame.
    pose proof (store_lookup_none_not_in_names x s_param Hlookup)
      as Hnotin_s_param.
    apply Hnotin_s_param.
    rewrite (store_names_store_param_prefix ps s_param frame Hprefix).
    apply in_or_app. right. exact Hin_frame.
  - simpl in Hlookup.
    destruct (ident_eqb x (se_name se)); try discriminate.
    eapply IH; eassumption.
Qed.


Lemma sctx_path_available_success :
  forall Σ x path,
    sctx_path_available Σ x path = infer_ok tt ->
    exists T st,
      sctx_lookup x Σ = Some (T, st) /\
      binding_available_b st path = true.
Proof.
  intros Σ x path Havailable.
  unfold sctx_path_available in Havailable.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b st path) eqn:Hbinding; try discriminate.
  inversion Havailable; subst.
  exists T, st. split.
  - reflexivity.
  - exact Hbinding.
Qed.


Theorem eval_preserves_frame_scope_roots_ready_mutual :
  frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame).
Proof.
  assert (Hframe : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
          ps frame,
        provenance_ready_expr e ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        root_env_covers_params ps R ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        store_frame_scope ps Σ s frame ->
        store_frame_static_fresh Σ frame ->
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame) /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
          ps frame,
        provenance_ready_args args ->
        typed_args_roots env Ω n R Σ args params Σ' R' roots ->
        root_env_covers_params ps R ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        store_frame_scope ps Σ s frame ->
        store_frame_static_fresh Σ frame ->
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame) /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
          ps frame,
        provenance_ready_fields fields ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        root_env_covers_params ps R ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        store_frame_scope ps Σ s frame ->
        store_frame_static_fresh Σ frame ->
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame)).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s i Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s f Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s b Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst;
      repeat split; try exact Hcover; try exact Hscope; try exact Hfresh;
      try (eapply store_frame_scope_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hscope ]);
      try (eapply store_frame_static_fresh_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hfresh ]).
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      ps frame _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst.
    + destruct (typed_place_direct_lookup env _ (PVar x) _ x []
                  ltac:(eassumption) eq_refl)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_used :
        store_frame_scope ps _ (store_mark_used x s) frame)
        by (eapply store_frame_scope_mark_used;
            [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
            | exact Hfresh | exact Hscope ]).
      repeat split; assumption.
    + destruct (typed_place_direct_lookup env _ (PVar x) _ x []
                  ltac:(eassumption) eq_refl)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_used :
        store_frame_scope ps _ (store_mark_used x s) frame)
        by (eapply store_frame_scope_mark_used;
            [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
            | exact Hfresh | exact Hscope ]).
      repeat split; try assumption.
      * eapply store_frame_scope_same_bindings.
        -- match goal with
           | Hconsume_ctx : sctx_consume_path _ _ _ = infer_ok _ |- _ =>
               eapply sctx_consume_path_same_bindings; exact Hconsume_ctx
           end.
        -- exact Hscope_used.
      * eapply store_frame_static_fresh_same_bindings.
        -- match goal with
           | Hconsume_ctx : sctx_consume_path _ _ _ = infer_ok _ |- _ =>
               eapply sctx_consume_path_same_bindings; exact Hconsume_ctx
           end.
        -- exact Hfresh.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      ps frame Hready Htyped Hcover _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst;
      repeat split; try exact Hcover; try exact Hscope; try exact Hfresh;
      try (eapply store_frame_scope_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hscope ]);
      try (eapply store_frame_static_fresh_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hfresh ]).
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover
      _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    + destruct (eval_place_matches_place_path s p x_eval path_eval x0 path0
                  Heval_place H3) as [Hx Hpath]; subst x_eval path_eval.
      destruct (typed_place_direct_lookup env Σ' p T x0 path0 H1 H3)
        as [T_root [st [Hlookup_ctx _]]].
      repeat split.
      * exact Hcover.
      * eapply (store_frame_scope_consume_path ps Σ' s frame x0 path0 s').
        -- eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
        -- exact Hfresh.
        -- exact Hscope.
        -- exact Hstore_consume.
      * exact Hfresh.
    + destruct (eval_place_matches_place_path s p x_eval path_eval x0 path0
                  Heval_place H3) as [Hx Hpath]; subst x_eval path_eval.
      destruct (typed_place_direct_lookup env Σ p T x0 path0 H1 H3)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_consume : store_frame_scope ps Σ s' frame).
      { eapply (store_frame_scope_consume_path ps Σ s frame x0 path0 s').
        - eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
        - exact Hfresh.
        - exact Hscope.
        - exact Hstore_consume. }
      repeat split.
      * exact Hcover.
      * eapply store_frame_scope_same_bindings.
        -- eapply sctx_consume_path_same_bindings. exact H4.
        -- exact Hscope_consume.
      * eapply store_frame_static_fresh_same_bindings.
        -- eapply sctx_consume_path_same_bindings. exact H4.
        -- exact Hfresh.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_struct name env = Some ?sdef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst sdef_typed
    end.
    match goal with
    | Hready_fields : provenance_ready_fields fields,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ fields
        (struct_fields sdef) Σ' R' roots |- _ =>
        exact (IHfields Ω n lts args R Σ Σ' R' roots ps frame
                 Hready_fields Htyped_fields Hcover Hroots Hshadow Hrn
                 Hscope Hfresh)
    end.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IHargs Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_enum enum_name env = Some ?edef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst edef_typed
    end.
    match goal with
    | Hvariant_typed : lookup_enum_variant variant_name (enum_variants edef) =
          Some ?vdef_typed |- _ =>
        rewrite Hvariant in Hvariant_typed; inversion Hvariant_typed; subst vdef_typed
    end.
    match goal with
    | Hready_args : provenance_ready_args payloads,
      Htyped_args : typed_args_roots env Ω n R Σ payloads _ Σ' R' ?payload_roots |- _ =>
        exact (IHargs Ω n R Σ _ Σ' R' payload_roots ps frame
                 Hready_args Htyped_args Hcover Hroots Hshadow Hrn
                 Hscope Hfresh)
    end.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1 v1
                Heval1 Ω n R Σ T1 Σ1 R1 roots1 Hready1 Hroots
                Hshadow Hrn H4)
      as [Hroots1 [Hv1_roots [Hshadow1 Hrn1]]].
    destruct (IH1 Ω n R Σ T1 Σ1 R1 roots1 ps frame Hready1 H4
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    pose proof (root_env_covers_params_lookup_none_not_in
                  ps R1 x Hcover1
                  ltac:(match goal with
                    | H : root_env_lookup x R1 = None |- _ => exact H
                    end)) as Hnotin.
    assert (Hlookup_fresh : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hnot_frame : ~ In x (store_names frame))
      by (eapply store_frame_scope_lookup_absent_in_frame; eassumption).
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_ann v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow :
      store_no_shadow (store_add x T_ann v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hscope_add :
      store_frame_scope ps (sctx_add x T_ann m Σ1)
        (store_add x T_ann v1 s1) frame)
      by (eapply store_frame_scope_add_weaken;
          [ exact Hnotin
          | simpl; left; reflexivity
          | intros y Hy; simpl; right; exact Hy
          | exact Hscope1 ]).
    assert (Hfresh_add :
      store_frame_static_fresh (sctx_add x T_ann m Σ1) frame)
      by (eapply store_frame_static_fresh_add; eassumption).
    assert (Htyped_body :
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots).
    { match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
              (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots |- _ =>
          exact H
      end. }
    destruct (proj1 eval_preserves_roots_ready_mutual env
                (store_add x T_ann v1 s1) e2 s2 v2 Heval2
                Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots Hready2
                Hadd_roots Hadd_shadow Hadd_rn Htyped_body)
      as [Hroots2 [_ [Hshadow2 Hrn2]]].
    destruct (IH2 Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots ps frame
                Hready2 Htyped_body
                (root_env_covers_params_add ps R1 x roots1 Hcover1)
                Hadd_roots Hadd_shadow Hadd_rn Hscope_add Hfresh_add)
      as [Hcover2 [Hscope2 Hfresh2]].
    assert (Hin_x_Σ2 : In x (ctx_names Σ2)).
    { pose proof (typed_env_structural_same_bindings env Ω n
                    (sctx_add x T_ann m Σ1) e2 T Σ2
                    (typed_env_roots_structural env Ω n
                      (root_env_add x roots1 R1)
                      (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots
                      Htyped_body))
        as Hsame_body.
      pose proof (sctx_same_bindings_names_alpha
                    (sctx_add x T_ann m Σ1) Σ2 Hsame_body) as Hnames.
      rewrite Hnames. simpl. left. reflexivity. }
    repeat split.
    + eapply root_env_covers_params_remove_non_param; eassumption.
    + eapply store_frame_scope_remove_non_param_sctx_remove; eassumption.
    + apply store_frame_static_fresh_remove. exact Hfresh2.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        exact (IH Ω n R Σ T_e Σ' R' roots_e ps frame Hready_e
                 Htyped_e Hcover Hroots Hshadow Hrn Hscope Hfresh)
    end.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    destruct (IHnew Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption)
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (sctx_path_available_success _ x [] ltac:(eassumption))
      as [T_root [st [Hlookup_ctx _]]].
    assert (Hscope2 : store_frame_scope ps _ s2 frame)
      by (eapply store_frame_scope_update_val;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope1 | exact Hupdate ]).
    assert (Hscope3 : store_frame_scope ps _ s3 frame)
      by (eapply store_frame_scope_restore_path;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope2 | exact Hrestore ]).
    repeat split.
    + apply root_env_covers_params_update. exact Hcover1.
    + eapply store_frame_scope_same_bindings.
      * eapply sctx_restore_path_same_bindings. eassumption.
      * exact Hscope3.
    + eapply store_frame_static_fresh_same_bindings.
      * eapply sctx_restore_path_same_bindings. eassumption.
      * exact Hfresh1.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    destruct (IHnew Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption)
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (sctx_path_available_success _ x [] ltac:(eassumption))
      as [T_root [st [Hlookup_ctx _]]].
    repeat split.
    + apply root_env_covers_params_update. exact Hcover1.
    + eapply store_frame_scope_update_val.
      * eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
      * exact Hfresh1.
      * exact Hscope1.
      * exact Hupdate.
    + exact Hfresh1.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new,
      Havailable : sctx_path_available ?Σ1 x path = infer_ok tt,
      Hrestore_ctx : sctx_restore_path ?Σ1 x path = infer_ok Σ' |- _ =>
        destruct (eval_place_matches_place_path s p x_eval path_eval x path
                    Heval_place H) as [Hx_eval Hpath_eval];
        subst x_eval path_eval;
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ1 x path Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        assert (Hscope2 : store_frame_scope ps Σ1 s2 frame)
          by (eapply store_frame_scope_update_path;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh1 | exact Hscope1 | exact Hupdate ]);
        assert (Hscope3 : store_frame_scope ps Σ1 s3 frame)
          by (eapply store_frame_scope_restore_path;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh1 | exact Hscope2 | exact Hrestore ]);
        repeat split;
        [ apply root_env_covers_params_update; exact Hcover1
        | eapply store_frame_scope_same_bindings;
          [ eapply sctx_restore_path_same_bindings; exact Hrestore_ctx
          | exact Hscope3 ]
        | eapply store_frame_static_fresh_same_bindings;
          [ eapply sctx_restore_path_same_bindings; exact Hrestore_ctx
          | exact Hfresh1 ] ]
    end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new,
      Havailable : sctx_path_available Σ' x path = infer_ok tt |- _ =>
        destruct (eval_place_matches_place_path s p x_eval path_eval x path
                    Heval_place H) as [Hx_eval Hpath_eval];
        subst x_eval path_eval;
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ' x path Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        repeat split;
        [ apply root_env_covers_params_update; exact Hcover1
        | eapply store_frame_scope_update_path;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope1 | exact Hupdate ]
        | exact Hfresh1 ]
    end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; repeat split; assumption.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame Hready _ _ _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Heval_r; subst.
    inversion Htyped; subst; try solve [repeat split; assumption].
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1
        ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 ?Σ1 e2 ?T2 ?Σ2
        ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hshadow Hrn Htyped_cond)
          as [Hroots1 [_ [Hshadow1 Hrn1]]];
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                    Hready_cond Htyped_cond Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2 ps frame
                    Hready_then Htyped_then Hcover1 Hroots1 Hshadow1 Hrn1
                    Hscope1 Hfresh1)
          as [Hcover2 [Hscope2 Hfresh2]];
        repeat split;
        [ exact Hcover2
        | eapply store_frame_scope_same_bindings;
          [ eapply ctx_merge_same_bindings_left; exact Hmerge
          | exact Hscope2 ]
        | eapply store_frame_static_fresh_same_bindings;
          [ eapply ctx_merge_same_bindings_left; exact Hmerge
          | exact Hfresh2 ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                roots_cond Hready1 Hroots Hshadow Hrn H2)
      as [Hroots1 [_ [Hshadow1 Hrn1]]].
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 H2 Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3 ps frame
                Hready3 H5 Hcover1 Hroots1 Hshadow1 Hrn1
                Hscope1 Hfresh1)
      as [Hcover3 [Hscope3 Hfresh3]].
    assert (Hsame_then_else : sctx_same_bindings Σ2 Σ3).
    { eapply sctx_same_bindings_trans.
      - apply sctx_same_bindings_sym.
        eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact H4.
      - eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact H5. }
    repeat split.
    + eapply root_env_covers_params_equiv.
      * apply root_env_equiv_sym. exact H14.
      * exact Hcover3.
    + eapply store_frame_scope_same_bindings.
      * eapply ctx_merge_same_bindings_right.
        -- exact Hsame_then_else.
        -- exact H13.
      * exact Hscope3.
	    + eapply store_frame_static_fresh_same_bindings.
	      * eapply ctx_merge_same_bindings_right.
	        -- exact Hsame_then_else.
	        -- exact H13.
	      * exact Hfresh3.
  - intros s s_scrut s_branch s' scrut branches enum_name variant_name
      lts_val args_val values edef_runtime vdef_runtime binders ps_payload
      e_branch v
      Heval_scrut IHscrut Hlookup_enum_runtime Hlookup_variant_runtime
      Hlookup_binders Hpayload_runtime Hvalues_len Hlookup
      Heval_branch IHbranch Hremove_params
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    dependent destruction Htyped.
	    destruct (proj1 eval_preserves_roots_ready_mutual env s scrut s_scrut
	                (VEnum enum_name variant_name lts_val args_val values)
	                Heval_scrut Ω n R Σ T_scrut Σ1 R1 roots_scrut Hready
	                Hroots Hshadow Hrn Htyped1)
	      as [Hroots1 [Hv_scrut [Hshadow1 Hrn1]]].
    destruct (IHscrut Ω n R Σ T_scrut Σ1 R1 roots_scrut ps frame
                Hready Htyped1 Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    assert (Hready_branch : provenance_ready_expr e_branch).
    { unfold lookup_match_branch in Hlookup.
      eapply provenance_ready_match_branches_lookup; eassumption. }
    unfold lookup_match_branch in Hlookup.
    assert (Hlookup_branch :
      lookup_expr_branch variant_name branches = Some e_branch).
    { rewrite lookup_expr_branch_lookup_expr_field. exact Hlookup. }
    assert (Hvariant_known :
      exists vdef, lookup_enum_variant variant_name (enum_variants edef) =
        Some vdef).
    { eapply first_unknown_variant_branch_lookup_some; eassumption. }
	    rewrite H6 in Hvariant_known. simpl in Hvariant_known.
	    assert (Hsame_head_final :
	      sctx_same_bindings (sctx_remove_params ps_head Σ_head_payload)
	        (sctx_of_ctx Γ_out)).
	    { eapply ctx_merge_many_same_bindings_left.
	      match goal with
	      | Hmerge : ctx_merge_many
	          (ctx_of_sctx (sctx_remove_params ps_head Σ_head_payload))
	          (map ctx_of_sctx Σ_tail) = Some Γ_out |- _ =>
	          exact Hmerge
	      end. }
	    destruct (String.eqb variant_name (enum_variant_name v_head))
	      eqn:Hvariant_head.
	    + apply String.eqb_eq in Hvariant_head. subst variant_name.
	      match goal with
	      | Htyped_head : typed_env_roots _ _ _ _ _ ?e_head _ _ _ _,
	        Hbranch_head : lookup_expr_branch (enum_variant_name v_head) branches =
	          Some ?e_head |- _ =>
	          rewrite Hbranch_head in Hlookup_branch
	      end.
	      inversion Hlookup_branch; subst.
		      assert (Hnames_payload : ctx_names (params_ctx ps_payload) =
		        ctx_names (params_ctx ps_head)).
		      { assert (Hnames_runtime :
		          ctx_names (params_ctx ps_payload) = binders).
		        { eapply match_payload_params_opt_names.
		          exact Hpayload_runtime. }
		        assert (Hhead :
		          exists binders_head,
		            lookup_expr_branch_binders (enum_variant_name v_head) branches =
		              Some binders_head /\
		            ctx_names (params_ctx ps_head) = binders_head).
		        { match goal with
		          | Hlookup_head : lookup_expr_branch_binders
		              (enum_variant_name v_head) branches = Some ?binders_head,
		            Hparams_head : match_payload_params ?binders_head ?lts_head
		              ?args_head v_head = infer_ok ps_head |- _ =>
		              exists binders_head; split;
		              [ exact Hlookup_head
		              | eapply match_payload_params_names; exact Hparams_head ]
		          end. }
		        destruct Hhead as [binders_head0 [Hlookup_head Hnames_head]].
		        rewrite Hnames_runtime, Hnames_head.
		        rewrite Hlookup_binders in Hlookup_head.
		        inversion Hlookup_head. reflexivity. }
	      assert (Hnone_payload :
	        root_env_lookup_params_none_b ps_payload R1 = true).
	      { eapply root_env_lookup_params_none_b_names.
	        - symmetry. exact Hnames_payload.
	        - match goal with
	          | Hnone_head : root_env_lookup_params_none_b ps_head R1 = true
	            |- _ => exact Hnone_head
	          end. }
	      pose proof (root_env_lookup_params_none_b_disjoint_covers
	        ps_payload ps R1 Hnone_payload Hcover1) as Hdisjoint_payload.
	      pose proof (value_roots_within_enum_payloads roots_scrut enum_name
	        (enum_variant_name v_head) lts_val args_val values Hv_scrut)
	        as Hvalues_roots.
	      assert (Hroots_payload :
	        store_roots_within
	          (root_env_add_params_roots_same ps_head roots_scrut R1)
	          (bind_params ps_payload values s_scrut)).
	      { eapply store_roots_within_bind_params_roots_same_names.
	        - exact Hnames_payload.
	        - eassumption.
	        - eassumption.
	        - exact Hroots1.
	        - exact Hvalues_roots.
	        - exact Hvalues_len. }
	      assert (Hshadow_payload :
	        store_no_shadow (bind_params ps_payload values s_scrut)).
	      { eapply bind_params_store_no_shadow_names.
	        - eapply params_names_nodup_b_sound.
	          eapply params_names_nodup_b_names.
	          + symmetry. exact Hnames_payload.
	          + eassumption.
	        - eapply store_roots_within_params_fresh_in_store.
	          + exact Hnone_payload.
	          + exact Hroots1.
	        - exact Hvalues_len.
	        - exact Hshadow1. }
	      assert (Hrn_payload :
	        root_env_no_shadow
	          (root_env_add_params_roots_same ps_head roots_scrut R1)).
	      { eapply root_env_add_params_roots_same_no_shadow; eauto. }
	      assert (Hcover_payload :
	        root_env_covers_params ps
	          (root_env_add_params_roots_same ps_head roots_scrut R1)).
	      { apply root_env_covers_params_add_params_roots_same_preserve.
	        exact Hcover1. }
	      assert (Hscope_payload :
	        store_frame_scope ps (sctx_add_params ps_head Σ1)
	          (bind_params ps_payload values s_scrut) frame).
	      { eapply store_frame_scope_bind_params_non_params_names.
	        - exact Hnames_payload.
	        - exact Hvalues_len.
	        - exact Hdisjoint_payload.
	        - exact Hscope1. }
	      assert (Hnot_frame_payload :
	        forall x,
	          In x (ctx_names (params_ctx ps_head)) ->
	          ~ In x (store_names frame)).
	      { intros x Hin_head.
	        assert (Hin_payload : In x (ctx_names (params_ctx ps_payload))).
	        { rewrite Hnames_payload. exact Hin_head. }
	        assert (Hlookup_none : root_env_lookup x R1 = None).
	        { apply root_env_lookup_not_in_names.
	          eapply root_env_lookup_params_none_b_not_in; eassumption. }
	        assert (Hstore_none : store_lookup x s_scrut = None)
	          by (eapply store_roots_within_lookup_none; eassumption).
	        eapply store_frame_scope_lookup_absent_in_frame.
	        - exact Hscope1.
	        - exact Hstore_none.
	        - apply Hdisjoint_payload. exact Hin_payload. }
	      assert (Hfresh_payload :
	        store_frame_static_fresh (sctx_add_params ps_head Σ1) frame).
	      { apply store_frame_static_fresh_add_params; assumption. }
	      destruct (IHbranch Ω n
	                  (root_env_add_params_roots_same ps_head roots_scrut R1)
	                  (sctx_add_params ps_head Σ1)
	                  T_head Σ_head_payload R_head_payload roots_head ps frame
	                  Hready_branch Htyped2 Hcover_payload Hroots_payload
	                  Hshadow_payload Hrn_payload Hscope_payload Hfresh_payload)
	        as [Hcover_branch [Hscope_branch Hfresh_branch]].
	      destruct (proj1 eval_preserves_roots_ready_mutual env
	                  (bind_params ps_payload values s_scrut) e_branch
	                  s_branch v Heval_branch Ω n
	                  (root_env_add_params_roots_same ps_head roots_scrut R1)
	                  (sctx_add_params ps_head Σ1)
	                  T_head Σ_head_payload R_head_payload roots_head
	                  Hready_branch Hroots_payload Hshadow_payload
	                  Hrn_payload Htyped2)
	        as [_ [_ [Hshadow_branch _]]].
	      repeat split.
	      * eapply root_env_covers_params_remove_match_params_non_params.
	        -- intros x Hin. apply Hdisjoint_payload.
	           rewrite Hnames_payload. exact Hin.
	        -- exact Hcover_branch.
	      * eapply store_frame_scope_same_bindings.
	        -- exact Hsame_head_final.
	        -- eapply store_frame_scope_remove_params_non_params_names.
	           ++ exact Hnames_payload.
	           ++ exact Hshadow_branch.
	           ++ intros x Hin.
	              apply Hnot_frame_payload.
	              rewrite <- Hnames_payload. exact Hin.
	           ++ exact Hdisjoint_payload.
	           ++ exact Hscope_branch.
	      * eapply store_frame_static_fresh_same_bindings.
	        -- exact Hsame_head_final.
	        -- apply store_frame_static_fresh_remove_params.
	           exact Hfresh_branch.
	    + destruct Hvariant_known as [vdef_tail Hvariant_tail].
	      destruct (typed_match_tail_roots_lookup_frame_ready env Ω n lts args
		                  R1 roots_scrut Σ1 branches v_tail (ty_core T_head)
		                  (root_env_remove_match_params ps_head R_head_payload)
		                  Σ_tail Ts_tail roots_tail
		                  variant_name vdef_tail e_branch
		                  ltac:(match goal with
		                    | Htail : typed_match_tail_roots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
		                        exact Htail
		                    end)
		                  Hvariant_tail
		                  Hlookup_branch)
	        as [T_branch [Σ_branch_payload [R_branch_payload [Σ_branch
		             [R_branch [roots_branch [ps_branch [binders_branch
		             [R_payload_branch [HRpayload [Hnodup_branch_params
		             [Hroot_none_branch [Hbinders_branch
		             [Hparams_branch [Htyped_branch [Hremove_branch
		             [Hctx_remove_branch [Hcore_branch
	             [Hequiv_branch [HinΣ_branch Hin_roots]]]]]]]]]]]]]]]]]]]].
	      assert (Hbinders_same : binders_branch = binders).
	      { rewrite Hlookup_binders in Hbinders_branch.
	        inversion Hbinders_branch. reflexivity. }
	      subst binders_branch.
	      assert (Hnames_payload : ctx_names (params_ctx ps_payload) =
	        ctx_names (params_ctx ps_branch)).
	      { rewrite (match_payload_params_opt_names binders lts_val args_val
	          vdef_runtime ps_payload Hpayload_runtime).
	        rewrite (match_payload_params_opt_names binders lts args vdef_tail
	          ps_branch Hparams_branch).
	        reflexivity. }
	      assert (Hnone_payload :
	        root_env_lookup_params_none_b ps_payload R1 = true).
	      { eapply root_env_lookup_params_none_b_names.
	        - symmetry. exact Hnames_payload.
	        - exact Hroot_none_branch. }
	      pose proof (root_env_lookup_params_none_b_disjoint_covers
	        ps_payload ps R1 Hnone_payload Hcover1) as Hdisjoint_payload.
	      pose proof (value_roots_within_enum_payloads roots_scrut enum_name
	        variant_name lts_val args_val values Hv_scrut) as Hvalues_roots.
	      assert (Hroots_payload : store_roots_within R_payload_branch
	          (bind_params ps_payload values s_scrut)).
	      { subst R_payload_branch.
	        eapply store_roots_within_bind_params_roots_same_names.
	        - exact Hnames_payload.
	        - eassumption.
	        - eassumption.
	        - exact Hroots1.
	        - exact Hvalues_roots.
	        - exact Hvalues_len. }
	      assert (Hshadow_payload :
	        store_no_shadow (bind_params ps_payload values s_scrut)).
	      { eapply bind_params_store_no_shadow_names.
	        - eapply params_names_nodup_b_sound.
	          eapply params_names_nodup_b_names.
	          + symmetry. exact Hnames_payload.
	          + eassumption.
	        - eapply store_roots_within_params_fresh_in_store.
	          + exact Hnone_payload.
	          + exact Hroots1.
	        - exact Hvalues_len.
	        - exact Hshadow1. }
	      assert (Hrn_payload : root_env_no_shadow R_payload_branch).
	      { subst R_payload_branch.
	        eapply root_env_add_params_roots_same_no_shadow; eauto. }
	      assert (Hcover_payload : root_env_covers_params ps R_payload_branch).
	      { subst R_payload_branch.
	        apply root_env_covers_params_add_params_roots_same_preserve.
	        exact Hcover1. }
	      assert (Hscope_payload :
	        store_frame_scope ps (sctx_add_params ps_branch Σ1)
	          (bind_params ps_payload values s_scrut) frame).
	      { eapply store_frame_scope_bind_params_non_params_names.
	        - exact Hnames_payload.
	        - exact Hvalues_len.
	        - exact Hdisjoint_payload.
	        - exact Hscope1. }
	      assert (Hnot_frame_payload :
	        forall x,
	          In x (ctx_names (params_ctx ps_branch)) ->
	          ~ In x (store_names frame)).
	      { intros x Hin_branch.
	        assert (Hin_payload : In x (ctx_names (params_ctx ps_payload))).
	        { rewrite Hnames_payload. exact Hin_branch. }
	        assert (Hlookup_none : root_env_lookup x R1 = None).
	        { apply root_env_lookup_not_in_names.
	          eapply root_env_lookup_params_none_b_not_in; eassumption. }
	        assert (Hstore_none : store_lookup x s_scrut = None)
	          by (eapply store_roots_within_lookup_none; eassumption).
	        eapply store_frame_scope_lookup_absent_in_frame.
	        - exact Hscope1.
	        - exact Hstore_none.
	        - apply Hdisjoint_payload. exact Hin_payload. }
	      assert (Hfresh_payload :
	        store_frame_static_fresh (sctx_add_params ps_branch Σ1) frame).
	      { apply store_frame_static_fresh_add_params; assumption. }
	      destruct (IHbranch Ω n R_payload_branch (sctx_add_params ps_branch Σ1)
	                  T_branch Σ_branch_payload R_branch_payload roots_branch
	                  ps frame Hready_branch Htyped_branch Hcover_payload
	                  Hroots_payload Hshadow_payload Hrn_payload Hscope_payload
	                  Hfresh_payload)
	        as [Hcover_branch [Hscope_branch Hfresh_branch]].
	      destruct (proj1 eval_preserves_roots_ready_mutual env
	                  (bind_params ps_payload values s_scrut) e_branch
	                  s_branch v Heval_branch Ω n R_payload_branch
	                  (sctx_add_params ps_branch Σ1)
	                  T_branch Σ_branch_payload R_branch_payload roots_branch
	                  Hready_branch Hroots_payload Hshadow_payload
	                  Hrn_payload Htyped_branch)
	        as [_ [_ [Hshadow_branch _]]].
	      assert (Hsame_1_head :
	        sctx_same_bindings Σ1
	          (sctx_remove_params ps_head Σ_head_payload)).
	      { apply sctx_same_bindings_remove_added_params.
	        eapply typed_env_structural_same_bindings.
	        eapply typed_env_roots_structural. exact Htyped2. }
	      assert (Hsame_branch_1 : sctx_same_bindings Σ1 Σ_branch).
	      { rewrite Hctx_remove_branch.
	        apply sctx_same_bindings_remove_added_params.
	        eapply typed_env_structural_same_bindings.
	        eapply typed_env_roots_structural. exact Htyped_branch. }
	      assert (Hsame_branch_final :
	        sctx_same_bindings Σ_branch (sctx_of_ctx Γ_out)).
	      { eapply sctx_same_bindings_trans.
	        - apply sctx_same_bindings_sym. exact Hsame_branch_1.
	        - eapply sctx_same_bindings_trans.
	          + exact Hsame_1_head.
	          + exact Hsame_head_final. }
	      repeat split.
	      * eapply root_env_covers_params_equiv.
	        -- exact Hequiv_branch.
	        -- rewrite Hremove_branch.
	           eapply root_env_covers_params_remove_match_params_non_params.
	           ++ intros x Hin. apply Hdisjoint_payload.
	              rewrite Hnames_payload. exact Hin.
	           ++ exact Hcover_branch.
	      * eapply store_frame_scope_same_bindings.
	        -- exact Hsame_branch_final.
	        -- rewrite Hremove_params.
	           rewrite Hctx_remove_branch.
	           eapply store_frame_scope_remove_params_non_params_names.
	           ++ exact Hnames_payload.
	           ++ exact Hshadow_branch.
	           ++ intros x Hin.
	              apply Hnot_frame_payload.
	              rewrite <- Hnames_payload. exact Hin.
	           ++ exact Hdisjoint_payload.
	           ++ exact Hscope_branch.
	      * eapply store_frame_static_fresh_same_bindings.
	        -- exact Hsame_branch_final.
	        -- rewrite Hctx_remove_branch.
	           apply store_frame_static_fresh_remove_params.
	           exact Hfresh_branch.
		  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
		      roots ps frame Hready _ _ _ _ _ _ _.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args0 vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ
	      T Σ' R' roots ps frame Hready _ _ _ _ _ _ _.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
	      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Ω n R Σ T Σ' R' roots ps frame Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ params Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ params Σ' R' roots ps frame Hready Htyped Hcover
      Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    dependent destruction Htyped.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?params_rest
        ?Σ2 ?R2 ?roots_rest |- _ =>
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e Hready_e
                    Hroots Hshadow Hrn Htyped_e)
          as [Hroots1 [_ [Hshadow1 Hrn1]]];
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e ps frame Hready_e
                    Htyped_e Hcover Hroots Hshadow Hrn Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        exact (IHrest Ω n R1 Σ1 params_rest Σ2 R2 roots_rest ps frame
                 Hready_rest Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                 Hscope1 Hfresh1)
    end.
  - intros s Ω n lts args0 R Σ Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    destruct (typed_fields_roots_cons_inv_ts env Ω n lts args0 R Σ
                fields f rest Σ' R' roots Htyped)
      as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
    rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
    rewrite Hlookup_typed in Hlookup_expr.
    inversion Hlookup_expr; subst e_field.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                Hready_field Hroots Hshadow Hrn Htyped_field)
      as [Hroots1 [_ [Hshadow1 Hrn1]]].
    destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                Hready_field Htyped_field Hcover Hroots Hshadow Hrn
                Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    exact (IHrest Ω n lts args0 R1 Σ1 Σ' R' roots_rest ps frame
             Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
             Hscope1 Hfresh1).
  }
  assert (Hexpr : frame_scope_roots_ready_expr_preservation).
  { intros env s e s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e s' v
                Heval Ω n R Σ T Σ' R' roots Hready Hroots Hshadow
                Hrn Htyped)
      as [Hroots' [_ [Hshadow' Hrn']]].
    destruct (Hframe env) as [Hframe_expr _].
    destruct (Hframe_expr s e s' v Heval Ω n R Σ T Σ' R' roots
                ps frame Hready Htyped Hcover Hroots Hshadow Hrn
                Hscope Hfresh)
      as [Hcover' [Hscope' Hfresh']].
    repeat split; assumption. }
  split.
  - exact Hexpr.
  - exact (eval_preserves_frame_scope_roots_ready_args_fields_from_expr Hexpr).
Qed.
