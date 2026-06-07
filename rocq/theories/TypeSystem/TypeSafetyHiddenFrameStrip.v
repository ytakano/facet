From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyHiddenFrameBase.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma fields_local_store_names_in_expr :
  forall fname e fields x,
    In (fname, e) fields ->
    In x (expr_local_store_names e) ->
    In x (fields_local_store_names fields).
Proof.
  intros fname e fields x Hin Hx.
  induction fields as [| [fname' e'] rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + inversion Hin; subst. apply in_or_app. left. exact Hx.
    + apply in_or_app. right. apply IH. exact Hin.
Qed.

Lemma match_branches_local_store_names_in_expr :
  forall name binders e branches x,
    In (name, binders, e) branches ->
    In x (expr_local_store_names e) ->
    In x (match_branches_local_store_names branches).
Proof.
  intros name binders e branches x Hin Hx.
  induction branches as [| [[name' binders'] e'] rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + inversion Hin; subst. apply in_or_app. right.
      apply in_or_app. left. exact Hx.
    + apply in_or_app. right. apply in_or_app. right.
      apply IH. exact Hin.
Qed.

Scheme hidden_frame_eval_ind' := Induction for eval Sort Prop
with hidden_frame_eval_args_ind' := Induction for eval_args Sort Prop
with hidden_frame_eval_struct_fields_ind' :=
  Induction for eval_struct_fields Sort Prop.

Combined Scheme hidden_frame_eval_eval_args_eval_struct_fields_ind
  from hidden_frame_eval_ind',
       hidden_frame_eval_args_ind',
       hidden_frame_eval_struct_fields_ind'.

Fixpoint args_free_vars_ts (args : list expr) : list ident :=
  match args with
  | [] => []
  | e :: rest => free_vars_expr e ++ args_free_vars_ts rest
  end.

Fixpoint fields_free_vars_ts (fields : list (string * expr)) : list ident :=
  match fields with
  | [] => []
  | (_, e) :: rest => free_vars_expr e ++ fields_free_vars_ts rest
  end.

Fixpoint match_branches_free_vars_ts
    (branches : list (string * list ident * expr)) : list ident :=
  match branches with
  | [] => []
  | (_, _, e) :: rest => free_vars_expr e ++ match_branches_free_vars_ts rest
  end.

Lemma args_free_vars_ts_cons_notin :
  forall x e rest,
    ~ In x (args_free_vars_ts (e :: rest)) ->
    ~ In x (free_vars_expr e) /\ ~ In x (args_free_vars_ts rest).
Proof.
  intros x e rest Hnotin. simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma fields_free_vars_ts_cons_notin :
  forall x name e rest,
    ~ In x (fields_free_vars_ts ((name, e) :: rest)) ->
    ~ In x (free_vars_expr e) /\ ~ In x (fields_free_vars_ts rest).
Proof.
  intros x name e rest Hnotin. simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma args_local_store_names_cons_notin :
  forall x e rest,
    ~ In x (args_local_store_names (e :: rest)) ->
    ~ In x (expr_local_store_names e) /\
    ~ In x (args_local_store_names rest).
Proof.
  intros x e rest Hnotin.
  unfold args_local_store_names in *.
  simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma fields_local_store_names_cons_notin :
  forall x name e rest,
    ~ In x (fields_local_store_names ((name, e) :: rest)) ->
    ~ In x (expr_local_store_names e) /\
    ~ In x (fields_local_store_names rest).
Proof.
  intros x name e rest Hnotin.
  unfold fields_local_store_names in *.
  simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma lookup_expr_field_in :
  forall lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    exists field_name, In (field_name, e) fields.
Proof.
  intros lookup_name fields.
  induction fields as [| [name expr] rest IH]; intros e Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (String.eqb lookup_name name) eqn:Hname.
  - inversion Hlookup; subst. exists name. left. reflexivity.
  - destruct (IH e Hlookup) as [field_name Hin].
    exists field_name. right. exact Hin.
Qed.

Lemma fields_free_vars_ts_in_expr :
  forall field_name e fields x,
    In (field_name, e) fields ->
    In x (free_vars_expr e) ->
    In x (fields_free_vars_ts fields).
Proof.
  intros field_name e fields x Hin Hx.
  induction fields as [| [name expr] rest IH]; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - inversion Hin; subst. apply in_or_app. left. exact Hx.
  - apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma fields_free_vars_ts_lookup_notin :
  forall x lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    ~ In x (fields_free_vars_ts fields) ->
    ~ In x (free_vars_expr e).
Proof.
  intros x lookup_name fields e Hlookup Hnotin Hin.
  destruct (lookup_expr_field_in lookup_name fields e Hlookup)
    as [field_name Hfield].
  apply Hnotin.
  eapply fields_free_vars_ts_in_expr; eassumption.
Qed.

Lemma match_branches_free_vars_ts_in_expr :
  forall name binders e branches x,
    In (name, binders, e) branches ->
    In x (free_vars_expr e) ->
    In x (match_branches_free_vars_ts branches).
Proof.
  intros name binders e branches x Hin Hx.
  induction branches as [| [[name' binders'] e'] rest IH]; simpl in *;
    try contradiction.
  destruct Hin as [Hin | Hin].
  - inversion Hin; subst. apply in_or_app. left. exact Hx.
  - apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma match_branches_free_vars_ts_lookup_notin :
  forall x lookup_name branches e,
    lookup_expr_branch lookup_name branches = Some e ->
    ~ In x (match_branches_free_vars_ts branches) ->
    ~ In x (free_vars_expr e).
Proof.
  intros x lookup_name branches e Hlookup Hnotin Hin.
  destruct (lookup_expr_branch_in_alpha lookup_name branches e Hlookup)
    as [binders Hbranch].
  apply Hnotin.
  eapply match_branches_free_vars_ts_in_expr; eassumption.
Qed.

Lemma fields_local_store_names_lookup_notin :
  forall x lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    ~ In x (fields_local_store_names fields) ->
    ~ In x (expr_local_store_names e).
Proof.
  intros x lookup_name fields e Hlookup Hnotin Hin.
  destruct (lookup_expr_field_in lookup_name fields e Hlookup)
    as [field_name Hfield].
  apply Hnotin.
  eapply fields_local_store_names_in_expr; eassumption.
Qed.

Lemma match_branches_local_store_names_lookup_notin :
  forall x lookup_name branches e,
    lookup_expr_branch lookup_name branches = Some e ->
    ~ In x (match_branches_local_store_names branches) ->
    ~ In x (expr_local_store_names e).
Proof.
  intros x lookup_name branches e Hlookup Hnotin Hin.
  destruct (lookup_expr_branch_in_alpha lookup_name branches e Hlookup)
    as [binders Hbranch].
  apply Hnotin.
  eapply match_branches_local_store_names_in_expr; eassumption.
Qed.

Lemma match_binder_params_opt_names_hfs :
  forall binders tys ps,
    match_binder_params_opt binders tys = Some ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params_opt xs Ts) as [ps_tail |] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps; simpl.
    rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_opt_names_hfs :
  forall binders lts args v ps,
    match_payload_params_opt binders lts args v = Some ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params_opt in Hmatch.
  eapply match_binder_params_opt_names_hfs. exact Hmatch.
Qed.

Inductive store_hidden_frame_rel
    (x : ident) (T : Ty) (hidden : value) : store -> store -> Prop :=
  | SHFR_Here : forall s,
      store_hidden_frame_rel x T hidden (store_add x T hidden s) s
  | SHFR_Keep : forall se s_with s_without,
      se_name se <> x ->
      store_hidden_frame_rel x T hidden s_with s_without ->
      store_hidden_frame_rel x T hidden (se :: s_with) (se :: s_without).

Lemma store_hidden_frame_rel_here :
  forall x T hidden s,
    store_hidden_frame_rel x T hidden (store_add x T hidden s) s.
Proof.
  intros x T hidden s. constructor.
Qed.

Lemma store_hidden_frame_rel_head :
  forall x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    store_names s_with = x :: store_names s_without ->
    s_with = store_add x T hidden s_without.
Proof.
  intros x T hidden s_with s_without Hrel Hnames.
  inversion Hrel; subst; try reflexivity.
  simpl in Hnames. inversion Hnames; subst.
  contradiction.
Qed.

Lemma store_lookup_hidden_frame_rel_strip :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_lookup y s_with = store_lookup y s_without.
Proof.
  intros x T hidden s_with s_without y Hrel Hyx.
  induction Hrel as [s | se s_with s_without Hsex _ IH].
  - unfold store_add. simpl.
    destruct (ident_eqb y x) eqn:Hy; try reflexivity.
    apply ident_eqb_eq in Hy. contradiction.
  - simpl.
    destruct (ident_eqb y (se_name se)); try reflexivity.
    exact IH.
Qed.

Lemma store_hidden_frame_rel_lookup :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_lookup y s_with = store_lookup y s_without.
Proof.
  eapply store_lookup_hidden_frame_rel_strip.
Qed.

Lemma store_hidden_frame_rel_mark_used :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_hidden_frame_rel x T hidden
      (store_mark_used y s_with) (store_mark_used y s_without).
Proof.
  intros x T hidden s_with s_without y Hrel Hyx.
  induction Hrel as [s | se s_with s_without Hsex Hrel IH].
  - unfold store_add. simpl.
    destruct (ident_eqb y x) eqn:Hy.
    + apply ident_eqb_eq in Hy. contradiction.
    + constructor.
  - simpl.
    destruct (ident_eqb y (se_name se)); constructor; assumption.
Qed.

Lemma store_hidden_frame_rel_update_state :
  forall x T hidden s_with s_without y f s_with',
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_update_state y f s_with = Some s_with' ->
    exists s_without',
      store_update_state y f s_without = Some s_without' /\
      store_hidden_frame_rel x T hidden s_with' s_without'.
Proof.
  intros x T hidden s_with s_without y f s_with' Hrel.
  revert y f s_with'.
  induction Hrel as [s | se s_with s_without Hsex Hrel IH];
    intros y f s_with' Hyx Hupdate.
  - unfold store_add in Hupdate. simpl in Hupdate.
    destruct (ident_eqb y x) eqn:Hy.
    + apply ident_eqb_eq in Hy. contradiction.
    + destruct (store_update_state y f s) as [s0 |] eqn:Hbase;
        try discriminate.
      inversion Hupdate; subst s_with'.
      exists s0. split; [reflexivity | constructor].
  - simpl in Hupdate.
    destruct (ident_eqb y (se_name se)) eqn:Hy.
    + inversion Hupdate; subst s_with'.
      exists (MkStoreEntry (se_name se) (se_ty se) (se_val se)
        (f (se_state se)) :: s_without).
      split; [simpl; rewrite Hy; reflexivity |].
      constructor; assumption.
    + destruct (store_update_state y f s_with) as [tail' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s_with'.
      destruct (IH y f tail' Hyx Htail) as [tail0 [Htail0 Hrel0]].
      exists (se :: tail0). split.
      * simpl. rewrite Hy, Htail0. reflexivity.
      * constructor; assumption.
Qed.

Lemma store_hidden_frame_rel_update_val :
  forall x T hidden s_with s_without y v_new s_with',
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_update_val y v_new s_with = Some s_with' ->
    exists s_without',
      store_update_val y v_new s_without = Some s_without' /\
      store_hidden_frame_rel x T hidden s_with' s_without'.
Proof.
  intros x T hidden s_with s_without y v_new s_with' Hrel.
  revert y v_new s_with'.
  induction Hrel as [s | se s_with s_without Hsex Hrel IH];
    intros y v_new s_with' Hyx Hupdate.
  - unfold store_add in Hupdate. simpl in Hupdate.
    destruct (ident_eqb y x) eqn:Hy.
    + apply ident_eqb_eq in Hy. contradiction.
    + destruct (store_update_val y v_new s) as [s0 |] eqn:Hbase;
        try discriminate.
      inversion Hupdate; subst s_with'.
      exists s0. split; [reflexivity | constructor].
  - simpl in Hupdate.
    destruct (ident_eqb y (se_name se)) eqn:Hy.
    + inversion Hupdate; subst s_with'.
      exists (MkStoreEntry (se_name se) (se_ty se) v_new (se_state se) :: s_without).
      split; [simpl; rewrite Hy; reflexivity |].
      constructor; assumption.
    + destruct (store_update_val y v_new s_with) as [tail' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s_with'.
      destruct (IH y v_new tail' Hyx Htail) as [tail0 [Htail0 Hrel0]].
      exists (se :: tail0). split.
      * simpl. rewrite Hy, Htail0. reflexivity.
      * constructor; assumption.
Qed.

Lemma store_hidden_frame_rel_update_path :
  forall x T hidden s_with s_without y path v_new s_with',
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_update_path y path v_new s_with = Some s_with' ->
    exists s_without',
      store_update_path y path v_new s_without = Some s_without' /\
      store_hidden_frame_rel x T hidden s_with' s_without'.
Proof.
  intros x T hidden s_with s_without y path v_new s_with' Hrel.
  revert y path v_new s_with'.
  induction Hrel as [s | se s_with s_without Hsex Hrel IH];
    intros y path v_new s_with' Hyx Hupdate.
  - unfold store_add in Hupdate. simpl in Hupdate.
    destruct (ident_eqb y x) eqn:Hy.
    + apply ident_eqb_eq in Hy. contradiction.
    + destruct (store_update_path y path v_new s) as [s0 |] eqn:Hbase;
        try discriminate.
      inversion Hupdate; subst s_with'.
      exists s0. split; [reflexivity | constructor].
  - simpl in Hupdate.
    destruct (ident_eqb y (se_name se)) eqn:Hy.
    + destruct (value_update_path (se_val se) path v_new) as [v' |] eqn:Hval;
        try discriminate.
      inversion Hupdate; subst s_with'.
      exists (MkStoreEntry (se_name se) (se_ty se) v' (se_state se) :: s_without).
      split; [simpl; rewrite Hy, Hval; reflexivity |].
      constructor; assumption.
    + destruct (store_update_path y path v_new s_with) as [tail' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s_with'.
      destruct (IH y path v_new tail' Hyx Htail) as [tail0 [Htail0 Hrel0]].
      exists (se :: tail0). split.
      * simpl. rewrite Hy, Htail0. reflexivity.
      * constructor; assumption.
Qed.

Lemma store_hidden_frame_rel_restore_path :
  forall x T hidden s_with s_without y path s_with',
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_restore_path y path s_with = Some s_with' ->
    exists s_without',
      store_restore_path y path s_without = Some s_without' /\
      store_hidden_frame_rel x T hidden s_with' s_without'.
Proof.
  intros x T hidden s_with s_without y path s_with' Hrel Hyx Hrestore.
  unfold store_restore_path in *.
  eapply store_hidden_frame_rel_update_state; eassumption.
Qed.

Lemma store_hidden_frame_rel_consume_path :
  forall x T hidden s_with s_without y path s_with',
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_consume_path y path s_with = Some s_with' ->
    exists s_without',
      store_consume_path y path s_without = Some s_without' /\
      store_hidden_frame_rel x T hidden s_with' s_without'.
Proof.
  intros x T hidden s_with s_without y path s_with' Hrel Hyx Hconsume.
  unfold store_consume_path in *.
  rewrite (store_hidden_frame_rel_lookup x T hidden s_with s_without y Hrel Hyx)
    in Hconsume.
  destruct (store_lookup y s_without) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havail; try discriminate.
  eapply store_hidden_frame_rel_update_state; eassumption.
Qed.

Lemma eval_place_hidden_frame_rel_strip :
  forall s_with s_without p y path x T hidden,
    store_hidden_frame_rel x T hidden s_with s_without ->
    place_name p <> x ->
    store_refs_exclude_root x s_without ->
    eval_place s_with p y path ->
    y <> x /\ eval_place s_without p y path.
Proof.
  intros s_with s_without p y path x T hidden Hrel Hfresh Hrefs Heval.
  induction Heval.
  - split.
    + exact Hfresh.
    + eapply EvalPlace_Var.
      rewrite <- (store_hidden_frame_rel_lookup x T hidden s s_without x0
                    Hrel Hfresh).
      exact H.
  - simpl in Hfresh.
    destruct IHHeval as [Hyx Hbase].
    + exact Hrel.
    + exact Hfresh.
    + split; [exact Hyx | constructor; exact Hbase].
  - simpl in Hfresh.
    destruct IHHeval as [Hrx Hbase].
    + exact Hrel.
    + exact Hfresh.
    + rewrite (store_hidden_frame_rel_lookup x T hidden s s_without r
                 Hrel Hrx) in H.
      split.
      * eapply value_refs_exclude_lookup_ref_neq.
        -- eapply store_refs_exclude_lookup_value; eassumption.
        -- exact H0.
      * eapply EvalPlace_Deref; eassumption.
Qed.

Lemma bind_params_hidden_frame_rel :
  forall ps vs x T hidden s_with s_without,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_hidden_frame_rel x T hidden s_with s_without ->
    store_hidden_frame_rel x T hidden
      (bind_params ps vs s_with) (bind_params ps vs s_without).
Proof.
  induction ps as [| p ps IH]; intros vs x T hidden s_with s_without
    Hnotin Hrel; destruct vs as [| v vs']; simpl.
  - exact Hrel.
  - exact Hrel.
  - exact Hrel.
  - apply SHFR_Keep.
    + simpl. intros Heq. apply Hnotin. left. exact Heq.
    + apply IH.
      * intros Hin. apply Hnotin. right. exact Hin.
      * exact Hrel.
Qed.

Lemma store_hidden_frame_rel_bind_params :
  forall ps vs x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_hidden_frame_rel x T hidden
      (bind_params ps vs s_with) (bind_params ps vs s_without).
Proof.
  intros ps vs x T hidden s_with s_without Hrel Hnotin.
  eapply bind_params_hidden_frame_rel; eassumption.
Qed.

Lemma store_remove_hidden_frame_rel :
  forall x T hidden s_with s_without y,
    store_hidden_frame_rel x T hidden s_with s_without ->
    y <> x ->
    store_hidden_frame_rel x T hidden
      (store_remove y s_with) (store_remove y s_without).
Proof.
  intros x T hidden s_with s_without y Hrel Hyx.
  induction Hrel as [s | se s_with s_without Hsex Hrel IH].
  - unfold store_add. simpl.
    destruct (ident_eqb y x) eqn:Hy.
    + apply ident_eqb_eq in Hy. contradiction.
    + apply SHFR_Here.
  - simpl.
    destruct (ident_eqb y (se_name se)) eqn:Hy.
    + exact Hrel.
    + apply SHFR_Keep; assumption.
Qed.

Lemma store_remove_params_hidden_frame_rel :
  forall ps x T hidden s_with s_without,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_hidden_frame_rel x T hidden s_with s_without ->
    store_hidden_frame_rel x T hidden
      (store_remove_params ps s_with) (store_remove_params ps s_without).
Proof.
  induction ps as [| p ps IH]; intros x T hidden s_with s_without Hnotin Hrel.
  - exact Hrel.
  - simpl.
    apply IH.
    + intros Hin. apply Hnotin. right. exact Hin.
    + apply store_remove_hidden_frame_rel.
      * exact Hrel.
      * intros Heq. apply Hnotin. left. exact Heq.
Qed.

Lemma store_hidden_frame_rel_remove_params :
  forall ps x T hidden s_with s_without,
    store_hidden_frame_rel x T hidden s_with s_without ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_hidden_frame_rel x T hidden
      (store_remove_params ps s_with) (store_remove_params ps s_without).
Proof.
  intros ps x T hidden s_with s_without Hrel Hnotin.
  eapply store_remove_params_hidden_frame_rel; eassumption.
Qed.

Lemma store_add_refs_exclude_root :
  forall root x T v s,
    value_refs_exclude_root root v ->
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_add x T v s).
Proof.
  intros root x T v s Hv Hs.
  unfold store_add. constructor.
  - constructor. exact Hv.
  - exact Hs.
Qed.

Lemma bind_params_refs_exclude_root :
  forall root ps vs s,
    Forall (value_refs_exclude_root root) vs ->
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (bind_params ps vs s).
Proof.
  intros root ps.
  induction ps as [| p ps IH]; intros vs s Hvs Hs;
    destruct vs as [| v vs']; simpl; try exact Hs.
  inversion Hvs; subst.
  apply store_add_refs_exclude_root; eauto.
Qed.

Lemma store_remove_refs_exclude_root :
  forall root y s,
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_remove y s).
Proof.
  intros root y s Hrefs.
  induction Hrefs as [| se rest Hse Hrest IH]; simpl; try constructor.
  destruct (ident_eqb y (se_name se)).
  - exact Hrest.
  - constructor; assumption.
Qed.

Lemma store_remove_params_refs_exclude_root :
  forall root ps s,
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_remove_params ps s).
Proof.
  induction ps as [| p ps IH]; intros s Hrefs; simpl.
  - exact Hrefs.
  - apply IH. apply store_remove_refs_exclude_root. exact Hrefs.
Qed.

Lemma match_binder_params_opt_notin_hfs :
  forall binders tys ps x,
    match_binder_params_opt binders tys = Some ps ->
    ~ In x binders ->
    ~ In x (ctx_names (params_ctx ps)).
Proof.
  intros binders tys ps x Hmatch Hnotin Hin.
  apply Hnotin.
  rewrite <- (match_binder_params_opt_names_hfs binders tys ps Hmatch).
  exact Hin.
Qed.

Lemma match_payload_params_opt_notin_hfs :
  forall binders lts args v ps x,
    match_payload_params_opt binders lts args v = Some ps ->
    ~ In x binders ->
    ~ In x (ctx_names (params_ctx ps)).
Proof.
  intros binders lts args v ps x Hmatch Hnotin Hin.
  apply Hnotin.
  rewrite <- (match_payload_params_opt_names_hfs binders lts args v ps Hmatch).
  exact Hin.
Qed.

Theorem hidden_frame_eval_strip_rel_mutual :
  (forall env s e s_hidden' v,
    eval env s e s_hidden' v ->
    forall x T hidden s_base,
      store_hidden_frame_rel x T hidden s s_base ->
      preservation_ready_expr e ->
      ~ In x (free_vars_expr e) ->
      ~ In x (expr_local_store_names e) ->
      store_refs_exclude_root x s_base ->
      exists s',
        store_hidden_frame_rel x T hidden s_hidden' s' /\
        eval env s_base e s' v /\
        store_refs_exclude_root x s' /\
        value_refs_exclude_root x v) /\
  (forall env s args s_hidden' vs,
    eval_args env s args s_hidden' vs ->
    forall x T hidden s_base,
      store_hidden_frame_rel x T hidden s s_base ->
      preservation_ready_args args ->
      ~ In x (args_free_vars_ts args) ->
      ~ In x (args_local_store_names args) ->
      store_refs_exclude_root x s_base ->
      exists s',
        store_hidden_frame_rel x T hidden s_hidden' s' /\
        eval_args env s_base args s' vs /\
        store_refs_exclude_root x s' /\
        Forall (value_refs_exclude_root x) vs) /\
  (forall env s fields defs s_hidden' values,
    eval_struct_fields env s fields defs s_hidden' values ->
    forall x T hidden s_base,
      store_hidden_frame_rel x T hidden s s_base ->
      preservation_ready_fields fields ->
      ~ In x (fields_free_vars_ts fields) ->
      ~ In x (fields_local_store_names fields) ->
      store_refs_exclude_root x s_base ->
      exists s',
        store_hidden_frame_rel x T hidden s_hidden' s' /\
        eval_struct_fields env s_base fields defs s' values /\
        store_refs_exclude_root x s' /\
        value_fields_refs_exclude_root x values).
Proof.
  assert (Hmut : forall env,
    (forall s e s_hidden' v,
      eval env s e s_hidden' v ->
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s',
          store_hidden_frame_rel x T hidden s_hidden' s' /\
          eval env s_base e s' v /\
          store_refs_exclude_root x s' /\
          value_refs_exclude_root x v) /\
    (forall s args s_hidden' vs,
      eval_args env s args s_hidden' vs ->
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s',
          store_hidden_frame_rel x T hidden s_hidden' s' /\
          eval_args env s_base args s' vs /\
          store_refs_exclude_root x s' /\
          Forall (value_refs_exclude_root x) vs) /\
    (forall s fields defs s_hidden' values,
      eval_struct_fields env s fields defs s_hidden' values ->
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s',
          store_hidden_frame_rel x T hidden s_hidden' s' /\
          eval_struct_fields env s_base fields defs s' values /\
          store_refs_exclude_root x s' /\
          value_fields_refs_exclude_root x values)).
  { intro env.
  apply (hidden_frame_eval_eval_args_eval_struct_fields_ind env
    (fun s e s' v _ =>
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          store_hidden_frame_rel x T hidden s' s_base' /\
          eval env s_base e s_base' v /\
          store_refs_exclude_root x s_base' /\
          value_refs_exclude_root x v)
    (fun s args s' vs _ =>
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          store_hidden_frame_rel x T hidden s' s_base' /\
          eval_args env s_base args s_base' vs /\
          store_refs_exclude_root x s_base' /\
          Forall (value_refs_exclude_root x) vs)
    (fun s fields defs s' values _ =>
      forall x T hidden s_base,
        store_hidden_frame_rel x T hidden s s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          store_hidden_frame_rel x T hidden s' s_base' /\
          eval_struct_fields env s_base fields defs s_base' values /\
          store_refs_exclude_root x s_base' /\
          value_fields_refs_exclude_root x values)).
  - intros s x T hidden s_base Hs Hready _ _ Hrefs.
    exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    exists s_base. destruct lit; repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    exists s_base. repeat split; try constructor; assumption.
  - intros s y se Hlookup Hconsume x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Var_Copy; eassumption.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s y se Hlookup Hconsume Hused x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    exists (store_mark_used y s_base). repeat split.
    + apply store_hidden_frame_rel_mark_used; assumption.
    + eapply Eval_Var_Consume; eassumption.
    + apply store_mark_used_refs_exclude_root. exact Hrefs.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s p y path se Ty v Heval_place Hlookup Havail Hty Hneeds
      Hvalue x T hidden s_base Hs Hready Hfree _ Hrefs.
    inversion Hready; subst; clear Hready.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_hidden_frame_rel_strip s s_base p y path x T hidden
                Hs Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Place_Copy; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' p y path se Ty v Heval_place Hlookup Havail Hty
      Hneeds Hvalue Hconsume x T hidden s_base Hs Hready Hfree _ Hrefs.
    inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_hidden_frame_rel_strip s s_base p y path x T hidden
                Hs Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    destruct (store_hidden_frame_rel_consume_path x T hidden s s_base y path s'
                Hs Hyx Hconsume) as [s_base' [Hconsume_base Hs']].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Place_Consume; eassumption.
    + eapply store_consume_path_refs_exclude_root; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IH x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_fields fields |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' Hvalues]]]].
    exists s_base'. split; try assumption.
    split.
    + eapply Eval_Struct; eassumption.
    + split; try assumption.
      constructor. exact Hvalues.
  - intros s s' enum_name variant_name lts variant_lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IH x T hidden s_base Hs Hready Hfree
      Hlocal Hrefs.
    inversion Hready; subst.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_args payloads |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' Hvalues]]]].
    exists s_base'. split; try assumption.
    split.
    + eapply Eval_Enum; eassumption.
    + split; try assumption.
      constructor. exact Hvalues.
  - intros s s1 s2 m y Ty e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s' e v Heval IH x T hidden s_base Hs Hready Hfree
      Hlocal Hrefs.
    inversion Hready; subst.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' _]]]].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Drop. exact Heval_base.
    + constructor.
  - intros s s1 s2 s3 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate Hrestore x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    destruct (store_hidden_frame_rel_update_val x T hidden s1 s1_base y v_new s2
                Hs1 Hyx Hupdate) as [s2_base [Hupdate_base Hs2]].
    destruct (store_hidden_frame_rel_restore_path x T hidden s2 s2_base y [] s3
                Hs2 Hyx Hrestore) as [s3_base [Hrestore_base Hs3]].
    exists s3_base. repeat split; try assumption.
    + eapply Eval_Replace; eassumption.
    + eapply store_restore_path_refs_exclude_root.
      * eapply store_update_val_refs_exclude_root; eassumption.
      * exact Hrestore_base.
    + exact (store_refs_exclude_lookup_value x s_base y old_e Hrefs Hlookup).
  - intros s s1 s2 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    destruct (store_hidden_frame_rel_update_val x T hidden s1 s1_base y v_new s2
                Hs1 Hyx Hupdate) as [s2_base [Hupdate_base Hs2]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign; eassumption.
    + eapply store_update_val_refs_exclude_root; eassumption.
    + constructor.
  - intros s s1 s2 s3 p y path old_v e_new v_new Heval_place
      Hlookup_path Heval_new IH Hupdate Hrestore x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_hidden_frame_rel_strip s s_base p y path x T hidden
                Hs Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    unfold store_lookup_path in Hlookup_path.
    rewrite (store_hidden_frame_rel_lookup x T hidden s s_base y Hs Hyx)
      in Hlookup_path.
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    destruct (store_hidden_frame_rel_update_path x T hidden s1 s1_base y path v_new s2
                Hs1 Hyx Hupdate)
      as [s2_base [Hupdate_base Hs2]].
    destruct (store_hidden_frame_rel_restore_path x T hidden s2 s2_base y path s3
                Hs2 Hyx Hrestore) as [s3_base [Hrestore_base Hs3]].
    exists s3_base. repeat split; try assumption.
    + eapply Eval_Replace_Place; eassumption.
    + eapply store_restore_path_refs_exclude_root.
      * eapply store_update_path_refs_exclude_root; eassumption.
      * exact Hrestore_base.
    + destruct (store_lookup y s_base) as [se |] eqn:Hlookup_base;
        simpl in Hlookup_path; try discriminate.
      pose proof (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup_base)
        as Hse_refs.
      pose proof (value_refs_exclude_lookup_path x (se_val se) path old_v
                    Hse_refs Hlookup_path) as Hold_refs.
      exact Hold_refs.
  - intros s s1 s2 p y path e_new v_new Heval_place Heval_new IH
      Hupdate x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_hidden_frame_rel_strip s s_base p y path x T hidden
                Hs Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    destruct (IH x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    destruct (store_hidden_frame_rel_update_path x T hidden s1 s1_base y path v_new s2
                Hs1 Hyx Hupdate)
      as [s2_base [Hupdate_base Hs2]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign_Place; eassumption.
    + eapply store_update_path_refs_exclude_root; eassumption.
    + constructor.
  - intros s p y path rk Heval_place x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_hidden_frame_rel_strip s s_base p y path x T hidden
                Hs Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    exists s_base. repeat split; try assumption.
    + eapply Eval_Borrow; eassumption.
    + constructor. apply ident_eqb_neq. intros Heq. apply Hyx. symmetry. exact Heq.
  - intros s r p y path se v Ty Has_place Heval_place Hlookup Hvalue
      Hty Husage x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s_r r y path se v Ty Hnot_place Heval_r IHr Hlookup
      Hvalue Hty Husage x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Fn; eassumption.
    + constructor. constructor.
  - intros s fname captures captured fdef Hlookup Hcopy x T hidden
      s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    assert (Hfree_then : ~ In x (free_vars_expr e2)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (Hlocal_then : ~ In x (expr_local_store_names e2)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    destruct (IHthen x T hidden s1_base Hs1
                ltac:(match goal with
                | H : preservation_ready_expr e2 |- _ => exact H
                end) Hfree_then Hlocal_then Hrefs1)
      as [s2_base [Hs2 [Heval_then_base [Hrefs2 Hv]]]].
    exists s2_base. repeat split; try assumption.
    eapply Eval_If_True; eassumption.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    assert (Hfree_else : ~ In x (free_vars_expr e3)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    assert (Hlocal_else : ~ In x (expr_local_store_names e3)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
	    destruct (IHelse x T hidden s1_base Hs1
	                ltac:(match goal with
	                | H : preservation_ready_expr e3 |- _ => exact H
	                end) Hfree_else Hlocal_else Hrefs1)
	      as [s2_base [Hs2 [Heval_else_base [Hrefs2 Hv]]]].
	    exists s2_base. repeat split; try assumption.
	    eapply Eval_If_False; eassumption.
  - intros s s_scrut s_branch s' scrut branches enum_name variant_name
      lts args values edef vdef binders ps e_branch v
      Heval_scrut IHscrut Hlookup_enum Hlookup_variant Hlookup_binders
      Hparams Hlen Hlookup Heval_branch IHbranch Hstore
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    assert (Hfree_scrut : ~ In x (free_vars_expr scrut)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_scrut : ~ In x (expr_local_store_names scrut)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHscrut x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr scrut |- _ => exact H
                end) Hfree_scrut Hlocal_scrut Hrefs)
      as [s_scrut_base [Hs_scrut [Heval_scrut_base [Hrefs_scrut Hvenum]]]].
    assert (Hready_branch : preservation_ready_expr e_branch).
    { eapply lookup_match_branch_preservation_ready; eassumption. }
    assert (Hfree_branches : ~ In x (match_branches_free_vars_ts branches)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right. exact Hin. }
    assert (Hfree_branch : ~ In x (free_vars_expr e_branch)).
    { eapply match_branches_free_vars_ts_lookup_notin; eassumption. }
    assert (Hlocal_branches : ~ In x (match_branches_local_store_names branches)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right. exact Hin. }
    assert (Hlocal_branch : ~ In x (expr_local_store_names e_branch)).
    { eapply match_branches_local_store_names_lookup_notin; eassumption. }
    assert (Hnotin_ps : ~ In x (ctx_names (params_ctx ps))).
    { rewrite (match_payload_params_opt_names_hfs binders lts args vdef ps Hparams).
      intros Hin. apply Hlocal_branches.
      eapply lookup_expr_branch_binders_local_store_names_in; eassumption. }
    destruct (IHbranch x T hidden (bind_params ps values s_scrut_base)
                (store_hidden_frame_rel_bind_params ps values x T hidden
                   s_scrut s_scrut_base Hs_scrut Hnotin_ps)
                Hready_branch Hfree_branch Hlocal_branch
                (bind_params_refs_exclude_root x ps values s_scrut_base
                   ltac:(inversion Hvenum; subst; assumption) Hrefs_scrut))
      as [s_branch_base [Hs_branch [Heval_branch_base [Hrefs_branch Hv]]]].
    exists (store_remove_params ps s_branch_base). repeat split.
    + apply store_hidden_frame_rel_remove_params; assumption.
    + eapply Eval_MatchEnum.
      * exact Heval_scrut_base.
      * exact Hlookup_enum.
      * exact Hlookup_variant.
      * exact Hlookup_binders.
      * exact Hparams.
      * exact Hlen.
      * exact Hlookup.
      * exact Heval_branch_base.
      * reflexivity.
    + eapply store_remove_params_refs_exclude_root; eassumption.
    + assumption.
		  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody x T hidden s_base Hs
		      Hready Hfree Hlocal Hrefs.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody x T hidden
	      s_base Hs Hready Hfree Hlocal Hrefs.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args fname captured fdef fcall
	      vs ret used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s_fn s_args s_body callee type_args args fname captured fdef fcall
      vs ret used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody x T hidden s_base0 Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_args IHargs
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready; subst.
    destruct (args_free_vars_ts_cons_notin x e es Hfree)
      as [Hfree_e Hfree_es].
    destruct (args_local_store_names_cons_notin x e es Hlocal)
      as [Hlocal_e Hlocal_es].
    destruct (IHe x T hidden s_base Hs
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    destruct (IHargs x T hidden s1_base Hs1
                ltac:(match goal with
                | H : preservation_ready_args es |- _ => exact H
                end) Hfree_es Hlocal_es Hrefs1)
      as [s2_base [Hs2 [Heval_args_base [Hrefs2 Hvs]]]].
    exists s2_base. repeat split; try assumption.
    + eapply EvalArgs_Cons; eassumption.
    + constructor; assumption.
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 fields f rest e v values Hlookup Heval_e IHe
      Heval_fields IHfields x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    assert (Hready_e : preservation_ready_expr e).
    { eapply preservation_ready_fields_lookup; eassumption. }
    assert (Hfree_e : ~ In x (free_vars_expr e)).
    { eapply fields_free_vars_ts_lookup_notin; eassumption. }
    assert (Hlocal_e : ~ In x (expr_local_store_names e)).
    { eapply fields_local_store_names_lookup_notin; eassumption. }
    destruct (IHe x T hidden s_base Hs Hready_e Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    destruct (IHfields x T hidden s1_base Hs1 Hready Hfree Hlocal Hrefs1)
      as [s2_base [Hs2 [Heval_fields_base [Hrefs2 Hvalues]]]].
    exists s2_base. repeat split; try assumption.
    + eapply EvalStructFields_Cons; eassumption.
    + constructor; assumption.
  }
  repeat split; intros env; destruct (Hmut env) as [Heval [Hargs Hfields]]; eauto.
Qed.

Lemma preservation_ready_eval_args_hidden_frame_strip :
  forall env s args s_hidden' vs x T hidden,
    eval_args env (store_add x T hidden s) args s_hidden' vs ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s ->
    exists s',
      s_hidden' = store_add x T hidden s' /\
      eval_args env s args s' vs /\
      store_refs_exclude_root x s' /\
      Forall (value_refs_exclude_root x) vs.
Proof.
  intros env s args s_hidden' vs x T hidden Heval Hready Hfree Hlocal Hrefs.
  destruct hidden_frame_eval_strip_rel_mutual as [_ [Hargs _]].
  destruct (Hargs env (store_add x T hidden s) args s_hidden' vs Heval
              x T hidden s (store_hidden_frame_rel_here x T hidden s)
              Hready Hfree Hlocal Hrefs)
    as [s' [Hrel [Heval_base [Hrefs' Hvs]]]].
  exists s'. repeat split; try assumption.
  apply store_hidden_frame_rel_head with (s_without := s'); try assumption.
  rewrite (proj1 (proj2 preservation_ready_eval_store_names_mutual)
             env (store_add x T hidden s) args s_hidden' vs Heval Hready).
  rewrite (proj1 (proj2 preservation_ready_eval_store_names_mutual)
             env s args s' vs Heval_base Hready).
  unfold store_add. simpl. reflexivity.
Qed.

Lemma store_refs_exclude_root_app :
  forall root s1 s2,
    store_refs_exclude_root root s1 ->
    store_refs_exclude_root root s2 ->
    store_refs_exclude_root root (s1 ++ s2).
Proof.
  intros root s1.
  induction s1 as [| se rest IH]; intros s2 H1 H2; simpl.
  - exact H2.
  - inversion H1; subst. constructor; eauto.
Qed.

Lemma store_remove_store_add_same :
  forall x T v s,
    store_remove x (store_add x T v s) = s.
Proof.
  intros x T v s.
  unfold store_add. simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma store_remove_commute_neq :
  forall x y s,
    x <> y ->
    store_remove x (store_remove y s) =
      store_remove y (store_remove x s).
Proof.
  intros x y s Hneq.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb y (se_name se)) eqn:Hy;
    destruct (ident_eqb x (se_name se)) eqn:Hx; simpl.
  - apply ident_eqb_eq in Hy. apply ident_eqb_eq in Hx.
    subst. contradiction.
  - rewrite Hy. reflexivity.
  - rewrite Hx. reflexivity.
  - rewrite Hy, Hx. rewrite IH. reflexivity.
Qed.

Lemma store_remove_params_store_remove_commute :
  forall ps x s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove x (store_remove_params ps s) =
      store_remove_params ps (store_remove x s).
Proof.
  induction ps as [| p ps IH]; intros x s Hnotin; simpl.
  - reflexivity.
  - rewrite store_remove_commute_neq.
    + rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
    + intros Heq. apply Hnotin. left. exact Heq.
Qed.

Lemma store_remove_params_store_add_non_param :
  forall ps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove_params ps (store_add x T v s) =
      store_add x T v (store_remove_params ps s).
Proof.
  induction ps as [| p ps IH]; intros x T v s Hnotin; simpl.
  - reflexivity.
  - unfold store_add. simpl.
    destruct (ident_eqb (param_name p) x) eqn:Hpx.
    + apply ident_eqb_eq in Hpx. subst x.
      contradiction Hnotin. left. reflexivity.
    + change (MkStoreEntry x T v (binding_state_of_bool false) ::
        store_remove (param_name p) s)
        with (store_add x T v (store_remove (param_name p) s)).
      rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_hidden_after_params :
  forall ps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove x (store_remove_params ps (store_add x T v s)) =
      store_remove_params ps s.
Proof.
  intros ps x T v s Hnotin.
  rewrite store_remove_params_store_add_non_param by exact Hnotin.
  rewrite store_remove_store_add_same. reflexivity.
Qed.

Lemma store_remove_hidden_after_param_groups :
  forall ps caps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (ctx_names (params_ctx caps)) ->
    store_remove x
      (store_remove_params caps
        (store_remove_params ps (store_add x T v s))) =
      store_remove_params caps (store_remove_params ps s).
Proof.
  intros ps caps x T v s Hnotin_ps Hnotin_caps.
  rewrite store_remove_params_store_add_non_param by exact Hnotin_ps.
  rewrite store_remove_params_store_add_non_param by exact Hnotin_caps.
  rewrite store_remove_store_add_same. reflexivity.
Qed.

Lemma alpha_rename_fn_def_params_not_in_used :
  forall used f fr used' x,
    alpha_rename_fn_def used f = (fr, used') ->
    In x used ->
    ~ In x (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros used f fr used' x Hrename Hused Hin.
  pose proof (alpha_rename_fn_def_params_fresh_used
                used f fr used' Hrename x Hin) as Hfresh.
  exact (Hfresh Hused).
Qed.

Lemma alpha_rename_fn_def_body_local_store_names_not_in_used :
  forall used f fr used' x,
    alpha_rename_fn_def used f = (fr, used') ->
    In x used ->
    ~ In x (expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' x Hrename Hused Hin.
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                used f fr used' Hrename) as Hfresh.
  pose proof (proj1 (Forall_forall _ _) Hfresh x Hin) as Hnotin.
  exact (Hnotin Hused).
Qed.

Lemma eval_let_make_closure_captured_call_args_strip :
  forall env s s_final m x T fname captures args ret,
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s ->
    exists captured fdef s_args_hidden s_args vs fcall used' s_body,
      lookup_fn fname (env_fns env) = Some fdef /\
      copy_capture_store_as captures (fn_captures fdef) s = Some captured /\
      s_args_hidden = store_add x T (VClosure fname captured) s_args /\
      eval_args env s args s_args vs /\
      store_refs_exclude_root x s_args /\
      Forall (value_refs_exclude_root x) vs /\
      alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
        (fcall, used') /\
      eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
        (fn_body fcall) s_body ret /\
      s_final =
        store_remove x
          (store_remove_params (fn_captures fcall)
            (store_remove_params (fn_params fcall) s_body)).
Proof.
  intros env s s_final m x T fname captures args ret Husage Heval Hready
    Hfree Hlocal Hrefs.
  inversion Heval; subst; clear Heval.
  match goal with
  | Hmake : eval _ _ (EMakeClosure _ _) _ _ |- _ =>
      inversion Hmake; subst; clear Hmake
  end.
  match goal with
  | Hcall : eval _ _ (ECallExpr (EVar x) args) _ _ |- _ =>
      inversion Hcall; subst; clear Hcall
  end.
  match goal with
  | Hcallee : eval _ _ (EVar x) _ _ |- _ =>
      inversion Hcallee; subst; clear Hcallee
  end.
  - match goal with
    | Hlookup_var : store_lookup x
        (store_add x T (VClosure fname ?captured) ?s_base) =
        Some ?se |- _ =>
        rewrite store_lookup_store_add_same in Hlookup_var;
        inversion Hlookup_var; subst se; clear Hlookup_var
    end.
    repeat match goal with
    | Hvalue : se_val _ = VClosure _ _ |- _ =>
        simpl in Hvalue; inversion Hvalue; subst; clear Hvalue
    end.
    match goal with
    | Hlookup_make : lookup_fn ?fname_call (env_fns env) = Some ?fdef_make,
      Hlookup_call : lookup_fn ?fname_call (env_fns env) = Some ?fdef_call |- _ =>
        assert (Hfdef_same : fdef_call = fdef_make)
        by (eapply lookup_fn_deterministic; eassumption);
        subst fdef_call
    end.
    match goal with
    | Heval_args : eval_args _ _ _ _ _ |- _ =>
        destruct (preservation_ready_eval_args_hidden_frame_strip
                    env s1 args s_args vs x T (VClosure fname0 captured0)
                    Heval_args Hready Hfree Hlocal Hrefs)
          as [s_args_base [Hs_args_hidden
            [Heval_args_base [Hrefs_args Hvs_refs]]]]
    end.
    subst s_args.
    exists captured0, fdef,
      (store_add x T (VClosure fname0 captured0) s_args_base),
      s_args_base, vs, fcall, used', s_body.
    repeat split; try eassumption.
  - match goal with
    | Hlookup_var : store_lookup x
        (store_add x T (VClosure fname ?captured) ?s_base) =
        Some ?se |- _ =>
        rewrite store_lookup_store_add_same in Hlookup_var;
        inversion Hlookup_var; subst se; clear Hlookup_var
    end.
    match goal with
    | Hconsume : needs_consume _ = true |- _ =>
        simpl in Hconsume;
        unfold needs_consume in Hconsume;
        rewrite Husage in Hconsume;
        discriminate
    end.
Qed.
