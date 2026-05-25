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

Theorem hidden_frame_eval_strip_mutual :
  (forall env s e s_hidden' v,
    eval env s e s_hidden' v ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_expr e ->
      ~ In x (free_vars_expr e) ->
      ~ In x (expr_local_store_names e) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval env s_base e s' v /\
        store_refs_exclude_root x s' /\
        value_refs_exclude_root x v) /\
  (forall env s args s_hidden' vs,
    eval_args env s args s_hidden' vs ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_args args ->
      ~ In x (args_free_vars_ts args) ->
      ~ In x (args_local_store_names args) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval_args env s_base args s' vs /\
        store_refs_exclude_root x s' /\
        Forall (value_refs_exclude_root x) vs) /\
  (forall env s fields defs s_hidden' values,
    eval_struct_fields env s fields defs s_hidden' values ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_fields fields ->
      ~ In x (fields_free_vars_ts fields) ->
      ~ In x (fields_local_store_names fields) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval_struct_fields env s_base fields defs s' values /\
        store_refs_exclude_root x s' /\
        value_fields_refs_exclude_root x values).
Proof.
  assert (Hmut : forall env,
    (forall s e s_hidden' v,
      eval env s e s_hidden' v ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval env s_base e s' v /\
          store_refs_exclude_root x s' /\
          value_refs_exclude_root x v) /\
    (forall s args s_hidden' vs,
      eval_args env s args s_hidden' vs ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval_args env s_base args s' vs /\
          store_refs_exclude_root x s' /\
          Forall (value_refs_exclude_root x) vs) /\
    (forall s fields defs s_hidden' values,
      eval_struct_fields env s fields defs s_hidden' values ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval_struct_fields env s_base fields defs s' values /\
          store_refs_exclude_root x s' /\
          value_fields_refs_exclude_root x values)).
  { intro env.
  apply (hidden_frame_eval_eval_args_eval_struct_fields_ind env
    (fun s e s' v _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval env s_base e s_base' v /\
          store_refs_exclude_root x s_base' /\
          value_refs_exclude_root x v)
    (fun s args s' vs _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval_args env s_base args s_base' vs /\
          store_refs_exclude_root x s_base' /\
          Forall (value_refs_exclude_root x) vs)
    (fun s fields defs s' values _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval_struct_fields env s_base fields defs s_base' values /\
          store_refs_exclude_root x s_base' /\
          value_fields_refs_exclude_root x values)).
  - intros s x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. destruct lit; repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s y se Hlookup Hconsume x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    subst s.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Var_Copy; eassumption.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s y se Hlookup Hconsume Hused x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    subst s.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists (store_mark_used y s_base). repeat split.
    + rewrite store_mark_used_store_add_diff by exact Hyx. reflexivity.
    + eapply Eval_Var_Consume; eassumption.
    + apply store_mark_used_refs_exclude_root. exact Hrefs.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s p y path se Ty v Heval_place Hlookup Havail Hty Hneeds
      Hvalue x T hidden s_base Hs Hready Hfree _ Hrefs.
    subst s. inversion Hready; subst; clear Hready.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Place_Copy; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' p y path se Ty v Heval_place Hlookup Havail Hty
      Hneeds Hvalue Hconsume x T hidden s_base Hs Hready Hfree _ Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (store_consume_path_store_add_inv y x path T hidden s_base s'
                Hyx Hconsume) as [s_base' [Hs' Hconsume_base]].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Place_Consume; eassumption.
    + eapply store_consume_path_refs_exclude_root; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IH x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_fields fields |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' Hvalues]]]].
    exists s_base'. split; try assumption.
    split.
    + subst s'. eapply Eval_Struct; eassumption.
    + split; try assumption.
      constructor. exact Hvalues.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IH x T hidden s_base Hs Hready Hfree
      Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_args payloads |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' Hvalues]]]].
    exists s_base'. split; try assumption.
    split.
    + subst s'. eapply Eval_Enum; eassumption.
    + split; try assumption.
      constructor. exact Hvalues.
  - intros s s1 s2 m y Ty e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s' e v Heval IH x T hidden s_base Hs Hready Hfree
      Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' _]]]].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Drop. exact Heval_base.
    + constructor.
  - intros s s1 s2 s3 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate Hrestore x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_val_store_add_inv y x T hidden v_new s1_base s2
                Hyx Hupdate) as [s2_base [Hs2 Hupdate_base]].
    subst s2.
    destruct (store_restore_path_store_add_inv y x [] T hidden s2_base s3
                Hyx Hrestore) as [s3_base [Hs3 Hrestore_base]].
    exists s3_base. repeat split; try assumption.
    + eapply Eval_Replace; eassumption.
    + eapply store_restore_path_refs_exclude_root.
      * eapply store_update_val_refs_exclude_root; eassumption.
      * exact Hrestore_base.
    + exact (store_refs_exclude_lookup_value x s_base y old_e Hrefs Hlookup).
  - intros s s1 s2 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_val_store_add_inv y x T hidden v_new s1_base s2
                Hyx Hupdate) as [s2_base [Hs2 Hupdate_base]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign; eassumption.
    + eapply store_update_val_refs_exclude_root; eassumption.
    + constructor.
  - intros s s1 s2 s3 p y path old_v e_new v_new Heval_place
      Hlookup_path Heval_new IH Hupdate Hrestore x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    unfold store_lookup_path in Hlookup_path.
    rewrite store_lookup_store_add_diff in Hlookup_path by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_path_store_add_inv y x path T hidden v_new
                s1_base s2 Hyx Hupdate)
      as [s2_base [Hs2 Hupdate_base]].
    subst s2.
    destruct (store_restore_path_store_add_inv y x path T hidden s2_base s3
                Hyx Hrestore) as [s3_base [Hs3 Hrestore_base]].
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
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_path_store_add_inv y x path T hidden v_new
                s1_base s2 Hyx Hupdate)
      as [s2_base [Hs2 Hupdate_base]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign_Place; eassumption.
    + eapply store_update_path_refs_exclude_root; eassumption.
    + constructor.
  - intros s p y path rk Heval_place x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
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
    subst s. exists s_base. repeat split; try assumption.
    + eapply Eval_Fn; eassumption.
    + constructor. constructor.
  - intros s fname captures captured fdef Hlookup Hcopy x T hidden
      s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    subst s1.
    assert (Hfree_then : ~ In x (free_vars_expr e2)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (Hlocal_then : ~ In x (expr_local_store_names e2)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    destruct (IHthen x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e2 |- _ => exact H
                end) Hfree_then Hlocal_then Hrefs1)
      as [s2_base [Hs2 [Heval_then_base [Hrefs2 Hv]]]].
    exists s2_base. repeat split; try assumption.
    subst s2. eapply Eval_If_True; eassumption.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    subst s1.
    assert (Hfree_else : ~ In x (free_vars_expr e3)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    assert (Hlocal_else : ~ In x (expr_local_store_names e3)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    destruct (IHelse x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e3 |- _ => exact H
                end) Hfree_else Hlocal_else Hrefs1)
      as [s2_base [Hs2 [Heval_else_base [Hrefs2 Hv]]]].
    exists s2_base. repeat split; try assumption.
    subst s2. eapply Eval_If_False; eassumption.
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
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_args IHargs
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (args_free_vars_ts_cons_notin x e es Hfree)
      as [Hfree_e Hfree_es].
    destruct (args_local_store_names_cons_notin x e es Hlocal)
      as [Hlocal_e Hlocal_es].
    destruct (IHe x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    subst s1.
    destruct (IHargs x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_args es |- _ => exact H
                end) Hfree_es Hlocal_es Hrefs1)
      as [s2_base [Hs2 [Heval_args_base [Hrefs2 Hvs]]]].
    exists s2_base. repeat split; try assumption.
    + subst s2. eapply EvalArgs_Cons; eassumption.
    + constructor; assumption.
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 fields f rest e v values Hlookup Heval_e IHe
      Heval_fields IHfields x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s.
    assert (Hready_e : preservation_ready_expr e).
    { eapply preservation_ready_fields_lookup; eassumption. }
    assert (Hfree_e : ~ In x (free_vars_expr e)).
    { eapply fields_free_vars_ts_lookup_notin; eassumption. }
    assert (Hlocal_e : ~ In x (expr_local_store_names e)).
    { eapply fields_local_store_names_lookup_notin; eassumption. }
    destruct (IHe x T hidden s_base eq_refl Hready_e Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    subst s1.
    destruct (IHfields x T hidden s1_base eq_refl Hready Hfree Hlocal Hrefs1)
      as [s2_base [Hs2 [Heval_fields_base [Hrefs2 Hvalues]]]].
    exists s2_base. repeat split; try assumption.
    + subst s2. eapply EvalStructFields_Cons; eassumption.
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
  destruct hidden_frame_eval_strip_mutual as [_ [Hargs _]].
  eapply (Hargs env (store_add x T hidden s) args s_hidden' vs Heval
            x T hidden s eq_refl); eassumption.
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
