From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootsReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_param_prefix_remove_non_param :
  forall ps s_param s x,
    store_param_prefix ps s_param s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_param_prefix ps (store_remove x s_param) (store_remove x s).
Proof.
  intros ps s_param s x Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH]; intros Hnotin.
  - constructor.
  - simpl in Hnotin.
    simpl.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin. left. reflexivity.
    + constructor. apply IH.
      intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_param_scope_remove_non_param :
  forall ps s_param s x,
    store_param_scope ps s_param s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    exists frame',
      store_param_scope ps (store_remove x s_param) frame'.
Proof.
  intros ps s_param s x Hscope Hnotin.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH].
  - exists (store_remove x s).
    constructor.
    eapply store_param_prefix_remove_non_param; eassumption.
  - simpl.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + exists s. exact Hscope_tail.
    + destruct (IH Hnotin) as [frame' Hscope'].
      exists frame'.
      constructor; assumption.
Qed.


Lemma store_param_prefix_update_state :
  forall ps s_param s x f s',
    store_param_prefix ps s_param s ->
    store_update_state x f s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x f s' Hprefix.
  revert x f s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x f s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_state x f s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x f s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_mark_used :
  forall ps s_param s x,
    store_param_prefix ps s_param s ->
    exists frame',
      store_param_prefix ps (store_mark_used x s_param) frame'.
Proof.
  intros ps s_param s x Hprefix.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH].
  - exists (store_mark_used x s). constructor.
  - simpl.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + exists s. constructor. exact Hprefix_tail.
    + destruct IH as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_update_val :
  forall ps s_param s x v_new s',
    store_param_prefix ps s_param s ->
    store_update_val x v_new s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x v_new s' Hprefix.
  revert x v_new s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x v_new s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_val x v_new s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x v_new s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_update_path :
  forall ps s_param s x path v_new s',
    store_param_prefix ps s_param s ->
    store_update_path x path v_new s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path v_new s' Hprefix.
  revert x path v_new s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x path v_new s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + destruct (value_update_path v path v_new) as [v' |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x path v_new s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_restore_path :
  forall ps s_param s x path s',
    store_param_prefix ps s_param s ->
    store_restore_path x path s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path s' Hprefix Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_param_prefix_update_state; eassumption.
Qed.

Lemma store_param_prefix_consume_path :
  forall ps s_param s x path s',
    store_param_prefix ps s_param s ->
    store_consume_path x path s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path s' Hprefix Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_param_prefix_update_state; eassumption.
Qed.

Lemma store_param_scope_update_state :
  forall ps s_param s x f s',
    store_param_scope ps s_param s ->
    store_update_state x f s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x f s' Hscope.
  revert x f s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x f s' Hupdate.
  - destruct (store_param_prefix_update_state
      ps s_param s x f s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_state x f s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x f s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_mark_used :
  forall ps s_param s x,
    store_param_scope ps s_param s ->
    exists frame',
      store_param_scope ps (store_mark_used x s_param) frame'.
Proof.
  intros ps s_param s x Hscope.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH].
  - destruct (store_param_prefix_mark_used
      ps s_param s x Hprefix) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + exists s. constructor; assumption.
    + destruct IH as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_update_val :
  forall ps s_param s x v_new s',
    store_param_scope ps s_param s ->
    store_update_val x v_new s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x v_new s' Hscope.
  revert x v_new s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x v_new s' Hupdate.
  - destruct (store_param_prefix_update_val
      ps s_param s x v_new s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_val x v_new s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x v_new s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_update_path :
  forall ps s_param s x path v_new s',
    store_param_scope ps s_param s ->
    store_update_path x path v_new s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path v_new s' Hscope.
  revert x path v_new s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x path v_new s' Hupdate.
  - destruct (store_param_prefix_update_path
      ps s_param s x path v_new s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + destruct (value_update_path (se_val se) path v_new) as [v' |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x path v_new s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_restore_path :
  forall ps s_param s x path s',
    store_param_scope ps s_param s ->
    store_restore_path x path s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path s' Hscope Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_param_scope_update_state; eassumption.
Qed.

Lemma store_param_scope_consume_path :
  forall ps s_param s x path s',
    store_param_scope ps s_param s ->
    store_consume_path x path s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path s' Hscope Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_param_scope_update_state; eassumption.
Qed.

Theorem eval_preserves_param_scope_roots_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
          ps frame,
        provenance_ready_expr e ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
          ps frame,
        provenance_ready_args args ->
        typed_args_roots env Ω n R Σ args params Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
          ps frame,
        provenance_ready_fields fields ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s i Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s f Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s b Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover Hscope.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst.
    all: split; [exact Hcover | eapply store_param_scope_mark_used; exact Hscope].
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      ps frame Hready Htyped Hcover Hscope.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: split; [exact Hcover | eapply store_param_scope_consume_path; eassumption].
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hscope.
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
          Hready_fields Htyped_fields Hcover Hscope)
    end.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IHargs Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
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
          Hready_args Htyped_args Hcover Hscope)
    end.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IH1 Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption) Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    pose proof (root_env_covers_params_lookup_none_not_in
                  ps _ x Hcover1 ltac:(eassumption)) as Hnotin.
    pose proof (root_env_covers_params_add
                  ps _ x roots1 Hcover1) as Hcover_add.
    pose proof (store_param_scope_add
                  ps s1 frame1 x T_ann v1 Hnotin Hscope1) as Hscope_add.
    destruct (IH2 Ω n _ _ _ _ _ _ ps frame1
                ltac:(eassumption) ltac:(eassumption)
                Hcover_add Hscope_add)
      as [Hcover2 [frame2 Hscope2]].
    split.
    + eapply root_env_covers_params_remove_non_param; eassumption.
    + eapply store_param_scope_remove_non_param; eassumption.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        exact (IH Ω n R Σ T_e Σ' R' roots_e ps frame
                 Hready_e Htyped_e Hcover Hscope)
    end.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_val
                    ps s1 frame1 x v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        destruct (store_param_scope_restore_path
                    ps s2 frame2 x [] s3 Hscope2 Hrestore)
          as [frame3 Hscope3];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame3; exact Hscope3 ]
    end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_val
                    ps s1 frame1 x v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame2; exact Hscope2 ]
    end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_path
                    ps s1 frame1 x_eval path_eval v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        destruct (store_param_scope_restore_path
                    ps s2 frame2 x_eval path_eval s3 Hscope2 Hrestore)
          as [frame3 Hscope3];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame3; exact Hscope3 ]
    end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_path
                    ps s1 frame1 x_eval path_eval v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame2; exact Hscope2 ]
    end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame Hready _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Heval_r; subst.
    inversion Htyped; subst;
      try solve [split; [exact Hcover | exists frame; exact Hscope]].
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 Htyped1 Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    exact (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2 ps frame1
             Hready2 Htyped2 Hcover1 Hscope1).
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 Htyped1 Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3 ps frame1
                Hready3 Htyped3 Hcover1 Hscope1)
      as [Hcover3 [frame3 Hscope3]].
    split.
	    + eapply root_env_covers_params_equiv.
	      * apply root_env_equiv_sym. exact H2.
	      * exact Hcover3.
	    + exists frame3. exact Hscope3.
  - intros s s_scrut s' scrut branches enum_name variant_name e_branch v
      Heval_scrut IHscrut Hlookup Heval_branch IHbranch
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped _ _.
    inversion Hready; subst. inversion Htyped.
		  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
		      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
		      roots ps frame Hready _ _ _.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args0 vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ
	      T Σ' R' roots ps frame Hready _ _ _.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
	      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Ω n R Σ T Σ' R' roots ps frame Hready _ _ _.
    inversion Hready.
  - intros s Ω n R Σ params Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ params Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?params_rest
        ?Σ2 ?R2 ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e ps frame
                    Hready_e Htyped_e Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        exact (IHrest Ω n R1 Σ1 params_rest Σ' R' roots_rest ps frame1
                 Hready_rest Htyped_rest Hcover1 Hscope1)
    end.
  - intros s Ω n lts args0 R Σ Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    destruct (typed_fields_roots_cons_inv_ts env Ω n lts args0 R Σ
                fields f rest Σ' R' roots Htyped)
      as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
    rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
    rewrite Hlookup_typed in Hlookup_expr.
    inversion Hlookup_expr; subst e_field.
    destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                Hready_field Htyped_field Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    exact (IHrest Ω n lts args0 R1 Σ1 Σ' R' roots_rest ps frame1
             Hready Htyped_rest Hcover1 Hscope1).
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0'
      roots0 ps0 frame0 Hready Htyped Hcover Hscope.
    destruct (Hmut env0) as [Hexpr [_ _]].
    destruct (Hexpr s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0'
                roots0 ps0 frame0 Hready Htyped Hcover Hscope)
      as [_ Hscope'].
    exact Hscope'.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 params0
        Σ0' R0' roots0 ps0 frame0 Hready Htyped Hcover Hscope.
      destruct (Hmut env0) as [_ [Hargs _]].
      destruct (Hargs s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 params0
                  Σ0' R0' roots0 ps0 frame0 Hready Htyped Hcover Hscope)
        as [_ Hscope'].
      exact Hscope'.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 ps0 frame0 Hready Htyped
        Hcover Hscope.
      destruct (Hmut env0) as [_ [_ Hfields]].
      destruct (Hfields s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
                  args0 R0 Σ0 Σ0' R0' roots0 ps0 frame0 Hready Htyped
                  Hcover Hscope)
        as [_ Hscope'].
      exact Hscope'.
Qed.
