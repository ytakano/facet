From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming TypingRules RootProvenance TypeChecker.
From Stdlib Require Import List String.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Context shadowing summaries                                          *)
(* ------------------------------------------------------------------ *)

Definition sctx_no_shadow (Σ : sctx) : Prop :=
  NoDup (ctx_names Σ).

Lemma sctx_lookup_not_in_names :
  forall x Σ,
    ~ In x (ctx_names Σ) ->
    sctx_lookup x Σ = None.
Proof.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hnotin;
    simpl in *; try reflexivity.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exfalso. apply Hnotin. left. reflexivity.
  - apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma sctx_lookup_none_not_in_names :
  forall x Σ,
    sctx_lookup x Σ = None ->
    ~ In x (ctx_names Σ).
Proof.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hlookup Hin;
    simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y. rewrite ident_eqb_refl in Hlookup. discriminate.
    + destruct (ident_eqb x y); try discriminate.
      eapply IH; eassumption.
Qed.

Lemma sctx_no_shadow_add :
  forall x T m Σ,
    sctx_no_shadow Σ ->
    sctx_lookup x Σ = None ->
    sctx_no_shadow (sctx_add x T m Σ).
Proof.
  unfold sctx_no_shadow, sctx_add, ctx_add.
  intros x T m Σ Hnodup Hlookup.
  simpl. constructor.
  - eapply sctx_lookup_none_not_in_names. exact Hlookup.
  - exact Hnodup.
Qed.

Lemma sctx_no_shadow_remove :
  forall x Σ,
    sctx_no_shadow Σ ->
    sctx_no_shadow (sctx_remove x Σ).
Proof.
  unfold sctx_no_shadow, sctx_remove.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hnodup;
    simpl in *.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct (ident_eqb x y).
    + exact Hnodup_tail.
    + simpl. constructor.
      * intros Hin. apply Hnotin.
        clear -Hin.
        induction rest as [| [[[z Tz] stz] mz] rest IHrest];
          simpl in *.
        -- contradiction.
        -- destruct (ident_eqb x z) eqn:Heq.
           ++ apply ident_eqb_eq in Heq. subst z.
              right. exact Hin.
           ++ destruct Hin as [Hin | Hin].
              ** left. exact Hin.
              ** right. apply IHrest. exact Hin.
      * apply IH. exact Hnodup_tail.
Qed.

Lemma sctx_update_state_names :
  forall x f Σ Σ',
    sctx_update_state x f Σ = Some Σ' ->
    ctx_names Σ' = ctx_names Σ.
Proof.
  intros x f Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Σ' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - inversion Hupdate; subst. reflexivity.
  - destruct (sctx_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst. simpl.
    rewrite (IH rest' eq_refl). reflexivity.
Qed.

Lemma sctx_update_state_no_shadow :
  forall x f Σ Σ',
    sctx_no_shadow Σ ->
    sctx_update_state x f Σ = Some Σ' ->
    sctx_no_shadow Σ'.
Proof.
  unfold sctx_no_shadow.
  intros x f Σ Σ' Hnodup Hupdate.
  rewrite (sctx_update_state_names x f Σ Σ' Hupdate).
  exact Hnodup.
Qed.

Lemma sctx_consume_path_no_shadow :
  forall Σ Σ' x path,
    sctx_no_shadow Σ ->
    sctx_consume_path Σ x path = infer_ok Σ' ->
    sctx_no_shadow Σ'.
Proof.
  intros Σ Σ' x path Hnodup Hconsume.
  unfold sctx_consume_path in Hconsume.
  unfold sctx_path_available in Hconsume.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b st path); try discriminate.
  destruct (sctx_update_state x (state_consume_path path) Σ) as [Σ0 |]
    eqn:Hupdate; try discriminate.
  inversion Hconsume; subst.
  eapply sctx_update_state_no_shadow; eassumption.
Qed.

Lemma sctx_restore_path_no_shadow :
  forall Σ Σ' x path,
    sctx_no_shadow Σ ->
    sctx_restore_path Σ x path = infer_ok Σ' ->
    sctx_no_shadow Σ'.
Proof.
  intros Σ Σ' x path Hnodup Hrestore.
  unfold sctx_restore_path in Hrestore.
  destruct (sctx_update_state x (state_restore_path path) Σ) as [Σ0 |]
    eqn:Hupdate; try discriminate.
  inversion Hrestore; subst.
  eapply sctx_update_state_no_shadow; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Wrapper-free env/stateful typing specification                       *)
(* ------------------------------------------------------------------ *)

Inductive typed_place_type_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPTES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      typed_place_type_env_structural env Σ (PVar x) T
  | TPTES_Deref : forall p la rk T u,
      typed_place_type_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_type_env_structural env Σ (PDeref p) T
  | TPTES_Field : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      typed_place_type_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).

Inductive typed_place_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      binding_available_b st [] = true ->
      typed_place_env_structural env Σ (PVar x) T
  | TPES_Deref : forall p la rk T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_env_structural env Σ (PDeref p) T
  | TPES_Field : forall p sname lts args sdef fdef x path T_root st T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = Some (x, path) ->
      sctx_lookup x Σ = Some (T_root, st) ->
      binding_available_b st path = true ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef)
  | TPES_Field_Indirect : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = None ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).
Inductive place_under_unique_ref_structural (env : global_env) (Σ : sctx)
    : place -> Prop :=
  | PUURS_Deref : forall p la T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
      place_under_unique_ref_structural env Σ (PDeref p)
  | PUURS_Field : forall p f,
      place_under_unique_ref_structural env Σ p ->
      place_under_unique_ref_structural env Σ (PField p f).

Inductive writable_place_env_structural (env : global_env) (Σ : sctx)
    : place -> Prop :=
  | WPES_Var : forall x,
      sctx_lookup_mut x Σ = Some MMutable ->
      writable_place_env_structural env Σ (PVar x)
  | WPES_Deref : forall p la T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
      writable_place_env_structural env Σ (PDeref p)
  | WPES_Field : forall p sname lts args sdef fdef T_parent,
      writable_place_env_structural env Σ p ->
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      field_mutability fdef = MMutable ->
      writable_place_env_structural env Σ (PField p (field_name fdef)).

(* ------------------------------------------------------------------ *)
(* Context shape preservation                                           *)
(* ------------------------------------------------------------------ *)

Inductive sctx_entry_same_binding : sctx_entry -> sctx_entry -> Prop :=
  | SESB : forall x T st1 st2 m,
      sctx_entry_same_binding (x, T, st1, m) (x, T, st2, m).

Definition sctx_same_bindings (Σ1 Σ2 : sctx) : Prop :=
  Forall2 sctx_entry_same_binding Σ1 Σ2.

Definition sctx_entry_type_eq (ce1 ce2 : sctx_entry) : Prop :=
  match ce1, ce2 with
  | (_, T1, _, _), (_, T2, _, _) => T1 = T2
  end.

Lemma sctx_entry_same_binding_refl :
  forall ce,
    sctx_entry_same_binding ce ce.
Proof.
  intros [[[x T] st] m]. constructor.
Qed.

Lemma sctx_same_bindings_refl :
  forall Σ,
    sctx_same_bindings Σ Σ.
Proof.
  intros Σ.
  induction Σ as [|ce rest IH].
  - constructor.
  - constructor.
    + apply sctx_entry_same_binding_refl.
    + exact IH.
Qed.

Lemma sctx_entry_same_binding_trans :
  forall ce1 ce2 ce3,
    sctx_entry_same_binding ce1 ce2 ->
    sctx_entry_same_binding ce2 ce3 ->
    sctx_entry_same_binding ce1 ce3.
Proof.
  intros [[[x1 T1] st1] m1] [[[x2 T2] st2] m2] [[[x3 T3] st3] m3] H12 H23.
  inversion H12; subst.
  inversion H23; subst.
  constructor.
Qed.

Lemma sctx_same_bindings_trans :
  forall Σ1 Σ2 Σ3,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_same_bindings Σ2 Σ3 ->
    sctx_same_bindings Σ1 Σ3.
Proof.
  intros Σ1 Σ2 Σ3 H12.
  revert Σ3.
  induction H12 as [|ce1 ce2 Σ1_tail Σ2_tail Hhead Htail IH]; intros Σ3 H23.
  - inversion H23; subst. constructor.
  - inversion H23; subst.
    constructor.
    + eapply sctx_entry_same_binding_trans; eassumption.
    + eapply IH.
      match goal with
      | H : Forall2 sctx_entry_same_binding Σ2_tail _ |- _ => exact H
      end.
Qed.

Lemma sctx_entry_same_binding_sym :
  forall ce1 ce2,
    sctx_entry_same_binding ce1 ce2 ->
    sctx_entry_same_binding ce2 ce1.
Proof.
  intros [[[x1 T1] st1] m1] [[[x2 T2] st2] m2] Hsame.
  inversion Hsame; subst.
  constructor.
Qed.

Lemma sctx_same_bindings_sym :
  forall Σ1 Σ2,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_same_bindings Σ2 Σ1.
Proof.
  intros Σ1 Σ2 Hsame.
  induction Hsame as [|ce1 ce2 Σ1_tail Σ2_tail Hhead Htail IH].
  - constructor.
  - constructor.
    + apply sctx_entry_same_binding_sym. exact Hhead.
    + exact IH.
Qed.

Lemma sctx_same_bindings_lookup :
  forall Σ1 Σ2 x T st,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_lookup x Σ1 = Some (T, st) ->
    exists st',
      sctx_lookup x Σ2 = Some (T, st').
Proof.
  intros Σ1 Σ2 x T st Hsame.
  induction Hsame; intros Hlookup.
  - discriminate.
  - destruct H.
    simpl in Hlookup |- *.
    match goal with
    | |- context[ident_eqb x ?y] => destruct (ident_eqb x y) eqn:Hx
    end.
    + inversion Hlookup; subst.
      eexists. reflexivity.
    + eapply IHHsame. exact Hlookup.
Qed.

Lemma sctx_same_bindings_lookup_mut :
  forall Σ1 Σ2 x m,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_lookup_mut x Σ1 = Some m ->
    sctx_lookup_mut x Σ2 = Some m.
Proof.
  intros Σ1 Σ2 x m Hsame.
  induction Hsame; intros Hlookup.
  - discriminate.
  - destruct H.
    simpl in Hlookup |- *.
    match goal with
    | |- context[ident_eqb x ?y] => destruct (ident_eqb x y)
    end; [exact Hlookup |].
    eapply IHHsame. exact Hlookup.
Qed.

Lemma sctx_same_bindings_type_eq :
  forall Σ1 Σ2,
    sctx_same_bindings Σ1 Σ2 ->
    Forall2 sctx_entry_type_eq Σ1 Σ2.
Proof.
  intros Σ1 Σ2 Hsame.
  induction Hsame.
  - constructor.
  - constructor.
    + inversion H; subst. reflexivity.
    + exact IHHsame.
Qed.

Lemma sctx_same_bindings_common_type_eq :
  forall Σ Σ1 Σ2,
    sctx_same_bindings Σ Σ1 ->
    sctx_same_bindings Σ Σ2 ->
    Forall2 sctx_entry_type_eq Σ1 Σ2.
Proof.
  intros Σ Σ1 Σ2 Hleft.
  revert Σ2.
  induction Hleft as [|ce ce1 Σ_tail Σ1_tail Hhead_left Htail_left IH];
    intros Σ2 Hright.
  - inversion Hright; subst. constructor.
  - inversion Hright as [|ce' ce2 Σ_tail' Σ2_tail Hhead_right Htail_right];
      subst.
    constructor.
    + inversion Hhead_left; subst.
      inversion Hhead_right; subst.
      reflexivity.
    + eapply IH. exact Htail_right.
Qed.

Lemma sctx_update_state_same_bindings :
  forall Σ x f Σ',
    sctx_update_state x f Σ = Some Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  unfold sctx_update_state.
  intros Σ x f.
  induction Σ as [|[[[y T] st] m] rest IH]; intros Σ' Hupdate.
  - discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x y).
    + inversion Hupdate; subst. constructor.
      * constructor.
      * apply sctx_same_bindings_refl.
    + destruct (ctx_update_state x f rest) as [rest' |] eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      constructor.
      * constructor.
      * apply IH. reflexivity.
Qed.

Lemma sctx_consume_path_same_bindings :
  forall Σ x path Σ',
    sctx_consume_path Σ x path = infer_ok Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros Σ x path Σ' Hconsume.
  unfold sctx_consume_path in Hconsume.
  destruct (sctx_path_available Σ x path) as [[] | err]; try discriminate.
  destruct (sctx_update_state x (state_consume_path path) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion Hconsume; subst.
  eapply sctx_update_state_same_bindings. exact Hupdate.
Qed.

Lemma sctx_restore_path_same_bindings :
  forall Σ x path Σ',
    sctx_restore_path Σ x path = infer_ok Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros Σ x path Σ' Hrestore.
  unfold sctx_restore_path in Hrestore.
  destruct (sctx_update_state x (state_restore_path path) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion Hrestore; subst.
  eapply sctx_update_state_same_bindings. exact Hupdate.
Qed.

Lemma sctx_same_bindings_remove_added :
  forall Σ Σ1 Σ2 x T m,
    sctx_same_bindings Σ Σ1 ->
    sctx_same_bindings (sctx_add x T m Σ1) Σ2 ->
    sctx_same_bindings Σ (sctx_remove x Σ2).
Proof.
  intros Σ Σ1 Σ2 x T m Hsame Hadded.
  inversion Hadded; subst.
  inversion H1; subst.
  simpl.
  rewrite ident_eqb_refl.
  eapply sctx_same_bindings_trans; eassumption.
Qed.

Lemma ctx_merge_same_bindings_left :
  forall Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    sctx_same_bindings Σ2 Σ4.
Proof.
  intros Σ2.
  induction Σ2 as [|[[[x T] st2] m] tail2 IH]; intros Σ3 Σ4 Hmerge.
  - destruct Σ3 as [|ce3 tail3]; simpl in Hmerge; try discriminate.
    inversion Hmerge; subst. constructor.
  - destruct Σ3 as [|[[[x3 T3] st3] m3] tail3]; simpl in Hmerge; try discriminate.
    destruct (negb (ident_eqb x x3)) eqn:Hneq; try discriminate.
    destruct (ctx_merge tail2 tail3) as [tail4 |] eqn:Htail; try discriminate.
    destruct (ty_usage T); try (inversion Hmerge; subst; constructor; [constructor | eapply IH; exact Htail]).
    destruct (Bool.eqb (st_consumed st2) (st_consumed st3)); try discriminate.
    inversion Hmerge; subst.
    constructor.
    + constructor.
    + eapply IH. exact Htail.
Qed.

Lemma ctx_merge_same_bindings_right :
  forall Σ2 Σ3 Σ4,
    sctx_same_bindings Σ2 Σ3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    sctx_same_bindings Σ3 Σ4.
Proof.
  intros Σ2 Σ3 Σ4 Hsame Hmerge.
  eapply sctx_same_bindings_trans.
  - apply sctx_same_bindings_sym. exact Hsame.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
Qed.

Inductive typed_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TES_Unit : forall Σ,
      typed_env_structural env Ω n Σ EUnit (MkTy UUnrestricted TUnits) Σ
  | TES_LitInt : forall Σ i,
      typed_env_structural env Ω n Σ (ELit (LInt i)) (MkTy UUnrestricted TIntegers) Σ
  | TES_LitFloat : forall Σ f,
      typed_env_structural env Ω n Σ (ELit (LFloat f)) (MkTy UUnrestricted TFloats) Σ
  | TES_LitBool : forall Σ b,
      typed_env_structural env Ω n Σ (ELit (LBool b)) (MkTy UUnrestricted TBooleans) Σ
  | TES_Var_Copy : forall Σ x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EVar x) T Σ
  | TES_Var_Move : forall Σ Σ' x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EVar x) T Σ'
  | TES_Place_Copy : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ
  | TES_Place_Move : forall Σ Σ' p T x path,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ'
  | TES_Fn : forall Σ fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_structural env Ω n Σ (EFn fname) (fn_value_ty fdef) Σ
  | TES_MakeClosure : forall Σ fname fdef captures captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_structural env Ω n Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ
  | TES_Struct : forall Σ Σ' sname lts args fields sdef,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      typed_fields_env_structural env Ω n lts args Σ fields (struct_fields sdef) Σ' ->
      typed_env_structural env Ω n Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ'
  | TES_Let : forall Σ Σ1 Σ2 m x T T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      ty_compatible_b Ω T1 T = true ->
      typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
      sctx_check_ok env x T Σ2 = true ->
      typed_env_structural env Ω n Σ (ELet m x T e1 e2) T2 (sctx_remove x Σ2)
  | TES_LetInfer : forall Σ Σ1 Σ2 m x T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      typed_env_structural env Ω n (sctx_add x T1 m Σ1) e2 T2 Σ2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      typed_env_structural env Ω n Σ (ELetInfer m x e1 e2) T2 (sctx_remove x Σ2)
  | TES_Drop : forall Σ Σ' e T,
      typed_env_structural env Ω n Σ e T Σ' ->
      typed_env_structural env Ω n Σ (EDrop e) (MkTy UUnrestricted TUnits) Σ'
  | TES_Replace_Path : forall Σ Σ1 Σ2 p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ2
  | TES_Replace_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = None ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ'
  | TES_Assign_Path : forall Σ Σ' p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_Assign_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = None ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_BorrowShared : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_structural env Ω n Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ
  | TES_BorrowUnique : forall Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_BorrowUnique_Indirect : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_Deref_Place : forall Σ r p la rk T u,
      expr_as_place r = Some p ->
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ
  | TES_Deref_Expr : forall Σ Σ' r la rk T u,
      expr_as_place r = None ->
      typed_env_structural env Ω n Σ r (MkTy u (TRef la rk T)) Σ' ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ'
  | TES_If : forall Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3,
      typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
      ty_core T_cond = TBooleans ->
      typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
      typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      typed_env_structural env Ω n Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)) Σ4
  | TES_Call : forall Σ Σ' fname fdef args σ,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_args_env_structural env Ω n Σ args (apply_lt_params σ (fn_params fdef)) Σ' ->
      Forall (fun '(a, b) => outlives Ω a b) (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_structural env Ω n Σ (ECall fname args) (apply_lt_ty σ (fn_ret fdef)) Σ'
  | TES_CallExpr_Fn : forall Σ Σ1 Σ' callee args u param_tys ret,
      typed_env_structural env Ω n Σ callee (MkTy u (TFn param_tys ret)) Σ1 ->
      typed_args_env_structural env Ω n Σ1 args (params_of_tys param_tys) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) ret Σ'
  | TES_CallExpr_Closure : forall Σ Σ1 Σ' callee args u env_lt param_tys ret,
      typed_env_structural env Ω n Σ callee (MkTy u (TClosure env_lt param_tys ret)) Σ1 ->
      typed_args_env_structural env Ω n Σ1 args (params_of_tys param_tys) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) ret Σ'
  | TES_CallExpr_Forall : forall Σ Σ1 Σ' callee args u m bounds body param_tys ret σ,
      typed_env_structural env Ω n Σ callee (MkTy u (TForall m bounds body)) Σ1 ->
      ty_core body = TFn param_tys ret ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) (open_bound_ty σ ret) Σ'
with typed_args_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> sctx -> Prop :=
  | TESArgs_Nil : forall Σ,
      typed_args_env_structural env Ω n Σ [] [] Σ
  | TESArgs_Cons : forall Σ Σ1 Σ2 e es p ps T_e,
      typed_env_structural env Ω n Σ e T_e Σ1 ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_env_structural env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural env Ω n Σ (e :: es) (p :: ps) Σ2
with typed_fields_env_structural
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * expr) -> list field_def -> sctx -> Prop :=
  | TESFields_Nil : forall lts args Σ fields,
      typed_fields_env_structural env Ω n lts args Σ fields [] Σ
  | TESFields_Cons : forall lts args Σ Σ1 Σ2 fields f rest e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_structural env Ω n Σ e_field T_field Σ1 ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_env_structural env Ω n lts args Σ1 fields rest Σ2 ->
      typed_fields_env_structural env Ω n lts args Σ fields (f :: rest) Σ2.

Inductive typed_env_roots (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TER_Unit : forall R Σ,
      typed_env_roots env Ω n R Σ EUnit
        (MkTy UUnrestricted TUnits) Σ R []
  | TER_LitInt : forall R Σ i,
      typed_env_roots env Ω n R Σ (ELit (LInt i))
        (MkTy UUnrestricted TIntegers) Σ R []
  | TER_LitFloat : forall R Σ f,
      typed_env_roots env Ω n R Σ (ELit (LFloat f))
        (MkTy UUnrestricted TFloats) Σ R []
  | TER_LitBool : forall R Σ b,
      typed_env_roots env Ω n R Σ (ELit (LBool b))
        (MkTy UUnrestricted TBooleans) Σ R []
  | TER_Var_Copy : forall R Σ x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EVar x) T Σ R roots
  | TER_Var_Move : forall R Σ Σ' x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EVar x) T Σ' R roots
  | TER_Place_Copy : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EPlace p) T Σ R roots
  | TER_Place_Move : forall R Σ Σ' p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EPlace p) T Σ' R roots
  | TER_Call : forall R R' Σ Σ' fname fdef args σ arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => outlives Ω a b) (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots env Ω n R Σ (ECall fname args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TER_Fn : forall R Σ fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_roots env Ω n R Σ (EFn fname) (fn_value_ty fdef) Σ R []
  | TER_MakeClosure : forall R Σ fname fdef captures captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_roots env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ R []
  | TER_Struct : forall R R' Σ Σ' sname lts args fields sdef roots,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      typed_fields_roots env Ω n lts args R Σ fields (struct_fields sdef) Σ' R' roots ->
      typed_env_roots env Ω n R Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ' R' roots
  | TER_Let : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TER_LetInfer : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TER_Drop : forall R R' Σ Σ' e T roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots env Ω n R Σ (EDrop e)
        (MkTy UUnrestricted TUnits) Σ' R' []
  | TER_Replace_Path : forall R R1 Σ Σ1 Σ2 p e_new T_old T_new
      x path roots_result roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      root_env_lookup x R = Some roots_result ->
      typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_roots env Ω n R Σ (EReplace p e_new) T_old Σ2
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TER_Assign_Path : forall R R1 Σ Σ' p e_new T_old T_new
      x path roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_roots env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TER_BorrowShared : forall R Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_roots env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ R (root_of_place p)
  | TER_BorrowUnique : forall R Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_roots env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ R [RStore x]
  | TER_DerefBorrowShared : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RShared p)) T Σ R roots
  | TER_DerefBorrowUnique : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RUnique p)) T Σ R roots
  | TER_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3,
      typed_env_roots env Ω n R Σ e1 T_cond Σ1 R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
      typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      root_env_equiv R2 R3 ->
      typed_env_roots env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        Σ4 R2 (root_set_union roots2 roots3)
with typed_args_roots (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param -> sctx -> root_env -> list root_set -> Prop :=
  | TERArgs_Nil : forall R Σ,
      typed_args_roots env Ω n R Σ [] [] Σ R []
  | TERArgs_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest,
      typed_env_roots env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_roots env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots env Ω n R Σ (e :: es) (p :: ps) Σ2 R2 (roots :: roots_rest)
with typed_fields_roots
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> root_env -> sctx -> list (string * expr) ->
      list field_def -> sctx -> root_env -> root_set -> Prop :=
  | TERFields_Nil : forall lts args R Σ fields,
      typed_fields_roots env Ω n lts args R Σ fields [] Σ R []
  | TERFields_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields f rest
      e_field T_field roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_roots env Ω n lts args R1 Σ1 fields rest Σ2 R2 roots_rest ->
      typed_fields_roots env Ω n lts args R Σ fields (f :: rest) Σ2 R2
        (root_set_union roots_field roots_rest).

Scheme typed_env_roots_ind' := Induction for typed_env_roots Sort Prop
with typed_args_roots_ind' := Induction for typed_args_roots Sort Prop
with typed_fields_roots_ind' := Induction for typed_fields_roots Sort Prop.
Combined Scheme typed_roots_ind
  from typed_env_roots_ind', typed_args_roots_ind', typed_fields_roots_ind'.

Lemma typed_roots_structural :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    typed_args_env_structural env Ω n Σ args ps Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ').
Proof.
  intros env Ω n.
  apply typed_roots_ind;
    intros; try solve [econstructor; eauto].
  - eapply TES_Deref_Expr.
    + reflexivity.
    + eapply TES_BorrowShared. eassumption.
    + assumption.
  - eapply TES_Deref_Expr.
    + reflexivity.
    + eapply TES_BorrowUnique; eauto.
    + assumption.
Qed.

Lemma typed_env_roots_structural :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_structural env Ω n) R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_structural :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    typed_args_env_structural env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_structural env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_structural :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ'.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj2 (proj2 (typed_roots_structural env Ω n))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Lemma typed_roots_no_shadow :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R').
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros;
    eauto using root_env_no_shadow_add, root_env_no_shadow_remove,
      root_env_no_shadow_update.
Qed.

Lemma typed_env_roots_no_shadow :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_no_shadow env Ω n) R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_no_shadow :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_no_shadow env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_no_shadow :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj2 (proj2 (typed_roots_no_shadow env Ω n))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Theorem typed_roots_instantiate_fresh_mutual :
  forall env Ω n rho,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_env_roots env Ω n R0 Σ e T Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_args_roots env Ω n R0 Σ args ps Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        Forall2 root_set_equiv roots0
          (map (root_set_instantiate rho) roots)) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_fields_roots env Ω n lts args R0 Σ fields defs Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)).
Proof.
  intros env Ω n rho.
  apply typed_roots_ind.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ i Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ f Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ b Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ x T roots Hplace Husage Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Var_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' x T roots Hplace Husage Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Var_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Place_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' p T x path roots Hplace Husage Hpath Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Place_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R' Σ Σ' fname fdef args σ arg_roots Hin Hfname Hcaps
      Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TER_Call; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R Σ fname fdef Hin Hfname Hcaps Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TER_Fn; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures captured_tys Hin Hfname Hcaptures
      Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TER_MakeClosure; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R R' Σ Σ' sname lts args fields sdef roots Hlookup Hlen_lts
      Hlen_args Hbounds Hfields IHfields Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_struct in Hfresh.
    destruct (IHfields Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [Hfields0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', roots0. split; [| split; [| split]].
    + eapply TER_Struct; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + exact Hroots0.
  - intros R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hcompat Hlookup_none He2 IHe2 Hcheck
      Hexcl_roots Hexcl_env Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - exact He2.
      - apply root_env_no_shadow_add; assumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TER_Let.
      * exact He10.
      * exact Hcompat.
      * exact Hlookup_R10_none.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hlookup_none He2 IHe2 Hcheck
      Hexcl_roots Hexcl_env Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - exact He2.
      - apply root_env_no_shadow_add; assumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TER_LetInfer.
      * exact He10.
      * exact Hlookup_R10_none.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R' Σ Σ' e T roots He IHe Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [He0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', []. split; [| split; [| split]].
    + apply TER_Drop with (T := T) (roots := roots0). exact He0.
    + exact HnsR0'.
    + exact HR0'.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ1 Σ2 p e_new T_old T_new x path roots_result
      roots_old roots_new Hplace Hpath Hwritable Hlookup_result He_new IHe_new
      Hlookup_old Hcompat Havailable Hrestore Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TER_Replace_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ' p e_new T_old T_new x path roots_old roots_new
      Hplace Husage Hpath Hwritable He_new IHe_new Hlookup_old Hcompat
      Havailable Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TER_Assign_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R Σ p T Hplace Hfresh R0 HnsR HnsR0 HR0.
    exists R0, (root_of_place p). split; [| split; [| split]].
    + constructor. exact Hplace.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_root_of_place_equiv.
  - intros R Σ p T x path Hplace Hpath Hmut Hfresh R0 HnsR HnsR0 HR0.
    exists R0, [RStore x]. split; [| split; [| split]].
    + eapply TER_BorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_store_singleton_equiv.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowShared; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hmut Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3
      roots_cond roots2 roots3 He1 IHe1 Hcond He2 IHe2 He3 IHe3 Hcore
      Hmerge HR23 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1)
      (expr_local_store_names e2 ++ expr_local_store_names e3) rho
      Hfresh) as [Hfresh1 Hfresh23].
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e2) (expr_local_store_names e3) rho
      Hfresh23) as [Hfresh2 Hfresh3].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots_cond0 [He10 [HnsR10 [HR10 Hroots_cond0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHe2 Hfresh2 R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    destruct (IHe3 Hfresh3 R10 Hns_R1 HnsR10 HR10)
      as [R30 [roots30 [He30 [HnsR30 [HR30 Hroots30]]]]].
    exists R20, (root_set_union roots20 roots30). split; [| split; [| split]].
    + eapply TER_If; eauto.
      eapply root_env_equiv_trans.
      * exact HR20.
      * eapply root_env_equiv_trans.
        -- apply root_env_equiv_instantiate. exact HR23.
        -- apply root_env_equiv_sym. exact HR30.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + constructor.
  - intros R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest
      He IHe Hcompat Hes IHes Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_args_cons_inv
      e es rho Hfresh) as [Hfresh_e Hfresh_es].
    destruct (IHe Hfresh_e R0 HnsR HnsR0 HR0)
      as [R10 [roots0 [He0 [HnsR10 [HR10 Hroots0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHes Hfresh_es R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hes0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (roots0 :: roots_rest0). split; [| split; [| split]].
    + eapply TERArgs_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + constructor; assumption.
  - intros lts args R Σ fields Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros lts args R R1 R2 Σ Σ1 Σ2 fields f rest e_field T_field
      roots_field roots_rest Hlookup He_field IHe_field Hcompat Hfields IHfields
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hfresh_field :
      root_subst_images_exclude_names (expr_local_store_names e_field) rho).
    { unfold lookup_field_b in Hlookup.
      clear Hfields IHfields.
      induction fields as [| [field_name0 e0] fields IH]; simpl in *;
        try discriminate.
      destruct (String.eqb (field_name f) field_name0) eqn:Hfield.
      - inversion Hlookup. subst e0.
        apply root_subst_images_exclude_names_app_inv in Hfresh.
        exact (proj1 Hfresh).
      - apply IH.
        + exact Hlookup.
        + apply root_subst_images_exclude_names_app_inv in Hfresh.
          exact (proj2 Hfresh). }
    destruct (IHe_field Hfresh_field R0 HnsR HnsR0 HR0)
      as [R10 [roots_field0 [He_field0 [HnsR10 [HR10 Hroots_field0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHfields Hfresh R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hfields0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (root_set_union roots_field0 roots_rest0). split; [| split; [| split]].
    + eapply TERFields_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
Qed.

Lemma typed_env_roots_instantiate_fresh :
  forall env Ω n rho R Σ e T Σ' R' roots R0,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_env_roots env Ω n R0 Σ e T Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho R Σ e T Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (typed_roots_instantiate_fresh_mutual env Ω n rho)
    R Σ e T Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_args_roots_instantiate_fresh :
  forall env Ω n rho R Σ args ps Σ' R' roots R0,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_args_roots env Ω n R0 Σ args ps Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      Forall2 root_set_equiv roots0 (map (root_set_instantiate rho) roots).
Proof.
  intros env Ω n rho R Σ args ps Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (typed_roots_instantiate_fresh_mutual env Ω n rho))
    R Σ args ps Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_fields_roots_instantiate_fresh :
  forall env Ω n rho lts args R Σ fields defs Σ' R' roots R0,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_fields_roots env Ω n lts args R0 Σ fields defs Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho lts args R Σ fields defs Σ' R' roots R0
    Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj2 (proj2 (typed_roots_instantiate_fresh_mutual env Ω n rho))
    lts args R Σ fields defs Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_env_structural_same_bindings :
  forall env Ω n Σ e T Σ',
    typed_env_structural env Ω n Σ e T Σ' ->
    sctx_same_bindings Σ Σ'
with typed_args_env_structural_same_bindings :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural env Ω n Σ args ps Σ' ->
    sctx_same_bindings Σ Σ'
with typed_fields_env_structural_same_bindings :
  forall env Ω n lts args Σ fields defs Σ',
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  - intros env Ω n Σ e T Σ' Htyped.
    induction Htyped.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + eapply sctx_consume_path_same_bindings.
      match goal with
      | H : sctx_consume_path _ _ [] = infer_ok _ |- _ => exact H
      end.
    + apply sctx_same_bindings_refl.
    + eapply sctx_consume_path_same_bindings.
      match goal with
      | H : sctx_consume_path _ _ _ = infer_ok _ |- _ => exact H
      end.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + eapply typed_fields_env_structural_same_bindings.
      match goal with
      | H : typed_fields_env_structural _ _ _ _ _ _ _ _ _ |- _ => exact H
      end.
    + eapply sctx_same_bindings_remove_added.
      * exact IHHtyped1.
      * exact IHHtyped2.
    + eapply sctx_same_bindings_remove_added.
      * exact IHHtyped1.
      * exact IHHtyped2.
    + exact IHHtyped.
    + eapply sctx_same_bindings_trans.
      * exact IHHtyped.
      * eapply sctx_restore_path_same_bindings.
        match goal with
        | H : sctx_restore_path _ _ _ = infer_ok _ |- _ => exact H
        end.
    + exact IHHtyped.
    + exact IHHtyped.
    + exact IHHtyped.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + exact IHHtyped.
    + eapply sctx_same_bindings_trans.
      * eapply sctx_same_bindings_trans.
        -- exact IHHtyped1.
        -- exact IHHtyped2.
      * eapply ctx_merge_same_bindings_left.
        match goal with
        | H : ctx_merge _ _ = Some _ |- _ => exact H
        end.
    + eapply typed_args_env_structural_same_bindings.
      match goal with
      | H : typed_args_env_structural _ _ _ _ _ _ _ |- _ => exact H
      end.
    + eapply sctx_same_bindings_trans.
      * exact IHHtyped.
      * eapply typed_args_env_structural_same_bindings.
        match goal with
        | H : typed_args_env_structural _ _ _ _ _ _ _ |- _ => exact H
        end.
    + eapply sctx_same_bindings_trans.
      * exact IHHtyped.
      * eapply typed_args_env_structural_same_bindings.
        match goal with
        | H : typed_args_env_structural _ _ _ _ _ _ _ |- _ => exact H
        end.
	    + eapply sctx_same_bindings_trans.
	      * exact IHHtyped.
	      * eapply typed_args_env_structural_same_bindings.
        match goal with
        | H : typed_args_env_structural _ _ _ _ _ _ _ |- _ => exact H
        end.
  - intros env Ω n Σ args ps Σ' Htyped.
    induction Htyped.
    + apply sctx_same_bindings_refl.
    + eapply sctx_same_bindings_trans.
      * eapply typed_env_structural_same_bindings. exact H.
      * exact IHHtyped.
  - intros env Ω n lts args Σ fields defs Σ' Htyped.
    induction Htyped.
    + apply sctx_same_bindings_refl.
    + eapply sctx_same_bindings_trans.
      * eapply typed_env_structural_same_bindings. exact H0.
      * exact IHHtyped.
Qed.

Lemma typed_env_structural_branch_type_eq :
  forall env Ω n Σ e2 T2 Σ2 e3 T3 Σ3,
    typed_env_structural env Ω n Σ e2 T2 Σ2 ->
    typed_env_structural env Ω n Σ e3 T3 Σ3 ->
    Forall2 sctx_entry_type_eq Σ2 Σ3.
Proof.
  intros env Ω n Σ e2 T2 Σ2 e3 T3 Σ3 Htyped_left Htyped_right.
  eapply sctx_same_bindings_common_type_eq.
  - eapply typed_env_structural_same_bindings. exact Htyped_left.
  - eapply typed_env_structural_same_bindings. exact Htyped_right.
Qed.

Inductive borrow_ok_env_structural (env : global_env)
    : path_borrow_state -> ctx -> expr -> path_borrow_state -> Prop :=
  | BOES_Unit : forall PBS Γ,
      borrow_ok_env_structural env PBS Γ EUnit PBS
  | BOES_Lit : forall PBS Γ l,
      borrow_ok_env_structural env PBS Γ (ELit l) PBS
  | BOES_Var : forall PBS Γ x,
      borrow_check_place_access env PBS Γ (PVar x) = infer_ok tt ->
      borrow_ok_env_structural env PBS Γ (EVar x) PBS
  | BOES_Fn : forall PBS Γ fname,
      borrow_ok_env_structural env PBS Γ (EFn fname) PBS
  | BOES_MakeClosure : forall PBS Γ fname captures,
      Forall (fun x => pbs_has_mut x [] PBS = false) captures ->
      borrow_ok_env_structural env PBS Γ (EMakeClosure fname captures) PBS
  | BOES_Place : forall PBS Γ p,
      borrow_check_place_access env PBS Γ p = infer_ok tt ->
      borrow_ok_env_structural env PBS Γ (EPlace p) PBS
  | BOES_Struct : forall PBS PBS' Γ sname lts args fields,
      borrow_ok_fields_env_structural env PBS Γ fields PBS' ->
      borrow_ok_env_structural env PBS Γ (EStruct sname lts args fields) PBS'
  | BOES_BorrowShared : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_mut x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RShared p) (PBShared x path :: PBS)
  | BOES_BorrowUnique : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RUnique p) (PBMut x path :: PBS)
  | BOES_Write : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EReplace p e_new) PBS'
  | BOES_Assign : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EAssign p e_new) PBS'
  | BOES_Deref : forall PBS PBS' Γ e,
      match expr_ref_root e with
      | Some r => pbs_has_mut r [] PBS = false
      | None => True
      end ->
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDeref e) PBS'
  | BOES_Drop : forall PBS PBS' Γ e,
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDrop e) PBS'
  | BOES_Let : forall PBS PBS1 PBS2 Γ m x T e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 (ctx_add_b x T m Γ) e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELet m x T e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_LetInfer : forall PBS PBS1 PBS2 Γ m x e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELetInfer m x e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_If : forall PBS PBS1 PBS2 PBS3 Γ e1 e2 e3,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS1 Γ e3 PBS3 ->
      PBS2 = PBS3 ->
      borrow_ok_env_structural env PBS Γ (EIf e1 e2 e3) PBS2
  | BOES_Call : forall PBS PBS' Γ fname args,
      borrow_ok_args_env_structural env PBS Γ args PBS' ->
      borrow_ok_env_structural env PBS Γ (ECall fname args) PBS'
  | BOES_CallExpr : forall PBS PBS1 PBS2 Γ callee args,
      borrow_ok_env_structural env PBS Γ callee PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ args PBS2 ->
      borrow_ok_env_structural env PBS Γ (ECallExpr callee args) PBS2
with borrow_ok_args_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list expr -> path_borrow_state -> Prop :=
  | BOESArgs_Nil : forall PBS Γ,
      borrow_ok_args_env_structural env PBS Γ [] PBS
  | BOESArgs_Cons : forall PBS PBS1 PBS2 Γ e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_args_env_structural env PBS Γ (e :: rest) PBS2
with borrow_ok_fields_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list (string * expr) -> path_borrow_state -> Prop :=
  | BOESFields_Nil : forall PBS Γ,
      borrow_ok_fields_env_structural env PBS Γ [] PBS
  | BOESFields_Cons : forall PBS PBS1 PBS2 Γ name e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_fields_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_fields_env_structural env PBS Γ ((name, e) :: rest) PBS2.

Definition typed_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  exists T_body Γ_out,
    typed_env_structural env (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Γ_out) /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Γ_out = true.

Definition env_fns_typed_structural (env : global_env) : Prop :=
  forall f, In f (env_fns env) -> typed_fn_env_structural env f.

Definition checked_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  typed_fn_env_structural env f /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Definition env_fns_checked_structural (env : global_env) : Prop :=
  forall f, In f (env_fns env) -> checked_fn_env_structural env f.

Lemma checked_fn_env_structural_typed :
  forall env f,
    checked_fn_env_structural env f ->
    typed_fn_env_structural env f.
Proof.
  intros env f Hchecked.
  exact (proj1 Hchecked).
Qed.

Lemma checked_fn_env_structural_params_nodup :
  forall env f,
    checked_fn_env_structural env f ->
    NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f Hchecked.
  exact (proj2 (proj2 Hchecked)).
Qed.

Lemma env_fns_checked_structural_typed :
  forall env,
    env_fns_checked_structural env ->
    env_fns_typed_structural env.
Proof.
  intros env Hchecked f Hin.
  apply checked_fn_env_structural_typed.
  apply Hchecked. exact Hin.
Qed.
