From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition expr_local_no_shadow_from (Γ : sctx) (e : expr) : Prop :=
  NoDup (ctx_names Γ ++ expr_local_store_names e).

Definition args_local_no_shadow_from (Γ : sctx) (args : list expr) : Prop :=
  NoDup (ctx_names Γ ++ args_local_store_names args).

Definition fields_local_no_shadow_from
    (Γ : sctx) (fields : list (string * expr)) : Prop :=
  NoDup (ctx_names Γ ++ fields_local_store_names fields).

Lemma apply_lt_lifetime_nil_ts :
  forall l,
    apply_lt_lifetime [] l = l.
Proof.
  intros l. destruct l as [| i | i]; simpl; try reflexivity.
  induction i as [| i IH]; simpl; try reflexivity.
Qed.

Lemma apply_lt_outlives_nil_ts :
  forall Ω,
    apply_lt_outlives [] Ω = Ω.
Proof.
  unfold apply_lt_outlives.
  induction Ω as [| [a b] Ω IH]; cbn [map].
  - reflexivity.
  - rewrite !apply_lt_lifetime_nil_ts. rewrite IH. reflexivity.
Qed.

Lemma apply_lt_ty_nil_ts :
  forall T,
    apply_lt_ty [] T = T.
Proof.
  fix IH 1.
  intros [u core].
  destruct core; cbn [apply_lt_ty]; try reflexivity.
  - assert (Hlts : map (apply_lt_lifetime []) l = l).
    { induction l as [| lt l IHl]; cbn [map].
      - reflexivity.
      - rewrite apply_lt_lifetime_nil_ts. rewrite IHl. reflexivity. }
    assert (Hargs :
      (fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty [] x :: map_lt xs'
        end) l0 = l0).
    { induction l0 as [| T l0 IHl]; simpl.
      - reflexivity.
      - rewrite IH. rewrite IHl. reflexivity. }
    rewrite Hlts. rewrite Hargs. reflexivity.
  - assert (Hargs :
      (fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty [] x :: map_lt xs'
        end) l = l).
    { induction l as [| T l IHl]; simpl.
      - reflexivity.
      - rewrite IH. rewrite IHl. reflexivity. }
    rewrite Hargs. rewrite IH. reflexivity.
  - assert (Hargs :
      (fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty [] x :: map_lt xs'
        end) l0 = l0).
    { induction l0 as [| T l0 IHl]; simpl.
      - reflexivity.
      - rewrite IH. rewrite IHl. reflexivity. }
    rewrite apply_lt_lifetime_nil_ts. rewrite Hargs. rewrite IH.
    reflexivity.
	  - rewrite apply_lt_outlives_nil_ts. rewrite IH. reflexivity.
		  - assert (Hbounds :
		      map (map_core_trait_bound (apply_lt_ty [])) l = l).
		    { induction l as [| b bs IHbs]; simpl; try reflexivity.
		      destruct b as [idx refs]; simpl.
		      assert (Hrefs :
		        map (map_core_trait_ref (apply_lt_ty [])) refs = refs).
			      { induction refs as [| tr refs IHrefs]; cbn [map]; try reflexivity.
			        destruct tr as [name args].
			        cbn [map_core_trait_ref core_trait_ref_name core_trait_ref_args].
			        assert (Hargs : map (apply_lt_ty []) args = args).
			        { induction args as [| T Ts IHTs]; cbn [map]; try reflexivity.
			          rewrite IH, IHTs. reflexivity. }
			        change (MkCoreTraitRef Ty name (map (apply_lt_ty []) args)
			                  :: map (map_core_trait_ref (apply_lt_ty [])) refs =
			                MkCoreTraitRef Ty name args :: refs).
			        rewrite Hargs. f_equal. exact IHrefs. }
			      change (MkCoreTraitBound Ty idx
			                (map (map_core_trait_ref (apply_lt_ty [])) refs)
			              :: map (map_core_trait_bound (apply_lt_ty [])) bs =
			              MkCoreTraitBound Ty idx refs :: bs).
			      rewrite Hrefs. f_equal. exact IHbs. }
		    rewrite Hbounds. rewrite IH. reflexivity.
	  - rewrite apply_lt_lifetime_nil_ts. rewrite IH. reflexivity.
Qed.

Lemma NoDup_app_remove_middle_ts : forall (xs ys zs : list ident),
  NoDup (xs ++ ys ++ zs) ->
  NoDup (xs ++ zs).
Proof.
  intros xs ys zs Hnodup.
  induction xs as [| x xs IH]; simpl in *.
  - eapply NoDup_app_right_ts. exact Hnodup.
  - inversion Hnodup; subst.
    constructor.
    + intro Hin.
      apply H1. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. apply in_or_app. right. exact Hin.
    + apply IH. exact H2.
Qed.

Lemma NoDup_app_middle_fresh_ts : forall (xs ys : list ident) x,
  NoDup (xs ++ x :: ys) ->
  ~ In x xs.
Proof.
  intros xs ys x Hnodup Hin.
  induction xs as [| y xs IH]; simpl in *.
  - contradiction.
  - inversion Hnodup; subst.
    destruct Hin as [Heq | Hin].
    + subst y. apply H1. apply in_or_app. right. simpl. left. reflexivity.
    + apply IH.
      * exact H2.
      * exact Hin.
Qed.

Lemma NoDup_app_middle_cons_ts : forall (xs ys : list ident) x,
  NoDup (xs ++ x :: ys) ->
  NoDup (x :: xs ++ ys).
Proof.
  intros xs ys x Hnodup.
  constructor.
  - intro Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply NoDup_app_middle_fresh_ts; eassumption.
    + pose proof (NoDup_app_right_ts xs (x :: ys) Hnodup) as Htail.
      inversion Htail; subst. contradiction.
  - eapply (NoDup_app_remove_middle_ts xs [x] ys). exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_same_bindings :
  forall Γ Γ' e,
    sctx_same_bindings Γ Γ' ->
    expr_local_no_shadow_from Γ e ->
    expr_local_no_shadow_from Γ' e.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ Γ' e Hsame Hnodup.
  rewrite (sctx_same_bindings_names_alpha Γ Γ' Hsame).
  exact Hnodup.
Qed.

Lemma args_local_no_shadow_from_same_bindings :
  forall Γ Γ' args,
    sctx_same_bindings Γ Γ' ->
    args_local_no_shadow_from Γ args ->
    args_local_no_shadow_from Γ' args.
Proof.
  unfold args_local_no_shadow_from.
  intros Γ Γ' args Hsame Hnodup.
  rewrite (sctx_same_bindings_names_alpha Γ Γ' Hsame).
  exact Hnodup.
Qed.

Lemma fields_local_no_shadow_from_same_bindings :
  forall Γ Γ' fields,
    sctx_same_bindings Γ Γ' ->
    fields_local_no_shadow_from Γ fields ->
    fields_local_no_shadow_from Γ' fields.
Proof.
  unfold fields_local_no_shadow_from.
  intros Γ Γ' fields Hsame Hnodup.
  rewrite (sctx_same_bindings_names_alpha Γ Γ' Hsame).
  exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_let_init :
  forall Γ m x T e1 e2,
    expr_local_no_shadow_from Γ (ELet m x T e1 e2) ->
    expr_local_no_shadow_from Γ e1.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ m x T e1 e2 Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_left_ts. exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_let_binder_fresh_prefix :
  forall Γ m x T e1 e2,
    expr_local_no_shadow_from Γ (ELet m x T e1 e2) ->
    ~ In x (ctx_names Γ ++ expr_local_store_names e1).
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ m x T e1 e2 Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_middle_fresh_ts. exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_let_body :
  forall Γ Γ1 m x T e1 e2,
    sctx_same_bindings Γ Γ1 ->
    expr_local_no_shadow_from Γ (ELet m x T e1 e2) ->
    expr_local_no_shadow_from (sctx_add x T m Γ1) e2.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ Γ1 m x T e1 e2 Hsame Hnodup.
  simpl in Hnodup |- *.
  rewrite (sctx_same_bindings_names_alpha Γ Γ1 Hsame).
  simpl in Hnodup.
  apply NoDup_app_middle_cons_ts.
  eapply (NoDup_app_remove_middle_ts
    (ctx_names Γ) (expr_local_store_names e1) (x :: expr_local_store_names e2)).
  exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_letinfer_init :
  forall Γ m x e1 e2,
    expr_local_no_shadow_from Γ (ELetInfer m x e1 e2) ->
    expr_local_no_shadow_from Γ e1.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ m x e1 e2 Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_left_ts. exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_letinfer_binder_fresh_prefix :
  forall Γ m x e1 e2,
    expr_local_no_shadow_from Γ (ELetInfer m x e1 e2) ->
    ~ In x (ctx_names Γ ++ expr_local_store_names e1).
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ m x e1 e2 Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_middle_fresh_ts. exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_letinfer_body :
  forall Γ Γ1 m x T1 e1 e2,
    sctx_same_bindings Γ Γ1 ->
    expr_local_no_shadow_from Γ (ELetInfer m x e1 e2) ->
    expr_local_no_shadow_from (sctx_add x T1 m Γ1) e2.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ Γ1 m x T1 e1 e2 Hsame Hnodup.
  simpl in Hnodup |- *.
  rewrite (sctx_same_bindings_names_alpha Γ Γ1 Hsame).
  simpl in Hnodup.
  apply NoDup_app_middle_cons_ts.
  eapply (NoDup_app_remove_middle_ts
    (ctx_names Γ) (expr_local_store_names e1) (x :: expr_local_store_names e2)).
  exact Hnodup.
Qed.

Lemma args_local_no_shadow_from_cons_head :
  forall Γ e es,
    args_local_no_shadow_from Γ (e :: es) ->
    expr_local_no_shadow_from Γ e.
Proof.
  unfold args_local_no_shadow_from, expr_local_no_shadow_from.
  intros Γ e es Hnodup.
  unfold args_local_store_names in Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_left_ts. exact Hnodup.
Qed.

Lemma args_local_no_shadow_from_cons_tail :
  forall Γ Γ1 e es,
    sctx_same_bindings Γ Γ1 ->
    args_local_no_shadow_from Γ (e :: es) ->
    args_local_no_shadow_from Γ1 es.
Proof.
  unfold args_local_no_shadow_from.
  intros Γ Γ1 e es Hsame Hnodup.
  unfold args_local_store_names in Hnodup.
  simpl in Hnodup.
  eapply args_local_no_shadow_from_same_bindings.
  - exact Hsame.
  - unfold args_local_no_shadow_from, args_local_store_names.
    eapply NoDup_app_remove_middle_ts. exact Hnodup.
Qed.

Lemma fields_local_no_shadow_lookup :
  forall Γ fields name e,
    fields_local_no_shadow_from Γ fields ->
    lookup_field_b name fields = Some e ->
    expr_local_no_shadow_from Γ e.
Proof.
  unfold fields_local_no_shadow_from, expr_local_no_shadow_from.
  intros Γ fields.
  induction fields as [| [fname e0] rest IH]; intros name e Hnodup Hlookup;
    simpl in Hlookup; try discriminate.
  unfold fields_local_store_names in Hnodup.
  simpl in Hnodup.
  destruct (String.eqb name fname) eqn:Hname.
  - inversion Hlookup; subst e0.
    rewrite app_assoc in Hnodup.
    eapply NoDup_app_left_ts. exact Hnodup.
  - eapply IH.
    + unfold fields_local_store_names.
      eapply NoDup_app_remove_middle_ts. exact Hnodup.
    + exact Hlookup.
Qed.

Lemma expr_local_no_shadow_from_if_cond :
  forall Γ e1 e2 e3,
    expr_local_no_shadow_from Γ (EIf e1 e2 e3) ->
    expr_local_no_shadow_from Γ e1.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ e1 e2 e3 Hnodup.
  simpl in Hnodup.
  rewrite app_assoc in Hnodup.
  eapply NoDup_app_left_ts. exact Hnodup.
Qed.

Lemma expr_local_no_shadow_from_if_then :
  forall Γ Γ1 e1 e2 e3,
    sctx_same_bindings Γ Γ1 ->
    expr_local_no_shadow_from Γ (EIf e1 e2 e3) ->
    expr_local_no_shadow_from Γ1 e2.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ Γ1 e1 e2 e3 Hsame Hnodup.
  simpl in Hnodup.
  eapply expr_local_no_shadow_from_same_bindings.
  - exact Hsame.
  - unfold expr_local_no_shadow_from.
    assert (Hno_e1 :
      NoDup (ctx_names Γ ++
        expr_local_store_names e2 ++ expr_local_store_names e3)).
    { eapply NoDup_app_remove_middle_ts. exact Hnodup. }
    rewrite app_assoc in Hno_e1.
    eapply NoDup_app_left_ts. exact Hno_e1.
Qed.

Lemma expr_local_no_shadow_from_if_else :
  forall Γ Γ1 e1 e2 e3,
    sctx_same_bindings Γ Γ1 ->
    expr_local_no_shadow_from Γ (EIf e1 e2 e3) ->
    expr_local_no_shadow_from Γ1 e3.
Proof.
  unfold expr_local_no_shadow_from.
  intros Γ Γ1 e1 e2 e3 Hsame Hnodup.
  simpl in Hnodup.
  eapply expr_local_no_shadow_from_same_bindings.
  - exact Hsame.
  - unfold expr_local_no_shadow_from.
    assert (Hno_e1 :
      NoDup (ctx_names Γ ++
        expr_local_store_names e2 ++ expr_local_store_names e3)).
    { eapply NoDup_app_remove_middle_ts. exact Hnodup. }
    eapply NoDup_app_remove_middle_ts. exact Hno_e1.
Qed.


Lemma value_roots_within_stores_subset :
  (forall roots v,
    value_roots_within roots v ->
    forall roots',
      root_set_stores_subset roots roots' ->
      value_roots_within roots' v) /\
  (forall R se,
    store_entry_roots_within R se -> True) /\
  (forall R s,
    store_roots_within R s -> True) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall roots',
      root_set_stores_subset roots roots' ->
      value_fields_roots_within roots' fields).
Proof.
  apply value_roots_within_mutind; intros; try solve [constructor; eauto].
  - constructor.
    intros root Hexclude.
    apply s.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
Qed.

Lemma value_roots_within_store_subset :
  forall roots v roots',
    value_roots_within roots v ->
    root_set_stores_subset roots roots' ->
    value_roots_within roots' v.
Proof.
  intros roots v roots' Hwithin Hsubset.
  exact (proj1 value_roots_within_stores_subset
    roots v Hwithin roots' Hsubset).
Qed.


Lemma value_roots_exclude_root_stores_subset :
  forall roots v root roots_bound,
    value_roots_within roots v ->
    root_set_stores_subset roots roots_bound ->
    roots_exclude root roots_bound ->
    value_refs_exclude_root root v.
Proof.
  intros roots v root roots_bound Hwithin Hsubset Hexclude.
  eapply value_roots_exclude_root.
  - exact Hwithin.
  - eapply roots_exclude_stores_subset; eassumption.
Qed.
