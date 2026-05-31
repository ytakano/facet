From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCapturedCall.
From Facet.TypeSystem Require Import TypeSafetyHiddenFrameBaseCapture.
From Facet.TypeSystem Require Import TypeSafetyRootsReadyCtx.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Direct place helper facts                                            *)
(* ------------------------------------------------------------------ *)

Lemma store_lookup_some_in_names :
  forall s x se,
    store_lookup x s = Some se ->
    In x (store_names s).
Proof.
  induction s as [| se_head rest IH]; intros x se Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (ident_eqb x (se_name se_head)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hlookup.
Qed.

Lemma eval_place_root_name_in_store_names :
  forall s p x path,
    eval_place s p x path ->
    In (root_provenance_place_name p) (store_names s).
Proof.
  intros s p x path Heval.
  induction Heval; simpl.
  - eapply store_lookup_some_in_names. exact H.
  - exact IHHeval.
  - exact IHHeval.
Qed.

Lemma typed_env_structural_preserves_direct_path_target :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 e_new T_new p T_old x path,
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ e_new T_new Σ1 ->
    exists T_root st,
      sctx_lookup x Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path = Some T_old.
Proof.
  intros env Ω n Σ Σ1 e_new T_new p T_old x path Hplace Hpath Htyped.
  destruct (typed_place_direct_lookup env Σ p T_old x path Hplace Hpath)
    as [T_root [st [Hlookup [_ Htype_path]]]].
  destruct (sctx_same_bindings_lookup Σ Σ1 x T_root st
              (typed_env_structural_same_bindings env Ω n Σ e_new T_new Σ1 Htyped)
              Hlookup)
    as [st1 Hlookup1].
  exists T_root, st1. split; assumption.
Qed.

Lemma typed_env_structural_preserves_var_target :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 e_new T_new x T_old,
    typed_place_env_structural env Σ (PVar x) T_old ->
    typed_env_structural env Ω n Σ e_new T_new Σ1 ->
    exists st,
      sctx_lookup x Σ1 = Some (T_old, st).
Proof.
  intros env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped.
  destruct (typed_env_structural_preserves_direct_path_target
              env Ω n Σ Σ1 e_new T_new (PVar x) T_old x []
              Hplace eq_refl Htyped)
    as [T_root [st [Hlookup Htype_path]]].
  simpl in Htype_path.
  inversion Htype_path; subst T_root.
  exists st. exact Hlookup.
Qed.

Lemma ty_lifetime_equiv_usage :
  forall T_actual T_expected,
    ty_lifetime_equiv T_actual T_expected ->
    ty_usage T_actual = ty_usage T_expected.
Proof.
  intros T_actual T_expected Heq.
  inversion Heq; reflexivity.
Qed.

Lemma eval_place_direct_runtime_target_exists :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_root [st [HΣ [_ Htype_path]]]].
  destruct (store_typed_lookup_sctx env s Σ x_static T_root st Hstore HΣ)
    as [se [Hlookup [_ [Hse_ty [_ Hvroot]]]]].
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { eapply VHT_LifetimeEquiv.
    - exact Hvroot.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_root
              path_static T Hse_ty Htype_path)
    as [T_eval [Htype_path_se Heq_path]].
  destruct (value_has_type_path_exists env s (se_val se) (se_ty se)
              path_static T_eval Hvroot_se Htype_path_se)
    as [v_target [Hvalue_path _]].
  exists se, v_target, T_eval.
  repeat split; assumption.
Qed.


Lemma writable_place_none_under_unique_ref :
  forall env Σ p,
    writable_place_env_structural env Σ p ->
    place_path p = None ->
    place_under_unique_ref_structural env Σ p.
Proof.
  intros env Σ p Hwrite.
  induction Hwrite; intros Hpath; simpl in Hpath; try discriminate.
  - econstructor 1. exact H.
  - constructor 2.
    apply IHHwrite.
    destruct (place_path p) as [[x path] |] eqn:Hparent;
      simpl in Hpath; try discriminate; reflexivity.
Qed.

Lemma typed_place_type_env_structural_functional :
  forall env Σ p T1,
    typed_place_type_env_structural env Σ p T1 ->
    forall T2,
      typed_place_type_env_structural env Σ p T2 ->
      T1 = T2.
Proof.
  intros env Σ p T1 Htyped1.
  induction Htyped1; intros T2 Htyped2; inversion Htyped2; subst.
  - match goal with
    | Hleft : sctx_lookup x Σ = Some (T, st),
      Hright : sctx_lookup x Σ = Some (T2, st0) |- _ =>
        rewrite Hleft in Hright; inversion Hright; reflexivity
    end.
  - match goal with
    | IH : forall T2, typed_place_type_env_structural env Σ p T2 -> _ = T2,
      Hsub : typed_place_type_env_structural env Σ p ?Tsub |- _ =>
        specialize (IH Tsub Hsub); inversion IH; reflexivity
    end.
  - match goal with
    | IH : forall T2, typed_place_type_env_structural env Σ p T2 -> _ = T2,
      Hsub : typed_place_type_env_structural env Σ p ?Tsub |- _ =>
        specialize (IH Tsub Hsub); subst Tsub
    end.
    repeat match goal with
    | H1 : ?lhs = Some ?a, H2 : ?lhs = Some ?b |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end.
    congruence.
Qed.

Lemma typed_place_env_structural_to_type_env_structural :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    typed_place_type_env_structural env Σ p T.
Proof.
  intros env Σ p T Htyped.
  induction Htyped.
  - econstructor. exact H.
  - econstructor. exact IHHtyped.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Lemma typed_place_env_structural_functional :
  forall env Σ p T1,
    typed_place_env_structural env Σ p T1 ->
    forall T2,
      typed_place_env_structural env Σ p T2 ->
      T1 = T2.
Proof.
  intros env Σ p T1 Htyped1 T2 Htyped2.
  eapply typed_place_type_env_structural_functional.
  - apply typed_place_env_structural_to_type_env_structural. exact Htyped1.
  - apply typed_place_env_structural_to_type_env_structural. exact Htyped2.
Qed.

Lemma typed_place_env_structural_unique_ref_target_lifetime_equiv :
  forall env Σ p u la T_unique u2 la2 rk2 T_other,
    typed_place_env_structural env Σ p
      (MkTy u (TRef la RUnique T_unique)) ->
    typed_place_env_structural env Σ p
      (MkTy u2 (TRef la2 rk2 T_other)) ->
    ty_lifetime_equiv T_unique T_other.
Proof.
  intros env Σ p u la T_unique u2 la2 rk2 T_other Hunique Hother.
  pose proof (typed_place_env_structural_functional
                env Σ p (MkTy u (TRef la RUnique T_unique)) Hunique
                (MkTy u2 (TRef la2 rk2 T_other)) Hother) as Heq.
  inversion Heq; subst.
  apply ty_lifetime_equiv_refl.
Qed.



Lemma value_lookup_path_app_some :
  forall v p q v_mid v_final,
    value_lookup_path v p = Some v_mid ->
    value_lookup_path v_mid q = Some v_final ->
    value_lookup_path v (p ++ q) = Some v_final.
Proof.
  intros v p.
  revert v.
  induction p as [|seg rest IH]; intros v q v_mid v_final Hmid Hfinal.
  - simpl in Hmid. inversion Hmid; subst. exact Hfinal.
  - simpl in *.
    destruct v; try discriminate.
    match goal with
    | H : match ?lookup_result with Some fv => value_lookup_path fv rest | None => None end = Some v_mid |- _ =>
        destruct lookup_result as [fv |] eqn:Hfield; try discriminate
    end.
    eapply IH; eassumption.
Qed.


Lemma eval_place_direct_runtime_target_typed_exists_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_root [st [HΣ [_ Htype_path]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_root st Hstore HΣ)
    as [se [Hlookup [_ [Hse_ty [_ Hvroot]]]]].
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { eapply VHT_LifetimeEquiv.
    - exact Hvroot.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_root
              path_static T Hse_ty Htype_path)
    as [T_eval [Htype_path_se Heq_path]].
  destruct (value_has_type_path_exists env s (se_val se) (se_ty se)
              path_static T_eval Hvroot_se Htype_path_se)
    as [v_target [Hvalue_path Hvtarget]].
  exists se, v_target, T_eval.
  repeat split; assumption.
Qed.

Lemma eval_writable_place_runtime_target_exists_prefix :
  forall env Σ s p T x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    writable_place_env_structural env Σ p ->
    (exists x_static path_static,
      place_path p = Some (x_static, path_static)) ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env Σ s p T x_eval path_eval Hstore Htyped _ Hpath_exists Heval.
  destruct Hpath_exists as [x_static [path_static Hpath_static]].
  eapply eval_place_direct_runtime_target_typed_exists_prefix;
    eassumption.
Qed.


Lemma sctx_lookup_mut_some_lookup :
  forall x Σ m,
    sctx_lookup_mut x Σ = Some m ->
    exists T st,
      sctx_lookup x Σ = Some (T, st).
Proof.
  intros x Σ m Hmut.
  unfold sctx_lookup_mut, sctx_lookup in *.
  induction Σ as [|[[[y T] st] my] rest IH]; simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - exists T, st. reflexivity.
  - apply IH. exact Hmut.
Qed.

Lemma needs_consume_false_usage :
  forall T,
    needs_consume T = false ->
    ty_usage T = UUnrestricted.
Proof.
  intros [u c] Hconsume.
  destruct u; simpl in Hconsume; try discriminate; reflexivity.
Qed.

Lemma needs_consume_true_usage :
  forall T,
    needs_consume T = true ->
    ty_usage T <> UUnrestricted.
Proof.
  intros [u c] Hconsume Husage.
  destruct u; simpl in Hconsume; discriminate.
Qed.

Lemma eval_var_consume_static_copy_contradiction :
  forall env Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  pose proof (ty_lifetime_equiv_usage _ _ HT) as Husage_eq.
  apply (needs_consume_true_usage (se_ty se) Hconsume).
  rewrite Husage_eq. exact Husage.
Qed.

Lemma eval_var_copy_static_move_contradiction :
  forall env Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  apply Husage.
  pose proof (ty_lifetime_equiv_usage _ _ HT) as Husage_eq.
  rewrite <- Husage_eq.
  exact (needs_consume_false_usage (se_ty se) Hconsume).
Qed.

Lemma eval_place_consume_static_copy_direct_contradiction :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_root
              path_static T HTy Htype_static)
    as [T_actual [Htype_actual Heq_path]].
  rewrite Htype_eval in Htype_actual.
  inversion Htype_actual; subst T_actual.
  apply (needs_consume_true_usage T_eval Hconsume).
  pose proof (ty_lifetime_equiv_usage _ _ Heq_path) as Husage_eq.
  rewrite Husage_eq. exact Husage.
Qed.

Lemma eval_place_copy_static_move_direct_contradiction :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  apply Husage.
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_root
              path_static T HTy Htype_static)
    as [T_actual [Htype_actual Heq_path]].
  rewrite Htype_eval in Htype_actual.
  inversion Htype_actual; subst T_actual.
  pose proof (ty_lifetime_equiv_usage _ _ Heq_path) as Husage_eq.
  rewrite <- Husage_eq.
  exact (needs_consume_false_usage T_eval Hconsume).
Qed.

Lemma eval_var_consume_static_copy_contradiction_prefix :
  forall env Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HT [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  pose proof (needs_consume_true_usage (se_ty se) Hconsume) as Husage_se.
  pose proof (ty_lifetime_equiv_usage _ _ HT) as Husage_eq.
  apply Husage_se.
  rewrite Husage_eq.
  exact Husage.
Qed.

Lemma eval_var_copy_static_move_contradiction_prefix :
  forall env Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HT [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  apply Husage.
  pose proof (needs_consume_false_usage (se_ty se) Hconsume) as Husage_se.
  pose proof (ty_lifetime_equiv_usage _ _ HT) as Husage_eq.
  rewrite <- Husage_eq.
  exact Husage_se.
Qed.

Lemma eval_place_consume_static_copy_direct_contradiction_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_static
              path_static T HTy Htype_static)
    as [T_actual [Htype_actual Heq_path]].
  rewrite Htype_eval in Htype_actual.
  inversion Htype_actual; subst T_actual.
  apply (needs_consume_true_usage T_eval Hconsume).
  pose proof (ty_lifetime_equiv_usage _ _ Heq_path) as Husage_eq.
  rewrite Husage_eq. exact Husage.
Qed.

Lemma eval_place_copy_static_move_direct_contradiction_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  apply Husage.
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_static
              path_static T HTy Htype_static)
    as [T_actual [Htype_actual Heq_path]].
  rewrite Htype_eval in Htype_actual.
  inversion Htype_actual; subst T_actual.
  pose proof (needs_consume_false_usage T_eval Hconsume) as Husage_eval.
  pose proof (ty_lifetime_equiv_usage _ _ Heq_path) as Husage_eq.
  rewrite <- Husage_eq.
  exact Husage_eval.
Qed.

Lemma runtime_path_lookup_typing :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall path v_path T_path,
      value_lookup_path v path = Some v_path ->
      type_lookup_path env T path = Some T_path ->
      value_has_type env s v_path T_path) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall name field_value fdef rest v_path T_path,
      lookup_value_field name fields = Some field_value ->
      lookup_field name defs = Some fdef ->
      value_lookup_path field_value rest = Some v_path ->
      type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
        Some T_path ->
      value_has_type env s v_path T_path) /\
  (forall values tys,
    enum_values_have_type env s values tys ->
    True).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; subst; simpl in *; try discriminate.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path as [|seg rest].
    + simpl in *.
      match goal with
      | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
          inversion Hvalue; inversion Htype; subst
      end.
      econstructor; eassumption.
    + simpl in *.
      rewrite lookup_value_field_local in *.
      match goal with
      | Hlookup : lookup_struct name env = Some sdef |- _ =>
          destruct (lookup_struct_success env name sdef Hlookup) as [_ Hstruct_name]
      end.
      match goal with
      | Hlookup : lookup_struct name env = Some sdef,
        Htype : context[lookup_struct (struct_name sdef) env] |- _ =>
          rewrite Hstruct_name in Htype;
          rewrite Hlookup in Htype
      end.
      destruct (lookup_value_field seg fields) as [field_value |] eqn:Hvalue_field;
        try discriminate.
      destruct (lookup_field seg (struct_fields sdef)) as [fdef |] eqn:Hfield;
        try discriminate.
      match goal with
      | IHfields : forall name field_value fdef rest v_path T_path,
          lookup_value_field name fields = Some field_value ->
          lookup_field name (struct_fields sdef) = Some fdef ->
          value_lookup_path field_value rest = Some v_path ->
          type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
            Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHfields; eassumption
      end.
  - destruct path; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst
    end.
    eapply VHT_Enum; eassumption.
  - match goal with
    | Hvalue : value_lookup_path (VRef _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst; econstructor; eassumption
    end.
  - match goal with
    | Hvalue : value_lookup_path (VClosure _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst
    end.
    eapply VHT_ClosureEmpty; eassumption.
  - match goal with
    | Hvalue : value_lookup_path (VClosure _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst
    end.
    match goal with
    | Hin : In ?fdef (env_fns env) |- _ =>
        eapply VHT_ClosureIn; [exact Hin | reflexivity | eassumption]
    end.
  - match goal with
    | Hcompat : ty_compatible ?Omega ?T_actual ?T_expected,
      Htype : type_lookup_path env ?T_expected ?lookup_path = Some ?T_path |- _ =>
        destruct (type_lookup_path_compatible env Omega T_actual T_expected
                    lookup_path T_path Hcompat Htype)
          as [T_actual_path [Hactual_path Hcompat_path]]
    end.
    eapply (VHT_Compatible env s Ω v_path T_actual_path T_path).
    + match goal with
      | IHvalue : forall path v_path T_path,
          value_lookup_path _ path = Some v_path ->
          type_lookup_path env _ path = Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHvalue; eassumption
      end.
    + exact Hcompat_path.
  - match goal with
    | Heq : ty_lifetime_equiv ?T_actual ?T_expected,
      Htype : type_lookup_path env ?T_expected ?lookup_path = Some ?T_path |- _ =>
        destruct (type_lookup_path_lifetime_equiv env T_actual T_expected
                    lookup_path T_path Heq Htype)
          as [T_actual_path [Hactual_path Heq_path]]
    end.
    eapply (VHT_LifetimeEquiv env s v_path T_actual_path T_path).
    + match goal with
      | IHvalue : forall path v_path T_path,
          value_lookup_path _ path = Some v_path ->
          type_lookup_path env _ path = Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHvalue; eassumption
      end.
    + exact Heq_path.
  - destruct (String.eqb name0 (field_name f)) eqn:Hfield_name.
    + inversion H1; subst field_value.
      inversion H2; subst fdef.
      eapply H; eassumption.
    + eapply H0; eassumption.
  - exact I.
  - exact I.
Qed.

Lemma value_lookup_path_has_type :
  forall env s path v T v_path T_path,
    value_has_type env s v T ->
    value_lookup_path v path = Some v_path ->
    type_lookup_path env T path = Some T_path ->
    value_has_type env s v_path T_path.
Proof.
  intros env s path v T v_path T_path Htyped Hvalue Htype.
  exact (proj1 (runtime_path_lookup_typing env s) v T Htyped path v_path T_path Hvalue Htype).
Qed.

Lemma store_typed_prefix_lookup_path_value_has_type :
  forall env s Σ x m se path v_target T_eval,
    store_typed_prefix env s Σ ->
    sctx_lookup_mut x Σ = Some m ->
    store_lookup x s = Some se ->
    value_lookup_path (se_val se) path = Some v_target ->
    type_lookup_path env (se_ty se) path = Some T_eval ->
    value_has_type env s v_target T_eval.
Proof.
  intros env s Σ x m se path v_target T_eval
    Hstore Hmut Hlookup Hvalue Htype.
  destruct (sctx_lookup_mut_some_lookup x Σ m Hmut) as [T_static [st HΣ]].
  destruct (store_typed_prefix_lookup_sctx env s Σ x T_static st Hstore HΣ)
    as [se_static [Hlookup_static [_ [Hse_ty [_ Hvroot]]]]].
  rewrite Hlookup in Hlookup_static. inversion Hlookup_static; subst se_static.
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { eapply VHT_LifetimeEquiv.
    - exact Hvroot.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  eapply value_lookup_path_has_type; eassumption.
Qed.

Lemma value_has_type_unique_ref_target_lifetime_equiv :
  forall env s x path T_actual u la T_expected,
    value_has_type env s (VRef x path) T_actual ->
    ty_lifetime_equiv T_actual (MkTy u (TRef la RUnique T_expected)) ->
    exists se v_target T_target,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T_target /\
      ty_lifetime_equiv T_target T_expected.
Proof.
  intros env s x path T_actual u la T_expected Htyped.
  remember (VRef x path) as v eqn:Hvref.
  revert x path u la T_expected Hvref.
  induction Htyped; intros x0 path0 u_ref la_ref T_expected0 Hvref Heq;
    inversion Hvref; subst; try discriminate.
  - inversion Heq; subst.
    exists se, v, T. repeat split; assumption.
  - inversion Heq; subst.
    inversion H; subst; try discriminate.
    + eapply (IHHtyped x0 path0 ua la_ref T_expected0).
      * reflexivity.
      * constructor. exact H3.
    + eapply (IHHtyped x0 path0 ua la_ref T_expected0).
      * reflexivity.
      * constructor. exact H3.
  - eapply (IHHtyped x0 path0 u_ref la_ref T_expected0).
    + reflexivity.
    + exact (ty_lifetime_equiv_trans _ _ _ H Heq).
Qed.




Lemma eval_place_resolved_writable_target_matches_prefix :
  forall env R Σ s p T x x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    writable_place_env_structural env Σ p ->
    store_roots_within R s ->
    place_resolved_write_target R p = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    x_eval = x.
Proof.
  intros env R Σ s p T x x_eval path_eval _ _ _ Hroots Htarget _ Heval.
  eapply eval_place_resolved_write_target_matches_root; eassumption.
Qed.

Lemma eval_place_resolved_writable_direct_runtime_target_exists_prefix :
  forall env R Σ s p T x x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    writable_place_env_structural env Σ p ->
    store_roots_within R s ->
    place_resolved_write_target R p = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      x_eval = x /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env R Σ s p T x x_static path_static x_eval path_eval
    Hstore Htyped Hwrite Hroots Htarget Hmut Hpath Heval.
  assert (Hx : x_eval = x).
  { eapply eval_place_resolved_writable_target_matches_prefix; eassumption. }
  destruct (eval_place_direct_runtime_target_typed_exists_prefix
              env Σ s p T x_static path_static x_eval path_eval
              Hstore Htyped Hpath Heval)
    as [se [v_target [T_eval
        [Hlookup [Hvalue [Htype [Hequiv Hvtarget]]]]]]].
  exists se, v_target, T_eval.
  subst x_eval.
  repeat split; assumption.
Qed.

Lemma eval_place_unique_ref_direct_runtime_target_exists_prefix :
  forall env Σ s p T u la x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
    place_path p = Some (x_static, path_static) ->
    eval_place s (PDeref p) x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T.
Proof.
  intros env Σ s p T u la x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  inversion Heval_place; subst.
  destruct (eval_place_direct_runtime_target_typed_exists_prefix
              env Σ s p (MkTy u (TRef la RUnique T))
              x_static path_static r rpath
              Hstore Hplace Hpath_static H0)
    as [se_parent [v_parent [T_parent_eval
        [Hlookup_parent [Hvalue_parent [Htype_parent
          [Heq_parent Hv_parent]]]]]]].
  rewrite Hlookup_parent in H1. inversion H1; subst se_r.
  rewrite Hvalue_parent in H3. inversion H3; subst v_parent.
  eapply value_has_type_unique_ref_target_lifetime_equiv in Hv_parent.
  - exact Hv_parent.
  - exact Heq_parent.
Qed.

Lemma eval_place_unique_ref_direct_runtime_target_typed_exists_prefix :
  forall env Σ s p T u la x_static path_static x_eval path_eval m,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_eval Σ = Some m ->
    eval_place s (PDeref p) x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env Σ s p T u la x_static path_static x_eval path_eval m
    Hstore Hplace Hpath_static Hmut Heval_place.
  destruct (eval_place_unique_ref_direct_runtime_target_exists_prefix
              env Σ s p T u la x_static path_static x_eval path_eval
              Hstore Hplace Hpath_static Heval_place)
    as [se [v_target [T_eval [Hlookup [Hvalue [Htype Hequiv]]]]]].
  exists se, v_target, T_eval.
  repeat split; try assumption.
  eapply store_typed_prefix_lookup_path_value_has_type; eassumption.
Qed.

Lemma eval_pathless_writable_unique_deref_runtime_target_exists_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PDeref p) T ->
    writable_place_env_structural env Σ (PDeref p) ->
    place_path p = Some (x_static, path_static) ->
    eval_place s (PDeref p) x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Htyped Hwrite Hpath_parent Heval.
  inversion Htyped as
    [| p_t la_t rk_t T_t u_t Hparent_typed
     | |]; subst.
  inversion Hwrite as
    [| p_w la_w T_w u_w Hparent_unique
     |]; subst.
  destruct (eval_place_unique_ref_direct_runtime_target_exists_prefix
              env Σ s p T_w u_w la_w x_static path_static x_eval path_eval
              Hstore Hparent_unique Hpath_parent Heval)
    as [se [v_target [T_eval [Hlookup [Hvalue [Htype Heq_eval]]]]]].
  exists se, v_target, T_eval.
  repeat split; try assumption.
  eapply ty_lifetime_equiv_trans.
  - exact Heq_eval.
  - eapply typed_place_env_structural_unique_ref_target_lifetime_equiv.
    + exact Hparent_unique.
    + exact Hparent_typed.
Qed.

Lemma eval_place_resolved_writable_indirect_unique_deref_runtime_target_exists_prefix :
  forall env R Σ s p T x x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PDeref p) T ->
    writable_place_env_structural env Σ (PDeref p) ->
    store_roots_within R s ->
    place_resolved_write_target R (PDeref p) = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    place_path p = Some (x_static, path_static) ->
    eval_place s (PDeref p) x_eval path_eval ->
    exists se v_target T_eval,
      x_eval = x /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env R Σ s p T x x_static path_static x_eval path_eval
    Hstore Htyped Hwrite Hroots Htarget Hmut Hpath_parent Heval.
  assert (Hx : x_eval = x).
  { eapply eval_place_resolved_writable_target_matches_prefix; eassumption. }
  destruct (eval_pathless_writable_unique_deref_runtime_target_exists_prefix
              env Σ s p T x_static path_static x_eval path_eval
              Hstore Htyped Hwrite Hpath_parent Heval)
    as [se [v_target [T_eval [Hlookup [Hvalue [Htype Hequiv]]]]]].
  destruct (sctx_lookup_mut_some_lookup x Σ MMutable Hmut)
    as [T_static [st HΣ]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x T_static st Hstore HΣ)
    as [se_static [Hlookup_static [_ [Hse_ty [_ Hvroot]]]]].
  subst x_eval.
  rewrite Hlookup in Hlookup_static. inversion Hlookup_static; subst se_static.
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { eapply VHT_LifetimeEquiv.
    - exact Hvroot.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  assert (Hvtarget : value_has_type env s v_target T_eval).
  { eapply value_lookup_path_has_type; eassumption. }
  exists se, v_target, T_eval.
  repeat split; assumption.
Qed.
Lemma eval_place_resolved_writable_indirect_unique_deref_runtime_target_exists :
  forall env R Σ s p T x x_static path_static x_eval path_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PDeref p) T ->
    writable_place_env_structural env Σ (PDeref p) ->
    store_roots_within R s ->
    place_resolved_write_target R (PDeref p) = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    place_path p = Some (x_static, path_static) ->
    eval_place s (PDeref p) x_eval path_eval ->
    exists se v_target T_eval,
      x_eval = x /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env R Σ s p T x x_static path_static x_eval path_eval
    Hstore Htyped Hwrite Hroots Htarget Hmut Hpath_parent Heval.
  eapply eval_place_resolved_writable_indirect_unique_deref_runtime_target_exists_prefix.
  - apply store_typed_prefix_exact. exact Hstore.
  - exact Htyped.
  - exact Hwrite.
  - exact Hroots.
  - exact Htarget.
  - exact Hmut.
  - exact Hpath_parent.
  - exact Heval.
Qed.


Lemma eval_place_resolved_writable_chain_runtime_target_exists_prefix :
  forall env R Σ s p T x x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    writable_place_env_structural env Σ p ->
    store_roots_within R s ->
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_target R p = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      x_eval = x /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env R Σ s p T x x_eval path_eval Hstore Htyped Hwrite Hroots Hchain.
  revert T x x_eval path_eval Htyped Hwrite.
  induction Hchain as [p Hdirect | p x_parent Hchain IH Hwrite_parent Htarget_parent Hmut_parent];
    intros T x x_eval path_eval Htyped Hwrite Htarget Hmut Heval.
  - destruct Hdirect as [q [x_static [path_static [Hp Hpath_parent]]]].
    subst p.
    eapply eval_place_resolved_writable_indirect_unique_deref_runtime_target_exists_prefix;
      eassumption.
  - inversion Htyped as
      [| p_t la_t rk_t T_t u_t Hparent_typed
       | |]; subst.
    inversion Hwrite as
      [| p_w la_w T_w u_w Hparent_unique
       |]; subst.
    inversion Heval; subst.
    destruct (IH (MkTy u_w (TRef la_w RUnique T_w))
              x_parent r rpath Hparent_unique Hwrite_parent
              Htarget_parent Hmut_parent H0)
      as [se_parent [v_parent [T_parent_eval
          [Hr_eq [Hlookup_parent [Hvalue_parent
            [Htype_parent [Hequiv_parent Hv_parent]]]]]]]].
    subst r.
    rewrite Hlookup_parent in H1. inversion H1; subst se_r.
    rewrite Hvalue_parent in H3. inversion H3; subst v_parent.
    assert (Hx : x_eval = x).
    { eapply eval_place_resolved_write_target_matches_root; eassumption. }
    subst x_eval.
    destruct (value_has_type_unique_ref_target_lifetime_equiv
                env s x path_eval T_parent_eval u_w la_w T_w
                Hv_parent Hequiv_parent)
      as [se [v_target [T_eval
          [Hlookup [Hvalue [Htype Hequiv_target]]]]]].
    assert (Hvtarget : value_has_type env s v_target T_eval).
    { eapply store_typed_prefix_lookup_path_value_has_type; eassumption. }
    assert (Hequiv_typed : ty_lifetime_equiv T_w T).
    { eapply typed_place_env_structural_unique_ref_target_lifetime_equiv.
      - exact Hparent_unique.
      - exact Hparent_typed. }
    exists se, v_target, T_eval.
    repeat split; try assumption.
    eapply ty_lifetime_equiv_trans; eassumption.
Qed.

Lemma eval_place_resolved_writable_chain_runtime_target_exists :
  forall env R Σ s p T x x_eval path_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    writable_place_env_structural env Σ p ->
    store_roots_within R s ->
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_target R p = Some x ->
    sctx_lookup_mut x Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      x_eval = x /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T /\
      value_has_type env s v_target T_eval.
Proof.
  intros env R Σ s p T x x_eval path_eval Hstore Htyped Hwrite Hroots
    Hchain Htarget Hmut Heval.
  eapply eval_place_resolved_writable_chain_runtime_target_exists_prefix.
  - apply store_typed_prefix_exact. exact Hstore.
  - exact Htyped.
  - exact Hwrite.
  - exact Hroots.
  - exact Hchain.
  - exact Htarget.
  - exact Hmut.
  - exact Heval.
Qed.


Lemma eval_place_direct_runtime_target_exists_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target T_eval,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T_eval /\
      ty_lifetime_equiv T_eval T.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_root [st [HΣ [_ Htype_path]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_root st Hstore HΣ)
    as [se [Hlookup [_ [Hse_ty [_ Hvroot]]]]].
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { eapply VHT_LifetimeEquiv.
    - exact Hvroot.
    - apply ty_lifetime_equiv_sym. exact Hse_ty. }
  destruct (type_lookup_path_lifetime_equiv env (se_ty se) T_root
              path_static T Hse_ty Htype_path)
    as [T_eval [Htype_path_se Heq_path]].
  destruct (value_has_type_path_exists env s (se_val se) (se_ty se)
              path_static T_eval Hvroot_se Htype_path_se)
    as [v_target [Hvalue_path _]].
  exists se, v_target, T_eval.
  repeat split; assumption.
Qed.
