From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyBasePreservationBasic.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_drop_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' e T v,
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e T Σ' ->
     eval env s e s' v ->
     store_typed env s' Σ' /\ value_has_type env s' v T) ->
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    eval env s e s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ' s s' e T v Hpres Hstore Htyped Heval.
  destruct (Hpres Hstore Htyped Heval) as [Hstore' _].
  split; [exact Hstore' | constructor].
Qed.

Lemma eval_let_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2
      m x T T1 e1 e2 T2 v1 v2,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T1 Σ1 ->
    eval env s e1 s1 v1 ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T1 Σ1 ->
     eval env s e1 s1 v1 ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 v1 T1 /\
     store_ref_targets_preserved env s s1) ->
    ty_compatible_b Ω T1 T = true ->
    store_ref_targets_preserved env s1 (store_add x T v1 s1) ->
    typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
    eval env (store_add x T v1 s1) e2 s2 v2 ->
    (store_typed env (store_add x T v1 s1) (sctx_add x T m Σ1) ->
     typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
     eval env (store_add x T v1 s1) e2 s2 v2 ->
     store_typed env s2 Σ2 /\
     value_has_type env s2 v2 T2 /\
     store_ref_targets_preserved env (store_add x T v1 s1) s2) ->
    store_lookup x s1 = None ->
    value_refs_exclude_root x v2 ->
    store_refs_exclude_root x (store_remove x s2) ->
    store_typed env (store_remove x s2) (sctx_remove x Σ2) /\
    value_has_type env (store_remove x s2) v2 T2 /\
    store_ref_targets_preserved env s (store_remove x s2).
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 m x T T1 e1 e2 T2 v1 v2
    Hstore Htyped1 Heval1 Hpres1 Hcompat Hadd_pres Htyped2 Heval2
    Hpres2 Hfresh Hexclude_v Hexclude_store.
  destruct (Hpres1 Hstore Htyped1 Heval1) as [Hstore1 [Hv1 Hpres_s_s1]].
  pose proof (ty_compatible_b_sound Ω T1 T Hcompat) as Hcompat_prop.
  pose proof (store_typed_add_compatible env Ω s1 Σ1 x T1 T m v1
                Hstore1 Hv1 Hcompat_prop) as Hstore_add.
  specialize (Hstore_add Hadd_pres).
  destruct (Hpres2 Hstore_add Htyped2 Heval2)
    as [Hstore2 [Hv2 Hpres_add_s2]].
  split.
  - eapply store_typed_remove_excluding_root; eassumption.
  - split.
    + eapply value_has_type_store_remove_excluding_root; eassumption.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_s_s1.
      * eapply store_ref_targets_preserved_remove_after_absent_root.
        -- eapply store_ref_targets_preserved_trans.
           ++ exact Hadd_pres.
           ++ exact Hpres_add_s2.
        -- exact Hfresh.
Qed.

Lemma eval_let_roots_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R R1 R2 Σ Σ1 Σ2 s s1 s2
      m x T T1 e1 e2 T2 roots1 roots2 v1 v2,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
    ty_compatible_b Ω T1 T = true ->
    root_env_lookup x R1 = None ->
    typed_env_roots env Ω n (root_env_add x roots1 R1)
      (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
    sctx_check_ok env x T Σ2 = true ->
    roots_exclude x roots2 ->
    root_env_excludes x (root_env_remove x R2) ->
    provenance_ready_expr e1 ->
    provenance_ready_expr e2 ->
    eval env s e1 s1 v1 ->
    eval env (store_add x T v1 s1) e2 s2 v2 ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T1 Σ1 ->
     eval env s e1 s1 v1 ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 v1 T1 /\
     store_ref_targets_preserved env s s1) ->
    (store_typed env (store_add x T v1 s1) (sctx_add x T m Σ1) ->
     typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
     eval env (store_add x T v1 s1) e2 s2 v2 ->
     store_typed env s2 Σ2 /\
     value_has_type env s2 v2 T2 /\
     store_ref_targets_preserved env (store_add x T v1 s1) s2) ->
    store_typed env (store_remove x s2) (sctx_remove x Σ2) /\
    value_has_type env (store_remove x s2) v2 T2 /\
    store_ref_targets_preserved env s (store_remove x s2).
Proof.
  intros env Ω n R R1 R2 Σ Σ1 Σ2 s s1 s2 m x T T1 e1 e2 T2
    roots1 roots2 v1 v2 Hstore Hroots Hnodup Hrn Htyped1 Hcompat
    Hfresh_root Htyped2 _ Hexclude_roots Hexclude_env Hready1 Hready2
    Heval1 Heval2 Hpres1 Hpres2.
  destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1 v1 Heval1
              Ω n R Σ T1 Σ1 R1 roots1 Hready1 Hroots Hnodup Hrn Htyped1)
    as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]].
  assert (Hfresh_store : store_lookup x s1 = None)
    by (eapply store_roots_within_lookup_none; eassumption).
  assert (Hadd_pres :
    store_ref_targets_preserved env s1 (store_add x T v1 s1))
    by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
  assert (Hadd_roots :
    store_roots_within (root_env_add x roots1 R1)
      (store_add x T v1 s1))
    by (eapply store_add_roots_within; eassumption).
  assert (Hadd_nodup : store_no_shadow (store_add x T v1 s1))
    by (apply store_no_shadow_add; assumption).
  assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
    by (apply root_env_no_shadow_add; assumption).
  destruct (proj1 eval_preserves_roots_ready_mutual env
              (store_add x T v1 s1) e2 s2 v2 Heval2
              Ω n (root_env_add x roots1 R1) (sctx_add x T m Σ1)
              T2 Σ2 R2 roots2 Hready2 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
    as [Hroots2_runtime [Hv2_roots [Hnodup2 _]]].
  assert (Hremove_names :
    forall se, In se (store_remove x s2) -> se_name se <> x)
    by (apply store_no_shadow_remove_no_name; exact Hnodup2).
  assert (Hroots_removed :
    store_roots_within (root_env_remove x R2) (store_remove x s2))
    by (eapply store_remove_roots_within; eassumption).
  assert (Hexclude_v : value_refs_exclude_root x v2)
    by (eapply value_roots_exclude_root; eassumption).
  assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2))
    by (eapply store_roots_exclude_root; eassumption).
  eapply eval_let_preserves_typing.
  - exact Hstore.
  - eapply typed_env_roots_structural. exact Htyped1.
  - exact Heval1.
  - exact Hpres1.
  - exact Hcompat.
  - exact Hadd_pres.
  - eapply typed_env_roots_structural. exact Htyped2.
  - exact Heval2.
  - exact Hpres2.
  - exact Hfresh_store.
  - exact Hexclude_v.
  - exact Hexclude_store.
Qed.

Lemma eval_let_roots_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) R R1 R2 Σ Σ1 Σ2 s s1 s2
      m x T T1 e1 e2 T2 roots1 roots2 v1 v2,
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
    ty_compatible_b Ω T1 T = true ->
    root_env_lookup x R1 = None ->
    typed_env_roots env Ω n (root_env_add x roots1 R1)
      (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
    sctx_check_ok env x T Σ2 = true ->
    roots_exclude x roots2 ->
    root_env_excludes x (root_env_remove x R2) ->
    provenance_ready_expr e1 ->
    provenance_ready_expr e2 ->
    eval env s e1 s1 v1 ->
    eval env (store_add x T v1 s1) e2 s2 v2 ->
    (store_typed_prefix env s Σ ->
     typed_env_structural env Ω n Σ e1 T1 Σ1 ->
     eval env s e1 s1 v1 ->
     store_typed_prefix env s1 Σ1 /\
     value_has_type env s1 v1 T1 /\
     store_ref_targets_preserved env s s1) ->
    (store_typed_prefix env (store_add x T v1 s1) (sctx_add x T m Σ1) ->
     typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
     eval env (store_add x T v1 s1) e2 s2 v2 ->
     store_typed_prefix env s2 Σ2 /\
     value_has_type env s2 v2 T2 /\
     store_ref_targets_preserved env (store_add x T v1 s1) s2) ->
    store_typed_prefix env (store_remove x s2) (sctx_remove x Σ2) /\
    value_has_type env (store_remove x s2) v2 T2 /\
    store_ref_targets_preserved env s (store_remove x s2).
Proof.
  intros env Ω n R R1 R2 Σ Σ1 Σ2 s s1 s2 m x T T1 e1 e2 T2
    roots1 roots2 v1 v2 Hstore Hroots Hnodup Hrn Htyped1 Hcompat
    Hfresh_root Htyped2 _ Hexclude_roots Hexclude_env Hready1 Hready2
    Heval1 Heval2 Hpres1 Hpres2.
  destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1 v1 Heval1
              Ω n R Σ T1 Σ1 R1 roots1 Hready1 Hroots Hnodup Hrn Htyped1)
    as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]].
  assert (Hfresh_store : store_lookup x s1 = None)
    by (eapply store_roots_within_lookup_none; eassumption).
  assert (Hadd_pres :
    store_ref_targets_preserved env s1 (store_add x T v1 s1))
    by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
  destruct (Hpres1 Hstore (typed_env_roots_structural env Ω n R Σ e1 T1
                            Σ1 R1 roots1 Htyped1) Heval1)
    as [Hstore1 [Hv1 Hpres_s_s1]].
  pose proof (ty_compatible_b_sound Ω T1 T Hcompat) as Hcompat_prop.
  pose proof (store_typed_prefix_add_compatible env Ω s1 Σ1 x T1 T m v1
                Hstore1 Hv1 Hcompat_prop) as Hstore_add.
  specialize (Hstore_add Hadd_pres).
  assert (Hadd_roots :
    store_roots_within (root_env_add x roots1 R1)
      (store_add x T v1 s1))
    by (eapply store_add_roots_within; eassumption).
  assert (Hadd_nodup : store_no_shadow (store_add x T v1 s1))
    by (apply store_no_shadow_add; assumption).
  assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
    by (apply root_env_no_shadow_add; assumption).
  destruct (proj1 eval_preserves_roots_ready_mutual env
              (store_add x T v1 s1) e2 s2 v2 Heval2
              Ω n (root_env_add x roots1 R1) (sctx_add x T m Σ1)
              T2 Σ2 R2 roots2 Hready2 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
    as [Hroots2_runtime [Hv2_roots [Hnodup2 _]]].
  destruct (Hpres2 Hstore_add (typed_env_roots_structural env Ω n
                                (root_env_add x roots1 R1)
                                (sctx_add x T m Σ1) e2 T2 Σ2 R2
                                roots2 Htyped2) Heval2)
    as [Hstore2 [Hv2 Hpres_add_s2]].
  assert (Hremove_names :
    forall se, In se (store_remove x s2) -> se_name se <> x)
    by (apply store_no_shadow_remove_no_name; exact Hnodup2).
  assert (Hroots_removed :
    store_roots_within (root_env_remove x R2) (store_remove x s2))
    by (eapply store_remove_roots_within; eassumption).
  assert (Hexclude_v : value_refs_exclude_root x v2)
    by (eapply value_roots_exclude_root; eassumption).
  assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2))
    by (eapply store_roots_exclude_root; eassumption).
  split.
  - eapply store_typed_prefix_remove_excluding_root; eassumption.
  - split.
    + eapply value_has_type_store_remove_excluding_root; eassumption.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_s_s1.
      * eapply store_ref_targets_preserved_remove_after_absent_root.
        -- eapply store_ref_targets_preserved_trans.
           ++ exact Hadd_pres.
           ++ exact Hpres_add_s2.
        -- exact Hfresh_store.
Qed.

Lemma usage_sub_left_max :
  forall u1 u2,
    usage_sub u1 (usage_max u1 u2).
Proof.
  destruct u1, u2; simpl; constructor.
Qed.

Lemma usage_sub_right_max :
  forall u1 u2,
    usage_sub u2 (usage_max u1 u2).
Proof.
  destruct u1, u2; simpl; constructor.
Qed.

Lemma value_has_type_if_left_result :
  forall env s v T2 T3,
    value_has_type env s v T2 ->
    value_has_type env s v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env s v [u2 c2] [u3 c3] Hv.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + apply usage_sub_left_max.
    + reflexivity.
Qed.

Lemma value_has_type_if_right_result :
  forall env s v T2 T3,
    value_has_type env s v T3 ->
    ty_core T2 = ty_core T3 ->
    value_has_type env s v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env s v [u2 c2] [u3 c3] Hv Hcore.
  simpl in Hcore. subst c3.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + apply usage_sub_right_max.
    + reflexivity.
Qed.

Lemma eval_if_true_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat)
      Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 (e1 e2 e3 : expr) T_cond T2 T3 v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
    eval env s e1 s1 (VBool true) ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
     eval env s e1 s1 (VBool true) ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 (VBool true) T_cond) ->
    typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
    eval env s1 e2 s2 v ->
    (store_typed env s1 Σ1 ->
     typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
     eval env s1 e2 s2 v ->
     store_typed env s2 Σ2 /\ value_has_type env s2 v T2) ->
    ty_core T2 = ty_core T3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s2 Σ4 /\
    value_has_type env s2 v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env Ω n Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 e1 e2 e3 T_cond T2 T3 v
    Hstore Htyped_cond Heval_cond Hpres_cond Htyped_then Heval_then
    Hpres_then _ Hmerge.
  destruct (Hpres_cond Hstore Htyped_cond Heval_cond) as [Hstore1 _].
  destruct (Hpres_then Hstore1 Htyped_then Heval_then) as [Hstore2 Hv].
  split.
  - eapply store_typed_ctx_merge_left; eassumption.
  - eapply value_has_type_if_left_result. exact Hv.
Qed.

Lemma eval_if_false_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat)
      Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 (e1 e2 e3 : expr) T_cond T2 T3 v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
    eval env s e1 s1 (VBool false) ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
     eval env s e1 s1 (VBool false) ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 (VBool false) T_cond) ->
    typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
    typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
    eval env s1 e3 s2 v ->
    (store_typed env s1 Σ1 ->
     typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
     eval env s1 e3 s2 v ->
     store_typed env s2 Σ3 /\ value_has_type env s2 v T3) ->
    ty_core T2 = ty_core T3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s2 Σ4 /\
    value_has_type env s2 v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env Ω n Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 e1 e2 e3 T_cond T2 T3 v
    Hstore Htyped_cond Heval_cond Hpres_cond Htyped_then Htyped_else Heval_else
    Hpres_else Hcore Hmerge.
  destruct (Hpres_cond Hstore Htyped_cond Heval_cond) as [Hstore1 _].
  destruct (Hpres_else Hstore1 Htyped_else Heval_else) as [Hstore3 Hv].
  assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3).
  { eapply typed_env_structural_branch_type_eq.
    - exact Htyped_then.
    - exact Htyped_else. }
  split.
  - eapply store_typed_ctx_merge_right; eassumption.
  - eapply value_has_type_if_right_result; eassumption.
Qed.

Lemma eval_borrow_shared_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T_eval ->
    ty_lifetime_equiv T_eval T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target T_eval Hstore _ _
    Hlookup Htype Heq Hvalue.
  split; [exact Hstore |].
  eapply VHT_LifetimeEquiv with
    (T_actual := MkTy UUnrestricted (TRef (LVar n) RShared T_eval)).
  - econstructor; eassumption.
  - constructor. exact Heq.
Qed.

Lemma eval_borrow_unique_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    ty_lifetime_equiv T_eval T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target T_eval Hstore _ _ _ _ Hlookup Htype Heq Hvalue.
  split; [exact Hstore |].
  eapply VHT_LifetimeEquiv with
    (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_eval)).
  - econstructor; eassumption.
  - constructor. exact Heq.
Qed.

Lemma eval_borrow_unique_indirect_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = None ->
    place_under_unique_ref_structural env Σ p ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _ _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_shared_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T_eval ->
    ty_lifetime_equiv T_eval T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target T_eval Hstore _ _
    Hlookup Htype Heq Hvalue.
  split; [exact Hstore |].
  eapply VHT_LifetimeEquiv with
    (T_actual := MkTy UUnrestricted (TRef (LVar n) RShared T_eval)).
  - econstructor; eassumption.
  - constructor. exact Heq.
Qed.

Lemma eval_borrow_unique_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    ty_lifetime_equiv T_eval T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target T_eval Hstore _ _ _ _ Hlookup Htype Heq Hvalue.
  split; [exact Hstore |].
  eapply VHT_LifetimeEquiv with
    (T_actual := MkTy UAffine (TRef (LVar n) RUnique T_eval)).
  - econstructor; eassumption.
  - constructor. exact Heq.
Qed.
