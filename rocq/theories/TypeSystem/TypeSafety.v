From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace
  TypeSafetyLocalFacts TypeSafetyRootNamed.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_args_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s args params
      s' values,
    store_typed env s Σ ->
    typed_args_env_structural env Ω n Σ args params Σ' ->
    eval_args env s args s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    eval_args_values_have_types env Ω s' values params /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s args params s' values
    Hstore Htyped Heval Hpres.
  revert s s' values Hstore Heval.
  induction Htyped as
      [Σ
      |Σ Σ1 Σ2 e es p ps T_e Htyped_e Hcompat Htyped_rest IH];
    intros s s' values Hstore Heval.
  - inversion Heval; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - inversion Heval; subst.
    match goal with
    | Heval_e : eval env s e ?s1 ?v,
      Heval_rest : eval_args env ?s1 es s' ?vs |- _ =>
        destruct (Hpres Σ s e T_e Σ1 s1 v Hstore Htyped_e Heval_e)
          as [Hstore1 [Hv Hpres1]];
        destruct (IH s1 s' vs Hstore1 Heval_rest)
          as [Hstore2 [Hargs_values Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs_values ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
Qed.

Lemma eval_struct_fields_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) lts args Σ Σ' s fields defs
      s' values,
    store_typed env s Σ ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
    eval_struct_fields env s fields defs s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    struct_fields_have_type env s' lts args values defs /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n lts args Σ Σ' s fields defs s' values
    Hstore Htyped Heval Hpres.
  revert s s' values Hstore Heval.
  induction Htyped as
      [lts args Σ fields
      | lts args Σ Σ1 Σ2 fields f rest e_field T_field
          Hlookup Htyped_field Hcompat Htyped_rest IH];
    intros s s' values Hstore Heval.
  - inversion Heval; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - inversion Heval; subst.
    rewrite lookup_field_b_lookup_expr_field in Hlookup.
    match goal with
    | Hexpr : lookup_expr_field (field_name f) fields = Some _ |- _ =>
        rewrite Hlookup in Hexpr; inversion Hexpr; subst
    end.
    match goal with
    | Htyped_e : typed_env_structural env Ω n Σ ?e T_field Σ1,
      Heval_field : eval env s ?e ?s1 ?v,
      Heval_rest : eval_struct_fields env ?s1 fields rest s' ?values_tail |- _ =>
        destruct (Hpres Σ s e T_field Σ1 s1 v
                    Hstore Htyped_e Heval_field)
          as [Hstore1 [Hvalue Hpres1]];
        destruct (IH s1 s' values_tail Hstore1 Heval_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
Qed.

Lemma eval_struct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s'
      name lts args fields values sdef,
    store_typed env s Σ ->
    lookup_struct name env = Some sdef ->
    typed_fields_env_structural env Ω n lts args Σ fields (struct_fields sdef) Σ' ->
    eval_struct_fields env s fields (struct_fields sdef) s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' (VStruct name values)
      (instantiate_struct_instance_ty sdef lts args) /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' name lts args fields values sdef
    Hstore Hlookup Htyped_fields Heval_fields Hpres.
  destruct (eval_struct_fields_preserves_typing env Ω n lts args
              Σ Σ' s fields (struct_fields sdef) s' values
              Hstore Htyped_fields Heval_fields Hpres)
    as [Hstore' [Hfields Hpres_store]].
  split.
  - exact Hstore'.
  - split.
    + econstructor; eassumption.
    + exact Hpres_store.
Qed.

(* ------------------------------------------------------------------ *)
(* Basic big-step preservation cases                                    *)
(* ------------------------------------------------------------------ *)

Lemma eval_unit_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ s Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_int_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s i,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VInt i) (MkTy UUnrestricted TIntegers).
Proof.
  intros env Ω n Σ s i Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_float_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s f,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VFloat f) (MkTy UUnrestricted TFloats).
Proof.
  intros env Ω n Σ s f Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_bool_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s b,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VBool b) (MkTy UUnrestricted TBooleans).
Proof.
  intros env Ω n Σ s b Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_fn_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s fname fdef,
    store_typed env s Σ ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    store_typed env s Σ /\
    value_has_type env s (VClosure fname []) (fn_value_ty fdef).
Proof.
  intros env Ω n Σ s fname fdef Hstore Hin Hname.
  split; [exact Hstore |].
  eapply VHT_ClosureIn; eassumption.
Qed.

Lemma eval_var_copy_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    store_typed env s Σ /\
    value_has_type env s (se_val se) T.
Proof.
  intros env Ω n Σ s x T se Hstore Hplace _ Hlookup _.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst.
  split; [exact Hstore | exact Hv].
Qed.

Lemma eval_var_move_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    sctx_consume_path Σ x [] = infer_ok Σ' ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    se_used se = false ->
    store_typed env (store_mark_used x s) Σ' /\
    value_has_type env (store_mark_used x s) (se_val se) T.
Proof.
  intros env Ω n Σ Σ' s x T se Hstore Hplace _ Hconsume Hlookup _ _.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  destruct (sctx_consume_path_success Σ x [] Σ' Hconsume)
    as [T0 [st0 [HlookupΣ [_ Hupdate]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HlookupΣ
  end.
  inversion HlookupΣ; subst T0 st0.
  split.
  - eapply store_typed_mark_used; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hv.
    + apply store_mark_used_ref_targets_preserved.
Qed.

Lemma eval_place_copy_direct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_typed env s Σ /\ value_has_type env s v T.
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval se T_eval v
    Hstore Hplace _ Hpath_static Heval Hlookup _ Htype_eval _ Hvalue.
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
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  split; [exact Hstore |].
  eapply value_lookup_path_has_type; eassumption.
Qed.

Lemma eval_place_move_direct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    sctx_consume_path Σ x_static path_static = infer_ok Σ' ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_consume_path x_eval path_eval s = Some s' ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' p T x_static path_static x_eval path_eval se
    T_eval v Hstore Hplace _ Hpath_static Hconsume Heval Hlookup _
    Htype_eval _ Hvalue Hstore_consume.
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
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  assert (Hvpath : value_has_type env s v T).
  { eapply value_lookup_path_has_type; eassumption. }
  split.
  - eapply store_typed_consume_path; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hvpath.
    + unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_static s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_static);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
Qed.

Lemma eval_var_copy_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    store_typed_prefix env s Σ /\
    value_has_type env s (se_val se) T.
Proof.
  intros env Ω n Σ s x T se Hstore Hplace _ Hlookup _.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HTy [_ Hv]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  split; assumption.
Qed.

Lemma eval_var_move_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    sctx_consume_path Σ x [] = infer_ok Σ' ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    se_used se = false ->
    store_typed_prefix env (store_mark_used x s) Σ' /\
    value_has_type env (store_mark_used x s) (se_val se) T.
Proof.
  intros env Ω n Σ Σ' s x T se Hstore Hplace _ Hconsume Hlookup _ _.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HTy [_ Hv]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  destruct (sctx_consume_path_success Σ x [] Σ' Hconsume)
    as [T0 [st0 [HlookupΣ [_ Hupdate]]]].
  rewrite HΣ in HlookupΣ.
  inversion HlookupΣ; subst T0 st0.
  split.
  - eapply store_typed_prefix_mark_used; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hv.
    + apply store_mark_used_ref_targets_preserved.
Qed.

Lemma eval_place_copy_direct_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_typed_prefix env s Σ /\ value_has_type env s v T.
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval se T_eval v
    Hstore Hplace _ Hpath_static Heval Hlookup _ Htype_eval _ Hvalue.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ Hvroot]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  split; [exact Hstore |].
  eapply value_lookup_path_has_type; eassumption.
Qed.

Lemma eval_place_move_direct_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    sctx_consume_path Σ x_static path_static = infer_ok Σ' ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_consume_path x_eval path_eval s = Some s' ->
    store_typed_prefix env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' p T x_static path_static x_eval path_eval se
    T_eval v Hstore Hplace _ Hpath_static Hconsume Heval Hlookup _
    Htype_eval _ Hvalue Hstore_consume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ Hvroot]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  assert (Hvpath : value_has_type env s v T).
  { eapply value_lookup_path_has_type; eassumption. }
  split.
  - eapply store_typed_prefix_consume_path; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hvpath.
    + unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_static s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_static);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
Qed.


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
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_unique_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target Hstore _ _ _ _ Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
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
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_unique_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target Hstore _ _ _ _ Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma store_typed_prefix_update_path_typed :
  forall env s Σ x path v_new T_path s',
    store_typed_prefix env s Σ ->
    store_ref_targets_preserved env s s' ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path = Some T_path) ->
    value_has_type env s v_new T_path ->
    store_update_path x path v_new s = Some s' ->
    store_typed_prefix env s' Σ.
Proof.
  intros env s Σ x path v_new T_path s' Hstore Hpres Htarget Hvnew Hupdate.
  destruct Htarget as [T_root [st [HΣ Htype_path]]].
  eapply store_typed_prefix_update_path.
  - exact Hstore.
  - exact Hpres.
  - intros se T st0 Hlookup HΣ0 v_root Hvalue_update.
    rewrite HΣ in HΣ0.
    inversion HΣ0; subst T st0.
    destruct (store_typed_prefix_lookup_sctx env s Σ x T_root st Hstore HΣ)
      as [se' [Hlookup' [_ [HTse [_ Hvroot]]]]].
    rewrite Hlookup in Hlookup'.
    inversion Hlookup'; subst se'.
    eapply (value_update_path_has_type env s (se_val se) T_root
              path v_new T_path v_root).
    + exact Hvroot.
    + exact Htype_path.
    + exact Hvnew.
    + exact Hvalue_update.
  - exact Hupdate.
Qed.

Lemma eval_assign_path_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 p
      T_old T_new x_static path_static x_eval path_eval v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    eval_place s p x_eval path_eval ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_typed env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 p T_old T_new
    x_static path_static x_eval path_eval v_new Hstore Hplace Hpath_static
    Hstore1 Hvnew _ Hcompat Htarget Heval_place Hpres_update Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  split.
  - eapply store_typed_update_path_typed.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Htarget.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_assign_var_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 x
      old_e T_old T_new v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_typed env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 x old_e T_old T_new v_new
    Hstore _ Hstore1 Hvnew _ Hcompat Htarget _
    Hpres_update Hupdate.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st Hlookup1].
  split.
  - eapply store_typed_update_val.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Hlookup1.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_var_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 x
      old_e T_old T_new v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    sctx_path_available Σ1 x [] = infer_ok tt ->
    sctx_restore_path Σ1 x [] = infer_ok Σ2 ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_restore_path x [] s2 = Some s3 ->
    store_typed env s3 Σ2 /\
    value_has_type env s3 (se_val old_e) T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 x old_e T_old T_new v_new
    Hstore Hplace Hstore1 Hvnew Hpres_new_store Hcompat Htarget Havailable Hrestore
    Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (typed_place_direct_lookup env Σ (PVar x) T_old x [] Hplace eq_refl)
    as [T_root [st [Hlookup0 [_ Htype_old]]]].
  simpl in Htype_old. inversion Htype_old; subst T_root.
  destruct (store_typed_lookup env s Σ x old_e Hstore Hlookup_old)
    as [Tse [stse [m [HΣ [Hname [HT [Href Hold]]]]]]].
  rewrite Hlookup0 in HΣ.
  inversion HΣ; subst Tse stse.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st_target HΣ_target].
  destruct (sctx_path_available_success Σ1 x [] Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  rewrite HΣ_target in HΣ_av.
  inversion HΣ_av; subst T_av st_av.
  assert (Hstore2 : store_typed env s2 Σ1).
  { eapply store_typed_update_val.
    - exact Hstore1.
    - exact Hpres_update.
    - exact HΣ_target.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  split.
  - eapply store_typed_restore_available_path.
    + exact Hstore2.
    + exact HΣ_target.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_replace_path_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 p
      T_old T_new x_static path_static x_eval path_eval old_v v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    sctx_path_available Σ1 x_static path_static = infer_ok tt ->
    sctx_restore_path Σ1 x_static path_static = infer_ok Σ2 ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_restore_path x_eval path_eval s2 = Some s3 ->
    store_typed env s3 Σ2 /\
    value_has_type env s3 old_v T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 p T_old T_new
    x_static path_static x_eval path_eval old_v v_new Hstore Hplace
    Hpath_static Hstore1 Hvnew Hpres_new_store Hcompat Htarget
    Havailable Hrestore Heval_place Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T_old x_static path_static
              Hplace Hpath_static)
    as [T_root0 [st0 [HΣ0 [_ Htype_old]]]].
  destruct (store_typed_lookup_path env s Σ x_static path_static old_v
              Hstore Hlookup_old)
    as [se [T_root [st [m [HΣ [Hname [HTy [Hstore_lookup Hvalue_lookup]]]]]]]].
  rewrite HΣ0 in HΣ.
  inversion HΣ; subst T_root st.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hstore_lookup)
    as [Tse [stse [mse [HΣlookup [_ [HTse [_ Hvroot]]]]]]].
  rewrite HΣ0 in HΣlookup.
  inversion HΣlookup; subst Tse stse.
  assert (Hold : value_has_type env s old_v T_old).
  { eapply value_lookup_path_has_type.
    - exact Hvroot.
    - exact Hvalue_lookup.
    - match goal with
      | Hty : se_ty se = T_root0 |- _ =>
          rewrite Hty; exact Htype_old
      | Hty : T_root0 = se_ty se |- _ =>
          rewrite <- Hty; exact Htype_old
      end.
  }
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  assert (Hstore2 : store_typed env s2 Σ1).
  { eapply store_typed_update_path_typed.
    - exact Hstore1.
    - exact Hpres_update.
    - exact Htarget.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  destruct (sctx_path_available_success Σ1 x_static path_static Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  split.
  - eapply store_typed_restore_available_path.
    + exact Hstore2.
    + exact HΣ_av.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_var_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 x
      old_e T_old T_new v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_typed_prefix env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 x old_e T_old T_new v_new
    _ _ Hstore1 Hvnew _ Hcompat Htarget _ Hpres_update Hupdate.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st Hlookup1].
  split.
  - eapply store_typed_prefix_update_val.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Hlookup1.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_var_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 x
      old_e T_old T_new v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    sctx_path_available Σ1 x [] = infer_ok tt ->
    sctx_restore_path Σ1 x [] = infer_ok Σ2 ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_restore_path x [] s2 = Some s3 ->
    store_typed_prefix env s3 Σ2 /\
    value_has_type env s3 (se_val old_e) T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 x old_e T_old T_new v_new
    Hstore Hplace Hstore1 Hvnew Hpres_new_store Hcompat Htarget Havailable Hrestore
    Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (typed_place_direct_lookup env Σ (PVar x) T_old x [] Hplace eq_refl)
    as [T_root [st [Hlookup0 [_ Htype_old]]]].
  simpl in Htype_old. inversion Htype_old; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T_old st Hstore Hlookup0)
    as [se [Hlookup_se [_ [HT [_ Hold]]]]].
  rewrite Hlookup_old in Hlookup_se.
  inversion Hlookup_se; subst se.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st_target HΣ_target].
  destruct (sctx_path_available_success Σ1 x [] Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  rewrite HΣ_target in HΣ_av.
  inversion HΣ_av; subst T_av st_av.
  assert (Hstore2 : store_typed_prefix env s2 Σ1).
  { eapply store_typed_prefix_update_val.
    - exact Hstore1.
    - exact Hpres_update.
    - exact HΣ_target.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  split.
  - eapply store_typed_prefix_restore_available_path.
    + exact Hstore2.
    + exact HΣ_target.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_path_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 p
      T_old T_new x_static path_static x_eval path_eval v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    eval_place s p x_eval path_eval ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_typed_prefix env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 p T_old T_new
    x_static path_static x_eval path_eval v_new _ _ Hpath_static
    Hstore1 Hvnew _ Hcompat Htarget Heval_place Hpres_update Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  split.
  - eapply store_typed_prefix_update_path_typed.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Htarget.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_path_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 p
      T_old T_new x_static path_static x_eval path_eval old_v v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    sctx_path_available Σ1 x_static path_static = infer_ok tt ->
    sctx_restore_path Σ1 x_static path_static = infer_ok Σ2 ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_restore_path x_eval path_eval s2 = Some s3 ->
    store_typed_prefix env s3 Σ2 /\
    value_has_type env s3 old_v T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 p T_old T_new
    x_static path_static x_eval path_eval old_v v_new Hstore Hplace
    Hpath_static Hstore1 Hvnew Hpres_new_store Hcompat Htarget
    Havailable Hrestore Heval_place Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T_old x_static path_static
              Hplace Hpath_static)
    as [T_root0 [st0 [HΣ0 [_ Htype_old]]]].
  unfold store_lookup_path in Hlookup_old.
  destruct (store_lookup x_static s) as [se |] eqn:Hstore_lookup; try discriminate.
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_root0 st0 Hstore HΣ0)
    as [se' [Hstore_lookup' [_ [HTse [_ Hvroot]]]]].
  rewrite Hstore_lookup in Hstore_lookup'.
  inversion Hstore_lookup'; subst se'.
  assert (Hold : value_has_type env s old_v T_old).
  { eapply value_lookup_path_has_type.
    - exact Hvroot.
    - exact Hlookup_old.
    - exact Htype_old.
  }
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  assert (Hstore2 : store_typed_prefix env s2 Σ1).
  { eapply store_typed_prefix_update_path_typed.
    - exact Hstore1.
    - exact Hpres_update.
    - exact Htarget.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  destruct (sctx_path_available_success Σ1 x_static path_static Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  split.
  - eapply store_typed_prefix_restore_available_path.
    + exact Hstore2.
    + exact HΣ_av.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_direct_case_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p e_new x path,
    store_typed env s Σ ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ (EAssign p e_new)
      (MkTy UUnrestricted TUnits) Σ' ->
    eval env s (EAssign p e_new) s' VUnit ->
    (forall T_new Σ1 s1 v_new,
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      eval env s e_new s1 v_new ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v_new T_new /\
      store_ref_targets_preserved env s s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' VUnit (MkTy UUnrestricted TUnits) /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' p e_new x path
    Hstore Hpath Htyped Heval Hpres.
  inversion Htyped; subst; try discriminate.
  - inversion Heval; subst; try discriminate.
    + simpl in Hpath. inversion Hpath; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      destruct (typed_env_structural_preserves_var_target
                  env Ω n Σ Σ' e_new T_new x0 T_old H1 H5)
        as [st Htarget].
      destruct (Hpres T_new Σ' s1 v_new H5 H10)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s').
      { eapply store_update_val_ref_targets_preserved.
        - exact Hstore1.
        - exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H7.
        - exact H12. }
      destruct (eval_assign_var_preserves_typing env Ω n Σ Σ' s s1 s'
                  x0 old_e T_old T_new v_new Hstore H1
                  Hstore1 Hvnew Hpres_new
                  H7 (ex_intro _ st Htarget) H6 Hpres_update H12)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans; eassumption.
    + destruct (typed_env_structural_preserves_direct_path_target
                  env Ω n Σ Σ' e_new T_new p T_old x0 path0
                  H1 H3 H5) as [T_root [st Htarget]].
      destruct (eval_place_matches_place_path s p x1 path1 x0 path0 H6 H3)
        as [Hx_eval Hpath_eval].
      subst x1 path1.
      destruct (Hpres T_new Σ' s1 v_new H5 H10)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s').
      { eapply store_update_path_ref_targets_preserved.
        - exact Hstore1.
        - exists T_root, st. exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H7.
        - exact H12. }
      destruct (eval_assign_path_preserves_typing env Ω n Σ Σ' s s1 s'
                  p T_old T_new x0 path0 x0 path0 v_new
                  Hstore H1 H3 Hstore1 Hvnew Hpres_new
                  H7 (ex_intro _ T_root (ex_intro _ st Htarget))
                  H6 Hpres_update H12)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans; eassumption.
  - match goal with
    | Hnone : place_path p = None |- _ =>
        rewrite Hpath in Hnone; discriminate
    end.
Qed.

Lemma eval_replace_direct_case_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p e_new T_old x path v,
    store_typed env s Σ ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ' ->
    eval env s (EReplace p e_new) s' v ->
    (forall T_new Σ1 s1 v_new,
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      eval env s e_new s1 v_new ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v_new T_new /\
      store_ref_targets_preserved env s s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' v T_old /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' p e_new T_old x path v
    Hstore Hpath Htyped Heval Hpres.
  inversion Htyped; subst; try discriminate.
  - inversion Heval; subst; try discriminate.
    + simpl in Hpath. inversion Hpath; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      destruct (typed_env_structural_preserves_var_target
                  env Ω n Σ Σ1 e_new T_new x0 T_old H1 H4)
        as [st Htarget].
      destruct (Hpres T_new Σ1 s1 v_new H4 H8)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s2).
      { eapply store_update_val_ref_targets_preserved.
        - exact Hstore1.
        - exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H5.
        - exact H11. }
      assert (Hpres_restore : store_ref_targets_preserved env s2 s').
      { unfold store_restore_path in H14.
        eapply store_update_state_ref_targets_preserved.
        exact H14. }
      destruct (eval_replace_var_preserves_typing env Ω n Σ Σ1 Σ' s s1 s2 s'
                  x0 old_e T_old T_new v_new Hstore H1
                  Hstore1 Hvnew Hpres_new
                  H5 (ex_intro _ st Htarget) H7 H10 H6 Hpres_update H11 H14)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_new.
      * eapply store_ref_targets_preserved_trans; eassumption.
    + destruct (typed_env_structural_preserves_direct_path_target
                  env Ω n Σ Σ1 e_new T_new p T_old x0 path0
                  H1 H2 H4) as [T_root [st Htarget]].
      destruct (eval_place_matches_place_path s p x1 path1 x0 path0 H6 H2)
        as [Hx_eval Hpath_eval].
      subst x1 path1.
      destruct (Hpres T_new Σ1 s1 v_new H4 H9)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s2).
      { eapply store_update_path_ref_targets_preserved.
        - exact Hstore1.
        - exists T_root, st. exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H5.
        - exact H12. }
      assert (Hpres_restore : store_ref_targets_preserved env s2 s').
      { unfold store_restore_path in H15.
        eapply store_update_state_ref_targets_preserved.
        exact H15. }
      destruct (eval_replace_path_preserves_typing env Ω n Σ Σ1 Σ' s s1 s2 s'
                  p T_old T_new x0 path0 x0 path0 v v_new
                  Hstore H1 H2 Hstore1 Hvnew Hpres_new
                  H5 (ex_intro _ T_root (ex_intro _ st Htarget))
                  H7 H10 H6 H8 Hpres_update H12 H15)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_new.
      * eapply store_ref_targets_preserved_trans; eassumption.
  - match goal with
    | Hnone : place_path p = None |- _ =>
        rewrite Hpath in Hnone; discriminate
    end.
Qed.

Lemma eval_letinfer_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s'
      m x e1 e2 T v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ (ELetInfer m x e1 e2) T Σ' ->
    eval env s (ELetInfer m x e1 e2) s' v ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' m x e1 e2 T v _ _ Heval.
  inversion Heval.
Qed.

Theorem eval_preserves_typing_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction; eassumption.
    + assert (Hmove_pair :
        store_typed env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
    IHfields Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : preservation_ready_fields ?fields0,
      Htyped_fields : typed_fields_env_structural env Ω n lts args
        Σ ?fields0 (struct_fields sdef) Σ' |- _ =>
        destruct (IHfields Ω n lts args Σ Σ'
                    Hready_fields Hstore Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready.
  - intros s s' e v Heval IH Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e Σ' |- _ =>
        destruct (IH Ω n Σ T_e Σ' Hready_e Hstore Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s p x path rk Heval_place Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore0 Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore0 Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n Σ T Σ'
      Hready _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_then : preservation_ready_expr e2,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHthen Ω n Σ1 T2 Σ2
                    Hready_then Hstore1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_else : preservation_ready_expr e3,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Htyped_else : typed_env_structural env Ω n ?Σ1 e3 ?T3 ?Σ3,
      Hcore : ty_core ?T2 = ty_core ?T3,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHelse Ω n Σ1 T3 Σ3
                    Hready_else Hstore1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq; eassumption);
        split;
        [ eapply store_typed_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n Σ T Σ'
      Hready _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s Ω n Σ ps Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n Σ ps Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Hready_rest : preservation_ready_args es,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_env_structural env Ω n ?Σ1 es ?ps_rest Σ' |- _ =>
        destruct (IHe Ω n Σ T_e Σ1 Hready_e Hstore Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (IHrest Ω n Σ1 ps_rest Σ' Hready_rest Hstore1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args Σ Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args Σ Σ' Hready Hstore Htyped.
    pose proof (preservation_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Hready; subst.
    simpl in Hlookup_expr; try discriminate.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_structural env Ω n Σ ?e_field ?T_field ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_env_structural env Ω n lts args
        ?Σ1 ?fields0 rest Σ' |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst;
        destruct (IHfield Ω n Σ T_field Σ1 Hready_field Hstore Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (IHrest Ω n lts args Σ1 Σ' Hready Hstore1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 Σ0 T0 Σ0'
      Hready Hstore Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 Σ0 ps0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 Σ0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Theorem typed_fn_env_structural_big_step_safe_ready :
  forall env f s s' v,
    typed_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Htyped_fn Hready Hstore Heval.
  unfold typed_fn_env_structural in Htyped_fn.
  destruct Htyped_fn as
    (T_body & Γ_out & Htyped & Hcompat & _).
  destruct (proj1 eval_preserves_typing_ready_mutual
      env s (fn_body f) s' v Heval
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      T_body (sctx_of_ctx Γ_out)
      Hready Hstore Htyped)
    as [_ [Hv _]].
  eapply VHT_Compatible.
  - exact Hv.
  - apply ty_compatible_b_sound. exact Hcompat.
Qed.

Theorem checked_fn_env_structural_big_step_safe_ready :
  forall env f s s' v,
    checked_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros env f s s' v Hchecked Hready Hstore Heval.
  eapply typed_fn_env_structural_big_step_safe_ready.
  - exact (proj1 Hchecked).
  - exact Hready.
  - exact Hstore.
  - exact Heval.
Qed.

Theorem eval_preserves_typing_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed_prefix env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed_prefix env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed_prefix env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed_prefix env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed_prefix env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed_prefix env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing_prefix env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction_prefix; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction_prefix; eassumption.
    + destruct (eval_var_move_preserves_typing_prefix env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing_prefix
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction_prefix; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction_prefix; eassumption.
    + assert (Hmove_pair :
        store_typed_prefix env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing_prefix; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
    IHfields Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : preservation_ready_fields ?fields0,
      Htyped_fields : typed_fields_env_structural env Ω n lts args
        Σ ?fields0 (struct_fields sdef) Σ' |- _ =>
        destruct (IHfields Ω n lts args Σ Σ'
                    Hready_fields Hstore Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready.
  - intros s s' e v Heval IH Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e Σ' |- _ =>
        destruct (IH Ω n Σ T_e Σ' Hready_e Hstore Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s p x path rk Heval_place Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore0 Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore0 Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n Σ T Σ'
      Hready _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_then : preservation_ready_expr e2,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHthen Ω n Σ1 T2 Σ2
                    Hready_then Hstore1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_prefix_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_else : preservation_ready_expr e3,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Htyped_else : typed_env_structural env Ω n ?Σ1 e3 ?T3 ?Σ3,
      Hcore : ty_core ?T2 = ty_core ?T3,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHelse Ω n Σ1 T3 Σ3
                    Hready_else Hstore1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq; eassumption);
        split;
        [ eapply store_typed_prefix_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n Σ T Σ'
      Hready _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s Ω n Σ ps Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n Σ ps Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Hready_rest : preservation_ready_args es,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_env_structural env Ω n ?Σ1 es ?ps_rest Σ' |- _ =>
        destruct (IHe Ω n Σ T_e Σ1 Hready_e Hstore Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (IHrest Ω n Σ1 ps_rest Σ' Hready_rest Hstore1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args Σ Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args Σ Σ' Hready Hstore Htyped.
    pose proof (preservation_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Hready; subst.
    simpl in Hlookup_expr; try discriminate.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_structural env Ω n Σ ?e_field ?T_field ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_env_structural env Ω n lts args
        ?Σ1 ?fields0 rest Σ' |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst;
        destruct (IHfield Ω n Σ T_field Σ1 Hready_field Hstore Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (IHrest Ω n lts args Σ1 Σ' Hready Hstore1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 Σ0 T0 Σ0'
      Hready Hstore Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 Σ0 ps0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 Σ0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Scheme preservation_ready_expr_ind' :=
  Induction for preservation_ready_expr Sort Prop
with preservation_ready_args_ind' :=
  Induction for preservation_ready_args Sort Prop
with preservation_ready_fields_ind' :=
  Induction for preservation_ready_fields Sort Prop.
Combined Scheme preservation_ready_mutind
  from preservation_ready_expr_ind', preservation_ready_args_ind',
       preservation_ready_fields_ind'.

Lemma preservation_ready_implies_provenance_ready_mutual :
  (forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e) /\
  (forall args,
    preservation_ready_args args ->
    provenance_ready_args args) /\
  (forall fields,
    preservation_ready_fields fields ->
    provenance_ready_fields fields).
Proof.
  apply preservation_ready_mutind;
    try solve [econstructor; eauto].
Qed.

Lemma preservation_ready_implies_provenance_ready :
  forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e.
Proof.
  exact (proj1 preservation_ready_implies_provenance_ready_mutual).
Qed.

Lemma preservation_ready_args_implies_provenance_ready :
  forall args,
    preservation_ready_args args ->
    provenance_ready_args args.
Proof.
  exact (proj1 (proj2 preservation_ready_implies_provenance_ready_mutual)).
Qed.

Lemma preservation_ready_fields_implies_provenance_ready :
  forall fields,
    preservation_ready_fields fields ->
    provenance_ready_fields fields.
Proof.
  exact (proj2 (proj2 preservation_ready_implies_provenance_ready_mutual)).
Qed.

Theorem eval_preserves_roots_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s').
Proof.
  split.
  - intros env s e s' v Heval Ω n R Σ T Σ' R' roots
      Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 eval_preserves_typing_ready_prefix_mutual
                env s e s' v Heval Ω n Σ T Σ' Hpres_ready Hstore
                (typed_env_roots_structural env Ω n R Σ e T Σ' R' roots
                  Htyped))
      as [Hstore' [_ Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env s args s' vs Heval Ω n R Σ ps Σ' R' roots
        Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 eval_preserves_typing_ready_prefix_mutual)
                  env s args s' vs Heval Ω n Σ ps Σ' Hpres_ready Hstore
                  (typed_args_roots_structural env Ω n R Σ args ps Σ' R'
                    roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
                  env s args s' vs Heval Ω n R Σ ps Σ' R' roots
                  Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
        roots Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj2 (proj2 eval_preserves_typing_ready_prefix_mutual)
                  env s fields defs s' values Heval Ω n lts args Σ Σ'
                  Hpres_ready Hstore
                  (typed_fields_roots_structural env Ω n lts args R Σ
                    fields defs Σ' R' roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual)
                  env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
                  roots Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used' T_body Γ_out,
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    typed_env_structural env (fn_outlives fcall) (fn_lifetimes fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  intros env Ω n Σ Σ_args fname args fdef fcall σ s s_args s_body
    vs ret used' T_body Γ_out Hstore Hready_args Htyped_args Heval_args
    Hlookup Henv_checked Henv_ready Hrename Htyped_body Hcompat_body
    Heval_body.
  destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore Htyped_args)
    as [Hstore_args [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hready_body : preservation_ready_expr (fn_body fcall)).
  { eapply lookup_alpha_rename_fn_def_preservation_ready_body; eassumption. }
  destruct (proj1 eval_preserves_typing_ready_prefix_mutual
              env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out)
              Hready_body Hstore_bind Htyped_body)
    as [Hstore_body [Hv_body Hpres_body]].
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  repeat split; try assumption.
  eapply value_has_type_apply_lt_ty. exact Hv_ret_fdef.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix_from_lookup :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used',
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    fn_captures fcall = [] ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    exists Γ_out,
      store_typed env s_args Σ_args /\
      store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
      value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
      store_ref_targets_preserved env
        (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  intros env Ω n Σ Σ_args fname args fdef fcall σ s s_args s_body
    vs ret used' Hstore Hready_args Htyped_args Heval_args Hlookup
    Henv_checked Henv_ready Hrename Hcaps_call Heval_body.
  pose proof (lookup_alpha_rename_fn_def_typed_structural
                env fname fdef fcall (store_names s_args) used'
                Hlookup Henv_checked Hrename) as Htyped_fn.
  destruct (typed_fn_env_structural_body env fcall Htyped_fn)
    as [T_body [Γ_out [Htyped_body [Hcompat_body _]]]].
  rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
             fcall Hcaps_call) in Htyped_body.
  exists Γ_out.
  eapply eval_direct_call_body_preserves_typing_prefix; eassumption.
Qed.

Theorem eval_preserves_typing_roots_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  assert (Htyping : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing_prefix env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction_prefix; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction_prefix; eassumption.
    + destruct (eval_var_move_preserves_typing_prefix env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hstore _ _ _ Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing_prefix
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction_prefix; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots Hready Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction_prefix; eassumption.
    + assert (Hmove_pair :
        store_typed_prefix env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing_prefix; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : provenance_ready_fields ?fields0,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ ?fields0
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hstore Hroots Hnodup Hrn Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
        ?R1_body ?roots1_body,
      Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
      Hfresh : root_env_lookup x ?R1_body = None,
      Htyped2 : typed_env_roots env Ω n
        (root_env_add x ?roots1_body ?R1_body)
        (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
        ?R2_body ?roots2_body,
      Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
      Hexcl_roots : roots_exclude x ?roots2_body,
      Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
      Hready1 : provenance_ready_expr e1,
      Hready2 : provenance_ready_expr e2 |- _ =>
        let Hpres1 := fresh "Hpres1" in
        let Hpres2 := fresh "Hpres2" in
        assert (Hpres1 :
          store_typed_prefix env s Σ ->
          typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
          eval env s e1 s1 v1 ->
          store_typed_prefix env s1 Σ1_body /\
          value_has_type env s1 v1 T1_body /\
          store_ref_targets_preserved env s s1);
        [ intros Hstore0 _ Heval0;
          exact (IH1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hstore0 Hroots Hnodup Hrn Htyped1)
        | destruct (proj1 eval_preserves_roots_ready_mutual env s e1
            s1 v1 Heval1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]];
          assert (Hfresh_store : store_lookup x s1 = None)
            by (eapply store_roots_within_lookup_none; eassumption);
          assert (Hadd_roots :
            store_roots_within (root_env_add x roots1_body R1_body)
              (store_add x T_ann v1 s1))
            by (eapply store_add_roots_within; eassumption);
          assert (Hadd_nodup :
            store_no_shadow (store_add x T_ann v1 s1))
            by (apply store_no_shadow_add; assumption);
          assert (Hadd_rn :
            root_env_no_shadow (root_env_add x roots1_body R1_body))
            by (apply root_env_no_shadow_add; assumption);
          assert (Hpres2 :
            store_typed_prefix env (store_add x T_ann v1 s1)
              (sctx_add x T_ann m Σ1_body) ->
            typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
              e2 T2_body Σ2_body ->
            eval env (store_add x T_ann v1 s1) e2 s2 v2 ->
            store_typed_prefix env s2 Σ2_body /\
            value_has_type env s2 v2 T2_body /\
            store_ref_targets_preserved env
              (store_add x T_ann v1 s1) s2);
          [ intros Hstore0 _ Heval0;
            exact (IH2 Ω n (root_env_add x roots1_body R1_body)
              (sctx_add x T_ann m Σ1_body) T2_body Σ2_body R2_body
              roots2_body Hready2 Hstore0 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
          | eapply eval_let_roots_preserves_typing_prefix;
            eassumption ] ]
    end.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ' R' roots_e Hready_e
                    Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup
      Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hstore Hroots
      Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped.
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H4 H2)
        as [Hx Hpath].
      subst x path.
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_root [st [HΣ [_ Htype_path]]]].
      destruct (store_typed_prefix_lookup_sctx
                  env s_r Σ x1 T_root st Hstore HΣ)
        as [se' [Hlookup' [_ [HT [_ Hvroot]]]]].
      rewrite Hlookup in Hlookup'.
      inversion Hlookup'; subst se'.
      rewrite HT in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H5 H2)
        as [Hx Hpath].
      subst x path.
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_root [st [HΣ [_ Htype_path]]]].
      destruct (store_typed_prefix_lookup_sctx
                  env s_r Σ x1 T_root st Hstore HΣ)
        as [se' [Hlookup' [_ [HT [_ Hvroot]]]]].
      rewrite Hlookup in Hlookup'.
      inversion Hlookup'; subst se'.
      rewrite HT in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2
                    Hready_then Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_prefix_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
      | Hready_cond : provenance_ready_expr e1,
        Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
        Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
        Hready_else : provenance_ready_expr e3,
        Htyped_else : typed_env_roots env Ω n ?R1 Σ1 e3 ?T3 ?Σ3 ?R3 ?roots3,
        Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3
                    Hready_else Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq;
            [ eapply typed_env_roots_structural; exact Htyped_then
            | eapply typed_env_roots_structural; exact Htyped_else ]);
        split;
        [ eapply store_typed_prefix_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1 Σ1 ps_rest Σ' R' roots_rest
                    Hready_rest Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args R Σ Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args R Σ Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_roots env Ω n lts args ?R1 ?Σ1
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hstore Hroots Hnodup Hrn Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest
                    Hready Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 (Htyping env0) s0 e0 s0' v0 Heval
                Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' [Hv Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual env0 s0 e0 s0' v0
                Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 (Htyping env0)) s0 args0 s0' vs0 Heval
                  Ω0 n0 R0 Σ0 ps0 Σ0' R0' roots0
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0' R0'
                  roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hstore Hroots Hnodup Hrn
        Htyped.
      destruct (proj2 (proj2 (Htyping env0)) s0 fields0 defs0 s0'
                  values0 Heval Ω0 n0 lts0 args0 R0 Σ0 Σ0' R0'
                  roots0 Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 R0
                  Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.

Lemma eval_call_body_cleanup_preserves_value_and_refs_frame :
  forall env (Ω : outlives_ctx) frame Σ_frame fdef fcall σ s_body vs ret
      used' T_body Γ_out R_params R_body roots_body,
    store_typed env frame Σ_frame ->
    alpha_rename_fn_def (store_names frame) fdef = (fcall, used') ->
    eval_args_values_have_types env Ω frame vs (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs frame) ->
    store_no_shadow (bind_params (fn_params fcall) vs frame) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs frame)
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_frame /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env frame
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = frame /\
    value_roots_within roots_body ret.
Proof.
  eapply (eval_call_body_cleanup_preserves_value_and_refs_frame_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_store captured ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω captured Rcap s_args R_args Σ_args fdef fcall σ s_body
    vs ret used' T_body Γ_out R_params R_body roots_body Hframe_ready
    Htyped_args Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_params Hprov_body Htyped_body Hcompat_body Hexclude_ret
    Hexclude_env Heval_body.
  eapply eval_call_body_cleanup_preserves_value_and_refs_frame;
    try eassumption.
  eapply captured_call_frame_store_typed; eassumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args σ T_body Γ_out
      R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_store captured ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret used' Rcap R_args Σ_args σ T_body Γ_out R_params R_body
    roots_body Heval_callee Hlookup Heval_args Hrename Heval_body
    Hframe_ready Htyped_args Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_params Hprov_body Htyped_body Hcompat_body Hexclude_ret
    Hexclude_env.
  split.
  - eapply Eval_CallExpr; eassumption.
  - eapply eval_captured_call_body_cleanup_preserves_value_and_refs;
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args caps
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω captured Rcap s_args R_args Σ_args caps fdef fcall σ
    s_body vs ret used' T_body Γ_out R_params R_body roots_body
    Hframe_params_ready Htyped_args Hrename Hargs_fcall Hroots_bind
    Hshadow_bind Hrn_params Hcover_params Hprov_body Htyped_body
    Hcompat_body Hexclude_ret Hexclude_env Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  destruct (eval_captured_call_body_cleanup_preserves_value_and_refs
              env Ω captured Rcap s_args R_args Σ_args fdef fcall σ
              s_body vs ret used' T_body Γ_out R_params R_body roots_body
              Hframe_ready Htyped_args Hrename Hargs_fcall Hroots_bind
              Hshadow_bind Hrn_params Hcover_params Hprov_body Htyped_body
              Hcompat_body Hexclude_ret Hexclude_env Heval_body)
    as [_ Hcleanup].
  destruct Hcleanup as [Hprefix Hcleanup].
  destruct Hcleanup as [Hroots_body Hcleanup].
  destruct Hcleanup as [Hshadow_body Hcleanup].
  destruct Hcleanup as [Hrn_body Hcleanup].
  destruct Hcleanup as [Hv_ret Hcleanup].
  destruct Hcleanup as [Hpres Hcleanup].
  destruct Hcleanup as [frame_final [locals [Hscope [Hremoved
    [Hret_exclude [Hstore_exclude [Hremoved_exact Hroots_ret]]]]]]].
  assert (Htyped_frame :
    store_typed env (captured ++ s_args)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args)).
  { eapply captured_call_frame_params_store_typed.
    - split; eassumption.
    - exact Htyped_args. }
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Htyped_frame.
  - exists frame_final, locals. repeat split; assumption.
Qed.

Lemma eval_captured_call_expr_cleanup_preserves_value_and_refs_params :
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args caps σ T_body
      Γ_out R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env (store_remove_params (fn_params fcall) s_body)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args) /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env (captured ++ s_args)
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = captured ++ s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret used' Rcap R_args Σ_args caps σ T_body Γ_out R_params R_body
    roots_body Heval_callee Hlookup Heval_args Hrename Heval_body
    Hframe_params_ready Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_params Hprov_body Htyped_body Hcompat_body
    Hexclude_ret Hexclude_env.
  split.
  - eapply Eval_CallExpr; eassumption.
  - eapply eval_captured_call_body_cleanup_preserves_value_and_refs_params;
      eassumption.
Qed.

Lemma eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args caps
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    roots_exclude_params caps roots_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove_params caps
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params caps
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove_params caps
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  intros env Ω captured Rcap s_args R_args Σ_args caps fdef fcall σ
    s_body vs ret used' T_body Γ_out R_params R_body roots_body
    Hframe_params_ready Htyped_args Hrename Hargs_fcall Hroots_bind
    Hshadow_bind Hrn_params Hcover_params Hprov_body Htyped_body
    Hcompat_body Hexclude_ret Hexclude_env Hexclude_caps Heval_body.
  destruct Hframe_params_ready as [Hframe_ready Hcaptured_params_typed].
  destruct (eval_captured_call_body_cleanup_preserves_value_and_refs_params
              env Ω captured Rcap s_args R_args Σ_args caps fdef fcall σ
              s_body vs ret used' T_body Γ_out R_params R_body roots_body
              (conj Hframe_ready Hcaptured_params_typed) Htyped_args
              Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
              Hcover_params Hprov_body Htyped_body Hcompat_body
              Hexclude_ret Hexclude_env Heval_body)
    as [Hstore_frame Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [Hv_ret Hcleanup].
  destruct Hcleanup as [_ Hcleanup].
  destruct Hcleanup as [frame_final [locals [_ [_ [_ [_
    [Hremoved_exact Hroots_ret]]]]]]].
  assert (Hfinal_exact :
    store_remove_params caps
      (store_remove_params (fn_params fcall) s_body) = s_args).
  { rewrite Hremoved_exact.
    eapply captured_params_store_typed_remove_app.
    exact Hcaptured_params_typed. }
  repeat split.
  - rewrite Hfinal_exact. exact Htyped_args.
  - rewrite Hremoved_exact.
    eapply value_has_type_store_remove_params_excluding.
    + rewrite <- Hremoved_exact. exact Hv_ret.
    + eapply value_roots_exclude_params; eassumption.
  - exact Hfinal_exact.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased :
  forall env (Ω : outlives_ctx) captured Rcap s_args R_args Σ_args
      fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
      roots_body,
    captured_call_frame_params_ready env captured Rcap s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove_params (fn_captures fcall)
      (store_remove_params (fn_params fcall) s_body) = s_args.
Proof.
  eapply (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased :
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    store_no_shadow
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    roots_exclude x roots_body ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body))) Σ_args /\
    value_has_type env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body)))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  eapply (eval_captured_call_body_ctx_cleanup_hidden_frame_erased_with_preservation_core
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Lemma eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset :
  forall env (Ω : outlives_ctx) captured s_args_hidden s_args
      Σ_args x T_hidden hidden fdef fcall σ s_body vs ret used'
      T_body Γ_out R_params R_body roots_body roots_bound,
    s_args_hidden = store_add x T_hidden hidden s_args ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    store_no_shadow
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    root_set_stores_subset roots_body roots_bound ->
    roots_exclude x roots_bound ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
      (fn_body fcall) s_body ret ->
    store_typed env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body))) Σ_args /\
    value_has_type env
      (store_remove x
        (store_remove_params (fn_captures fcall)
          (store_remove_params (fn_params fcall) s_body)))
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_remove x
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) = s_args.
Proof.
  intros env Ω captured s_args_hidden s_args Σ_args x T_hidden hidden
    fdef fcall σ s_body vs ret used' T_body Γ_out R_params R_body
    roots_body roots_bound Hhidden Hcaptured_params_typed Htyped_args
    Hrename Hargs_fcall Hroots_bind Hshadow_bind Hrn_params Hcover_all
    Hprov_body Htyped_body Hcompat_body Hexclude_all Hexclude_env_all
    Hsubset Hroot_exclude_bound Heval_body.
  eapply eval_captured_call_body_ctx_cleanup_hidden_frame_erased;
    try eassumption.
  eapply roots_exclude_stores_subset; eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_hidden_cleanup_package :
  forall env (Ω : outlives_ctx) s s_final m x T fname captures args ret,
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
            (store_remove_params (fn_params fcall) s_body)) /\
      forall sigma_result Σ_args T_body Γ_out R_params R_body roots_body roots_bound,
        captured_params_store_typed env captured (fn_captures fcall) ->
        store_typed env s_args Σ_args ->
        eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
          (fn_params fcall) ->
        store_roots_within R_params
          (bind_params (fn_params fcall) vs
            (captured ++ s_args_hidden)) ->
        store_no_shadow
          (bind_params (fn_params fcall) vs
            (captured ++ s_args_hidden)) ->
        root_env_no_shadow R_params ->
        root_env_covers_params (fn_params fcall ++ fn_captures fcall)
          R_params ->
        provenance_ready_expr (fn_body fcall) ->
        typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
          R_params (sctx_of_ctx (fn_body_ctx fcall))
          (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
        ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
        roots_exclude_params (fn_params fcall ++ fn_captures fcall)
          roots_body ->
        root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
          R_body ->
        root_set_stores_subset roots_body roots_bound ->
        roots_exclude x roots_bound ->
        store_typed env s_final Σ_args /\
        value_has_type env s_final ret (apply_lt_ty sigma_result (fn_ret fdef)) /\
        s_final = s_args.
Proof.
  intros env Ω s s_final m x T fname captures args ret Husage Heval Hready
    Hfree Hlocal Hrefs.
  destruct (eval_let_make_closure_captured_call_args_strip
              env s s_final m x T fname captures args ret Husage Heval
              Hready Hfree Hlocal Hrefs)
    as (captured & fdef & s_args_hidden & s_args & vs & fcall & used' &
        s_body & Hlookup & Hcopy & Hhidden & Heval_args & Hrefs_args &
        Hvs_refs & Hrename & Heval_body & Hfinal).
  exists captured, fdef, s_args_hidden, s_args, vs, fcall, used', s_body.
  split; [exact Hlookup|].
  split; [exact Hcopy|].
  split; [exact Hhidden|].
  split; [exact Heval_args|].
  split; [exact Hrefs_args|].
  split; [exact Hvs_refs|].
  split; [exact Hrename|].
  split; [exact Heval_body|].
  split; [exact Hfinal|].
  intros ? ? ? ? ? ? ? ?
    Hcaptured_params Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
    Hexclude_env_all Hsubset Hroot_exclude_bound.
  subst s_final.
  eapply eval_captured_call_body_ctx_cleanup_hidden_frame_erased_subset;
    eassumption.
Qed.

Lemma eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased :
  forall env (Ω : outlives_ctx) s s_fn s_args s_body callee args fname
      captured fdef fcall vs ret used' Rcap R_args Σ_args σ T_body Γ_out
      R_params R_body roots_body,
    eval env s callee s_fn (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s_fn args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    captured_call_frame_params_ready env captured Rcap s_args R_args
      (fn_captures fcall) ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr callee args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  intros env Ω s s_fn s_args s_body callee args fname captured fdef fcall
    vs ret used' Rcap R_args Σ_args σ T_body Γ_out R_params R_body
    roots_body Heval_callee Hlookup Heval_args Hrename Heval_body
    Hframe_params_ready Htyped_args Hargs_fcall Hroots_bind Hshadow_bind
    Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body
    Hexclude_all Hexclude_env_all.
  split.
  - eapply Eval_CallExpr; eassumption.
  - destruct (eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased
                env Ω captured Rcap s_args R_args Σ_args fdef fcall σ
                s_body vs ret used' T_body Γ_out R_params R_body roots_body
                Hframe_params_ready Htyped_args Hrename Hargs_fcall
                Hroots_bind Hshadow_bind Hrn_params Hcover_all Hprov_body
                Htyped_body Hcompat_body Hexclude_all Hexclude_env_all
                Heval_body)
      as [Hstore [Hv _]].
    split; assumption.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased :
  forall env (Ω : outlives_ctx) s s_args s_body args fname captures
      captured fdef fcall vs ret used' Rcap R_args Σ Σ_args captured_tys
      σ T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  intros env Ω s s_args s_body args fname captures captured fdef fcall vs
    ret used' Rcap R_args Σ Σ_args captured_tys σ T_body Γ_out R_params
    R_body roots_body Hstore Heval_make Hlookup Heval_args Hrename
    Heval_body Hcheck Hframe_ready Htyped_args Hargs_fcall Hroots_bind
    Hshadow_bind Hrn_params Hcover_all Hprov_body Htyped_body Hcompat_body
    Hexclude_all Hexclude_env_all.
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready
      env Ω s Σ fname captures captured fdef fcall used' Rcap s_args
      R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck
      Hframe_ready) as Hframe_params_ready.
  eapply eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased;
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto :
  forall env (Ω : outlives_ctx) s s_args s_body args fname captures
      captured fdef fcall vs ret used' R_args Σ Σ_args captured_tys
      σ T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures (fn_captures fdef) =
      infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    store_typed env s_args Σ_args ->
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    store_no_shadow (bind_params (fn_params fcall) vs (captured ++ s_args)) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall ++ fn_captures fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall) roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall) R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty σ (fn_ret fdef)).
Proof.
  intros env Ω s s_args s_body args fname captures captured fdef fcall vs
    ret used' R_args Σ Σ_args captured_tys σ T_body Γ_out R_params R_body
    roots_body Hstore Heval_make Hlookup Heval_args Hrename Heval_body
    Hcheck Hnodup Hready_args Hroots_args Hshadow_args Hrn_args Hnamed_args
    Hkeys_args Htyped_args Hargs_fcall Hroots_bind Hshadow_bind Hrn_params
    Hcover_all Hprov_body Htyped_body Hcompat_body Hexclude_all
    Hexclude_env_all.
  pose proof
    (eval_make_closure_exact_captured_call_frame_params_ready_auto
      env Ω s Σ fname captures captured fdef fcall used' args s_args vs
      R_args captured_tys Hstore Heval_make Hlookup Hrename Hcheck Hnodup
      Hready_args Heval_args Hroots_args Hshadow_args Hrn_args Hnamed_args
      Hkeys_args) as Hframe_params_ready.
  eapply eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased;
    eassumption.
Qed.

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall σ s s_args s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    provenance_ready_args args ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = s_args /\
    value_roots_within roots_body ret.
Proof.
  eapply (eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core
            eval_preserves_typing_ready_mutual
            eval_preserves_roots_ready_mutual
            eval_preserves_frame_scope_roots_ready_mutual
            eval_preserves_typing_roots_ready_prefix_mutual
            eval_preserves_param_scope_roots_ready_mutual);
    eassumption.
Qed.

Theorem eval_preserves_typing_ready_with_call_invariants_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  split.
  - intros env s e s' v Heval _ _ Ω n Σ T Σ' Hready Hstore Htyped.
    exact (proj1 eval_preserves_typing_ready_mutual env s e s' v Heval
      Ω n Σ T Σ' Hready Hstore Htyped).
  - split.
    + intros env s args s' vs Heval _ _ Ω n Σ ps Σ' Hready Hstore Htyped.
      exact (proj1 (proj2 eval_preserves_typing_ready_mutual)
        env s args s' vs Heval Ω n Σ ps Σ' Hready Hstore Htyped).
    + intros env s fields defs s' values Heval _ _ Ω n lts args Σ Σ'
        Hready Hstore Htyped.
      exact (proj2 (proj2 eval_preserves_typing_ready_mutual)
        env s fields defs s' values Heval Ω n lts args Σ Σ'
        Hready Hstore Htyped).
Qed.

Lemma eval_let_roots_ready_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R R' Σ Σ' s s'
      m x T_ann e1 e2 T roots v,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ (ELet m x T_ann e1 e2) T Σ' R' roots ->
    provenance_ready_expr (ELet m x T_ann e1 e2) ->
    preservation_ready_expr e1 ->
    preservation_ready_expr e2 ->
    eval env s (ELet m x T_ann e1 e2) s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' v T /\
    store_ref_targets_preserved env s s' /\
    store_roots_within R' s' /\
    value_roots_within roots v /\
    store_no_shadow s' /\
    root_env_no_shadow R'.
Proof.
  intros env Ω n R R' Σ Σ' s s' m x T_ann e1 e2 T roots v
    Hstore Hroots Hnodup Hrn Htyped Hready Hready1_struct
    Hready2_struct Heval.
  destruct (proj1 eval_preserves_roots_ready_mutual env s
              (ELet m x T_ann e1 e2) s' v Heval
              Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped)
    as [Hroots_final [Hv_roots [Hnodup_final Hrn_final]]].
  dependent destruction Hready.
  inversion Heval; subst.
  inversion Htyped; subst.
  match goal with
  | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
      ?R1_body ?roots1_body,
    Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
    Hfresh : root_env_lookup x ?R1_body = None,
    Htyped2 : typed_env_roots env Ω n
      (root_env_add x ?roots1_body ?R1_body)
      (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
      ?R2_body ?roots2_body,
    Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
    Hexcl_roots : roots_exclude x ?roots2_body,
    Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
    Heval1 : eval env s e1 ?s1_body ?v1_body,
    Heval2 : eval env (store_add x T_ann ?v1_body ?s1_body) e2
      ?s2_body ?v2_body |- _ =>
      let Hpres1 := fresh "Hpres1" in
      let Hpres2 := fresh "Hpres2" in
      assert (Hpres1 :
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
        eval env s e1 s1_body v1_body ->
        store_typed env s1_body Σ1_body /\
        value_has_type env s1_body v1_body T1_body /\
        store_ref_targets_preserved env s s1_body);
      [ intros Hstore0 Htyped0 Heval0;
        exact (proj1 eval_preserves_typing_ready_mutual env s e1
          s1_body v1_body Heval0 Ω n Σ T1_body Σ1_body
          Hready1_struct Hstore0 Htyped0)
      | assert (Hpres2 :
          store_typed env (store_add x T_ann v1_body s1_body)
            (sctx_add x T_ann m Σ1_body) ->
          typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
            e2 T2_body Σ2_body ->
          eval env (store_add x T_ann v1_body s1_body) e2 s2_body v2_body ->
          store_typed env s2_body Σ2_body /\
          value_has_type env s2_body v2_body T2_body /\
          store_ref_targets_preserved env
            (store_add x T_ann v1_body s1_body) s2_body);
        [ intros Hstore0 Htyped0 Heval0;
          exact (proj1 eval_preserves_typing_ready_mutual env
            (store_add x T_ann v1_body s1_body) e2 s2_body v2_body
            Heval0 Ω n (sctx_add x T_ann m Σ1_body) T2_body
            Σ2_body Hready2_struct Hstore0 Htyped0)
        | destruct (eval_let_roots_preserves_typing env Ω n R R1_body
            R2_body Σ Σ1_body Σ2_body s s1_body s2_body m x T_ann
            T1_body e1 e2 T2_body roots1_body roots2_body v1_body
            v2_body Hstore Hroots Hnodup Hrn Htyped1 Hcompat Hfresh
            Htyped2 Hcheck Hexcl_roots Hexcl_env Hready1 Hready2 Heval1
            Heval2 Hpres1 Hpres2)
          as [Hstore_final [Hv_final Hpres_final]];
          repeat split; assumption ]
      ]
  end.
Qed.

Theorem eval_preserves_typing_roots_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  assert (Htyping : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hstore _ _ _ Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots Hready Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction; eassumption.
    + assert (Hmove_pair :
        store_typed env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : provenance_ready_fields ?fields0,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ ?fields0
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hstore Hroots Hnodup Hrn Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
        ?R1_body ?roots1_body,
      Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
      Hfresh : root_env_lookup x ?R1_body = None,
      Htyped2 : typed_env_roots env Ω n
        (root_env_add x ?roots1_body ?R1_body)
        (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
        ?R2_body ?roots2_body,
      Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
      Hexcl_roots : roots_exclude x ?roots2_body,
      Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
      Hready1 : provenance_ready_expr e1,
      Hready2 : provenance_ready_expr e2 |- _ =>
        let Hpres1 := fresh "Hpres1" in
        let Hpres2 := fresh "Hpres2" in
        assert (Hpres1 :
          store_typed env s Σ ->
          typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
          eval env s e1 s1 v1 ->
          store_typed env s1 Σ1_body /\
          value_has_type env s1 v1 T1_body /\
          store_ref_targets_preserved env s s1);
        [ intros Hstore0 _ Heval0;
          exact (IH1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hstore0 Hroots Hnodup Hrn Htyped1)
        | destruct (proj1 eval_preserves_roots_ready_mutual env s e1
            s1 v1 Heval1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]];
          assert (Hfresh_store : store_lookup x s1 = None)
            by (eapply store_roots_within_lookup_none; eassumption);
          assert (Hadd_roots :
            store_roots_within (root_env_add x roots1_body R1_body)
              (store_add x T_ann v1 s1))
            by (eapply store_add_roots_within; eassumption);
          assert (Hadd_nodup :
            store_no_shadow (store_add x T_ann v1 s1))
            by (apply store_no_shadow_add; assumption);
          assert (Hadd_rn :
            root_env_no_shadow (root_env_add x roots1_body R1_body))
            by (apply root_env_no_shadow_add; assumption);
          assert (Hpres2 :
            store_typed env (store_add x T_ann v1 s1)
              (sctx_add x T_ann m Σ1_body) ->
            typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
              e2 T2_body Σ2_body ->
            eval env (store_add x T_ann v1 s1) e2 s2 v2 ->
            store_typed env s2 Σ2_body /\
            value_has_type env s2 v2 T2_body /\
            store_ref_targets_preserved env
              (store_add x T_ann v1 s1) s2);
          [ intros Hstore0 _ Heval0;
            exact (IH2 Ω n (root_env_add x roots1_body R1_body)
              (sctx_add x T_ann m Σ1_body) T2_body Σ2_body R2_body
              roots2_body Hready2 Hstore0 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
          | eapply eval_let_roots_preserves_typing;
            eassumption ] ]
    end.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ' R' roots_e Hready_e
                    Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup
      Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hstore Hroots
      Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped.
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H4 H2)
        as [Hx Hpath].
      subst x path.
      destruct (store_typed_lookup env s_r Σ x1 se Hstore Hlookup)
        as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_static [st_static [HΣstatic [_ Htype_path]]]].
      rewrite HΣstatic in HΣ.
      inversion HΣ; subst T_static st_static.
      rewrite HTy in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H5 H2)
        as [Hx Hpath].
      subst x path.
      destruct (store_typed_lookup env s_r Σ x1 se Hstore Hlookup)
        as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_static [st_static [HΣstatic [_ Htype_path]]]].
      rewrite HΣstatic in HΣ.
      inversion HΣ; subst T_static st_static.
      rewrite HTy in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2
                    Hready_then Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
      | Hready_cond : provenance_ready_expr e1,
        Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
        Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
        Hready_else : provenance_ready_expr e3,
        Htyped_else : typed_env_roots env Ω n ?R1 Σ1 e3 ?T3 ?Σ3 ?R3 ?roots3,
        Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3
                    Hready_else Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq;
            [ eapply typed_env_roots_structural; exact Htyped_then
            | eapply typed_env_roots_structural; exact Htyped_else ]);
        split;
        [ eapply store_typed_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1 Σ1 ps_rest Σ' R' roots_rest
                    Hready_rest Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args R Σ Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args R Σ Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_roots env Ω n lts args ?R1 ?Σ1
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hstore Hroots Hnodup Hrn Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest
                    Hready Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 (Htyping env0) s0 e0 s0' v0 Heval
                Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' [Hv Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual env0 s0 e0 s0' v0
                Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 (Htyping env0)) s0 args0 s0' vs0 Heval
                  Ω0 n0 R0 Σ0 ps0 Σ0' R0' roots0
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0' R0'
                  roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hstore Hroots Hnodup Hrn
        Htyped.
      destruct (proj2 (proj2 (Htyping env0)) s0 fields0 defs0 s0'
                  values0 Heval Ω0 n0 lts0 args0 R0 Σ0 Σ0' R0'
                  roots0 Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 R0
                  Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.

Theorem eval_preserves_root_names_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s').
Proof.
  apply eval_preserves_root_names_ready_mutual_core.
  exact eval_preserves_typing_roots_ready_mutual.
Qed.

Lemma eval_args_root_subst_images_exclude_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_subst_images_exclude_names
      (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fcall) arg_roots).
Proof.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Htyped_args Hrename.
  destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Hnamed Htyped_args)
    as [_ Harg_roots_named].
  eapply alpha_rename_fn_def_body_root_subst_images_exclude_names_from_store_roots;
    eassumption.
Qed.

Theorem eval_preserves_root_keys_named_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s').
Proof.
  apply eval_preserves_root_keys_named_ready_mutual_core.
  exact eval_preserves_typing_roots_ready_mutual.
Qed.

Lemma eval_make_closure_captured_call_runtime_args_ready_auto :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args vs R_args Σ_args arg_roots captured_tys,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args R_args
      (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args)).
Proof.
  eapply
    (eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_runtime_args_ready_auto :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args_hidden s_args vs R_args Σ_args arg_roots captured_tys x T,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    lookup_fn fname (env_fns env) = Some fdef ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    s_args_hidden = store_add x T (VClosure fname captured) s_args ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
      (fcall, used') ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    ~ In x (store_names captured) ->
    captured_call_frame_params_ready env captured
      (empty_root_env_for_store captured) s_args_hidden
      (root_env_add x [] R_args) (fn_captures fcall) /\
    store_typed env s_args Σ_args /\
    eval_args_values_have_types env Ω (captured ++ s_args_hidden) vs
      (fn_params fcall) /\
    Forall2 value_roots_within arg_roots vs /\
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args))
      (bind_params (fn_params fcall) vs (captured ++ s_args_hidden)) /\
    store_no_shadow (bind_params (fn_params fcall) vs
      (captured ++ s_args_hidden)) /\
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)) /\
    root_env_covers_params (fn_params fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args)).
Proof.
  eapply
    (eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core
      eval_preserves_typing_ready_mutual
      eval_preserves_roots_ready_mutual
      eval_preserves_root_names_ready_mutual
      eval_preserves_root_keys_named_ready_mutual);
    eassumption.
Qed.

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    provenance_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body ->
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros env Ω n R Σ args fname captures captured fdef fcall used'
    s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
    T_body Γ_out R_body roots_body Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Heval_make Hlookup Heval_args Hrename Heval_body Hcheck Hnodup_caps
    Hready_args Htyped_args Hprov_body Htyped_body Hcompat_body
    Hexclude_roots Hexclude_env.
  destruct (eval_make_closure_captured_call_runtime_args_ready_auto
              env Ω n R Σ args fname captures captured fdef fcall used'
              s s_args vs R_args Σ_args arg_roots captured_tys
              Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_make Hlookup
              Heval_args Hrename Hcheck Hnodup_caps Hready_args
              Htyped_args)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [_ [Hroots_bind [Hshadow_bind
          [Hrn_bind Hcover_params]]]]]]].
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hcover_all :
    root_env_covers_params (fn_params fcall ++ fn_captures fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))).
  { eapply captured_call_runtime_root_env_covers_params_captures;
      eassumption. }
  destruct (eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased
              env Ω s s_args s_body args fname captures captured fdef
              fcall vs ret used'
              (empty_root_env_for_store captured) R_args Σ Σ_args
              captured_tys [] T_body Γ_out
              (call_param_root_env (fn_params fcall) arg_roots
                (empty_root_env_for_store captured ++ R_args))
              R_body roots_body Hstore Heval_make Hlookup Heval_args
              Hrename Heval_body Hcheck Hframe_ready Hstore_args
              Hargs_fcall Hroots_bind Hshadow_bind Hrn_bind Hcover_all
              Hprov_body Htyped_body Hcompat_body Hexclude_roots
              Hexclude_env)
    as [Heval_final [Hstore_final Hv_final]].
  repeat split; assumption.
Qed.

Lemma root_env_store_keys_named_excludes_names :
  forall R s names,
    root_env_store_keys_named R s ->
    Forall (fun x => ~ In x (store_names s)) names ->
    forall x, In x names -> root_env_lookup x R = None.
Proof.
  intros R s names Hnamed Hfresh x Hin.
  eapply root_env_store_keys_named_lookup_excludes_name.
  - exact Hnamed.
  - apply (proj1 (Forall_forall _ _) Hfresh). exact Hin.
Qed.

Lemma eval_args_root_keys_exclude_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_keys_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    forall x,
      In x (expr_local_store_names (fn_body fcall)) ->
      root_env_lookup x R_args = None.
Proof.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Htyped_args Hrename x Hin.
  pose proof (proj1 (proj2 eval_preserves_root_keys_named_ready_mutual)
                env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
                R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
                Hnamed Htyped_args)
    as Harg_keys_named.
  eapply root_env_store_keys_named_excludes_names.
  - exact Harg_keys_named.
  - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
    exact Hrename.
  - exact Hin.
Qed.

Lemma eval_args_root_tail_fresh_names_for_fresh_call :
  forall env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
      fdef fcall used',
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    root_env_tail_fresh_names (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env Ω n R Σ ps_typed Σ_args R_args arg_roots args s s_args vs
    fdef fcall used' Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Htyped_args Hrename x Hin.
  destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
              Hnamed Htyped_args)
    as [Harg_roots_named _].
  pose proof (proj1 (proj2 eval_preserves_root_keys_named_ready_mutual)
                env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
                R_args arg_roots Hprov_args Hstore Hroots Hshadow Hrn
                Hkeys Htyped_args)
    as Harg_keys_named.
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names s_args) fdef fcall used' Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names s_args)).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes.
    + eapply typed_args_roots_no_shadow; eassumption.
    + exact Hexcl.
Qed.

Lemma captured_call_frame_root_tail_fresh_names_for_fresh_call :
  forall env captured Rcap s_args R_args fdef fcall used',
    captured_call_frame_ready env captured Rcap s_args R_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) (Rcap ++ R_args))
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env captured Rcap s_args R_args fdef fcall used'
    Hframe Hrename x Hin.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [_ [_ [_ [Hrn_tail [Hnamed_tail Hkeys_tail]]]]].
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names (captured ++ s_args))).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x (Rcap ++ R_args) = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x (Rcap ++ R_args)).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes; assumption.
Qed.

Lemma eval_args_root_names_excludes_params_ready :
  forall env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots
      ps_bind,
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    params_fresh_in_store ps_bind s_args ->
    root_env_excludes_params ps_bind R_args.
Proof.
  intros env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots
    ps_bind Heval Hready Hstore Hroots Hnodup Hrn Hnamed Htyped Hfresh.
  destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval Ω n R Σ ps Σ_args R_args
              arg_roots Hready Hstore Hroots Hnodup Hrn Hnamed Htyped)
    as [Hnamed_args _].
  eapply root_env_store_roots_named_excludes_params; eassumption.
Qed.

Lemma eval_args_root_sets_union_excludes_fresh_name :
  forall env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots x,
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    ~ In x (store_names s) ->
    roots_exclude x (root_sets_union arg_roots).
Proof.
  intros env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots x
    Heval Hready Hstore Hroots Hnodup Hrn Hnamed Htyped Hfresh.
  pose proof (preservation_ready_args_implies_provenance_ready args Hready)
    as Hprov.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
              env s args s_args vs Heval Hready) as Hnames.
  destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval Ω n R Σ ps Σ_args R_args
              arg_roots Hprov Hstore Hroots Hnodup Hrn Hnamed Htyped)
    as [_ Harg_roots_named].
  eapply root_sets_union_store_roots_named_excludes_name.
  - exact Harg_roots_named.
  - rewrite Hnames. exact Hfresh.
Qed.

Lemma direct_call_callee_body_root_shadow_summary_bridge_of_unique :
  forall env,
    fn_env_unique_by_name env ->
    direct_call_callee_body_root_shadow_summary_bridge env.
Proof.
  intros env Hunique Hsummary Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  destruct (env_fns_root_shadow_summary_evidence_in_unique
              env Hsummary Hunique fname fdef Hin Hfname)
    as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov_body & Hready_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { rewrite <- (apply_lt_params_length σ (fn_params fdef)).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call; eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply eval_args_root_names_excludes_params_ready; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hready_fcall : preservation_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_preservation_ready_body; eassumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply preservation_ready_implies_provenance_ready.
    exact Hready_fcall. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_ready_at.
  exists T_body, Γ_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots args fdef fcall σ s s_args
    vs used' Hsummary Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { rewrite <- (apply_lt_params_length σ (fn_params fdef)).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply eval_args_root_tail_fresh_names_for_fresh_call; eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply eval_args_root_names_excludes_params_ready; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hsame_body_r :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall))) Γ_out_r).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_renamed. }
  assert (Hroots_set_body_r :
    root_set_sctx_roots_named roots_body_r Γ_out_r).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    destruct (Hroots_expr
                (initial_root_env_for_params_origin
                  (fn_params fdef) (fn_params fcall))
                (sctx_of_ctx (params_ctx (fn_params fcall)))
                (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
                Htyped_renamed Hrn_initial_r
                (initial_root_env_for_params_origin_sctx_roots_named
                  (fn_params fdef) (fn_params fcall)))
      as [_ Hroots_set].
    exact Hroots_set. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply root_set_no_store_of_sctx_named_excludes_params; eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply root_set_stores_subset_equiv.
    - exact Hroots_inst_equiv.
    - eapply root_set_instantiate_no_store_stores_subset_root_sets_union.
      exact Hroots_body_r_no_store. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Γ_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots args fdef fcall σ s s_args
    vs used' Hsummary Hcaps Htyped_args Heval_args Hprov_args Hstore Hroots
    Hshadow Hrn Hnamed Hkeys Hrename.
  destruct
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset
      env Ω n R Σ Σ_args R_args arg_roots args fdef fcall σ s s_args vs
      used' Hsummary Hcaps Htyped_args Heval_args Hprov_args Hstore Hroots
      Hshadow Hrn Hnamed Hkeys Hrename)
    as (T_body & Γ_out & R_body & roots_body &
        Hprov_body & Htyped_body & Hcompat_body &
        Hexclude_roots & Hexclude_env & _).
  unfold callee_body_root_shadow_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma eval_make_closure_captured_call_expr_preserves_typing_with_callee_components :
  forall env Ω n R Σ args fname captures captured fdef fcall used'
      s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    eval env s (EMakeClosure fname captures) s (VClosure fname captured) ->
    lookup_fn fname (env_fns env) = Some fdef ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs (captured ++ s_args))
      (fn_body fcall) s_body ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    eval env s (ECallExpr (EMakeClosure fname captures) args)
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) ret /\
    store_typed env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body)) Σ_args /\
    value_has_type env
      (store_remove_params (fn_captures fcall)
        (store_remove_params (fn_params fcall) s_body))
      ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros env Ω n R Σ args fname captures captured fdef fcall used'
    s s_args s_body vs ret R_args Σ_args arg_roots captured_tys
    T_body Γ_out R_body roots_body Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Heval_make Hlookup Heval_args Hrename Heval_body Hcheck Hnodup_caps
    Hready_args Htyped_args Hnodup_binding Hprov_body Htyped_body
    Hcompat_body Hexclude_roots Hexclude_env.
  destruct (eval_make_closure_captured_call_runtime_args_ready_auto
              env Ω n R Σ args fname captures captured fdef fcall used'
              s s_args vs R_args Σ_args arg_roots captured_tys
              Hstore Hroots Hshadow Hrn Hnamed Hkeys Heval_make Hlookup
              Heval_args Hrename Hcheck Hnodup_caps Hready_args
              Htyped_args)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [Hvalue_roots [Hroots_bind
          [Hshadow_bind [Hrn_bind Hcover_params]]]]]]].
  destruct (alpha_rename_fn_def_binding_initial_support_facts
              (store_names (captured ++ s_args)) fdef fcall used'
              Hrename Hnodup_binding)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_binding & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names (captured ++ s_args)) fdef fcall used'
              Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fdef))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_params
                (fn_params fdef ++ fn_captures fdef))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fdef))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_binding Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_binding.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_binding.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names (captured ++ s_args))
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_binding_roots :
    List.length
      (arg_roots ++ repeat [] (List.length (fn_captures fdef))) =
    List.length (fn_params fdef ++ fn_captures fdef)).
  { rewrite length_app, repeat_length, length_app.
    rewrite Hlen_arg_roots_fdef. reflexivity. }
  assert (Harg_roots_named_sargs :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      arg_roots).
  { pose proof (preservation_ready_args_implies_provenance_ready
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hbinding_roots_named :
    Forall
      (fun roots => root_set_store_roots_named roots (captured ++ s_args))
      (arg_roots ++ repeat [] (List.length (fn_captures fdef)))).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_weaken_store.
      + exact Harg_roots_named_sargs.
      + intros z Hin. rewrite store_names_app.
        apply in_or_app. right. exact Hin.
    - assert (Hrepeat_named :
        Forall
          (fun roots => root_set_store_roots_named roots (captured ++ s_args))
          (repeat [] (List.length (fn_captures fdef)))).
      { assert (Hrepeat_named_all :
          forall k,
            Forall
              (fun roots =>
                root_set_store_roots_named roots (captured ++ s_args))
              (repeat [] k)).
        { induction k; simpl.
          - constructor.
          - constructor; [apply root_set_store_roots_named_nil | assumption]. }
        apply Hrepeat_named_all. }
      exact Hrepeat_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Hbinding_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hparams_fresh_captured :
    params_fresh_in_store (fn_params fcall) captured).
  { assert (Hfresh :
      params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    unfold params_fresh_in_store in *.
    intros x Hin Hstore_x. apply (Hfresh x Hin).
    rewrite store_names_app. apply in_or_app. left. exact Hstore_x. }
  assert (Hbase_equiv :
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))).
  { eapply captured_call_binding_runtime_root_env_equiv; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_base :
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))).
  { apply call_param_root_env_no_shadow.
    - exact Hnodup_fcall.
    - apply root_env_no_shadow_empty_root_env_for_store.
      unfold captured_call_frame_ready in Hframe_ready.
      destruct Hframe_ready as [[_ [_ [Hshadow_captured _]]] _].
      exact Hshadow_captured. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params
                (fn_params fdef ++ fn_captures fdef)
                (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots
                (empty_root_env_for_store captured))
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_base)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & _ & Hbody_inst_equiv & Hroots_inst_equiv).
  { exact Hbase_equiv. }
  assert (Hfresh_binding_sargs :
    params_fresh_in_store (fn_params fcall ++ fn_captures fcall) s_args).
  { unfold params_fresh_in_store.
    intros x Hin Hstore_x.
    rewrite params_ctx_app, ctx_names_app in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_caps].
    - assert (Hfresh :
        params_fresh_in_store (fn_params fcall) (captured ++ s_args)).
      { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      apply (Hfresh x Hin_params).
      rewrite store_names_app. apply in_or_app. right. exact Hstore_x.
    - pose proof (captured_params_store_typed_store_param_prefix
                    env captured (fn_captures fcall)
                    Hcaptured_params_typed) as Hprefix_caps0.
      pose proof (store_param_prefix_append_frame
                    (fn_captures fcall) captured s_args []
                    Hprefix_caps0) as Hprefix_caps.
      simpl in Hprefix_caps.
      assert (Hshadow_frame : store_no_shadow (captured ++ s_args)).
      { unfold captured_call_frame_ready in Hframe_ready.
        destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
        exact Hshadow_frame. }
      pose proof (store_param_prefix_frame_static_fresh
                    (fn_captures fcall) (captured ++ s_args) s_args
                    Hprefix_caps Hshadow_frame) as Hfresh_caps.
      apply (Hfresh_caps x).
      + unfold sctx_of_ctx. exact Hin_caps.
      + exact Hstore_x. }
  assert (Hbinding_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall ++ fn_captures fcall))
      (arg_roots ++ repeat [] (List.length (fn_captures fdef)))).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_excludes_params; eassumption.
    - assert (Hrepeat_exclude :
        Forall (roots_exclude_params
          (fn_params fcall ++ fn_captures fcall))
          (repeat [] (List.length (fn_captures fdef)))).
      { assert (Hrepeat_exclude_all :
          forall k,
            Forall (roots_exclude_params
              (fn_params fcall ++ fn_captures fcall))
              (repeat [] k)).
        { intros k. apply Forall_forall. intros roots Hin_repeat.
          apply repeat_spec in Hin_repeat. subst roots.
          unfold roots_exclude_params, roots_exclude.
          intros x Hin Hroot. contradiction. }
        apply Hrepeat_exclude_all. }
      exact Hrepeat_exclude. }
  assert (Himages_exclude :
    forall x,
      In x
        (ctx_names
          (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Hbinding_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply captured_call_runtime_args_tail_fresh_names_for_fresh_call;
      eassumption. }
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold captured_call_frame_ready in Hframe_ready.
    destruct Hframe_ready as [_ [_ [_ [Hrn_tail _]]]].
    unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_args : root_env_store_roots_named R_args s_args).
  { pose proof (preservation_ready_args_implies_provenance_ready
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [Henv_named _].
    exact Henv_named. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { eapply captured_call_runtime_args_tail_excludes_binding_params;
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured) ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_decompose :
    call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured ++ R_args) =
    call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured) ++
      root_env_remove_params (fn_params fcall) R_args).
  { apply captured_call_runtime_root_env_tail_decompose.
    intros x Hin.
    eapply empty_root_env_for_store_params_fresh_lookup_none; eassumption. }
  assert (Htyped_tail_roots :
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { rewrite Houts. rewrite Hlts.
    rewrite Htail_decompose.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_tail. }
  assert (Hcompat_fcall :
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true).
  { rewrite Houts. rewrite Hret. exact Hcompat_body. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  eapply eval_make_closure_captured_call_expr_preserves_typing_with_instantiated_body;
    eassumption.
Qed.

Lemma eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components :
  forall env Ω n R Σ m x T args fname captures fdef
      s s_final ret R_args Σ_args arg_roots captured_tys
      T_body Γ_out R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args (fn_params fdef)
      Σ_args R_args arg_roots ->
    NoDup (ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))) ->
    provenance_ready_expr (fn_body fdef) ->
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef))
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true ->
    roots_exclude_params (fn_params fdef ++ fn_captures fdef)
      roots_body ->
    root_env_excludes_params (fn_params fdef ++ fn_captures fdef)
      R_body ->
    lookup_fn fname (env_fns env) = Some fdef ->
    ~ In x (store_names s) ->
    ~ In x (ctx_names (params_ctx (fn_captures fdef))) ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_typed env s_final Σ_args /\
    value_has_type env s_final ret (apply_lt_ty [] (fn_ret fdef)).
Proof.
  intros env Ω n R Σ m x T args fname captures fdef s s_final ret
    R_args Σ_args arg_roots captured_tys T_body Γ_out R_body roots_body
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Husage Heval Hcheck Hnodup_caps
    Hready_args Htyped_args Hnodup_binding Hprov_body Htyped_body
    Hcompat_body Hexclude_roots Hexclude_env Hlookup Hfresh_s
    Hfresh_cap_names Hfree_args Hlocal_args.
  assert (Hrefs_s : store_refs_exclude_root x s).
  { eapply store_roots_within_named_fresh_refs_exclude_root; eassumption. }
  destruct (eval_let_make_closure_captured_call_hidden_cleanup_package
              env Ω s s_final m x T fname captures args ret Husage Heval
              Hready_args Hfree_args Hlocal_args Hrefs_s)
    as (captured & fdef_pkg & s_args_hidden & s_args & vs & fcall &
        used' & s_body & Hlookup_pkg & Hcopy & Hhidden & Heval_args &
        Hrefs_args & Hvs_refs & Hrename & Heval_body & Hfinal & Hcleanup).
  assert (Hfdef_eq : fdef_pkg = fdef).
  { eapply lookup_fn_deterministic; eassumption. }
  subst fdef_pkg.
  assert (Hfresh_captured : ~ In x (store_names captured)).
  { rewrite (copy_capture_store_as_store_names
               captures (fn_captures fdef) s captured Hcopy).
    exact Hfresh_cap_names. }
  destruct (eval_let_make_closure_captured_call_runtime_args_ready_auto
              env Ω n R Σ args fname captures captured fdef fcall used'
              s s_args_hidden s_args vs R_args Σ_args arg_roots
              captured_tys x T Hstore Hroots Hshadow Hrn Hnamed Hkeys
              Hlookup Hcopy Hhidden Heval_args Hrename Hcheck Hnodup_caps
              Hready_args Htyped_args Hfresh_s Hfresh_captured)
    as [[Hframe_ready Hcaptured_params_typed]
        [Hstore_args [Hargs_fcall [Hvalue_roots [Hroots_bind
          [Hshadow_bind [Hrn_bind Hcover_params]]]]]]].
  destruct (alpha_rename_fn_def_binding_initial_support_facts
              (store_names (captured ++ s_args_hidden)) fdef fcall used'
              Hrename Hnodup_binding)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_binding & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names (captured ++ s_args_hidden)) fdef fcall used'
              Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fdef))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_params
                (fn_params fdef ++ fn_captures fdef))
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (sctx_of_ctx (fn_body_ctx fdef))
              (sctx_of_ctx (fn_body_ctx fcall))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_binding Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall ++ fn_captures fcall)
      roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_binding.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_binding.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape
                (store_names (captured ++ s_args_hidden)) fdef fcall used'
                Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Harg_roots_named_sargs :
    Forall (fun roots => root_set_store_roots_named roots s_args)
      arg_roots).
  { pose proof (preservation_ready_args_implies_provenance_ready
                  args Hready_args) as Hprov_args.
    destruct (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hbinding_roots_named :
    Forall
      (fun roots =>
        root_set_store_roots_named roots (captured ++ s_args_hidden))
      (arg_roots ++ repeat [] (List.length (fn_captures fdef)))).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_weaken_store.
      + exact Harg_roots_named_sargs.
      + intros z Hin. rewrite store_names_app.
        apply in_or_app. right.
        subst s_args_hidden. simpl. right. exact Hin.
    - assert (Hrepeat_named :
        Forall
          (fun roots =>
            root_set_store_roots_named roots (captured ++ s_args_hidden))
          (repeat [] (List.length (fn_captures fdef)))).
      { assert (Hrepeat_named_all :
          forall k,
            Forall
              (fun roots =>
                root_set_store_roots_named roots (captured ++ s_args_hidden))
              (repeat [] k)).
        { induction k; simpl.
          - constructor.
          - constructor; [apply root_set_store_roots_named_nil | assumption]. }
        apply Hrepeat_named_all. }
      exact Hrepeat_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Hbinding_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  assert (Hparams_fresh_captured :
    params_fresh_in_store (fn_params fcall) captured).
  { assert (Hfresh :
      params_fresh_in_store (fn_params fcall) (captured ++ s_args_hidden)).
    { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
    unfold params_fresh_in_store in *.
    intros y Hin Hstore_y. apply (Hfresh y Hin).
    rewrite store_names_app. apply in_or_app. left. exact Hstore_y. }
  assert (Hbase_equiv :
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))).
  { eapply captured_call_binding_runtime_root_env_equiv; eassumption. }
  assert (Hnodup_fcall :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hrn_base :
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))).
  { apply call_param_root_env_no_shadow.
    - exact Hnodup_fcall.
    - apply root_env_no_shadow_empty_root_env_for_store.
      unfold captured_call_frame_ready in Hframe_ready.
      destruct Hframe_ready as [[_ [_ [Hshadow_captured _]]] _].
      exact Hshadow_captured. }
  assert (Hfresh_binding_hidden :
    params_fresh_in_store (fn_params fcall ++ fn_captures fcall)
      s_args_hidden).
  { unfold params_fresh_in_store.
    intros y Hin Hstore_y.
    rewrite params_ctx_app, ctx_names_app in Hin.
    apply in_app_or in Hin as [Hin_params | Hin_caps].
    - assert (Hfresh :
        params_fresh_in_store (fn_params fcall)
          (captured ++ s_args_hidden)).
      { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
      apply (Hfresh y Hin_params).
      rewrite store_names_app. apply in_or_app. right. exact Hstore_y.
    - pose proof (captured_params_store_typed_store_param_prefix
                    env captured (fn_captures fcall)
                    Hcaptured_params_typed) as Hprefix_caps0.
      pose proof (store_param_prefix_append_frame
                    (fn_captures fcall) captured s_args_hidden []
                    Hprefix_caps0) as Hprefix_caps.
      simpl in Hprefix_caps.
      assert (Hshadow_frame : store_no_shadow (captured ++ s_args_hidden)).
      { unfold captured_call_frame_ready in Hframe_ready.
        destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
        exact Hshadow_frame. }
      pose proof (store_param_prefix_frame_static_fresh
                    (fn_captures fcall) (captured ++ s_args_hidden)
                    s_args_hidden Hprefix_caps Hshadow_frame) as Hfresh_caps.
      apply (Hfresh_caps y).
      + unfold sctx_of_ctx. exact Hin_caps.
      + exact Hstore_y. }
  assert (Hbinding_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall ++ fn_captures fcall))
      (arg_roots ++ repeat [] (List.length (fn_captures fdef)))).
  { apply Forall_app. split.
    - eapply root_sets_store_roots_named_excludes_params.
      + exact Harg_roots_named_sargs.
      + intros y Hin Hstore_y.
        apply (Hfresh_binding_hidden y Hin).
        subst s_args_hidden. simpl. right. exact Hstore_y.
    - assert (Hrepeat_exclude :
        Forall (roots_exclude_params
          (fn_params fcall ++ fn_captures fcall))
          (repeat [] (List.length (fn_captures fdef)))).
      { assert (Hrepeat_exclude_all :
          forall k,
            Forall (roots_exclude_params
              (fn_params fcall ++ fn_captures fcall))
              (repeat [] k)).
        { intros k. apply Forall_forall. intros roots Hin_repeat.
          apply repeat_spec in Hin_repeat. subst roots.
          unfold roots_exclude_params, roots_exclude.
          intros y Hin Hroot. contradiction. }
        apply Hrepeat_exclude_all. }
      exact Hrepeat_exclude. }
  assert (Himages_exclude :
    forall y,
      In y
        (ctx_names
          (params_ctx (fn_params fcall ++ fn_captures fcall))) ->
      root_subst_images_exclude y
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { intros y Hin_y.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Hbinding_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_y. }
  assert (Hsame_body_r :
    sctx_same_bindings
      (sctx_of_ctx (fn_body_ctx fcall)) Γ_out_r).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_renamed. }
  assert (Hroots_set_body_r :
    root_set_sctx_roots_named roots_body_r Γ_out_r).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    destruct (Hroots_expr
                (initial_root_env_for_params_origin
                  (fn_params fdef ++ fn_captures fdef)
                  (fn_params fcall ++ fn_captures fcall))
                (sctx_of_ctx (fn_body_ctx fcall))
                (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
                Htyped_renamed Hrn_initial_r
                (initial_root_env_for_params_origin_sctx_roots_named
                  (fn_params fdef ++ fn_captures fdef)
                  (fn_params fcall ++ fn_captures fcall)))
      as [_ Hroots_set].
    exact Hroots_set. }
    assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
    { eapply root_set_no_store_of_sctx_named_excludes_params.
      - exact Hsame_body_r.
      - exact Hroots_set_body_r.
      - exact Hexclude_roots_renamed. }
  assert (Hsubset_inst_input :
    root_set_stores_subset (root_set_instantiate
      (root_subst_of_params
        (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
      roots_body_r)
      (root_sets_union
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { eapply root_set_instantiate_no_store_stores_subset_root_sets_union.
    exact Hroots_body_r_no_store. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall)
        (root_env_add x [] R_args))
      (expr_local_store_names (fn_body fcall))).
  { eapply captured_call_runtime_args_tail_fresh_names_for_fresh_call;
      eassumption. }
  pose proof (preservation_ready_args_implies_provenance_ready
                args Hready_args) as Hprov_args.
  pose proof (proj1 (proj2 eval_preserves_root_names_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ (fn_params fdef)
              Σ_args R_args arg_roots Hprov_args Hstore Hroots Hshadow
              Hrn Hnamed Htyped_args) as Hnames_args.
  destruct Hnames_args as [Hnamed_args Harg_roots_named].
  assert (Hrn_hidden_args :
    root_env_no_shadow (root_env_add x [] R_args)).
  { unfold captured_call_frame_ready in Hframe_ready.
    destruct Hframe_ready as [_ [_ [_ [Hrn_tail _]]]].
    unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_hidden_args :
    root_env_store_roots_named (root_env_add x [] R_args)
      s_args_hidden).
  { subst s_args_hidden.
    eapply root_env_store_roots_named_add_env_store_add.
    - exact Hnamed_args.
    - apply root_set_store_roots_named_nil. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall ++ fn_captures fcall)
      (root_env_remove_params (fn_params fcall)
        (root_env_add x [] R_args))).
  { eapply captured_call_runtime_args_tail_excludes_binding_params.
    - exact Hrn_hidden_args.
    - exact Hnamed_hidden_args.
    - exact Hfresh_binding_hidden. }
  assert (Hprov_fcall0 : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Htyped_renamed_fcall :
    typed_env_roots_shadow_safe env (fn_outlives fcall)
      (fn_lifetimes fcall)
      (initial_root_env_for_params_origin
        (fn_params fdef ++ fn_captures fdef)
        (fn_params fcall ++ fn_captures fcall))
      (sctx_of_ctx (fn_body_ctx fcall)) (fn_body fcall) T_body
      Γ_out_r R_body_r roots_body_r).
  { rewrite Houts. rewrite Hlts. exact Htyped_renamed. }
  assert (Hcompat_fcall0 :
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true).
  { rewrite Houts. rewrite Hret. exact Hcompat_body. }
  destruct (captured_call_callee_body_root_shadow_provenance_instantiated_tail_frame
              env
              (initial_root_env_for_params_origin
                (fn_params fdef ++ fn_captures fdef)
                (fn_params fcall ++ fn_captures fcall))
              (call_param_root_env (fn_params fcall) arg_roots
                (empty_root_env_for_store captured))
              (root_env_remove_params (fn_params fcall)
                (root_env_add x [] R_args))
              fcall
              (root_subst_of_params
                (fn_params fdef ++ fn_captures fdef)
                (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
              T_body (ctx_of_sctx Γ_out_r) R_body_r roots_body_r
              (root_sets_union
                (arg_roots ++ repeat [] (List.length (fn_captures fdef)))))
    as (T_body_i & Γ_out_i & R_body_i & roots_body_i &
        Hprov_fcall & Htyped_tail & Hcompat_fcall &
        Hexclude_roots_i & Hexclude_env_i & Hsubset_i);
    try exact Hprov_fcall0;
    try exact Htyped_renamed_fcall;
    try exact Hcompat_fcall0;
    try exact Hexclude_roots_renamed;
    try exact Hexclude_env_renamed;
    try exact Hsubst_fresh;
    try exact Hrn_initial_r;
    try exact Hrn_base;
    try exact Hbase_equiv;
    try exact Himages_exclude;
    try exact Hsubset_inst_input;
    try exact Htail_fresh;
    try exact Htail_exclude.
  assert (Htail_decompose :
    call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured ++ root_env_add x [] R_args) =
    call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured) ++
      root_env_remove_params (fn_params fcall)
        (root_env_add x [] R_args)).
  { apply captured_call_runtime_root_env_tail_decompose.
    intros y Hin.
    eapply empty_root_env_for_store_params_fresh_lookup_none; eassumption. }
  assert (Htyped_tail_roots :
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args))
      (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body_i (sctx_of_ctx Γ_out_i)
      (R_body_i ++
        root_env_remove_params (fn_params fcall)
          (root_env_add x [] R_args))
      roots_body_i).
  { rewrite Htail_decompose. exact Htyped_tail. }
  assert (Hcover_all :
    root_env_covers_params (fn_params fcall ++ fn_captures fcall)
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured ++ root_env_add x [] R_args))).
  { eapply captured_call_runtime_root_env_covers_params_captures;
      eassumption. }
  assert (Hroot_exclude_bound :
    roots_exclude x
      (root_sets_union
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))).
  { apply roots_exclude_root_sets_union_app_repeat_nil.
    eapply eval_args_root_sets_union_excludes_fresh_name; eassumption. }
  destruct (Hcleanup [] Σ_args T_body_i Γ_out_i
              (call_param_root_env (fn_params fcall) arg_roots
                (empty_root_env_for_store captured ++ root_env_add x [] R_args))
              (R_body_i ++
                root_env_remove_params (fn_params fcall)
                  (root_env_add x [] R_args))
              roots_body_i
              (root_sets_union
                (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
              Hcaptured_params_typed Hstore_args Hargs_fcall Hroots_bind
              Hshadow_bind Hrn_bind Hcover_all Hprov_fcall Htyped_tail_roots
              Hcompat_fcall Hexclude_roots_i Hexclude_env_i Hsubset_i
              Hroot_exclude_bound)
    as [Hstore_final [Hv_final _]].
  split; assumption.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique :
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_provenance_summary_evidence env ->
    forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
        (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
        used',
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
      eval_args env s args s_args vs ->
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  intros env Hunique Hsummary Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary;
    try eassumption.
  eapply Hsummary.
  eapply lookup_fn_in_unique_by_name; eassumption.
Qed.

Lemma eval_direct_call_body_provenance_ready_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall σ s s_args s_body vs ret used',
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    provenance_ready_args args ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    fn_captures fdef = [] ->
    callee_body_root_provenance_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body).
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots args fdef fcall σ
    s s_args s_body vs ret used' Hstore Hroots Hshadow Hrn Hprov_args
    Hready_args Htyped_args Heval_args Hrename Hcaps Hbody_ready Heval_body.
  unfold callee_body_root_provenance_ready_at in Hbody_ready.
  destruct Hbody_ready
    as (T_body & Γ_out & R_body & roots_body &
        Hprov_body & Htyped_body & Hcompat_body &
        Hexclude_ret & Hexclude_env).
  destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              (fn_params fcall) Heval_args Hprov_args Htyped_args
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
               (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      env (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
      roots_body Hcaps_call Htyped_body) as Htyped_body_params.
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs
              env Ω n R Σ Σ_args R_args arg_roots (fn_name fdef) args fdef
              fcall σ s s_args s_body vs ret used' T_body Γ_out
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              R_body roots_body Hstore Hroots Hshadow Hrn Hprov_args
              Hready_args Htyped_args Heval_args Hrename Hroots_bind
              Hshadow_bind Hrn_params Hcover_params Hprov_body
              Htyped_body_params Hcompat_body Hexclude_ret Hexclude_env
              Heval_body)
    as [_ [Hstore_final [_ [_ [_ [_ [Hv_final [Hpres_final _]]]]]]]].
  repeat split; assumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_ready :
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_preservation_ready env ->
      direct_call_callee_body_root_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros env s e s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique _ Hcallee_roots.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof (preservation_ready_implies_provenance_ready e Hpres_ready)
      as Hprov.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hstore Hroots Hshadow Hrn Htyped)
      as [Hstore' [Hv [Hpres _]]].
    repeat split; assumption.
  - dependent destruction Heval.
    dependent destruction Htyped.
    match goal with
    | Hready_args0 : preservation_ready_args ?args_call |- _ =>
        pose proof (preservation_ready_args_implies_provenance_ready
                      args_call Hready_args0) as Hprov_args
    end.
    repeat match goal with
    | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
        Some ?f_runtime,
      Hin : In ?f_typed (env_fns env) |- _ =>
        pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
          f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
        subst f_runtime
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : fn_name ?f_typed = ?fname_call |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin Hname Hunique) as Hsame;
        subst f_typed
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : ?fname_call = fn_name ?f_typed |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
        subst f_typed
    end.
    match goal with
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hfname : fn_name ?fdef = ?fname_call,
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (Hcallee_roots Ω n R Σ Σ' R' arg_roots
                      fname_call args_call fdef fcall σ s s_args vs
                      used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_ready_at env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_ready) as Hbody_prov_ready;
        eapply eval_direct_call_body_provenance_ready_preserves_typing;
          eassumption
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (Hcallee_roots Ω n R Σ Σ' R' arg_roots
                      (fn_name fdef) args_call fdef fcall σ s s_args vs
                      used' Hin eq_refl Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_ready_at env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_ready) as Hbody_prov_ready;
        eapply eval_direct_call_body_provenance_ready_preserves_typing;
          eassumption
    end.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready :
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_provenance_summary_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros env s e s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hsummary.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof (preservation_ready_implies_provenance_ready e Hpres_ready)
      as Hprov.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hstore Hroots Hshadow Hrn Htyped)
      as [Hstore' [Hv [Hpres _]]].
    repeat split; assumption.
  - dependent destruction Heval.
    dependent destruction Htyped.
    match goal with
    | Hready_args0 : preservation_ready_args ?args_call |- _ =>
        pose proof (preservation_ready_args_implies_provenance_ready
                      args_call Hready_args0) as Hprov_args
    end.
    repeat match goal with
    | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
        Some ?f_runtime,
      Hin : In ?f_typed (env_fns env) |- _ =>
        pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
          f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
        subst f_runtime
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : fn_name ?f_typed = ?fname_call |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin Hname Hunique) as Hsame;
        subst f_typed
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : ?fname_call = fn_name ?f_typed |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
        subst f_typed
    end.
    match goal with
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hfname : fn_name ?fdef = ?fname_call,
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique
                      env Hunique Hsummary Ω n R Σ Σ' R' arg_roots
                      fname_call args_call fdef fcall σ s s_args vs
                      used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_shadow_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at
            env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_shadow_ready) as Hbody_ready;
        eapply eval_direct_call_body_provenance_ready_preserves_typing;
          eassumption
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique
                      env Hunique Hsummary Ω n R Σ Σ' R' arg_roots
                      (fn_name fdef) args_call fdef fcall σ s s_args vs
                      used' Hin eq_refl Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_shadow_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at
            env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_shadow_ready) as Hbody_ready;
        eapply eval_direct_call_body_provenance_ready_preserves_typing;
          eassumption
    end.
Qed.

Lemma eval_call_expr_fn_as_call :
  forall env s s' v fname args,
    eval env s (ECallExpr (EFn fname) args) s' v ->
    eval env s (ECall fname args) s' v.
Proof.
  intros env s s' v fname args Heval.
  dependent destruction Heval.
  match goal with
  | Hcallee : eval _ _ (EFn _) _ (VClosure _ _) |- _ =>
      dependent destruction Hcallee
  end.
  simpl in *.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?fdef_fn,
    Hcaps_fn : fn_captures ?fdef_fn = [],
    Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?fdef,
    Hargs : eval_args env s args ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
      (?fcall, ?used'),
    Hbody : eval env (bind_params (fn_params ?fcall) ?vs ?s_args)
      (fn_body ?fcall) ?s_body ?ret |- _ =>
      assert (Hsame : fdef_fn = fdef)
        by (eapply lookup_fn_deterministic; eassumption);
      subst fdef;
      assert (Hcaps_call : fn_captures fcall = [])
        by (rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef_fn fcall used' Hrename);
            exact Hcaps_fn);
      rewrite Hcaps_call;
      simpl;
      eapply Eval_Call;
      [ exact Hlookup | exact Hcaps_fn | exact Hargs | exact Hrename | exact Hbody ]
  end.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary :
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots fdef,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_provenance_summary env fdef ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros env s s' v fname args Heval Ω n R Σ T Σ' R' roots fdef
    Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
    Hin_summary Hfname_summary Hcallee_summary.
  pose proof (preservation_ready_args_implies_provenance_ready
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  | Hin : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call,
    Hin0 : In ?f_summary (env_fns env),
    Hname0 : fn_name ?f_summary = ?fname_call |- _ =>
      pose proof (Hunique f_typed f_summary Hin Hin0
        (eq_trans Hname (eq_sym Hname0))) as Hsame;
      subst f_typed
  end.
  assert (Hcaps_fdef1 : fn_captures fdef1 = []) by assumption.
  match goal with
  | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
      (apply_lt_params ?σ (fn_params ?fdef_call)) Σ' R' ?arg_roots,
    Heval_args : eval_args env s ?args_call ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef_call =
      (?fcall, ?used') |- _ =>
      pose proof
        (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset
          env Ω n R Σ Σ' R' arg_roots args_call fdef_call fcall σ
          s s_args vs used' Hcallee_summary Hcaps_fdef1 Htyped_args Heval_args
          Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
        as Hbody_shadow_ready;
      unfold callee_body_root_shadow_provenance_ready_at_result_subset
        in Hbody_shadow_ready;
      destruct Hbody_shadow_ready
        as (T_body & Γ_out & R_body & roots_body &
            Hprov_body & Htyped_shadow_body & Hcompat_body &
            Hexclude_ret & Hexclude_env & Hresult_subset);
      assert (Hcaps_call : fn_captures fcall = [])
        by (rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef_call fcall used' Hrename);
            exact Hcaps_fdef1);
      pose proof (typed_env_roots_shadow_safe_roots
          env (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R')
          (sctx_of_ctx (fn_body_ctx fcall))
          (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body
          Htyped_shadow_body) as Htyped_body_ctx;
      pose proof
        (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
          env (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R')
          fcall (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
          roots_body Hcaps_call Htyped_body_ctx) as Htyped_body
  end.
  destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef1)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef1)) Σ' R'
                arg_roots H6))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef1)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H6)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef1 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef1))
  by (eapply eval_args_values_have_types_apply_lt_params_inv;
      exact Hargs_subst).
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall))
  by (eapply eval_args_values_have_types_params_alpha;
      [ exact Hparams_alpha | exact Hargs_unsubst_fdef ]).
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall))))
  by (eapply alpha_rename_fn_def_params_nodup_ctx_names;
      exact H2).
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args)
  by (eapply alpha_rename_fn_def_params_fresh_in_store;
      exact H2).
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef1)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H6
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs
              env Ω n R Σ Σ' R' arg_roots (fn_name fdef1) args
              fdef1 fcall σ s s_args s_body vs ret used' T_body
              Γ_out (call_param_root_env (fn_params fcall) arg_roots R')
              R_body roots_body Hstore Hroots Hshadow Hrn Hprov_args
              Hready_args H6 H1 H2 Hroots_bind
              Hshadow_bind Hrn_params Hcover_params Hprov_body
              Htyped_body Hcompat_body Hexclude_ret Hexclude_env
              Heval)
    as [_ [Hstore_final [_ [_ [_ [_ [Hv_final
          [Hpres_final Hcleanup_tail]]]]]]]].
  destruct Hcleanup_tail
    as [frame_final [locals_final
        [_ [_ [_ [_ [Hremoved_exact Hret_roots_body]]]]]]].
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Hroots_args.
  - eapply value_roots_within_store_subset; eassumption.
  - rewrite Hremoved_exact. exact Hshadow_args.
Qed.
