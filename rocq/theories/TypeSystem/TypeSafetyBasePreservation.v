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

Theorem eval_preserves_typing_ready_mutual_core :
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

Theorem typed_fn_env_structural_big_step_safe_ready_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  forall env f s s' v,
    typed_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpres env f s s' v Htyped_fn Hready Hstore Heval.
  unfold typed_fn_env_structural in Htyped_fn.
  destruct Htyped_fn as
    (T_body & Γ_out & Htyped & Hcompat & _).
  destruct (proj1 Hpres
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

Theorem checked_fn_env_structural_big_step_safe_ready_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  forall env f s s' v,
    checked_fn_env_structural env f ->
    preservation_ready_expr (fn_body f) ->
    store_typed env s (sctx_of_ctx (fn_body_ctx f)) ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
Proof.
  intros Hpres env f s s' v Hchecked Hready Hstore Heval.
  eapply typed_fn_env_structural_big_step_safe_ready_with_preservation_core.
  - exact Hpres.
  - exact (proj1 Hchecked).
  - exact Hready.
  - exact Hstore.
  - exact Heval.
Qed.
