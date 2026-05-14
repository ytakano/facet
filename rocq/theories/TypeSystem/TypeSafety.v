From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  OperationalSemantics TypingRules TypeChecker RuntimeTyping EnvStructuralRules
  EnvSoundnessFacts.
From Stdlib Require Import List Bool ZArith String.
Import ListNotations.

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
  - eapply value_has_type_store_irrelevant. exact Hv.
Qed.
