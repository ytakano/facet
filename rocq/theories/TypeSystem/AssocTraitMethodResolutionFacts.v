From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program CheckerTraits AssocTraitMethodSigFacts.
From Stdlib Require Import List Bool String.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Associated-projection trait method resolution facts                  *)
(* ------------------------------------------------------------------ *)

Inductive trait_method_resolution_assoc_checked
    (env : global_env) (trait_name : string) (trait_args : list Ty)
    (for_ty : Ty) (method_name : string)
    (t : trait_def) (sig : trait_method_sig)
    (impl : impl_def) (fn : fn_def) : Prop :=
  | TraitMethodResolutionAssocChecked :
      lookup_trait trait_name env = Some t ->
      Nat.eqb (List.length trait_args) (trait_type_params t) = true ->
      find_trait_method_sig method_name (trait_methods t) = Some sig ->
      matching_impls trait_name trait_args for_ty (env_impls env) = [impl] ->
      find_impl_method_def method_name (impl_methods impl) = Some fn ->
      resolve_trait_method_impl env trait_name trait_args for_ty method_name =
        Some impl ->
      resolve_trait_method_def env trait_name trait_args for_ty method_name =
        Some fn ->
      trait_method_sig_assoc_checked env sig fn ->
      trait_method_resolution_assoc_checked
        env trait_name trait_args for_ty method_name t sig impl fn.

Lemma resolve_trait_method_impl_from_components :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    lookup_trait trait_name env = Some t ->
    Nat.eqb (List.length trait_args) (trait_type_params t) = true ->
    find_trait_method_sig method_name (trait_methods t) = Some sig ->
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] ->
    find_impl_method_def method_name (impl_methods impl) = Some fn ->
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn
    Htrait Harity Hsig Himpls Hfn.
  unfold resolve_trait_method_impl.
  rewrite Htrait, Harity, Hsig, Himpls, Hfn.
  reflexivity.
Qed.

Lemma resolve_trait_method_def_from_components :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    lookup_trait trait_name env = Some t ->
    Nat.eqb (List.length trait_args) (trait_type_params t) = true ->
    find_trait_method_sig method_name (trait_methods t) = Some sig ->
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] ->
    find_impl_method_def method_name (impl_methods impl) = Some fn ->
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn
    Htrait Harity Hsig Himpls Hfn.
  unfold resolve_trait_method_def.
  rewrite (resolve_trait_method_impl_from_components
    env trait_name trait_args for_ty method_name t sig impl fn
    Htrait Harity Hsig Himpls Hfn).
  exact Hfn.
Qed.

Lemma trait_method_resolution_assoc_checked_intro :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    lookup_trait trait_name env = Some t ->
    Nat.eqb (List.length trait_args) (trait_type_params t) = true ->
    find_trait_method_sig method_name (trait_methods t) = Some sig ->
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] ->
    find_impl_method_def method_name (impl_methods impl) = Some fn ->
    trait_method_sig_assoc_checked env sig fn ->
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn
    Htrait Harity Hsig Himpls Hfn Hchecked.
  econstructor; eauto.
  - eapply resolve_trait_method_impl_from_components; eauto.
  - eapply resolve_trait_method_def_from_components; eauto.
Qed.

Lemma trait_method_resolution_assoc_checked_inv :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    lookup_trait trait_name env = Some t /\
    Nat.eqb (List.length trait_args) (trait_type_params t) = true /\
    find_trait_method_sig method_name (trait_methods t) = Some sig /\
    matching_impls trait_name trait_args for_ty (env_impls env) = [impl] /\
    find_impl_method_def method_name (impl_methods impl) = Some fn /\
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl /\
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn /\
    trait_method_sig_assoc_checked env sig fn.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn Hres.
  inversion Hres; subst.
  repeat match goal with
  | |- _ /\ _ => split
  end; assumption.
Qed.

Lemma trait_method_resolution_assoc_checked_resolve_impl :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn Hres.
  destruct (trait_method_resolution_assoc_checked_inv _ _ _ _ _ _ _ _ _ Hres)
    as [_ [_ [_ [_ [_ [Himpl _]]]]]].
  exact Himpl.
Qed.

Lemma trait_method_resolution_assoc_checked_resolve_def :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn Hres.
  destruct (trait_method_resolution_assoc_checked_inv _ _ _ _ _ _ _ _ _ Hres)
    as [_ [_ [_ [_ [_ [_ [Hdef _]]]]]]].
  exact Hdef.
Qed.

Lemma trait_method_resolution_assoc_checked_sig :
  forall env trait_name trait_args for_ty method_name t sig impl fn,
    trait_method_resolution_assoc_checked
      env trait_name trait_args for_ty method_name t sig impl fn ->
    trait_method_sig_assoc_checked env sig fn.
Proof.
  intros env trait_name trait_args for_ty method_name t sig impl fn Hres.
  destruct (trait_method_resolution_assoc_checked_inv _ _ _ _ _ _ _ _ _ Hres)
    as [_ [_ [_ [_ [_ [_ [_ Hchecked]]]]]]].
  exact Hchecked.
Qed.

Lemma resolve_trait_method_impl_success :
  forall env trait_name trait_args for_ty method_name impl,
    resolve_trait_method_impl env trait_name trait_args for_ty method_name =
      Some impl ->
    exists t sig fn,
      lookup_trait trait_name env = Some t /\
      Nat.eqb (List.length trait_args) (trait_type_params t) = true /\
      find_trait_method_sig method_name (trait_methods t) = Some sig /\
      matching_impls trait_name trait_args for_ty (env_impls env) = [impl] /\
      find_impl_method_def method_name (impl_methods impl) = Some fn.
Proof.
  intros env trait_name trait_args for_ty method_name impl Hresolve.
  unfold resolve_trait_method_impl in Hresolve.
  destruct (lookup_trait trait_name env) as [t|] eqn:Htrait;
    try discriminate.
  destruct (negb (Nat.eqb (List.length trait_args) (trait_type_params t)))
    eqn:Harity; try discriminate.
  apply negb_false_iff in Harity.
  destruct (find_trait_method_sig method_name (trait_methods t))
    as [sig|] eqn:Hsig; try discriminate.
  destruct (matching_impls trait_name trait_args for_ty (env_impls env))
    as [|impl' rest] eqn:Himpls; try discriminate.
  destruct rest as [|impl'' rest']; try discriminate.
  destruct (find_impl_method_def method_name (impl_methods impl'))
    as [fn|] eqn:Hfn; try discriminate.
  inversion Hresolve; subst.
  exists t, sig, fn.
  repeat split; assumption.
Qed.

Lemma resolve_trait_method_def_success :
  forall env trait_name trait_args for_ty method_name fn,
    resolve_trait_method_def env trait_name trait_args for_ty method_name =
      Some fn ->
    exists impl,
      resolve_trait_method_impl env trait_name trait_args for_ty method_name =
        Some impl /\
      find_impl_method_def method_name (impl_methods impl) = Some fn.
Proof.
  intros env trait_name trait_args for_ty method_name fn Hresolve.
  unfold resolve_trait_method_def in Hresolve.
  destruct (resolve_trait_method_impl env trait_name trait_args for_ty
    method_name) as [impl|] eqn:Himpl; try discriminate.
  destruct (find_impl_method_def method_name (impl_methods impl))
    as [fn'|] eqn:Hfn; try discriminate.
  inversion Hresolve; subst.
  exists impl. split; [reflexivity | exact Hfn].
Qed.
