From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program AssocCompatibility.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Associated-projection trait method signature facts                    *)
(* ------------------------------------------------------------------ *)

Definition trait_method_param_assoc_checked
    (env : global_env) (Ω : outlives_ctx)
    (sig_param impl_param : param) : Prop :=
  param_mutability sig_param = param_mutability impl_param /\
  param_name sig_param = param_name impl_param /\
  ty_compatible_assoc_checked env Ω
    (param_ty impl_param) (param_ty sig_param).

Definition trait_method_params_assoc_checked
    (env : global_env) (Ω : outlives_ctx)
    (sig_params impl_params : list param) : Prop :=
  Forall2
    (trait_method_param_assoc_checked env Ω)
    sig_params impl_params.

Definition trait_method_ret_assoc_checked
    (env : global_env) (Ω : outlives_ctx)
    (sig : trait_method_sig) (impl : fn_def) : Prop :=
  ty_compatible_assoc_checked env Ω (fn_ret impl) (trait_method_ret sig).

Inductive trait_method_sig_assoc_checked
    (env : global_env) (sig : trait_method_sig) (impl : fn_def) : Prop :=
  | TraitMethodSigAssocChecked :
      fst (fn_name impl) = trait_method_name sig ->
      fn_lifetimes impl = trait_method_lifetimes sig ->
      fn_type_params impl = trait_method_type_params sig ->
      fn_bounds impl = trait_method_bounds sig ->
      fn_captures impl = [] ->
      trait_method_params_assoc_checked env (fn_outlives impl)
        (trait_method_params sig) (fn_params impl) ->
      trait_method_ret_assoc_checked env (fn_outlives impl) sig impl ->
      trait_method_sig_assoc_checked env sig impl.

Lemma trait_method_params_assoc_checked_length :
  forall env Ω sig_params impl_params,
    trait_method_params_assoc_checked env Ω sig_params impl_params ->
    length sig_params = length impl_params.
Proof.
  intros env Ω sig_params impl_params Hparams.
  induction Hparams.
  - reflexivity.
  - simpl. f_equal. exact IHHparams.
Qed.

Lemma trait_method_params_assoc_checked_nil_inv :
  forall env Ω impl_params,
    trait_method_params_assoc_checked env Ω [] impl_params ->
    impl_params = [].
Proof.
  intros env Ω impl_params Hparams.
  inversion Hparams; subst. reflexivity.
Qed.

Lemma trait_method_params_assoc_checked_cons_inv :
  forall env Ω sig_param sig_params impl_param impl_params,
    trait_method_params_assoc_checked env Ω
      (sig_param :: sig_params) (impl_param :: impl_params) ->
    trait_method_param_assoc_checked env Ω sig_param impl_param /\
    trait_method_params_assoc_checked env Ω sig_params impl_params.
Proof.
  intros env Ω sig_param sig_params impl_param impl_params Hparams.
  inversion Hparams; subst. split; assumption.
Qed.

Lemma trait_method_param_assoc_checked_inv :
  forall env Ω sig_param impl_param,
    trait_method_param_assoc_checked env Ω sig_param impl_param ->
    param_mutability sig_param = param_mutability impl_param /\
    param_name sig_param = param_name impl_param /\
    ty_compatible_assoc_checked env Ω
      (param_ty impl_param) (param_ty sig_param).
Proof.
  intros env Ω sig_param impl_param Hparam.
  exact Hparam.
Qed.

Lemma trait_method_sig_assoc_checked_inv :
  forall env sig impl,
    trait_method_sig_assoc_checked env sig impl ->
    fst (fn_name impl) = trait_method_name sig /\
    fn_lifetimes impl = trait_method_lifetimes sig /\
    fn_type_params impl = trait_method_type_params sig /\
    fn_bounds impl = trait_method_bounds sig /\
    fn_captures impl = [] /\
    trait_method_params_assoc_checked env (fn_outlives impl)
      (trait_method_params sig) (fn_params impl) /\
    trait_method_ret_assoc_checked env (fn_outlives impl) sig impl.
Proof.
  intros env sig impl Hsig.
  inversion Hsig; subst.
  repeat split; assumption.
Qed.

Lemma trait_method_sig_assoc_checked_params_length :
  forall env sig impl,
    trait_method_sig_assoc_checked env sig impl ->
    length (trait_method_params sig) = length (fn_params impl).
Proof.
  intros env sig impl Hsig.
  destruct (trait_method_sig_assoc_checked_inv _ _ _ Hsig)
    as [_ [_ [_ [_ [_ [Hparams _]]]]]].
  eapply trait_method_params_assoc_checked_length. exact Hparams.
Qed.

Lemma trait_method_sig_assoc_checked_intro :
  forall env sig impl,
    fst (fn_name impl) = trait_method_name sig ->
    fn_lifetimes impl = trait_method_lifetimes sig ->
    fn_type_params impl = trait_method_type_params sig ->
    fn_bounds impl = trait_method_bounds sig ->
    fn_captures impl = [] ->
    trait_method_params_assoc_checked env (fn_outlives impl)
      (trait_method_params sig) (fn_params impl) ->
    trait_method_ret_assoc_checked env (fn_outlives impl) sig impl ->
    trait_method_sig_assoc_checked env sig impl.
Proof.
  intros env sig impl Hname Hlts Htparams Hbounds Hcaptures Hparams Hret.
  econstructor; eauto.
Qed.
