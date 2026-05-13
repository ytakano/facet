From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program TypingRules TypeChecker.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Struct-aware Prop-level checker specification                         *)
(* ------------------------------------------------------------------ *)

(* The legacy [typed] judgment is deliberately left unchanged: it is the
   existing ctx-based rule set used by CheckerSoundness.  The definitions
   below specify the newer executable env/sctx checker in Prop form so that
   struct field paths, partial moves, and path-sensitive borrows have a
   stable proof surface without disturbing the legacy proofs. *)

Inductive typed_place_env (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPE_Checker : forall p T,
      infer_place_sctx env Σ p = infer_ok T ->
      typed_place_env env Σ p T.

Inductive typed_place_type_env (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPTE_Checker : forall p T,
      infer_place_type_sctx env Σ p = infer_ok T ->
      typed_place_type_env env Σ p T.

Inductive typed_env (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TE_Checker : forall fuel Σ e T Σ',
      infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
      typed_env env Ω n Σ e T Σ'
  | TE_Place_Copy : forall Σ p T,
      typed_place_env env Σ p T ->
      ty_usage T = UUnrestricted ->
      typed_env env Ω n Σ (EPlace p) T Σ
  | TE_Place_Move : forall Σ Σ' p T x path,
      typed_place_env env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      typed_env env Ω n Σ (EPlace p) T Σ'
  | TE_Struct : forall Σ Σ' sname lts args fields sdef,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      (fix go (Σ0 : sctx) (defs0 : list field_def) : infer_result sctx :=
         match defs0 with
         | [] => infer_ok Σ0
         | f :: rest =>
             match lookup_field_b (field_name f) fields with
             | None => infer_err (ErrMissingField (field_name f))
             | Some e_field =>
                 match infer_core_env_state_fuel 10000 env Ω n Σ0 e_field with
                 | infer_err err => infer_err err
                 | infer_ok (T_field, Σ1) =>
                     let T_expected := instantiate_struct_field_ty lts args f in
                     if ty_compatible_b Ω T_field T_expected
                     then go Σ1 rest
                     else infer_err (compatible_error T_field T_expected)
                 end
             end
         end) Σ (struct_fields sdef) = infer_ok Σ' ->
      typed_env env Ω n Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ'
  | TE_Replace_Path : forall Σ Σ1 Σ2 p e_new T_old T_new x path,
      typed_place_type_env env Σ p T_old ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env env Ω n Σ e_new T_new Σ1 ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env env Ω n Σ (EReplace p e_new) T_old Σ2
  | TE_Assign_Path : forall Σ Σ' p e_new T_old T_new x path,
      typed_place_env env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TE_Borrow_Shared_Path : forall Σ p T,
      typed_place_env env Σ p T ->
      typed_env env Ω n Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ
  | TE_Borrow_Unique_Path : forall Σ p T x path,
      typed_place_env env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ.

(* Field-list checking as used by struct literals: fields are evaluated in
   struct-definition order, while source literal order remains irrelevant. *)
Inductive typed_fields_env
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (lts : list lifetime) (args : list Ty)
    : sctx -> list (string * expr) -> list field_def -> sctx -> Prop :=
  | TFE_Checker : forall fuel Σ fields defs Σ',
      (fix go (Σ0 : sctx) (defs0 : list field_def) : infer_result sctx :=
         match defs0 with
         | [] => infer_ok Σ0
         | f :: rest =>
             match lookup_field_b (field_name f) fields with
             | None => infer_err (ErrMissingField (field_name f))
             | Some e_field =>
                 match infer_core_env_state_fuel fuel env Ω n Σ0 e_field with
                 | infer_err err => infer_err err
                 | infer_ok (T_field, Σ1) =>
                     let T_expected := instantiate_struct_field_ty lts args f in
                     if ty_compatible_b Ω T_field T_expected
                     then go Σ1 rest
                     else infer_err (compatible_error T_field T_expected)
                 end
             end
         end) Σ defs = infer_ok Σ' ->
      typed_fields_env env Ω n lts args Σ fields defs Σ'
  | TFE_Nil : forall Σ fields,
      typed_fields_env env Ω n lts args Σ fields [] Σ
  | TFE_Cons : forall Σ Σ1 Σ2 fields f rest e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env env Ω n Σ e_field T_field Σ1 ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_env env Ω n lts args Σ1 fields rest Σ2 ->
      typed_fields_env env Ω n lts args Σ fields (f :: rest) Σ2.

Inductive borrow_ok_env (env : global_env)
    : path_borrow_state -> ctx -> expr -> path_borrow_state -> Prop :=
  | BOE_Checker : forall PBS Γ e PBS',
      borrow_check_env env PBS Γ e = infer_ok PBS' ->
      borrow_ok_env env PBS Γ e PBS'
  | BOE_Struct : forall PBS PBS' Γ sname lts args fields,
      borrow_ok_fields_env env PBS Γ fields PBS' ->
      borrow_ok_env env PBS Γ (EStruct sname lts args fields) PBS'
  | BOE_Borrow_Shared_Path : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_mut x path PBS = false ->
      borrow_ok_env env PBS Γ (EBorrow RShared p) (PBShared x path :: PBS)
  | BOE_Borrow_Unique_Path : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env env PBS Γ (EBorrow RUnique p) (PBMut x path :: PBS)
  | BOE_Write_Path : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env env PBS Γ e_new PBS' ->
      borrow_ok_env env PBS Γ (EReplace p e_new) PBS'
  | BOE_Assign_Path : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env env PBS Γ e_new PBS' ->
      borrow_ok_env env PBS Γ (EAssign p e_new) PBS'
with borrow_ok_fields_env (env : global_env)
    : path_borrow_state -> ctx -> list (string * expr) -> path_borrow_state -> Prop :=
  | BOEF_Nil : forall PBS Γ,
      borrow_ok_fields_env env PBS Γ [] PBS
  | BOEF_Cons : forall PBS PBS1 PBS2 Γ name e rest,
      borrow_ok_env env PBS Γ e PBS1 ->
      borrow_ok_fields_env env PBS1 Γ rest PBS2 ->
      borrow_ok_fields_env env PBS Γ ((name, e) :: rest) PBS2.

Definition typed_fn_env (env : global_env) (f : fn_def) : Prop :=
  exists T_body Γ_out,
    typed_env env (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (params_ctx (fn_params f)))
      (fn_body f) T_body (sctx_of_ctx Γ_out) /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_b (fn_params f) Γ_out = true.

Definition checked_fn_env (env : global_env) (f : fn_def) : Prop :=
  typed_fn_env env f /\
  exists PBS',
    borrow_ok_env env [] (params_ctx (fn_params f)) (fn_body f) PBS'.

Definition trait_impl_resolved_env
    (env : global_env) (trait_name : string) (for_ty : Ty) : Prop :=
  exists i, matching_impls trait_name [] for_ty (env_impls env) = [i].

Definition struct_bounds_ok_env
    (env : global_env) (bounds : list trait_bound) (args : list Ty) : Prop :=
  check_struct_bounds env bounds args = None.

Definition trait_names_resolved_env
    (env : global_env) (traits : list string) (for_ty : Ty) : Prop :=
  Forall (fun trait_name => trait_impl_resolved_env env trait_name for_ty) traits.

Definition struct_bound_resolved_env
    (env : global_env) (args : list Ty) (b : trait_bound) : Prop :=
  exists for_ty,
    nth_error args (bound_type_index b) = Some for_ty /\
    trait_names_resolved_env env (bound_traits b) for_ty.

Definition struct_bounds_resolved_env
    (env : global_env) (bounds : list trait_bound) (args : list Ty) : Prop :=
  Forall (struct_bound_resolved_env env args) bounds.

(* ------------------------------------------------------------------ *)
(* Local soundness of executable env checker                             *)
(* ------------------------------------------------------------------ *)

Lemma infer_place_sctx_sound : forall env Σ p T,
  infer_place_sctx env Σ p = infer_ok T ->
  typed_place_env env Σ p T.
Proof.
  intros. econstructor. exact H.
Qed.

Lemma infer_place_type_sctx_sound : forall env Σ p T,
  infer_place_type_sctx env Σ p = infer_ok T ->
  typed_place_type_env env Σ p T.
Proof.
  intros. econstructor. exact H.
Qed.

Lemma infer_core_env_state_fuel_sound :
  forall fuel env Ω n Σ e T Σ',
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env env Ω n Σ e T Σ'.
Proof.
  intros. econstructor. exact H.
Qed.

Theorem infer_core_env_sound : forall env Ω n Γ e T Γ',
  infer_core_env env Ω n Γ e = infer_ok (T, Γ') ->
  typed_env env Ω n (sctx_of_ctx Γ) e T (sctx_of_ctx Γ').
Proof.
  unfold infer_core_env, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n Γ e T Γ' H.
  destruct (infer_core_env_state_fuel 10000 env Ω n Γ e)
    as [[T0 Γ0] | err] eqn:Hcore; inversion H; subst.
  eapply infer_core_env_state_fuel_sound. exact Hcore.
Qed.

Lemma trait_impl_error_none_sound : forall env trait_name for_ty,
  trait_impl_error env trait_name for_ty = None ->
  trait_impl_resolved_env env trait_name for_ty.
Proof.
  unfold trait_impl_error, trait_impl_resolved_env.
  intros env trait_name for_ty H.
  destruct (matching_impls trait_name [] for_ty (env_impls env))
    as [|i rest] eqn:Hmatches; try discriminate.
  destruct rest as [|i' rest']; try discriminate.
  exists i. reflexivity.
Qed.

Lemma check_trait_names_for_ty_sound : forall env traits for_ty,
  check_trait_names_for_ty env traits for_ty = None ->
  trait_names_resolved_env env traits for_ty.
Proof.
  unfold trait_names_resolved_env.
  induction traits as [|trait_name rest IH]; simpl; intros for_ty H.
  - constructor.
  - destruct (trait_impl_error env trait_name for_ty) eqn:Himpl; try discriminate.
    constructor.
    + apply trait_impl_error_none_sound. exact Himpl.
    + apply IH. exact H.
Qed.

Lemma check_struct_bounds_sound : forall env bounds args,
  check_struct_bounds env bounds args = None ->
  struct_bounds_resolved_env env bounds args.
Proof.
  unfold struct_bounds_resolved_env, struct_bound_resolved_env.
  induction bounds as [|b rest IH]; simpl; intros args H.
  - constructor.
  - destruct (nth_error args (bound_type_index b)) as [for_ty|] eqn:Hnth;
      try discriminate.
    destruct (check_trait_names_for_ty env (bound_traits b) for_ty) eqn:Htraits;
      try discriminate.
    constructor.
    + exists for_ty. split.
      * exact Hnth.
      * apply check_trait_names_for_ty_sound. exact Htraits.
    + apply IH. exact H.
Qed.

Lemma infer_core_env_state_struct_bounds_sound :
  forall fuel env Ω n Σ sname lts args fields T Σ' s,
    infer_core_env_state_fuel fuel env Ω n Σ
      (EStruct sname lts args fields) = infer_ok (T, Σ') ->
    lookup_struct sname env = Some s ->
    struct_bounds_ok_env env (struct_bounds s) args.
Proof.
  unfold struct_bounds_ok_env.
  intros fuel env Ω n Σ sname lts args fields T Σ' s Hinfer Hlookup.
  destruct fuel as [|fuel']; simpl in Hinfer; try discriminate.
  rewrite Hlookup in Hinfer.
  destruct (negb (Nat.eqb (Datatypes.length lts) (struct_lifetimes s)));
    try discriminate.
  destruct (negb (Nat.eqb (Datatypes.length args) (struct_type_params s)));
    try discriminate.
  destruct (check_struct_bounds env (struct_bounds s) args) eqn:Hbounds;
    try discriminate.
  reflexivity.
Qed.

Theorem infer_env_sound : forall env f T Γ',
  infer_env env f = infer_ok (T, Γ') ->
  typed_fn_env env f.
Proof.
  unfold infer_env, typed_fn_env.
  intros env f T Γ' H.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (infer_core_env env (fn_outlives f) (fn_lifetimes f)
              (params_ctx (fn_params f)) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompatible; try discriminate.
  destruct (params_ok_b (fn_params f) Γ_out) eqn:Hparams; try discriminate.
  inversion H; subst.
  exists T_body, Γ'.
  repeat split.
  - eapply infer_core_env_sound. exact Hcore.
  - exact Hcompatible.
  - exact Hparams.
Qed.

Lemma typed_fields_env_sound :
  forall fuel env Ω n lts args Σ fields defs Σ',
    (fix go (Σ0 : sctx) (defs0 : list field_def) : infer_result sctx :=
       match defs0 with
       | [] => infer_ok Σ0
       | f :: rest =>
           match lookup_field_b (field_name f) fields with
           | None => infer_err (ErrMissingField (field_name f))
           | Some e_field =>
               match infer_core_env_state_fuel fuel env Ω n Σ0 e_field with
               | infer_err err => infer_err err
               | infer_ok (T_field, Σ1) =>
                   let T_expected := instantiate_struct_field_ty lts args f in
                   if ty_compatible_b Ω T_field T_expected
                   then go Σ1 rest
                   else infer_err (compatible_error T_field T_expected)
               end
           end
       end) Σ defs = infer_ok Σ' ->
    typed_fields_env env Ω n lts args Σ fields defs Σ'.
Proof.
  intros. econstructor. exact H.
Qed.

Lemma borrow_check_env_sound : forall env PBS Γ e PBS',
  borrow_check_env env PBS Γ e = infer_ok PBS' ->
  borrow_ok_env env PBS Γ e PBS'.
Proof.
  intros. constructor. exact H.
Qed.

Theorem infer_full_env_sound : forall env f T Γ',
  infer_full_env env f = infer_ok (T, Γ') ->
  checked_fn_env env f.
Proof.
  unfold infer_full_env, checked_fn_env.
  intros env f T Γ' H.
  destruct (infer_env env f) as [[T0 Γ0] | err] eqn:Hinfer; try discriminate.
  destruct (borrow_check_env env [] (params_ctx (fn_params f)) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  split.
  - eapply infer_env_sound. exact Hinfer.
  - exists PBS'. eapply borrow_check_env_sound. exact Hborrow.
Qed.

(* ------------------------------------------------------------------ *)
(* Small path-borrow facts used by later proof slices                    *)
(* ------------------------------------------------------------------ *)

Lemma borrow_check_env_shared_field_sound : forall env PBS Γ p PBS',
  borrow_check_env env PBS Γ (EBorrow RShared p) = infer_ok PBS' ->
  PBS' = PBShared (place_root p) (place_suffix_path p) :: PBS.
Proof.
  intros env PBS Γ p PBS' H.
  simpl in H.
  destruct (pbs_has_mut (place_root p) (place_suffix_path p) PBS); [inversion H |].
  inversion H; subst. reflexivity.
Qed.

Lemma borrow_check_env_unique_field_sound : forall env PBS Γ p PBS',
  borrow_check_env env PBS Γ (EBorrow RUnique p) = infer_ok PBS' ->
  PBS' = PBMut (place_root p) (place_suffix_path p) :: PBS.
Proof.
  intros env PBS Γ p PBS' H.
  simpl in H.
  destruct (pbs_has_any (place_root p) (place_suffix_path p) PBS); [inversion H |].
  inversion H; subst. reflexivity.
Qed.
