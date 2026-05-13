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
      typed_env env Ω n Σ e T Σ'.

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
      typed_fields_env env Ω n lts args Σ fields defs Σ'.

Inductive borrow_ok_env (env : global_env)
    : path_borrow_state -> ctx -> expr -> path_borrow_state -> Prop :=
  | BOE_Checker : forall PBS Γ e PBS',
      borrow_check_env env PBS Γ e = infer_ok PBS' ->
      borrow_ok_env env PBS Γ e PBS'.

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
