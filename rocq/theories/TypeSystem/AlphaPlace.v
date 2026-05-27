From Facet.TypeSystem Require Import Types Syntax PathState Renaming TypingRules.
From Facet.TypeSystem Require Import AlphaCore.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Place alpha-renaming facts                                          *)
(* ------------------------------------------------------------------ *)

(* Alpha-renaming relation for places: rename_place ρ maps PVar x to
   PVar (lookup_rename x ρ) and PDeref recursively. *)
Inductive place_alpha (ρ : rename_env) : place -> place -> Prop :=
  | PA_Var : forall x,
      ~ In x (rename_range ρ) ->
      place_alpha ρ (PVar x) (PVar (lookup_rename x ρ))
  | PA_Deref : forall p pr,
      place_alpha ρ p pr ->
      place_alpha ρ (PDeref p) (PDeref pr)
  | PA_Field : forall p pr f,
      place_alpha ρ p pr ->
      place_alpha ρ (PField p f) (PField pr f).

(* place_name gives the root variable; disjointness of root ↔ place_alpha holds. *)
Lemma rename_place_alpha_sound : forall ρ p,
  ~ In (place_name p) (rename_range ρ) ->
  place_alpha ρ p (rename_place ρ p).
Proof.
  intros ρ p Hdisj. induction p; simpl in *.
  - apply PA_Var. exact Hdisj.
  - apply PA_Deref. apply IHp. exact Hdisj.
  - apply PA_Field. apply IHp. exact Hdisj.
Qed.

Lemma place_name_root : forall p,
  place_name p = place_root p.
Proof.
  induction p; simpl; auto.
Qed.

Lemma place_root_rename_place : forall ρ p,
  place_root (rename_place ρ p) = lookup_rename (place_root p) ρ.
Proof.
  induction p; simpl; auto.
Qed.

