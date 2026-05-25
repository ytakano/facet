From Stdlib.Strings Require Import String.
From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.
From Facet.TypeSystem Require Import Lifetime.

Inductive mutability :=
| MImmutable
| MMutable.

Inductive usage :=
| ULinear
| UAffine
| UUnrestricted.

Inductive ref_kind :=
| RShared      (* &T *)
| RUnique.     (* &mut T *)

Record core_trait_ref (A : Type) : Type := MkCoreTraitRef {
  core_trait_ref_name : string;
  core_trait_ref_args : list A
}.

Record core_trait_bound (A : Type) : Type := MkCoreTraitBound {
  core_bound_type_index : nat;
  core_bound_traits     : list (core_trait_ref A)
}.

Inductive TypeCore (A : Type) : Type :=
| TUnits    : TypeCore A
| TIntegers : TypeCore A
| TFloats   : TypeCore A
| TBooleans : TypeCore A
| TNamed    : string -> TypeCore A
| TParam    : nat -> TypeCore A
| TStruct   : string -> list lifetime -> list A -> TypeCore A
| TEnum     : string -> list lifetime -> list A -> TypeCore A
| TFn       : list A -> A -> TypeCore A
| TClosure  : lifetime -> list A -> A -> TypeCore A
| TForall   : nat -> outlives_ctx -> A -> TypeCore A
| TTypeForall : nat -> list (core_trait_bound A) -> A -> TypeCore A
| TRef      : lifetime -> ref_kind -> A -> TypeCore A.

Arguments TUnits {A}.
Arguments TIntegers {A}.
Arguments TFloats {A}.
Arguments TBooleans {A}.
Arguments TNamed {A} _.
Arguments TParam {A} _.
Arguments TStruct {A} _ _ _.
Arguments TEnum {A} _ _ _.
Arguments TFn {A} _ _.
Arguments TClosure {A} _ _ _.
Arguments TForall {A} _ _ _.
Arguments TTypeForall {A} _ _ _.
Arguments TRef {A} _ _ _.

Inductive Ty : Type :=
| MkTy : usage -> TypeCore Ty -> Ty.

Definition ty_usage (T : Ty) : usage :=
  match T with
  | MkTy u _ => u
  end.

Definition ty_core (T : Ty) : TypeCore Ty :=
match T with
| MkTy _ c => c
end.

Definition ref_usage_ok_b (u : usage) (rk : ref_kind) : bool :=
  match rk with
  | RShared => true
  | RUnique =>
      match u with
      | UUnrestricted => false
      | UAffine | ULinear => true
      end
  end.


(* ------------------------------------------------------------------ *)
(* Lifetime substitution on types                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint apply_lt_lifetime (σ : list lifetime) (l : lifetime) : lifetime :=
  match l with
  | LStatic => LStatic
  | LVar i  =>
      match nth_error σ i with
      | Some l' => l'
      | None    => LVar i
      end
  | LBound i => LBound i
  end.

Definition apply_lt_outlives (σ : list lifetime) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (apply_lt_lifetime σ a, apply_lt_lifetime σ b)) Ω.

Definition map_core_trait_ref
    {A B : Type} (f : A -> B) (tr : core_trait_ref A) : core_trait_ref B :=
  MkCoreTraitRef B (core_trait_ref_name A tr) (map f (core_trait_ref_args A tr)).

Definition map_core_trait_bound
    {A B : Type} (f : A -> B) (b : core_trait_bound A) : core_trait_bound B :=
  MkCoreTraitBound B (core_bound_type_index A b)
    (map (map_core_trait_ref f) (core_bound_traits A b)).

Definition close_fn_lifetime (m : nat) (l : lifetime) : lifetime :=
  match l with
  | LVar i => if Nat.ltb i m then LBound i else l
  | _ => l
  end.

Fixpoint apply_lt_ty (σ : list lifetime) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TParam i) => MkTy u (TParam i)
  | MkTy u (TStruct name lts args) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TStruct name (map (apply_lt_lifetime σ) lts) (map_lt args))
  | MkTy u (TEnum name lts args) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TEnum name (map (apply_lt_lifetime σ) lts) (map_lt args))
  | MkTy u (TFn ts r) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TFn (map_lt ts) (apply_lt_ty σ r))
  | MkTy u (TClosure l ts r) =>
      let fix map_lt (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => apply_lt_ty σ x :: map_lt xs'
        end
      in
      MkTy u (TClosure (apply_lt_lifetime σ l) (map_lt ts) (apply_lt_ty σ r))
  | MkTy u (TForall n Ω body) =>
      MkTy u (TForall n (apply_lt_outlives σ Ω) (apply_lt_ty σ body))
  | MkTy u (TTypeForall n bounds body) =>
      MkTy u (TTypeForall n
        (map (map_core_trait_bound (apply_lt_ty σ)) bounds)
        (apply_lt_ty σ body))
  | MkTy u (TRef l rk t) =>
      MkTy u (TRef (apply_lt_lifetime σ l) rk (apply_lt_ty σ t))
  end.

Fixpoint map_lifetimes_ty
    (f : lifetime -> lifetime) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TParam i) => MkTy u (TParam i)
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TStruct name (map f lts) (go args))
  | MkTy u (TEnum name lts args) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TEnum name (map f lts) (go args))
  | MkTy u (TFn ts r) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TFn (go ts) (map_lifetimes_ty f r))
  | MkTy u (TClosure l ts r) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => map_lifetimes_ty f x :: go xs'
        end
      in
      MkTy u (TClosure (f l) (go ts) (map_lifetimes_ty f r))
  | MkTy u (TForall n Ω body) =>
      MkTy u (TForall n (map (fun '(a, b) => (f a, f b)) Ω)
        (map_lifetimes_ty f body))
  | MkTy u (TTypeForall n bounds body) =>
      MkTy u (TTypeForall n bounds (map_lifetimes_ty f body))
  | MkTy u (TRef l rk t) =>
      MkTy u (TRef (f l) rk (map_lifetimes_ty f t))
  end.

Definition close_fn_ty (m : nat) (T : Ty) : Ty :=
  map_lifetimes_ty (close_fn_lifetime m) T.

Lemma close_fn_lifetime_0 :
  forall l,
    close_fn_lifetime 0 l = l.
Proof.
  intros [| i | i]; simpl; reflexivity.
Qed.

Lemma map_lifetimes_ty_close_fn_lifetime_0 :
  forall T,
    map_lifetimes_ty (close_fn_lifetime 0) T = T.
Proof.
  fix IH 1.
  intros [u core].
  destruct core as [| | | | s | i | s lts args | s lts args
                   | ts r | l ts r | n o body | n bounds body | l rk t];
    simpl; try reflexivity.
  - assert (Hlts : map (close_fn_lifetime 0) lts = lts).
    { induction lts as [| lt lts IHlts]; simpl.
      - reflexivity.
      - rewrite close_fn_lifetime_0, IHlts. reflexivity. }
    assert (Hargs :
      (fix go (xs : list Ty) : list Ty :=
         match xs with
         | [] => []
         | x :: xs' => map_lifetimes_ty (close_fn_lifetime 0) x :: go xs'
         end) args = args).
    { induction args as [| T Ts IHTs]; simpl; try reflexivity.
      rewrite IH, IHTs. reflexivity. }
    rewrite Hlts, Hargs. reflexivity.
  - assert (Hlts : map (close_fn_lifetime 0) lts = lts).
    { induction lts as [| lt lts IHlts]; simpl.
      - reflexivity.
      - rewrite close_fn_lifetime_0, IHlts. reflexivity. }
    assert (Hargs :
      (fix go (xs : list Ty) : list Ty :=
         match xs with
         | [] => []
         | x :: xs' => map_lifetimes_ty (close_fn_lifetime 0) x :: go xs'
         end) args = args).
    { induction args as [| T Ts IHTs]; simpl; try reflexivity.
      rewrite IH, IHTs. reflexivity. }
    rewrite Hlts, Hargs. reflexivity.
  - assert (Hargs :
      (fix go (xs : list Ty) : list Ty :=
         match xs with
         | [] => []
         | x :: xs' => map_lifetimes_ty (close_fn_lifetime 0) x :: go xs'
         end) ts = ts).
    { induction ts as [| T Ts IHTs]; simpl; try reflexivity.
      rewrite IH, IHTs. reflexivity. }
    rewrite Hargs, IH. reflexivity.
  - assert (Hargs :
      (fix go (xs : list Ty) : list Ty :=
         match xs with
         | [] => []
         | x :: xs' => map_lifetimes_ty (close_fn_lifetime 0) x :: go xs'
         end) ts = ts).
    { induction ts as [| T Ts IHTs]; simpl; try reflexivity.
      rewrite IH, IHTs. reflexivity. }
    rewrite close_fn_lifetime_0, Hargs, IH. reflexivity.
  - assert (Hbounds :
      map
        (fun '(a, b) =>
          (close_fn_lifetime 0 a, close_fn_lifetime 0 b)) o = o).
    { induction o as [| [a b] rest IHrest]; simpl.
      - reflexivity.
      - rewrite !close_fn_lifetime_0, IHrest. reflexivity. }
    rewrite Hbounds, IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite close_fn_lifetime_0, IH. reflexivity.
Qed.

Lemma map_lifetimes_tys_close_fn_lifetime_0 :
  forall Ts,
    (fix go (xs : list Ty) : list Ty :=
       match xs with
       | [] => []
       | x :: xs' => map_lifetimes_ty (close_fn_lifetime 0) x :: go xs'
       end) Ts = Ts.
Proof.
  induction Ts as [| T Ts IH]; simpl; try reflexivity.
  rewrite map_lifetimes_ty_close_fn_lifetime_0, IH. reflexivity.
Qed.

Definition close_fn_outlives (m : nat) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (close_fn_lifetime m a, close_fn_lifetime m b)) Ω.

Definition open_bound_lifetime (σ : list (option lifetime)) (l : lifetime) : lifetime :=
  match l with
  | LBound i =>
      match nth_error σ i with
      | Some (Some l') => l'
      | _ => LBound i
      end
  | _ => l
  end.

Definition open_bound_ty (σ : list (option lifetime)) (T : Ty) : Ty :=
  map_lifetimes_ty (open_bound_lifetime σ) T.

Definition open_bound_outlives (σ : list (option lifetime)) (Ω : outlives_ctx) : outlives_ctx :=
  map (fun '(a, b) => (open_bound_lifetime σ a, open_bound_lifetime σ b)) Ω.

Definition contains_lbound_lifetime (l : lifetime) : bool :=
  match l with
  | LBound _ => true
  | _ => false
  end.

Definition contains_lbound_outlives (Ω : outlives_ctx) : bool :=
  existsb (fun '(a, b) => contains_lbound_lifetime a || contains_lbound_lifetime b) Ω.

Fixpoint contains_lbound_ty (T : Ty) : bool :=
  match T with
  | MkTy _ (TStruct _ lts args) =>
      existsb contains_lbound_lifetime lts || existsb contains_lbound_ty args
  | MkTy _ (TEnum _ lts args) =>
      existsb contains_lbound_lifetime lts || existsb contains_lbound_ty args
  | MkTy _ (TFn ts r) =>
      existsb contains_lbound_ty ts || contains_lbound_ty r
  | MkTy _ (TClosure l ts r) =>
      contains_lbound_lifetime l || existsb contains_lbound_ty ts || contains_lbound_ty r
  | MkTy _ (TForall _ Ω body) =>
      contains_lbound_outlives Ω || contains_lbound_ty body
  | MkTy _ (TTypeForall _ bounds body) =>
      existsb
        (fun b =>
           existsb
             (fun tr => existsb contains_lbound_ty (core_trait_ref_args Ty tr))
             (core_bound_traits Ty b))
        bounds || contains_lbound_ty body
  | MkTy _ (TRef l _ t) =>
      contains_lbound_lifetime l || contains_lbound_ty t
  | _ => false
  end.

Fixpoint ty_ref_free_b (T : Ty) : bool :=
  match T with
  | MkTy _ (TStruct _ _ args) =>
      forallb ty_ref_free_b args
  | MkTy _ (TEnum _ _ args) =>
      forallb ty_ref_free_b args
  | MkTy _ (TFn ts r) =>
      forallb ty_ref_free_b ts && ty_ref_free_b r
  | MkTy _ (TClosure _ ts r) =>
      false
  | MkTy _ (TForall _ _ body) =>
      ty_ref_free_b body
  | MkTy _ (TTypeForall _ bounds body) =>
      ty_ref_free_b body
  | MkTy _ (TRef _ _ _) =>
      false
  | _ => true
  end.
