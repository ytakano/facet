From Facet.TypeSystem Require Import Lifetime Types Syntax.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Top-level declarations for struct/trait planning                      *)
(* ------------------------------------------------------------------ *)

Record field_def : Type := MkFieldDef {
  field_name       : string;
  field_mutability : mutability;
  field_ty         : Ty
}.

Record trait_bound : Type := MkTraitBound {
  bound_type_index : nat;
  bound_traits     : list string
}.

Record struct_def : Type := MkStructDef {
  struct_name      : string;
  struct_lifetimes : nat;
  struct_type_params : nat;
  struct_bounds    : list trait_bound;
  struct_fields    : list field_def
}.

Record trait_def : Type := MkTraitDef {
  trait_name        : string;
  trait_type_params : nat;
  trait_bounds      : list trait_bound
}.

Record impl_def : Type := MkImplDef {
  impl_lifetimes    : nat;
  impl_type_params  : nat;
  impl_trait_name   : string;
  impl_trait_args   : list Ty;
  impl_for_ty       : Ty
}.

Record global_env : Type := MkGlobalEnv {
  env_structs : list struct_def;
  env_traits  : list trait_def;
  env_impls   : list impl_def;
  env_fns     : list fn_def
}.

Definition empty_global_env (fenv : list fn_def) : global_env :=
  MkGlobalEnv [] [] [] fenv.

Fixpoint lookup_struct_in (name : string) (structs : list struct_def) : option struct_def :=
  match structs with
  | [] => None
  | s :: rest =>
      if String.eqb name (struct_name s)
      then Some s
      else lookup_struct_in name rest
  end.

Definition lookup_struct (name : string) (env : global_env) : option struct_def :=
  lookup_struct_in name (env_structs env).

Fixpoint lookup_trait_in (name : string) (traits : list trait_def) : option trait_def :=
  match traits with
  | [] => None
  | t :: rest =>
      if String.eqb name (trait_name t)
      then Some t
      else lookup_trait_in name rest
  end.

Definition lookup_trait (name : string) (env : global_env) : option trait_def :=
  lookup_trait_in name (env_traits env).

Fixpoint lookup_impls_for_trait (name : string) (impls : list impl_def) : list impl_def :=
  match impls with
  | [] => []
  | i :: rest =>
      let rest' := lookup_impls_for_trait name rest in
      if String.eqb name (impl_trait_name i) then i :: rest' else rest'
  end.

Definition usage_max_decl (u1 u2 : usage) : usage :=
  match u1, u2 with
  | ULinear, _ | _, ULinear => ULinear
  | UAffine, _ | _, UAffine => UAffine
  | UUnrestricted, UUnrestricted => UUnrestricted
  end.

Fixpoint usage_max_list (fields : list field_def) : usage :=
  match fields with
  | [] => UUnrestricted
  | f :: rest => usage_max_decl (ty_usage (field_ty f)) (usage_max_list rest)
  end.

(* ------------------------------------------------------------------ *)
(* Decidable matching helpers for generic impl lookup                    *)
(* ------------------------------------------------------------------ *)

Definition usage_eqb_decl (u1 u2 : usage) : bool :=
  match u1, u2 with
  | ULinear, ULinear => true
  | UAffine, UAffine => true
  | UUnrestricted, UUnrestricted => true
  | _, _ => false
  end.

Definition ref_kind_eqb_decl (k1 k2 : ref_kind) : bool :=
  match k1, k2 with
  | RShared, RShared => true
  | RUnique, RUnique => true
  | _, _ => false
  end.

Fixpoint lifetime_list_eqb_decl (l1 l2 : list lifetime) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => lifetime_eqb x y && lifetime_list_eqb_decl xs ys
  | _, _ => false
  end.

Fixpoint outlives_ctx_eqb_decl (Ω1 Ω2 : outlives_ctx) : bool :=
  match Ω1, Ω2 with
  | [], [] => true
  | (a1, b1) :: xs, (a2, b2) :: ys =>
      lifetime_eqb a1 a2 && lifetime_eqb b1 b2 && outlives_ctx_eqb_decl xs ys
  | _, _ => false
  end.

Fixpoint ty_eqb_decl (T1 T2 : Ty) {struct T1} : bool :=
  match T1, T2 with
  | MkTy u1 c1, MkTy u2 c2 =>
      usage_eqb_decl u1 u2 &&
      match c1, c2 with
      | TUnits, TUnits => true
      | TIntegers, TIntegers => true
      | TFloats, TFloats => true
      | TBooleans, TBooleans => true
      | TNamed s1, TNamed s2 => String.eqb s1 s2
      | TParam i1, TParam i2 => Nat.eqb i1 i2
      | TStruct n1 lts1 args1, TStruct n2 lts2 args2 =>
          String.eqb n1 n2 && lifetime_list_eqb_decl lts1 lts2 &&
          (fix go (xs ys : list Ty) : bool :=
             match xs, ys with
             | [], [] => true
             | x :: xs', y :: ys' => ty_eqb_decl x y && go xs' ys'
             | _, _ => false
             end) args1 args2
      | TFn ps1 r1, TFn ps2 r2 =>
          (fix go (xs ys : list Ty) : bool :=
             match xs, ys with
             | [], [] => true
             | x :: xs', y :: ys' => ty_eqb_decl x y && go xs' ys'
             | _, _ => false
             end) ps1 ps2 && ty_eqb_decl r1 r2
      | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
          Nat.eqb n1 n2 && outlives_ctx_eqb_decl Ω1 Ω2 && ty_eqb_decl b1 b2
      | TRef l1 rk1 t1, TRef l2 rk2 t2 =>
          lifetime_eqb l1 l2 && ref_kind_eqb_decl rk1 rk2 && ty_eqb_decl t1 t2
      | _, _ => false
      end
  end.

Definition type_subst := list (option Ty).
Definition lifetime_subst := list (option lifetime).

Fixpoint repeat_none {A : Type} (n : nat) : list (option A) :=
  match n with
  | O => []
  | S n' => None :: repeat_none n'
  end.

Fixpoint list_set_nth {A : Type} (i : nat) (v : A) (xs : list A) : list A :=
  match i, xs with
  | O, _ :: rest => v :: rest
  | O, [] => []
  | S i', x :: rest => x :: list_set_nth i' v rest
  | S _, [] => []
  end.

Definition bind_type_param (i : nat) (T : Ty) (σ : type_subst) : option type_subst :=
  match nth_error σ i with
  | None => None
  | Some None => Some (list_set_nth i (Some T) σ)
  | Some (Some T') => if ty_eqb_decl T T' then Some σ else None
  end.

Definition bind_lifetime_param
    (i : nat) (l : lifetime) (σ : lifetime_subst) : option lifetime_subst :=
  match nth_error σ i with
  | None => None
  | Some None => Some (list_set_nth i (Some l) σ)
  | Some (Some l') => if lifetime_eqb l l' then Some σ else None
  end.

Definition impl_match_state := (type_subst * lifetime_subst)%type.

Definition match_lifetime
    (lt_params : nat) (pattern actual : lifetime) (st : impl_match_state)
    : option impl_match_state :=
  let '(tyσ, ltσ) := st in
  match pattern with
  | LVar i =>
      if Nat.ltb i lt_params
      then match bind_lifetime_param i actual ltσ with
           | Some ltσ' => Some (tyσ, ltσ')
           | None => None
           end
      else if lifetime_eqb pattern actual then Some st else None
  | _ => if lifetime_eqb pattern actual then Some st else None
  end.

Fixpoint match_lifetimes
    (lt_params : nat) (patterns actuals : list lifetime) (st : impl_match_state)
    : option impl_match_state :=
  match patterns, actuals with
  | [], [] => Some st
  | p :: ps, a :: as_ =>
      match match_lifetime lt_params p a st with
      | Some st' => match_lifetimes lt_params ps as_ st'
      | None => None
      end
  | _, _ => None
  end.

Fixpoint match_ty
    (ty_params lt_params fuel : nat) (pattern actual : Ty) (st : impl_match_state)
    : option impl_match_state :=
  match fuel with
  | O => None
  | S fuel' =>
      match pattern, actual with
      | MkTy u_p (TParam i), _ =>
          if Nat.ltb i ty_params
          then if usage_eqb_decl u_p (ty_usage actual)
               then let '(tyσ, ltσ) := st in
                    match bind_type_param i actual tyσ with
                    | Some tyσ' => Some (tyσ', ltσ)
                    | None => None
                    end
               else None
          else if ty_eqb_decl pattern actual then Some st else None
      | MkTy u_p c_p, MkTy u_a c_a =>
          if negb (usage_eqb_decl u_p u_a) then None else
          match c_p, c_a with
          | TUnits, TUnits => Some st
          | TIntegers, TIntegers => Some st
          | TFloats, TFloats => Some st
          | TBooleans, TBooleans => Some st
          | TNamed s1, TNamed s2 => if String.eqb s1 s2 then Some st else None
          | TStruct n1 lts1 args1, TStruct n2 lts2 args2 =>
              if String.eqb n1 n2
              then match match_lifetimes lt_params lts1 lts2 st with
                   | Some st' => match_tys ty_params lt_params fuel' args1 args2 st'
                   | None => None
                   end
              else None
          | TFn ps1 r1, TFn ps2 r2 =>
              match match_tys ty_params lt_params fuel' ps1 ps2 st with
              | Some st' => match_ty ty_params lt_params fuel' r1 r2 st'
              | None => None
              end
          | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
              if Nat.eqb n1 n2 && outlives_ctx_eqb_decl Ω1 Ω2
              then match_ty ty_params lt_params fuel' b1 b2 st
              else None
          | TRef l1 rk1 t1, TRef l2 rk2 t2 =>
              if ref_kind_eqb_decl rk1 rk2
              then match match_lifetime lt_params l1 l2 st with
                   | Some st' => match_ty ty_params lt_params fuel' t1 t2 st'
                   | None => None
                   end
              else None
          | _, _ => None
          end
      end
  end
with match_tys
    (ty_params lt_params fuel : nat)
    (patterns actuals : list Ty) (st : impl_match_state)
    : option impl_match_state :=
  match fuel with
  | O => None
  | S fuel' =>
      match patterns, actuals with
      | [], [] => Some st
      | p :: ps, a :: as_ =>
          match match_ty ty_params lt_params fuel' p a st with
          | Some st' => match_tys ty_params lt_params fuel' ps as_ st'
          | None => None
          end
      | _, _ => None
      end
  end.

Fixpoint ty_match_fuel (T : Ty) : nat :=
  match T with
  | MkTy _ (TStruct _ lts args) =>
      S (List.length lts + fold_right (fun T acc => ty_match_fuel T + acc) 0 args)
  | MkTy _ (TFn ps r) =>
      S (ty_match_fuel r + fold_right (fun T acc => ty_match_fuel T + acc) 0 ps)
  | MkTy _ (TForall _ Ω body) => S (List.length Ω + ty_match_fuel body)
  | MkTy _ (TRef _ _ inner) => S (ty_match_fuel inner)
  | _ => 1
  end.

Definition impl_matches_b
    (trait_name : string) (trait_args : list Ty) (for_ty : Ty) (i : impl_def)
    : bool :=
  if negb (String.eqb trait_name (impl_trait_name i)) then false else
  let st0 := (repeat_none (impl_type_params i), repeat_none (impl_lifetimes i)) in
  let fuel :=
    S (ty_match_fuel for_ty +
       ty_match_fuel (impl_for_ty i) +
       fold_right (fun T acc => ty_match_fuel T + acc) 0 trait_args +
       fold_right (fun T acc => ty_match_fuel T + acc) 0 (impl_trait_args i)) in
  match match_tys (impl_type_params i) (impl_lifetimes i) fuel
          (impl_trait_args i) trait_args st0 with
  | None => false
  | Some st1 =>
      match match_ty (impl_type_params i) (impl_lifetimes i) fuel
              (impl_for_ty i) for_ty st1 with
      | Some _ => true
      | None => false
      end
  end.

Fixpoint matching_impls
    (trait_name : string) (trait_args : list Ty) (for_ty : Ty) (impls : list impl_def)
    : list impl_def :=
  match impls with
  | [] => []
  | i :: rest =>
      let rest' := matching_impls trait_name trait_args for_ty rest in
      if impl_matches_b trait_name trait_args for_ty i then i :: rest' else rest'
  end.

Definition resolve_impl
    (env : global_env) (trait_name : string) (trait_args : list Ty) (for_ty : Ty)
    : option impl_def :=
  match matching_impls trait_name trait_args for_ty (env_impls env) with
  | [i] => Some i
  | _ => None
  end.
