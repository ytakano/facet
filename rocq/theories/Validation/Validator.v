From Facet.TypeSystem Require Import Lifetime Types Syntax Program.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Shared list checks                                                    *)
(* ------------------------------------------------------------------ *)

Fixpoint string_mem_b (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | y :: ys => String.eqb x y || string_mem_b x ys
  end.

Fixpoint string_no_dup_b (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (string_mem_b x rest) && string_no_dup_b rest
  end.

Fixpoint nat_mem_b (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => Nat.eqb x y || nat_mem_b x ys
  end.

Fixpoint nat_no_dup_b (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (nat_mem_b x rest) && nat_no_dup_b rest
  end.

Fixpoint fn_names (fns : list fn_def) : list string :=
  match fns with
  | [] => []
  | f :: rest => fst (fn_name f) :: fn_names rest
  end.

Fixpoint struct_names (structs : list struct_def) : list string :=
  match structs with
  | [] => []
  | s :: rest => struct_name s :: struct_names rest
  end.

Fixpoint trait_names (traits : list trait_def) : list string :=
  match traits with
  | [] => []
  | t :: rest => trait_name t :: trait_names rest
  end.

Fixpoint field_names (fields : list field_def) : list string :=
  match fields with
  | [] => []
  | f :: rest => field_name f :: field_names rest
  end.

(* ------------------------------------------------------------------ *)
(* Type parameter and lifetime reference collection                      *)
(* ------------------------------------------------------------------ *)

Fixpoint used_type_params_ty (T : Ty) : list nat :=
  match T with
  | MkTy _ (TParam i) => [i]
  | MkTy _ (TStruct _ _ args) =>
      let fix go (xs : list Ty) : list nat :=
        match xs with
        | [] => []
        | x :: rest => used_type_params_ty x ++ go rest
        end
      in go args
  | MkTy _ (TFn args ret) =>
      let fix go (xs : list Ty) : list nat :=
        match xs with
        | [] => used_type_params_ty ret
        | x :: rest => used_type_params_ty x ++ go rest
        end
      in go args
  | MkTy _ (TForall _ _ body) => used_type_params_ty body
  | MkTy _ (TRef _ _ inner) => used_type_params_ty inner
  | _ => []
  end.

Fixpoint used_lifetime_vars_ty (T : Ty) : list nat :=
  match T with
  | MkTy _ (TStruct _ lts args) =>
      let lifetime_indices :=
        fold_right (fun l acc =>
          match l with
          | LVar i => i :: acc
          | _ => acc
          end) [] lts in
      let fix go (xs : list Ty) : list nat :=
        match xs with
        | [] => lifetime_indices
        | x :: rest => used_lifetime_vars_ty x ++ go rest
        end
      in go args
  | MkTy _ (TFn args ret) =>
      let fix go (xs : list Ty) : list nat :=
        match xs with
        | [] => used_lifetime_vars_ty ret
        | x :: rest => used_lifetime_vars_ty x ++ go rest
        end
      in go args
  | MkTy _ (TForall _ _ body) => used_lifetime_vars_ty body
  | MkTy _ (TRef (LVar i) _ inner) => i :: used_lifetime_vars_ty inner
  | MkTy _ (TRef _ _ inner) => used_lifetime_vars_ty inner
  | _ => []
  end.

Definition index_in_range_b (n i : nat) : bool := Nat.ltb i n.

Fixpoint all_indices_in_range_b (n : nat) (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => index_in_range_b n x && all_indices_in_range_b n rest
  end.

Fixpoint all_indices_used_b (n : nat) (used : list nat) : bool :=
  match n with
  | O => true
  | S n' => nat_mem_b n' used && all_indices_used_b n' used
  end.

Definition type_params_ok_b (n : nat) (tys : list Ty) : bool :=
  let used :=
    fold_right (fun T acc => used_type_params_ty T ++ acc) [] tys in
  all_indices_in_range_b n used && all_indices_used_b n used.

Definition lifetime_params_ok_b (n : nat) (tys : list Ty) : bool :=
  let used :=
    fold_right (fun T acc => used_lifetime_vars_ty T ++ acc) [] tys in
  all_indices_in_range_b n used && all_indices_used_b n used.

Definition struct_params_ok_b (s : struct_def) : bool :=
  let tys := map field_ty (struct_fields s) in
  type_params_ok_b (struct_type_params s) tys &&
  lifetime_params_ok_b (struct_lifetimes s) tys.

Definition trait_bounds_wf_b (traits : list trait_def) (bounds : list trait_bound) : bool :=
  forallb (fun b => forallb (fun t => string_mem_b t (trait_names traits)) (bound_traits b)) bounds.

Definition struct_wf_b (traits : list trait_def) (s : struct_def) : bool :=
  string_no_dup_b (field_names (struct_fields s)) &&
  trait_bounds_wf_b traits (struct_bounds s) &&
  struct_params_ok_b s.

Definition trait_wf_b (traits : list trait_def) (t : trait_def) : bool :=
  trait_bounds_wf_b traits (trait_bounds t).

Definition impl_key_eqb (a b : impl_def) : bool :=
  String.eqb (impl_trait_name a) (impl_trait_name b) &&
  Nat.eqb (impl_lifetimes a) (impl_lifetimes b) &&
  Nat.eqb (impl_type_params a) (impl_type_params b).

Fixpoint impl_mem_b (x : impl_def) (xs : list impl_def) : bool :=
  match xs with
  | [] => false
  | y :: ys => impl_key_eqb x y || impl_mem_b x ys
  end.

Fixpoint impl_no_dup_b (xs : list impl_def) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (impl_mem_b x rest) && impl_no_dup_b rest
  end.

Definition impl_wf_b (traits : list trait_def) (i : impl_def) : bool :=
  string_mem_b (impl_trait_name i) (trait_names traits).

Definition global_names (env : global_env) : list string :=
  struct_names (env_structs env) ++ trait_names (env_traits env) ++ fn_names (env_fns env).

Definition valid_global_env_b (env : global_env) : bool :=
  string_no_dup_b (global_names env) &&
  forallb (struct_wf_b (env_traits env)) (env_structs env) &&
  forallb (trait_wf_b (env_traits env)) (env_traits env) &&
  impl_no_dup_b (env_impls env) &&
  forallb (impl_wf_b (env_traits env)) (env_impls env).

Definition validate_env (env : global_env) : option global_env :=
  if valid_global_env_b env then Some env else None.

Definition validate_fns (fenv : list fn_def) : option global_env :=
  validate_env (empty_global_env fenv).

Definition ValidEnv (env : global_env) : Prop :=
  valid_global_env_b env = true.
