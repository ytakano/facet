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

Fixpoint type_struct_refs (T : Ty) : list string :=
  match T with
  | MkTy _ (TStruct name _ args) =>
      name ::
      fold_right (fun T acc => type_struct_refs T ++ acc) [] args
  | MkTy _ (TFn args ret) =>
      fold_right (fun T acc => type_struct_refs T ++ acc) (type_struct_refs ret) args
  | MkTy _ (TForall _ _ body) => type_struct_refs body
  | MkTy _ (TRef _ _ inner) => type_struct_refs inner
  | _ => []
  end.

Fixpoint fields_struct_refs (fields : list field_def) : list string :=
  match fields with
  | [] => []
  | f :: rest => type_struct_refs (field_ty f) ++ fields_struct_refs rest
  end.

Definition struct_deps (s : struct_def) : list string :=
  fields_struct_refs (struct_fields s).

Fixpoint lookup_struct_local (name : string) (structs : list struct_def) : option struct_def :=
  match structs with
  | [] => None
  | s :: rest =>
      if String.eqb name (struct_name s) then Some s else lookup_struct_local name rest
  end.

Fixpoint reaches_struct_b
    (structs : list struct_def) (fuel : nat) (target current : string) (seen : list string)
    : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if string_mem_b current seen then false else
      match lookup_struct_local current structs with
      | None => false
      | Some s =>
          let deps := struct_deps s in
          if string_mem_b target deps then true
          else existsb (fun dep => reaches_struct_b structs fuel' target dep (current :: seen)) deps
      end
  end.

Definition struct_acyclic_b (structs : list struct_def) (s : struct_def) : bool :=
  negb (reaches_struct_b structs (S (List.length structs)) (struct_name s) (struct_name s) []).

Definition structs_acyclic_b (structs : list struct_def) : bool :=
  forallb (struct_acyclic_b structs) structs.

(* ------------------------------------------------------------------ *)
(* Type well-formedness against the collected top-level environment      *)
(* ------------------------------------------------------------------ *)

Definition lifetime_wf_b (lt_params bound_depth : nat) (l : lifetime) : bool :=
  match l with
  | LStatic => true
  | LVar i => Nat.ltb i lt_params
  | LBound i => Nat.ltb i bound_depth
  end.

Fixpoint outlives_wf_b (lt_params bound_depth : nat) (Ω : outlives_ctx) : bool :=
  match Ω with
  | [] => true
  | (a, b) :: rest =>
      lifetime_wf_b lt_params bound_depth a &&
      lifetime_wf_b lt_params bound_depth b &&
      outlives_wf_b lt_params bound_depth rest
  end.

Fixpoint type_env_wf_b
    (structs : list struct_def) (ty_params lt_params bound_depth : nat) (T : Ty)
    {struct T} : bool :=
  match T with
  | MkTy _ TUnits | MkTy _ TIntegers | MkTy _ TFloats | MkTy _ TBooleans => true
  | MkTy _ (TNamed _) => false
  | MkTy _ (TParam i) => Nat.ltb i ty_params
  | MkTy _ (TStruct name lts args) =>
      match lookup_struct_local name structs with
      | None => false
      | Some s =>
          Nat.eqb (List.length lts) (struct_lifetimes s) &&
          Nat.eqb (List.length args) (struct_type_params s) &&
          forallb (lifetime_wf_b lt_params bound_depth) lts &&
          forallb (type_env_wf_b structs ty_params lt_params bound_depth) args
      end
  | MkTy _ (TFn args ret) =>
      forallb (type_env_wf_b structs ty_params lt_params bound_depth) args &&
      type_env_wf_b structs ty_params lt_params bound_depth ret
  | MkTy _ (TForall n Ω body) =>
      outlives_wf_b lt_params (n + bound_depth) Ω &&
      type_env_wf_b structs ty_params lt_params (n + bound_depth) body
  | MkTy _ (TRef l _ inner) =>
      lifetime_wf_b lt_params bound_depth l &&
      type_env_wf_b structs ty_params lt_params bound_depth inner
  end.

Definition field_type_wf_b (structs : list struct_def) (s : struct_def)
    (f : field_def) : bool :=
  type_env_wf_b structs (struct_type_params s) (struct_lifetimes s) 0 (field_ty f).

Definition struct_field_types_wf_b (structs : list struct_def) (s : struct_def) : bool :=
  forallb (field_type_wf_b structs s) (struct_fields s).

Definition param_type_wf_b (structs : list struct_def) (n : nat) (p : param) : bool :=
  type_env_wf_b structs 0 n 0 (param_ty p).

Definition fn_types_wf_b (structs : list struct_def) (f : fn_def) : bool :=
  forallb (param_type_wf_b structs (fn_lifetimes f)) (fn_params f) &&
  type_env_wf_b structs 0 (fn_lifetimes f) 0 (fn_ret f).

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

Definition struct_wf_b (structs : list struct_def) (traits : list trait_def) (s : struct_def) : bool :=
  string_no_dup_b (field_names (struct_fields s)) &&
  struct_field_types_wf_b structs s &&
  trait_bounds_wf_b traits (struct_bounds s) &&
  struct_params_ok_b s.

Definition trait_wf_b (traits : list trait_def) (t : trait_def) : bool :=
  trait_bounds_wf_b traits (trait_bounds t).

Definition impl_key_eqb (a b : impl_def) : bool :=
  String.eqb (impl_trait_name a) (impl_trait_name b) &&
  Nat.eqb (impl_lifetimes a) (impl_lifetimes b) &&
  Nat.eqb (impl_type_params a) (impl_type_params b) &&
  ty_eqb_decl (impl_for_ty a) (impl_for_ty b) &&
  (fix go (xs ys : list Ty) : bool :=
     match xs, ys with
     | [], [] => true
     | x :: xs', y :: ys' => ty_eqb_decl x y && go xs' ys'
     | _, _ => false
     end) (impl_trait_args a) (impl_trait_args b).

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

Definition impl_wf_b (structs : list struct_def) (traits : list trait_def) (i : impl_def) : bool :=
  string_mem_b (impl_trait_name i) (trait_names traits) &&
  forallb (type_env_wf_b structs (impl_type_params i) (impl_lifetimes i) 0)
    (impl_trait_args i) &&
  type_env_wf_b structs (impl_type_params i) (impl_lifetimes i) 0 (impl_for_ty i).

Definition global_names (env : global_env) : list string :=
  struct_names (env_structs env) ++ trait_names (env_traits env) ++ fn_names (env_fns env).

Definition valid_global_env_b (env : global_env) : bool :=
  string_no_dup_b (global_names env) &&
  structs_acyclic_b (env_structs env) &&
  forallb (struct_wf_b (env_structs env) (env_traits env)) (env_structs env) &&
  forallb (trait_wf_b (env_traits env)) (env_traits env) &&
  impl_no_dup_b (env_impls env) &&
  forallb (impl_wf_b (env_structs env) (env_traits env)) (env_impls env) &&
  forallb (fn_types_wf_b (env_structs env)) (env_fns env).

Definition validate_env (env : global_env) : option global_env :=
  if valid_global_env_b env then Some env else None.

Definition validate_fns (fenv : list fn_def) : option global_env :=
  validate_env (empty_global_env fenv).

Definition ValidEnv (env : global_env) : Prop :=
  valid_global_env_b env = true.

(* ------------------------------------------------------------------ *)
(* Smoke examples checked by Rocq compilation                            *)
(* ------------------------------------------------------------------ *)

Definition ex_trait_show : trait_def :=
  MkTraitDef "Show" 0 [].

Definition ex_struct_box : struct_def :=
  MkStructDef "Box" 0 1 [] [MkFieldDef "value" MImmutable (MkTy UUnrestricted (TParam 0))].

Definition ex_impl_show_box : impl_def :=
  MkImplDef 0 1 "Show" []
    (MkTy UUnrestricted (TStruct "Box" [] [MkTy UUnrestricted (TParam 0)])).

Definition ex_env_show_box : global_env :=
  MkGlobalEnv [ex_struct_box] [ex_trait_show] [ex_impl_show_box] [].

Example validate_env_show_box :
  validate_env ex_env_show_box = Some ex_env_show_box.
Proof. reflexivity. Qed.

Example resolve_impl_show_box_isize :
  resolve_impl ex_env_show_box "Show" []
    (MkTy UUnrestricted (TStruct "Box" [] [MkTy UUnrestricted TIntegers])) =
  Some ex_impl_show_box.
Proof. reflexivity. Qed.

Definition ex_struct_a : struct_def :=
  MkStructDef "A" 0 0 [] [MkFieldDef "b" MImmutable (MkTy UUnrestricted (TStruct "B" [] []))].

Definition ex_struct_b : struct_def :=
  MkStructDef "B" 0 0 [] [MkFieldDef "a" MImmutable (MkTy UUnrestricted (TStruct "A" [] []))].

Definition ex_env_recursive : global_env :=
  MkGlobalEnv [ex_struct_a; ex_struct_b] [] [] [].

Example validate_env_rejects_recursive_structs :
  validate_env ex_env_recursive = None.
Proof. reflexivity. Qed.
