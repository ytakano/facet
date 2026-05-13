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
