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

Record struct_def : Type := MkStructDef {
  struct_name      : string;
  struct_lifetimes : nat;
  struct_type_params : nat;
  struct_bounds    : list trait_bound;
  struct_fields    : list field_def
}.

Record enum_variant_def : Type := MkEnumVariantDef {
  enum_variant_name   : string;
  enum_variant_fields : list Ty
}.

Record enum_def : Type := MkEnumDef {
  enum_name        : string;
  enum_lifetimes   : nat;
  enum_type_params : nat;
  enum_bounds      : list trait_bound;
  enum_variants    : list enum_variant_def
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
  env_enums   : list enum_def;
  env_traits  : list trait_def;
  env_impls   : list impl_def;
  env_local_bounds : list trait_bound;
  env_fns     : list fn_def
}.

Definition empty_global_env (fenv : list fn_def) : global_env :=
  MkGlobalEnv [] [] [] [] [] fenv.

Definition global_env_with_local_bounds
    (env : global_env) (bounds : list trait_bound) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    bounds (env_fns env).

Definition core_trait_ref_of_trait_ref (tr : trait_ref) : core_trait_ref Ty :=
  MkCoreTraitRef Ty (trait_ref_name tr) (trait_ref_args tr).

Definition core_trait_bound_of_trait_bound
    (b : trait_bound) : core_trait_bound Ty :=
  MkCoreTraitBound Ty (bound_type_index b)
    (map core_trait_ref_of_trait_ref (bound_traits b)).

Definition trait_ref_of_core_trait_ref (tr : core_trait_ref Ty) : trait_ref :=
  MkTraitRef (core_trait_ref_name Ty tr) (core_trait_ref_args Ty tr).

Definition trait_bound_of_core_trait_bound
    (b : core_trait_bound Ty) : trait_bound :=
  MkTraitBound (core_bound_type_index Ty b)
    (map trait_ref_of_core_trait_ref (core_bound_traits Ty b)).

Definition trait_bounds_of_core_trait_bounds
    (bounds : list (core_trait_bound Ty)) : list trait_bound :=
  map trait_bound_of_core_trait_bound bounds.

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

Fixpoint lookup_enum_in (name : string) (enums : list enum_def) : option enum_def :=
  match enums with
  | [] => None
  | e :: rest =>
      if String.eqb name (enum_name e)
      then Some e
      else lookup_enum_in name rest
  end.

Definition lookup_enum (name : string) (env : global_env) : option enum_def :=
  lookup_enum_in name (env_enums env).

Fixpoint lookup_enum_variant
    (name : string) (variants : list enum_variant_def)
    : option enum_variant_def :=
  match variants with
  | [] => None
  | v :: rest =>
      if String.eqb name (enum_variant_name v)
      then Some v
      else lookup_enum_variant name rest
  end.

Fixpoint lookup_field (name : string) (fields : list field_def) : option field_def :=
  match fields with
  | [] => None
  | f :: rest =>
      if String.eqb name (field_name f)
      then Some f
      else lookup_field name rest
  end.

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

Fixpoint subst_type_params_ty (σ : list Ty) (T : Ty) {struct T} : Ty :=
  match T with
  | MkTy u TUnits => MkTy u TUnits
  | MkTy u TIntegers => MkTy u TIntegers
  | MkTy u TFloats => MkTy u TFloats
  | MkTy u TBooleans => MkTy u TBooleans
  | MkTy u (TNamed s) => MkTy u (TNamed s)
  | MkTy u (TParam i) =>
      match nth_error σ i with
      | Some T' => MkTy u (ty_core T')
      | None => MkTy u (TParam i)
      end
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => subst_type_params_ty σ x :: go xs'
        end
      in
      MkTy u (TStruct name lts (go args))
  | MkTy u (TEnum name lts args) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => subst_type_params_ty σ x :: go xs'
        end
      in
      MkTy u (TEnum name lts (go args))
  | MkTy u (TFn ps r) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => subst_type_params_ty σ x :: go xs'
        end
      in
      MkTy u (TFn (go ps) (subst_type_params_ty σ r))
  | MkTy u (TClosure env ps r) =>
      let fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: xs' => subst_type_params_ty σ x :: go xs'
        end
      in
      MkTy u (TClosure env (go ps) (subst_type_params_ty σ r))
  | MkTy u (TForall n Ω body) =>
      MkTy u (TForall n Ω (subst_type_params_ty σ body))
  | MkTy u (TTypeForall n bounds body) =>
      MkTy u (TTypeForall n bounds body)
  | MkTy u (TRef l rk inner) =>
      MkTy u (TRef l rk (subst_type_params_ty σ inner))
  end.

Fixpoint subst_type_params_expr (σ : list Ty) (e : expr) {struct e} : expr :=
  match e with
  | EUnit => EUnit
  | ELit lit => ELit lit
  | EVar x => EVar x
  | ELet mut x T e1 e2 =>
      ELet mut x (subst_type_params_ty σ T)
        (subst_type_params_expr σ e1)
        (subst_type_params_expr σ e2)
  | ELetInfer mut x e1 e2 =>
      ELetInfer mut x
        (subst_type_params_expr σ e1)
        (subst_type_params_expr σ e2)
  | EFn fname => EFn fname
  | EMakeClosure fname captures => EMakeClosure fname captures
  | EPlace p => EPlace p
  | ECall fname args =>
      let fix go (es : list expr) : list expr :=
        match es with
        | [] => []
        | e' :: es' => subst_type_params_expr σ e' :: go es'
        end
      in
      ECall fname (go args)
  | ECallGeneric fname type_args args =>
      let fix go (es : list expr) : list expr :=
        match es with
        | [] => []
        | e' :: es' => subst_type_params_expr σ e' :: go es'
        end
      in
      ECallGeneric fname (map (subst_type_params_ty σ) type_args) (go args)
  | ECallExpr ef args =>
      let fix go (es : list expr) : list expr :=
        match es with
        | [] => []
        | e' :: es' => subst_type_params_expr σ e' :: go es'
        end
      in
      ECallExpr (subst_type_params_expr σ ef) (go args)
  | EStruct name lts type_args fields =>
      let fix go (fs : list (string * expr)) : list (string * expr) :=
        match fs with
        | [] => []
        | (field, e') :: fs' => (field, subst_type_params_expr σ e') :: go fs'
        end
      in
      EStruct name lts (map (subst_type_params_ty σ) type_args) (go fields)
  | EEnum name variant lts type_args args =>
      let fix go (es : list expr) : list expr :=
        match es with
        | [] => []
        | e' :: es' => subst_type_params_expr σ e' :: go es'
        end
      in
      EEnum name variant lts (map (subst_type_params_ty σ) type_args) (go args)
  | EMatch discr branches =>
      let fix go (bs : list (string * list ident * expr))
          : list (string * list ident * expr) :=
        match bs with
        | [] => []
        | (name, binders, e') :: bs' =>
            (name, binders, subst_type_params_expr σ e') :: go bs'
        end
      in
      EMatch (subst_type_params_expr σ discr) (go branches)
  | EReplace p rhs =>
      EReplace p (subst_type_params_expr σ rhs)
  | EAssign p rhs =>
      EAssign p (subst_type_params_expr σ rhs)
  | EBorrow rk p => EBorrow rk p
  | EDeref e' => EDeref (subst_type_params_expr σ e')
  | EDrop e' => EDrop (subst_type_params_expr σ e')
  | EIf e1 e2 e3 =>
      EIf (subst_type_params_expr σ e1)
        (subst_type_params_expr σ e2)
        (subst_type_params_expr σ e3)
  end.

Definition subst_type_params_param (σ : list Ty) (p : param) : param :=
  MkParam (param_mutability p) (param_name p)
    (subst_type_params_ty σ (param_ty p)).

Lemma subst_type_params_ty_outer_usage_core : forall σ u T,
  subst_type_params_ty σ (MkTy u (ty_core T)) =
  MkTy u (ty_core (subst_type_params_ty σ T)).
Proof.
  intros σ u [u' c]. destruct c; simpl; try reflexivity.
  destruct (nth_error σ n) as [[u'' c''] |]; reflexivity.
Qed.

Fixpoint compose_type_params_go
    (σ τ fallback : list Ty) {struct τ} : list Ty :=
  match τ, fallback with
  | [], fb => fb
  | T :: τ', [] =>
      subst_type_params_ty σ T :: compose_type_params_go σ τ' []
  | T :: τ', _ :: fb' =>
      subst_type_params_ty σ T :: compose_type_params_go σ τ' fb'
  end.

Definition compose_type_params (σ τ : list Ty) : list Ty :=
  compose_type_params_go σ τ σ.

Lemma nth_error_compose_type_params_go : forall σ τ fallback i,
  nth_error (compose_type_params_go σ τ fallback) i =
  match nth_error τ i with
  | Some T => Some (subst_type_params_ty σ T)
  | None => nth_error fallback i
  end.
Proof.
  intros σ τ. induction τ as [| T τ IH]; intros fallback [| i];
    destruct fallback as [| F fallback']; simpl; try reflexivity.
  - specialize (IH [] i).
    destruct (nth_error τ i) eqn:Hτi.
    + exact IH.
    + destruct i; simpl in IH; exact IH.
  - exact (IH fallback' i).
Qed.

Lemma nth_error_compose_type_params : forall σ τ i,
  nth_error (compose_type_params σ τ) i =
  match nth_error τ i with
  | Some T => Some (subst_type_params_ty σ T)
  | None => nth_error σ i
  end.
Proof.
  intros σ τ i. unfold compose_type_params.
  apply nth_error_compose_type_params_go.
Qed.

Lemma subst_type_params_ty_compose : forall σ τ T,
  subst_type_params_ty σ (subst_type_params_ty τ T) =
  subst_type_params_ty (compose_type_params σ τ) T.
Proof.
  intros σ τ. fix IH 1. intros [u c]. destruct c; simpl; try reflexivity.
  - rewrite nth_error_compose_type_params.
    destruct (nth_error τ n) as [T' |] eqn:Hτ.
    + simpl. exact (subst_type_params_ty_outer_usage_core σ u T').
    + destruct (nth_error σ n) as [[u' c'] |] eqn:Hσ.
      * simpl. rewrite Hσ. reflexivity.
      * simpl. rewrite Hσ. reflexivity.
  - induction l0 as [| T0 Ts IHTs].
    + reflexivity.
    + simpl in *. rewrite (IH T0). injection IHTs as Htail.
      rewrite Htail. reflexivity.
  - induction l0 as [| T0 Ts IHTs].
    + reflexivity.
    + simpl in *. rewrite (IH T0). injection IHTs as Htail.
      rewrite Htail. reflexivity.
  - induction l as [| T0 Ts IHTs].
    + simpl. rewrite (IH t). reflexivity.
    + simpl in *. rewrite (IH T0). injection IHTs as Hparams Hret.
      rewrite Hparams, Hret. reflexivity.
  - induction l0 as [| T0 Ts IHTs].
    + simpl. rewrite (IH t). reflexivity.
    + simpl in *. rewrite (IH T0). injection IHTs as Hparams Hret.
      rewrite Hparams, Hret. reflexivity.
  - simpl. rewrite (IH t). reflexivity.
  - simpl. rewrite (IH t). reflexivity.
Qed.

Definition instantiate_struct_field_ty
    (lifetime_args : list lifetime) (type_args : list Ty) (f : field_def) : Ty :=
  subst_type_params_ty type_args (apply_lt_ty lifetime_args (field_ty f)).

Definition instantiate_struct_ty
    (s : struct_def) (lifetime_args : list lifetime) (type_args : list Ty) : Ty :=
  MkTy (usage_max_list (struct_fields s))
       (TStruct (struct_name s) lifetime_args type_args).

Definition instantiate_enum_variant_field_ty
    (lifetime_args : list lifetime) (type_args : list Ty)
    (T : Ty) : Ty :=
  subst_type_params_ty type_args (apply_lt_ty lifetime_args T).

Lemma instantiate_struct_field_ty_type_subst_compose : forall σ lts args f,
  subst_type_params_ty σ (instantiate_struct_field_ty lts args f) =
  instantiate_struct_field_ty lts (compose_type_params σ args) f.
Proof.
  intros σ lts args f. unfold instantiate_struct_field_ty.
  apply subst_type_params_ty_compose.
Qed.

Lemma instantiate_enum_variant_field_ty_type_subst_compose : forall σ lts args T,
  subst_type_params_ty σ (instantiate_enum_variant_field_ty lts args T) =
  instantiate_enum_variant_field_ty lts (compose_type_params σ args) T.
Proof.
  intros σ lts args T. unfold instantiate_enum_variant_field_ty.
  apply subst_type_params_ty_compose.
Qed.

Fixpoint usage_max_ty_list (tys : list Ty) : usage :=
  match tys with
  | [] => UUnrestricted
  | T :: rest => usage_max_decl (ty_usage T) (usage_max_ty_list rest)
  end.

Fixpoint usage_max_enum_variants (variants : list enum_variant_def) : usage :=
  match variants with
  | [] => UUnrestricted
  | v :: rest =>
      usage_max_decl (usage_max_ty_list (enum_variant_fields v))
        (usage_max_enum_variants rest)
  end.

Definition instantiate_enum_ty
    (e : enum_def) (lifetime_args : list lifetime) (type_args : list Ty) : Ty :=
  MkTy (usage_max_enum_variants (enum_variants e))
       (TEnum (enum_name e) lifetime_args type_args).

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
      | TEnum n1 lts1 args1, TEnum n2 lts2 args2 =>
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
      | TClosure env1 ps1 r1, TClosure env2 ps2 r2 =>
          lifetime_eqb env1 env2 &&
          (fix go (xs ys : list Ty) : bool :=
             match xs, ys with
             | [], [] => true
             | x :: xs', y :: ys' => ty_eqb_decl x y && go xs' ys'
             | _, _ => false
             end) ps1 ps2 && ty_eqb_decl r1 r2
      | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
          Nat.eqb n1 n2 && outlives_ctx_eqb_decl Ω1 Ω2 && ty_eqb_decl b1 b2
      | TTypeForall n1 bs1 b1, TTypeForall n2 bs2 b2 =>
          Nat.eqb n1 n2 &&
          (fix go_bounds (xs ys : list (core_trait_bound Ty)) : bool :=
             match xs, ys with
             | [], [] => true
             | x :: xs', y :: ys' =>
                 Nat.eqb (core_bound_type_index Ty x) (core_bound_type_index Ty y) &&
                 (fix go_refs (rs ss : list (core_trait_ref Ty)) : bool :=
                    match rs, ss with
                    | [], [] => true
                    | r :: rs', s :: ss' =>
                        String.eqb (core_trait_ref_name Ty r) (core_trait_ref_name Ty s) &&
                        (fix go_args (as_ bs : list Ty) : bool :=
                           match as_, bs with
                           | [], [] => true
                           | a :: as', b :: bs' => ty_eqb_decl a b && go_args as' bs'
                           | _, _ => false
                           end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                        go_refs rs' ss'
                    | _, _ => false
                    end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
                 go_bounds xs' ys'
             | _, _ => false
             end) bs1 bs2 &&
          ty_eqb_decl b1 b2
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
          | TEnum n1 lts1 args1, TEnum n2 lts2 args2 =>
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
          | TTypeForall n1 bs1 b1, TTypeForall n2 bs2 b2 =>
              if Nat.eqb n1 n2 && ty_eqb_decl
                   (MkTy UUnrestricted (TTypeForall n1 bs1 b1))
                   (MkTy UUnrestricted (TTypeForall n2 bs2 b2))
              then Some st
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
  | MkTy _ (TEnum _ lts args) =>
      S (List.length lts + fold_right (fun T acc => ty_match_fuel T + acc) 0 args)
  | MkTy _ (TFn ps r) =>
      S (ty_match_fuel r + fold_right (fun T acc => ty_match_fuel T + acc) 0 ps)
  | MkTy _ (TForall _ Ω body) => S (List.length Ω + ty_match_fuel body)
  | MkTy _ (TTypeForall _ bounds body) =>
      S (List.length bounds + ty_match_fuel body)
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
