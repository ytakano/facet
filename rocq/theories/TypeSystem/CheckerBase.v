From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Decidable equality helpers                                            *)
(* ------------------------------------------------------------------ *)

Definition usage_eqb (u1 u2 : usage) : bool :=
  match u1, u2 with
  | ULinear,       ULinear       => true
  | UAffine,       UAffine       => true
  | UUnrestricted, UUnrestricted => true
  | _,             _             => false
  end.

(* usage_sub_bool u1 u2 = true iff u1 <: u2 (unrestricted <: affine <: linear) *)
Definition usage_sub_bool (u1 u2 : usage) : bool :=
  match u1, u2 with
  | UUnrestricted, _          => true
  | UAffine,       UAffine    => true
  | UAffine,       ULinear    => true
  | ULinear,       ULinear    => true
  | _,             _          => false
  end.

Definition ref_kind_eqb (k1 k2 : ref_kind) : bool :=
  match k1, k2 with
  | RShared, RShared => true
  | RUnique, RUnique => true
  | _, _ => false
  end.

Definition lifetime_pair_eqb (p1 p2 : lifetime * lifetime) : bool :=
  lifetime_eqb (fst p1) (fst p2) && lifetime_eqb (snd p1) (snd p2).

Fixpoint outlives_ctx_eqb (Ω1 Ω2 : outlives_ctx) : bool :=
  match Ω1, Ω2 with
  | [], [] => true
  | p1 :: Ω1', p2 :: Ω2' => lifetime_pair_eqb p1 p2 && outlives_ctx_eqb Ω1' Ω2'
  | _, _ => false
  end.

Fixpoint lifetime_list_eqb (l1 l2 : list lifetime) : bool :=
  match l1, l2 with
  | [], [] => true
  | lt1 :: l1', lt2 :: l2' => lifetime_eqb lt1 lt2 && lifetime_list_eqb l1' l2'
  | _, _ => false
  end.

Fixpoint ty_eqb (T1 T2 : Ty) {struct T1} : bool :=
  match T1, T2 with
  | MkTy u1 c1, MkTy u2 c2 =>
      usage_eqb u1 u2 &&
      match c1, c2 with
      | TUnits,    TUnits    => true
      | TIntegers, TIntegers => true
      | TFloats,   TFloats   => true
      | TBooleans, TBooleans => true
      | TNamed s1, TNamed s2 => String.eqb s1 s2
      | TParam i1, TParam i2 => Nat.eqb i1 i2
      | TStruct name1 lts1 args1, TStruct name2 lts2 args2 =>
          String.eqb name1 name2 &&
          lifetime_list_eqb lts1 lts2 &&
          (fix go_args (l1 l2 : list Ty) : bool :=
             match l1, l2 with
             | [], [] => true
             | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go_args l1' l2'
             | _, _ => false
             end) args1 args2
      | TEnum name1 lts1 args1, TEnum name2 lts2 args2 =>
          String.eqb name1 name2 &&
          lifetime_list_eqb lts1 lts2 &&
          (fix go_args (l1 l2 : list Ty) : bool :=
             match l1, l2 with
             | [], [] => true
             | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go_args l1' l2'
             | _, _ => false
             end) args1 args2
      | TFn ts1 r1, TFn ts2 r2 =>
          (fix go (l1 l2 : list Ty) : bool :=
             match l1, l2 with
             | [], [] => true
             | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
             | _, _ => false
             end) ts1 ts2 && ty_eqb r1 r2
      | TClosure env1 ts1 r1, TClosure env2 ts2 r2 =>
          lifetime_eqb env1 env2 &&
          (fix go (l1 l2 : list Ty) : bool :=
             match l1, l2 with
             | [], [] => true
             | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
             | _, _ => false
             end) ts1 ts2 && ty_eqb r1 r2
      | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
          Nat.eqb n1 n2 && outlives_ctx_eqb Ω1 Ω2 && ty_eqb b1 b2
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
                           | a :: as', b :: bs' => ty_eqb a b && go_args as' bs'
                           | _, _ => false
                           end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                        go_refs rs' ss'
                    | _, _ => false
                    end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
                 go_bounds xs' ys'
             | _, _ => false
             end) bs1 bs2 &&
          ty_eqb b1 b2
      | TRef l1 k1 t1, TRef l2 k2 t2 =>
          lifetime_eqb l1 l2 && ref_kind_eqb k1 k2 && ty_eqb t1 t2
      | _, _ => false
      end
  end.

Definition ty_core_eqb (c1 c2 : TypeCore Ty) : bool :=
  match c1, c2 with
  | TUnits,    TUnits    => true
  | TIntegers, TIntegers => true
  | TFloats,   TFloats   => true
  | TBooleans, TBooleans => true
  | TNamed s1, TNamed s2 => String.eqb s1 s2
  | TParam i1, TParam i2 => Nat.eqb i1 i2
  | TStruct name1 lts1 args1, TStruct name2 lts2 args2 =>
      String.eqb name1 name2 &&
      lifetime_list_eqb lts1 lts2 &&
      (fix go_args (l1 l2 : list Ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go_args l1' l2'
         | _, _ => false
         end) args1 args2
  | TEnum name1 lts1 args1, TEnum name2 lts2 args2 =>
      String.eqb name1 name2 &&
      lifetime_list_eqb lts1 lts2 &&
      (fix go_args (l1 l2 : list Ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go_args l1' l2'
         | _, _ => false
         end) args1 args2
  | TFn ts1 r1, TFn ts2 r2 =>
      (fix go (l1 l2 : list Ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
         | _, _ => false
         end) ts1 ts2 && ty_eqb r1 r2
  | TClosure env1 ts1 r1, TClosure env2 ts2 r2 =>
      lifetime_eqb env1 env2 &&
      (fix go (l1 l2 : list Ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
         | _, _ => false
         end) ts1 ts2 && ty_eqb r1 r2
  | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
      Nat.eqb n1 n2 && outlives_ctx_eqb Ω1 Ω2 && ty_eqb b1 b2
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
                       | a :: as', b :: bs' => ty_eqb a b && go_args as' bs'
                       | _, _ => false
                       end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                    go_refs rs' ss'
                | _, _ => false
                end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
             go_bounds xs' ys'
         | _, _ => false
         end) bs1 bs2 &&
      ty_eqb b1 b2
  | TRef l1 k1 t1, TRef l2 k2 t2 =>
      lifetime_eqb l1 l2 && ref_kind_eqb k1 k2 && ty_eqb t1 t2
  | _, _ => false
  end.

Fixpoint ty_depth (T : Ty) : nat :=
  match T with
  | MkTy _ c =>
      match c with
      | TFn ts r =>
          S ((fix go (l : list Ty) : nat :=
               match l with
               | [] => ty_depth r
               | t :: l' => S (ty_depth t) + go l'
               end) ts)
      | TClosure _ ts r =>
          S ((fix go (l : list Ty) : nat :=
               match l with
               | [] => ty_depth r
               | t :: l' => S (ty_depth t) + go l'
               end) ts)
      | TStruct _ lts args =>
          S (List.length lts +
             (fix go (l : list Ty) : nat :=
                match l with
                | [] => 0
                | t :: l' => S (ty_depth t) + go l'
                end) args)
      | TEnum _ lts args =>
          S (List.length lts +
             (fix go (l : list Ty) : nat :=
                match l with
                | [] => 0
                | t :: l' => S (ty_depth t) + go l'
                end) args)
      | TRef _ _ t => S (ty_depth t)
      | TForall _ Ω body => S (List.length Ω + ty_depth body)
      | TTypeForall _ bounds body =>
          S (ty_depth body +
             (fix go_bounds (bs : list (core_trait_bound Ty)) : nat :=
                match bs with
                | [] => 0
                | b :: bs' =>
                    (fix go_refs (rs : list (core_trait_ref Ty)) : nat :=
                       match rs with
                       | [] => 0
                       | tr :: rs' =>
                           (fix go_args (args : list Ty) : nat :=
                              match args with
                              | [] => 0
                              | arg :: args' => S (ty_depth arg) + go_args args'
                              end) (core_trait_ref_args Ty tr) +
                           go_refs rs'
                       end) (core_bound_traits Ty b) +
                    go_bounds bs'
                end) bounds)
      | _ => 1
      end
  end.

Fixpoint ty_compatible_args_contra_b_fuel
    (compat : outlives_ctx -> Ty -> Ty -> bool)
    (Ω : outlives_ctx)
    (actual expected : list Ty) : bool :=
  match actual, expected with
  | [], [] => true
  | a :: actual', e :: expected' =>
      compat Ω e a &&
      ty_compatible_args_contra_b_fuel compat Ω actual' expected'
  | _, _ => false
  end.

Fixpoint ty_compatible_b_fuel (fuel : nat) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      usage_sub_bool (ty_usage T_actual) (ty_usage T_expected) &&
      match ty_core T_actual, ty_core T_expected with
      | TRef la rka Ta, TRef lb rkb Tb =>
          outlives_b Ω la lb && ref_kind_eqb rka rkb &&
          match rka with
          | RShared => ty_compatible_b_fuel fuel' Ω Ta Tb
          | RUnique => ty_eqb Ta Tb
          end
      | TFn params_a ret_a, TFn params_e ret_e =>
          ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel') Ω params_a params_e &&
          ty_compatible_b_fuel fuel' Ω ret_a ret_e
      | TClosure env_a params_a ret_a, TClosure env_e params_e ret_e =>
          outlives_b Ω env_a env_e &&
          ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel') Ω params_a params_e &&
          ty_compatible_b_fuel fuel' Ω ret_a ret_e
      | TFn params_a ret_a, TClosure _ params_e ret_e =>
          ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel') Ω params_a params_e &&
          ty_compatible_b_fuel fuel' Ω ret_a ret_e
      | TForall na Ωa Ta, TForall nb Ωb Tb =>
          Nat.eqb na nb && outlives_ctx_eqb Ωa Ωb &&
          ty_compatible_b_fuel fuel' Ω Ta Tb
      | TTypeForall na ba Ta, TTypeForall nb bb Tb =>
          Nat.eqb na nb &&
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
                           | a :: as', b :: bs' => ty_eqb a b && go_args as' bs'
                           | _, _ => false
                           end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                        go_refs rs' ss'
                    | _, _ => false
                    end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
                 go_bounds xs' ys'
             | _, _ => false
             end) ba bb &&
          ty_compatible_b_fuel fuel' Ω Ta Tb
      | _, TForall _ [] Tb =>
          negb (contains_lbound_ty Tb) &&
          ty_compatible_b_fuel fuel' Ω T_actual Tb
      | ca, cb => ty_core_eqb ca cb
      end
  end.

Definition ty_compatible_b (Ω : outlives_ctx) (T_actual T_expected : Ty) : bool :=
  ty_compatible_b_fuel (ty_depth T_actual + ty_depth T_expected) Ω T_actual T_expected.

Inductive capture_ref_free_ty (env : global_env) : Ty -> Prop :=
  | CRFT_Unit : forall u,
      capture_ref_free_ty env (MkTy u TUnits)
  | CRFT_Int : forall u,
      capture_ref_free_ty env (MkTy u TIntegers)
  | CRFT_Float : forall u,
      capture_ref_free_ty env (MkTy u TFloats)
  | CRFT_Bool : forall u,
      capture_ref_free_ty env (MkTy u TBooleans)
  | CRFT_Struct : forall u name lts args sdef,
      lookup_struct name env = Some sdef ->
      Forall (capture_ref_free_ty env) args ->
      Forall
        (fun f =>
           capture_ref_free_ty env
             (instantiate_struct_field_ty lts args f))
        (struct_fields sdef) ->
      capture_ref_free_ty env (MkTy u (TStruct name lts args))
  | CRFT_Enum : forall u name lts args edef,
      lookup_enum name env = Some edef ->
      Forall (capture_ref_free_ty env) args ->
      Forall
        (fun v =>
           Forall
             (fun T =>
                capture_ref_free_ty env
                  (instantiate_enum_variant_field_ty lts args T))
             (enum_variant_fields v))
        (enum_variants edef) ->
      capture_ref_free_ty env (MkTy u (TEnum name lts args))
  | CRFT_Fn : forall u params ret,
      Forall (capture_ref_free_ty env) params ->
      capture_ref_free_ty env ret ->
      capture_ref_free_ty env (MkTy u (TFn params ret))
  | CRFT_Forall : forall u n Ω body,
      capture_ref_free_ty env body ->
      capture_ref_free_ty env (MkTy u (TForall n Ω body))
  | CRFT_TypeForall : forall u n bounds body,
      capture_ref_free_ty env body ->
      capture_ref_free_ty env (MkTy u (TTypeForall n bounds body))
  .

Fixpoint capture_ref_free_ty_b_fuel
    (fuel : nat) (env : global_env) (T : Ty) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match T with
      | MkTy _ (TStruct name lts args) =>
          forallb (capture_ref_free_ty_b_fuel fuel' env) args &&
          match lookup_struct name env with
          | Some sdef =>
              forallb
                (fun f =>
                  capture_ref_free_ty_b_fuel fuel' env
                    (instantiate_struct_field_ty lts args f))
                (struct_fields sdef)
          | None => false
          end
      | MkTy _ (TEnum name lts args) =>
          forallb (capture_ref_free_ty_b_fuel fuel' env) args &&
          match lookup_enum name env with
          | Some edef =>
              forallb
                (fun v =>
                  forallb
                    (fun T =>
                      capture_ref_free_ty_b_fuel fuel' env
                        (instantiate_enum_variant_field_ty lts args T))
                    (enum_variant_fields v))
                (enum_variants edef)
          | None => false
          end
      | MkTy _ (TFn ts r) =>
          forallb (capture_ref_free_ty_b_fuel fuel' env) ts &&
          capture_ref_free_ty_b_fuel fuel' env r
      | MkTy _ (TClosure _ _ _) => false
      | MkTy _ (TForall _ _ body) =>
          capture_ref_free_ty_b_fuel fuel' env body
      | MkTy _ (TTypeForall _ bounds body) =>
          capture_ref_free_ty_b_fuel fuel' env body
      | MkTy _ (TRef _ _ _) => false
      | MkTy _ (TNamed _) => false
      | MkTy _ (TParam _) => false
      | _ => true
      end
  end.

Definition capture_ref_free_ty_b (env : global_env) (T : Ty) : bool :=
  capture_ref_free_ty_b_fuel
    (S (List.length (env_structs env) + List.length (env_enums env) + ty_depth T)) env T.

Lemma capture_ref_free_ty_b_fuel_sound :
  forall fuel env T,
    capture_ref_free_ty_b_fuel fuel env T = true ->
    capture_ref_free_ty env T.
Proof.
  induction fuel as [| fuel IH]; intros env T Hfree; simpl in Hfree;
    try discriminate.
  assert (Hlist : forall ts,
    forallb (capture_ref_free_ty_b_fuel fuel env) ts = true ->
    Forall (capture_ref_free_ty env) ts).
  { induction ts as [| T0 Ts IHTs]; simpl; intros Hts.
    - constructor.
    - apply andb_true_iff in Hts as [HT HTs].
      constructor.
      + apply IH. exact HT.
      + apply IHTs. exact HTs. }
  destruct T as [u core].
  destruct core as
    [| | | | named | tparam | name lts args | name lts args | params ret
     | env_lt params ret | n Ω body | tn tbounds tbody | la rk inner];
    simpl in *; try discriminate.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply andb_true_iff in Hfree as [Hargs Hfields_lookup].
    destruct (lookup_struct name env) as [sdef |] eqn:Hlookup;
      try discriminate.
    eapply CRFT_Struct.
    + exact Hlookup.
    + apply Hlist. exact Hargs.
    + apply Forall_forall.
      intros f Hin.
      apply forallb_forall with (x := f) in Hfields_lookup; [| exact Hin].
      apply IH. exact Hfields_lookup.
  - apply andb_true_iff in Hfree as [Hargs Hvariants_lookup].
    destruct (lookup_enum name env) as [edef |] eqn:Hlookup;
      try discriminate.
    eapply CRFT_Enum.
    + exact Hlookup.
    + apply Hlist. exact Hargs.
    + apply Forall_forall.
      intros v Hvin.
      apply forallb_forall with (x := v) in Hvariants_lookup; [| exact Hvin].
      apply Forall_forall.
      intros T Hin.
      apply forallb_forall with (x := T) in Hvariants_lookup; [| exact Hin].
      apply IH. exact Hvariants_lookup.
  - apply andb_true_iff in Hfree as [Hparams Hret].
    eapply CRFT_Fn.
    + apply Hlist. exact Hparams.
    + apply IH. exact Hret.
  - apply CRFT_Forall. apply IH. exact Hfree.
  - apply CRFT_TypeForall. apply IH. exact Hfree.
Qed.

Lemma capture_ref_free_ty_b_sound :
  forall env T,
    capture_ref_free_ty_b env T = true ->
    capture_ref_free_ty env T.
Proof.
  intros env T Hfree.
  unfold capture_ref_free_ty_b in Hfree.
  eapply capture_ref_free_ty_b_fuel_sound. exact Hfree.
Qed.

Lemma capture_ref_free_ty_b_fuel_ty_ref_free :
  forall fuel env T,
    capture_ref_free_ty_b_fuel fuel env T = true ->
    ty_ref_free_b T = true.
Proof.
  induction fuel as [| fuel IH]; intros env T Hfree; simpl in Hfree;
    try discriminate.
  assert (Hlist : forall ts,
    forallb (capture_ref_free_ty_b_fuel fuel env) ts = true ->
    forallb ty_ref_free_b ts = true).
  { induction ts as [| T0 Ts IHTs]; simpl; intros Hts; try reflexivity.
    apply andb_true_iff in Hts as [HT HTs].
    rewrite (IH env T0 HT), (IHTs HTs). reflexivity. }
  destruct T as [u core]; destruct core; simpl in *; try reflexivity;
    try discriminate.
  - apply andb_true_iff in Hfree as [Hargs _].
    apply Hlist. exact Hargs.
  - apply andb_true_iff in Hfree as [Hargs _].
    apply Hlist. exact Hargs.
  - apply andb_true_iff in Hfree as [Hargs Hret].
    rewrite (Hlist _ Hargs), (IH env t Hret). reflexivity.
  - apply (IH env t). exact Hfree.
  - apply (IH env t). exact Hfree.
Qed.

Lemma capture_ref_free_ty_b_ty_ref_free :
  forall env T,
    capture_ref_free_ty_b env T = true ->
    ty_ref_free_b T = true.
Proof.
  intros env T Hfree.
  unfold capture_ref_free_ty_b in Hfree.
  eapply capture_ref_free_ty_b_fuel_ty_ref_free. exact Hfree.
Qed.

(* ------------------------------------------------------------------ *)
(* Decidable context operations                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup_b (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, st, _) :: t =>
      if ident_eqb x n then Some (T, st_consumed st) else ctx_lookup_b x t
  end.

Fixpoint ctx_consume_b (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, st, m) :: t =>
      if ident_eqb x n
      then Some ((n, T, state_consume_path [] st, m) :: t)
      else match ctx_consume_b x t with
           | None    => None
           | Some t' => Some ((n, T, st, m) :: t')
           end
  end.

Fixpoint ctx_lookup_mut_b (x : ident) (Γ : ctx) : option mutability :=
  match Γ with
  | [] => None
  | (n, _, _, m) :: t => if ident_eqb x n then Some m else ctx_lookup_mut_b x t
  end.

Definition ctx_add_b (x : ident) (T : Ty) (m : mutability) (Γ : ctx) : ctx :=
  (x, T, binding_state_of_bool false, m) :: Γ.

Fixpoint ctx_remove_b (x : ident) (Γ : ctx) : ctx :=
  match Γ with
  | []              => []
  | (n, T, st, m) :: t =>
      if ident_eqb x n then t
      else (n, T, st, m) :: ctx_remove_b x t
  end.

(* Returns true iff x's usage constraint is satisfied after its scope:
   - linear: x must be consumed (found with consumed=true)
   - affine/unrestricted: always ok *)
Definition ctx_check_ok (x : ident) (T : Ty) (Γ : ctx) : bool :=
  match ty_usage T with
  | ULinear =>
      match ctx_lookup_state x Γ with
      | Some (_, st) => st_consumed st
      | _              => false
      end
  | _ => true
  end.

(* ------------------------------------------------------------------ *)
(* Function environment lookup                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint lookup_fn_b (name : ident) (fenv : list fn_def) : option fn_def :=
  match fenv with
  | []     => None
  | f :: t => if ident_eqb name (fn_name f) then Some f
              else lookup_fn_b name t
  end.

(* ------------------------------------------------------------------ *)
(* Lifetime well-formedness                                           *)
(*                                                                    *)
(* mk_region_ctx n  =  [LVar 0; LVar 1; ...; LVar (n-1)]             *)
(* wf_type_b Δ T    =  true iff every reference lifetime in T is      *)
(*                      LStatic or a member of Δ.                     *)
(* ------------------------------------------------------------------ *)

Fixpoint mk_region_ctx (n : nat) : region_ctx :=
  match n with
  | O    => []
  | S k  => mk_region_ctx k ++ [LVar k]
  end.

Definition wf_lifetime_at_b (bound_depth : nat) (Δ : region_ctx) (l : lifetime) : bool :=
  match l with
  | LStatic => true
  | LVar _  => existsb (lifetime_eqb l) Δ
  | LBound i => Nat.ltb i bound_depth
  end.

Definition wf_outlives_at_b (bound_depth : nat) (Δ : region_ctx) (Ω : outlives_ctx) : bool :=
  forallb (fun '(a, b) => wf_lifetime_at_b bound_depth Δ a && wf_lifetime_at_b bound_depth Δ b) Ω.

Fixpoint wf_type_at_b (bound_depth : nat) (Δ : region_ctx) (T : Ty) : bool :=
  match T with
  | MkTy _ (TStruct _ lts args) =>
      forallb (wf_lifetime_at_b bound_depth Δ) lts &&
      forallb (wf_type_at_b bound_depth Δ) args
  | MkTy _ (TEnum _ lts args) =>
      forallb (wf_lifetime_at_b bound_depth Δ) lts &&
      forallb (wf_type_at_b bound_depth Δ) args
  | MkTy u (TRef l rk T_inner) =>
      ref_usage_ok_b u rk && wf_lifetime_at_b bound_depth Δ l && wf_type_at_b bound_depth Δ T_inner
  | MkTy _ (TFn ts r) =>
      forallb (wf_type_at_b bound_depth Δ) ts && wf_type_at_b bound_depth Δ r
  | MkTy _ (TClosure l ts r) =>
      wf_lifetime_at_b bound_depth Δ l &&
      forallb (wf_type_at_b bound_depth Δ) ts && wf_type_at_b bound_depth Δ r
  | MkTy _ (TForall n Ω body) =>
      wf_outlives_at_b (n + bound_depth) Δ Ω && wf_type_at_b (n + bound_depth) Δ body
  | MkTy _ (TTypeForall _ bounds body) =>
      forallb
        (fun b =>
           forallb
             (fun tr => forallb (wf_type_at_b bound_depth Δ)
                (core_trait_ref_args Ty tr))
             (core_bound_traits Ty b))
        bounds &&
      wf_type_at_b bound_depth Δ body
  | _ => true
  end.

Definition wf_lifetime_b (Δ : region_ctx) (l : lifetime) : bool :=
  wf_lifetime_at_b 0 Δ l.

Definition wf_type_b (Δ : region_ctx) (T : Ty) : bool :=
  wf_type_at_b 0 Δ T.
