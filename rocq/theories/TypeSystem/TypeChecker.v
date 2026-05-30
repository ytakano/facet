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
(* Function environment lookup                                           *)
(* ------------------------------------------------------------------ *)

Fixpoint lookup_fn_b (name : ident) (fenv : list fn_def) : option fn_def :=
  match fenv with
  | []     => None
  | f :: t => if ident_eqb name (fn_name f) then Some f
              else lookup_fn_b name t
  end.

(* ------------------------------------------------------------------ *)
(* Lifetime well-formedness                                              *)
(*                                                                      *)
(* mk_region_ctx n  =  [LVar 0; LVar 1; ...; LVar (n-1)]              *)
(* wf_type_b Δ T    =  true iff every reference lifetime in T is       *)
(*                      LStatic or a member of Δ.                      *)
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

(* ------------------------------------------------------------------ *)
(* Checker result/error types                                            *)
(* ------------------------------------------------------------------ *)

Inductive infer_error : Type :=
  | ErrUnknownVar : ident -> infer_error
  | ErrAlreadyConsumed : ident -> infer_error
  | ErrTypeMismatch : TypeCore Ty -> TypeCore Ty -> infer_error
  | ErrNotMutable : ident -> infer_error
  | ErrUsageMismatch : usage -> usage -> infer_error
  | ErrFunctionNotFound : ident -> infer_error
  | ErrArityMismatch : infer_error
  | ErrDuplicateParam : ident -> infer_error
  | ErrContextCheckFailed : infer_error
  | ErrNotImplemented : infer_error
  | ErrImmutableBorrow : ident -> infer_error       (* &mut x where x is immutable *)
  | ErrNotAReference : TypeCore Ty -> infer_error   (* *e where e is not a reference type *)
  | ErrNotAFunction : TypeCore Ty -> infer_error
  | ErrBorrowConflict : ident -> infer_error       (* borrow conflicts with existing active borrow *)
  | ErrLifetimeLeak : infer_error                 (* return type references a local lifetime *)
  | ErrLifetimeConflict : infer_error             (* unification conflict in call lifetime substitution *)
  | ErrHrtBoundUnsatisfied : infer_error
  | ErrHrtUnresolvedBound : infer_error
  | ErrHrtMonomorphicUsedBound : infer_error
  | ErrMalformedHrtBody : TypeCore Ty -> infer_error
  | ErrStructNotFound : string -> infer_error
  | ErrEnumNotFound : string -> infer_error
  | ErrVariantNotFound : string -> infer_error
  | ErrNotAnEnum : TypeCore Ty -> infer_error
  | ErrDuplicateVariant : string -> infer_error
  | ErrMissingVariant : string -> infer_error
  | ErrMatchPayloadUnsupported : string -> infer_error
  | ErrFieldNotFound : string -> infer_error
  | ErrDuplicateField : string -> infer_error
  | ErrMissingField : string -> infer_error
  | ErrTraitImplNotFound : string -> Ty -> infer_error
  | ErrTraitImplAmbiguous : string -> Ty -> infer_error
  | ErrTypeArgInferenceFailed : infer_error
  | ErrEndToEndSafetyGateFailed : infer_error
  | ErrGlobalNamesNotUnique : infer_error
  | ErrInFunction : ident -> infer_error -> infer_error.

Definition compatible_error (T_actual T_expected : Ty) : infer_error :=
  match ty_core T_actual, ty_core T_expected with
  | TFn _ _, TForall _ _ body =>
      if contains_lbound_ty body
      then ErrHrtMonomorphicUsedBound
      else ErrTypeMismatch (ty_core T_actual) (ty_core T_expected)
  | _, _ =>
      if ty_core_eqb (ty_core T_actual) (ty_core T_expected)
      then ErrUsageMismatch (ty_usage T_actual) (ty_usage T_expected)
      else ErrTypeMismatch (ty_core T_actual) (ty_core T_expected)
  end.

Definition no_captures_b (f : fn_def) : bool :=
  match fn_captures f with
  | [] => true
  | _ :: _ => false
  end.

Definition trait_impl_error_with_args
    (env : global_env) (trait_name : string) (trait_args : list Ty)
    (for_ty : Ty) : option infer_error :=
  match lookup_trait trait_name env with
  | None => Some (ErrTraitImplNotFound trait_name for_ty)
  | Some t =>
      if negb (Nat.eqb (List.length trait_args) (trait_type_params t))
      then Some ErrArityMismatch
      else
      match matching_impls trait_name trait_args for_ty (env_impls env) with
      | [] => Some (ErrTraitImplNotFound trait_name for_ty)
      | [_] => None
      | _ :: _ :: _ => Some (ErrTraitImplAmbiguous trait_name for_ty)
      end
  end.

Definition trait_impl_error
    (env : global_env) (trait_name : string) (for_ty : Ty) : option infer_error :=
  trait_impl_error_with_args env trait_name [] for_ty.

Definition instantiate_trait_ref (args : list Ty) (tr : trait_ref) : trait_ref :=
  MkTraitRef (trait_ref_name tr)
    (map (subst_type_params_ty args) (trait_ref_args tr)).

Fixpoint ty_list_eqb (xs ys : list Ty) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => ty_eqb x y && ty_list_eqb xs' ys'
  | _, _ => false
  end.

Definition trait_ref_eqb (a b : trait_ref) : bool :=
  String.eqb (trait_ref_name a) (trait_ref_name b) &&
  ty_list_eqb (trait_ref_args a) (trait_ref_args b).

Definition local_bound_satisfies_trait
    (bounds : list trait_bound) (type_index : nat) (tr : trait_ref) : bool :=
  existsb
    (fun b =>
      Nat.eqb (bound_type_index b) type_index &&
      existsb (trait_ref_eqb tr) (bound_traits b))
    bounds.

Definition local_bounds_satisfy_trait_ref_for_ty
    (bounds : list trait_bound) (tr : trait_ref) (for_ty : Ty) : bool :=
  match ty_core for_ty with
  | TParam i => local_bound_satisfies_trait bounds i tr
  | _ => false
  end.

Definition check_trait_ref_for_ty
    (env : global_env) (tr : trait_ref) (for_ty : Ty) : option infer_error :=
  if local_bounds_satisfy_trait_ref_for_ty (env_local_bounds env) tr for_ty
  then None
  else trait_impl_error_with_args env (trait_ref_name tr) (trait_ref_args tr) for_ty.

Fixpoint check_trait_refs_for_ty
    (env : global_env) (traits : list trait_ref) (for_ty : Ty)
    : option infer_error :=
  match traits with
  | [] => None
  | tr :: rest =>
      match check_trait_ref_for_ty env tr for_ty with
      | Some err => Some err
      | None => check_trait_refs_for_ty env rest for_ty
      end
  end.

Fixpoint type_arg_list_set_nth
    (i : nat) (v : option Ty) (σ : list (option Ty)) : list (option Ty) :=
  match i, σ with
  | O, _ :: rest => v :: rest
  | O, [] => []
  | S i', h :: rest => h :: type_arg_list_set_nth i' v rest
  | S _, [] => []
  end.

Definition type_arg_subst_vec_add
    (σ : list (option Ty)) (i : nat) (T : Ty)
    : option (list (option Ty)) :=
  match nth_error σ i with
  | None => None
  | Some None => Some (type_arg_list_set_nth i (Some T) σ)
  | Some (Some T_old) =>
      if ty_eqb T_old T then Some σ else None
  end.

Fixpoint infer_type_args_from_ty
    (fuel : nat) (formal actual : Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match fuel with
  | O => None
  | S fuel' =>
  match formal, actual with
  | MkTy u_f (TParam i), MkTy _ c_a =>
      type_arg_subst_vec_add σ i (MkTy u_f c_a)
  | MkTy _ (TStruct name_f lts_f args_f), MkTy _ (TStruct name_a lts_a args_a) =>
      if String.eqb name_f name_a && lifetime_list_eqb lts_f lts_a
      then infer_type_args_from_tys fuel' args_f args_a σ
      else None
  | MkTy _ (TEnum name_f lts_f args_f), MkTy _ (TEnum name_a lts_a args_a) =>
      if String.eqb name_f name_a && lifetime_list_eqb lts_f lts_a
      then infer_type_args_from_tys fuel' args_f args_a σ
      else None
  | MkTy _ (TRef _ rk_f inner_f), MkTy _ (TRef _ rk_a inner_a) =>
      if ref_kind_eqb rk_f rk_a
      then infer_type_args_from_ty fuel' inner_f inner_a σ
      else None
  | MkTy _ (TFn ps_f ret_f), MkTy _ (TFn ps_a ret_a) =>
      match infer_type_args_from_tys fuel' ps_f ps_a σ with
      | Some σ' => infer_type_args_from_ty fuel' ret_f ret_a σ'
      | None => None
      end
  | MkTy _ (TClosure _ ps_f ret_f), MkTy _ (TClosure _ ps_a ret_a) =>
      match infer_type_args_from_tys fuel' ps_f ps_a σ with
      | Some σ' => infer_type_args_from_ty fuel' ret_f ret_a σ'
      | None => None
      end
  | MkTy _ (TForall n_f Ω_f body_f), MkTy _ (TForall n_a Ω_a body_a) =>
      if Nat.eqb n_f n_a && outlives_ctx_eqb Ω_f Ω_a
      then infer_type_args_from_ty fuel' body_f body_a σ
      else None
  | MkTy _ (TTypeForall n_f bounds_f body_f),
    MkTy _ (TTypeForall n_a bounds_a body_a) =>
      if Nat.eqb n_f n_a &&
         ty_eqb (MkTy UUnrestricted (TTypeForall n_f bounds_f body_f))
                (MkTy UUnrestricted (TTypeForall n_a bounds_a body_a))
      then Some σ
      else None
  | _, _ =>
      if ty_core_eqb (ty_core formal) (ty_core actual) then Some σ else None
  end
  end

with infer_type_args_from_tys
    (fuel : nat) (formals actuals : list Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match fuel with
  | O => None
  | S fuel' =>
  match formals, actuals with
  | [], [] => Some σ
  | f :: fs, a :: as_ =>
      match infer_type_args_from_ty fuel' f a σ with
      | Some σ' => infer_type_args_from_tys fuel' fs as_ σ'
      | None => None
      end
	  | _, _ => None
	  end
	  end.

Fixpoint infer_type_args_from_params
    (params : list param) (arg_tys : list Ty) (σ : list (option Ty))
    : option (list (option Ty)) :=
  match params, arg_tys with
  | [], [] => Some σ
  | p :: ps, a :: as_ =>
      match infer_type_args_from_ty (ty_depth (param_ty p) + ty_depth a)
              (param_ty p) a σ with
      | Some σ' => infer_type_args_from_params ps as_ σ'
      | None => None
      end
  | _, _ => None
  end.

Fixpoint finalize_type_args (σ : list (option Ty)) : option (list Ty) :=
  match σ with
  | [] => Some []
  | Some T :: rest =>
      match finalize_type_args rest with
      | Some Ts => Some (T :: Ts)
      | None => None
      end
  | None :: _ => None
  end.

Definition infer_call_type_args
    (fdef : fn_def) (arg_tys : list Ty) : option (list Ty) :=
  match infer_type_args_from_params
          (fn_params fdef) arg_tys (repeat None (fn_type_params fdef)) with
  | Some σ => finalize_type_args σ
  | None => None
  end.

Definition infer_call_type_args_expected
    (fdef : fn_def) (arg_tys : list Ty) (expected : option Ty)
    : option (list Ty) :=
  match infer_type_args_from_params
          (fn_params fdef) arg_tys (repeat None (fn_type_params fdef)) with
  | None => None
  | Some σ_args =>
      let σ_expected :=
        match expected with
        | None => Some σ_args
        | Some T_expected =>
            infer_type_args_from_ty
              (ty_depth (fn_ret fdef) + ty_depth T_expected)
              (fn_ret fdef) T_expected σ_args
        end in
      match σ_expected with
      | Some σ => finalize_type_args σ
      | None => None
      end
  end.

Fixpoint check_struct_bounds
    (env : global_env) (bounds : list trait_bound) (args : list Ty)
    : option infer_error :=
  match bounds with
  | [] => None
  | b :: rest =>
      match nth_error args (bound_type_index b) with
      | None => Some ErrArityMismatch
      | Some for_ty =>
          let traits := map (instantiate_trait_ref args) (bound_traits b) in
          match check_trait_refs_for_ty env traits for_ty with
          | Some err => Some err
          | None => check_struct_bounds env rest args
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(* Higher-rank lifetime helpers                                          *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Lifetime substitution helpers for ECall                               *)
(* ------------------------------------------------------------------ *)

Fixpoint list_set_nth {A : Type} (i : nat) (v : A) (l : list A) : list A :=
  match i, l with
  | O, _ :: t => v :: t
  | O, [] => []
  | S i', h :: t => h :: list_set_nth i' v t
  | S _, [] => []
  end.

Definition lt_subst_vec_add
    (σ : list (option lifetime))
    (i : nat)
    (l_a : lifetime)
    : option (list (option lifetime)) :=
  match nth_error σ i with
  | None => None
  | Some None => Some (list_set_nth i (Some l_a) σ)
  | Some (Some l') =>
      if lifetime_eqb l' l_a then Some σ else None
  end.

Fixpoint unify_lt (m : nat) (σ : list (option lifetime))
    (T_param T_e : Ty) {struct T_param} : option (list (option lifetime)) :=
  match T_param with
  | MkTy _ (TForall _ [] body) =>
      if negb (contains_lbound_ty body)
      then unify_lt m σ body T_e
      else if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  | MkTy _ (TRef l_p rk T_p_inner) =>
      match T_e with
      | MkTy _ (TRef l_a rk' T_e_inner) =>
          if negb (ref_kind_eqb rk rk') then None
          else
            match l_p with
            | LVar i =>
                if Nat.ltb i m then
                  match lt_subst_vec_add σ i l_a with
                  | None => None
                  | Some σ' => unify_lt m σ' T_p_inner T_e_inner
                  end
                else if lifetime_eqb (LVar i) l_a
                     then unify_lt m σ T_p_inner T_e_inner
                     else None
            | LStatic =>
                if lifetime_eqb LStatic l_a
                then unify_lt m σ T_p_inner T_e_inner
                else None
            | LBound i =>
                if lifetime_eqb (LBound i) l_a
                then unify_lt m σ T_p_inner T_e_inner
                else None
            end
      | _ => None
      end
  | _ =>
      if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  end.

Fixpoint finalize_subst (σ : list (option lifetime)) : list lifetime :=
  match σ with
  | [] => []
  | None :: rest => LStatic :: finalize_subst rest
  | Some l :: rest => l :: finalize_subst rest
  end.

Fixpoint build_sigma (m : nat) (σ_acc : list (option lifetime))
    (arg_tys : list Ty) (params : list param)
    : option (list (option lifetime)) :=
  match arg_tys, params with
  | [], [] => Some σ_acc
  | t :: ts, p :: ps =>
      match unify_lt m σ_acc (param_ty p) t with
      | None => None
      | Some σ' => build_sigma m σ' ts ps
      end
  | _, _ => None
  end.

Definition bound_subst_vec_add
    (σ : list (option lifetime))
    (i : nat)
    (l_a : lifetime)
    : option (list (option lifetime)) :=
  lt_subst_vec_add σ i l_a.

Fixpoint unify_bound_lt (σ : list (option lifetime))
    (T_param T_e : Ty) {struct T_param} : option (list (option lifetime)) :=
  match T_param with
  | MkTy _ (TRef l_p rk T_p_inner) =>
      match T_e with
      | MkTy _ (TRef l_a rk' T_e_inner) =>
          if negb (ref_kind_eqb rk rk') then None
          else
            match l_p with
            | LBound i =>
                match bound_subst_vec_add σ i l_a with
                | None => None
                | Some σ' => unify_bound_lt σ' T_p_inner T_e_inner
                end
            | _ =>
                if lifetime_eqb l_p l_a
                then unify_bound_lt σ T_p_inner T_e_inner
                else None
            end
      | _ => None
      end
  | MkTy _ (TFn ps pr) =>
      match T_e with
      | MkTy _ (TFn es er) =>
          let fix go (σ0 : list (option lifetime)) ps0 es0 :=
            match ps0, es0 with
            | [], [] => unify_bound_lt σ0 pr er
            | p :: ps', e :: es' =>
                match unify_bound_lt σ0 p e with
                | None => None
                | Some σ' => go σ' ps' es'
                end
            | _, _ => None
            end
          in go σ ps es
      | _ => None
      end
  | _ =>
      if ty_core_eqb (ty_core T_param) (ty_core T_e) then Some σ else None
  end.

Fixpoint build_bound_sigma (σ_acc : list (option lifetime))
    (arg_tys params : list Ty) : option (list (option lifetime)) :=
  match arg_tys, params with
  | [], [] => Some σ_acc
  | t :: ts, p :: ps =>
      match unify_bound_lt σ_acc p t with
      | None => None
      | Some σ' => build_bound_sigma σ' ts ps
      end
  | _, _ => None
  end.

Fixpoint complete_bound_sigma_with_vars_from
    (n i : nat) (σ : list (option lifetime)) : list (option lifetime) :=
  match σ with
  | [] => []
  | Some l :: rest =>
      Some l :: complete_bound_sigma_with_vars_from n (S i) rest
  | None :: rest =>
      (if Nat.ltb i n then Some (LVar i) else None) ::
      complete_bound_sigma_with_vars_from n (S i) rest
  end.

Definition complete_bound_sigma_with_vars
    (n : nat) (σ : list (option lifetime)) : list (option lifetime) :=
  complete_bound_sigma_with_vars_from n 0 σ.

Fixpoint check_args (Ω : outlives_ctx) (arg_tys : list Ty) (params : list param)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_b Ω t (param_ty p)
      then check_args Ω ts ps
      else Some (compatible_error t (param_ty p))
  | _, _ => Some ErrArityMismatch
  end.

Fixpoint check_arg_tys (Ω : outlives_ctx) (arg_tys params : list Ty)
    : option infer_error :=
  match arg_tys, params with
  | [], [] => None
  | t :: ts, p :: ps =>
      if ty_compatible_b Ω t p
      then check_arg_tys Ω ts ps
      else Some (compatible_error t p)
  | _, _ => Some ErrArityMismatch
  end.

Inductive infer_result (A : Type) : Type :=
  | infer_ok : A -> infer_result A
  | infer_err : infer_error -> infer_result A.

Arguments infer_ok {_} _.
Arguments infer_err {_} _.

Definition infer_if_bool {A : Type} (b : bool)
    (ok err : infer_result A) : infer_result A :=
  if b then ok else err.

Fixpoint tys_depth (ts : list Ty) : nat :=
  match ts with
  | [] => 0
  | t :: ts' => ty_depth t + tys_depth ts'
  end.

Definition infer_type_forall_args
    (type_params : nat) (param_tys arg_tys : list Ty) : option (list Ty) :=
  match infer_type_args_from_tys
          (S (tys_depth param_tys + tys_depth arg_tys))
          param_tys arg_tys (repeat None type_params) with
  | Some σ => finalize_type_args σ
  | None => None
  end.

Definition check_type_forall_bounds
    (env : global_env) (bounds : list (core_trait_bound Ty)) (type_args : list Ty)
    : option infer_error :=
  check_struct_bounds env (trait_bounds_of_core_trait_bounds bounds) type_args.

Definition infer_type_forall_call_no_env
    (Ω : outlives_ctx) (type_params : nat)
    (bounds : list (core_trait_bound Ty)) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match bounds with
  | [] =>
      match ty_core body with
      | TFn param_tys ret =>
          match infer_type_forall_args type_params param_tys arg_tys with
          | None => infer_err ErrTypeArgInferenceFailed
          | Some type_args =>
              let param_tys' := map (subst_type_params_ty type_args) param_tys in
              match check_arg_tys Ω arg_tys param_tys' with
              | Some err => infer_err err
              | None => infer_ok (subst_type_params_ty type_args ret)
              end
          end
      | c => infer_err (ErrMalformedHrtBody c)
      end
  | _ => infer_err ErrNotImplemented
  end.

Definition infer_type_forall_call_env
    (env : global_env) (Ω : outlives_ctx) (type_params : nat)
    (bounds : list (core_trait_bound Ty)) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          match check_type_forall_bounds env bounds type_args with
          | Some err => infer_err err
          | None =>
              match check_arg_tys Ω arg_tys (map (subst_type_params_ty type_args) param_tys) with
              | Some err => infer_err err
              | None => infer_ok (subst_type_params_ty type_args ret)
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition shared_ref_lifetime_of_ty (T : Ty) : option lifetime :=
  match T with
  | MkTy _ (TRef l RShared _) => Some l
  | _ => None
  end.

Fixpoint collect_shared_ref_lifetimes (captured_tys : list Ty) : list lifetime :=
  match captured_tys with
  | [] => []
  | T :: rest =>
      match shared_ref_lifetime_of_ty T with
      | Some l => l :: collect_shared_ref_lifetimes rest
      | None => collect_shared_ref_lifetimes rest
      end
  end.

Fixpoint all_outlive_b (Ω : outlives_ctx) (lts : list lifetime)
    (env_lt : lifetime) : bool :=
  match lts with
  | [] => true
  | l :: rest => outlives_b Ω l env_lt && all_outlive_b Ω rest env_lt
  end.

Fixpoint find_closure_env_lifetime
    (Ω : outlives_ctx) (lts candidates : list lifetime)
    : option lifetime :=
  match candidates with
  | [] => None
  | l :: rest =>
      if all_outlive_b Ω lts l
      then Some l
      else find_closure_env_lifetime Ω lts rest
  end.

Definition infer_closure_env_lifetime
    (Ω : outlives_ctx) (captured_tys : list Ty) : infer_result lifetime :=
  let lts := collect_shared_ref_lifetimes captured_tys in
  match lts with
  | [] => infer_ok LStatic
  | _ =>
      match find_closure_env_lifetime Ω lts lts with
      | Some env_lt => infer_ok env_lt
      | None => infer_err ErrLifetimeConflict
      end
  end.

Definition closure_capture_allowed_b
    (env : global_env) (Ω : outlives_ctx) (env_lt : lifetime) (T : Ty)
    : bool :=
  capture_ref_free_ty_b env T ||
  match T with
  | MkTy _ (TRef l RShared _) => outlives_b Ω l env_lt
  | _ => false
  end.

Fixpoint closure_captures_allowed_b
    (env : global_env) (Ω : outlives_ctx) (env_lt : lifetime)
    (captured_tys : list Ty) : bool :=
  match captured_tys with
  | [] => true
  | T :: rest =>
      closure_capture_allowed_b env Ω env_lt T &&
      closure_captures_allowed_b env Ω env_lt rest
  end.

Fixpoint check_make_closure_captures_ctx_base
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      match ctx_lookup_state x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if negb (binding_available_b st [])
          then infer_err (ErrAlreadyConsumed x)
          else
          match ctx_lookup_mut_b x Γ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if ty_compatible_b Ω T (param_ty cap)
                then
                  match check_make_closure_captures_ctx_base env Ω Γ captures' params' with
                  | infer_ok captured_tys => infer_ok (T :: captured_tys)
                  | infer_err err => infer_err err
                  end
                else infer_err (compatible_error T (param_ty cap))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition check_make_closure_captures_ctx
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (lifetime * list Ty) :=
  match check_make_closure_captures_ctx_base env Ω Γ captures params with
  | infer_ok captured_tys =>
      match infer_closure_env_lifetime Ω captured_tys with
      | infer_ok env_lt =>
          if closure_captures_allowed_b env Ω env_lt captured_tys
          then infer_ok (env_lt, captured_tys)
          else infer_err (ErrNotAReference TUnits)
      | infer_err err => infer_err err
      end
  | infer_err err => infer_err err
  end.

Fixpoint check_make_closure_captures_exact_ctx
    (env : global_env) (Ω : outlives_ctx) (Γ : ctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      if match param_mutability cap with MImmutable => false | MMutable => true end
      then infer_err ErrContextCheckFailed
      else
      match ctx_lookup_state (param_name cap) Γ with
      | Some _ => infer_err ErrContextCheckFailed
      | None =>
      match ctx_lookup_state x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if st_consumed st
          then infer_err ErrContextCheckFailed
          else
          match st_moved_paths st with
          | _ :: _ => infer_err ErrContextCheckFailed
          | [] =>
          match ctx_lookup_mut_b x Γ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if capture_ref_free_ty_b env T
                then
                  if ty_eqb T (param_ty cap) &&
                     ty_compatible_b Ω T (param_ty cap)
                  then
                    match check_make_closure_captures_exact_ctx env Ω Γ captures' params' with
                    | infer_ok rest_tys => infer_ok (T :: rest_tys)
                    | infer_err err => infer_err err
                    end
                  else infer_err (compatible_error T (param_ty cap))
                else infer_err (ErrNotAReference (ty_core T))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
          end
      end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Fixpoint infer_place (Γ : ctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T, false) => infer_ok T
      end
  | PDeref q =>
      match infer_place Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField _ _ => infer_err ErrNotImplemented
  end.

Definition lookup_field_b (name : string) (fields : list (string * expr)) : option expr :=
  let fix go fields0 :=
    match fields0 with
    | [] => None
    | (fname, e) :: rest =>
        if String.eqb name fname then Some e else go rest
    end
  in go fields.

Definition has_field_b (name : string) (fields : list (string * expr)) : bool :=
  match lookup_field_b name fields with
  | Some _ => true
  | None => false
  end.

Fixpoint field_names_unique_b (fields : list (string * expr)) : bool :=
  match fields with
  | [] => true
  | (name, _) :: rest =>
      negb (has_field_b name rest) && field_names_unique_b rest
  end.

Definition first_duplicate_field (fields : list (string * expr)) : option string :=
  let fix go fields0 :=
    match fields0 with
    | [] => None
    | (name, _) :: rest =>
        if has_field_b name rest then Some name else go rest
    end
  in go fields.

Fixpoint first_unknown_field
    (fields : list (string * expr)) (defs : list field_def) : option string :=
  match fields with
  | [] => None
  | (name, _) :: rest =>
      match lookup_field name defs with
      | Some _ => first_unknown_field rest defs
      | None => Some name
      end
  end.

Fixpoint first_missing_field
    (defs : list field_def) (fields : list (string * expr)) : option string :=
  match defs with
  | [] => None
  | f :: rest =>
      if has_field_b (field_name f) fields
      then first_missing_field rest fields
      else Some (field_name f)
  end.

Definition lookup_branch_b (name : string)
    (branches : list (string * list ident * expr))
    : option expr :=
  lookup_expr_branch name branches.

Fixpoint has_branch_b (name : string)
    (branches : list (string * list ident * expr)) : bool :=
  match branches with
  | [] => false
  | (name', _, _) :: rest =>
      if String.eqb name name' then true else has_branch_b name rest
  end.

Fixpoint first_duplicate_branch
    (branches : list (string * list ident * expr)) : option string :=
  match branches with
  | [] => None
  | b :: rest =>
      let name := match_branch_name b in
      if has_branch_b name rest then Some name else first_duplicate_branch rest
  end.

Fixpoint first_unknown_variant_branch
    (branches : list (string * list ident * expr))
    (defs : list enum_variant_def)
    : option string :=
  match branches with
  | [] => None
  | (name, _, _) :: rest =>
      match lookup_enum_variant name defs with
      | Some _ => first_unknown_variant_branch rest defs
      | None => Some name
      end
  end.

Fixpoint first_missing_variant_branch
    (defs : list enum_variant_def)
    (branches : list (string * list ident * expr))
    : option string :=
  match defs with
  | [] => None
  | v :: rest =>
      if has_branch_b (enum_variant_name v) branches
      then first_missing_variant_branch rest branches
      else Some (enum_variant_name v)
  end.

Fixpoint first_payload_binder_branch
    (branches : list (string * list ident * expr)) : option string :=
  match branches with
  | [] => None
  | (name, [], _) :: rest => first_payload_binder_branch rest
  | (name, _ :: _, _) :: _ => Some name
  end.

Fixpoint first_payload_variant (defs : list enum_variant_def) : option string :=
  match defs with
  | [] => None
  | v :: rest =>
      match enum_variant_fields v with
      | [] => first_payload_variant rest
      | _ :: _ => Some (enum_variant_name v)
      end
  end.

Definition first_unsupported_match_payload
    (branches : list (string * list ident * expr))
    (defs : list enum_variant_def) : option string :=
  match first_payload_binder_branch branches with
  | Some name => Some name
  | None => first_payload_variant defs
  end.

Fixpoint usage_max_tys_nonempty (head : Ty) (tail : list Ty) : usage :=
  match tail with
  | [] => ty_usage head
  | t :: rest => usage_max (ty_usage head) (usage_max_tys_nonempty t rest)
  end.

Fixpoint ctx_merge_many (head : ctx) (tail : list ctx) : option ctx :=
  match tail with
  | [] => Some head
  | c :: rest =>
      match ctx_merge head c with
      | Some merged => ctx_merge_many merged rest
      | None => None
      end
  end.

Fixpoint match_binder_params (binders : list ident) (tys : list Ty)
    : infer_result (list param) :=
  match binders, tys with
  | [], [] => infer_ok []
  | x :: xs, T :: Ts =>
      match match_binder_params xs Ts with
      | infer_ok ps => infer_ok (MkParam MImmutable x T :: ps)
      | infer_err err => infer_err err
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition instantiate_enum_variant_field_tys
    (lts : list lifetime) (args : list Ty) (v : enum_variant_def) : list Ty :=
  map (instantiate_enum_variant_field_ty lts args) (enum_variant_fields v).

Definition match_payload_params
    (binders : list ident) (lts : list lifetime) (args : list Ty)
    (v : enum_variant_def) : infer_result (list param) :=
  match_binder_params binders (instantiate_enum_variant_field_tys lts args v).

Lemma match_binder_params_names :
  forall binders tys ps,
    match_binder_params binders tys = infer_ok ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params xs Ts) as [ps_tail | err] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps; simpl.
    rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_names :
  forall binders lts args v ps,
    match_payload_params binders lts args v = infer_ok ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params in Hmatch.
  eapply match_binder_params_names. exact Hmatch.
Qed.

Definition ctx_add_params (ps : list param) (Γ : ctx) : ctx :=
  params_ctx ps ++ Γ.

Fixpoint ctx_remove_params (ps : list param) (Γ : ctx) : ctx :=
  match ps with
  | [] => Γ
  | p :: rest => ctx_remove_params rest (ctx_remove_b (param_name p) Γ)
  end.

Fixpoint ctx_check_ok_params (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      ctx_check_ok (param_name p) (param_ty p) Γ &&
      ctx_check_ok_params rest Γ
  end.

Fixpoint ident_in_b (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: rest => ident_eqb x y || ident_in_b x rest
  end.

Fixpoint ident_nodup_b (xs : list ident) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (ident_in_b x rest) && ident_nodup_b rest
  end.

Definition params_names_nodup_b (ps : list param) : bool :=
  ident_nodup_b (ctx_names (params_ctx ps)).

Fixpoint ctx_lookup_params_none_b (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      match ctx_lookup_state (param_name p) Γ with
      | Some _ => false
      | None => ctx_lookup_params_none_b rest Γ
      end
  end.

Fixpoint unrestricted_unit_params_of_binders (binders : list ident) : list param :=
  match binders with
  | [] => []
  | x :: rest =>
      MkParam MImmutable x (MkTy UUnrestricted TUnits) ::
        unrestricted_unit_params_of_binders rest
  end.

Fixpoint infer_place_env (env : global_env) (Γ : ctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T, false) => infer_ok T
      end
  | PDeref q =>
      match infer_place_env env Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField q field =>
      match infer_place_env env Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TStruct sname lts args =>
              match lookup_struct sname env with
              | None => infer_err (ErrStructNotFound sname)
              | Some s =>
                  match lookup_field field (struct_fields s) with
                  | None => infer_err (ErrFieldNotFound field)
                  | Some f => infer_ok (instantiate_struct_field_ty lts args f)
                  end
              end
          | c => infer_err (ErrTypeMismatch c (TStruct "" [] []))
          end
      end
  end.

Definition wf_outlives_b (Δ : region_ctx) (Ω : outlives_ctx) : bool :=
  wf_outlives_at_b 0 Δ Ω.

Definition outlives_constraints_hold_b (Ω : outlives_ctx) (constraints : outlives_ctx) : bool :=
  forallb (fun '(a, b) => outlives_b Ω a b) constraints.

(* Infer the return type for a HRT (for<'a,...> fn(&...) -> ...) call.
   Used by the roots checker to handle TForall callee types. *)
Definition infer_hrt_call_env
    (Ω : outlives_ctx) (n m : nat) (bounds : outlives_ctx) (body : Ty) (arg_tys : list Ty)
    : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match build_bound_sigma (repeat None m) arg_tys param_tys with
      | None => infer_err ErrLifetimeConflict
      | Some σ =>
          match check_arg_tys Ω arg_tys (map (open_bound_ty σ) param_tys) with
          | Some err => infer_err err
          | None =>
              if contains_lbound_ty (open_bound_ty σ ret) ||
                 contains_lbound_outlives (open_bound_outlives σ bounds)
              then infer_err ErrHrtUnresolvedBound
              else if outlives_constraints_hold_b Ω (open_bound_outlives σ bounds)
                   then infer_ok (open_bound_ty σ ret)
                   else infer_err ErrHrtBoundUnsatisfied
          end
      end
  | TClosure env_lt param_tys ret =>
      match build_bound_sigma (repeat None m) arg_tys param_tys with
      | None => infer_err ErrLifetimeConflict
      | Some σ0 =>
          let σ := complete_bound_sigma_with_vars n σ0 in
          match check_arg_tys Ω arg_tys (map (open_bound_ty σ) param_tys) with
          | Some err => infer_err err
          | None =>
              let env_open := open_bound_lifetime σ env_lt in
              let ret_open := open_bound_ty σ ret in
              let bounds_open := open_bound_outlives σ bounds in
              if contains_lbound_lifetime env_open ||
                 contains_lbound_ty ret_open ||
                 contains_lbound_outlives bounds_open
              then infer_err ErrHrtUnresolvedBound
              else if outlives_constraints_hold_b Ω bounds_open
                   then infer_ok ret_open
                   else infer_err ErrHrtBoundUnsatisfied
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

Definition open_core_trait_bounds
    (σ : list (option lifetime)) (bounds : list (core_trait_bound Ty))
    : list (core_trait_bound Ty) :=
  map (map_core_trait_bound (open_bound_ty σ)) bounds.

Definition infer_mixed_forall_call_env
    (env : global_env) (Ω : outlives_ctx) (n m : nat)
    (lt_bounds : outlives_ctx) (type_params : nat)
    (type_bounds : list (core_trait_bound Ty)) (body : Ty)
    (arg_tys : list Ty) : infer_result Ty :=
  match ty_core body with
  | TFn param_tys ret =>
      match infer_type_forall_args type_params param_tys arg_tys with
      | None => infer_err ErrTypeArgInferenceFailed
      | Some type_args =>
          let param_tys_t := map (subst_type_params_ty type_args) param_tys in
          match build_bound_sigma (repeat None m) arg_tys param_tys_t with
          | None => infer_err ErrLifetimeConflict
          | Some σ0 =>
              let σ := complete_bound_sigma_with_vars n σ0 in
              let param_tys_open := map (open_bound_ty σ) param_tys_t in
              match check_arg_tys Ω arg_tys param_tys_open with
              | Some err => infer_err err
              | None =>
                  let ret_open := open_bound_ty σ
                    (subst_type_params_ty type_args ret) in
                  let lt_bounds_open := open_bound_outlives σ lt_bounds in
                  let type_bounds_open := open_core_trait_bounds σ type_bounds in
                  if contains_lbound_ty ret_open ||
                     contains_lbound_outlives lt_bounds_open ||
                     existsb
                       (fun b =>
                         existsb
                           (fun tr =>
                             existsb contains_lbound_ty (core_trait_ref_args Ty tr))
                           (core_bound_traits Ty b))
                       type_bounds_open
                  then infer_err ErrHrtUnresolvedBound
                  else if outlives_constraints_hold_b Ω lt_bounds_open
                  then
                    match check_type_forall_bounds env type_bounds_open type_args with
                    | Some err => infer_err err
                    | None => infer_ok ret_open
                    end
                  else infer_err ErrHrtBoundUnsatisfied
              end
          end
      end
  | c => infer_err (ErrMalformedHrtBody c)
  end.

(* ------------------------------------------------------------------ *)
(* Type inference                                                        *)
(*                                                                      *)
(* infer_core fenv Γ e = Some (T, Γ')                                   *)
(*   Returns the type T and the updated context Γ' after e is typed.      *)
(*   Returns infer_err on any type or usage error.                       *)
(*                                                                      *)
(* The ECall case uses an inline local fixpoint to process the argument  *)
(* list without requiring a mutual fixpoint (which complicates           *)
(* termination checking).                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_core (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match e with

  | EUnit =>
      infer_ok (MkTy UUnrestricted TUnits, Γ)

  | ELit (LInt _) =>
      infer_ok (MkTy UUnrestricted TIntegers, Γ)

  | ELit (LFloat _) =>
      infer_ok (MkTy UUnrestricted TFloats, Γ)

  | ELit (LBool _) =>
      infer_ok (MkTy UUnrestricted TBooleans, Γ)

  | EVar x =>
      match ctx_lookup_b x Γ with
      | None        => infer_err (ErrUnknownVar x)
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else if b
               then infer_err (ErrAlreadyConsumed x)
               else match ctx_consume_b x Γ with
                    | None    => infer_err (ErrUnknownVar x)
                    | Some Γ' => infer_ok (T, Γ')
                    end
      end

  | EFn fname =>
      match lookup_fn_b fname fenv with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Γ)
          else infer_err ErrNotImplemented
      end

  | EMakeClosure fname captures =>
      match lookup_fn_b fname fenv with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_ctx
                  (empty_global_env fenv) Ω Γ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Γ)
          | infer_err err => infer_err err
          end
      end

  | EPlace _ => infer_err ErrNotImplemented

  | EStruct _ _ _ _ => infer_err ErrNotImplemented
  | EEnum _ _ _ _ _ => infer_err ErrNotImplemented
  | EMatch _ _ => infer_err ErrNotImplemented

  | ELet m x T e1 e2 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (T1, Γ1) =>
          if ty_compatible_b Ω T1 T then
            match infer_core fenv Ω n (ctx_add_b x T m Γ1) e2 with
            | infer_err err          => infer_err err
            | infer_ok (T2, Γ2) =>
                if ctx_check_ok x T Γ2
                then infer_ok (T2, ctx_remove_b x Γ2)
                else infer_err ErrContextCheckFailed
            end
          else infer_err (compatible_error T1 T)
      end

  | EDrop e1 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err          => infer_err err
      | infer_ok (_, Γ') => infer_ok (MkTy UUnrestricted TUnits, Γ')
      end

  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None              => infer_err (ErrUnknownVar x)
      | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | None => infer_err (ErrUnknownVar x)
          | Some MImmutable => infer_err (ErrNotMutable x)
          | Some MMutable =>
              match infer_core fenv Ω n Γ e_new with
              | infer_err err            => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_x
                  then infer_ok (T_x, Γ')
                  else infer_err (compatible_error T_new T_x)
              end
          end
      end

  (* *p <- e_new where p : &mut T: write through mutable reference, return old T *)
  | EReplace (PDeref p) e_new =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              match infer_core fenv Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_inner
                  then infer_ok (T_inner, Γ')
                  else infer_err (compatible_error T_new T_inner)
              end
          | c => infer_err (ErrNotAReference c)
          end
      end

  | EReplace (PField _ _) _ => infer_err ErrNotImplemented

  | EAssign (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | None => infer_err (ErrUnknownVar x)
          | Some MImmutable => infer_err (ErrNotMutable x)
          | Some MMutable =>
              if usage_eqb (ty_usage T_x) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_x) UAffine)
              else
                match infer_core fenv Ω n Γ e_new with
                | infer_err err => infer_err err
                | infer_ok (T_new, Γ') =>
                    if ty_compatible_b Ω T_new T_x
                    then infer_ok (MkTy UUnrestricted TUnits, Γ')
                    else infer_err (compatible_error T_new T_x)
                end
          end
      end

  (* *p = e_new where p : &mut T (non-linear): assign through mutable reference, return unit *)
  | EAssign (PDeref p) e_new =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              if usage_eqb (ty_usage T_inner) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_inner) UAffine)
              else
                match infer_core fenv Ω n Γ e_new with
                | infer_err err => infer_err err
	                | infer_ok (T_new, Γ') =>
	                    if ty_compatible_b Ω T_new T_inner
	                    then infer_ok (MkTy UUnrestricted TUnits, Γ')
	                    else infer_err (compatible_error T_new T_inner)
	                end
	          | c => infer_err (ErrNotAReference c)
	          end
      end

  | EAssign (PField _ _) _ => infer_err ErrNotImplemented

  | ECall fname args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
	                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
				                          end
			                          end
	            end
		                                  in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end

  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrArityMismatch
      end

  | ECallExpr callee args =>
      match infer_core fenv Ω n Γ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Γc) =>
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | []      => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core fenv Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
	              | TForall m bounds body =>
	                  match ty_core body with
	                  | TFn param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ =>
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_ty ret_open || contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | TClosure env_lt param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ0 =>
                          let σ := complete_bound_sigma_with_vars n σ0 in
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let env_open := open_bound_lifetime σ env_lt in
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_lifetime env_open ||
                                 contains_lbound_ty ret_open ||
                                 contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | c => infer_err (ErrNotAFunction c)
              end
          end
      end

  | ELetInfer m x e1 e2 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          match infer_core fenv Ω n (ctx_add_b x T1 m Γ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Γ2) =>
              if ctx_check_ok x T1 Γ2
              then infer_ok (T2, ctx_remove_b x Γ2)
              else infer_err ErrContextCheckFailed
          end
      end

  | EIf e1 e2 e3 =>
      match infer_core fenv Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Γ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans then
            match infer_core fenv Ω n Γ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Γ2) =>
                match infer_core fenv Ω n Γ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Γ3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3) then
                      match ctx_merge Γ2 Γ3 with
                      | None    => infer_err ErrContextCheckFailed
                      | Some Γ4 =>
                          infer_ok (MkTy (usage_max (ty_usage T2) (ty_usage T3))
                                         (ty_core T2), Γ4)
                      end
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end

  | EBorrow rk (PVar x) =>
      match ctx_lookup_b x Γ with
      | None              => infer_err (ErrUnknownVar x)
      | Some (_, true)    => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match rk with
          | RUnique =>
              (* &mut requires a mutable binding *)
              match ctx_lookup_mut_b x Γ with
              | Some MMutable =>
                  infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_x), Γ)
              | _ => infer_err (ErrImmutableBorrow x)
              end
          | RShared =>
              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_x), Γ)
          end
      end

  (* &*p (shared re-borrow): p has &T or &mut T, produce &T *)
  | EBorrow RShared (PDeref p) =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ _ T_inner =>
              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_inner), Γ)
          | c => infer_err (ErrNotAReference c)
          end
      end

  (* &mut *p (mutable re-borrow): p must have &mut T *)
  | EBorrow RUnique (PDeref p) =>
      match infer_place Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_inner), Γ)
          | c => infer_err (ErrNotAReference c)
          end
      end

  | EBorrow _ (PField _ _) => infer_err ErrNotImplemented

  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place Γ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core fenv Ω n Γ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Γ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  (* Move-out through a reference is forbidden;
                     only UUnrestricted inner types may be read via deref *)
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end

  end.

Fixpoint infer_core_env_fuel (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit =>
      infer_ok (MkTy UUnrestricted TUnits, Γ)
  | ELit (LInt _) =>
      infer_ok (MkTy UUnrestricted TIntegers, Γ)
  | ELit (LFloat _) =>
      infer_ok (MkTy UUnrestricted TFloats, Γ)
  | ELit (LBool _) =>
      infer_ok (MkTy UUnrestricted TBooleans, Γ)
  | EVar x =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, b) =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else if b
               then infer_err (ErrAlreadyConsumed x)
               else match ctx_consume_b x Γ with
                    | Some Γ' => infer_ok (T, Γ')
                    | None => infer_err (ErrUnknownVar x)
                    end
      end
  | EPlace p =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          if usage_eqb (ty_usage T) UUnrestricted
          then infer_ok (T, Γ)
          else match p with
               | PVar x =>
                   match ctx_consume_b x Γ with
                   | Some Γ' => infer_ok (T, Γ')
                   | None => infer_err (ErrUnknownVar x)
                   end
               | PField q _ =>
                   match ctx_consume_b (place_name q) Γ with
                   | Some Γ' => infer_ok (T, Γ')
                   | None => infer_err (ErrUnknownVar (place_name q))
                   end
               | PDeref _ => infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
               end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Γ)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_ctx env Ω Γ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Γ)
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Γ0 : ctx) (defs : list field_def)
                              : infer_result ctx :=
                            match defs with
                            | [] => infer_ok Γ0
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_fuel fuel' env Ω n Γ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Γ1) =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then go Γ1 rest
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Γ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok Γ' => infer_ok (instantiate_struct_ty s lts args, Γ')
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Γ0 : ctx) (fields : list Ty) (es : list expr)
                      : infer_result ctx :=
                    match fields, es with
                    | [], [] => infer_ok Γ0
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_fuel fuel' env Ω n Γ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Γ1) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then go Γ1 fields' es'
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Γ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok Γ' => infer_ok (instantiate_enum_ty edef lts args, Γ')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_fuel fuel' env Ω n Γ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Γ1) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else
                    match check_struct_bounds env (enum_bounds edef) args with
                    | Some err => infer_err err
                    | None =>
                        match first_duplicate_branch branches with
                        | Some name => infer_err (ErrDuplicateVariant name)
                        | None =>
                            match first_unknown_variant_branch branches (enum_variants edef) with
                            | Some name => infer_err (ErrVariantNotFound name)
                            | None =>
                                match first_unsupported_match_payload branches
                                        (enum_variants edef) with
                                | Some name => infer_err (ErrMatchPayloadUnsupported name)
                                | None =>
                                match first_missing_variant_branch (enum_variants edef) branches with
                                | Some name => infer_err (ErrMissingVariant name)
                                | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result (Ty * list ctx * list Ty) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Γ1
                                                  then
                                                  match infer_core_env_fuel fuel' env Ω n
                                                          (ctx_add_params ps Γ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Γ_branch_payload) =>
                                                      if ctx_check_ok_params ps Γ_branch_payload
                                                      then infer_ok
                                                        (T_branch, ctx_remove_params ps Γ_branch_payload)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Γ_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result (list ctx * list Ty) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Γ0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Γs, Ts) =>
                                                                    infer_ok (Γ0 :: Γs, T0 :: Ts)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                      end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Γs, Ts) =>
                                                    infer_ok (T_branch, Γ_branch :: Γs, Ts)
                                                end
                                            end
                                        end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Γ_head :: Γ_tail, Ts_tail) =>
                                      match ctx_merge_many Γ_head Γ_tail with
	                                      | Some Γ_out =>
	                                          infer_ok
	                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
	                                                  (ty_core T_head), Γ_out)
	                                      | None => infer_err ErrContextCheckFailed
	                                      end
	                                  | infer_ok (_, [], _) => infer_err ErrContextCheckFailed
	                                  end
	                                end
	                            end
		                        end
		                  end
		                  end
			              end
			          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_fuel fuel' env Ω n (ctx_add_b x T m Γ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Γ2) =>
                   if ctx_check_ok x T Γ2
                   then infer_ok (T2, ctx_remove_b x Γ2)
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Γ1) =>
          match infer_core_env_fuel fuel' env Ω n (ctx_add_b x T1 m Γ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Γ2) =>
              if ctx_check_ok x T1 Γ2
              then infer_ok (T2, ctx_remove_b x Γ2)
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Γ') => infer_ok (MkTy UUnrestricted TUnits, Γ')
      end
  | EReplace (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | Some MMutable =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_x
                  then infer_ok (T_x, Γ')
                  else infer_err (compatible_error T_new T_x)
              end
          | Some MImmutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | EReplace (PDeref p) e_new =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_inner
                  then infer_ok (T_inner, Γ')
                  else infer_err (compatible_error T_new T_inner)
              end
          | c => infer_err (ErrNotAReference c)
          end
      end
  | EReplace (PField p field) e_new =>
      match infer_place_env env Γ (PField p field) with
      | infer_err err => infer_err err
      | infer_ok T_field =>
          match ctx_lookup_mut_b (place_name p) Γ with
          | Some MMutable =>
              match infer_core_env_fuel fuel' env Ω n Γ e_new with
              | infer_err err => infer_err err
              | infer_ok (T_new, Γ') =>
                  if ty_compatible_b Ω T_new T_field
                  then infer_ok (T_field, Γ')
                  else infer_err (compatible_error T_new T_field)
              end
          | Some MImmutable => infer_err (ErrNotMutable (place_name p))
          | None => infer_err (ErrUnknownVar (place_name p))
          end
      end
  | EAssign (PVar x) e_new =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T_x, false) =>
          match ctx_lookup_mut_b x Γ with
          | Some MMutable =>
              if usage_eqb (ty_usage T_x) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_x) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_x
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_x)
                   end
          | Some MImmutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | EAssign (PDeref p) e_new =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match ty_core T_p with
          | TRef _ RUnique T_inner =>
              if usage_eqb (ty_usage T_inner) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_inner) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_inner
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_inner)
                   end
          | c => infer_err (ErrNotAReference c)
          end
      end
  | EAssign (PField p field) e_new =>
      match infer_place_env env Γ (PField p field) with
      | infer_err err => infer_err err
      | infer_ok T_field =>
          match ctx_lookup_mut_b (place_name p) Γ with
          | Some MMutable =>
              if usage_eqb (ty_usage T_field) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_field) UAffine)
              else match infer_core_env_fuel fuel' env Ω n Γ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Γ') =>
                       if ty_compatible_b Ω T_new T_field
                       then infer_ok (MkTy UUnrestricted TUnits, Γ')
                       else infer_err (compatible_error T_new T_field)
                   end
          | Some MImmutable => infer_err (ErrNotMutable (place_name p))
          | None => infer_err (ErrUnknownVar (place_name p))
          end
      end
  | EBorrow rk p =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match rk with
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Γ)
          | RUnique =>
              match ctx_lookup_mut_b (place_name p) Γ with
              | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Γ)
              | Some MImmutable => infer_err (ErrImmutableBorrow (place_name p))
              | None => infer_err (ErrUnknownVar (place_name p))
              end
          end
      end
  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place_env env Γ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core_env_fuel fuel' env Ω n Γ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Γ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Γ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_fuel fuel' env Ω n Γ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Γ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_fuel fuel' env Ω n Γ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Γ2) =>
                   match infer_core_env_fuel fuel' env Ω n Γ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Γ3) =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge Γ2 Γ3 with
                            | Some Γ4 =>
                                infer_ok (MkTy (usage_max (ty_usage T2) (ty_usage T3))
                                               (ty_core T2), Γ4)
                            | None => infer_err ErrContextCheckFailed
                            end
                       else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                   end
               end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)), Γ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_fuel fuel' env Ω n Γ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Γc) =>
          let fix collect (Γ0 : ctx) (as_ : list expr)
              : infer_result (list Ty * ctx) :=
            match as_ with
            | [] => infer_ok ([], Γ0)
            | e' :: es =>
                match infer_core_env_fuel fuel' env Ω n Γ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Γ1) =>
                    match collect Γ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
                    end
                end
            end
          in
          match collect Γc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Γ') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Γ')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Γ')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TFn param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ =>
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_ty ret_open || contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | TClosure env_lt param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ0 =>
                          let σ := complete_bound_sigma_with_vars n σ0 in
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let env_open := open_bound_lifetime σ env_lt in
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_lifetime env_open ||
                                 contains_lbound_ty ret_open ||
                                 contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | c => infer_err (ErrNotAFunction c)
	              end
		          end
		      end
		  end
	  end.

Definition sctx_entry : Type := ctx_entry.
Definition sctx : Type := ctx.

Definition sctx_of_ctx (Γ : ctx) : sctx := Γ.
Definition ctx_of_sctx (Σ : sctx) : ctx := Σ.

Definition mutability_eqb (m1 m2 : mutability) : bool :=
  match m1, m2 with
  | MImmutable, MImmutable => true
  | MMutable, MMutable => true
  | _, _ => false
  end.

Fixpoint field_path_eqb (p q : field_path) : bool :=
  match p, q with
  | [], [] => true
  | x :: xs, y :: ys => String.eqb x y && field_path_eqb xs ys
  | _, _ => false
  end.

Fixpoint field_paths_eqb (ps qs : list field_path) : bool :=
  match ps, qs with
  | [], [] => true
  | p :: ps', q :: qs' => field_path_eqb p q && field_paths_eqb ps' qs'
  | _, _ => false
  end.

Definition binding_state_eqb (st1 st2 : binding_state) : bool :=
  Bool.eqb (st_consumed st1) (st_consumed st2) &&
  field_paths_eqb (st_moved_paths st1) (st_moved_paths st2).

Definition sctx_entry_eqb (ce1 ce2 : sctx_entry) : bool :=
  match ce1, ce2 with
  | (x1, T1, st1, m1), (x2, T2, st2, m2) =>
      ident_eqb x1 x2 && ty_eqb T1 T2 &&
      binding_state_eqb st1 st2 && mutability_eqb m1 m2
  end.

Fixpoint sctx_eqb (Σ1 Σ2 : sctx) : bool :=
  match Σ1, Σ2 with
  | [], [] => true
  | ce1 :: rest1, ce2 :: rest2 =>
      sctx_entry_eqb ce1 ce2 && sctx_eqb rest1 rest2
  | _, _ => false
  end.

Definition sctx_lookup (x : ident) (Σ : sctx) : option (Ty * binding_state) :=
  ctx_lookup_state x Σ.

Definition sctx_lookup_mut (x : ident) (Σ : sctx) : option mutability :=
  ctx_lookup_mut x Σ.

Fixpoint check_make_closure_captures_sctx_base
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      match sctx_lookup x Σ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if negb (binding_available_b st [])
          then infer_err (ErrAlreadyConsumed x)
          else
          match sctx_lookup_mut x Σ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if ty_compatible_b Ω T (param_ty cap)
                then
                  match check_make_closure_captures_sctx_base env Ω Σ captures' params' with
                  | infer_ok captured_tys => infer_ok (T :: captured_tys)
                  | infer_err err => infer_err err
                  end
                else infer_err (compatible_error T (param_ty cap))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Fixpoint check_make_closure_captures_sctx
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      match sctx_lookup x Σ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if negb (binding_available_b st [])
          then infer_err (ErrAlreadyConsumed x)
          else
          match sctx_lookup_mut x Σ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if capture_ref_free_ty_b env T
                then
                  if ty_compatible_b Ω T (param_ty cap)
                  then
                    match check_make_closure_captures_sctx env Ω Σ captures' params' with
                    | infer_ok captured_tys => infer_ok (T :: captured_tys)
                    | infer_err err => infer_err err
                    end
                  else infer_err (compatible_error T (param_ty cap))
                else infer_err (ErrNotAReference (ty_core T))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition check_make_closure_captures_sctx_with_env
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (lifetime * list Ty) :=
  match check_make_closure_captures_sctx_base env Ω Σ captures params with
  | infer_ok captured_tys =>
      match infer_closure_env_lifetime Ω captured_tys with
      | infer_ok env_lt =>
          if closure_captures_allowed_b env Ω env_lt captured_tys
          then infer_ok (env_lt, captured_tys)
          else infer_err (ErrNotAReference TUnits)
      | infer_err err => infer_err err
      end
  | infer_err err => infer_err err
  end.

Fixpoint check_make_closure_captures_exact_sctx
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      if match param_mutability cap with MImmutable => false | MMutable => true end
      then infer_err ErrContextCheckFailed
      else
      match sctx_lookup (param_name cap) Σ with
      | Some _ => infer_err ErrContextCheckFailed
      | None =>
      match sctx_lookup x Σ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if st_consumed st
          then infer_err ErrContextCheckFailed
          else
          match st_moved_paths st with
          | _ :: _ => infer_err ErrContextCheckFailed
          | [] =>
          match sctx_lookup_mut x Σ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if capture_ref_free_ty_b env T
                then
                  if ty_eqb T (param_ty cap) &&
                     ty_compatible_b Ω T (param_ty cap)
                  then
                    match check_make_closure_captures_exact_sctx env Ω Σ captures' params' with
                    | infer_ok rest_tys => infer_ok (T :: rest_tys)
                    | infer_err err => infer_err err
                    end
                  else infer_err (compatible_error T (param_ty cap))
                else infer_err (ErrNotAReference (ty_core T))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
          end
      end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Fixpoint check_make_closure_captures_exact_sctx_with_env_base
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (list Ty) :=
  match captures, params with
  | [], [] => infer_ok []
  | x :: captures', cap :: params' =>
      if match param_mutability cap with MImmutable => false | MMutable => true end
      then infer_err ErrContextCheckFailed
      else
      match sctx_lookup (param_name cap) Σ with
      | Some _ => infer_err ErrContextCheckFailed
      | None =>
      match sctx_lookup x Σ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if st_consumed st
          then infer_err ErrContextCheckFailed
          else
          match st_moved_paths st with
          | _ :: _ => infer_err ErrContextCheckFailed
          | [] =>
          match sctx_lookup_mut x Σ with
          | Some MImmutable =>
              if usage_eqb (ty_usage T) UUnrestricted
              then
                if ty_eqb T (param_ty cap) &&
                   ty_compatible_b Ω T (param_ty cap)
                then
                  match check_make_closure_captures_exact_sctx_with_env_base
                          env Ω Σ captures' params' with
                  | infer_ok rest_tys => infer_ok (T :: rest_tys)
                  | infer_err err => infer_err err
                  end
                else infer_err (compatible_error T (param_ty cap))
              else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
          | Some MMutable => infer_err (ErrNotMutable x)
          | None => infer_err (ErrUnknownVar x)
          end
          end
      end
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition check_make_closure_captures_exact_sctx_with_env
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx)
    (captures : list ident) (params : list param)
    : infer_result (lifetime * list Ty) :=
  match check_make_closure_captures_exact_sctx_with_env_base
          env Ω Σ captures params with
  | infer_ok captured_tys =>
      match infer_closure_env_lifetime Ω captured_tys with
      | infer_ok env_lt =>
          if closure_captures_allowed_b env Ω env_lt captured_tys
          then infer_ok (env_lt, captured_tys)
          else infer_err (ErrNotAReference TUnits)
      | infer_err err => infer_err err
      end
  | infer_err err => infer_err err
  end.

Definition sctx_add (x : ident) (T : Ty) (m : mutability) (Σ : sctx) : sctx :=
  ctx_add x T m Σ.

Definition sctx_remove (x : ident) (Σ : sctx) : sctx :=
  ctx_remove x Σ.

Definition sctx_update_state (x : ident) (f : binding_state -> binding_state) (Σ : sctx)
    : option sctx :=
  ctx_update_state x f Σ.

Fixpoint prefix_obligation_paths (prefix : field_path) (paths : list field_path)
    : list field_path :=
  match paths with
  | [] => []
  | p :: rest => (prefix ++ p) :: prefix_obligation_paths prefix rest
  end.

Fixpoint linear_obligation_paths_fuel (fuel : nat) (env : global_env) (T : Ty)
    {struct fuel} : list field_path :=
  match ty_usage T with
  | ULinear =>
      match ty_core T with
      | TStruct sname lts args =>
          match fuel with
          | O => [[]]
          | S fuel' =>
              match lookup_struct sname env with
              | Some s =>
                  if Nat.eqb (List.length lts) (struct_lifetimes s) &&
                     Nat.eqb (List.length args) (struct_type_params s)
                  then
                    let fix go (fields : list field_def) : list field_path :=
                      match fields with
                      | [] => []
                      | f :: rest =>
                          prefix_obligation_paths [field_name f]
                            (linear_obligation_paths_fuel fuel' env
                              (instantiate_struct_field_ty lts args f)) ++ go rest
                      end
                    in
                    match go (struct_fields s) with
                    | [] => [[]]
                    | obligations => obligations
                    end
                  else [[]]
              | None => [[]]
              end
          end
      | _ => [[]]
      end
  | _ => []
  end.

Definition linear_obligation_paths (env : global_env) (T : Ty) : list field_path :=
  linear_obligation_paths_fuel (S (List.length (env_structs env) + ty_depth T)) env T.

Definition moved_path_satisfies_obligation_b
    (moved_paths : list field_path) (obligation : field_path) : bool :=
  existsb (fun moved => path_prefix_b moved obligation) moved_paths.

Fixpoint moved_paths_satisfy_obligations_b
    (moved_paths obligations : list field_path) : bool :=
  match obligations with
  | [] => true
  | obligation :: rest =>
      moved_path_satisfies_obligation_b moved_paths obligation &&
      moved_paths_satisfy_obligations_b moved_paths rest
  end.

Definition linear_scope_ok_b (env : global_env) (T : Ty) (st : binding_state) : bool :=
  st_consumed st ||
  moved_paths_satisfy_obligations_b
    (st_moved_paths st) (linear_obligation_paths env T).

Definition sctx_check_ok (env : global_env) (x : ident) (T : Ty) (Σ : sctx) : bool :=
  match ty_usage T with
  | ULinear =>
      match sctx_lookup x Σ with
      | Some (_, st) => linear_scope_ok_b env T st
      | None => false
      end
  | _ => true
  end.

Fixpoint params_ok_sctx_b (env : global_env) (ps : list param) (Σ : sctx) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      sctx_check_ok env (param_name p) (param_ty p) Σ &&
      params_ok_sctx_b env rest Σ
  end.

Definition params_ok_env_b (env : global_env) (ps : list param) (Γ : ctx) : bool :=
  params_ok_sctx_b env ps (sctx_of_ctx Γ).

Definition sctx_add_params (ps : list param) (Σ : sctx) : sctx :=
  ctx_add_params ps Σ.

Definition sctx_remove_params (ps : list param) (Σ : sctx) : sctx :=
  ctx_remove_params ps Σ.

Definition sctx_path_available (Σ : sctx) (x : ident) (p : field_path) : infer_result unit :=
  match sctx_lookup x Σ with
  | None => infer_err (ErrUnknownVar x)
  | Some (_, st) =>
      if binding_available_b st p
      then infer_ok tt
      else infer_err (ErrAlreadyConsumed x)
  end.

Definition sctx_consume_path (Σ : sctx) (x : ident) (p : field_path) : infer_result sctx :=
  match sctx_path_available Σ x p with
  | infer_err err => infer_err err
  | infer_ok _ =>
      match sctx_update_state x (state_consume_path p) Σ with
      | Some Σ' => infer_ok Σ'
      | None => infer_err (ErrUnknownVar x)
      end
  end.

Definition sctx_restore_path (Σ : sctx) (x : ident) (p : field_path) : infer_result sctx :=
  match sctx_update_state x (state_restore_path p) Σ with
  | Some Σ' => infer_ok Σ'
  | None => infer_err (ErrUnknownVar x)
  end.

Fixpoint infer_place_sctx (env : global_env) (Σ : sctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match sctx_lookup x Σ with
      | None => infer_err (ErrUnknownVar x)
      | Some (T, st) =>
          if binding_available_b st []
          then infer_ok T
          else infer_err (ErrAlreadyConsumed x)
      end
  | PDeref q =>
      match infer_place_sctx env Σ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField q field =>
      match infer_place_env env (ctx_of_sctx Σ) q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TStruct sname lts args =>
              match lookup_struct sname env with
              | None => infer_err (ErrStructNotFound sname)
              | Some s =>
                  match lookup_field field (struct_fields s) with
                  | None => infer_err (ErrFieldNotFound field)
                  | Some f =>
                      match place_path (PField q field) with
                      | Some (x, path) =>
                          match sctx_path_available Σ x path with
                          | infer_ok _ => infer_ok (instantiate_struct_field_ty lts args f)
                          | infer_err err => infer_err err
                          end
                      | None => infer_ok (instantiate_struct_field_ty lts args f)
                      end
                  end
              end
          | c => infer_err (ErrTypeMismatch c (TStruct "" [] []))
          end
      end
  end.

Fixpoint infer_place_type_sctx (env : global_env) (Σ : sctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match sctx_lookup x Σ with
      | Some (T, _) => infer_ok T
      | None => infer_err (ErrUnknownVar x)
      end
  | PDeref q =>
      match infer_place_type_sctx env Σ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField q field =>
      match infer_place_type_sctx env Σ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TStruct sname lts args =>
              match lookup_struct sname env with
              | None => infer_err (ErrStructNotFound sname)
              | Some s =>
                  match lookup_field field (struct_fields s) with
                  | None => infer_err (ErrFieldNotFound field)
                  | Some f => infer_ok (instantiate_struct_field_ty lts args f)
                  end
              end
          | c => infer_err (ErrTypeMismatch c (TStruct "" [] []))
          end
      end
  end.

Fixpoint place_under_unique_ref_b (env : global_env) (Σ : sctx) (p : place) : bool :=
  match p with
  | PVar _ => false
  | PField q _ => place_under_unique_ref_b env Σ q
  | PDeref q =>
      match infer_place_sctx env Σ q with
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ RUnique _ => true
          | _ => false
          end
      | infer_err _ => false
      end
  end.

Fixpoint writable_place_b (env : global_env) (Σ : sctx) (p : place) : bool :=
  match p with
  | PVar x =>
      match sctx_lookup_mut x Σ with
      | Some MMutable => true
      | _ => false
      end
  | PDeref q =>
      match infer_place_sctx env Σ q with
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ RUnique _ => true
          | _ => false
          end
      | infer_err _ => false
      end
  | PField q field =>
      if writable_place_b env Σ q
      then
        match infer_place_type_sctx env Σ q with
        | infer_ok Tq =>
            match ty_core Tq with
            | TStruct sname _ _ =>
                match lookup_struct sname env with
                | Some s =>
                    match lookup_field field (struct_fields s) with
                    | Some f =>
                        match field_mutability f with
                        | MMutable => true
                        | MImmutable => false
                        end
                    | None => false
                    end
                | None => false
                end
            | _ => false
            end
        | infer_err _ => false
        end
      else false
  end.

Definition consume_place_value (env : global_env) (Σ : sctx) (p : place) (T : Ty)
    : infer_result sctx :=
  if usage_eqb (ty_usage T) UUnrestricted
  then infer_ok Σ
  else match place_path p with
       | Some (x, path) => sctx_consume_path Σ x path
       | None => infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
       end.

Fixpoint usage_max_tys (ts : list Ty) : usage :=
  match ts with
  | [] => UUnrestricted
  | t :: rest => usage_max (ty_usage t) (usage_max_tys rest)
  end.

Definition instantiate_struct_instance_ty
    (s : struct_def) (lifetime_args : list lifetime) (type_args : list Ty) : Ty :=
  MkTy (usage_max_tys (map (instantiate_struct_field_ty lifetime_args type_args) (struct_fields s)))
       (TStruct (struct_name s) lifetime_args type_args).

Fixpoint auto_drop_paths_for_ty_fuel
    (fuel : nat) (env : global_env) (T : Ty) (prefix : field_path)
    {struct fuel} : list field_path :=
  match ty_usage T with
  | UAffine =>
      match ty_core T with
      | TStruct sname lts args =>
          match fuel with
          | O => [prefix]
          | S fuel' =>
              match lookup_struct sname env with
              | Some s =>
                  let fix go (fields : list field_def) : list field_path :=
                    match fields with
                    | [] => []
                    | f :: rest =>
                        auto_drop_paths_for_ty_fuel fuel' env
                          (instantiate_struct_field_ty lts args f)
                          (prefix ++ [field_name f]) ++ go rest
                    end
                  in go (struct_fields s)
              | None => [prefix]
              end
          end
      | _ => [prefix]
      end
  | _ => []
  end.

Definition auto_drop_paths_for_ty
    (env : global_env) (T : Ty) : list field_path :=
  auto_drop_paths_for_ty_fuel
    (S (List.length (env_structs env) + ty_depth T)) env T [].

Fixpoint filter_live_drop_paths
    (st : binding_state) (paths : list field_path) : list field_path :=
  match paths with
  | [] => []
  | p :: rest =>
      if binding_available_b st p
      then p :: filter_live_drop_paths st rest
      else filter_live_drop_paths st rest
  end.

Definition auto_drop_live_paths
    (env : global_env) (x : ident) (T : Ty) (Σ : sctx)
    : list field_path :=
  match sctx_lookup x Σ with
  | Some (_, st) => filter_live_drop_paths st (auto_drop_paths_for_ty env T)
  | None => []
  end.

Fixpoint infer_core_env_state_fuel (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ)
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ)
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ)
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ)
  | EVar x =>
      match infer_place_sctx env Σ (PVar x) with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ (PVar x) T with
          | infer_ok Σ' => infer_ok (T, Σ')
          | infer_err err => infer_err err
          end
      end
  | EPlace p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ p T with
          | infer_ok Σ' => infer_ok (T, Σ')
          | infer_err err => infer_err err
          end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ)
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Σ0 : sctx) (defs : list field_def)
                              : infer_result sctx :=
                            match defs with
                            | [] => infer_ok Σ0
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel fuel' env Ω n Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1) =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then go Σ1 rest
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok Σ' => infer_ok (instantiate_struct_instance_ty s lts args, Σ')
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Σ0 : sctx) (fields : list Ty) (es : list expr)
                      : infer_result sctx :=
                    match fields, es with
                    | [], [] => infer_ok Σ0
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel fuel' env Ω n Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then go Σ1 fields' es'
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok Σ' => infer_ok (instantiate_enum_ty edef lts args, Σ')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel fuel' env Ω n Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else match check_struct_bounds env (enum_bounds edef) args with
                  | Some err => infer_err err
                  | None =>
                  match first_duplicate_branch branches with
                  | Some name => infer_err (ErrDuplicateVariant name)
                  | None =>
	                      match first_unknown_variant_branch branches (enum_variants edef) with
	                      | Some name => infer_err (ErrVariantNotFound name)
	                      | None =>
	                          match first_unsupported_match_payload branches
	                                  (enum_variants edef) with
	                          | Some name => infer_err (ErrMatchPayloadUnsupported name)
	                          | None =>
	                          match first_missing_variant_branch (enum_variants edef) branches with
                          | Some name => infer_err (ErrMissingVariant name)
                          | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result (Ty * list sctx * list Ty) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Σ1
                                                  then
                                                  match infer_core_env_state_fuel fuel' env Ω n
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload) =>
                                                      if params_ok_sctx_b env ps Σ_branch_payload
                                                      then infer_ok
                                                        (T_branch, sctx_remove_params ps Σ_branch_payload)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result (list sctx * list Ty) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Σs, Ts) =>
                                                                    infer_ok (Σ0 :: Σs, T0 :: Ts)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts) =>
                                                    infer_ok (T_branch, Σ_branch :: Σs, Ts)
                                                end
                                            end
                                        end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head :: Σ_tail, Ts_tail) =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
                                                  (ty_core T_head), sctx_of_ctx Γ_out)
                                      | None => infer_err ErrContextCheckFailed
                                      end
	                                  | infer_ok (_, [], _) => infer_err ErrContextCheckFailed
	                                  end
	                          end
	                          end
	                      end
                  end
                  end
              end
          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1) =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_state_fuel fuel' env Ω n (sctx_add x T m Σ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2) =>
                   if sctx_check_ok env x T Σ2
                   then infer_ok (T2, sctx_remove x Σ2)
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1) =>
          match infer_core_env_state_fuel fuel' env Ω n (sctx_add x T1 m Σ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Σ2) =>
              if sctx_check_ok env x T1 Σ2
              then infer_ok (T2, sctx_remove x Σ2)
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ') => infer_ok (MkTy UUnrestricted TUnits, Σ')
      end
  | EReplace p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1) =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    match sctx_restore_path Σ1 x path with
                                    | infer_ok Σ2 => infer_ok (T_old, Σ2)
                                    | infer_err err => infer_err err
                                    end
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1) =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (T_old, Σ1)
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EAssign p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          if usage_eqb (ty_usage T_old) ULinear
          then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
          else
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1) =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ => infer_ok (MkTy UUnrestricted TUnits, Σ1)
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1) =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (MkTy UUnrestricted TUnits, Σ1)
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match rk with
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ)
          | RUnique =>
              match place_path p with
              | Some (x, _) =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ)
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              | None =>
                  if place_under_unique_ref_b env Σ p
                  then infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ)
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core_env_state_fuel fuel' env Ω n Σ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Σ') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_state_fuel fuel' env Ω n Σ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2) =>
                   match infer_core_env_state_fuel fuel' env Ω n Σ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Σ3) =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                            | Some Γ4 => infer_ok
                                (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                                 sctx_of_ctx Γ4)
                            | None => infer_err ErrContextCheckFailed
                            end
                       else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                   end
               end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Σ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)), Σ')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_state_fuel fuel' env Ω n Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σc) =>
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx) :=
            match as_ with
            | [] => infer_ok ([], Σ0)
            | e' :: es =>
                match infer_core_env_state_fuel fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
                    end
                end
            end
          in
          match collect Σc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Σ')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
	                      | infer_ok ret => infer_ok (ret, Σ')
                      end
                  | TFn param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ =>
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_ty ret_open || contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Σ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | TClosure env_lt param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ0 =>
                          let σ := complete_bound_sigma_with_vars n σ0 in
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let env_open := open_bound_lifetime σ env_lt in
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_lifetime env_open ||
                                 contains_lbound_ty ret_open ||
                                 contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Σ')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | c => infer_err (ErrNotAFunction c)
              end
          end
      end
  end
  end.

Definition infer_core_env
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  match infer_core_env_state_fuel 10000 env Ω n (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ) => infer_ok (T, ctx_of_sctx Σ)
  | infer_err err => infer_err err
  end.

Fixpoint infer_core_env_state_fuel_elab (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * expr) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ, e)
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ, e)
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ, e)
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ, e)
  | EVar x =>
      match infer_place_sctx env Σ (PVar x) with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ (PVar x) T with
          | infer_ok Σ' => infer_ok (T, Σ', e)
          | infer_err err => infer_err err
          end
      end
  | EPlace p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          match consume_place_value env Σ p T with
          | infer_ok Σ' => infer_ok (T, Σ', e)
          | infer_err err => infer_err err
          end
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ, e)
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ,
                EMakeClosure fname captures)
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Σ0 : sctx) (defs : list field_def)
                              : infer_result (sctx * list (string * expr)) :=
                            match defs with
                            | [] => infer_ok (Σ0, [])
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1, e_field') =>
                                        let T_expected := instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then match go Σ1 rest with
                                             | infer_err err => infer_err err
                                             | infer_ok (Σ2, fields') =>
                                                 infer_ok (Σ2, (field_name f, e_field') :: fields')
                                             end
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok (Σ', fields') =>
                              infer_ok (instantiate_struct_instance_ty s lts args,
                                        Σ',
                                        EStruct sname lts args fields')
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Σ0 : sctx) (fields : list Ty) (es : list expr)
                      : infer_result (sctx * list expr) :=
                    match fields, es with
                    | [], [] => infer_ok (Σ0, [])
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1, e_payload') =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then match go Σ1 fields' es' with
                                 | infer_err err => infer_err err
                                 | infer_ok (Σ2, payloads') =>
                                     infer_ok (Σ2, e_payload' :: payloads')
                                 end
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok (Σ', payloads') =>
                      infer_ok (instantiate_enum_ty edef lts args, Σ',
                        EEnum enum_name variant_name lts args payloads')
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1, scrut') =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  match first_duplicate_branch branches with
                  | Some name => infer_err (ErrDuplicateVariant name)
                  | None =>
	                      match first_unknown_variant_branch branches (enum_variants edef) with
	                      | Some name => infer_err (ErrVariantNotFound name)
	                      | None =>
	                          match first_missing_variant_branch (enum_variants edef) branches with
                          | Some name => infer_err (ErrMissingVariant name)
                          | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result
                                          (Ty * list sctx * list Ty *
                                           list (string * list ident * expr)) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Σ1
                                                  then
                                                  match infer_core_env_state_fuel_elab fuel' env Ω n
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload, e_branch') =>
                                                      if params_ok_sctx_b env ps Σ_branch_payload
                                                      then infer_ok
                                                        (T_branch,
                                                         sctx_remove_params ps Σ_branch_payload,
                                                         e_branch',
                                                         binders)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch, e_branch', binders) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result
                                                        (list sctx * list Ty *
                                                         list (string * list ident * expr)) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0, e0', binders0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_result :=
                                                                  infer_rest T_head rest0 in
                                                                match rest_result with
                                                                | infer_err err => infer_err err
                                                                | infer_ok (Σs, Ts, bs) =>
                                                                    infer_ok
                                                                      (Σ0 :: Σs, T0 :: Ts,
                                                                       (enum_variant_name v0, binders0, e0') :: bs)
                                                                end
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts, bs) =>
                                                    infer_ok
                                                      (T_branch, Σ_branch :: Σs, Ts,
                                                       (enum_variant_name v, binders, e_branch') :: bs)
                                                end
                                            end
                                    end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head :: Σ_tail, Ts_tail, branches') =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
                                                  (ty_core T_head),
                                             sctx_of_ctx Γ_out,
                                             EMatch scrut' branches')
                                      | None => infer_err ErrContextCheckFailed
                                      end
	                                  | infer_ok (_, [], _, _) => infer_err ErrContextCheckFailed
	                                  end
	                          end
	                      end
                  end
              end
          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, e1') =>
          if ty_compatible_b Ω T1 T
          then match infer_core_env_state_fuel_elab fuel' env Ω n (sctx_add x T m Σ1) e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2, e2') =>
                   if sctx_check_ok env x T Σ2
                   then infer_ok (T2, sctx_remove x Σ2, ELet m x T e1' e2')
                   else infer_err ErrContextCheckFailed
               end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, e1') =>
          match infer_core_env_state_fuel_elab fuel' env Ω n (sctx_add x T1 m Σ1) e2 with
          | infer_err err => infer_err err
          | infer_ok (T2, Σ2, e2') =>
              if sctx_check_ok env x T1 Σ2
              then infer_ok (T2, sctx_remove x Σ2, ELet m x T1 e1' e2')
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ', e1') =>
          infer_ok (MkTy UUnrestricted TUnits, Σ', EDrop e1')
      end
  | EReplace p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1, e_new') =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    match sctx_restore_path Σ1 x path with
                                    | infer_ok Σ2 => infer_ok (T_old, Σ2, EReplace p e_new')
                                    | infer_err err => infer_err err
                                    end
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1, e_new') =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (T_old, Σ1, EReplace p e_new')
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EAssign p e_new =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_old =>
          if usage_eqb (ty_usage T_old) ULinear
          then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
          else
          let root := place_name p in
          match place_path p with
          | Some (x, path) =>
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                       | infer_err err => infer_err err
                       | infer_ok (T_new, Σ1, e_new') =>
                           if ty_compatible_b Ω T_new T_old
                           then match sctx_path_available Σ1 x path with
                                | infer_err err => infer_err err
                                | infer_ok _ =>
                                    infer_ok (MkTy UUnrestricted TUnits, Σ1, EAssign p e_new')
                                end
                           else infer_err (compatible_error T_new T_old)
                       end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          | None =>
              if writable_place_b env Σ p
              then match infer_core_env_state_fuel_elab fuel' env Ω n Σ e_new with
                   | infer_err err => infer_err err
                   | infer_ok (T_new, Σ1, e_new') =>
                       if ty_compatible_b Ω T_new T_old
                       then infer_ok (MkTy UUnrestricted TUnits, Σ1, EAssign p e_new')
                       else infer_err (compatible_error T_new T_old)
                   end
              else infer_err (ErrNotMutable root)
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match rk with
          | RShared => infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, e)
          | RUnique =>
              match place_path p with
              | Some (x, _) =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable => infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, e)
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              | None =>
                  if place_under_unique_ref_b env Σ p
                  then infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, e)
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref r =>
      match expr_as_place r with
      | Some p =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_r =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ, EDeref r)
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      | None =>
          match infer_core_env_state_fuel_elab fuel' env Ω n Σ r with
          | infer_err err => infer_err err
          | infer_ok (T_r, Σ', r') =>
              match ty_core T_r with
              | TRef _ _ T_inner =>
                  if usage_eqb (ty_usage T_inner) UUnrestricted
                  then infer_ok (T_inner, Σ', EDeref r')
                  else infer_err (ErrUsageMismatch (ty_usage T_inner) UUnrestricted)
              | c => infer_err (ErrNotAReference c)
              end
          end
      end
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1, e1') =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then match infer_core_env_state_fuel_elab fuel' env Ω n Σ1 e2 with
               | infer_err err => infer_err err
               | infer_ok (T2, Σ2, e2') =>
                   match infer_core_env_state_fuel_elab fuel' env Ω n Σ1 e3 with
                   | infer_err err => infer_err err
                   | infer_ok (T3, Σ3, e3') =>
                       if ty_core_eqb (ty_core T2) (ty_core T3)
                       then match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                            | Some Γ4 => infer_ok
                                (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                                 sctx_of_ctx Γ4,
                                 EIf e1' e2' e3')
                            | None => infer_err ErrContextCheckFailed
                            end
                       else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                   end
               end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok (apply_lt_ty σ (fn_ret fdef), Σ', ECall fname args')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σ args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)),
                           Σ',
                           ECallGeneric fname type_args args')
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | ECallExpr callee args =>
      match infer_core_env_state_fuel_elab fuel' env Ω n Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σc, callee') =>
          let fix collect (Σ0 : sctx) (as_ : list expr)
              : infer_result (list Ty * sctx * list expr) :=
            match as_ with
            | [] => infer_ok ([], Σ0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_elab fuel' env Ω n Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, e_elab) =>
                    match collect Σ1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, es_elab) =>
                        infer_ok (T_e :: tys, Σ2, e_elab :: es_elab)
                    end
                end
            end
          in
          match collect Σc args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', args') =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ', ECallExpr callee' args')
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None => infer_ok (ret, Σ', ECallExpr callee' args')
                  end
              | TTypeForall type_params bounds body =>
                  match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                  | infer_err err => infer_err err
                  | infer_ok ret => infer_ok (ret, Σ', ECallExpr callee' args')
                  end
              | TForall m bounds body =>
                  match ty_core body with
                  | TFn param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ =>
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_ty ret_open || contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Σ', ECallExpr callee' args')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | TClosure env_lt param_tys ret =>
                      match build_bound_sigma (repeat None m) arg_tys param_tys with
                      | None => infer_err ErrLifetimeConflict
                      | Some σ0 =>
                          let σ := complete_bound_sigma_with_vars n σ0 in
                          let param_tys_open := map (open_bound_ty σ) param_tys in
                          match check_arg_tys Ω arg_tys param_tys_open with
                          | Some err => infer_err err
                          | None =>
                              let env_open := open_bound_lifetime σ env_lt in
                              let ret_open := open_bound_ty σ ret in
                              let bounds_open := open_bound_outlives σ bounds in
                              if contains_lbound_lifetime env_open ||
                                 contains_lbound_ty ret_open ||
                                 contains_lbound_outlives bounds_open
                              then infer_err ErrHrtUnresolvedBound
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Σ', ECallExpr callee' args')
                                   else infer_err ErrHrtBoundUnsatisfied
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
                  end
              | c => infer_err (ErrNotAFunction c)
              end
          end
      end
  end
  end.

Definition infer_core_env_elab
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * expr) :=
  match infer_core_env_state_fuel_elab 10000 env Ω n (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, e') => infer_ok (T, ctx_of_sctx Σ, e')
  | infer_err err => infer_err err
  end.

Fixpoint root_set_eqb (a b : root_set) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => root_atom_eqb x y && root_set_eqb xs ys
  | _, _ => false
  end.

Fixpoint root_env_eqb (R1 R2 : root_env) : bool :=
  match R1, R2 with
  | [], [] => true
  | (x1, roots1) :: rest1, (x2, roots2) :: rest2 =>
      ident_eqb x1 x2 && root_set_eqb roots1 roots2 && root_env_eqb rest1 rest2
  | _, _ => false
  end.

Definition roots_exclude_b (x : ident) (roots : root_set) : bool :=
  negb (existsb (root_atom_eqb (RStore x)) roots).

Fixpoint root_env_excludes_b (x : ident) (R : root_env) : bool :=
  match R with
  | [] => true
  | (y, roots) :: rest =>
      (if ident_eqb x y then true else roots_exclude_b x roots) &&
      root_env_excludes_b x rest
  end.

Fixpoint roots_exclude_params_b (ps : list param) (roots : root_set) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      roots_exclude_b (param_name p) roots &&
      roots_exclude_params_b rest roots
  end.

Fixpoint root_env_excludes_params_b (ps : list param) (R : root_env) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      root_env_excludes_b (param_name p) R &&
      root_env_excludes_params_b rest R
  end.

Fixpoint root_env_add_params_roots_same
    (ps : list param) (roots : root_set) (R : root_env) : root_env :=
  match ps with
  | [] => R
  | p :: rest =>
      root_env_add (param_name p) roots
        (root_env_add_params_roots_same rest roots R)
  end.

Fixpoint root_env_remove_match_params (ps : list param) (R : root_env) : root_env :=
  match ps with
  | [] => R
  | p :: rest => root_env_remove_match_params rest (root_env_remove (param_name p) R)
  end.

Fixpoint root_env_lookup_params_none_b (ps : list param) (R : root_env) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      match root_env_lookup (param_name p) R with
      | Some _ => false
      | None => root_env_lookup_params_none_b rest R
      end
  end.

Lemma ident_in_b_false_not_in :
  forall x xs,
    ident_in_b x xs = false ->
    ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; intros Hfalse Hin; simpl in *.
  - contradiction.
  - apply orb_false_iff in Hfalse as [Hneq Hrest].
    destruct Hin as [Heq | Hin].
    + subst. rewrite ident_eqb_refl in Hneq. discriminate.
    + eapply IH; eauto.
Qed.

Lemma ident_nodup_b_sound :
  forall xs,
    ident_nodup_b xs = true ->
    NoDup xs.
Proof.
  induction xs as [| x xs IH]; intros Hnodup; simpl in *.
  - constructor.
  - apply andb_true_iff in Hnodup as [Hnotin Htail].
    constructor.
    + apply ident_in_b_false_not_in. apply negb_true_iff. exact Hnotin.
    + apply IH. exact Htail.
Qed.

Lemma params_names_nodup_b_sound :
  forall ps,
    params_names_nodup_b ps = true ->
    NoDup (ctx_names (params_ctx ps)).
Proof.
  intros ps H.
  unfold params_names_nodup_b in H.
  apply ident_nodup_b_sound. exact H.
Qed.

Lemma root_env_lookup_add_params_roots_same_none :
  forall ps roots R x,
    root_env_lookup x R = None ->
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_add_params_roots_same ps roots R) = None.
Proof.
  induction ps as [| p ps IH]; intros roots R x Hlookup Hnotin; simpl in *.
  - exact Hlookup.
  - destruct p as [m y T]. simpl in *.
    destruct (ident_eqb x y) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst.
      exfalso. apply Hnotin. left. reflexivity.
    + apply IH.
      * exact Hlookup.
      * intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_add_params_roots_same_no_shadow :
  forall ps roots R,
    root_env_no_shadow R ->
    root_env_lookup_params_none_b ps R = true ->
    params_names_nodup_b ps = true ->
    root_env_no_shadow (root_env_add_params_roots_same ps roots R).
Proof.
  induction ps as [| p ps IH]; intros roots R Hns Hfresh Hnodup; simpl in *.
  - exact Hns.
  - destruct p as [m x T]. simpl in *.
    destruct (root_env_lookup x R) as [existing |] eqn:Hlookup; try discriminate.
    apply andb_true_iff in Hnodup as [Hnotin_b Hnodup_tail].
    apply root_env_no_shadow_add.
    + apply IH.
      * exact Hns.
      * exact Hfresh.
      * exact Hnodup_tail.
    + apply root_env_lookup_add_params_roots_same_none.
      * exact Hlookup.
      * apply ident_in_b_false_not_in. apply negb_true_iff. exact Hnotin_b.
Qed.

Lemma root_env_remove_match_params_no_shadow :
  forall ps R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_remove_match_params ps R).
Proof.
  induction ps as [| p ps IH]; intros R Hns; simpl.
  - exact Hns.
  - apply IH. apply root_env_no_shadow_remove. exact Hns.
Qed.

Lemma root_env_lookup_params_none_b_instantiate_equiv :
  forall ps rho R R0,
    root_env_lookup_params_none_b ps R = true ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    root_env_lookup_params_none_b ps R0 = true.
Proof.
  induction ps as [| p ps IH]; intros rho R R0 Hfresh Heq; simpl in *.
  - reflexivity.
  - destruct p as [m x T]. simpl in *.
    destruct (root_env_lookup x R) as [roots |] eqn:Hlookup; try discriminate.
    assert (Hlookup_inst : root_env_lookup x (root_env_instantiate rho R) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup. }
    assert (Hlookup_R0 : root_env_lookup x R0 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    rewrite Hlookup_R0.
    eapply IH; eassumption.
Qed.

Lemma root_env_add_params_roots_same_instantiate_equiv :
  forall ps rho roots roots0 R R0,
    root_set_equiv roots0 (root_set_instantiate rho roots) ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    root_env_equiv
      (root_env_add_params_roots_same ps roots0 R0)
      (root_env_instantiate rho
        (root_env_add_params_roots_same ps roots R)).
Proof.
  induction ps as [| p ps IH]; intros rho roots roots0 R R0 Hroots HR; simpl.
  - exact HR.
  - destruct p as [m x T]. simpl.
    eapply root_env_equiv_trans.
    + apply root_env_equiv_add.
      * exact Hroots.
      * apply IH.
        -- exact Hroots.
        -- exact HR.
    + apply root_env_equiv_sym.
      apply root_env_instantiate_add_equiv.
      * apply root_set_equiv_refl.
      * apply root_env_equiv_refl.
Qed.

Lemma root_env_remove_match_params_instantiate_equiv :
  forall ps rho R R0,
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    root_env_equiv
      (root_env_remove_match_params ps R0)
      (root_env_instantiate rho (root_env_remove_match_params ps R)).
Proof.
  induction ps as [| p ps IH]; intros rho R R0 HnsR HnsR0 HR; simpl.
  - exact HR.
  - destruct p as [m x T]. simpl.
    apply IH.
    + apply root_env_no_shadow_remove. exact HnsR.
    + apply root_env_no_shadow_remove. exact HnsR0.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR0.
        -- apply root_env_instantiate_no_shadow. exact HnsR.
        -- exact HR.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact HnsR.
        -- exact HnsR.
        -- apply root_env_equiv_refl.
Qed.

Fixpoint preservation_ready_expr_b (e : expr) : bool :=
  match e with
  | EUnit => true
  | ELit _ => true
  | EVar _ => true
  | EFn _ => true
  | EMakeClosure _ _ => false
  | EPlace p =>
      match place_path p with
      | Some _ => true
      | None => false
      end
  | EBorrow _ p =>
      match place_path p with
      | Some _ => true
      | None => false
      end
  | EStruct _ _ _ fields =>
      let fix go (fields0 : list (string * expr)) : bool :=
        match fields0 with
        | [] => true
        | (_, e_field) :: rest =>
            preservation_ready_expr_b e_field && go rest
        end
      in go fields
  | EEnum _ _ _ _ payloads =>
      forallb preservation_ready_expr_b payloads
  | EMatch scrut branches =>
      preservation_ready_expr_b scrut &&
      let fix go (branches0 : list (string * list ident * expr)) : bool :=
        match branches0 with
        | [] => true
        | (_, binders, e_branch) :: rest =>
            match binders with
            | [] => preservation_ready_expr_b e_branch && go rest
            | _ :: _ => false
            end
        end
      in go branches
  | EDrop e1 => preservation_ready_expr_b e1
  | EAssign p e_new =>
      match place_path p with
      | Some _ => preservation_ready_expr_b e_new
      | None => false
      end
  | EReplace p e_new =>
      match place_path p with
      | Some _ => preservation_ready_expr_b e_new
      | None => false
      end
  | EIf e1 e2 e3 =>
      preservation_ready_expr_b e1 &&
      preservation_ready_expr_b e2 &&
      preservation_ready_expr_b e3
  | ECall _ _ => false
  | ECallGeneric _ _ _ => false
  | ECallExpr _ _ => false
  | ELet _ _ _ _ _ => false
  | ELetInfer _ _ _ _ => false
  | EDeref _ => false
  end
.

Definition preservation_ready_args_b (args : list expr) : bool :=
  forallb preservation_ready_expr_b args.

Definition preservation_ready_fields_b (fields : list (string * expr)) : bool :=
  let fix go (fields0 : list (string * expr)) : bool :=
    match fields0 with
    | [] => true
    | (_, e) :: rest =>
        preservation_ready_expr_b e && go rest
    end
  in go fields.

Fixpoint provenance_ready_expr_b (e : expr) : bool :=
  match e with
  | EUnit => true
  | ELit _ => true
  | EVar _ => true
  | EFn _ => true
  | EMakeClosure _ _ => false
  | EPlace p =>
      match place_path p with
      | Some _ => true
      | None => false
      end
  | EBorrow _ p =>
      match place_path p with
      | Some _ => true
      | None => false
      end
  | EStruct _ _ _ fields =>
      let fix go (fields0 : list (string * expr)) : bool :=
        match fields0 with
        | [] => true
        | (_, e_field) :: rest =>
            provenance_ready_expr_b e_field && go rest
        end
      in go fields
  | EEnum _ _ _ _ payloads =>
      forallb provenance_ready_expr_b payloads
  | EMatch scrut branches =>
      provenance_ready_expr_b scrut &&
      let fix go (branches0 : list (string * list ident * expr)) : bool :=
        match branches0 with
        | [] => true
        | (_, _, e_branch) :: rest =>
            provenance_ready_expr_b e_branch && go rest
        end
      in go branches
  | ELet _ _ _ e1 e2 =>
      provenance_ready_expr_b e1 && provenance_ready_expr_b e2
  | ELetInfer _ _ e1 e2 =>
      provenance_ready_expr_b e1 && provenance_ready_expr_b e2
  | EDrop e1 => provenance_ready_expr_b e1
  | EAssign p e_new =>
      match place_path p with
      | Some _ => provenance_ready_expr_b e_new
      | None => false
      end
  | EReplace p e_new =>
      match place_path p with
      | Some _ => provenance_ready_expr_b e_new
      | None => false
      end
  | EIf e1 e2 e3 =>
      provenance_ready_expr_b e1 &&
      provenance_ready_expr_b e2 &&
      provenance_ready_expr_b e3
  | ECall _ _ => false
  | ECallGeneric _ _ _ => false
  | ECallExpr _ _ => false
  | EDeref (EBorrow _ p) =>
      match place_path p with
      | Some _ => true
      | None => false
      end
  | EDeref _ => false
  end
.

Definition provenance_ready_args_b (args : list expr) : bool :=
  forallb provenance_ready_expr_b args.

Definition provenance_ready_fields_b (fields : list (string * expr)) : bool :=
  let fix go (fields0 : list (string * expr)) : bool :=
    match fields0 with
    | [] => true
    | (_, e) :: rest =>
        provenance_ready_expr_b e && go rest
    end
  in go fields.

Definition infer_place_roots (env : global_env) (Σ : sctx)
    (R : root_env) (p : place) : infer_result (Ty * ident * field_path * root_set) :=
  match place_path p with
  | None => infer_err ErrNotImplemented
  | Some (x, path) =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          match root_env_lookup x R with
          | Some roots => infer_ok (T, x, path, roots)
          | None => infer_err ErrContextCheckFailed
          end
      end
  end.

Definition consume_direct_place_value_roots (env : global_env) (Σ : sctx)
    (R : root_env) (p : place)
    : infer_result (Ty * sctx * root_set) :=
  match infer_place_roots env Σ R p with
  | infer_err err => infer_err err
  | infer_ok (T, x, path, roots) =>
      if usage_eqb (ty_usage T) UUnrestricted
      then infer_ok (T, Σ, roots)
      else
        match sctx_consume_path Σ x path with
        | infer_ok Σ' => infer_ok (T, Σ', roots)
        | infer_err err => infer_err err
        end
  end.

Fixpoint infer_core_env_state_fuel_roots (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ, R, [])
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ, R, [])
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ, R, [])
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ, R, [])
  | EVar x =>
      match consume_direct_place_value_roots env Σ R (PVar x) with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | EPlace p =>
      match consume_direct_place_value_roots env Σ R p with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then
                          infer_ok
                            (apply_lt_ty σ (fn_ret fdef), Σ', R',
                             root_sets_union arg_roots)
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)),
                           Σ', R', root_sets_union arg_roots)
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ, R, [])
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ, R, [])
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Σ0 : sctx) (R0 : root_env)
                              (defs : list field_def)
                              : infer_result (sctx * root_env * root_set) :=
                            match defs with
                            | [] => infer_ok (Σ0, R0, [])
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel_roots
                                            fuel' env Ω n R0 Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1, R1, roots_field) =>
                                        let T_expected :=
                                          instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then
                                          match go Σ1 R1 rest with
                                          | infer_err err => infer_err err
                                          | infer_ok (Σ2, R2, roots_rest) =>
                                              infer_ok
                                                (Σ2, R2,
                                                 root_set_union roots_field roots_rest)
                                          end
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ R (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok (Σ', R', roots) =>
                              infer_ok
                                (instantiate_struct_instance_ty s lts args, Σ', R', roots)
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Σ0 : sctx) (R0 : root_env)
                      (fields : list Ty) (es : list expr)
                      : infer_result (sctx * root_env * root_set) :=
                    match fields, es with
                    | [], [] => infer_ok (Σ0, R0, [])
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel_roots
                                fuel' env Ω n R0 Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1, R1, roots_payload) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then
                              match go Σ1 R1 fields' es' with
                              | infer_err err => infer_err err
                              | infer_ok (Σ2, R2, roots_rest) =>
                                  infer_ok
                                    (Σ2, R2,
                                     root_set_union roots_payload roots_rest)
                              end
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ R (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok (Σ', R', roots) =>
                      infer_ok (instantiate_enum_ty edef lts args, Σ', R', roots)
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1, R1, roots_scrut) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else match check_struct_bounds env (enum_bounds edef) args with
                  | Some err => infer_err err
                  | None =>
                  match first_duplicate_branch branches with
                  | Some name => infer_err (ErrDuplicateVariant name)
                  | None =>
	                      match first_unknown_variant_branch branches (enum_variants edef) with
	                      | Some name => infer_err (ErrVariantNotFound name)
	                      | None =>
	                          match first_missing_variant_branch (enum_variants edef) branches with
                          | Some name => infer_err (ErrMissingVariant name)
                          | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result
                                          (Ty * sctx * root_env * root_set *
                                           list sctx * list Ty * list root_set) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Σ1 &&
                                                     root_env_lookup_params_none_b ps R1
                                                  then
                                                  let R_payload :=
                                                    root_env_add_params_roots_same ps roots_scrut R1 in
                                                  match infer_core_env_state_fuel_roots
                                                          fuel' env Ω n R_payload
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload,
                                                              R_branch_payload, roots_branch) =>
                                                      let R_branch :=
                                                        root_env_remove_match_params ps R_branch_payload in
                                                      if params_ok_sctx_b env ps Σ_branch_payload &&
                                                         roots_exclude_params_b ps roots_branch &&
                                                         root_env_excludes_params_b ps R_branch
                                                      then infer_ok
                                                        (T_branch,
                                                         sctx_remove_params ps Σ_branch_payload,
                                                         R_branch,
                                                         roots_branch)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch, R_branch, roots_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (R_out : root_env)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result
                                                        (list sctx * list Ty * list root_set) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0, R0, roots0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_ok :=
                                                                  let rest_result :=
                                                                    infer_rest T_head R_out rest0 in
                                                                  match rest_result with
                                                                  | infer_err err => infer_err err
                                                                  | infer_ok (Σs, Ts, rootss) =>
                                                                      infer_ok
                                                                        (Σ0 :: Σs,
                                                                         T0 :: Ts,
                                                                         roots0 :: rootss)
                                                                  end
                                                                in
                                                                let context_error :=
                                                                  infer_err ErrContextCheckFailed in
                                                                infer_if_bool
                                                                  (root_env_eqb R0 R_out)
                                                                  rest_ok context_error
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch R_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts, rootss) =>
                                                    infer_ok
                                                      (T_branch, Σ_branch, R_branch, roots_branch,
                                                       Σs, Ts, rootss)
		                                  end
		                          end
		                          end
	                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head, R_out, roots_head,
                                              Σ_tail, Ts_tail, roots_tail) =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
	                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
	                                                  (ty_core T_head),
	                                             sctx_of_ctx Γ_out, R_out,
	                                             root_sets_union (roots_head :: roots_tail))
	                                      | None => infer_err ErrContextCheckFailed
	                                      end
	                                  end
	                      end
	                  end
	                  end
	                  end
	              end
	          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          if ty_compatible_b Ω T1 T
          then
            match root_env_lookup x R1 with
            | Some _ => infer_err ErrContextCheckFailed
            | None =>
                match infer_core_env_state_fuel_roots fuel' env Ω n
                        (root_env_add x roots1 R1) (sctx_add x T m Σ1) e2 with
                | infer_err err => infer_err err
                | infer_ok (T2, Σ2, R2, roots2) =>
                    if sctx_check_ok env x T Σ2 &&
                       roots_exclude_b x roots2 &&
                       root_env_excludes_b x (root_env_remove x R2)
                    then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                    else infer_err ErrContextCheckFailed
                end
            end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          match root_env_lookup x R1 with
          | Some _ => infer_err ErrContextCheckFailed
          | None =>
              match infer_core_env_state_fuel_roots fuel' env Ω n
                      (root_env_add x roots1 R1) (sctx_add x T1 m Σ1) e2 with
              | infer_err err => infer_err err
              | infer_ok (T2, Σ2, R2, roots2) =>
                  if sctx_check_ok env x T1 Σ2 &&
                     roots_exclude_b x roots2 &&
                     root_env_excludes_b x (root_env_remove x R2)
                  then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                  else infer_err ErrContextCheckFailed
              end
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ', R', _) => infer_ok (MkTy UUnrestricted TUnits, Σ', R', [])
      end
  | EReplace p e_new =>
      match place_path p with
      | None => infer_err ErrNotImplemented
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              match root_env_lookup x R with
              | None => infer_err ErrContextCheckFailed
              | Some roots_result =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      if writable_place_b env Σ p
                      then
                        match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e_new with
                        | infer_err err => infer_err err
                        | infer_ok (T_new, Σ1, R1, roots_new) =>
                            match root_env_lookup x R1 with
                            | None => infer_err ErrContextCheckFailed
                            | Some roots_old =>
                                if ty_compatible_b Ω T_new T_old
                                then
                                  match sctx_path_available Σ1 x path with
                                  | infer_err err => infer_err err
                                  | infer_ok _ =>
                                      match sctx_restore_path Σ1 x path with
                                      | infer_ok Σ2 =>
                                          infer_ok
                                            (T_old, Σ2,
                                             root_env_update x
                                               (root_set_union roots_old roots_new) R1,
                                             roots_result)
                                      | infer_err err => infer_err err
                                      end
                                  end
                                else infer_err (compatible_error T_new T_old)
                            end
                        end
                      else infer_err (ErrNotMutable x)
                  | Some MImmutable => infer_err (ErrNotMutable x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          end
      end
  | EAssign p e_new =>
      match place_path p with
      | None => infer_err ErrNotImplemented
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if usage_eqb (ty_usage T_old) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
              else
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then
                    match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e_new with
                    | infer_err err => infer_err err
                    | infer_ok (T_new, Σ1, R1, roots_new) =>
                        match root_env_lookup x R1 with
                        | None => infer_err ErrContextCheckFailed
                        | Some roots_old =>
                            if ty_compatible_b Ω T_new T_old
                            then
                              match sctx_path_available Σ1 x path with
                              | infer_err err => infer_err err
                              | infer_ok _ =>
                                  infer_ok
                                    (MkTy UUnrestricted TUnits, Σ1,
                                     root_env_update x
                                       (root_set_union roots_old roots_new) R1,
                                     [])
                              end
                            else infer_err (compatible_error T_new T_old)
                        end
                    end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match place_path p with
          | Some (x, _) =>
              match rk with
              | RShared =>
                  infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, [RStore x])
              | RUnique =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, [RStore x])
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          | None =>
              match rk with
              | RShared =>
                  match place_borrow_roots R p with
                  | Some roots =>
                      infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                  | None => infer_err ErrContextCheckFailed
                  end
              | RUnique =>
                  if place_under_unique_ref_b env Σ p
                  then
                    match place_borrow_roots R p with
                    | Some roots =>
                        infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                    | None => infer_err ErrContextCheckFailed
                    end
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref (EBorrow rk p) =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          if usage_eqb (ty_usage T_p) UUnrestricted
          then
            match place_path p with
            | Some (x, _) =>
                match root_env_lookup x R with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        match sctx_lookup_mut x Σ with
                        | Some MMutable => infer_ok (T_p, Σ, R, roots)
                        | Some MImmutable => infer_err (ErrImmutableBorrow x)
                        | None => infer_err (ErrUnknownVar x)
                        end
                    end
                end
            | None =>
                match place_root_lookup R p with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        if place_under_unique_ref_b env Σ p
                        then infer_ok (T_p, Σ, R, roots)
                        else infer_err (ErrImmutableBorrow (place_name p))
                    end
                end
            end
          else infer_err (ErrUsageMismatch (ty_usage T_p) UUnrestricted)
      end
  | EDeref _ => infer_err ErrNotImplemented
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1, R1, _) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then
            match infer_core_env_state_fuel_roots fuel' env Ω n R1 Σ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Σ2, R2, roots2) =>
                match infer_core_env_state_fuel_roots fuel' env Ω n R1 Σ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Σ3, R3, roots3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3)
                    then
                      if root_env_eqb R2 R3
                      then
                        match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                        | Some Γ4 =>
                            infer_ok
                              (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                               sctx_of_ctx Γ4, R2, root_set_union roots2 roots3)
                        | None => infer_err ErrContextCheckFailed
                        end
                      else infer_err ErrContextCheckFailed
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECallExpr (EMakeClosure fname captures) args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
            match check_make_closure_captures_sctx_with_env env Ω Σ captures
                    (fn_captures fdef) with
            | infer_err err => infer_err err
            | infer_ok _ =>
                let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
                    : infer_result (list Ty * sctx * root_env * list root_set) :=
                  match as_ with
                  | [] => infer_ok ([], Σ0, R0, [])
                  | e' :: es =>
                      match infer_core_env_state_fuel_roots fuel' env Ω n R0 Σ0 e' with
                      | infer_err err => infer_err err
                      | infer_ok (T_e, Σ1, R1, roots_e) =>
                          match collect Σ1 R1 es with
                          | infer_err err => infer_err err
                          | infer_ok (tys, Σ2, R2, roots_es) =>
                              infer_ok
                                (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                          end
                      end
                  end
                in
                match collect Σ R args with
                | infer_err err => infer_err err
                | infer_ok (arg_tys, Σ', R', arg_roots) =>
                    match build_sigma (fn_lifetimes fdef)
                            (repeat None (fn_lifetimes fdef))
                            arg_tys (fn_params fdef) with
                    | None => infer_err ErrLifetimeConflict
                    | Some σ_acc =>
                        let σ := finalize_subst σ_acc in
                        let ps_subst := apply_lt_params σ (fn_params fdef) in
                        match check_args Ω arg_tys ps_subst with
                        | Some err => infer_err err
                        | None =>
                            if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                            then
                              let Ω_subst :=
                                apply_lt_outlives σ (fn_outlives fdef) in
                              if outlives_constraints_hold_b Ω Ω_subst
                              then infer_ok
                                (apply_lt_ty σ (fn_ret fdef), Σ', R',
                                  root_sets_union arg_roots)
                              else infer_err ErrHrtBoundUnsatisfied
                            else infer_err ErrLifetimeLeak
	                        end
	                    end
	                end
	            end
	      end
  | ECallExpr callee args =>
      (* General function-value call: check callee, collect args, match callee type. *)
      match infer_core_env_state_fuel_roots fuel' env Ω n R Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σ1, R1, roots_callee) =>
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ2, R2, roots_e) =>
                    match collect Σ2 R2 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ3, R3, roots_es) =>
                        infer_ok (T_e :: tys, Σ3, R3, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ1 R1 args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TTypeForall type_params bounds body =>
                 match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                 | infer_err err => infer_err err
                 | infer_ok ret =>
                     infer_ok (ret, Σ', R',
                       root_set_union roots_callee (root_sets_union arg_roots))
                 end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  | _ =>
                      match infer_hrt_call_env Ω n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  end
              | _ => infer_err ErrNotImplemented
              end
          end
      end
  end
  end.

Definition infer_core_env_roots
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots 10000 env Ω n R (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, R', roots) => infer_ok (T, ctx_of_sctx Σ, R', roots)
  | infer_err err => infer_err err
  end.

Fixpoint infer_core_env_state_fuel_roots_shadow_safe (fuel : nat)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr)
    : infer_result (Ty * sctx * root_env * root_set) :=
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
  match e with
  | EUnit => infer_ok (MkTy UUnrestricted TUnits, Σ, R, [])
  | ELit (LInt _) => infer_ok (MkTy UUnrestricted TIntegers, Σ, R, [])
  | ELit (LFloat _) => infer_ok (MkTy UUnrestricted TFloats, Σ, R, [])
  | ELit (LBool _) => infer_ok (MkTy UUnrestricted TBooleans, Σ, R, [])
  | EVar x =>
      match consume_direct_place_value_roots env Σ R (PVar x) with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | EPlace p =>
      match consume_direct_place_value_roots env Σ R p with
      | infer_ok (T, Σ', roots) => infer_ok (T, Σ', R, roots)
      | infer_err err => infer_err err
      end
  | ECall fname args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
          then
          let m := fn_lifetimes fdef in
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ (fn_params fdef) in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then
                          infer_ok
                            (apply_lt_ty σ (fn_ret fdef), Σ', R',
                             root_sets_union arg_roots)
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          else infer_err ErrNotImplemented
      end
  | ECallGeneric fname type_args args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef &&
             Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
          then
          match check_struct_bounds env (fn_bounds fdef) type_args with
          | Some err => infer_err err
          | None =>
          let m := fn_lifetimes fdef in
          let params_typed := apply_type_params type_args (fn_params fdef) in
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ1, R1, roots_e) =>
                    match collect Σ1 R1 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ2, R2, roots_es) =>
                        infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ R args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match build_sigma m (repeat None m) arg_tys params_typed with
              | None => infer_err ErrLifetimeConflict
              | Some σ_acc =>
                  let σ := finalize_subst σ_acc in
                  let ps_subst := apply_lt_params σ params_typed in
                  match check_args Ω arg_tys ps_subst with
                  | Some err => infer_err err
                  | None =>
                      if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                      then
                        let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                        if outlives_constraints_hold_b Ω Ω_subst
                        then infer_ok
                          (apply_lt_ty σ
                            (subst_type_params_ty type_args (fn_ret fdef)),
                           Σ', R', root_sets_union arg_roots)
                        else infer_err ErrHrtBoundUnsatisfied
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
          end
          else infer_err ErrArityMismatch
      end
  | EFn fname =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          if no_captures_b fdef
          then infer_ok (fn_value_ty fdef, Σ, R, [])
          else infer_err ErrNotImplemented
      end
  | EMakeClosure fname captures =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
          match check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) with
          | infer_ok (env_lt, captured_tys) =>
              infer_ok (closure_value_ty_at env_lt fdef captured_tys, Σ, R, [])
          | infer_err err => infer_err err
          end
      end
  | EStruct sname lts args fields =>
      match lookup_struct sname env with
      | None => infer_err (ErrStructNotFound sname)
      | Some s =>
          if negb (Nat.eqb (List.length lts) (struct_lifetimes s))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (struct_type_params s))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (struct_bounds s) args with
          | Some err => infer_err err
          | None =>
              match first_duplicate_field fields with
              | Some name => infer_err (ErrDuplicateField name)
              | None =>
                  match first_unknown_field fields (struct_fields s) with
                  | Some name => infer_err (ErrFieldNotFound name)
                  | None =>
                      match first_missing_field (struct_fields s) fields with
                      | Some name => infer_err (ErrMissingField name)
                      | None =>
                          let fix go (Σ0 : sctx) (R0 : root_env)
                              (defs : list field_def)
                              : infer_result (sctx * root_env * root_set) :=
                            match defs with
                            | [] => infer_ok (Σ0, R0, [])
                            | f :: rest =>
                                match lookup_field_b (field_name f) fields with
                                | None => infer_err (ErrMissingField (field_name f))
                                | Some e_field =>
                                    match infer_core_env_state_fuel_roots_shadow_safe
                                            fuel' env Ω n R0 Σ0 e_field with
                                    | infer_err err => infer_err err
                                    | infer_ok (T_field, Σ1, R1, roots_field) =>
                                        let T_expected :=
                                          instantiate_struct_field_ty lts args f in
                                        if ty_compatible_b Ω T_field T_expected
                                        then
                                          match go Σ1 R1 rest with
                                          | infer_err err => infer_err err
                                          | infer_ok (Σ2, R2, roots_rest) =>
                                              infer_ok
                                                (Σ2, R2,
                                                 root_set_union roots_field roots_rest)
                                          end
                                        else infer_err (compatible_error T_field T_expected)
                                    end
                                end
                            end
                          in
                          match go Σ R (struct_fields s) with
                          | infer_err err => infer_err err
                          | infer_ok (Σ', R', roots) =>
                              infer_ok
                                (instantiate_struct_instance_ty s lts args, Σ', R', roots)
                          end
                        end
                  end
              end
          end
      end
  | EEnum enum_name variant_name lts args payloads =>
      match lookup_enum enum_name env with
      | None => infer_err (ErrEnumNotFound enum_name)
      | Some edef =>
          if negb (Nat.eqb (List.length lts) (enum_lifetimes edef))
          then infer_err ErrArityMismatch
          else if negb (Nat.eqb (List.length args) (enum_type_params edef))
          then infer_err ErrArityMismatch
          else
          match check_struct_bounds env (enum_bounds edef) args with
          | Some err => infer_err err
          | None =>
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  let fix go (Σ0 : sctx) (R0 : root_env)
                      (fields : list Ty) (es : list expr)
                      : infer_result (sctx * root_env * root_set) :=
                    match fields, es with
                    | [], [] => infer_ok (Σ0, R0, [])
                    | T_field :: fields', e_payload :: es' =>
                        match infer_core_env_state_fuel_roots_shadow_safe
                                fuel' env Ω n R0 Σ0 e_payload with
                        | infer_err err => infer_err err
                        | infer_ok (T_payload, Σ1, R1, roots_payload) =>
                            let T_expected :=
                              instantiate_enum_variant_field_ty lts args T_field in
                            if ty_compatible_b Ω T_payload T_expected
                            then
                              match go Σ1 R1 fields' es' with
                              | infer_err err => infer_err err
                              | infer_ok (Σ2, R2, roots_rest) =>
                                  infer_ok
                                    (Σ2, R2,
                                     root_set_union roots_payload roots_rest)
                              end
                            else infer_err (compatible_error T_payload T_expected)
                        end
                    | _, _ => infer_err ErrArityMismatch
                    end
                  in
                  match go Σ R (enum_variant_fields vdef) payloads with
                  | infer_err err => infer_err err
                  | infer_ok (Σ', R', roots) =>
                      infer_ok (instantiate_enum_ty edef lts args, Σ', R', roots)
                  end
              end
          end
      end
  | EMatch scrut branches =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ scrut with
      | infer_err err => infer_err err
      | infer_ok (T_scrut, Σ1, R1, roots_scrut) =>
          match ty_core T_scrut with
          | TEnum enum_name lts args =>
              match lookup_enum enum_name env with
              | None => infer_err (ErrEnumNotFound enum_name)
              | Some edef =>
                  if negb (Nat.eqb (Datatypes.length lts) (enum_lifetimes edef))
                  then infer_err ErrArityMismatch
                  else if negb (Nat.eqb (Datatypes.length args) (enum_type_params edef))
                  then infer_err ErrArityMismatch
                  else match check_struct_bounds env (enum_bounds edef) args with
                  | Some err => infer_err err
                  | None =>
                  match first_duplicate_branch branches with
                  | Some name => infer_err (ErrDuplicateVariant name)
                  | None =>
	                      match first_unknown_variant_branch branches (enum_variants edef) with
	                      | Some name => infer_err (ErrVariantNotFound name)
	                      | None =>
	                          match first_missing_variant_branch (enum_variants edef) branches with
                          | Some name => infer_err (ErrMissingVariant name)
                          | None =>
                                  let fix infer_first (defs : list enum_variant_def)
                                      : infer_result
                                          (Ty * sctx * root_env * root_set *
                                           list sctx * list Ty * list root_set) :=
                                    match defs with
                                    | [] => infer_err (ErrMissingVariant "")
                                    | v :: rest =>
                                        let infer_branch :=
                                          fun (v0 : enum_variant_def) =>
                                          match lookup_expr_branch_binders (enum_variant_name v0) branches,
                                                lookup_branch_b (enum_variant_name v0) branches with
                                          | Some binders, Some e_branch =>
                                              match match_payload_params binders lts args v0 with
                                              | infer_err err => infer_err err
                                              | infer_ok ps =>
                                                  if params_names_nodup_b ps &&
                                                     ctx_lookup_params_none_b ps Σ1 &&
                                                     root_env_lookup_params_none_b ps R1
                                                  then
                                                  let R_payload :=
                                                    root_env_add_params_roots_same ps roots_scrut R1 in
                                                  match infer_core_env_state_fuel_roots_shadow_safe
                                                          fuel' env Ω n R_payload
                                                          (sctx_add_params ps Σ1) e_branch with
                                                  | infer_err err => infer_err err
                                                  | infer_ok (T_branch, Σ_branch_payload,
                                                              R_branch_payload, roots_branch) =>
                                                      let R_branch :=
                                                        root_env_remove_match_params ps R_branch_payload in
                                                      if params_ok_sctx_b env ps Σ_branch_payload &&
                                                         roots_exclude_params_b ps roots_branch &&
                                                         root_env_excludes_params_b ps R_branch
                                                      then infer_ok
                                                        (T_branch,
                                                         sctx_remove_params ps Σ_branch_payload,
                                                         R_branch,
                                                         roots_branch)
                                                      else infer_err ErrContextCheckFailed
                                                  end
                                                  else infer_err ErrContextCheckFailed
                                              end
                                          | _, _ => infer_err (ErrMissingVariant (enum_variant_name v0))
                                          end in
                                        match infer_branch v with
                                            | infer_err err => infer_err err
                                            | infer_ok (T_branch, Σ_branch, R_branch, roots_branch) =>
                                                let fix infer_rest
                                                    (T_head : Ty)
                                                    (R_out : root_env)
                                                    (defs0 : list enum_variant_def)
                                                    : infer_result
                                                        (list sctx * list Ty * list root_set) :=
                                                  match defs0 with
                                                  | [] => infer_ok ([], [], [])
                                                  | v0 :: rest0 =>
                                                      match infer_branch v0 with
                                                          | infer_err err => infer_err err
                                                          | infer_ok (T0, Σ0, R0, roots0) =>
                                                              if ty_core_eqb (ty_core T0) (ty_core T_head)
                                                              then
                                                                let rest_ok :=
                                                                  let rest_result :=
                                                                    infer_rest T_head R_out rest0 in
                                                                  match rest_result with
                                                                  | infer_err err => infer_err err
                                                                  | infer_ok (Σs, Ts, rootss) =>
                                                                      infer_ok
                                                                        (Σ0 :: Σs,
                                                                         T0 :: Ts,
                                                                         roots0 :: rootss)
                                                                  end
                                                                in
                                                                let context_error :=
                                                                  infer_err ErrContextCheckFailed in
                                                                infer_if_bool
                                                                  (root_env_eqb R0 R_out)
                                                                  rest_ok context_error
                                                              else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head))
                                                          end
                                                  end
                                                in
                                                match infer_rest T_branch R_branch rest with
                                                | infer_err err => infer_err err
                                                | infer_ok (Σs, Ts, rootss) =>
                                                    infer_ok
                                                      (T_branch, Σ_branch, R_branch, roots_branch,
                                                       Σs, Ts, rootss)
	                                  end
	                          end
	                          end
                                  in
                                  match infer_first (enum_variants edef) with
                                  | infer_err err => infer_err err
                                  | infer_ok (T_head, Σ_head, R_out, roots_head,
                                              Σ_tail, Ts_tail, roots_tail) =>
                                      match ctx_merge_many (ctx_of_sctx Σ_head)
                                              (map ctx_of_sctx Σ_tail) with
                                      | Some Γ_out =>
                                          infer_ok
	                                            (MkTy (usage_max_tys_nonempty T_head Ts_tail)
	                                                  (ty_core T_head),
	                                             sctx_of_ctx Γ_out, R_out,
	                                             root_sets_union (roots_head :: roots_tail))
	                                      | None => infer_err ErrContextCheckFailed
	                                      end
	                                  end
	                      end
	                  end
	                  end
	                  end
	              end
	          | c => infer_err (ErrNotAnEnum c)
          end
      end
  | ELet m x T e1 e2 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          if ty_compatible_b Ω T1 T
          then
            match root_env_lookup x R1 with
            | Some _ => infer_err ErrContextCheckFailed
            | None =>
                if roots_exclude_b x roots1 && root_env_excludes_b x R1
                then
                  match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                          (root_env_add x roots1 R1) (sctx_add x T m Σ1) e2 with
                  | infer_err err => infer_err err
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      if sctx_check_ok env x T Σ2 &&
                         roots_exclude_b x roots2 &&
                         root_env_excludes_b x (root_env_remove x R2)
                      then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                      else infer_err ErrContextCheckFailed
                  end
                else infer_err ErrContextCheckFailed
            end
          else infer_err (compatible_error T1 T)
      end
  | ELetInfer m x e1 e2 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T1, Σ1, R1, roots1) =>
          match root_env_lookup x R1 with
          | Some _ => infer_err ErrContextCheckFailed
          | None =>
              if roots_exclude_b x roots1 && root_env_excludes_b x R1
              then
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                        (root_env_add x roots1 R1) (sctx_add x T1 m Σ1) e2 with
                | infer_err err => infer_err err
                | infer_ok (T2, Σ2, R2, roots2) =>
                    if sctx_check_ok env x T1 Σ2 &&
                       roots_exclude_b x roots2 &&
                       root_env_excludes_b x (root_env_remove x R2)
                    then infer_ok (T2, sctx_remove x Σ2, root_env_remove x R2, roots2)
                    else infer_err ErrContextCheckFailed
                end
              else infer_err ErrContextCheckFailed
          end
      end
  | EDrop e1 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (_, Σ', R', _) => infer_ok (MkTy UUnrestricted TUnits, Σ', R', [])
      end
  | EReplace p e_new =>
      match place_path p with
      | None => infer_err ErrNotImplemented
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              match root_env_lookup x R with
              | None => infer_err ErrContextCheckFailed
              | Some roots_result =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      if writable_place_b env Σ p
                      then
                        match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                        | infer_err err => infer_err err
                        | infer_ok (T_new, Σ1, R1, roots_new) =>
                            match root_env_lookup x R1 with
                            | None => infer_err ErrContextCheckFailed
                            | Some roots_old =>
                                if ty_compatible_b Ω T_new T_old
                                then
                                  match sctx_path_available Σ1 x path with
                                  | infer_err err => infer_err err
                                  | infer_ok _ =>
                                      match sctx_restore_path Σ1 x path with
                                      | infer_ok Σ2 =>
                                          infer_ok
                                            (T_old, Σ2,
                                             root_env_update x
                                               (root_set_union roots_old roots_new) R1,
                                             roots_result)
                                      | infer_err err => infer_err err
                                      end
                                  end
                                else infer_err (compatible_error T_new T_old)
                            end
                        end
                      else infer_err (ErrNotMutable x)
                  | Some MImmutable => infer_err (ErrNotMutable x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          end
      end
  | EAssign p e_new =>
      match place_path p with
      | None => infer_err ErrNotImplemented
      | Some (x, path) =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if usage_eqb (ty_usage T_old) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
              else
              match sctx_lookup_mut x Σ with
              | Some MMutable =>
                  if writable_place_b env Σ p
                  then
                    match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e_new with
                    | infer_err err => infer_err err
                    | infer_ok (T_new, Σ1, R1, roots_new) =>
                        match root_env_lookup x R1 with
                        | None => infer_err ErrContextCheckFailed
                        | Some roots_old =>
                            if ty_compatible_b Ω T_new T_old
                            then
                              match sctx_path_available Σ1 x path with
                              | infer_err err => infer_err err
                              | infer_ok _ =>
                                  infer_ok
                                    (MkTy UUnrestricted TUnits, Σ1,
                                     root_env_update x
                                       (root_set_union roots_old roots_new) R1,
                                     [])
                              end
                            else infer_err (compatible_error T_new T_old)
                        end
                    end
                  else infer_err (ErrNotMutable x)
              | Some MImmutable => infer_err (ErrNotMutable x)
              | None => infer_err (ErrUnknownVar x)
              end
          end
      end
  | EBorrow rk p =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          match place_path p with
          | Some (x, _) =>
              match rk with
              | RShared =>
                  infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, [RStore x])
              | RUnique =>
                  match sctx_lookup_mut x Σ with
                  | Some MMutable =>
                      infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, [RStore x])
                  | Some MImmutable => infer_err (ErrImmutableBorrow x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
          | None =>
              match rk with
              | RShared =>
                  match place_borrow_roots R p with
                  | Some roots =>
                      infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                  | None => infer_err ErrContextCheckFailed
                  end
              | RUnique =>
                  if place_under_unique_ref_b env Σ p
                  then
                    match place_borrow_roots R p with
                    | Some roots =>
                        infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                    | None => infer_err ErrContextCheckFailed
                    end
                  else infer_err (ErrImmutableBorrow (place_name p))
              end
          end
      end
  | EDeref (EBorrow rk p) =>
      match infer_place_sctx env Σ p with
      | infer_err err => infer_err err
      | infer_ok T_p =>
          if usage_eqb (ty_usage T_p) UUnrestricted
          then
            match place_path p with
            | Some (x, _) =>
                match root_env_lookup x R with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        match sctx_lookup_mut x Σ with
                        | Some MMutable => infer_ok (T_p, Σ, R, roots)
                        | Some MImmutable => infer_err (ErrImmutableBorrow x)
                        | None => infer_err (ErrUnknownVar x)
                        end
                    end
                end
            | None =>
                match place_root_lookup R p with
                | None => infer_err ErrContextCheckFailed
                | Some roots =>
                    match rk with
                    | RShared => infer_ok (T_p, Σ, R, roots)
                    | RUnique =>
                        if place_under_unique_ref_b env Σ p
                        then infer_ok (T_p, Σ, R, roots)
                        else infer_err (ErrImmutableBorrow (place_name p))
                    end
                end
            end
          else infer_err (ErrUsageMismatch (ty_usage T_p) UUnrestricted)
      end
  | EDeref _ => infer_err ErrNotImplemented
  | EIf e1 e2 e3 =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1 with
      | infer_err err => infer_err err
      | infer_ok (T_cond, Σ1, R1, _) =>
          if ty_core_eqb (ty_core T_cond) TBooleans
          then
            match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e2 with
            | infer_err err => infer_err err
            | infer_ok (T2, Σ2, R2, roots2) =>
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e3 with
                | infer_err err => infer_err err
                | infer_ok (T3, Σ3, R3, roots3) =>
                    if ty_core_eqb (ty_core T2) (ty_core T3)
                    then
                      if root_env_eqb R2 R3
                      then
                        match ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) with
                        | Some Γ4 =>
                            infer_ok
                              (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2),
                               sctx_of_ctx Γ4, R2, root_set_union roots2 roots3)
                        | None => infer_err ErrContextCheckFailed
                        end
                      else infer_err ErrContextCheckFailed
                    else infer_err (ErrTypeMismatch (ty_core T2) (ty_core T3))
                end
            end
          else infer_err (ErrTypeMismatch (ty_core T_cond) TBooleans)
      end
  | ECallExpr (EMakeClosure fname captures) args =>
      match lookup_fn_b fname (env_fns env) with
      | None => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
            match check_make_closure_captures_sctx_with_env env Ω Σ captures
                    (fn_captures fdef) with
            | infer_err err => infer_err err
            | infer_ok _ =>
                let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
                    : infer_result (list Ty * sctx * root_env * list root_set) :=
                  match as_ with
                  | [] => infer_ok ([], Σ0, R0, [])
                  | e' :: es =>
                      match infer_core_env_state_fuel_roots_shadow_safe
                              fuel' env Ω n R0 Σ0 e' with
                      | infer_err err => infer_err err
                      | infer_ok (T_e, Σ1, R1, roots_e) =>
                          match collect Σ1 R1 es with
                          | infer_err err => infer_err err
                          | infer_ok (tys, Σ2, R2, roots_es) =>
                              infer_ok
                                (T_e :: tys, Σ2, R2, roots_e :: roots_es)
                          end
                      end
                  end
                in
                match collect Σ R args with
                | infer_err err => infer_err err
                | infer_ok (arg_tys, Σ', R', arg_roots) =>
                    match build_sigma (fn_lifetimes fdef)
                            (repeat None (fn_lifetimes fdef))
                            arg_tys (fn_params fdef) with
                    | None => infer_err ErrLifetimeConflict
                    | Some σ_acc =>
                        let σ := finalize_subst σ_acc in
                        let ps_subst := apply_lt_params σ (fn_params fdef) in
                        match check_args Ω arg_tys ps_subst with
                        | Some err => infer_err err
                        | None =>
                            if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                            then
                              let Ω_subst :=
                                apply_lt_outlives σ (fn_outlives fdef) in
                              if outlives_constraints_hold_b Ω Ω_subst
                              then infer_ok
                                (apply_lt_ty σ (fn_ret fdef), Σ', R',
                                  root_sets_union arg_roots)
                              else infer_err ErrHrtBoundUnsatisfied
                            else infer_err ErrLifetimeLeak
                        end
                    end
                end
            end
      end
  | ECallExpr (EFn _) _ => infer_err ErrNotImplemented
  | ECallExpr callee args =>
      (* General function-value call: check callee, collect args, match callee type. *)
      match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ callee with
      | infer_err err => infer_err err
      | infer_ok (T_callee, Σ1, R1, roots_callee) =>
          let fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
              : infer_result (list Ty * sctx * root_env * list root_set) :=
            match as_ with
            | [] => infer_ok ([], Σ0, R0, [])
            | e' :: es =>
                match infer_core_env_state_fuel_roots_shadow_safe
                        fuel' env Ω n R0 Σ0 e' with
                | infer_err err => infer_err err
                | infer_ok (T_e, Σ2, R2, roots_e) =>
                    match collect Σ2 R2 es with
                    | infer_err err => infer_err err
                    | infer_ok (tys, Σ3, R3, roots_es) =>
                        infer_ok (T_e :: tys, Σ3, R3, roots_e :: roots_es)
                    end
                end
            end
          in
          match collect Σ1 R1 args with
          | infer_err err => infer_err err
          | infer_ok (arg_tys, Σ', R', arg_roots) =>
              match ty_core T_callee with
              | TFn param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TClosure _ param_tys ret =>
                  match check_arg_tys Ω arg_tys param_tys with
                  | Some err => infer_err err
                  | None =>
                      infer_ok (ret, Σ', R',
                        root_set_union roots_callee (root_sets_union arg_roots))
                  end
              | TTypeForall type_params bounds body =>
                 match infer_type_forall_call_env env Ω type_params bounds body arg_tys with
                 | infer_err err => infer_err err
                 | infer_ok ret =>
                     infer_ok (ret, Σ', R',
                       root_set_union roots_callee (root_sets_union arg_roots))
                 end
              | TForall m bounds body =>
                  match ty_core body with
                  | TTypeForall type_params type_bounds type_body =>
                      match infer_mixed_forall_call_env env Ω n m bounds
                              type_params type_bounds type_body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  | _ =>
                      match infer_hrt_call_env Ω n m bounds body arg_tys with
                      | infer_err err => infer_err err
                      | infer_ok ret =>
                          infer_ok (ret, Σ', R',
                            root_set_union roots_callee (root_sets_union arg_roots))
                      end
                  end
              | _ => infer_err ErrNotImplemented
              end
          end
      end
  end
  end.

Definition infer_core_env_roots_shadow_safe
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_core_env_state_fuel_roots_shadow_safe 10000 env Ω n R (sctx_of_ctx Γ) e with
  | infer_ok (T, Σ, R', roots) => infer_ok (T, ctx_of_sctx Σ, R', roots)
  | infer_err err => infer_err err
  end.

Definition infer_body (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  infer_core fenv Ω n Γ e.

(* ------------------------------------------------------------------ *)
(* Expose infer_args as a top-level definition for CheckerSoundness      *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_args (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx)
    (args : list expr) (params : list param) : infer_result ctx :=
  match args, params with
  | [],       []       => infer_ok Γ
  | [],       _ :: _   => infer_err ErrArityMismatch
  | _ :: _,   []       => infer_err ErrArityMismatch
  | e :: es,  p :: ps  =>
      match infer_core fenv Ω n Γ e with
      | infer_err err            => infer_err err
      | infer_ok (T_e, Γ1) =>
          if ty_compatible_b Ω T_e (param_ty p)
          then infer_args fenv Ω n Γ1 es ps
          else infer_err (compatible_error T_e (param_ty p))
      end
  end.

(* ------------------------------------------------------------------ *)
(* Argument collection helper for ECall soundness                        *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_args_collect (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx)
    (args : list expr) : infer_result (list Ty * ctx) :=
  match args with
  | [] => infer_ok ([], Γ)
  | e :: es =>
      match infer_core fenv Ω n Γ e with
      | infer_err err => infer_err err
      | infer_ok (T_e, Γ1) =>
          match infer_args_collect fenv Ω n Γ1 es with
          | infer_err err => infer_err err
          | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(* Function-definition-level type checker                                *)
(* ------------------------------------------------------------------ *)

Fixpoint params_ok_b (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: ps' =>
      ctx_check_ok (param_name p) (param_ty p) Γ &&
      params_ok_b ps' Γ
  end.

Fixpoint wf_params_b (Δ : region_ctx) (ps : list param) : bool :=
  match ps with
  | [] => true
  | p :: ps' => wf_type_b Δ (param_ty p) && wf_params_b Δ ps'
  end.

Fixpoint string_in (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else string_in x ys
  end.

Fixpoint duplicate_param_name_aux (seen : list string) (ps : list param) : option ident :=
  match ps with
  | [] => None
  | p :: ps' =>
      if string_in (fst (param_name p)) seen
      then Some (param_name p)
      else duplicate_param_name_aux (fst (param_name p) :: seen) ps'
  end.

Definition duplicate_param_name (ps : list param) : option ident :=
  duplicate_param_name_aux [] ps.

Definition check_fn_binding_params (Δ : region_ctx) (f : fn_def)
    : option infer_error :=
  if negb (wf_params_b Δ (fn_captures f))
  then Some ErrLifetimeLeak
  else
  if negb (wf_params_b Δ (fn_params f))
  then Some ErrLifetimeLeak
  else
  match duplicate_param_name (fn_binding_params f) with
  | Some x => Some (ErrDuplicateParam x)
  | None => None
  end.

Lemma string_in_false_not_in : forall x xs,
  string_in x xs = false ->
  ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros H Hin.
  - contradiction.
  - destruct (String.eqb x y) eqn:Heq.
    + discriminate.
    + destruct Hin as [Heq_xy | Hin].
      * subst y. rewrite String.eqb_refl in Heq. discriminate.
      * apply (IH H). exact Hin.
Qed.

Fixpoint string_names_unique_b (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (string_in x xs') && string_names_unique_b xs'
  end.

Definition fn_name_strings (fns : list fn_def) : list string :=
  map (fun f => fst (fn_name f)) fns.

Definition enum_variant_names (e : enum_def) : list string :=
  map enum_variant_name (enum_variants e).

Definition top_level_names (env : global_env) : list string :=
  map struct_name (env_structs env) ++
  map enum_name (env_enums env) ++
  map trait_name (env_traits env) ++
  fn_name_strings (env_fns env).

Definition top_level_names_unique_b (env : global_env) : bool :=
  string_names_unique_b (top_level_names env).

Definition enum_variants_unique_b (e : enum_def) : bool :=
  string_names_unique_b (enum_variant_names e).

Definition enum_variant_names_unique_b (env : global_env) : bool :=
  forallb enum_variants_unique_b (env_enums env).

Definition global_names_unique_b (env : global_env) : bool :=
  top_level_names_unique_b env && enum_variant_names_unique_b env.

Lemma string_names_unique_b_nodup : forall xs,
  string_names_unique_b xs = true ->
  NoDup xs.
Proof.
  induction xs as [| x xs IH]; simpl; intros Hunique.
  - constructor.
  - apply andb_true_iff in Hunique.
    destruct Hunique as [Hfresh Hrest].
    apply negb_true_iff in Hfresh.
    constructor.
    + apply string_in_false_not_in. exact Hfresh.
    + apply IH. exact Hrest.
Qed.

Lemma NoDup_app_right : forall (A : Type) (xs ys : list A),
  NoDup (xs ++ ys) ->
  NoDup ys.
Proof.
  intros A xs.
  induction xs as [| x xs IH]; intros ys Hnodup.
  - simpl in Hnodup. exact Hnodup.
  - simpl in Hnodup. inversion Hnodup as [| ? ? _ Hnodup_tail]; subst.
    apply IH. exact Hnodup_tail.
Qed.

Lemma NoDup_app_left : forall (A : Type) (xs ys : list A),
  NoDup (xs ++ ys) ->
  NoDup xs.
Proof.
  intros A xs.
  induction xs as [| x xs IH]; intros ys Hnodup.
  - constructor.
  - simpl in Hnodup. inversion Hnodup as [| ? ? Hfresh Hnodup_tail]; subst.
    constructor.
    + intros Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IH with (ys := ys). exact Hnodup_tail.
Qed.

Lemma top_level_names_unique_b_nodup : forall env,
  top_level_names_unique_b env = true ->
  NoDup (top_level_names env).
Proof.
  intros env Hunique.
  unfold top_level_names_unique_b in Hunique.
  apply string_names_unique_b_nodup. exact Hunique.
Qed.

Lemma top_level_names_unique_b_fn_names_nodup : forall env,
  top_level_names_unique_b env = true ->
  NoDup (fn_name_strings (env_fns env)).
Proof.
  intros env Hunique.
  pose proof (top_level_names_unique_b_nodup env Hunique) as Hnodup.
  unfold top_level_names in Hnodup.
  apply (NoDup_app_right string
    (map struct_name (env_structs env) ++
     map enum_name (env_enums env) ++
     map trait_name (env_traits env))).
  repeat rewrite <- app_assoc. exact Hnodup.
Qed.

Lemma ctx_names_params_ctx_param_names : forall ps,
  ctx_names (params_ctx ps) = param_names ps.
Proof.
  induction ps as [| p ps IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma param_names_app : forall ps1 ps2,
  param_names (ps1 ++ ps2) = param_names ps1 ++ param_names ps2.
Proof.
  induction ps1 as [| p ps1 IH]; intros ps2.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma duplicate_param_name_aux_none_no_seen : forall seen ps x,
  duplicate_param_name_aux seen ps = None ->
  In x (param_names ps) ->
  ~ In (fst x) seen.
Proof.
  intros seen ps.
  revert seen.
  induction ps as [| p ps IH]; simpl; intros seen x Hnone Hin.
  - contradiction.
  - destruct (string_in (fst (param_name p)) seen) eqn:Hseen;
      try discriminate.
    destruct Hin as [Hx | Hin].
    + subst x. apply string_in_false_not_in. exact Hseen.
    + specialize (IH (fst (param_name p) :: seen) x Hnone Hin).
      intros Hfst. apply IH. right. exact Hfst.
Qed.

Lemma duplicate_param_name_aux_none_nodup_param_names : forall seen ps,
  duplicate_param_name_aux seen ps = None ->
  NoDup (param_names ps).
Proof.
  intros seen ps.
  revert seen.
  induction ps as [| p ps IH]; simpl; intros seen Hnone.
  - constructor.
  - destruct (string_in (fst (param_name p)) seen) eqn:Hseen;
      try discriminate.
    constructor.
    + intros Hin.
      pose proof (duplicate_param_name_aux_none_no_seen
        (fst (param_name p) :: seen) ps (param_name p) Hnone Hin) as Hfresh.
      apply Hfresh. left. reflexivity.
    + apply (IH (fst (param_name p) :: seen)). exact Hnone.
Qed.

Lemma duplicate_param_name_none_nodup_params_ctx : forall ps,
  duplicate_param_name ps = None ->
  NoDup (ctx_names (params_ctx ps)).
Proof.
  intros ps Hnone.
  rewrite ctx_names_params_ctx_param_names.
  unfold duplicate_param_name in Hnone.
  eapply duplicate_param_name_aux_none_nodup_param_names.
  exact Hnone.
Qed.

Lemma duplicate_param_name_none_nodup_params_ctx_suffix : forall caps ps,
  duplicate_param_name (caps ++ ps) = None ->
  NoDup (ctx_names (params_ctx ps)).
Proof.
  intros caps ps Hnone.
  rewrite ctx_names_params_ctx_param_names.
  pose proof (duplicate_param_name_none_nodup_params_ctx (caps ++ ps) Hnone)
    as Hnodup_all.
  rewrite ctx_names_params_ctx_param_names in Hnodup_all.
  rewrite param_names_app in Hnodup_all.
  eapply NoDup_app_right. exact Hnodup_all.
Qed.

Lemma duplicate_param_name_none_nodup_params_ctx_prefix : forall ps caps,
  duplicate_param_name (ps ++ caps) = None ->
  NoDup (ctx_names (params_ctx ps)).
Proof.
  intros ps caps Hnone.
  rewrite ctx_names_params_ctx_param_names.
  pose proof (duplicate_param_name_none_nodup_params_ctx (ps ++ caps) Hnone)
    as Hnodup_all.
  rewrite ctx_names_params_ctx_param_names in Hnodup_all.
  rewrite param_names_app in Hnodup_all.
  eapply NoDup_app_left. exact Hnodup_all.
Qed.


(* Check a single function definition:
   - infer the body type
   - verify it matches fn_ret (core type + exact usage)
   - verify all linear/affine parameters are consumed *)
Definition infer (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_body fenv Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_b (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

(* Check all functions in the program *)
Definition check_program (fenv : list fn_def) : bool :=
  forallb (fun f =>
    match infer fenv f with
    | infer_ok _ => true
    | infer_err _ => false
    end) fenv.

Definition infer_env (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env body_env Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition fn_with_body (f : fn_def) (body : expr) : fn_def :=
  MkFnDef (fn_name f) (fn_lifetimes f) (fn_outlives f)
    (fn_captures f) (fn_params f) (fn_ret f) body
    (fn_type_params f) (fn_bounds f).

Definition infer_env_elab (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * fn_def) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_elab body_env Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, body') =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, fn_with_body f body')
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots_shadow_safe
    (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots_shadow_safe
          body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Lemma infer_env_params_nodup : forall env f T Γ',
  infer_env env f = infer_ok (T, Γ') ->
  NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f T Γ' Hinfer.
  unfold infer_env in Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  unfold check_fn_binding_params in Hinfer.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_captures f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (duplicate_param_name (fn_binding_params f)) as [dup |] eqn:Hdup;
    try discriminate.
  unfold fn_binding_params in Hdup.
  eapply duplicate_param_name_none_nodup_params_ctx_prefix. exact Hdup.
Qed.

Lemma infer_env_roots_params_nodup : forall env f R0 T Γ' R' roots,
  infer_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
  NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f R0 T Γ' R' roots Hinfer.
  unfold infer_env_roots in Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  unfold check_fn_binding_params in Hinfer.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_captures f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (duplicate_param_name (fn_binding_params f)) as [dup |] eqn:Hdup;
    try discriminate.
  unfold fn_binding_params in Hdup.
  eapply duplicate_param_name_none_nodup_params_ctx_prefix. exact Hdup.
Qed.

Definition ex_struct_pair : struct_def :=
  MkStructDef ("Pair"%string) 0 0 []
    [ MkFieldDef ("x"%string) MImmutable (MkTy UUnrestricted TIntegers)
    ; MkFieldDef ("y"%string) MImmutable (MkTy UUnrestricted TBooleans)
    ].

Definition ex_env_struct_pair : global_env :=
  MkGlobalEnv [ex_struct_pair] [] [] [] [] [].

Example infer_core_env_roots_var_summary_ok :
  infer_core_env_roots ex_env_struct_pair [] 0
    [((("x"%string), 0), [RStore (("x"%string), 0)])]
    [((("x"%string), 0), MkTy UUnrestricted TIntegers,
      binding_state_of_bool false, MImmutable)]
    (EVar (("x"%string), 0)) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [((("x"%string), 0), MkTy UUnrestricted TIntegers,
       binding_state_of_bool false, MImmutable)],
     [((("x"%string), 0), [RStore (("x"%string), 0)])],
     [RStore (("x"%string), 0)]).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_roots_let_escape_rejected :
  infer_core_env_roots ex_env_struct_pair [] 0 [] []
    (ELet MImmutable (("x"%string), 0) (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      (EBorrow RShared (PVar (("x"%string), 0)))) =
  infer_err ErrContextCheckFailed.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_roots_let_initializer_shadow_accepted :
  infer_core_env_roots ex_env_struct_pair [] 0 []
    [((("x"%string), 0), MkTy UUnrestricted TIntegers,
      binding_state_of_bool false, MImmutable)]
    (ELetInfer MImmutable (("x"%string), 0)
      (EBorrow RShared (PVar (("x"%string), 0)))
      EUnit) =
  infer_ok
    (MkTy UUnrestricted TUnits,
     [((("x"%string), 0), MkTy UUnrestricted TIntegers,
       binding_state_of_bool false, MImmutable)],
     [],
     []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_literal_ok :
  infer_core_env ex_env_struct_pair [] 0 []
    (EStruct ("Pair"%string) [] []
      [(("y"%string), ELit (LBool true)); (("x"%string), ELit (LInt 1))]) =
  infer_ok (MkTy UUnrestricted (TStruct ("Pair"%string) [] []), []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_field_ok :
  infer_core_env ex_env_struct_pair [] 0
    [((("p"%string), 0), MkTy UUnrestricted (TStruct ("Pair"%string) [] []),
      binding_state_of_bool false, MImmutable)]
    (EPlace (PField (PVar (("p"%string), 0)) ("x"%string))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [((("p"%string), 0), MkTy UUnrestricted (TStruct ("Pair"%string) [] []),
       binding_state_of_bool false, MImmutable)]).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_elab_nested_letinfer_ok :
  infer_core_env_elab ex_env_struct_pair [] 0 []
    (ELetInfer MImmutable (("x"%string), 0)
      (ELit (LInt 1))
      (ELetInfer MImmutable (("y"%string), 0)
        (EVar (("x"%string), 0))
        (EVar (("y"%string), 0)))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [],
     ELet MImmutable (("x"%string), 0) (MkTy UUnrestricted TIntegers)
       (ELit (LInt 1))
       (ELet MImmutable (("y"%string), 0) (MkTy UUnrestricted TIntegers)
         (EVar (("x"%string), 0))
         (EVar (("y"%string), 0)))).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_elab_no_letinfer_same_expr :
  infer_core_env_elab ex_env_struct_pair [] 0 []
    (EIf (ELit (LBool true)) (ELit (LInt 1)) (ELit (LInt 2))) =
  infer_ok
    (MkTy UUnrestricted TIntegers,
     [],
     EIf (ELit (LBool true)) (ELit (LInt 1)) (ELit (LInt 2))).
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_shared_ref_covariant_inner :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TRef LStatic RShared (MkTy UUnrestricted TIntegers)))
    (MkTy UUnrestricted
      (TRef LStatic RShared (MkTy UAffine TIntegers))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_unique_ref_invariant_inner :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TRef LStatic RUnique (MkTy UUnrestricted TIntegers)))
    (MkTy UUnrestricted
      (TRef LStatic RUnique (MkTy UAffine TIntegers))) = false.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_closure_env_contra_params_covariant_ret :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TClosure LStatic
        [MkTy UAffine TIntegers]
        (MkTy UUnrestricted TBooleans)))
    (MkTy UAffine
      (TClosure (LVar 0)
        [MkTy UUnrestricted TIntegers]
        (MkTy UAffine TBooleans))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_fn_expected_closure_bridge :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TFn
        [MkTy UAffine TIntegers]
        (MkTy UUnrestricted TBooleans)))
    (MkTy UAffine
      (TClosure (LVar 0)
        [MkTy UUnrestricted TIntegers]
        (MkTy UAffine TBooleans))) = true.
Proof. vm_compute. reflexivity. Qed.

Example ty_compatible_b_closure_not_expected_fn :
  ty_compatible_b []
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans)))
    (MkTy UUnrestricted
      (TFn [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.

Example ty_ref_free_b_rejects_closure_value :
  ty_ref_free_b
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_capture_ref_free_plain_struct : struct_def :=
  MkStructDef "PlainCapture"%string 0 0 [] [
    MkFieldDef "n"%string MImmutable (MkTy UUnrestricted TIntegers)
  ].

Definition ex_capture_ref_free_ref_struct : struct_def :=
  MkStructDef "RefCapture"%string 0 0 [] [
    MkFieldDef "r"%string MImmutable
      (MkTy UUnrestricted
        (TRef LStatic RShared (MkTy UUnrestricted TIntegers)))
  ].

Example capture_ref_free_ty_b_accepts_plain_struct :
  capture_ref_free_ty_b
    (MkGlobalEnv [ex_capture_ref_free_plain_struct] [] [] [] [] [])
    (MkTy UUnrestricted (TStruct "PlainCapture"%string [] [])) = true.
Proof. vm_compute. reflexivity. Qed.

Example capture_ref_free_ty_b_rejects_ref_struct :
  capture_ref_free_ty_b
    (MkGlobalEnv [ex_capture_ref_free_ref_struct] [] [] [] [] [])
    (MkTy UUnrestricted (TStruct "RefCapture"%string [] [])) = false.
Proof. vm_compute. reflexivity. Qed.

Example capture_ref_free_ty_b_rejects_closure_value :
  capture_ref_free_ty_b
    (MkGlobalEnv [] [] [] [] [] [])
    (MkTy UUnrestricted
      (TClosure LStatic [] (MkTy UUnrestricted TBooleans))) = false.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Borrow conflict checker                                               *)
(*                                                                      *)
(* borrow_check traverses an expression and maintains a borrow_state.   *)
(* It is run after infer succeeds (infer handles structural well-        *)
(* formedness; borrow_check handles aliasing constraints).               *)
(* ------------------------------------------------------------------ *)

Fixpoint borrow_check (fenv : list fn_def) (BS : borrow_state) (Γ : ctx)
    (e : expr) : infer_result borrow_state :=
  match e with
  | EUnit | ELit _ | EVar _ | EPlace _ => infer_ok BS
  | EFn _ => infer_ok BS
  | EMakeClosure _ captures =>
      let fix go (captures0 : list ident) : infer_result borrow_state :=
        match captures0 with
        | [] => infer_ok BS
        | x :: rest =>
            if bs_has_mut x BS
            then infer_err (ErrBorrowConflict x)
            else go rest
        end
      in go captures
  | EStruct _ _ _ _ => infer_err ErrNotImplemented
  | EEnum _ _ _ _ payloads =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | [] => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1 => go BS1 rest
            end
        end
      in go BS payloads
  | EMatch _ _ => infer_err ErrNotImplemented

  | EBorrow RShared (PVar x) =>
      if bs_has_mut x BS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (BEShared x :: BS)

  | EBorrow RUnique (PVar x) =>
      if bs_has_any x BS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (BEMut x :: BS)

  (* &*p / &mut *p: treat the root reference as the borrow target *)
  | EBorrow RShared (PDeref p) =>
      let r := place_root p in
      if bs_has_mut r BS
      then infer_err (ErrBorrowConflict r)
      else infer_ok (BEShared r :: BS)

  | EBorrow RUnique (PDeref p) =>
      let r := place_root p in
      if bs_has_any r BS
      then infer_err (ErrBorrowConflict r)
      else infer_ok (BEMut r :: BS)

  | EBorrow _ (PField _ _) => infer_err ErrNotImplemented

  | EDeref e1 =>
      match expr_ref_root e1 with
      | Some r =>
          if bs_has_mut r BS
          then infer_err (ErrBorrowConflict r)
          else borrow_check fenv BS Γ e1
      | None => borrow_check fenv BS Γ e1
      end

  | EDrop e1 =>
      borrow_check fenv BS Γ e1

  | EReplace (PVar _) e_new | EAssign (PVar _) e_new =>
      borrow_check fenv BS Γ e_new

  (* write-through blocked if root has any active re-borrow *)
  | EReplace (PDeref p) e_new | EAssign (PDeref p) e_new =>
      let r := place_root p in
      if bs_has_any r BS
      then infer_err (ErrBorrowConflict r)
      else borrow_check fenv BS Γ e_new

  | EReplace (PField _ _) _ | EAssign (PField _ _) _ =>
      infer_err ErrNotImplemented

  | ELet m x T e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 (ctx_add_b x T m Γ) e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  => infer_ok (bs_remove_all new_from_e1 BS2)
          end
      end

  | ELetInfer m x e1 e2 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let new_from_e1 := bs_new_entries BS BS1 in
          match borrow_check fenv BS1 Γ e2 with
          | infer_err err => infer_err err
          | infer_ok BS2  => infer_ok (bs_remove_all new_from_e1 BS2)
          end
      end

  | EIf e1 e2 e3 =>
      match borrow_check fenv BS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok BS1  =>
          match borrow_check fenv BS1 Γ e2,
                borrow_check fenv BS1 Γ e3 with
          | infer_ok BS2, infer_ok BS3 =>
              if bs_eqb BS2 BS3
              then infer_ok BS2
              else infer_err ErrContextCheckFailed
          | infer_err err, _ | _, infer_err err => infer_err err
          end
      end

  | ECall _ args =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | []      => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1  => go BS1 rest
            end
        end
      in go BS args
  | ECallGeneric _ _ args =>
      let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
        match as_ with
        | []      => infer_ok BS0
        | a :: rest =>
            match borrow_check fenv BS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok BS1  => go BS1 rest
            end
        end
      in go BS args
  | ECallExpr callee args =>
      match borrow_check fenv BS Γ callee with
      | infer_err err => infer_err err
      | infer_ok BS1 =>
          let fix go (BS0 : borrow_state) (as_ : list expr) : infer_result borrow_state :=
            match as_ with
            | []      => infer_ok BS0
            | a :: rest =>
                match borrow_check fenv BS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok BS2  => go BS2 rest
                end
            end
          in go BS1 args
      end
  end.

(* Separate top-level borrow_check_args for BorrowCheckSoundness proofs. *)
Fixpoint borrow_check_args (fenv : list fn_def) (BS : borrow_state) (Γ : ctx)
    (args : list expr) : infer_result borrow_state :=
  match args with
  | []       => infer_ok BS
  | a :: rest =>
      match borrow_check fenv BS Γ a with
      | infer_err err => infer_err err
      | infer_ok BS1  => borrow_check_args fenv BS1 Γ rest
      end
  end.

Inductive path_borrow_entry : Type :=
  | PBShared : ident -> field_path -> path_borrow_entry
  | PBMut : ident -> field_path -> path_borrow_entry.

Definition path_borrow_state := list path_borrow_entry.

Definition pbe_target_eqb (x : ident) (p : field_path) (e : path_borrow_entry) : bool :=
  match e with
  | PBShared y q | PBMut y q => ident_eqb x y && path_conflict_b p q
  end.

Definition pbs_has_mut (x : ident) (p : field_path) (PBS : path_borrow_state) : bool :=
  existsb (fun e =>
    match e with
    | PBMut y q => ident_eqb x y && path_conflict_b p q
    | _ => false
    end) PBS.

Definition pbs_has_any (x : ident) (p : field_path) (PBS : path_borrow_state) : bool :=
  existsb (pbe_target_eqb x p) PBS.

Definition borrow_target_of_place (p : place) : ident * field_path :=
  (place_root p, place_suffix_path p).

Definition path_borrow_entry_eqb (a b : path_borrow_entry) : bool :=
  match a, b with
  | PBShared x p, PBShared y q
  | PBMut x p, PBMut y q => ident_eqb x y && path_eqb p q
  | _, _ => false
  end.

Fixpoint pbs_remove_one (e : path_borrow_entry) (PBS : path_borrow_state)
    : path_borrow_state :=
  match PBS with
  | [] => []
  | h :: rest =>
      if path_borrow_entry_eqb e h then rest else h :: pbs_remove_one e rest
  end.

Definition pbs_remove_all (to_remove PBS : path_borrow_state) : path_borrow_state :=
  fold_left (fun acc e => pbs_remove_one e acc) to_remove PBS.

Definition pbs_new_entries (before after : path_borrow_state) : path_borrow_state :=
  firstn (List.length after - List.length before) after.

Fixpoint pbs_eqb (a b : path_borrow_state) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => path_borrow_entry_eqb x y && pbs_eqb xs ys
  | _, _ => false
  end.

Definition pbs_access_allowed_b
    (x : ident) (p : field_path) (PBS : path_borrow_state) (T : Ty) : bool :=
  negb (pbs_has_mut x p PBS) &&
  (usage_eqb (ty_usage T) UUnrestricted || negb (pbs_has_any x p PBS)).

Definition borrow_check_place_access
    (env : global_env) (PBS : path_borrow_state) (Γ : ctx) (p : place)
    : infer_result unit :=
  match place_path p with
  | None => infer_ok tt
  | Some (x, path) =>
      match infer_place_env env Γ p with
      | infer_err err => infer_err err
      | infer_ok T =>
          if pbs_access_allowed_b x path PBS T
          then infer_ok tt
          else infer_err (ErrBorrowConflict x)
      end
  end.

Fixpoint borrow_check_env (env : global_env) (PBS : path_borrow_state) (Γ : ctx)
    (e : expr) : infer_result path_borrow_state :=
  match e with
  | EUnit | ELit _ | EFn _ => infer_ok PBS
  | EMakeClosure _ captures =>
      let fix go (captures0 : list ident) : infer_result path_borrow_state :=
        match captures0 with
        | [] => infer_ok PBS
        | x :: rest =>
            if pbs_has_mut x [] PBS
            then infer_err (ErrBorrowConflict x)
            else go rest
        end
      in go captures
  | EVar x =>
      match borrow_check_place_access env PBS Γ (PVar x) with
      | infer_ok _ => infer_ok PBS
      | infer_err err => infer_err err
      end
  | EPlace p =>
      match borrow_check_place_access env PBS Γ p with
      | infer_ok _ => infer_ok PBS
      | infer_err err => infer_err err
      end
  | EStruct _ _ _ fields =>
      let fix go (PBS0 : path_borrow_state) (fields0 : list (string * expr))
          : infer_result path_borrow_state :=
        match fields0 with
        | [] => infer_ok PBS0
        | (_, e_field) :: rest =>
            match borrow_check_env env PBS0 Γ e_field with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS fields
  | EEnum _ _ _ _ payloads =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS payloads
  | EMatch scrut branches =>
      match borrow_check_env env PBS Γ scrut with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let fix go (expected : option path_borrow_state)
              (branches0 : list (string * list ident * expr))
              : infer_result path_borrow_state :=
            match branches0 with
            | [] =>
                match expected with
                | Some PBS_out => infer_ok PBS_out
                | None => infer_err (ErrMissingVariant "")
                end
            | (_, binders, e_branch) :: rest =>
                let Γ_branch := ctx_add_params (unrestricted_unit_params_of_binders binders) Γ in
                match borrow_check_env env PBS1 Γ_branch e_branch with
                | infer_err err => infer_err err
                | infer_ok PBS_branch =>
                    match expected with
                    | None => go (Some PBS_branch) rest
                    | Some PBS_expected =>
                        if pbs_eqb PBS_branch PBS_expected
                        then go expected rest
                        else infer_err ErrContextCheckFailed
                    end
                end
            end
          in go None branches
      end
  | EBorrow RShared p =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_mut x path PBS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (PBShared x path :: PBS)
  | EBorrow RUnique p =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_any x path PBS
      then infer_err (ErrBorrowConflict x)
      else infer_ok (PBMut x path :: PBS)
  | EReplace p e_new | EAssign p e_new =>
      let '(x, path) := borrow_target_of_place p in
      if pbs_has_any x path PBS
      then infer_err (ErrBorrowConflict x)
      else borrow_check_env env PBS Γ e_new
  | EDeref e1 =>
      match expr_ref_root e1 with
      | Some r =>
          if pbs_has_mut r [] PBS
          then infer_err (ErrBorrowConflict r)
          else borrow_check_env env PBS Γ e1
      | None => borrow_check_env env PBS Γ e1
      end
  | EDrop e1 => borrow_check_env env PBS Γ e1
  | ELet m x T e1 e2 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let new_from_e1 := pbs_new_entries PBS PBS1 in
          match borrow_check_env env PBS1 (ctx_add_b x T m Γ) e2 with
          | infer_err err => infer_err err
          | infer_ok PBS2 => infer_ok (pbs_remove_all new_from_e1 PBS2)
          end
      end
  | ELetInfer m x e1 e2 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let new_from_e1 := pbs_new_entries PBS PBS1 in
          match borrow_check_env env PBS1 Γ e2 with
          | infer_err err => infer_err err
          | infer_ok PBS2 => infer_ok (pbs_remove_all new_from_e1 PBS2)
          end
      end
  | EIf e1 e2 e3 =>
      match borrow_check_env env PBS Γ e1 with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          match borrow_check_env env PBS1 Γ e2,
                borrow_check_env env PBS1 Γ e3 with
          | infer_ok PBS2, infer_ok PBS3 =>
              if pbs_eqb PBS2 PBS3
              then infer_ok PBS2
              else infer_err ErrContextCheckFailed
          | infer_err err, _ | _, infer_err err => infer_err err
          end
      end
  | ECall _ args =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS args
  | ECallGeneric _ _ args =>
      let fix go (PBS0 : path_borrow_state) (args0 : list expr)
          : infer_result path_borrow_state :=
        match args0 with
        | [] => infer_ok PBS0
        | a :: rest =>
            match borrow_check_env env PBS0 Γ a with
            | infer_err err => infer_err err
            | infer_ok PBS1 => go PBS1 rest
            end
        end
      in go PBS args
  | ECallExpr callee args =>
      match borrow_check_env env PBS Γ callee with
      | infer_err err => infer_err err
      | infer_ok PBS1 =>
          let fix go (PBS0 : path_borrow_state) (args0 : list expr)
              : infer_result path_borrow_state :=
            match args0 with
            | [] => infer_ok PBS0
            | a :: rest =>
                match borrow_check_env env PBS0 Γ a with
                | infer_err err => infer_err err
                | infer_ok PBS2 => go PBS2 rest
                end
            end
          in go PBS1 args
      end
  end.

(* ------------------------------------------------------------------ *)
(* Combined type + borrow checker                                        *)
(* ------------------------------------------------------------------ *)

(* Legacy checker retained for proof compatibility only.  The OCaml CLI
   and extraction roots use the env/stateful checker below. *)
Definition infer_full (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer fenv f with
  | infer_err err => infer_err err
  | infer_ok res  =>
      let Γ := fn_body_ctx f in
      match borrow_check fenv [] Γ (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _    => infer_ok res
      end
  end.

Definition infer_full_env (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer_env env f with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition infer_full_env_elab (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * fn_def) :=
  match infer_env_elab env f with
  | infer_err err => infer_err err
  | infer_ok (T, Γ, f') =>
      match borrow_check_env env [] (fn_body_ctx f') (fn_body f') with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok (T, Γ, f')
      end
  end.

Definition infer_full_env_roots (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  match infer_env_roots env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      match borrow_check_env env [] (fn_body_ctx f) (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _ => infer_ok res
      end
  end.

Definition alpha_normalize_global_env (env : global_env) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (alpha_rename_syntax (env_fns env)).

Fixpoint infer_fns_env_elab (env : global_env) (fns : list fn_def)
    : infer_result (list fn_def) :=
  match fns with
  | [] => infer_ok []
  | f :: rest =>
      match infer_full_env_elab env f with
      | infer_err err => infer_err err
      | infer_ok (_, _, f') =>
          match infer_fns_env_elab env rest with
          | infer_err err => infer_err err
          | infer_ok rest' => infer_ok (f' :: rest')
          end
      end
  end.

Definition infer_program_env_alpha_elab (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  match infer_fns_env_elab env_alpha (env_fns env_alpha) with
  | infer_err err => infer_err err
  | infer_ok fns' =>
      infer_ok (MkGlobalEnv (env_structs env_alpha) (env_enums env_alpha)
        (env_traits env_alpha) (env_impls env_alpha)
        (env_local_bounds env_alpha) fns')
  end.

Definition fn_params_roots_exclude_b (ps : list param) (roots : root_set) : bool :=
  forallb (fun x => roots_exclude_b x roots) (ctx_names (params_ctx ps)).

Definition fn_params_root_env_excludes_b (ps : list param) (R : root_env) : bool :=
  forallb (fun x => root_env_excludes_b x R) (ctx_names (params_ctx ps)).

Definition check_fn_root_shadow_summary (env : global_env) (fdef : fn_def) : bool :=
  preservation_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_summary (env : global_env) : bool :=
  forallb (check_fn_root_shadow_summary env) (env_fns env).

Definition check_fn_root_shadow_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | infer_err _ => false
  end.

Definition check_env_root_shadow_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_provenance_summary env) (env_fns env).

Fixpoint store_safe_function_value_call_args_b
    (env : global_env) (args : list expr) : bool :=
  match args with
  | [] => true
  | EVar _ :: rest =>
      store_safe_function_value_call_args_b env rest
  | EFn fname :: rest =>
      match lookup_fn_b fname (env_fns env) with
      | Some callee =>
          check_fn_root_shadow_provenance_summary env callee &&
          store_safe_function_value_call_args_b env rest
      | None => false
      end
  | _ :: _ => false
  end.

Definition direct_call_target_expr (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ECall fname args => Some (fname, args, ECall fname args)
  | ECallExpr (EFn fname) args => Some (fname, args, ECall fname args)
  | _ => None
  end.

Definition direct_call_ready_expr_b (e : expr) : bool :=
  match direct_call_target_expr e with
  | Some (_, args, _) => preservation_ready_args_b args
  | None => false
  end.

Definition check_fn_root_shadow_direct_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_provenance_summary env fdef with
  | true => true
  | false =>
      match direct_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None => false
      end
  end.

Definition local_fn_value_call_target_expr
    (e : expr) : option (ident * list expr * expr) :=
  match e with
  | ELet m x T (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y && usage_eqb (ty_usage T) UUnrestricted
      then Some (fname, args, ELet m x T (EFn fname) (ECall fname args))
      else None
  | ELetInfer m x (EFn fname) (ECallExpr (EVar y) args) =>
      if ident_eqb x y
      then Some (fname, args, ELetInfer m x (EFn fname) (ECall fname args))
      else None
  | _ => None
  end.

Definition supported_non_type_generic_function_value_call_callee_ty_b
    (T : Ty) : bool :=
  match ty_core T with
  | TFn _ _ => true
  | TForall _ _ body =>
      match ty_core body with
      | TFn _ _ => true
      | _ => false
      end
  | _ => false
  end.

Definition check_supported_non_type_generic_function_value_call_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (callee : expr) : bool :=
  match callee with
  | EVar _ =>
      match infer_core_env_roots_shadow_safe env Ω n R Γ callee with
      | infer_ok (T_callee, _, _, _) =>
          supported_non_type_generic_function_value_call_callee_ty_b T_callee
      | infer_err _ => false
      end
  | _ => false
  end.

Definition check_fn_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_direct_call_provenance_summary env fdef with
  | true => true
  | false =>
      match local_fn_value_call_target_expr (fn_body fdef) with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_env_roots_shadow_safe env
                      (fn_with_body fdef synthetic_body)
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          end
      | None =>
          match fn_body fdef with
          | ECallExpr callee args =>
              preservation_ready_expr_b callee &&
              preservation_ready_args_b args &&
              check_supported_non_type_generic_function_value_call_expr
                (global_env_with_local_bounds env (fn_bounds fdef))
                (fn_outlives fdef)
                (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef)
                callee &&
              match infer_env_roots_shadow_safe env fdef
                      (initial_root_env_for_fn fdef) with
              | infer_ok (_, _, R_out, roots) =>
                  fn_params_roots_exclude_b (fn_params fdef) roots &&
                  fn_params_root_env_excludes_b (fn_params fdef) R_out
              | infer_err _ => false
              end
          | _ => false
          end
      end
  end.

Definition captured_call_target_expr
    (e : expr) : option (ident * list ident * list expr) :=
  match e with
  | ECallExpr (EMakeClosure fname captures) args =>
      Some (fname, captures, args)
  | _ => None
  end.

Definition args_free_vars_checker (args : list expr) : list ident :=
  args_local_store_names_with free_vars_expr args.

Definition local_captured_call_target_expr
    (e : expr)
    : option (ident * list ident * list expr * mutability * ident * Ty *
        expr * expr) :=
  match e with
  | ELet m x T (EMakeClosure fname captures) (ECallExpr (EVar y) args) =>
      if ident_eqb x y &&
         usage_eqb (ty_usage T) UUnrestricted &&
         negb (existsb (ident_eqb x) captures) &&
         negb (existsb (ident_eqb x) (args_free_vars_checker args)) &&
         negb (existsb (ident_eqb x) (args_local_store_names args))
      then
        let direct_body := ECallExpr (EMakeClosure fname captures) args in
        Some (fname, captures, args, m, x, T, direct_body,
          ELet m x T (EMakeClosure fname captures) direct_body)
      else None
  | _ => None
  end.

Definition check_fn_root_shadow_captured_callee_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  provenance_ready_expr_b (fn_body fdef) &&
  match infer_env_roots_shadow_safe env fdef
          (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)) with
  | infer_ok (_, _, R_out, roots) =>
      fn_params_roots_exclude_b (fn_params fdef ++ fn_captures fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef ++ fn_captures fdef) R_out
  | infer_err _ => false
  end.

Fixpoint capture_root_bound
    (R : root_env) (captures : list ident) (caps : list param)
    : option root_set :=
  match captures, caps with
  | [], [] => Some []
  | x :: captures', _ :: caps' =>
      match root_env_lookup x R, capture_root_bound R captures' caps' with
      | Some roots, Some rest => Some (root_set_union roots rest)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition callee_hidden_capture_args_disjoint_b
    (callee : fn_def) (args : list expr) : bool :=
  forallb
    (fun x =>
       negb (existsb (ident_eqb x) (args_local_store_names args)))
    (ctx_names (params_ctx (fn_captures callee))).

Fixpoint check_expr_root_shadow_captured_call_provenance_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      provenance_ready_expr_b e ||
      match direct_call_target_expr e with
      | Some (fname, args, synthetic_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              check_fn_root_shadow_provenance_summary env callee &&
              match infer_core_env_state_fuel_roots_shadow_safe
                      fuel env Ω n R Σ synthetic_body with
              | infer_ok _ => true
              | infer_err _ => false
              end
          end
      | None => false
      end ||
      match captured_call_target_expr e with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      Ω Σ captures (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  match capture_root_bound R captures (fn_captures callee) with
                  | Some _ =>
                      check_fn_root_shadow_captured_callee_provenance_summary
                        env callee
                  | None => false
                  end
              end
          end
      | None => false
      end ||
      match local_captured_call_target_expr e with
      | Some (fname, captures, args, m, x, T_hidden, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match root_env_lookup x R with
              | Some _ => false
              | None =>
                  match check_make_closure_captures_exact_sctx_with_env env
                          Ω Σ captures (fn_captures callee) with
                  | infer_err _ => false
                  | infer_ok _ =>
                      match capture_root_bound R captures
                              (fn_captures callee) with
                      | None => false
                      | Some _ =>
                          check_fn_root_shadow_captured_callee_provenance_summary
                            env callee &&
                          match
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ direct_body,
                            infer_core_env_state_fuel_roots_shadow_safe
                              fuel env Ω n R Σ e
                          with
	                          | infer_ok (T_direct, Σ_direct, R_direct, _),
	                            infer_ok (T_let, Σ_let, R_let, _) =>
	                              sctx_eqb Σ_direct Σ_let &&
	                              root_env_eqb R_direct R_let &&
	                              ty_compatible_b Ω T_direct T_let
                          | _, _ => false
                          end
                      end
                  end
              end
          end
      | None => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              provenance_ready_expr_b e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_captured_call_provenance_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_captured_call_provenance_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_captured_call_provenance_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_captured_call_provenance_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint non_function_value_ty_b (T : Ty) : bool :=
  match T with
  | MkTy _ (TFn _ _) => false
  | MkTy _ (TClosure _ _ _) => false
  | MkTy _ (TForall _ _ body) => non_function_value_ty_b body
  | MkTy _ (TTypeForall _ _ body) => non_function_value_ty_b body
  | _ => true
  end.

Fixpoint check_expr_root_shadow_store_safe_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      check_expr_root_shadow_captured_call_provenance_summary_fuel
        fuel env Ω n R Σ e ||
      match e with
      | ECallExpr callee args =>
          preservation_ready_args_b args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | _ => false
      end ||
      match e with
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      capture_ref_free_ty_b env T2 &&
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | _ => false
      end ||
      match e with
      | EIf e1 e2 e3 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T_cond, Σ1, R1, _) =>
              ty_core_eqb (ty_core T_cond) TBooleans &&
              provenance_ready_expr_b e1 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e2 &&
              check_expr_root_shadow_store_safe_summary_fuel
                fuel' env Ω n R1 Σ1 e3
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Fixpoint check_expr_root_shadow_store_safe_narrow_summary_fuel
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Σ : sctx) (e : expr) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
  match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
  | infer_err _ => false
  | infer_ok _ =>
      match e with
      | ECallExpr callee args =>
          store_safe_function_value_call_args_b env args &&
          check_supported_non_type_generic_function_value_call_expr
            env Ω n R (ctx_of_sctx Σ) callee
      | ELet m x T_hidden e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              ty_compatible_b Ω T1 T_hidden &&
              non_function_value_ty_b T_hidden &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T_hidden m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T_hidden Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T_hidden m Σ1) e2
                  end
              end
          end
      | ELetInfer m x e1 e2 =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel' env Ω n R Σ e1 with
          | infer_err _ => false
          | infer_ok (T1, Σ1, R1, roots1) =>
              non_function_value_ty_b T1 &&
              check_expr_root_shadow_store_safe_narrow_summary_fuel
                fuel' env Ω n R Σ e1 &&
              match root_env_lookup x R1 with
              | Some _ => false
              | None =>
                  roots_exclude_b x roots1 &&
                  root_env_excludes_b x R1 &&
                  match infer_core_env_state_fuel_roots_shadow_safe
                          fuel' env Ω n
                          (root_env_add x roots1 R1)
                          (sctx_add x T1 m Σ1) e2 with
                  | infer_err _ => false
                  | infer_ok (T2, Σ2, R2, roots2) =>
                      sctx_check_ok env x T1 Σ2 &&
                      roots_exclude_b x roots2 &&
                      root_env_excludes_b x (root_env_remove x R2) &&
                      check_expr_root_shadow_store_safe_narrow_summary_fuel
                        fuel' env Ω n
                        (root_env_add x roots1 R1)
                        (sctx_add x T1 m Σ1) e2
                  end
              end
          end
      | _ => false
      end
  end
  end.

Definition check_expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (R : root_env) (Γ : ctx) (e : expr) : bool :=
  check_expr_root_shadow_store_safe_narrow_summary_fuel
    10000 env Ω n R (sctx_of_ctx Γ) e.

Definition check_fn_root_shadow_captured_call_provenance_summary
    (env : global_env) (fdef : fn_def) : bool :=
  match check_fn_root_shadow_non_capturing_call_provenance_summary env fdef with
  | true => true
  | false =>
      (preservation_ready_expr_b (fn_body fdef) &&
       check_fn_root_shadow_captured_callee_provenance_summary env fdef) ||
      (match captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env fdef
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_out, roots) =>
                      fn_params_roots_exclude_b (fn_params fdef) roots &&
                      fn_params_root_env_excludes_b (fn_params fdef) R_out
                  | infer_err _ => false
                  end
              end
          end
      | None => false
      end ||
      (match infer_core_env_roots_shadow_safe env
                  (fn_outlives fdef)
                  (fn_lifetimes fdef)
                  (initial_root_env_for_fn fdef)
                  (fn_body_ctx fdef)
                  (fn_body fdef),
                infer_env_roots_shadow_safe env fdef
                  (initial_root_env_for_fn fdef) with
          | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
              check_expr_root_shadow_captured_call_provenance_summary
                env (fn_outlives fdef) (fn_lifetimes fdef)
                (initial_root_env_for_fn fdef)
                (fn_body_ctx fdef) (fn_body fdef) &&
              ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
              fn_params_roots_exclude_b (fn_params fdef) roots &&
              fn_params_root_env_excludes_b (fn_params fdef) R_out
          | _, _ => false
          end) ||
      match local_captured_call_target_expr (fn_body fdef) with
      | Some (fname, captures, args, m, x, T, direct_body, let_body) =>
          preservation_ready_args_b args &&
          match lookup_fn_b fname (env_fns env) with
          | None => false
          | Some callee =>
              callee_hidden_capture_args_disjoint_b callee args &&
              negb (existsb (ident_eqb x)
                (ctx_names (params_ctx (fn_captures callee)))) &&
              match check_make_closure_captures_exact_sctx_with_env env
                      (fn_outlives fdef)
                      (sctx_of_ctx (fn_body_ctx fdef))
                      captures
                      (fn_captures callee) with
              | infer_err _ => false
              | infer_ok _ =>
                  check_fn_root_shadow_captured_callee_provenance_summary
                    env callee &&
                  match infer_env_roots_shadow_safe env
                          (fn_with_body fdef direct_body)
                          (initial_root_env_for_fn fdef),
                        infer_env_roots_shadow_safe env
                          (fn_with_body fdef let_body)
                          (initial_root_env_for_fn fdef) with
                  | infer_ok (_, _, R_direct, roots_direct),
                    infer_ok (_, _, _, _) =>
                      fn_params_roots_exclude_b (fn_params fdef)
                        roots_direct &&
                      fn_params_root_env_excludes_b (fn_params fdef)
                        R_direct
                  | _, _ => false
                  end
              end
          end
      | None => false
      end)
  end.

Definition check_fn_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_provenance_summary env fdef ||
  (match direct_call_target_expr (fn_body fdef) with
   | Some (fname, args, synthetic_body) =>
       store_safe_function_value_call_args_b env args &&
       match lookup_fn_b fname (env_fns env) with
       | None => false
       | Some callee =>
           match infer_core_env_roots_shadow_safe env
                     (fn_outlives callee)
                     (fn_lifetimes callee)
                     (initial_root_env_for_fn callee)
                     (fn_body_ctx callee)
                     (fn_body callee),
                 infer_env_roots_shadow_safe env callee
                   (initial_root_env_for_fn callee),
                 infer_env_roots_shadow_safe env
                   (fn_with_body fdef synthetic_body)
                   (initial_root_env_for_fn fdef) with
           | infer_ok (T_callee, _, R_callee, roots_callee),
             infer_ok _,
             infer_ok (T_body, _, R_out, roots) =>
               check_expr_root_shadow_store_safe_narrow_summary
                 env (fn_outlives callee) (fn_lifetimes callee)
                 (initial_root_env_for_fn callee)
                 (fn_body_ctx callee) (fn_body callee) &&
               ty_compatible_b (fn_outlives callee) T_callee
                 (fn_ret callee) &&
               fn_params_roots_exclude_b (fn_params callee) roots_callee &&
               fn_params_root_env_excludes_b (fn_params callee) R_callee &&
               ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
               fn_params_roots_exclude_b (fn_params fdef) roots &&
               fn_params_root_env_excludes_b (fn_params fdef) R_out
           | _, _, _ => false
           end
       end
   | None => false
   end) ||
  match infer_core_env_roots_shadow_safe env
              (fn_outlives fdef)
              (fn_lifetimes fdef)
              (initial_root_env_for_fn fdef)
              (fn_body_ctx fdef)
              (fn_body fdef),
            infer_env_roots_shadow_safe env fdef
              (initial_root_env_for_fn fdef) with
  | infer_ok (T_body, _, R_out, roots), infer_ok _ =>
      check_expr_root_shadow_store_safe_narrow_summary
        env (fn_outlives fdef) (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (fn_body_ctx fdef) (fn_body fdef) &&
      ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) &&
      fn_params_roots_exclude_b (fn_params fdef) roots &&
      fn_params_root_env_excludes_b (fn_params fdef) R_out
  | _, _ => false
  end.

Definition check_env_root_shadow_captured_call_store_safe_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_store_safe_summary env)
    (env_fns env).

Definition check_env_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_direct_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_non_capturing_call_provenance_summary env)
    (env_fns env).

Definition check_env_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  forallb (check_fn_root_shadow_captured_call_provenance_summary env)
    (env_fns env).

Definition check_fn_ordinary_safety_gate
    (env : global_env) (fdef : fn_def) : bool :=
  check_fn_root_shadow_captured_call_provenance_summary env fdef.

Definition check_program_env (env : global_env) : bool :=
  forallb (fun f =>
    match infer_full_env env f with
    | infer_ok _ => check_fn_ordinary_safety_gate env f
    | infer_err _ => false
    end) (env_fns env).

Definition check_program_env_alpha (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  check_program_env (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated (env : global_env) : bool :=
  check_program_env_alpha env.

Definition check_program_env_alpha_elab (env : global_env) : bool :=
  global_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' => check_program_env env'
  | infer_err _ => false
  end.

Definition check_env_preservation_ready (env : global_env) : bool :=
  forallb (fun fdef => preservation_ready_expr_b (fn_body fdef))
    (env_fns env).

Definition check_program_env_alpha_validated_root_shadow (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_provenance_summary (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_direct_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_non_capturing_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  check_env_root_shadow_captured_call_provenance_summary
    (alpha_normalize_global_env env).

Definition check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    (env : global_env) : bool :=
  top_level_names_unique_b (alpha_normalize_global_env env) &&
  match infer_program_env_alpha_elab env with
  | infer_ok env' =>
      check_env_root_shadow_captured_call_provenance_summary env'
  | infer_err _ => false
  end.

Definition check_program_env_alpha_validated_root_shadow_provenance
    (env : global_env) : bool :=
  check_program_env_alpha_validated env &&
  (check_env_root_shadow_provenance_summary
     (alpha_normalize_global_env env) &&
   check_env_preservation_ready (alpha_normalize_global_env env)).

Definition infer_fn_env_end2end (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let R0 := initial_root_env_for_params (fn_params f ++ fn_captures f) in
  match infer_full_env_roots env f R0 with
  | infer_err err => infer_err err
  | infer_ok res =>
      if check_fn_root_shadow_captured_call_store_safe_summary env f
      then infer_ok res
      else infer_err ErrEndToEndSafetyGateFailed
  end.

Fixpoint infer_fns_env_end2end (env : global_env) (fns : list fn_def)
    : infer_result unit :=
  match fns with
  | [] => infer_ok tt
  | f :: rest =>
      match infer_fn_env_end2end env f with
      | infer_err err => infer_err (ErrInFunction (fn_name f) err)
      | infer_ok _ => infer_fns_env_end2end env rest
      end
  end.

Definition infer_program_env_end2end (env : global_env)
    : infer_result global_env :=
  let env_alpha := alpha_normalize_global_env env in
  if global_names_unique_b env_alpha then
    match infer_fns_env_end2end env_alpha (env_fns env_alpha) with
    | infer_err err => infer_err err
    | infer_ok _ => infer_ok env_alpha
    end
  else infer_err ErrGlobalNamesNotUnique.

Definition check_program_env_end2end (env : global_env) : bool :=
  match infer_program_env_end2end env with
  | infer_ok _ => true
  | infer_err _ => false
  end.

Definition ex_ready_gap_let_fn : fn_def :=
  MkFnDef (("ready_gap_let"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELetInfer MImmutable (("x"%string), 0)
      (ELit (LInt 1))
      EUnit) 0 [].

Definition ex_ready_gap_let_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_fn].

Example check_program_env_alpha_accepts_ready_gap_let :
  check_program_env_alpha ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_duplicate_fn_name_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_fn; ex_ready_gap_let_fn].

Example check_program_env_alpha_rejects_duplicate_fn_name :
  check_program_env_alpha ex_duplicate_fn_name_env = false.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_validated_root_shadow_rejects_ready_gap_let :
  check_program_env_alpha_validated_root_shadow ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

Example check_env_root_shadow_provenance_summary_accepts_elab_ready_gap_let :
  match infer_program_env_alpha_elab ex_ready_gap_let_env with
  | infer_ok env =>
      check_env_root_shadow_provenance_summary env
  | infer_err _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example preservation_ready_expr_b_rejects_ready_gap_let :
  preservation_ready_expr_b (fn_body ex_ready_gap_let_fn) = false.
Proof. vm_compute. reflexivity. Qed.

Example provenance_ready_expr_b_accepts_ready_gap_let :
  provenance_ready_expr_b (fn_body ex_ready_gap_let_fn) = true.
Proof. vm_compute. reflexivity. Qed.

Example infer_env_elab_ready_gap_let_annotates_body :
  infer_env_elab ex_ready_gap_let_env ex_ready_gap_let_fn =
  infer_ok
    (MkTy UUnrestricted TUnits,
     [],
     fn_with_body ex_ready_gap_let_fn
       (ELet MImmutable (("x"%string), 0)
         (MkTy UUnrestricted TIntegers)
         (ELit (LInt 1))
         EUnit)).
Proof. vm_compute. reflexivity. Qed.

Example check_env_preservation_ready_rejects_alpha_elab_ready_gap_let :
  match infer_program_env_alpha_elab ex_ready_gap_let_env with
  | infer_ok env => check_env_preservation_ready env
  | infer_err _ => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_elab_accepts_ready_gap_let :
  check_program_env_alpha_elab ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Example check_program_env_alpha_validated_root_shadow_provenance_rejects_ready_gap_let :
  check_program_env_alpha_validated_root_shadow_provenance ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

(* Ordinary-checker accepted core shapes that the safety validator rejects. *)

Definition ex_ready_gap_let_annotated_fn : fn_def :=
  MkFnDef (("ready_gap_let_annotated"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("x"%string), 0)
      (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      EUnit) 0 [].

Definition ex_ready_gap_let_annotated_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_let_annotated_fn].

Example ready_gap_matrix_annotated_let_checker_accepts :
  check_program_env_alpha ex_ready_gap_let_annotated_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_annotated_let_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_let_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_annotated_let_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_let_annotated_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_checker_accepts :
  check_program_env_alpha ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_let_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_infer_let_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_let_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_deref_borrow_fn : fn_def :=
  MkFnDef (("ready_gap_deref_borrow"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TIntegers)
    (ELet MImmutable (("x"%string), 0)
      (MkTy UUnrestricted TIntegers)
      (ELit (LInt 1))
      (EDeref (EBorrow RShared (PVar (("x"%string), 0))))) 0 [].

Definition ex_ready_gap_deref_borrow_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_ready_gap_deref_borrow_fn].

Example ready_gap_matrix_deref_borrow_checker_accepts :
  check_program_env_alpha ex_ready_gap_deref_borrow_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_deref_borrow_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_deref_borrow_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_deref_borrow_provenance_summary_accepts :
  check_program_env_alpha_validated_root_shadow_provenance_summary
    ex_ready_gap_deref_borrow_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_call_callee_fn : fn_def :=
  MkFnDef (("ready_gap_call_callee"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_ready_gap_direct_call_fn : fn_def :=
  MkFnDef (("ready_gap_direct_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ECall (("ready_gap_call_callee"%string), 0) []) 0 [].

Definition ex_ready_gap_direct_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_direct_call_fn].

Example ready_gap_matrix_direct_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_direct_call_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_direct_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_direct_call_direct_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_empty_capture_fn_value_accepts :
  infer_core_env ex_ready_gap_direct_call_env [] 0 []
    (EFn (("ready_gap_call_callee"%string), 0)) =
  infer_ok (fn_value_ty ex_ready_gap_call_callee_fn, []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_empty_capture_direct_call_accepts :
  infer_core_env ex_ready_gap_direct_call_env [] 0 []
    (ECall (("ready_gap_call_callee"%string), 0) []) =
  infer_ok (MkTy UUnrestricted TUnits, []).
Proof. vm_compute. reflexivity. Qed.

Definition ex_nonempty_capture_param : param :=
  MkParam MImmutable (("captured"%string), 0) (MkTy UUnrestricted TIntegers).

Definition ex_nonempty_capture_callee_fn : fn_def :=
  MkFnDef (("nonempty_capture_callee"%string), 0) 0 []
    [ex_nonempty_capture_param] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_nonempty_capture_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_nonempty_capture_callee_fn].

Example infer_core_env_nonempty_capture_fn_value_rejects :
  infer_core_env ex_nonempty_capture_env [] 0 []
    (EFn (("nonempty_capture_callee"%string), 0)) =
  infer_err ErrNotImplemented.
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_nonempty_capture_direct_call_rejects :
  infer_core_env ex_nonempty_capture_env [] 0 []
    (ECall (("nonempty_capture_callee"%string), 0) []) =
  infer_err ErrNotImplemented.
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_ty : Ty :=
  MkTy UUnrestricted (TRef (LVar 0) RShared (MkTy UUnrestricted TIntegers)).

Definition ex_shared_ref_capture_param : param :=
  MkParam MImmutable (("captured_ref"%string), 0) ex_shared_ref_capture_ty.

Definition ex_shared_ref_capture_callee_fn : fn_def :=
  MkFnDef (("shared_ref_capture_callee"%string), 0) 1 []
    [ex_shared_ref_capture_param] []
    (MkTy UUnrestricted TIntegers)
    (EDeref (EVar (("captured_ref"%string), 0))) 0 [].

Definition ex_shared_ref_capture_ctx : ctx :=
  [((("r"%string), 0), ex_shared_ref_capture_ty,
    MkBindingState false [], MImmutable)].

Definition ex_shared_ref_capture_env : global_env :=
  MkGlobalEnv [] [] [] [] [] [ex_shared_ref_capture_callee_fn].

Example infer_core_env_shared_ref_capture_accepts :
  infer_core_env ex_shared_ref_capture_env [] 1 ex_shared_ref_capture_ctx
    (EMakeClosure (("shared_ref_capture_callee"%string), 0)
      [(("r"%string), 0)]) =
  infer_ok
    (closure_value_ty_at (LVar 0) ex_shared_ref_capture_callee_fn
      [ex_shared_ref_capture_ty],
     ex_shared_ref_capture_ctx).
Proof. vm_compute. reflexivity. Qed.

Example exact_sctx_shared_ref_capture_still_rejects :
  check_make_closure_captures_exact_sctx ex_shared_ref_capture_env []
    (sctx_of_ctx ex_shared_ref_capture_ctx)
    [(("r"%string), 0)]
    [ex_shared_ref_capture_param] =
  infer_err (ErrNotAReference (TRef (LVar 0) RShared
    (MkTy UUnrestricted TIntegers))).
Proof. vm_compute. reflexivity. Qed.

Example exact_sctx_with_env_shared_ref_capture_accepts :
  check_make_closure_captures_exact_sctx_with_env ex_shared_ref_capture_env []
    (sctx_of_ctx ex_shared_ref_capture_ctx)
    [(("r"%string), 0)]
    [ex_shared_ref_capture_param] =
  infer_ok (LVar 0, [ex_shared_ref_capture_ty]).
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_ignore_callee_fn : fn_def :=
  MkFnDef (("shared_ref_capture_ignore_callee"%string), 0) 1 []
    [ex_shared_ref_capture_param] []
    (MkTy UUnrestricted TUnits)
    EUnit 0 [].

Definition ex_shared_ref_capture_direct_call_fn : fn_def :=
  MkFnDef (("shared_ref_capture_direct_call"%string), 0) 1 []
    [] [MkParam MImmutable (("r"%string), 0) ex_shared_ref_capture_ty]
    (MkTy UUnrestricted TUnits)
    (ECallExpr
      (EMakeClosure (("shared_ref_capture_ignore_callee"%string), 0)
        [(("r"%string), 0)])
      []) 0 [].

Definition ex_shared_ref_capture_direct_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_shared_ref_capture_ignore_callee_fn;
     ex_shared_ref_capture_direct_call_fn].

Example shared_ref_capture_direct_call_checker_accepts :
  check_program_env_alpha ex_shared_ref_capture_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example shared_ref_capture_direct_call_sidecar_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_shared_ref_capture_direct_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_shared_ref_capture_local_let_call_fn : fn_def :=
  MkFnDef (("shared_ref_capture_local_let_call"%string), 0) 1 []
    [] [MkParam MImmutable (("r"%string), 0) ex_shared_ref_capture_ty]
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (closure_value_ty_at (LVar 0) ex_shared_ref_capture_ignore_callee_fn
        [ex_shared_ref_capture_ty])
      (EMakeClosure (("shared_ref_capture_ignore_callee"%string), 0)
        [(("r"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_shared_ref_capture_local_let_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_shared_ref_capture_ignore_callee_fn;
     ex_shared_ref_capture_local_let_call_fn].

Example shared_ref_capture_local_let_call_checker_accepts :
  check_program_env_alpha ex_shared_ref_capture_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example shared_ref_capture_local_let_call_sidecar_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_shared_ref_capture_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_call_expr : expr :=
  ELet MImmutable (("cap"%string), 0)
    (MkTy UUnrestricted TIntegers)
    (ELit (LInt 1))
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      []).

Definition ex_ready_gap_captured_closure_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    ex_ready_gap_captured_closure_call_expr 0 [].

Definition ex_ready_gap_captured_closure_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_nonempty_capture_callee_fn; ex_ready_gap_captured_closure_call_fn].

Example ready_gap_matrix_captured_closure_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_captured_closure_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_direct_call_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_direct_param_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_direct_param_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      []) 0 [].

Definition ex_ready_gap_captured_closure_direct_param_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_direct_param_call_fn].

Example ready_gap_matrix_captured_closure_direct_param_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_direct_param_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_call_captured_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_direct_param_if_call_expr : expr :=
  EIf (ELit (LBool true))
    (ECallExpr
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      [])
    EUnit.

Definition ex_ready_gap_captured_closure_direct_param_if_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_direct_param_if_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    ex_ready_gap_captured_closure_direct_param_if_call_expr 0 [].

Definition ex_ready_gap_captured_closure_direct_param_if_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_direct_param_if_call_fn].

Example ready_gap_matrix_captured_closure_direct_param_if_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_direct_param_if_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_if_call_helper_accepts :
  check_expr_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_if_call_env
    (fn_outlives ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_lifetimes ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (initial_root_env_for_fn
      ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_body_ctx ex_ready_gap_captured_closure_direct_param_if_call_fn)
    (fn_body ex_ready_gap_captured_closure_direct_param_if_call_fn) = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_direct_param_if_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_direct_param_if_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_local_let_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_local_let_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (closure_value_ty ex_nonempty_capture_callee_fn
        [MkTy UUnrestricted TIntegers])
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_captured_closure_local_let_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_local_let_call_fn].

Example ready_gap_matrix_captured_closure_local_let_call_checker_accepts :
  check_program_env_alpha
    ex_ready_gap_captured_closure_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_direct_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_local_let_call_captured_summary_accepts :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_captured_closure_infer_local_let_call_fn : fn_def :=
  MkFnDef (("ready_gap_captured_closure_infer_local_let_call"%string), 0)
    0 [] [] [MkParam MImmutable (("cap"%string), 0)
      (MkTy UUnrestricted TIntegers)]
    (MkTy UUnrestricted TUnits)
    (ELetInfer MImmutable (("g"%string), 0)
      (EMakeClosure (("nonempty_capture_callee"%string), 0)
        [(("cap"%string), 0)])
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_captured_closure_infer_local_let_call_env
    : global_env :=
  MkGlobalEnv [] [] [] []
    []
    [ex_nonempty_capture_callee_fn;
     ex_ready_gap_captured_closure_infer_local_let_call_fn].

Example ready_gap_matrix_captured_closure_infer_local_let_call_elab_checker_accepts :
  check_program_env_alpha_elab
    ex_ready_gap_captured_closure_infer_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_infer_local_let_call_original_summary_rejects :
  check_program_env_alpha_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_infer_local_let_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_captured_closure_infer_local_let_call_elab_summary_accepts :
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
    ex_ready_gap_captured_closure_infer_local_let_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_make_closure_preservation_ready_rejects :
  preservation_ready_expr_b
    (EMakeClosure (("nonempty_capture_callee"%string), 0)
      [(("cap"%string), 0)]) = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_make_closure_provenance_ready_rejects :
  provenance_ready_expr_b
    (EMakeClosure (("nonempty_capture_callee"%string), 0)
      [(("cap"%string), 0)]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_call_expr_fn : fn_def :=
  MkFnDef (("ready_gap_call_expr"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ECallExpr (EFn (("ready_gap_call_callee"%string), 0)) []) 0 [].

Definition ex_ready_gap_call_expr_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_call_expr_fn].

Example ready_gap_matrix_call_expr_checker_accepts :
  check_program_env_alpha ex_ready_gap_call_expr_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_call_expr_validator_rejects :
  check_program_env_alpha_validated_root_shadow_provenance
    ex_ready_gap_call_expr_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_call_expr_direct_call_summary_accepts :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_call_expr_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_function_value_call_fn : fn_def :=
  MkFnDef (("ready_gap_function_value_call"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (fn_value_ty ex_ready_gap_call_callee_fn)
      (EFn (("ready_gap_call_callee"%string), 0))
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_function_value_call_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ex_ready_gap_call_callee_fn; ex_ready_gap_function_value_call_fn].

Example ready_gap_matrix_function_value_call_checker_accepts :
  check_program_env_alpha ex_ready_gap_function_value_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_direct_call_summary_rejects :
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
    ex_ready_gap_function_value_call_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_non_capturing_summary_accepts :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_function_value_call_env = true.
Proof. vm_compute. reflexivity. Qed.

Definition ex_ready_gap_function_value_call_affine_annotated_fn : fn_def :=
  MkFnDef (("ready_gap_function_value_call_affine_annotated"%string), 0) 0 [] [] []
    (MkTy UUnrestricted TUnits)
    (ELet MImmutable (("g"%string), 0)
      (MkTy UAffine (ty_core (fn_value_ty ex_ready_gap_call_callee_fn)))
      (EFn (("ready_gap_call_callee"%string), 0))
      (ECallExpr (EVar (("g"%string), 0)) [])) 0 [].

Definition ex_ready_gap_function_value_call_affine_annotated_env : global_env :=
  MkGlobalEnv [] [] [] [] []
    [ ex_ready_gap_call_callee_fn
    ; ex_ready_gap_function_value_call_affine_annotated_fn
    ].

Example ready_gap_matrix_function_value_call_affine_annotation_checker_rejects :
  check_program_env_alpha
    ex_ready_gap_function_value_call_affine_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Example ready_gap_matrix_function_value_call_affine_annotation_non_capturing_summary_rejects :
  check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary
    ex_ready_gap_function_value_call_affine_annotated_env = false.
Proof. vm_compute. reflexivity. Qed.

Definition ex_struct_split : struct_def :=
  MkStructDef ("Split"%string) 0 0 []
    [ MkFieldDef ("x"%string) MImmutable (MkTy UAffine TIntegers)
    ; MkFieldDef ("y"%string) MImmutable (MkTy UUnrestricted TBooleans)
    ].

Definition ex_env_split : global_env :=
  MkGlobalEnv [ex_struct_split] [] [] [] [] [].

Definition ex_split_ty : Ty :=
  MkTy UAffine (TStruct ("Split"%string) [] []).

Definition ex_split_ctx : ctx :=
  [((("p"%string), 0), ex_split_ty, binding_state_of_bool false, MMutable)].

Definition ex_split_ctx_x_moved : ctx :=
  [((("p"%string), 0), ex_split_ty, MkBindingState false [["x"%string]], MMutable)].

Example auto_drop_live_paths_affine_struct_field :
  auto_drop_live_paths ex_env_split (("p"%string), 0) ex_split_ty ex_split_ctx =
  [["x"%string]].
Proof. vm_compute. reflexivity. Qed.

Example auto_drop_live_paths_affine_struct_moved_field_skipped :
  auto_drop_live_paths ex_env_split (("p"%string), 0) ex_split_ty ex_split_ctx_x_moved =
  [].
Proof. vm_compute. reflexivity. Qed.

Example auto_drop_paths_linear_not_generated :
  auto_drop_paths_for_ty ex_env_split (MkTy ULinear TIntegers) = [].
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_struct_instance_usage_after_args :
  infer_core_env
    (MkGlobalEnv
      [MkStructDef ("Box"%string) 0 1 []
        [MkFieldDef ("value"%string) MImmutable (MkTy UAffine (TParam 0))]]
      [] [] [] [] [])
    [] 0 []
    (EStruct ("Box"%string) [] [MkTy UAffine TIntegers]
      [(("value"%string), ELit (LInt 1))]) =
  infer_ok
    (MkTy UAffine (TStruct ("Box"%string) [] [MkTy UAffine TIntegers]), []).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_moved_field_sibling_available :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EPlace (PField (PVar (("p"%string), 0)) ("y"%string)))) =
  infer_ok (MkTy UUnrestricted TBooleans, ex_split_ctx_x_moved).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_moved_field_blocks_parent_borrow :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RShared (PVar (("p"%string), 0)))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_replace_rejects_moved_field :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (ELetInfer MImmutable (("old"%string), 0)
        (EReplace (PField (PVar (("p"%string), 0)) ("x"%string)) (ELit (LInt 1)))
        (EBorrow RShared (PVar (("p"%string), 0))))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example infer_core_env_assign_rejects_moved_field :
  infer_core_env ex_env_split [] 0 ex_split_ctx
    (ELetInfer MImmutable (("tmp"%string), 0)
      (EPlace (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EAssign (PField (PVar (("p"%string), 0)) ("x"%string)) (ELit (LInt 1)))) =
  infer_err (ErrAlreadyConsumed (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

Example borrow_check_env_sibling_fields_do_not_conflict :
  borrow_check_env ex_env_split [] ex_split_ctx
    (ELetInfer MImmutable (("b"%string), 0)
      (EBorrow RShared (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RUnique (PField (PVar (("p"%string), 0)) ("y"%string)))) =
  infer_ok [PBMut (("p"%string), 0) [("y"%string)]].
Proof. vm_compute. reflexivity. Qed.

Example borrow_check_env_prefix_fields_conflict :
  borrow_check_env ex_env_split [] ex_split_ctx
    (ELetInfer MImmutable (("b"%string), 0)
      (EBorrow RShared (PField (PVar (("p"%string), 0)) ("x"%string)))
      (EBorrow RUnique (PVar (("p"%string), 0)))) =
  infer_err (ErrBorrowConflict (("p"%string), 0)).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Direct variant (no alpha renaming) — for differential testing only   *)
(* ------------------------------------------------------------------ *)

(* infer_direct skips alpha_rename_for_infer and calls infer_core directly.
   If the parser's de Bruijn indexing is correct, infer_direct fenv f and
   infer fenv f should always agree.  Run both at development time to
   validate that alpha renaming is indeed a no-op. *)
Definition infer_direct (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core fenv Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_b (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

(* ------------------------------------------------------------------ *)
(* Surface closure elaboration                                          *)
(* ------------------------------------------------------------------ *)

Inductive raw_expr : Type :=
| RawUnit : raw_expr
| RawLit : literal -> raw_expr
| RawVar : ident -> raw_expr
| RawFn : ident -> raw_expr
| RawPlace : place -> raw_expr
| RawLet : mutability -> ident -> Ty -> raw_expr -> raw_expr -> raw_expr
| RawLetInfer : mutability -> ident -> raw_expr -> raw_expr -> raw_expr
| RawCall : ident -> list raw_expr -> raw_expr
| RawCallGeneric : ident -> list Ty -> list raw_expr -> raw_expr
| RawCallExpr : raw_expr -> list raw_expr -> raw_expr
| RawStruct : string -> list lifetime -> list Ty -> list (string * raw_expr) -> raw_expr
| RawEnum : string -> string -> list lifetime -> list Ty -> list raw_expr -> raw_expr
| RawMatch : raw_expr -> list (string * list ident * raw_expr) -> raw_expr
| RawReplace : place -> raw_expr -> raw_expr
| RawAssign : place -> raw_expr -> raw_expr
| RawBorrow : ref_kind -> place -> raw_expr
| RawDeref : raw_expr -> raw_expr
| RawDrop : raw_expr -> raw_expr
| RawIf : raw_expr -> raw_expr -> raw_expr -> raw_expr
| RawClosure : list ident -> list param -> Ty -> raw_expr -> raw_expr
| RawCore : expr -> raw_expr.

Record raw_fn_def : Type := MkRawFnDef {
  raw_fn_name      : ident;
  raw_fn_lifetimes : nat;
  raw_fn_outlives  : outlives_ctx;
  raw_fn_params    : list param;
  raw_fn_ret       : Ty;
  raw_fn_body      : raw_expr;
  raw_fn_type_params : nat;
  raw_fn_bounds    : list trait_bound
}.

Definition fn_stub_of_raw (f : raw_fn_def) : fn_def :=
  MkFnDef (raw_fn_name f) (raw_fn_lifetimes f) (raw_fn_outlives f)
    [] (raw_fn_params f) (raw_fn_ret f) EUnit
    (raw_fn_type_params f) (raw_fn_bounds f).

Definition append_env_fns (env : global_env) (fns : list fn_def) : global_env :=
  MkGlobalEnv (env_structs env) (env_enums env) (env_traits env) (env_impls env)
    (env_local_bounds env) (env_fns env ++ fns).

Fixpoint closure_elab_suffix (idx : nat) : string :=
  match idx with
  | O => EmptyString
  | S idx' => String.append "_"%string (closure_elab_suffix idx')
  end.

Definition closure_elab_name (idx : nat) : ident :=
  (String.append "__facet_closure"%string (closure_elab_suffix idx), 0).

Definition generic_fn_value_wrapper_name (idx : nat) : ident :=
  (String.append "__facet_generic_fn_value"%string (closure_elab_suffix idx), 0).

Fixpoint wrapper_params_from_tys_from
    (idx : nat) (tys : list Ty) : list param :=
  match tys with
  | [] => []
  | T :: rest =>
      MkParam MImmutable ("__facet_generic_arg"%string, idx) T ::
      wrapper_params_from_tys_from (S idx) rest
  end.

Definition wrapper_params_from_tys (tys : list Ty) : list param :=
  wrapper_params_from_tys_from 0 tys.

Fixpoint expr_vars_of_params (ps : list param) : list expr :=
  match ps with
  | [] => []
  | p :: rest => EVar (param_name p) :: expr_vars_of_params rest
  end.

Definition infer_fn_value_type_args_expected
    (fdef : fn_def) (expected : option Ty) : option (list Ty * list Ty * Ty) :=
  match expected with
  | Some (MkTy _ (TFn param_tys ret)) =>
      match infer_call_type_args_expected fdef param_tys (Some ret) with
      | Some type_args => Some (type_args, param_tys, ret)
      | None => None
      end
  | _ => None
  end.

Definition auto_drop_ret_name (idx : nat) : ident :=
  ("__facet_auto_drop_ret"%string, idx).

Definition auto_drop_tmp_name (idx : nat) : ident :=
  ("__facet_auto_drop"%string, idx).

Fixpoint place_of_path_from (base : place) (p : field_path) : place :=
  match p with
  | [] => base
  | field :: rest => place_of_path_from (PField base field) rest
  end.

Definition place_of_field_path (x : ident) (p : field_path) : place :=
  place_of_path_from (PVar x) p.

Fixpoint wrap_auto_drop_expr
    (x : ident) (paths : list field_path) (ret : expr) (next : nat)
    : expr * nat :=
  match paths with
  | [] => (ret, next)
  | path :: rest =>
      let tmp := auto_drop_tmp_name next in
      let '(tail, next') := wrap_auto_drop_expr x rest ret (S next) in
      (ELet MImmutable tmp (MkTy UUnrestricted TUnits)
        (EDrop (EPlace (place_of_field_path x path))) tail, next')
  end.

Definition wrap_let_body_auto_drops
    (env : global_env) (x : ident) (T : Ty) (Σ_body : sctx)
    (body_ty : Ty) (body : expr) (next : nat) : expr * nat :=
  match auto_drop_live_paths env x T Σ_body with
  | [] => (body, next)
  | paths =>
      let ret := auto_drop_ret_name next in
      let '(tail, next') := wrap_auto_drop_expr x paths (EVar ret) (S next) in
      (ELet MImmutable ret body_ty body tail, next')
  end.

Definition closure_elab_capture_param
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (x : ident)
    : infer_result param :=
  match sctx_lookup x Σ with
  | None => infer_err (ErrUnknownVar x)
  | Some (T, st) =>
      if negb (binding_available_b st [])
      then infer_err (ErrAlreadyConsumed x)
      else
      match sctx_lookup_mut x Σ with
      | Some MImmutable =>
          if usage_eqb (ty_usage T) UUnrestricted
          then
            if capture_ref_free_ty_b env T
            then infer_ok (MkParam MImmutable x T)
            else
              match T with
              | MkTy _ (TRef _ RShared _) => infer_ok (MkParam MImmutable x T)
              | _ => infer_err (ErrNotAReference (ty_core T))
              end
          else infer_err (ErrUsageMismatch (ty_usage T) UUnrestricted)
      | Some MMutable => infer_err (ErrNotMutable x)
      | None => infer_err (ErrUnknownVar x)
      end
  end.

Fixpoint closure_elab_capture_params
    (env : global_env) (Ω : outlives_ctx) (Σ : sctx) (captures : list ident)
    : infer_result (list param) :=
  match captures with
  | [] => infer_ok []
  | x :: xs =>
      match closure_elab_capture_param env Ω Σ x with
      | infer_err err => infer_err err
      | infer_ok p =>
          match closure_elab_capture_params env Ω Σ xs with
          | infer_err err => infer_err err
          | infer_ok ps => infer_ok (p :: ps)
          end
      end
  end.

Definition infer_elaborated_expr_state
    (fuel : nat) (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (e : expr) : infer_result sctx :=
  match infer_core_env_state_fuel fuel env Ω n Σ e with
  | infer_err err => infer_err err
  | infer_ok (_, Σ') => infer_ok Σ'
  end.

Fixpoint elaborate_raw_expr_fuel
    (fuel : nat) (expected : option Ty)
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (Σ : sctx) (next : nat) (e : raw_expr)
    : infer_result (expr * sctx * list fn_def * nat) :=
  let finish env' e' extras next' :=
    match infer_elaborated_expr_state fuel env' Ω n Σ e' with
    | infer_err err => infer_err err
    | infer_ok Σ' => infer_ok (e', Σ', extras, next')
    end in
  let fix go_args fuel0 env0 Σ0 next0 args :=
    match args with
    | [] => infer_ok ([], Σ0, [], next0)
    | a :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  let fix go_args_expected fuel0 env0 Σ0 next0 args params :=
    match args, params with
    | [], [] => infer_ok ([], Σ0, [], next0)
    | a :: rest, p :: ps =>
        match elaborate_raw_expr_fuel fuel0 (Some (param_ty p)) env0 Ω n Σ0 next0 a with
        | infer_err err => infer_err err
        | infer_ok (a', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_args_expected fuel0 env1 Σ1 next1 rest ps with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok (a' :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    | _, _ => infer_err ErrArityMismatch
    end in
  let fix infer_arg_tys_state fuel0 env0 Σ0 args :=
    match args with
    | [] => infer_ok ([], Σ0)
    | a :: rest =>
        match infer_core_env_state_fuel fuel0 env0 Ω n Σ0 a with
        | infer_err err => infer_err err
        | infer_ok (T, Σ1) =>
            match infer_arg_tys_state fuel0 env0 Σ1 rest with
            | infer_err err => infer_err err
            | infer_ok (Ts, Σ2) => infer_ok (T :: Ts, Σ2)
            end
        end
    end in
  let fix go_fields fuel0 env0 Σ0 next0 fields :=
    match fields with
    | [] => infer_ok ([], Σ0, [], next0)
    | (fname, fe) :: rest =>
        match elaborate_raw_expr_fuel fuel0 None env0 Ω n Σ0 next0 fe with
        | infer_err err => infer_err err
        | infer_ok (fe', Σ1, extras1, next1) =>
            let env1 := append_env_fns env0 extras1 in
            match go_fields fuel0 env1 Σ1 next1 rest with
            | infer_err err => infer_err err
            | infer_ok (rest', Σ2, extras2, next2) =>
                infer_ok ((fname, fe') :: rest', Σ2, extras1 ++ extras2, next2)
            end
        end
    end in
  match fuel with
  | O => infer_err ErrNotImplemented
  | S fuel' =>
      match e with
      | RawUnit => finish env EUnit [] next
      | RawLit lit => finish env (ELit lit) [] next
      | RawVar x => finish env (EVar x) [] next
      | RawFn fname =>
          match lookup_fn_b fname (env_fns env) with
          | None => finish env (EFn fname) [] next
          | Some fdef =>
              if Nat.eqb (fn_type_params fdef) 0
              then finish env (EFn fname) [] next
              else
                if negb (no_captures_b fdef)
                then infer_err ErrNotImplemented
                else
                  match expected with
                  | Some T_expected =>
                      if ty_compatible_b Ω (fn_value_ty fdef) T_expected
                      then finish env (EFn fname) [] next
                      else if negb (Nat.eqb (fn_lifetimes fdef) 0)
                      then infer_err ErrTypeArgInferenceFailed
                      else
                        match infer_fn_value_type_args_expected fdef expected with
                        | None => infer_err ErrTypeArgInferenceFailed
                        | Some (type_args, param_tys, ret) =>
                            match check_struct_bounds env (fn_bounds fdef) type_args with
                            | Some err => infer_err err
                            | None =>
                                let wrapper_name := generic_fn_value_wrapper_name next in
                                let wrapper_params := wrapper_params_from_tys param_tys in
                                let wrapper_body :=
                                  ECallGeneric fname type_args
                                    (expr_vars_of_params wrapper_params) in
                                let wrapper :=
                                  MkFnDef wrapper_name 0 [] [] wrapper_params ret
                                    wrapper_body 0 [] in
                                let env' := append_env_fns env [wrapper] in
                                finish env' (EFn wrapper_name) [wrapper] (S next)
                            end
                        end
                  | None => infer_err ErrTypeArgInferenceFailed
                  end
          end
      | RawPlace p => finish env (EPlace p) [] next
      | RawCore ecore => finish env ecore [] next
      | RawBorrow rk p => finish env (EBorrow rk p) [] next
      | RawLet m x T e1 e2 =>
          match elaborate_raw_expr_fuel fuel' (Some T) env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                      (sctx_add x T m Σ1) next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', Σ2, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  let env2 := append_env_fns env extras in
                  match infer_core_env_state_fuel fuel' env2 Ω n
                          (sctx_add x T m Σ1) e2' with
                  | infer_err err => infer_err err
                  | infer_ok (T2, _) =>
                      let '(e2'', next3) :=
                        wrap_let_body_auto_drops env2 x T Σ2 T2 e2' next2 in
                      let e' := ELet m x T e1' e2'' in
                      finish env2 e' extras next3
                  end
              end
          end
      | RawLetInfer m x e1 e2 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              match infer_core_env_state_fuel fuel' (append_env_fns env extras1)
                      Ω n Σ e1' with
              | infer_err err => infer_err err
              | infer_ok (T1, _) =>
                  let env1 := append_env_fns env extras1 in
                  match elaborate_raw_expr_fuel fuel' expected env1 Ω n
                          (sctx_add x T1 m Σ1) next1 e2 with
                  | infer_err err => infer_err err
                  | infer_ok (e2', Σ2, extras2, next2) =>
                      let extras := extras1 ++ extras2 in
                      let env2 := append_env_fns env extras in
                      match infer_core_env_state_fuel fuel' env2 Ω n
                              (sctx_add x T1 m Σ1) e2' with
                      | infer_err err => infer_err err
                      | infer_ok (T2, _) =>
                          let '(e2'', next3) :=
                            wrap_let_body_auto_drops env2 x T1 Σ2 T2 e2' next2 in
                          let e' := ELet m x T1 e1' e2'' in
                          finish env2 e' extras next3
                      end
                  end
              end
          end
      | RawCall fname args =>
          let infer_plain :=
            match go_args fuel' env Σ next args with
            | infer_err err => infer_err err
            | infer_ok (args', _, extras, next') =>
                let env' := append_env_fns env extras in
                match lookup_fn_b fname (env_fns env') with
                | None => finish env' (ECall fname args') extras next'
                | Some fdef =>
                    if Nat.eqb (fn_type_params fdef) 0
                    then finish env' (ECall fname args') extras next'
                    else
                      match infer_arg_tys_state fuel' env' Σ args' with
                      | infer_err err => infer_err err
                      | infer_ok (arg_tys, _) =>
                          match infer_call_type_args_expected fdef arg_tys expected with
                          | None => infer_err ErrTypeArgInferenceFailed
                          | Some type_args =>
                              match check_struct_bounds env' (fn_bounds fdef) type_args with
                              | Some err => infer_err err
                              | None =>
                                  finish env' (ECallGeneric fname type_args args')
                                    extras next'
                              end
                          end
                      end
                end
            end in
          match lookup_fn_b fname (env_fns env) with
          | Some fdef =>
	              if Nat.eqb (fn_type_params fdef) 0
              then
                match go_args_expected fuel' env Σ next args (fn_params fdef) with
                | infer_err _ => infer_plain
                | infer_ok (args', _, extras, next') =>
                    finish (append_env_fns env extras)
                      (ECall fname args') extras next'
                end
              else infer_plain
          | None => infer_plain
          end
      | RawCallGeneric fname type_args args =>
          match go_args fuel' env Σ next args with
          | infer_err err => infer_err err
          | infer_ok (args', _, extras, next') =>
              finish (append_env_fns env extras)
                (ECallGeneric fname type_args args') extras next'
          end
      | RawCallExpr callee args =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next callee with
          | infer_err err => infer_err err
          | infer_ok (callee', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match go_args fuel' env1 Σ1 next1 args with
              | infer_err err => infer_err err
              | infer_ok (args', _, extras2, next2) =>
                  let extras := extras1 ++ extras2 in
                  finish (append_env_fns env extras)
                    (ECallExpr callee' args') extras next2
              end
          end
      | RawStruct sname lts tys fields =>
          match go_fields fuel' env Σ next fields with
          | infer_err err => infer_err err
          | infer_ok (fields', _, extras, next') =>
              finish (append_env_fns env extras)
                (EStruct sname lts tys fields') extras next'
          end
      | RawEnum enum_name variant_name lts tys payloads =>
          match go_args fuel' env Σ next payloads with
          | infer_err err => infer_err err
          | infer_ok (payloads', _, extras, next') =>
              finish (append_env_fns env extras)
                (EEnum enum_name variant_name lts tys payloads') extras next'
          end
      | RawMatch scrut branches =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next scrut with
          | infer_err err => infer_err err
          | infer_ok (scrut', Σ1, extras_scrut, next1) =>
              let env1 := append_env_fns env extras_scrut in
              match infer_core_env_state_fuel fuel' env1 Ω n Σ scrut' with
              | infer_err err => infer_err err
              | infer_ok (T_scrut, _) =>
                  match ty_core T_scrut with
                  | TEnum enum_name lts args =>
                      match lookup_enum enum_name env1 with
                      | None => infer_err (ErrEnumNotFound enum_name)
                      | Some edef =>
                          let fix go_branches env0 next0 branches0 :=
                            match branches0 with
                            | [] => infer_ok ([], [], next0)
                            | (variant_name, binders, e_branch) :: rest =>
                                match lookup_enum_variant variant_name (enum_variants edef) with
	                                | None => infer_err (ErrVariantNotFound variant_name)
	                                | Some vdef =>
	                                    match match_payload_params binders lts args vdef with
                                    | infer_err err => infer_err err
                                    | infer_ok ps =>
                                        if params_names_nodup_b ps &&
                                           ctx_lookup_params_none_b ps Σ1
                                        then
                                        match elaborate_raw_expr_fuel fuel' expected env0 Ω n
                                                (sctx_add_params ps Σ1) next0 e_branch with
                                        | infer_err err => infer_err err
                                        | infer_ok (e_branch', _, extras_branch, next_branch) =>
                                            let env_branch := append_env_fns env0 extras_branch in
                                            match go_branches env_branch next_branch rest with
                                            | infer_err err => infer_err err
                                            | infer_ok (rest', extras_rest, next_rest) =>
                                                infer_ok ((variant_name, binders, e_branch') :: rest',
                                                          extras_branch ++ extras_rest, next_rest)
                                            end
                                        end
	                                        else infer_err ErrContextCheckFailed
	                                    end
	                                end
                            end
                          in
                          match go_branches env1 next1 branches with
                          | infer_err err => infer_err err
                          | infer_ok (branches', extras_branches, next') =>
                              let extras := extras_scrut ++ extras_branches in
                              let env' := append_env_fns env extras in
                              match infer_core_env_state_fuel_elab fuel env' Ω n Σ
                                      (EMatch scrut' branches') with
                              | infer_err err => infer_err err
                              | infer_ok (_, Σ', e_match') =>
                                  infer_ok (e_match', Σ', extras, next')
                              end
                          end
                      end
                  | c => infer_err (ErrNotAnEnum c)
                  end
              end
          end
      | RawReplace p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EReplace p e1') extras next'
          end
      | RawAssign p e1 =>
          let expected_rhs :=
            match infer_place_sctx env Σ p with
            | infer_ok T => Some T
            | infer_err _ => None
            end in
          match elaborate_raw_expr_fuel fuel' expected_rhs env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EAssign p e1') extras next'
          end
      | RawDeref e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDeref e1') extras next'
          end
      | RawDrop e1 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', _, extras, next') =>
              finish (append_env_fns env extras) (EDrop e1') extras next'
          end
      | RawIf e1 e2 e3 =>
          match elaborate_raw_expr_fuel fuel' None env Ω n Σ next e1 with
          | infer_err err => infer_err err
          | infer_ok (e1', Σ1, extras1, next1) =>
              let env1 := append_env_fns env extras1 in
              match elaborate_raw_expr_fuel fuel' expected env1 Ω n Σ1 next1 e2 with
              | infer_err err => infer_err err
              | infer_ok (e2', _, extras2, next2) =>
                  let env2 := append_env_fns env1 extras2 in
                  match elaborate_raw_expr_fuel fuel' expected env2 Ω n Σ1 next2 e3 with
                  | infer_err err => infer_err err
                  | infer_ok (e3', _, extras3, next3) =>
                      let extras := extras1 ++ extras2 ++ extras3 in
                      finish (append_env_fns env extras)
                        (EIf e1' e2' e3') extras next3
                  end
              end
          end
      | RawClosure captures params ret body =>
          match closure_elab_capture_params env Ω Σ captures with
          | infer_err err => infer_err err
          | infer_ok cap_params =>
              let fname := closure_elab_name next in
              let body_ctx := sctx_of_ctx (params_ctx (cap_params ++ params)) in
              match elaborate_raw_expr_fuel fuel' (Some ret) env Ω n body_ctx (S next) body with
              | infer_err err => infer_err err
              | infer_ok (body', _, body_extras, next') =>
                  let fdef := MkFnDef fname n Ω cap_params params ret body' 0 [] in
                  let env_with_closure := append_env_fns env (body_extras ++ [fdef]) in
                  match infer_full_env env_with_closure fdef with
                  | infer_err err => infer_err err
                  | infer_ok _ =>
                      finish env_with_closure (EMakeClosure fname captures)
                        (body_extras ++ [fdef]) next'
                  end
              end
          end
      end
  end.

Definition elaborate_raw_expr
    (env : global_env) (Ω : outlives_ctx) (n : nat) (Σ : sctx)
    (e : raw_expr) : infer_result (expr * list fn_def) :=
  match elaborate_raw_expr_fuel 10000 None env Ω n Σ 0 e with
  | infer_err err => infer_err err
  | infer_ok (e', _, extras, _) => infer_ok (e', extras)
  end.

Definition raw_fn_body_ctx (f : raw_fn_def) : ctx :=
  params_ctx (raw_fn_params f).

Fixpoint elaborate_raw_fns_fuel
    (fuel : nat) (base_env : global_env) (done : list fn_def)
    (next : nat) (fs : list raw_fn_def)
    : infer_result (list fn_def * nat) :=
  match fs with
  | [] => infer_ok ([], next)
  | f :: rest =>
      let env0 := append_env_fns base_env done in
      let body_env := global_env_with_local_bounds env0 (raw_fn_bounds f) in
      match elaborate_raw_expr_fuel fuel (Some (raw_fn_ret f))
              body_env (raw_fn_outlives f)
              (raw_fn_lifetimes f) (sctx_of_ctx (raw_fn_body_ctx f))
              next (raw_fn_body f) with
      | infer_err err => infer_err err
      | infer_ok (body', _, extras, next1) =>
          let f' := MkFnDef (raw_fn_name f) (raw_fn_lifetimes f)
                      (raw_fn_outlives f) [] (raw_fn_params f)
                      (raw_fn_ret f) body'
                      (raw_fn_type_params f) (raw_fn_bounds f) in
          match elaborate_raw_fns_fuel fuel base_env (done ++ extras ++ [f'])
                  next1 rest with
          | infer_err err => infer_err err
          | infer_ok (rest', next2) => infer_ok (extras ++ f' :: rest', next2)
          end
      end
  end.

Definition elaborate_raw_global_env (env : global_env) (fs : list raw_fn_def)
    : infer_result global_env :=
  let stubs := map fn_stub_of_raw fs in
  let base := MkGlobalEnv (env_structs env) (env_enums env)
    (env_traits env) (env_impls env)
    [] stubs in
  match elaborate_raw_fns_fuel 10000 base [] 0 fs with
  | infer_err err => infer_err err
  | infer_ok (fns, _) =>
      infer_ok (MkGlobalEnv (env_structs env) (env_enums env)
        (env_traits env) (env_impls env) [] fns)
  end.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
Extraction "../fixtures/TypeChecker.ml"
  infer_core_env_roots infer_env_roots infer_full_env_roots
  infer_env infer_full_env check_program_env
  infer_core_env_elab infer_env_elab infer_full_env_elab
  infer_program_env_alpha_elab check_program_env_alpha_elab
  elaborate_raw_expr elaborate_raw_global_env
  alpha_normalize_global_env check_program_env_alpha
  check_program_env_alpha_validated
  preservation_ready_expr_b preservation_ready_args_b
  preservation_ready_fields_b
  provenance_ready_expr_b provenance_ready_args_b
  provenance_ready_fields_b
  infer_core_env_state_fuel_roots_shadow_safe
  infer_core_env_roots_shadow_safe infer_env_roots_shadow_safe
  check_fn_root_shadow_summary check_env_root_shadow_summary
  check_fn_root_shadow_provenance_summary
  check_env_root_shadow_provenance_summary
  direct_call_ready_expr_b
  check_fn_root_shadow_direct_call_provenance_summary
  check_env_root_shadow_direct_call_provenance_summary
  check_env_preservation_ready
  check_program_env_alpha_validated_root_shadow
  check_program_env_alpha_validated_root_shadow_provenance_summary
  check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
  check_program_env_alpha_validated_root_shadow_provenance
  infer_fn_env_end2end infer_program_env_end2end check_program_env_end2end.
