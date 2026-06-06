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
