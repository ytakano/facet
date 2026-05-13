From Facet.TypeSystem Require Import Lifetime Types Syntax TypingRules.
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
      | TFn ts1 r1, TFn ts2 r2 =>
          (fix go (l1 l2 : list Ty) : bool :=
             match l1, l2 with
             | [], [] => true
             | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
             | _, _ => false
             end) ts1 ts2 && ty_eqb r1 r2
      | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
          Nat.eqb n1 n2 && outlives_ctx_eqb Ω1 Ω2 && ty_eqb b1 b2
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
  | TFn ts1 r1, TFn ts2 r2 =>
      (fix go (l1 l2 : list Ty) : bool :=
         match l1, l2 with
         | [], [] => true
         | t1 :: l1', t2 :: l2' => ty_eqb t1 t2 && go l1' l2'
         | _, _ => false
         end) ts1 ts2 && ty_eqb r1 r2
  | TForall n1 Ω1 b1, TForall n2 Ω2 b2 =>
      Nat.eqb n1 n2 && outlives_ctx_eqb Ω1 Ω2 && ty_eqb b1 b2
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
      | TRef _ _ t => S (ty_depth t)
      | TForall _ Ω body => S (List.length Ω + ty_depth body)
      | _ => 1
      end
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
          ty_compatible_b_fuel fuel' Ω Ta Tb
      | TForall na Ωa Ta, TForall nb Ωb Tb =>
          Nat.eqb na nb && outlives_ctx_eqb Ωa Ωb &&
          ty_compatible_b_fuel fuel' Ω Ta Tb
      | _, TForall _ [] Tb =>
          negb (contains_lbound_ty Tb) &&
          ty_compatible_b_fuel fuel' Ω T_actual Tb
      | ca, cb => ty_core_eqb ca cb
      end
  end.

Definition ty_compatible_b (Ω : outlives_ctx) (T_actual T_expected : Ty) : bool :=
  ty_compatible_b_fuel (ty_depth T_actual + ty_depth T_expected) Ω T_actual T_expected.

(* ------------------------------------------------------------------ *)
(* Decidable context operations                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lookup_b (x : ident) (Γ : ctx) : option (Ty * bool) :=
  match Γ with
  | []              => None
  | (n, T, b, _) :: t => if ident_eqb x n then Some (T, b)
                      else ctx_lookup_b x t
  end.

Fixpoint ctx_consume_b (x : ident) (Γ : ctx) : option ctx :=
  match Γ with
  | []              => None
  | (n, T, b, m) :: t =>
      if ident_eqb x n
      then Some ((n, T, true, m) :: t)
      else match ctx_consume_b x t with
           | None    => None
           | Some t' => Some ((n, T, b, m) :: t')
           end
  end.

Fixpoint ctx_lookup_mut_b (x : ident) (Γ : ctx) : option mutability :=
  match Γ with
  | [] => None
  | (n, _, _, m) :: t => if ident_eqb x n then Some m else ctx_lookup_mut_b x t
  end.

Definition ctx_add_b (x : ident) (T : Ty) (m : mutability) (Γ : ctx) : ctx :=
  (x, T, false, m) :: Γ.

Fixpoint ctx_remove_b (x : ident) (Γ : ctx) : ctx :=
  match Γ with
  | []              => []
  | (n, T, b, m) :: t =>
      if ident_eqb x n then t
      else (n, T, b, m) :: ctx_remove_b x t
  end.

(* Returns true iff x's usage constraint is satisfied after its scope:
   - linear: x must be consumed (found with consumed=true)
   - affine/unrestricted: always ok *)
Definition ctx_check_ok (x : ident) (T : Ty) (Γ : ctx) : bool :=
  match ty_usage T with
  | ULinear =>
      match ctx_lookup_b x Γ with
      | Some (_, true) => true
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
  | MkTy u (TRef l rk T_inner) =>
      ref_usage_ok_b u rk && wf_lifetime_at_b bound_depth Δ l && wf_type_at_b bound_depth Δ T_inner
  | MkTy _ (TFn ts r) =>
      forallb (wf_type_at_b bound_depth Δ) ts && wf_type_at_b bound_depth Δ r
  | MkTy _ (TForall n Ω body) =>
      wf_outlives_at_b (n + bound_depth) Δ Ω && wf_type_at_b (n + bound_depth) Δ body
  | _ => true
  end.

Definition wf_lifetime_b (Δ : region_ctx) (l : lifetime) : bool :=
  wf_lifetime_at_b 0 Δ l.

Definition wf_type_b (Δ : region_ctx) (T : Ty) : bool :=
  wf_type_at_b 0 Δ T.

(* ------------------------------------------------------------------ *)
(* Alpha renaming                                                       *)
(* ------------------------------------------------------------------ *)

Definition rename_env : Type := list (ident * ident).

Fixpoint ident_in (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => if ident_eqb x y then true else ident_in x ys
  end.

Fixpoint lookup_rename (x : ident) (ρ : rename_env) : ident :=
  match ρ with
  | [] => x
  | (old, fresh) :: ρ' =>
      if ident_eqb x old then fresh else lookup_rename x ρ'
  end.

Fixpoint max_ident_index (base : string) (used : list ident) : nat :=
  match used with
  | [] => O
  | (base0, n) :: used' =>
      if String.eqb base base0
      then Nat.max n (max_ident_index base used')
      else max_ident_index base used'
  end.

Definition fresh_ident (x : ident) (used : list ident) : ident :=
  (fst x, S (max_ident_index (fst x) used)).

Fixpoint ctx_names (Γ : ctx) : list ident :=
  match Γ with
  | [] => []
  | (x, _, _, _) :: Γ' => x :: ctx_names Γ'
  end.

Fixpoint place_name (p : place) : ident :=
  match p with
  | PVar x    => x
  | PDeref q  => place_name q
  end.

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
  | ErrContextCheckFailed : infer_error
  | ErrNotImplemented : infer_error
  | ErrImmutableBorrow : ident -> infer_error       (* &mut x where x is immutable *)
  | ErrNotAReference : TypeCore Ty -> infer_error   (* *e where e is not a reference type *)
  | ErrNotAFunction : TypeCore Ty -> infer_error
  | ErrBorrowConflict : ident -> infer_error       (* borrow conflicts with existing active borrow *)
  | ErrLifetimeLeak : infer_error                 (* return type references a local lifetime *)
  | ErrLifetimeConflict : infer_error.            (* unification conflict in call lifetime substitution *)

Definition compatible_error (T_actual T_expected : Ty) : infer_error :=
  if ty_core_eqb (ty_core T_actual) (ty_core T_expected)
  then ErrUsageMismatch (ty_usage T_actual) (ty_usage T_expected)
  else ErrTypeMismatch (ty_core T_actual) (ty_core T_expected).

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
  end.

Fixpoint free_vars_expr (e : expr) : list ident :=
  match e with
  | EUnit => []
  | ELit _ => []
  | EVar x => [x]
  | EFn _ => []
  | ELet _ x _ e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ELetInfer _ x e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ECall _ args =>
      let fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end
      in go args
  | ECallExpr callee args =>
      let fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end
      in free_vars_expr callee ++ go args
  | EReplace p e_new => place_name p :: free_vars_expr e_new
  | EAssign p e_new => place_name p :: free_vars_expr e_new
  | EBorrow _ p => [place_name p]
  | EDeref e1 => free_vars_expr e1
  | EDrop e1 => free_vars_expr e1
  | EIf e1 e2 e3 => free_vars_expr e1 ++ free_vars_expr e2 ++ free_vars_expr e3
  end.

Fixpoint param_names (ps : list param) : list ident :=
  match ps with
  | [] => []
  | p :: ps' => param_name p :: param_names ps'
  end.

Fixpoint rename_place (ρ : rename_env) (p : place) : place :=
  match p with
  | PVar x   => PVar (lookup_rename x ρ)
  | PDeref q => PDeref (rename_place ρ q)
  end.

Fixpoint alpha_rename_expr (ρ : rename_env) (used : list ident)
    (e : expr) : expr * list ident :=
  match e with
  | EUnit => (EUnit, used)
  | ELit l => (ELit l, used)
  | EVar x => (EVar (lookup_rename x ρ), used)
  | EFn fname => (EFn fname, used)
  | ECall fname args =>
      let fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end
      in
      let (args', used') := go used args in
      (ECall fname args', used')
  | ECallExpr callee args =>
      let (callee', used1) := alpha_rename_expr ρ used callee in
      let fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1') := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1' rest in
            (arg' :: rest', used2)
        end
      in
      let (args', used') := go used1 args in
      (ECallExpr callee' args', used')
  | EReplace p e_new =>
      let (e_new', used') := alpha_rename_expr ρ used e_new in
      (EReplace (rename_place ρ p) e_new', used')
  | EAssign p e_new =>
      let (e_new', used') := alpha_rename_expr ρ used e_new in
      (EAssign (rename_place ρ p) e_new', used')
  | EBorrow rk p =>
      (EBorrow rk (rename_place ρ p), used)
  | EDeref e1 =>
      let (e1', used') := alpha_rename_expr ρ used e1 in
      (EDeref e1', used')
  | EDrop e1 =>
      let (e1', used') := alpha_rename_expr ρ used e1 in
      (EDrop e1', used')
  | ELet m x T e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELet m x' T e1' e2', used3)
  | ELetInfer m x e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELetInfer m x' e1' e2', used3)
  | EIf e1 e2 e3 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let (e2', used2) := alpha_rename_expr ρ used1 e2 in
      let (e3', used3) := alpha_rename_expr ρ used2 e3 in
      (EIf e1' e2' e3', used3)
  end.

Fixpoint alpha_rename_params (ρ : rename_env) (used : list ident)
    (ps : list param) : list param * rename_env * list ident :=
  match ps with
  | [] => ([], ρ, used)
  | p :: ps' =>
      let x := param_name p in
      let x' := fresh_ident x used in
      let p' := MkParam (param_mutability p) x' (param_ty p) in
      let '(ps'', ρ', used') :=
        alpha_rename_params ((x, x') :: ρ) (x' :: used) ps' in
      (p' :: ps'', ρ', used')
  end.

Definition alpha_rename_fn_def (used : list ident)
    (f : fn_def) : fn_def * list ident :=
  let used0 := param_names (fn_params f) ++ free_vars_expr (fn_body f) ++ used in
  let '(params', ρ, used1) := alpha_rename_params [] used0 (fn_params f) in
  let (body', used2) := alpha_rename_expr ρ used1 (fn_body f) in
  (MkFnDef (fn_name f) (fn_lifetimes f) (fn_outlives f) params' (fn_ret f) body', used2).

Fixpoint alpha_rename_syntax_go (used : list ident) (s : Syntax)
    : Syntax * list ident :=
  match s with
  | [] => ([], used)
  | f :: fs =>
      let (f', used1) := alpha_rename_fn_def used f in
      let (fs', used2) := alpha_rename_syntax_go used1 fs in
      (f' :: fs', used2)
  end.

Definition alpha_rename_syntax (s : Syntax) : Syntax :=
  fst (alpha_rename_syntax_go [] s).

Definition alpha_rename_for_infer (Γ : ctx) (fenv : list fn_def)
    (e : expr) : list fn_def * expr :=
  let (fenv', used) :=
    alpha_rename_syntax_go (free_vars_expr e ++ ctx_names Γ) fenv in
  let (e', _) := alpha_rename_expr [] used e in
  (fenv', e').

Definition wf_outlives_b (Δ : region_ctx) (Ω : outlives_ctx) : bool :=
  wf_outlives_at_b 0 Δ Ω.

Definition outlives_constraints_hold_b (Ω : outlives_ctx) (constraints : outlives_ctx) : bool :=
  forallb (fun '(a, b) => outlives_b Ω a b) constraints.

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
      | Some fdef => infer_ok (fn_value_ty fdef, Γ)
      end

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

  | ECall fname args =>
      match lookup_fn_b fname fenv with
      | None      => infer_err (ErrFunctionNotFound fname)
      | Some fdef =>
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
                        else infer_err ErrLifetimeConflict
                      else infer_err ErrLifetimeLeak
                  end
              end
          end
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
                              then infer_err ErrLifetimeLeak
                              else if outlives_constraints_hold_b Ω bounds_open
                                   then infer_ok (ret_open, Γ')
                                   else infer_err ErrLifetimeConflict
                          end
                      end
                  | c => infer_err (ErrNotAFunction c)
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
  if negb (wf_params_b Δ (fn_params f))
  then infer_err ErrLifetimeLeak
  else
  match infer_body fenv Ω n (params_ctx (fn_params f)) (fn_body f) with
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
  end.

(* Check all functions in the program *)
Definition check_program (fenv : list fn_def) : bool :=
  forallb (fun f =>
    match infer fenv f with
    | infer_ok _ => true
    | infer_err _ => false
    end) fenv.

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
  | EUnit | ELit _ | EVar _ => infer_ok BS
  | EFn _ => infer_ok BS

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

(* ------------------------------------------------------------------ *)
(* Combined type + borrow checker                                        *)
(* ------------------------------------------------------------------ *)

Definition infer_full (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  match infer fenv f with
  | infer_err err => infer_err err
  | infer_ok res  =>
      let Γ := params_ctx (fn_params f) in
      match borrow_check fenv [] Γ (fn_body f) with
      | infer_err err => infer_err err
      | infer_ok _    => infer_ok res
      end
  end.

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
  if negb (wf_params_b Δ (fn_params f))
  then infer_err ErrLifetimeLeak
  else
  match infer_core fenv Ω n (params_ctx (fn_params f)) (fn_body f) with
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
  end.

(* ------------------------------------------------------------------ *)
(* OCaml extraction                                                      *)
(* ------------------------------------------------------------------ *)

Require Extraction.
Extraction Language OCaml.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
Extraction "../fixtures/TypeChecker.ml" infer check_program infer_direct borrow_check infer_full.
