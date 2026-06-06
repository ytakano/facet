From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

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

Inductive place_resolved_write_mutable_chain
    (R : root_env) (Σ : sctx) : place -> Prop :=
  | PRWMC_Direct : forall p,
      place_resolved_write_direct_parent p ->
      place_resolved_write_mutable_chain R Σ p.

Definition place_resolved_write_mutable_chain_b
    (_R : root_env) (_Σ : sctx) (p : place) : bool :=
  place_resolved_write_direct_parent_b p.

Lemma place_resolved_write_mutable_chain_b_sound : forall R Σ p,
  place_resolved_write_mutable_chain_b R Σ p = true ->
  place_resolved_write_mutable_chain R Σ p.
Proof.
  intros R Σ p Hchain.
  apply PRWMC_Direct.
  apply place_resolved_write_direct_parent_b_sound. exact Hchain.
Qed.

Lemma place_resolved_write_mutable_chain_shape : forall R Σ p,
  place_resolved_write_mutable_chain R Σ p ->
  place_resolved_write_shape p.
Proof.
  intros R Σ p Hchain.
  inversion Hchain; subst.
  apply PRWS_Direct. exact H.
Qed.

Lemma place_resolved_write_mutable_chain_instantiate : forall rho R Σ p,
  place_resolved_write_mutable_chain R Σ p ->
  place_resolved_write_mutable_chain (root_env_instantiate rho R) Σ p.
Proof.
  intros rho R Σ p Hchain.
  inversion Hchain; subst.
  apply PRWMC_Direct. exact H.
Qed.

Lemma place_resolved_write_mutable_chain_equiv : forall R R' Σ p,
  root_env_equiv R R' ->
  place_resolved_write_mutable_chain R Σ p ->
  place_resolved_write_mutable_chain R' Σ p.
Proof.
  intros R R' Σ p _ Hchain.
  inversion Hchain; subst.
  apply PRWMC_Direct. exact H.
Qed.

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

Fixpoint place_resolved_write_writable_chain_b
    (env : global_env) (R : root_env) (Σ : sctx) (p : place) : bool :=
  if place_resolved_write_direct_parent_b p then true
  else match p with
  | PDeref q =>
      place_resolved_write_writable_chain_b env R Σ q &&
      writable_place_b env Σ q &&
      match place_resolved_write_target R q with
      | Some x =>
          match sctx_lookup_mut x Σ with
          | Some MMutable => true
          | _ => false
          end
      | None => false
      end
  | _ => false
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

