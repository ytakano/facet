From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerEnvHelpers AssocCompatibility.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* Assoc-aware variants of post-collection direct top-level call logic. *)

Definition infer_direct_call_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (fdef : fn_def) (arg_tys : list Ty) : infer_result Ty :=
  if no_captures_b fdef && Nat.eqb (fn_type_params fdef) 0
  then
    let m := fn_lifetimes fdef in
    match build_sigma m (repeat None m) arg_tys (fn_params fdef) with
    | None => infer_err ErrLifetimeConflict
    | Some σ_acc =>
        let σ := finalize_subst σ_acc in
        let ps_subst := apply_lt_params σ (fn_params fdef) in
        match check_args_assoc env Ω arg_tys ps_subst with
        | Some err => infer_err err
        | None =>
            if forallb (wf_lifetime_b (mk_region_ctx n)) σ
            then
              let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
              if outlives_constraints_hold_b Ω Ω_subst
              then infer_ok (apply_lt_ty σ (fn_ret fdef))
              else infer_err ErrHrtBoundUnsatisfied
            else infer_err ErrLifetimeLeak
        end
    end
  else infer_err ErrNotImplemented.

Definition infer_direct_call_generic_assoc
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    (fdef : fn_def) (type_args arg_tys : list Ty) : infer_result Ty :=
  if no_captures_b fdef &&
     Nat.eqb (Datatypes.length type_args) (fn_type_params fdef)
  then
    match check_struct_bounds env (fn_bounds fdef) type_args with
    | Some err => infer_err err
    | None =>
        let m := fn_lifetimes fdef in
        let params_typed := apply_type_params type_args (fn_params fdef) in
        match build_sigma m (repeat None m) arg_tys params_typed with
        | None => infer_err ErrLifetimeConflict
        | Some σ_acc =>
            let σ := finalize_subst σ_acc in
            let ps_subst := apply_lt_params σ params_typed in
            match check_args_assoc env Ω arg_tys ps_subst with
            | Some err => infer_err err
            | None =>
                if forallb (wf_lifetime_b (mk_region_ctx n)) σ
                then
                  let Ω_subst := apply_lt_outlives σ (fn_outlives fdef) in
                  if outlives_constraints_hold_b Ω Ω_subst
                  then infer_ok
                    (apply_lt_ty σ
                      (subst_type_params_ty type_args (fn_ret fdef)))
                  else infer_err ErrHrtBoundUnsatisfied
                else infer_err ErrLifetimeLeak
            end
        end
    end
  else infer_err ErrArityMismatch.
