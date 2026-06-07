From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

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

Definition roots_for_checked_result
    (env : global_env) (T : Ty) (roots : root_set) : root_set :=
  if capture_ref_free_ty_b env T then [] else roots.

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
  | EEnum _ _ _ _ _ payloads =>
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
  | ECallExprGeneric _ _ _ => false
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
  | EEnum _ _ _ _ _ payloads =>
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
  | EAssign _ e_new => provenance_ready_expr_b e_new
  | EReplace _ e_new => provenance_ready_expr_b e_new
  | EIf e1 e2 e3 =>
      provenance_ready_expr_b e1 &&
      provenance_ready_expr_b e2 &&
      provenance_ready_expr_b e3
  | ECall _ _ => false
  | ECallGeneric _ _ _ => false
  | ECallExpr _ _ => false
  | ECallExprGeneric _ _ _ => false
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
  | EEnum enum_name variant_name lts variant_lts args payloads =>
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
              if negb (enum_outlives_hold_b Ω edef lts)
              then infer_err ErrLifetimeConflict
              else
              match lookup_enum_variant variant_name (enum_variants edef) with
              | None => infer_err (ErrVariantNotFound variant_name)
              | Some vdef =>
                  if negb (Nat.eqb (List.length variant_lts)
                      (enum_variant_lifetimes vdef))
                  then infer_err ErrArityMismatch
                  else
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
                              instantiate_enum_variant_field_ty lts variant_lts args T_field in
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
                      if negb (enum_outlives_hold_b Ω edef lts)
                      then infer_err ErrLifetimeConflict
                      else
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
                                                      if contains_lbound_ty T_branch
                                                      then infer_err ErrLifetimeLeak
                                                      else if params_ok_sctx_b env ps Σ_branch_payload &&
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
      | None =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if place_resolved_write_writable_chain_b env R Σ p then
              match place_resolved_write_target R p with
              | None => infer_err ErrNotImplemented
              | Some x =>
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
                                      infer_ok
                                        (T_old, Σ1,
                                         root_env_update x
                                           (root_set_union roots_old roots_new) R1,
                                         roots_result)
                                    else infer_err (compatible_error T_new T_old)
                                end
                            end
                          else infer_err (ErrNotMutable x)
                      | Some MImmutable => infer_err (ErrNotMutable x)
                      | None => infer_err (ErrUnknownVar x)
                      end
                  end
              end
              else infer_err ErrNotImplemented
          end
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
      | None =>
          match infer_place_sctx env Σ p with
          | infer_err err => infer_err err
          | infer_ok T_old =>
              if usage_eqb (ty_usage T_old) ULinear
              then infer_err (ErrUsageMismatch (ty_usage T_old) UAffine)
              else
              if place_resolved_write_writable_chain_b env R Σ p then
              match place_resolved_write_target R p with
              | None => infer_err ErrNotImplemented
              | Some x =>
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
                                  infer_ok
                                    (MkTy UUnrestricted TUnits, Σ1,
                                     root_env_update x
                                       (root_set_union roots_old roots_new) R1,
                                     [])
                                else infer_err (compatible_error T_new T_old)
                            end
                        end
                      else infer_err (ErrNotMutable x)
                  | Some MImmutable => infer_err (ErrNotMutable x)
                  | None => infer_err (ErrUnknownVar x)
                  end
              end
              else infer_err ErrNotImplemented
          end
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
                  match place_resolved_roots R p with
                  | Some roots =>
                      match singleton_store_root roots with
                      | Some _ =>
                          infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                      | None =>
                          match place_borrow_roots R p with
                          | Some roots =>
                              infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                          | None => infer_err ErrContextCheckFailed
                          end
                      end
                  | None =>
                      match place_borrow_roots R p with
                      | Some roots =>
                          infer_ok (MkTy UUnrestricted (TRef (LVar n) RShared T_p), Σ, R, roots)
                      | None => infer_err ErrContextCheckFailed
                      end
                  end
              | RUnique =>
                  if place_under_unique_ref_b env Σ p
                  then
                    match
                      if place_resolved_write_writable_chain_b env R Σ p then
                        match place_resolved_write_target R p with
                        | Some x => Some [RStore x]
                        | None => None
                        end
                      else None
                    with
                    | Some roots =>
                        infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                    | None =>
                    match place_resolved_roots R p with
                    | Some roots =>
                        match singleton_store_root roots with
                        | Some _ =>
                            infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                        | None =>
                            match place_borrow_roots R p with
                            | Some roots =>
                                infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                            | None => infer_err ErrContextCheckFailed
                            end
                        end
                    | None =>
                        match place_borrow_roots R p with
                        | Some roots =>
                            infer_ok (MkTy UAffine (TRef (LVar n) RUnique T_p), Σ, R, roots)
                        | None => infer_err ErrContextCheckFailed
                        end
                    end
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
                match rk with
                | RShared =>
                    match place_resolved_roots R p with
                    | Some roots =>
                        match singleton_store_root roots with
                        | Some _ => infer_ok (T_p, Σ, R, roots)
                        | None =>
                            match place_root_lookup R p with
                            | None => infer_err ErrContextCheckFailed
                            | Some roots => infer_ok (T_p, Σ, R, roots)
                            end
                        end
                    | None =>
                        match place_root_lookup R p with
                        | None => infer_err ErrContextCheckFailed
                        | Some roots => infer_ok (T_p, Σ, R, roots)
                        end
                    end
                | RUnique =>
                    if place_under_unique_ref_b env Σ p
                    then
                      match place_resolved_roots R p with
                      | Some roots =>
                          match singleton_store_root roots with
                          | Some _ => infer_ok (T_p, Σ, R, roots)
                          | None =>
                              match place_root_lookup R p with
                              | None => infer_err ErrContextCheckFailed
                              | Some roots => infer_ok (T_p, Σ, R, roots)
                              end
                          end
                      | None =>
                          match place_root_lookup R p with
                          | None => infer_err ErrContextCheckFailed
                          | Some roots => infer_ok (T_p, Σ, R, roots)
                          end
                      end
                    else infer_err (ErrImmutableBorrow (place_name p))
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
  | ECallExprGeneric callee type_args args =>
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
              | TTypeForall type_params bounds body =>
                  match ty_core body with
                  | TFn param_tys ret =>
                      match check_type_forall_bounds env bounds type_args with
                      | Some err => infer_err err
                      | None =>
                          match check_arg_tys Ω arg_tys
                                  (map (subst_type_params_ty type_args) param_tys) with
                          | Some err => infer_err err
                          | None => infer_ok
                              (subst_type_params_ty type_args ret, Σ', R',
                                root_set_union roots_callee
                                  (root_sets_union arg_roots))
                          end
                      end
                  | c => infer_err (ErrMalformedHrtBody c)
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

