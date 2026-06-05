From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming TypingRules RootProvenance TypeChecker.
From Stdlib Require Import Bool List String PeanoNat Lia.
Import ListNotations.

Definition roots_exclude_params (ps : list param) (roots : root_set) : Prop :=
  Forall (fun x => roots_exclude x roots) (ctx_names (params_ctx ps)).

Definition root_env_excludes_params (ps : list param) (R : root_env) : Prop :=
  Forall (fun x => root_env_excludes x R) (ctx_names (params_ctx ps)).

Lemma roots_exclude_params_instantiate_local :
  forall ps rho roots,
    roots_exclude_params ps roots ->
    root_subst_images_exclude_names (ctx_names (params_ctx ps)) rho ->
    roots_exclude_params ps (root_set_instantiate rho roots).
Proof.
  unfold roots_exclude_params.
  intros ps rho roots Hexcl Hfresh.
  induction Hexcl as [| x xs Hx Hxs IH]; constructor.
  - eapply root_set_instantiate_excludes_images.
    + exact Hx.
    + apply root_subst_images_exclude_names_cons_inv in Hfresh.
      exact (proj1 Hfresh).
  - apply IH.
    apply root_subst_images_exclude_names_cons_inv in Hfresh.
    exact (proj2 Hfresh).
Qed.

Lemma root_env_excludes_params_instantiate_local :
  forall ps rho R,
    root_env_excludes_params ps R ->
    root_subst_images_exclude_names (ctx_names (params_ctx ps)) rho ->
    root_env_excludes_params ps (root_env_instantiate rho R).
Proof.
  unfold root_env_excludes_params.
  intros ps rho R Hexcl Hfresh.
  induction Hexcl as [| x xs Hx Hxs IH]; constructor.
  - eapply root_env_instantiate_excludes_images.
    + exact Hx.
    + apply root_subst_images_exclude_names_cons_inv in Hfresh.
      exact (proj1 Hfresh).
  - apply IH.
    apply root_subst_images_exclude_names_cons_inv in Hfresh.
    exact (proj2 Hfresh).
Qed.

Lemma ctx_names_subst_type_params_ctx : forall type_args Γ,
  ctx_names (subst_type_params_ctx type_args Γ) = ctx_names Γ.
Proof.
  intros type_args Γ. induction Γ as [| [[[x T] st] m] Γ IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma ctx_names_apply_lt_ctx : forall σ Γ,
  ctx_names (apply_lt_ctx σ Γ) = ctx_names Γ.
Proof.
  intros σ Γ. induction Γ as [| [[[x T] st] m] Γ IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma subst_type_params_ctx_sctx_add : forall type_args x T m Σ,
  subst_type_params_ctx type_args (sctx_add x T m Σ) =
  sctx_add x (subst_type_params_ty type_args T) m
    (subst_type_params_ctx type_args Σ).
Proof.
  reflexivity.
Qed.

Lemma subst_type_params_ctx_ctx_remove : forall type_args x Γ,
  subst_type_params_ctx type_args (ctx_remove x Γ) =
  ctx_remove x (subst_type_params_ctx type_args Γ).
Proof.
  intros type_args x Γ. induction Γ as [| [[[y T] st] m] Γ IH]; simpl; auto.
  destruct (ident_eqb x y); simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma subst_type_params_ctx_ctx_remove_b : forall type_args x Γ,
  subst_type_params_ctx type_args (ctx_remove_b x Γ) =
  ctx_remove_b x (subst_type_params_ctx type_args Γ).
Proof.
  intros type_args x Γ. induction Γ as [| [[[y T] st] m] Γ IH]; simpl; auto.
  destruct (ident_eqb x y); simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma subst_type_params_ctx_sctx_remove : forall type_args x Σ,
  subst_type_params_ctx type_args (sctx_remove x Σ) =
  sctx_remove x (subst_type_params_ctx type_args Σ).
Proof.
  intros type_args x Σ. unfold sctx_remove.
  apply subst_type_params_ctx_ctx_remove.
Qed.

Lemma subst_type_params_ctx_ctx_add_params : forall type_args ps Γ,
  subst_type_params_ctx type_args (ctx_add_params ps Γ) =
  ctx_add_params (apply_type_params type_args ps)
    (subst_type_params_ctx type_args Γ).
Proof.
  intros type_args ps Γ. unfold ctx_add_params.
  rewrite subst_type_params_ctx_app.
  rewrite <- params_ctx_apply_type_params.
  reflexivity.
Qed.

Lemma subst_type_params_ctx_sctx_add_params : forall type_args ps Σ,
  subst_type_params_ctx type_args (sctx_add_params ps Σ) =
  sctx_add_params (apply_type_params type_args ps)
    (subst_type_params_ctx type_args Σ).
Proof.
  intros type_args ps Σ. unfold sctx_add_params.
  apply subst_type_params_ctx_ctx_add_params.
Qed.

Lemma apply_lt_ctx_ctx_add_params : forall σ ps Γ,
  apply_lt_ctx σ (ctx_add_params ps Γ) =
  ctx_add_params (apply_lt_params σ ps) (apply_lt_ctx σ Γ).
Proof.
  intros σ ps Γ. unfold ctx_add_params.
  rewrite params_ctx_apply_lt_params. unfold apply_lt_ctx.
  rewrite map_app. reflexivity.
Qed.

Lemma apply_lt_ctx_sctx_add_params : forall σ ps Σ,
  apply_lt_ctx σ (sctx_add_params ps Σ) =
  sctx_add_params (apply_lt_params σ ps) (apply_lt_ctx σ Σ).
Proof.
  intros σ ps Σ. unfold sctx_add_params.
  apply apply_lt_ctx_ctx_add_params.
Qed.

Lemma subst_type_params_ctx_ctx_remove_params : forall type_args ps Γ,
  subst_type_params_ctx type_args (ctx_remove_params ps Γ) =
  ctx_remove_params ps (subst_type_params_ctx type_args Γ).
Proof.
  intros type_args ps. induction ps as [| p ps IH]; intros Γ; simpl; auto.
  rewrite IH, subst_type_params_ctx_ctx_remove_b. reflexivity.
Qed.

Lemma subst_type_params_ctx_sctx_remove_params : forall type_args ps Σ,
  subst_type_params_ctx type_args (sctx_remove_params ps Σ) =
  sctx_remove_params ps (subst_type_params_ctx type_args Σ).
Proof.
  intros type_args ps Σ. unfold sctx_remove_params.
  apply subst_type_params_ctx_ctx_remove_params.
Qed.

Lemma sctx_lookup_subst_type_params_ctx_eq : forall type_args x Σ,
  sctx_lookup x (subst_type_params_ctx type_args Σ) =
  match sctx_lookup x Σ with
  | Some (T, st) => Some (subst_type_params_ty type_args T, st)
  | None => None
  end.
Proof.
  intros type_args x Σ. unfold sctx_lookup.
  induction Σ as [| [[[y T] st] m] Σ IH]; simpl; auto.
  destruct (ident_eqb x y); auto.
Qed.

Lemma ctx_lookup_state_subst_type_params_ctx_eq : forall type_args x Γ,
  ctx_lookup_state x (subst_type_params_ctx type_args Γ) =
  match ctx_lookup_state x Γ with
  | Some (T, st) => Some (subst_type_params_ty type_args T, st)
  | None => None
  end.
Proof.
  intros type_args x Γ.
  induction Γ as [| [[[y T] st] m] Γ IH]; simpl; auto.
  destruct (ident_eqb x y); auto.
Qed.

Lemma sctx_path_available_subst_type_params_ctx : forall type_args Σ x path,
  sctx_path_available (subst_type_params_ctx type_args Σ) x path =
  sctx_path_available Σ x path.
Proof.
  intros type_args Σ x path. unfold sctx_path_available.
  rewrite sctx_lookup_subst_type_params_ctx_eq.
  destruct (sctx_lookup x Σ) as [[T st] |]; reflexivity.
Qed.

Lemma linear_scope_ok_b_subst_type_params_ty_consumed :
  forall env type_args T st,
    st_consumed st = true ->
    linear_scope_ok_b env (subst_type_params_ty type_args T) st = true.
Proof.
  intros env type_args T st Hconsumed.
  unfold linear_scope_ok_b. rewrite Hconsumed. reflexivity.
Qed.

Lemma sctx_check_ok_subst_type_params_ctx_consumed :
  forall env type_args x T Σ T0 st,
    sctx_check_ok env x T Σ = true ->
    sctx_lookup x Σ = Some (T0, st) ->
    st_consumed st = true ->
    sctx_check_ok env x (subst_type_params_ty type_args T)
      (subst_type_params_ctx type_args Σ) = true.
Proof.
  intros env type_args x T Σ T0 st Hcheck Hlookup Hconsumed.
  unfold sctx_check_ok in *.
  rewrite ty_usage_subst_type_params_ty.
  destruct (ty_usage T); try reflexivity.
  rewrite sctx_lookup_subst_type_params_ctx_eq.
  rewrite Hlookup. simpl.
  apply linear_scope_ok_b_subst_type_params_ty_consumed. exact Hconsumed.
Qed.

Lemma sctx_lookup_mut_subst_type_params_ctx :
  forall type_args x Σ,
    sctx_lookup_mut x (subst_type_params_ctx type_args Σ) =
    sctx_lookup_mut x Σ.
Proof.
  intros type_args x Σ. unfold sctx_lookup_mut.
  apply ctx_lookup_mut_subst_type_params_ctx.
Qed.

Lemma ctx_update_state_subst_type_params_ctx :
  forall type_args x f Σ,
    ctx_update_state x f (subst_type_params_ctx type_args Σ) =
    match ctx_update_state x f Σ with
    | Some Σ' => Some (subst_type_params_ctx type_args Σ')
    | None => None
    end.
Proof.
  intros type_args x f Σ. induction Σ as [| [[[y T] st] m] Σ IH]; simpl; auto.
  destruct (ident_eqb x y); simpl; auto.
  destruct (ctx_update_state x f Σ) as [Σ' |]; simpl; rewrite IH; reflexivity.
Qed.

Lemma sctx_consume_path_subst_type_params_ctx : forall type_args Σ x path,
  sctx_consume_path (subst_type_params_ctx type_args Σ) x path =
  match sctx_consume_path Σ x path with
  | infer_ok Σ' => infer_ok (subst_type_params_ctx type_args Σ')
  | infer_err err => infer_err err
  end.
Proof.
  intros type_args Σ x path. unfold sctx_consume_path, sctx_update_state.
  rewrite sctx_path_available_subst_type_params_ctx.
  destruct (sctx_path_available Σ x path) as [u | err]; simpl; auto.
  rewrite ctx_update_state_subst_type_params_ctx.
  destruct (ctx_update_state x (state_consume_path path) Σ); reflexivity.
Qed.

Lemma sctx_restore_path_subst_type_params_ctx : forall type_args Σ x path,
  sctx_restore_path (subst_type_params_ctx type_args Σ) x path =
  match sctx_restore_path Σ x path with
  | infer_ok Σ' => infer_ok (subst_type_params_ctx type_args Σ')
  | infer_err err => infer_err err
  end.
Proof.
  intros type_args Σ x path. unfold sctx_restore_path, sctx_update_state.
  rewrite ctx_update_state_subst_type_params_ctx.
  destruct (ctx_update_state x (state_restore_path path) Σ); reflexivity.
Qed.

Lemma ctx_lookup_params_none_b_subst_type_params_ctx :
  forall type_args ps Σ,
    ctx_lookup_params_none_b (apply_type_params type_args ps)
      (subst_type_params_ctx type_args Σ) =
    ctx_lookup_params_none_b ps Σ.
Proof.
  intros type_args ps Σ.
  induction ps as [| p ps IH]; simpl; auto.
  rewrite ctx_lookup_state_subst_type_params_ctx_eq.
  destruct (ctx_lookup_state (param_name p) Σ) as [[T st] |]; simpl; auto.
Qed.

Lemma roots_exclude_params_equiv_local :
  forall ps roots roots',
    root_set_equiv roots roots' ->
    roots_exclude_params ps roots ->
    roots_exclude_params ps roots'.
Proof.
  unfold roots_exclude_params.
  intros ps roots roots' Heq Hexcl.
  induction Hexcl as [| x xs Hx Hxs IH]; constructor.
  - eapply roots_exclude_equiv.
    + exact Heq.
    + exact Hx.
  - exact IH.
Qed.

Lemma root_env_excludes_params_equiv_local :
  forall ps R R',
    root_env_equiv R R' ->
    root_env_excludes_params ps R ->
    root_env_excludes_params ps R'.
Proof.
  unfold root_env_excludes_params.
  intros ps R R' Heq Hexcl.
  induction Hexcl as [| x xs Hx Hxs IH]; constructor.
  - eapply root_env_excludes_equiv.
    + exact Heq.
    + exact Hx.
  - exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Context shadowing summaries                                          *)
(* ------------------------------------------------------------------ *)

Definition sctx_no_shadow (Σ : sctx) : Prop :=
  NoDup (ctx_names Σ).

Lemma sctx_lookup_not_in_names :
  forall x Σ,
    ~ In x (ctx_names Σ) ->
    sctx_lookup x Σ = None.
Proof.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hnotin;
    simpl in *; try reflexivity.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exfalso. apply Hnotin. left. reflexivity.
  - apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma sctx_lookup_none_not_in_names :
  forall x Σ,
    sctx_lookup x Σ = None ->
    ~ In x (ctx_names Σ).
Proof.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hlookup Hin;
    simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y. rewrite ident_eqb_refl in Hlookup. discriminate.
    + destruct (ident_eqb x y); try discriminate.
      eapply IH; eassumption.
Qed.

Lemma sctx_no_shadow_add :
  forall x T m Σ,
    sctx_no_shadow Σ ->
    sctx_lookup x Σ = None ->
    sctx_no_shadow (sctx_add x T m Σ).
Proof.
  unfold sctx_no_shadow, sctx_add, ctx_add.
  intros x T m Σ Hnodup Hlookup.
  simpl. constructor.
  - eapply sctx_lookup_none_not_in_names. exact Hlookup.
  - exact Hnodup.
Qed.

Lemma sctx_no_shadow_remove :
  forall x Σ,
    sctx_no_shadow Σ ->
    sctx_no_shadow (sctx_remove x Σ).
Proof.
  unfold sctx_no_shadow, sctx_remove.
  intros x Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Hnodup;
    simpl in *.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct (ident_eqb x y).
    + exact Hnodup_tail.
    + simpl. constructor.
      * intros Hin. apply Hnotin.
        clear -Hin.
        induction rest as [| [[[z Tz] stz] mz] rest IHrest];
          simpl in *.
        -- contradiction.
        -- destruct (ident_eqb x z) eqn:Heq.
           ++ apply ident_eqb_eq in Heq. subst z.
              right. exact Hin.
           ++ destruct Hin as [Hin | Hin].
              ** left. exact Hin.
              ** right. apply IHrest. exact Hin.
      * apply IH. exact Hnodup_tail.
Qed.

Lemma sctx_update_state_names :
  forall x f Σ Σ',
    sctx_update_state x f Σ = Some Σ' ->
    ctx_names Σ' = ctx_names Σ.
Proof.
  intros x f Σ.
  induction Σ as [| [[[y T] st] m] rest IH]; intros Σ' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - inversion Hupdate; subst. reflexivity.
  - destruct (sctx_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst. simpl.
    rewrite (IH rest' eq_refl). reflexivity.
Qed.

Lemma sctx_update_state_no_shadow :
  forall x f Σ Σ',
    sctx_no_shadow Σ ->
    sctx_update_state x f Σ = Some Σ' ->
    sctx_no_shadow Σ'.
Proof.
  unfold sctx_no_shadow.
  intros x f Σ Σ' Hnodup Hupdate.
  rewrite (sctx_update_state_names x f Σ Σ' Hupdate).
  exact Hnodup.
Qed.

Lemma sctx_consume_path_no_shadow :
  forall Σ Σ' x path,
    sctx_no_shadow Σ ->
    sctx_consume_path Σ x path = infer_ok Σ' ->
    sctx_no_shadow Σ'.
Proof.
  intros Σ Σ' x path Hnodup Hconsume.
  unfold sctx_consume_path in Hconsume.
  unfold sctx_path_available in Hconsume.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b st path); try discriminate.
  destruct (sctx_update_state x (state_consume_path path) Σ) as [Σ0 |]
    eqn:Hupdate; try discriminate.
  inversion Hconsume; subst.
  eapply sctx_update_state_no_shadow; eassumption.
Qed.

Lemma sctx_restore_path_no_shadow :
  forall Σ Σ' x path,
    sctx_no_shadow Σ ->
    sctx_restore_path Σ x path = infer_ok Σ' ->
    sctx_no_shadow Σ'.
Proof.
  intros Σ Σ' x path Hnodup Hrestore.
  unfold sctx_restore_path in Hrestore.
  destruct (sctx_update_state x (state_restore_path path) Σ) as [Σ0 |]
    eqn:Hupdate; try discriminate.
  inversion Hrestore; subst.
  eapply sctx_update_state_no_shadow; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Wrapper-free env/stateful typing specification                       *)
(* ------------------------------------------------------------------ *)

Inductive typed_place_type_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPTES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      typed_place_type_env_structural env Σ (PVar x) T
  | TPTES_Deref : forall p la rk T u,
      typed_place_type_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_type_env_structural env Σ (PDeref p) T
  | TPTES_Field : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      typed_place_type_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).

Inductive typed_place_env_structural (env : global_env) (Σ : sctx)
    : place -> Ty -> Prop :=
  | TPES_Var : forall x T st,
      sctx_lookup x Σ = Some (T, st) ->
      binding_available_b st [] = true ->
      typed_place_env_structural env Σ (PVar x) T
  | TPES_Deref : forall p la rk T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      typed_place_env_structural env Σ (PDeref p) T
  | TPES_Field : forall p sname lts args sdef fdef x path T_root st T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = Some (x, path) ->
      sctx_lookup x Σ = Some (T_root, st) ->
      binding_available_b st path = true ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef)
  | TPES_Field_Indirect : forall p sname lts args sdef fdef T_parent,
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      place_path (PField p (field_name fdef)) = None ->
      typed_place_env_structural env Σ (PField p (field_name fdef))
        (instantiate_struct_field_ty lts args fdef).
Lemma typed_place_env_structural_pvar_subst_type_params_ctx :
  forall env type_args Sigma x T,
    typed_place_env_structural env Sigma (PVar x) T ->
    typed_place_env_structural env (subst_type_params_ctx type_args Sigma)
      (PVar x) (subst_type_params_ty type_args T).
Proof.
  intros env type_args Sigma x T Hplace.
  destruct (sctx_lookup x Sigma) as [[T0 st] |] eqn:Hlookup.
  - inversion Hplace; subst; try congruence.
    rewrite Hlookup in H0. inversion H0; subst.
    eapply TPES_Var.
    + rewrite sctx_lookup_subst_type_params_ctx_eq.
      rewrite Hlookup. reflexivity.
    + eassumption.
  - inversion Hplace; subst; congruence.
Qed.

Fixpoint type_params_bounded_ty_fuel
    (fuel n : nat) (T : Ty) {struct fuel} : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      match T with
      | MkTy _ TUnits => True
      | MkTy _ TIntegers => True
      | MkTy _ TFloats => True
      | MkTy _ TBooleans => True
      | MkTy _ (TNamed _) => True
      | MkTy _ (TParam i) => i < n
      | MkTy _ (TStruct _ _ args) =>
          Forall (type_params_bounded_ty_fuel fuel' n) args
      | MkTy _ (TEnum _ _ args) =>
          Forall (type_params_bounded_ty_fuel fuel' n) args
      | MkTy _ (TFn params ret) =>
          Forall (type_params_bounded_ty_fuel fuel' n) params /\
          type_params_bounded_ty_fuel fuel' n ret
      | MkTy _ (TClosure _ params ret) =>
          Forall (type_params_bounded_ty_fuel fuel' n) params /\
          type_params_bounded_ty_fuel fuel' n ret
      | MkTy _ (TForall _ _ body) =>
          type_params_bounded_ty_fuel fuel' n body
      | MkTy _ (TTypeForall _ _ _) => True
      | MkTy _ (TRef _ _ inner) =>
          type_params_bounded_ty_fuel fuel' n inner
      end
  end.

Definition type_params_bounded_ty (n : nat) (T : Ty) : Prop :=
  exists fuel, type_params_bounded_ty_fuel fuel n T.

Definition param_type_params_bounded (n : nat) (p : param) : Prop :=
  type_params_bounded_ty n (param_ty p).

Definition params_type_params_bounded (n : nat) (ps : list param) : Prop :=
  Forall (param_type_params_bounded n) ps.

Definition fn_type_params_bounded (f : fn_def) : Prop :=
  params_type_params_bounded (fn_type_params f) (fn_captures f) /\
  params_type_params_bounded (fn_type_params f) (fn_params f) /\
  type_params_bounded_ty (fn_type_params f) (fn_ret f).

Fixpoint type_params_no_implicit_fallback_ty_fuel
    (fuel subst_arity : nat) (T : Ty) {struct fuel} : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      match T with
      | MkTy _ TUnits => True
      | MkTy _ TIntegers => True
      | MkTy _ TFloats => True
      | MkTy _ TBooleans => True
      | MkTy _ (TNamed _) => True
      | MkTy _ (TParam i) => i < 0
      | MkTy _ (TStruct _ _ args) =>
          Datatypes.length args >= subst_arity /\
          Forall (type_params_no_implicit_fallback_ty_fuel fuel' subst_arity) args
      | MkTy _ (TEnum _ _ args) =>
          Datatypes.length args >= subst_arity /\
          Forall (type_params_no_implicit_fallback_ty_fuel fuel' subst_arity) args
      | MkTy _ (TFn params ret) =>
          Forall (type_params_no_implicit_fallback_ty_fuel fuel' subst_arity) params /\
          type_params_no_implicit_fallback_ty_fuel fuel' subst_arity ret
      | MkTy _ (TClosure _ params ret) =>
          Forall (type_params_no_implicit_fallback_ty_fuel fuel' subst_arity) params /\
          type_params_no_implicit_fallback_ty_fuel fuel' subst_arity ret
      | MkTy _ (TForall _ _ body) =>
          type_params_no_implicit_fallback_ty_fuel fuel' subst_arity body
      | MkTy _ (TTypeForall _ _ _) => True
      | MkTy _ (TRef _ _ inner) =>
          type_params_no_implicit_fallback_ty_fuel fuel' subst_arity inner
      end
  end.

Definition type_params_no_implicit_fallback_ty
    (subst_arity : nat) (T : Ty) : Prop :=
  exists fuel, type_params_no_implicit_fallback_ty_fuel fuel subst_arity T.

Definition type_params_subst_noop_ty (subst_arity : nat) (T : Ty) : Prop :=
  type_params_bounded_ty 0 T /\
  type_params_no_implicit_fallback_ty subst_arity T.

Definition param_type_params_subst_noop (subst_arity : nat) (p : param) : Prop :=
  type_params_subst_noop_ty subst_arity (param_ty p).

Definition params_type_params_subst_noop
    (subst_arity : nat) (ps : list param) : Prop :=
  Forall (param_type_params_subst_noop subst_arity) ps.

Definition fn_signature_type_params_subst_noop
    (subst_arity : nat) (f : fn_def) : Prop :=
  params_type_params_subst_noop subst_arity (fn_captures f) /\
  params_type_params_subst_noop subst_arity (fn_params f) /\
  type_params_subst_noop_ty subst_arity (fn_ret f).

Lemma subst_type_params_ty_go_noop :
  forall sigma args fallback,
    Datatypes.length args >= Datatypes.length fallback ->
    Forall (fun T => subst_type_params_ty sigma T = T) args ->
    ((fix go (xs fallback0 : list Ty) {struct xs} : list Ty :=
        match xs with
        | [] => fallback0
        | x :: rest =>
            match fallback0 with
            | [] => subst_type_params_ty sigma x :: go rest []
            | _ :: fb => subst_type_params_ty sigma x :: go rest fb
            end
        end) args fallback) = args.
Proof.
  intros sigma args.
  induction args as [| T args IH]; intros fallback Hlen Hnoop.
  - destruct fallback; simpl in *; [reflexivity | lia].
  - inversion Hnoop as [| ? ? Hhead Htail]; subst.
    destruct fallback as [| F fallback]; simpl in *.
    + rewrite Hhead. f_equal.
      apply (IH []); [apply le_0_n | exact Htail].
    + rewrite Hhead. f_equal.
      apply (IH fallback); [lia | exact Htail].
Qed.

Lemma subst_type_params_ty_list_noop :
  forall sigma args,
    Forall (fun T => subst_type_params_ty sigma T = T) args ->
    ((fix go (xs : list Ty) : list Ty :=
        match xs with
        | [] => []
        | x :: rest => subst_type_params_ty sigma x :: go rest
        end) args) = args.
Proof.
  intros sigma args Hnoop.
  induction Hnoop as [| T args Hhead Htail IH].
  - reflexivity.
  - simpl. rewrite Hhead, IH. reflexivity.
Qed.

Lemma subst_type_params_ty_noop_of_bounded_zero_and_no_fallback_fuel :
  forall fuel_bounded fuel_fallback sigma T,
    type_params_bounded_ty_fuel fuel_bounded 0 T ->
    type_params_no_implicit_fallback_ty_fuel fuel_fallback
      (Datatypes.length sigma) T ->
    subst_type_params_ty sigma T = T.
Proof.
  induction fuel_bounded as [| fuel_bounded IH];
    intros fuel_fallback sigma [u core] Hbounded Hfallback;
    simpl in Hbounded; try contradiction.
  destruct fuel_fallback as [| fuel_fallback]; simpl in Hfallback;
    try contradiction.
  destruct core; simpl in Hbounded, Hfallback |- *; try reflexivity.
  - lia.
  - destruct Hfallback as [Hlen Hfallback].
    apply (f_equal (fun args => MkTy u (TStruct s l args))).
    eapply subst_type_params_ty_go_noop.
    + exact Hlen.
    + clear Hlen.
      induction Hbounded as [| T args Hbounded_T Hbounded_args IHbounded_args].
      * constructor.
      * inversion Hfallback as [| ? ? Hfallback_T Hfallback_args]; subst.
        constructor.
        -- eapply IH; eassumption.
        -- apply IHbounded_args. exact Hfallback_args.
  - destruct Hfallback as [Hlen Hfallback].
    apply (f_equal (fun args => MkTy u (TEnum s l args))).
    eapply subst_type_params_ty_go_noop.
    + exact Hlen.
    + clear Hlen.
      induction Hbounded as [| T args Hbounded_T Hbounded_args IHbounded_args].
      * constructor.
      * inversion Hfallback as [| ? ? Hfallback_T Hfallback_args]; subst.
        constructor.
        -- eapply IH; eassumption.
        -- apply IHbounded_args. exact Hfallback_args.
  - destruct Hbounded as [Hbounded_params Hbounded_ret].
    destruct Hfallback as [Hfallback_params Hfallback_ret].
    rewrite (subst_type_params_ty_list_noop sigma l).
    + rewrite (IH fuel_fallback sigma t); [reflexivity | exact Hbounded_ret | exact Hfallback_ret].
    + induction Hbounded_params as [| T params Hbounded_T Hbounded_params IHbounded_params].
      * constructor.
      * inversion Hfallback_params as [| ? ? Hfallback_T Hfallback_params_tail]; subst.
        constructor.
        -- eapply IH; eassumption.
        -- apply IHbounded_params. exact Hfallback_params_tail.
  - destruct Hbounded as [Hbounded_params Hbounded_ret].
    destruct Hfallback as [Hfallback_params Hfallback_ret].
    rewrite (subst_type_params_ty_list_noop sigma l0).
    + rewrite (IH fuel_fallback sigma t); [reflexivity | exact Hbounded_ret | exact Hfallback_ret].
    + induction Hbounded_params as [| T params Hbounded_T Hbounded_params IHbounded_params].
      * constructor.
      * inversion Hfallback_params as [| ? ? Hfallback_T Hfallback_params_tail]; subst.
        constructor.
        -- eapply IH; eassumption.
        -- apply IHbounded_params. exact Hfallback_params_tail.
  - rewrite (IH fuel_fallback sigma t); [reflexivity | exact Hbounded | exact Hfallback].
  - rewrite (IH fuel_fallback sigma t); [reflexivity | exact Hbounded | exact Hfallback].
Qed.

Lemma subst_type_params_ty_noop_of_subst_noop :
  forall sigma T,
    type_params_subst_noop_ty (Datatypes.length sigma) T ->
    subst_type_params_ty sigma T = T.
Proof.
  intros sigma T [[fuel_bounded Hbounded] [fuel_fallback Hfallback]].
  eapply subst_type_params_ty_noop_of_bounded_zero_and_no_fallback_fuel;
    eassumption.
Qed.

Lemma apply_type_param_noop_of_subst_noop :
  forall sigma p,
    param_type_params_subst_noop (Datatypes.length sigma) p ->
    apply_type_param sigma p = p.
Proof.
  intros sigma [m x T] Hnoop.
  unfold apply_type_param, param_type_params_subst_noop in *; simpl in *.
  rewrite subst_type_params_ty_noop_of_subst_noop; [reflexivity | exact Hnoop].
Qed.

Lemma apply_type_params_noop_of_subst_noop :
  forall sigma ps,
    params_type_params_subst_noop (Datatypes.length sigma) ps ->
    apply_type_params sigma ps = ps.
Proof.
  intros sigma ps Hnoop.
  induction Hnoop as [| p ps Hhead Htail IH].
  - reflexivity.
  - simpl. rewrite apply_type_param_noop_of_subst_noop; [rewrite IH |];
      reflexivity || exact Hhead.
Qed.

Lemma contains_lbound_ty_outer_usage_core_structural :
  forall u T,
    contains_lbound_ty (MkTy u (ty_core T)) = contains_lbound_ty T.
Proof.
  intros u [u0 core]. destruct core; reflexivity.
Qed.

Lemma existsb_contains_lbound_ty_false_of_Forall_structural :
  forall ts,
    Forall (fun T => contains_lbound_ty T = false) ts ->
    existsb contains_lbound_ty ts = false.
Proof.
  intros ts H.
  induction H as [| T ts HT _ IH]; simpl.
  - reflexivity.
  - rewrite HT, IH. reflexivity.
Qed.

Lemma contains_lbound_ty_subst_type_params_ty_closed_structural :
  forall type_args T,
    Forall (fun T => contains_lbound_ty T = false) type_args ->
    contains_lbound_ty T = false ->
    contains_lbound_ty (subst_type_params_ty type_args T) = false.
Proof.
  intros type_args T Hclosed.
  revert T.
  fix IH 1.
  intros [u core] Hnone.
  destruct core as [| | | | name | i | name lts args | name lts args
                   | params ret | env_lt params ret | n bounds body
                   | n bounds body | lt rk inner]; simpl in *; try reflexivity.
  - destruct (nth_error type_args i) as [Targ|] eqn:Hnth; simpl.
    + assert (Harg_closed : contains_lbound_ty Targ = false).
      { apply ((proj1 (@Forall_forall Ty
          (fun T => contains_lbound_ty T = false) type_args)) Hclosed Targ).
        eapply nth_error_In. exact Hnth. }
      destruct Targ as [uarg corearg]. destruct corearg; simpl in *; exact Harg_closed.
    + reflexivity.
  - apply Bool.orb_false_iff in Hnone as [Hlts Hargs].
    rewrite Hlts. simpl.
    assert (Hgo : forall args0 fallback,
      existsb contains_lbound_ty args0 = false ->
      Forall (fun T => contains_lbound_ty T = false) fallback ->
      existsb contains_lbound_ty
        ((fix go (xs fallback0 : list Ty) : list Ty :=
            match xs with
            | [] => fallback0
            | x :: xs' =>
                match fallback0 with
                | [] => subst_type_params_ty type_args x :: go xs' []
                | _ :: fb' => subst_type_params_ty type_args x :: go xs' fb'
                end
            end) args0 fallback) = false).
    { fix IHargs 1.
      intros args0 fallback Hargs0 Hfallback.
      destruct args0 as [| T ts]; simpl in *.
      - apply existsb_contains_lbound_ty_false_of_Forall_structural. exact Hfallback.
      - apply Bool.orb_false_iff in Hargs0 as [HT Hts].
        destruct fallback as [| Tfallback rest]; simpl.
        + rewrite (IH T HT). apply IHargs; [exact Hts | constructor].
        + rewrite (IH T HT). apply IHargs.
          * exact Hts.
          * inversion Hfallback; subst. assumption. }
    exact (Hgo args type_args Hargs Hclosed).
  - apply Bool.orb_false_iff in Hnone as [Hlts Hargs].
    rewrite Hlts. simpl.
    assert (Hgo : forall args0 fallback,
      existsb contains_lbound_ty args0 = false ->
      Forall (fun T => contains_lbound_ty T = false) fallback ->
      existsb contains_lbound_ty
        ((fix go (xs fallback0 : list Ty) : list Ty :=
            match xs with
            | [] => fallback0
            | x :: xs' =>
                match fallback0 with
                | [] => subst_type_params_ty type_args x :: go xs' []
                | _ :: fb' => subst_type_params_ty type_args x :: go xs' fb'
                end
            end) args0 fallback) = false).
    { fix IHargs 1.
      intros args0 fallback Hargs0 Hfallback.
      destruct args0 as [| T ts]; simpl in *.
      - apply existsb_contains_lbound_ty_false_of_Forall_structural. exact Hfallback.
      - apply Bool.orb_false_iff in Hargs0 as [HT Hts].
        destruct fallback as [| Tfallback rest]; simpl.
        + rewrite (IH T HT). apply IHargs; [exact Hts | constructor].
        + rewrite (IH T HT). apply IHargs.
          * exact Hts.
          * inversion Hfallback; subst. assumption. }
    exact (Hgo args type_args Hargs Hclosed).
  - apply Bool.orb_false_iff in Hnone as [Hparams Hret].
    assert (Hparams_subst :
      existsb contains_lbound_ty
        ((fix go (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => subst_type_params_ty type_args x :: go xs'
            end) params) = false).
    { revert params Hparams.
      fix IHparams 1.
      intros params Hparams.
      destruct params as [| T ts]; simpl in *.
      - reflexivity.
      - apply Bool.orb_false_iff in Hparams as [HT Hts].
        rewrite (IH T HT), (IHparams ts Hts). reflexivity. }
    rewrite Hparams_subst, (IH ret Hret). reflexivity.
  - apply Bool.orb_false_iff in Hnone as [Hleft Hret].
    apply Bool.orb_false_iff in Hleft as [Hlt Hparams].
    rewrite Hlt.
    assert (Hparams_subst :
      existsb contains_lbound_ty
        ((fix go (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => subst_type_params_ty type_args x :: go xs'
            end) params) = false).
    { revert params Hparams.
      fix IHparams 1.
      intros params Hparams.
      destruct params as [| T ts]; simpl in *.
      - reflexivity.
      - apply Bool.orb_false_iff in Hparams as [HT Hts].
        rewrite (IH T HT), (IHparams ts Hts). reflexivity. }
    rewrite Hparams_subst, (IH ret Hret). reflexivity.
  - apply Bool.orb_false_iff in Hnone as [Hout Hbody].
    rewrite Hout, (IH body Hbody). reflexivity.
  - exact Hnone.
  - apply Bool.orb_false_iff in Hnone as [Hlt Hinner].
    rewrite Hlt, (IH inner Hinner). reflexivity.
Qed.

Lemma usage_eqb_refl : forall u,
  usage_eqb u u = true.
Proof.
  destruct u; reflexivity.
Qed.

Lemma ref_kind_eqb_refl : forall rk,
  ref_kind_eqb rk rk = true.
Proof.
  destruct rk; reflexivity.
Qed.

Lemma lifetime_list_eqb_refl : forall lts,
  lifetime_list_eqb lts lts = true.
Proof.
  induction lts as [| lt lts IH]; simpl; auto.
  apply andb_true_iff. split.
  - apply lifetime_eqb_eq. reflexivity.
  - exact IH.
Qed.

Lemma outlives_ctx_eqb_refl : forall Omega,
  outlives_ctx_eqb Omega Omega = true.
Proof.
  induction Omega as [| [a b] Omega IH]; simpl; auto.
  apply andb_true_iff. split.
  - unfold lifetime_pair_eqb; simpl.
    apply andb_true_iff. split; apply lifetime_eqb_eq; reflexivity.
  - exact IH.
Qed.

Lemma ty_eqb_refl : forall T,
  ty_eqb T T = true.
Proof.
  assert (Hsize : forall n T,
      ty_depth T < n ->
      ty_eqb T T = true).
  {
    induction n as [| n IH]; intros [u c] Hlt.
    - simpl in Hlt. lia.
    - simpl.
      rewrite usage_eqb_refl.
      destruct c as [| | | | s | i | name lts args | name lts args
                     | ts r | lc cts cr | k Omega body
                     | k bounds body | l rk inner];
        simpl; try reflexivity.
      + rewrite String.eqb_refl. reflexivity.
      + rewrite Nat.eqb_refl. reflexivity.
      + rewrite String.eqb_refl, lifetime_list_eqb_refl. simpl.
        revert Hlt. induction args as [| t args IHargs]; intros Hlt; simpl; auto.
        rewrite (IH t); [| simpl in Hlt; lia].
        rewrite IHargs; [reflexivity | eapply Nat.le_lt_trans; [| exact Hlt]; simpl; lia].
      + rewrite String.eqb_refl, lifetime_list_eqb_refl. simpl.
        revert Hlt. induction args as [| t args IHargs]; intros Hlt; simpl; auto.
        rewrite (IH t); [| simpl in Hlt; lia].
        rewrite IHargs; [reflexivity | eapply Nat.le_lt_trans; [| exact Hlt]; simpl; lia].
      + revert Hlt. induction ts as [| t ts IHts]; intros Hlt; simpl.
        * apply IH. simpl in Hlt. lia.
        * rewrite (IH t); [| simpl in Hlt; lia].
          apply IHts. eapply Nat.le_lt_trans; [| exact Hlt]; simpl; lia.
      + assert (Hlc : lifetime_eqb lc lc = true) by (apply lifetime_eqb_eq; reflexivity).
        rewrite Hlc. simpl.
        revert Hlt. induction cts as [| t cts IHts]; intros Hlt; simpl.
        * apply IH. simpl in Hlt. lia.
        * rewrite (IH t); [| simpl in Hlt; lia].
          apply IHts. eapply Nat.le_lt_trans; [| exact Hlt]; simpl; lia.
      + rewrite Nat.eqb_refl, outlives_ctx_eqb_refl. simpl.
        apply IH. simpl in Hlt. lia.
      + rewrite Nat.eqb_refl. simpl.
        assert (Hbounds :
          (fix go_bounds (xs ys : list (core_trait_bound Ty)) : bool :=
             match xs with
             | [] => match ys with | [] => true | _ :: _ => false end
             | x :: xs' =>
                 match ys with
                 | [] => false
                 | y :: ys' =>
                     Nat.eqb (core_bound_type_index Ty x) (core_bound_type_index Ty y) &&
                     (fix go_refs (rs ss : list (core_trait_ref Ty)) : bool :=
                        match rs with
                        | [] => match ss with | [] => true | _ :: _ => false end
                        | r :: rs' =>
                            match ss with
                            | [] => false
                            | s :: ss' =>
                                String.eqb (core_trait_ref_name Ty r) (core_trait_ref_name Ty s) &&
                                (fix go_args (as_ bs : list Ty) : bool :=
                                   match as_ with
                                   | [] => match bs with | [] => true | _ :: _ => false end
                                   | a :: as' =>
                                       match bs with
                                       | [] => false
                                       | b :: bs' => ty_eqb a b && go_args as' bs'
                                       end
                                   end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                                go_refs rs' ss'
                            end
                        end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
                     go_bounds xs' ys'
                 end
             end) bounds bounds = true).
        {
          revert Hlt.
          induction bounds as [| [idx refs] bounds IHbounds]; intros Hlt; simpl; auto.
          rewrite Nat.eqb_refl. simpl.
          assert (Hrefs :
            (fix go_refs (rs ss : list (core_trait_ref Ty)) : bool :=
               match rs with
               | [] => match ss with | [] => true | _ :: _ => false end
               | r :: rs' =>
                   match ss with
                   | [] => false
                   | s :: ss' =>
                       String.eqb (core_trait_ref_name Ty r) (core_trait_ref_name Ty s) &&
                       (fix go_args (as_ bs : list Ty) : bool :=
                          match as_ with
                          | [] => match bs with | [] => true | _ :: _ => false end
                          | a :: as' =>
                              match bs with
                              | [] => false
                              | b :: bs' => ty_eqb a b && go_args as' bs'
                              end
                          end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                       go_refs rs' ss'
                   end
               end) refs refs = true).
          {
            revert Hlt.
            induction refs as [| [tr_name tr_args] refs IHrefs]; intros Hlt; simpl; auto.
            rewrite String.eqb_refl. simpl.
            assert (Hargs :
              (fix go_args (as_ bs : list Ty) : bool :=
                 match as_ with
                 | [] => match bs with | [] => true | _ :: _ => false end
                 | a :: as' =>
                     match bs with
                     | [] => false
                     | b :: bs' => ty_eqb a b && go_args as' bs'
                     end
                 end) tr_args tr_args = true).
            {
              revert Hlt.
              induction tr_args as [| arg tr_args IHargs]; intros Hlt; simpl; auto.
              rewrite (IH arg); [| simpl in Hlt; lia].
              rewrite IHargs; [reflexivity | eapply Nat.lt_le_trans; [| exact Hlt]; simpl; lia].
            }
            rewrite Hargs, IHrefs; [reflexivity | eapply Nat.lt_le_trans; [| exact Hlt]; simpl; lia].
          }
          rewrite Hrefs, IHbounds; [reflexivity | eapply Nat.lt_le_trans; [| exact Hlt]; simpl; lia].
        }
        rewrite Hbounds. simpl.
        apply IH. simpl in Hlt. lia.
      + assert (Hl : lifetime_eqb l l = true) by (apply lifetime_eqb_eq; reflexivity).
        rewrite Hl, ref_kind_eqb_refl. simpl.
        apply IH. simpl in Hlt. lia.
  }
  intros T. exact (Hsize (S (ty_depth T)) T (Nat.lt_succ_diag_r _)).
Qed.

Lemma ty_core_eqb_refl : forall c,
  ty_core_eqb c c = true.
Proof.
  intros c.
  destruct c as [| | | | s | i | name lts args | name lts args
                 | ts r | lc cts cr | k Omega body
                 | k bounds body | l rk inner];
    simpl; try reflexivity.
  - rewrite String.eqb_refl. reflexivity.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite String.eqb_refl, lifetime_list_eqb_refl. simpl.
    induction args as [| t args IHargs]; simpl; auto.
    rewrite ty_eqb_refl, IHargs. reflexivity.
  - rewrite String.eqb_refl, lifetime_list_eqb_refl. simpl.
    induction args as [| t args IHargs]; simpl; auto.
    rewrite ty_eqb_refl, IHargs. reflexivity.
  - induction ts as [| t ts IHts]; simpl.
    + apply ty_eqb_refl.
    + rewrite ty_eqb_refl. simpl. exact IHts.
  - assert (Hlc : lifetime_eqb lc lc = true) by (apply lifetime_eqb_eq; reflexivity).
    rewrite Hlc.
    induction cts as [| t cts IHts]; simpl.
    + apply ty_eqb_refl.
    + rewrite ty_eqb_refl. simpl. exact IHts.
  - rewrite Nat.eqb_refl, outlives_ctx_eqb_refl. simpl.
    apply ty_eqb_refl.
  - rewrite Nat.eqb_refl. simpl.
    assert (Hbounds :
      (fix go_bounds (xs ys : list (core_trait_bound Ty)) : bool :=
         match xs with
         | [] => match ys with | [] => true | _ :: _ => false end
         | x :: xs' =>
             match ys with
             | [] => false
             | y :: ys' =>
                 Nat.eqb (core_bound_type_index Ty x) (core_bound_type_index Ty y) &&
                 (fix go_refs (rs ss : list (core_trait_ref Ty)) : bool :=
                    match rs with
                    | [] => match ss with | [] => true | _ :: _ => false end
                    | r :: rs' =>
                        match ss with
                        | [] => false
                        | s :: ss' =>
                            String.eqb (core_trait_ref_name Ty r) (core_trait_ref_name Ty s) &&
                            (fix go_args (as_ bs : list Ty) : bool :=
                               match as_ with
                               | [] => match bs with | [] => true | _ :: _ => false end
                               | a :: as' =>
                                   match bs with
                                   | [] => false
                                   | b :: bs' => ty_eqb a b && go_args as' bs'
                                   end
                               end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                            go_refs rs' ss'
                        end
                    end) (core_bound_traits Ty x) (core_bound_traits Ty y) &&
                 go_bounds xs' ys'
             end
         end) bounds bounds = true).
    {
      induction bounds as [| [idx refs] bounds IHbounds]; simpl; auto.
      rewrite Nat.eqb_refl. simpl.
      assert (Hrefs :
        (fix go_refs (rs ss : list (core_trait_ref Ty)) : bool :=
           match rs with
           | [] => match ss with | [] => true | _ :: _ => false end
           | r :: rs' =>
               match ss with
               | [] => false
               | s :: ss' =>
                   String.eqb (core_trait_ref_name Ty r) (core_trait_ref_name Ty s) &&
                   (fix go_args (as_ bs : list Ty) : bool :=
                      match as_ with
                      | [] => match bs with | [] => true | _ :: _ => false end
                      | a :: as' =>
                          match bs with
                          | [] => false
                          | b :: bs' => ty_eqb a b && go_args as' bs'
                          end
                      end) (core_trait_ref_args Ty r) (core_trait_ref_args Ty s) &&
                   go_refs rs' ss'
               end
           end) refs refs = true).
      {
        induction refs as [| [tr_name tr_args] refs IHrefs]; simpl; auto.
        rewrite String.eqb_refl. simpl.
        assert (Hargs :
          (fix go_args (as_ bs : list Ty) : bool :=
             match as_ with
             | [] => match bs with | [] => true | _ :: _ => false end
             | a :: as' =>
                 match bs with
                 | [] => false
                 | b :: bs' => ty_eqb a b && go_args as' bs'
                 end
             end) tr_args tr_args = true).
        {
          induction tr_args as [| arg tr_args IHargs]; simpl; auto.
          rewrite ty_eqb_refl, IHargs. reflexivity.
        }
        rewrite Hargs, IHrefs. reflexivity.
      }
      rewrite Hrefs, IHbounds. reflexivity.
    }
    rewrite Hbounds. simpl.
    apply ty_eqb_refl.
  - assert (Hl : lifetime_eqb l l = true) by (apply lifetime_eqb_eq; reflexivity).
    rewrite Hl, ref_kind_eqb_refl. simpl.
    apply ty_eqb_refl.
Qed.

Lemma ty_core_eqb_subst_type_params_same_core :
  forall type_args ua ue c,
    ty_core_eqb
      (ty_core (subst_type_params_ty type_args (MkTy ua c)))
      (ty_core (subst_type_params_ty type_args (MkTy ue c))) = true.
Proof.
  intros type_args ua ue c.
  change (MkTy ua c) with (MkTy ua (ty_core (MkTy ue c))).
  rewrite subst_type_params_ty_outer_usage_core.
  simpl. apply ty_core_eqb_refl.
Qed.

Lemma ty_compatible_b_fuel_monotone :
  forall fuel1 fuel2 Omega T_actual T_expected,
    fuel1 <= fuel2 ->
    ty_compatible_b_fuel fuel1 Omega T_actual T_expected = true ->
    ty_compatible_b_fuel fuel2 Omega T_actual T_expected = true.
Proof.
  induction fuel1 as [| fuel1 IH]; intros fuel2 Omega T_actual T_expected Hle Hcompat.
  - simpl in Hcompat. discriminate.
  - destruct fuel2 as [| fuel2]; [lia |].
    destruct T_actual as [ua ca], T_expected as [ue ce].
    simpl in *.
    apply andb_true_iff in Hcompat as [Husage Hcompat].
    rewrite Husage.
    assert (Hargs : forall actual expected,
      ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel1) Omega
        actual expected = true ->
      ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel2) Omega
        actual expected = true).
    { induction actual as [| a actual' IHargs]; intros expected Hargs;
        destruct expected as [| e expected']; simpl in *; try discriminate;
        try reflexivity.
      apply andb_true_iff in Hargs as [Hhead Htail].
      rewrite (IH fuel2 Omega e a (le_S_n _ _ Hle) Hhead).
      apply IHargs. exact Htail. }
    destruct ca, ce; simpl in *; try exact Hcompat;
      repeat match goal with
      | |- context [match ?rk with RShared => _ | RUnique => _ end] => destruct rk; simpl in *
      end;
      try exact Hcompat;
      repeat rewrite andb_assoc in *;
      repeat match goal with
      | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
      end;
      repeat match goal with
      | H : ?b = true |- context [?b] => rewrite H
      end;
      repeat match goal with
      | H : ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel1) Omega
              ?actual ?expected = true
        |- context [ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel2) Omega
              ?actual ?expected] => rewrite (Hargs actual expected H)
      | H : ty_compatible_b_fuel fuel1 Omega ?actual ?expected = true
        |- context [ty_compatible_b_fuel fuel2 Omega ?actual ?expected] =>
          rewrite (IH fuel2 Omega actual expected (le_S_n _ _ Hle) H)
      end;
      try reflexivity;
      match goal with
      | H : context [match ?bounds with [] => _ | _ :: _ => _ end]
        |- context [match ?bounds with [] => _ | _ :: _ => _ end] =>
          destruct bounds; simpl in *; try discriminate;
          apply andb_true_iff in H as [? Hrec];
          repeat match goal with
          | Hclosed : ?b = true |- context [?b] => rewrite Hclosed
          end;
          eapply IH; [lia | exact Hrec]
      end.
Qed.

Lemma fn_signature_type_params_subst_noop_captures :
  forall sigma f,
    fn_signature_type_params_subst_noop (Datatypes.length sigma) f ->
    apply_type_params sigma (fn_captures f) = fn_captures f.
Proof.
  intros sigma f [Hcaptures _].
  apply apply_type_params_noop_of_subst_noop. exact Hcaptures.
Qed.

Lemma fn_signature_type_params_subst_noop_params :
  forall sigma f,
    fn_signature_type_params_subst_noop (Datatypes.length sigma) f ->
    apply_type_params sigma (fn_params f) = fn_params f.
Proof.
  intros sigma f [_ [Hparams _]].
  apply apply_type_params_noop_of_subst_noop. exact Hparams.
Qed.

Lemma fn_signature_type_params_subst_noop_ret :
  forall sigma f,
    fn_signature_type_params_subst_noop (Datatypes.length sigma) f ->
    subst_type_params_ty sigma (fn_ret f) = fn_ret f.
Proof.
  intros sigma f [_ [_ Hret]].
  apply subst_type_params_ty_noop_of_subst_noop. exact Hret.
Qed.

Definition env_fns_signature_type_params_subst_noop
    (subst_arity : nat) (env : global_env) : Prop :=
  Forall (fn_signature_type_params_subst_noop subst_arity) (env_fns env).

Lemma env_fns_signature_type_params_subst_noop_in :
  forall (sigma : list Ty) env f,
    env_fns_signature_type_params_subst_noop (Datatypes.length sigma) env ->
    In f (env_fns env) ->
    fn_signature_type_params_subst_noop (Datatypes.length sigma) f.
Proof.
  intros sigma env f Henv Hin.
  unfold env_fns_signature_type_params_subst_noop in Henv.
  rewrite Forall_forall in Henv.
  apply Henv. exact Hin.
Qed.

Lemma env_fns_signature_type_params_subst_noop_captures :
  forall (sigma : list Ty) env f,
    env_fns_signature_type_params_subst_noop (Datatypes.length sigma) env ->
    In f (env_fns env) ->
    apply_type_params sigma (fn_captures f) = fn_captures f.
Proof.
  intros sigma env f Henv Hin.
  apply fn_signature_type_params_subst_noop_captures.
  eapply env_fns_signature_type_params_subst_noop_in; eassumption.
Qed.

Lemma env_fns_signature_type_params_subst_noop_params :
  forall (sigma : list Ty) env f,
    env_fns_signature_type_params_subst_noop (Datatypes.length sigma) env ->
    In f (env_fns env) ->
    apply_type_params sigma (fn_params f) = fn_params f.
Proof.
  intros sigma env f Henv Hin.
  apply fn_signature_type_params_subst_noop_params.
  eapply env_fns_signature_type_params_subst_noop_in; eassumption.
Qed.

Lemma env_fns_signature_type_params_subst_noop_ret :
  forall (sigma : list Ty) env f,
    env_fns_signature_type_params_subst_noop (Datatypes.length sigma) env ->
    In f (env_fns env) ->
    subst_type_params_ty sigma (fn_ret f) = fn_ret f.
Proof.
  intros sigma env f Henv Hin.
  apply fn_signature_type_params_subst_noop_ret.
  eapply env_fns_signature_type_params_subst_noop_in; eassumption.
Qed.

Lemma subst_type_params_ty_args_compose_go : forall sigma args fallback,
  ((fix go (xs fallback : list Ty) {struct xs} : list Ty :=
      match xs with
      | [] => fallback
      | x :: rest =>
          match fallback with
          | [] => subst_type_params_ty sigma x :: go rest []
          | _ :: fb => subst_type_params_ty sigma x :: go rest fb
          end
      end) args fallback) =
  compose_type_params_go sigma args fallback.
Proof.
  intros sigma args. induction args as [| T args IH]; intros [| F fallback];
    simpl; try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma typed_place_type_env_structural_subst_type_params_ctx_field_bounded :
  forall env sigma Sigma p T,
    typed_place_type_env_structural env Sigma p T ->
    (forall p0 T_parent sname lts (args : list Ty) sdef,
        typed_place_type_env_structural env Sigma p0 T_parent ->
        ty_core T_parent = TStruct sname lts args ->
        lookup_struct sname env = Some sdef ->
        Datatypes.length args = struct_type_params sdef) ->
    (forall sname lts (args : list Ty) sdef fdef,
        lookup_struct sname env = Some sdef ->
        lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
        Datatypes.length args = struct_type_params sdef ->
        type_params_bounded_ty (Datatypes.length args)
          (apply_lt_ty lts (field_ty fdef))) ->
    typed_place_type_env_structural env (subst_type_params_ctx sigma Sigma)
      p (subst_type_params_ty sigma T).
Proof.
  intros env sigma Sigma p T Hplace Hargs_ok Hfield_ok.
  induction Hplace.
  - simpl. eapply TPTES_Var.
    rewrite sctx_lookup_subst_type_params_ctx_eq.
    rewrite H. reflexivity.
  - simpl. eapply TPTES_Deref. exact IHHplace.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPTES_Field with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef).
    + exact IHHplace.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H0.
    + exact H1.
Qed.

Lemma typed_place_env_structural_subst_type_params_ctx_field_bounded :
  forall env sigma Sigma p T,
    typed_place_env_structural env Sigma p T ->
    (forall p0 T_parent sname lts (args : list Ty) sdef,
        typed_place_type_env_structural env Sigma p0 T_parent ->
        ty_core T_parent = TStruct sname lts args ->
        lookup_struct sname env = Some sdef ->
        Datatypes.length args = struct_type_params sdef) ->
    (forall sname lts (args : list Ty) sdef fdef,
        lookup_struct sname env = Some sdef ->
        lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
        Datatypes.length args = struct_type_params sdef ->
        type_params_bounded_ty (Datatypes.length args)
          (apply_lt_ty lts (field_ty fdef))) ->
    typed_place_env_structural env (subst_type_params_ctx sigma Sigma)
      p (subst_type_params_ty sigma T).
Proof.
  intros env sigma Sigma p T Hplace Hargs_ok Hfield_ok.
  induction Hplace.
  - simpl. eapply TPES_Var.
    + rewrite sctx_lookup_subst_type_params_ctx_eq.
      rewrite H. reflexivity.
    + exact H0.
  - simpl. eapply TPES_Deref. exact IHHplace.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPES_Field with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef) (T_root := subst_type_params_ty sigma T_root)
      (st := st).
    + eapply typed_place_type_env_structural_subst_type_params_ctx_field_bounded;
        eassumption.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H1.
    + exact H2.
    + exact H3.
    + rewrite sctx_lookup_subst_type_params_ctx_eq.
      rewrite H4. reflexivity.
    + exact H5.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPES_Field_Indirect with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef).
    + eapply typed_place_type_env_structural_subst_type_params_ctx_field_bounded;
        eassumption.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma typed_place_type_env_structural_subst_type_params_ctx :
  forall env sigma Sigma p T,
    typed_place_type_env_structural env Sigma p T ->
    typed_place_type_env_structural env (subst_type_params_ctx sigma Sigma)
      p (subst_type_params_ty sigma T).
Proof.
  intros env sigma Sigma p T Hplace.
  induction Hplace.
  - simpl. eapply TPTES_Var.
    rewrite sctx_lookup_subst_type_params_ctx_eq.
    rewrite H. reflexivity.
  - simpl. eapply TPTES_Deref. exact IHHplace.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPTES_Field with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef).
    + exact IHHplace.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H0.
    + exact H1.
Qed.

Lemma typed_place_env_structural_subst_type_params_ctx :
  forall env sigma Sigma p T,
    typed_place_env_structural env Sigma p T ->
    typed_place_env_structural env (subst_type_params_ctx sigma Sigma)
      p (subst_type_params_ty sigma T).
Proof.
  intros env sigma Sigma p T Hplace.
  induction Hplace.
  - simpl. eapply TPES_Var.
    + rewrite sctx_lookup_subst_type_params_ctx_eq.
      rewrite H. reflexivity.
    + exact H0.
  - simpl. eapply TPES_Deref. exact IHHplace.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPES_Field with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef) (T_root := subst_type_params_ty sigma T_root)
      (st := st).
    + eapply typed_place_type_env_structural_subst_type_params_ctx;
        eassumption.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H1.
    + exact H2.
    + exact H3.
    + rewrite sctx_lookup_subst_type_params_ctx_eq.
      rewrite H4. reflexivity.
    + exact H5.
  - rewrite (instantiate_struct_field_ty_type_subst_compose sigma lts args fdef).
    eapply TPES_Field_Indirect with
      (T_parent := subst_type_params_ty sigma T_parent)
      (sdef := sdef).
    + eapply typed_place_type_env_structural_subst_type_params_ctx;
        eassumption.
    + destruct T_parent as [u core]; simpl in *; subst core;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

Inductive place_under_unique_ref_structural (env : global_env) (Σ : sctx)
    : place -> Prop :=
  | PUURS_Deref : forall p la T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
      place_under_unique_ref_structural env Σ (PDeref p)
  | PUURS_Field : forall p f,
      place_under_unique_ref_structural env Σ p ->
      place_under_unique_ref_structural env Σ (PField p f).

Inductive writable_place_env_structural (env : global_env) (Σ : sctx)
    : place -> Prop :=
  | WPES_Var : forall x,
      sctx_lookup_mut x Σ = Some MMutable ->
      writable_place_env_structural env Σ (PVar x)
  | WPES_Deref : forall p la T u,
      typed_place_env_structural env Σ p (MkTy u (TRef la RUnique T)) ->
      writable_place_env_structural env Σ (PDeref p)
  | WPES_Field : forall p sname lts args sdef fdef T_parent,
      writable_place_env_structural env Σ p ->
      typed_place_type_env_structural env Σ p T_parent ->
      ty_core T_parent = TStruct sname lts args ->
      lookup_struct sname env = Some sdef ->
      lookup_field (field_name fdef) (struct_fields sdef) = Some fdef ->
      field_mutability fdef = MMutable ->
      writable_place_env_structural env Σ (PField p (field_name fdef)).

Inductive place_resolved_write_writable_chain
    (env : global_env) (R : root_env) (Σ : sctx) : place -> Prop :=
  | PRWWC_Direct : forall p,
      place_resolved_write_direct_parent p ->
      place_resolved_write_writable_chain env R Σ p
  | PRWWC_Deref : forall p x,
      place_resolved_write_writable_chain env R Σ p ->
      writable_place_env_structural env Σ p ->
      place_resolved_write_target R p = Some x ->
      sctx_lookup_mut x Σ = Some MMutable ->
      place_resolved_write_writable_chain env R Σ (PDeref p).

Lemma place_under_unique_ref_structural_subst_type_params_ctx :
  forall env sigma Sigma p,
    place_under_unique_ref_structural env Sigma p ->
    place_under_unique_ref_structural env (subst_type_params_ctx sigma Sigma) p.
Proof.
  intros env sigma Sigma p Hplace.
  induction Hplace.
  - eapply (PUURS_Deref env (subst_type_params_ctx sigma Sigma) p la
      (subst_type_params_ty sigma T) u).
    change (MkTy u (TRef la RUnique (subst_type_params_ty sigma T))) with
      (subst_type_params_ty sigma (MkTy u (TRef la RUnique T))).
    eapply typed_place_env_structural_subst_type_params_ctx.
    exact H.
  - eapply PUURS_Field. exact IHHplace.
Qed.

Lemma writable_place_env_structural_subst_type_params_ctx :
  forall env sigma Sigma p,
    writable_place_env_structural env Sigma p ->
    writable_place_env_structural env (subst_type_params_ctx sigma Sigma) p.
Proof.
  intros env sigma Sigma p Hplace.
  induction Hplace.
  - eapply WPES_Var.
    rewrite sctx_lookup_mut_subst_type_params_ctx.
    exact H.
  - eapply (WPES_Deref env (subst_type_params_ctx sigma Sigma) p la
      (subst_type_params_ty sigma T) u).
    change (MkTy u (TRef la RUnique (subst_type_params_ty sigma T))) with
      (subst_type_params_ty sigma (MkTy u (TRef la RUnique T))).
    eapply typed_place_env_structural_subst_type_params_ctx.
    exact H.
  - eapply (WPES_Field env (subst_type_params_ctx sigma Sigma) p sname lts
      (compose_type_params sigma args) sdef fdef
      (subst_type_params_ty sigma T_parent)).
    + exact IHHplace.
    + eapply typed_place_type_env_structural_subst_type_params_ctx.
      exact H.
    + destruct T_parent as [u core]; simpl in *; inversion H0; subst;
      unfold compose_type_params; rewrite subst_type_params_ty_args_compose_go;
      reflexivity.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma place_resolved_write_writable_chain_subst_type_params_ctx :
  forall env sigma R Sigma p,
    place_resolved_write_writable_chain env R Sigma p ->
    place_resolved_write_writable_chain env R
      (subst_type_params_ctx sigma Sigma) p.
Proof.
  intros env sigma R Sigma p Hchain.
  induction Hchain.
  - apply PRWWC_Direct. exact H.
  - eapply PRWWC_Deref.
    + exact IHHchain.
    + eapply writable_place_env_structural_subst_type_params_ctx.
      exact H.
    + exact H0.
    + rewrite sctx_lookup_mut_subst_type_params_ctx.
      exact H1.
Qed.

Lemma place_resolved_write_writable_chain_instantiate :
  forall env rho R Σ p,
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_writable_chain env (root_env_instantiate rho R) Σ p.
Proof.
  intros env rho R Σ p Hchain.
  induction Hchain.
  - apply PRWWC_Direct. exact H.
  - eapply PRWWC_Deref.
    + exact IHHchain.
    + exact H.
    + apply place_resolved_write_target_instantiate. exact H0.
    + exact H1.
Qed.

Lemma place_resolved_write_writable_chain_equiv :
  forall env R R' Σ p,
    root_env_equiv R R' ->
    place_resolved_write_writable_chain env R Σ p ->
    place_resolved_write_writable_chain env R' Σ p.
Proof.
  intros env R R' Σ p Hequiv Hchain.
  induction Hchain.
  - apply PRWWC_Direct. exact H.
  - eapply PRWWC_Deref.
    + exact IHHchain.
    + exact H.
    + eapply place_resolved_write_target_equiv; eassumption.
    + exact H1.
Qed.

(* ------------------------------------------------------------------ *)
(* Context shape preservation                                           *)
(* ------------------------------------------------------------------ *)

Inductive sctx_entry_same_binding : sctx_entry -> sctx_entry -> Prop :=
  | SESB : forall x T st1 st2 m,
      sctx_entry_same_binding (x, T, st1, m) (x, T, st2, m).

Definition sctx_same_bindings (Σ1 Σ2 : sctx) : Prop :=
  Forall2 sctx_entry_same_binding Σ1 Σ2.

Definition sctx_entry_type_eq (ce1 ce2 : sctx_entry) : Prop :=
  match ce1, ce2 with
  | (_, T1, _, _), (_, T2, _, _) => T1 = T2
  end.

Lemma sctx_entry_same_binding_refl :
  forall ce,
    sctx_entry_same_binding ce ce.
Proof.
  intros [[[x T] st] m]. constructor.
Qed.

Lemma sctx_same_bindings_refl :
  forall Σ,
    sctx_same_bindings Σ Σ.
Proof.
  intros Σ.
  induction Σ as [|ce rest IH].
  - constructor.
  - constructor.
    + apply sctx_entry_same_binding_refl.
    + exact IH.
Qed.

Lemma sctx_entry_same_binding_trans :
  forall ce1 ce2 ce3,
    sctx_entry_same_binding ce1 ce2 ->
    sctx_entry_same_binding ce2 ce3 ->
    sctx_entry_same_binding ce1 ce3.
Proof.
  intros [[[x1 T1] st1] m1] [[[x2 T2] st2] m2] [[[x3 T3] st3] m3] H12 H23.
  inversion H12; subst.
  inversion H23; subst.
  constructor.
Qed.

Lemma sctx_same_bindings_trans :
  forall Σ1 Σ2 Σ3,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_same_bindings Σ2 Σ3 ->
    sctx_same_bindings Σ1 Σ3.
Proof.
  intros Σ1 Σ2 Σ3 H12.
  revert Σ3.
  induction H12 as [|ce1 ce2 Σ1_tail Σ2_tail Hhead Htail IH]; intros Σ3 H23.
  - inversion H23; subst. constructor.
  - inversion H23; subst.
    constructor.
    + eapply sctx_entry_same_binding_trans; eassumption.
    + eapply IH.
      match goal with
      | H : Forall2 sctx_entry_same_binding Σ2_tail _ |- _ => exact H
      end.
Qed.

Lemma sctx_entry_same_binding_sym :
  forall ce1 ce2,
    sctx_entry_same_binding ce1 ce2 ->
    sctx_entry_same_binding ce2 ce1.
Proof.
  intros [[[x1 T1] st1] m1] [[[x2 T2] st2] m2] Hsame.
  inversion Hsame; subst.
  constructor.
Qed.

Lemma sctx_same_bindings_sym :
  forall Σ1 Σ2,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_same_bindings Σ2 Σ1.
Proof.
  intros Σ1 Σ2 Hsame.
  induction Hsame as [|ce1 ce2 Σ1_tail Σ2_tail Hhead Htail IH].
  - constructor.
  - constructor.
    + apply sctx_entry_same_binding_sym. exact Hhead.
    + exact IH.
Qed.

Lemma sctx_same_bindings_lookup :
  forall Σ1 Σ2 x T st,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_lookup x Σ1 = Some (T, st) ->
    exists st',
      sctx_lookup x Σ2 = Some (T, st').
Proof.
  intros Σ1 Σ2 x T st Hsame.
  induction Hsame; intros Hlookup.
  - discriminate.
  - destruct H.
    simpl in Hlookup |- *.
    match goal with
    | |- context[ident_eqb x ?y] => destruct (ident_eqb x y) eqn:Hx
    end.
    + inversion Hlookup; subst.
      eexists. reflexivity.
    + eapply IHHsame. exact Hlookup.
Qed.

Lemma sctx_same_bindings_lookup_mut :
  forall Σ1 Σ2 x m,
    sctx_same_bindings Σ1 Σ2 ->
    sctx_lookup_mut x Σ1 = Some m ->
    sctx_lookup_mut x Σ2 = Some m.
Proof.
  intros Σ1 Σ2 x m Hsame.
  induction Hsame; intros Hlookup.
  - discriminate.
  - destruct H.
    simpl in Hlookup |- *.
    match goal with
    | |- context[ident_eqb x ?y] => destruct (ident_eqb x y)
    end; [exact Hlookup |].
    eapply IHHsame. exact Hlookup.
Qed.

Lemma sctx_same_bindings_type_eq :
  forall Σ1 Σ2,
    sctx_same_bindings Σ1 Σ2 ->
    Forall2 sctx_entry_type_eq Σ1 Σ2.
Proof.
  intros Σ1 Σ2 Hsame.
  induction Hsame.
  - constructor.
  - constructor.
    + inversion H; subst. reflexivity.
    + exact IHHsame.
Qed.

Lemma sctx_same_bindings_common_type_eq :
  forall Σ Σ1 Σ2,
    sctx_same_bindings Σ Σ1 ->
    sctx_same_bindings Σ Σ2 ->
    Forall2 sctx_entry_type_eq Σ1 Σ2.
Proof.
  intros Σ Σ1 Σ2 Hleft.
  revert Σ2.
  induction Hleft as [|ce ce1 Σ_tail Σ1_tail Hhead_left Htail_left IH];
    intros Σ2 Hright.
  - inversion Hright; subst. constructor.
  - inversion Hright as [|ce' ce2 Σ_tail' Σ2_tail Hhead_right Htail_right];
      subst.
    constructor.
    + inversion Hhead_left; subst.
      inversion Hhead_right; subst.
      reflexivity.
    + eapply IH. exact Htail_right.
Qed.

Lemma sctx_update_state_same_bindings :
  forall Σ x f Σ',
    sctx_update_state x f Σ = Some Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  unfold sctx_update_state.
  intros Σ x f.
  induction Σ as [|[[[y T] st] m] rest IH]; intros Σ' Hupdate.
  - discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x y).
    + inversion Hupdate; subst. constructor.
      * constructor.
      * apply sctx_same_bindings_refl.
    + destruct (ctx_update_state x f rest) as [rest' |] eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      constructor.
      * constructor.
      * apply IH. reflexivity.
Qed.

Lemma sctx_consume_path_same_bindings :
  forall Σ x path Σ',
    sctx_consume_path Σ x path = infer_ok Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros Σ x path Σ' Hconsume.
  unfold sctx_consume_path in Hconsume.
  destruct (sctx_path_available Σ x path) as [[] | err]; try discriminate.
  destruct (sctx_update_state x (state_consume_path path) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion Hconsume; subst.
  eapply sctx_update_state_same_bindings. exact Hupdate.
Qed.

Lemma sctx_restore_path_same_bindings :
  forall Σ x path Σ',
    sctx_restore_path Σ x path = infer_ok Σ' ->
    sctx_same_bindings Σ Σ'.
Proof.
  intros Σ x path Σ' Hrestore.
  unfold sctx_restore_path in Hrestore.
  destruct (sctx_update_state x (state_restore_path path) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion Hrestore; subst.
  eapply sctx_update_state_same_bindings. exact Hupdate.
Qed.

Lemma sctx_same_bindings_remove_added :
  forall Σ Σ1 Σ2 x T m,
    sctx_same_bindings Σ Σ1 ->
    sctx_same_bindings (sctx_add x T m Σ1) Σ2 ->
    sctx_same_bindings Σ (sctx_remove x Σ2).
Proof.
  intros Σ Σ1 Σ2 x T m Hsame Hadded.
  inversion Hadded; subst.
  inversion H1; subst.
  simpl.
  rewrite ident_eqb_refl.
  eapply sctx_same_bindings_trans; eassumption.
Qed.

Lemma sctx_same_bindings_remove_added_params :
  forall ps Σ Σ2,
    sctx_same_bindings (sctx_add_params ps Σ) Σ2 ->
    sctx_same_bindings Σ (sctx_remove_params ps Σ2).
Proof.
  induction ps as [| p ps IH]; intros Σ Σ2 Hsame; simpl in *.
  - exact Hsame.
  - destruct p as [m x T]. simpl in *.
    apply IH.
    eapply sctx_same_bindings_remove_added.
    + apply sctx_same_bindings_refl.
    + exact Hsame.
Qed.

Lemma ctx_merge_same_bindings_left :
  forall Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    sctx_same_bindings Σ2 Σ4.
Proof.
  intros Σ2.
  induction Σ2 as [|[[[x T] st2] m] tail2 IH]; intros Σ3 Σ4 Hmerge.
  - destruct Σ3 as [|ce3 tail3]; simpl in Hmerge; try discriminate.
    inversion Hmerge; subst. constructor.
  - destruct Σ3 as [|[[[x3 T3] st3] m3] tail3]; simpl in Hmerge; try discriminate.
    destruct (negb (ident_eqb x x3)) eqn:Hneq; try discriminate.
    destruct (ctx_merge tail2 tail3) as [tail4 |] eqn:Htail; try discriminate.
    destruct (ty_usage T); try (inversion Hmerge; subst; constructor; [constructor | eapply IH; exact Htail]).
    destruct (Bool.eqb (st_consumed st2) (st_consumed st3)); try discriminate.
    inversion Hmerge; subst.
    constructor.
    + constructor.
    + eapply IH. exact Htail.
Qed.

Lemma ctx_merge_same_bindings_right :
  forall Σ2 Σ3 Σ4,
    sctx_same_bindings Σ2 Σ3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    sctx_same_bindings Σ3 Σ4.
Proof.
  intros Σ2 Σ3 Σ4 Hsame Hmerge.
  eapply sctx_same_bindings_trans.
  - apply sctx_same_bindings_sym. exact Hsame.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
Qed.

Lemma ctx_merge_many_same_bindings_left :
  forall Σ tail Γ,
    ctx_merge_many (ctx_of_sctx Σ) (map ctx_of_sctx tail) = Some Γ ->
    sctx_same_bindings Σ (sctx_of_ctx Γ).
Proof.
  intros Σ tail.
  revert Σ.
  induction tail as [|Σh rest IH]; intros Σ Γ Hmerge.
  - simpl in Hmerge. inversion Hmerge; subst. apply sctx_same_bindings_refl.
  - simpl in Hmerge.
    destruct (ctx_merge (ctx_of_sctx Σ) (ctx_of_sctx Σh)) as [Σm |] eqn:Hhead;
      try discriminate.
    eapply sctx_same_bindings_trans.
    + eapply ctx_merge_same_bindings_left. exact Hhead.
    + eapply IH. exact Hmerge.
Qed.

Inductive typed_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> expr -> Ty -> sctx -> Prop :=
  | TES_Unit : forall Σ,
      typed_env_structural env Ω n Σ EUnit (MkTy UUnrestricted TUnits) Σ
  | TES_LitInt : forall Σ i,
      typed_env_structural env Ω n Σ (ELit (LInt i)) (MkTy UUnrestricted TIntegers) Σ
  | TES_LitFloat : forall Σ f,
      typed_env_structural env Ω n Σ (ELit (LFloat f)) (MkTy UUnrestricted TFloats) Σ
  | TES_LitBool : forall Σ b,
      typed_env_structural env Ω n Σ (ELit (LBool b)) (MkTy UUnrestricted TBooleans) Σ
  | TES_Var_Copy : forall Σ x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EVar x) T Σ
  | TES_Var_Move : forall Σ Σ' x T,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EVar x) T Σ'
  | TES_Place_Copy : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ
  | TES_Place_Move : forall Σ Σ' p T x path,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      typed_env_structural env Ω n Σ (EPlace p) T Σ'
  | TES_Fn : forall Σ fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_structural env Ω n Σ (EFn fname) (fn_value_ty fdef) Σ
  | TES_MakeClosure : forall Σ fname fdef captures env_lt captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) =
        infer_ok (env_lt, captured_tys) ->
      typed_env_structural env Ω n Σ (EMakeClosure fname captures)
        (closure_value_ty_at env_lt fdef captured_tys) Σ
  | TES_MakeClosure_Static : forall Σ fname fdef captures captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx env Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_structural env Ω n Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ
  | TES_Struct : forall Σ Σ' sname lts args fields sdef,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      typed_fields_env_structural env Ω n lts args Σ fields (struct_fields sdef) Σ' ->
      typed_env_structural env Ω n Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ'
  | TES_Enum : forall Σ Σ' enum_name variant_name lts args payloads edef vdef,
      lookup_enum enum_name env = Some edef ->
      lookup_enum_variant variant_name (enum_variants edef) = Some vdef ->
      Datatypes.length lts = enum_lifetimes edef ->
      Datatypes.length args = enum_type_params edef ->
      check_struct_bounds env (enum_bounds edef) args = None ->
      typed_args_env_structural env Ω n Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (enum_variant_fields vdef))) Σ' ->
      typed_env_structural env Ω n Σ
        (EEnum enum_name variant_name lts args payloads)
        (instantiate_enum_ty edef lts args) Σ'
  | TES_Let : forall Σ Σ1 Σ2 m x T T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      ty_compatible_b Ω T1 T = true ->
      typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
      sctx_check_ok env x T Σ2 = true ->
      typed_env_structural env Ω n Σ (ELet m x T e1 e2) T2 (sctx_remove x Σ2)
  | TES_LetInfer : forall Σ Σ1 Σ2 m x T1 e1 e2 T2,
      typed_env_structural env Ω n Σ e1 T1 Σ1 ->
      typed_env_structural env Ω n (sctx_add x T1 m Σ1) e2 T2 Σ2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      typed_env_structural env Ω n Σ (ELetInfer m x e1 e2) T2 (sctx_remove x Σ2)
  | TES_Drop : forall Σ Σ' e T,
      typed_env_structural env Ω n Σ e T Σ' ->
      typed_env_structural env Ω n Σ (EDrop e) (MkTy UUnrestricted TUnits) Σ'
  | TES_Replace_Path : forall Σ Σ1 Σ2 p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ2
  | TES_Replace_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = None ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ'
  | TES_Assign_Path : forall Σ Σ' p e_new T_old T_new x path,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_Assign_Indirect : forall Σ Σ' p e_new T_old T_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = None ->
      writable_place_env_structural env Σ p ->
      typed_env_structural env Ω n Σ e_new T_new Σ' ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_structural env Ω n Σ (EAssign p e_new) (MkTy UUnrestricted TUnits) Σ'
  | TES_BorrowShared : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_structural env Ω n Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ
  | TES_BorrowUnique : forall Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_BorrowUnique_Indirect : forall Σ p T,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      typed_env_structural env Ω n Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ
  | TES_Deref_Place : forall Σ r p la rk T u,
      expr_as_place r = Some p ->
      typed_place_env_structural env Σ p (MkTy u (TRef la rk T)) ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ
  | TES_Deref_Expr : forall Σ Σ' r la rk T u,
      expr_as_place r = None ->
      typed_env_structural env Ω n Σ r (MkTy u (TRef la rk T)) Σ' ->
      ty_usage T = UUnrestricted ->
      typed_env_structural env Ω n Σ (EDeref r) T Σ'
  | TES_If : forall Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3,
      typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
      ty_core T_cond = TBooleans ->
      typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
      typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      typed_env_structural env Ω n Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)) Σ4
  | TES_Match : forall Σ Σ1 Σ_head_payload Σ_head Σ_tail Γ_out scrut branches
        enum_name lts args edef v_head v_tail e_head T_scrut T_head Ts_tail
        binders_head ps_head,
      typed_env_structural env Ω n Σ scrut T_scrut Σ1 ->
      ty_core T_scrut = TEnum enum_name lts args ->
      lookup_enum enum_name env = Some edef ->
      Datatypes.length lts = enum_lifetimes edef ->
      Datatypes.length args = enum_type_params edef ->
      check_struct_bounds env (enum_bounds edef) args = None ->
      first_unknown_variant_branch branches (enum_variants edef) = None ->
      enum_variants edef = v_head :: v_tail ->
      lookup_expr_branch_binders (enum_variant_name v_head) branches = Some binders_head ->
      match_payload_params binders_head lts args v_head = infer_ok ps_head ->
      params_names_nodup_b ps_head = true ->
      ctx_lookup_params_none_b ps_head Σ1 = true ->
      lookup_expr_branch (enum_variant_name v_head) branches = Some e_head ->
      typed_env_structural env Ω n (sctx_add_params ps_head Σ1)
        e_head T_head Σ_head_payload ->
      params_ok_sctx_b env ps_head Σ_head_payload = true ->
      Σ_head = sctx_remove_params ps_head Σ_head_payload ->
      typed_match_tail_env_structural env Ω n lts args Σ1 branches v_tail
        (ty_core T_head) Σ_tail Ts_tail ->
      ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail) =
        Some Γ_out ->
      typed_env_structural env Ω n Σ (EMatch scrut branches)
        (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head))
        (sctx_of_ctx Γ_out)
  | TES_Call : forall Σ Σ' fname fdef args σ,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_env_structural env Ω n Σ args (apply_lt_params σ (fn_params fdef)) Σ' ->
      Forall (fun '(a, b) => outlives Ω a b) (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_structural env Ω n Σ (ECall fname args) (apply_lt_ty σ (fn_ret fdef)) Σ'
  | TES_CallGeneric : forall Σ Σ' fname fdef (type_args : list Ty) args σ,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_env_structural env Ω n Σ args
        (apply_lt_params σ
          (apply_type_params type_args (fn_params fdef))) Σ' ->
      Forall (fun '(a, b) => outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_structural env Ω n Σ (ECallGeneric fname type_args args)
        (apply_lt_ty σ (subst_type_params_ty type_args (fn_ret fdef))) Σ'
  | TES_CallExpr_Fn : forall Σ Σ1 Σ' callee args u param_tys ret,
      typed_env_structural env Ω n Σ callee (MkTy u (TFn param_tys ret)) Σ1 ->
      typed_args_env_structural env Ω n Σ1 args (params_of_tys param_tys) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) ret Σ'
  | TES_CallExpr_Closure : forall Σ Σ1 Σ' callee args u env_lt param_tys ret,
      typed_env_structural env Ω n Σ callee (MkTy u (TClosure env_lt param_tys ret)) Σ1 ->
      typed_args_env_structural env Ω n Σ1 args (params_of_tys param_tys) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) ret Σ'
  | TES_CallExpr_Forall : forall Σ Σ1 Σ' callee args u m bounds body param_tys ret σ,
      typed_env_structural env Ω n Σ callee (MkTy u (TForall m bounds body)) Σ1 ->
      ty_core body = TFn param_tys ret ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) (open_bound_ty σ ret) Σ'
  | TES_CallExpr_Forall_Closure :
      forall Σ Σ1 Σ' callee args u m bounds body env_lt param_tys ret σ,
      typed_env_structural env Ω n Σ callee (MkTy u (TForall m bounds body)) Σ1 ->
      ty_core body = TClosure env_lt param_tys ret ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' ->
      contains_lbound_lifetime (open_bound_lifetime σ env_lt) = false ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_env_structural env Ω n Σ (ECallExpr callee args) (open_bound_ty σ ret) Σ'
  | TES_CallExpr_MixedForall :
      forall Σ Σ1 Σ' callee args u u_body m bounds type_params type_bounds body
        param_tys ret σ type_args,
      typed_env_structural env Ω n Σ callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body)))) Σ1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds σ type_bounds) type_args = None ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys))) Σ' ->
      contains_lbound_ty
        (open_bound_ty σ (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_env_structural env Ω n Σ (ECallExpr callee args)
        (open_bound_ty σ (subst_type_params_ty type_args ret)) Σ'
  | TES_CallExpr_TypeForall :
      forall Σ Σ1 Σ' callee args u m bounds body param_tys ret type_args,
      typed_env_structural env Ω n Σ callee (MkTy u (TTypeForall m bounds body)) Σ1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ' ->
      typed_env_structural env Ω n Σ (ECallExpr callee args)
        (subst_type_params_ty type_args ret) Σ'
  | TES_CallExprGeneric_TypeForall :
      forall Σ Σ1 Σ' callee args u m bounds body param_tys ret type_args,
      typed_env_structural env Ω n Σ callee (MkTy u (TTypeForall m bounds body)) Σ1 ->
      ty_core body = TFn param_tys ret ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_env_structural env Ω n Σ1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys)) Σ' ->
      typed_env_structural env Ω n Σ (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret) Σ'
  | TES_CallExpr_MakeClosure : forall Σ Σ' fname fdef captures env_lt
      captured_tys args σ,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_env_structural env Ω n Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' ->
      Forall (fun '(a, b) => outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_structural env Ω n Σ (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty σ (fn_ret fdef)) Σ'
with typed_args_env_structural (env : global_env) (Ω : outlives_ctx) (n : nat)
    : sctx -> list expr -> list param -> sctx -> Prop :=
  | TESArgs_Nil : forall Σ,
      typed_args_env_structural env Ω n Σ [] [] Σ
  | TESArgs_Cons : forall Σ Σ1 Σ2 e es p ps T_e,
      typed_env_structural env Ω n Σ e T_e Σ1 ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_env_structural env Ω n Σ1 es ps Σ2 ->
      typed_args_env_structural env Ω n Σ (e :: es) (p :: ps) Σ2
with typed_fields_env_structural
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * expr) -> list field_def -> sctx -> Prop :=
  | TESFields_Nil : forall lts args Σ fields,
      typed_fields_env_structural env Ω n lts args Σ fields [] Σ
  | TESFields_Cons : forall lts args Σ Σ1 Σ2 fields f rest e_field T_field,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_structural env Ω n Σ e_field T_field Σ1 ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_env_structural env Ω n lts args Σ1 fields rest Σ2 ->
      typed_fields_env_structural env Ω n lts args Σ fields (f :: rest) Σ2
with typed_match_tail_env_structural
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> sctx -> list (string * list ident * expr) -> list enum_variant_def ->
      TypeCore Ty -> list sctx -> list Ty -> Prop :=
  | TESMatchTail_Nil : forall lts args Σ branches expected_core,
      typed_match_tail_env_structural env Ω n lts args Σ branches []
        expected_core [] []
  | TESMatchTail_Cons : forall Σ branches v rest e T Σv_payload Σv Σs Ts
        expected_core binders ps lts args,
      lookup_expr_branch_binders (enum_variant_name v) branches = Some binders ->
      match_payload_params binders lts args v = infer_ok ps ->
      params_names_nodup_b ps = true ->
      ctx_lookup_params_none_b ps Σ = true ->
      lookup_expr_branch (enum_variant_name v) branches = Some e ->
      typed_env_structural env Ω n (sctx_add_params ps Σ) e T Σv_payload ->
      params_ok_sctx_b env ps Σv_payload = true ->
      Σv = sctx_remove_params ps Σv_payload ->
      ty_core T = expected_core ->
      typed_match_tail_env_structural env Ω n lts args Σ branches rest
        expected_core Σs Ts ->
      typed_match_tail_env_structural env Ω n lts args Σ branches (v :: rest)
        expected_core (Σv :: Σs) (T :: Ts).

Inductive typed_env_roots (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TER_Unit : forall R Σ,
      typed_env_roots env Ω n R Σ EUnit
        (MkTy UUnrestricted TUnits) Σ R []
  | TER_LitInt : forall R Σ i,
      typed_env_roots env Ω n R Σ (ELit (LInt i))
        (MkTy UUnrestricted TIntegers) Σ R []
  | TER_LitFloat : forall R Σ f,
      typed_env_roots env Ω n R Σ (ELit (LFloat f))
        (MkTy UUnrestricted TFloats) Σ R []
  | TER_LitBool : forall R Σ b,
      typed_env_roots env Ω n R Σ (ELit (LBool b))
        (MkTy UUnrestricted TBooleans) Σ R []
  | TER_Var_Copy : forall R Σ x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T = UUnrestricted ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EVar x) T Σ R roots
  | TER_Var_Move : forall R Σ Σ' x T roots,
      typed_place_env_structural env Σ (PVar x) T ->
      ty_usage T <> UUnrestricted ->
      sctx_consume_path Σ x [] = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EVar x) T Σ' R roots
  | TER_Place_Copy : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EPlace p) T Σ R roots
  | TER_Place_Move : forall R Σ Σ' p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T <> UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_consume_path Σ x path = infer_ok Σ' ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EPlace p) T Σ' R roots
  | TER_Call : forall R R' Σ Σ' fname fdef args σ arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      fn_type_params fdef = 0 ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => outlives Ω a b) (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots env Ω n R Σ (ECall fname args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TER_CallGeneric : forall R R' Σ Σ' fname fdef (type_args : list Ty) args σ arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      Datatypes.length type_args = fn_type_params fdef ->
      check_struct_bounds env (fn_bounds fdef) type_args = None ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ
          (apply_type_params type_args (fn_params fdef))) Σ' R' arg_roots ->
      Forall (fun '(a, b) => outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots env Ω n R Σ (ECallGeneric fname type_args args)
        (apply_lt_ty σ (subst_type_params_ty type_args (fn_ret fdef)))
        Σ' R' (root_sets_union arg_roots)
  | TER_Fn : forall R Σ fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      fn_captures fdef = [] ->
      typed_env_roots env Ω n R Σ (EFn fname) (fn_value_ty fdef) Σ R []
  | TER_MakeClosure : forall R Σ fname fdef captures env_lt captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures (fn_captures fdef) =
        infer_ok (env_lt, captured_tys) ->
      typed_env_roots env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty_at env_lt fdef captured_tys) Σ R []
  | TER_MakeClosure_Static : forall R Σ fname fdef captures captured_tys,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx env Ω Σ captures (fn_captures fdef) =
        infer_ok captured_tys ->
      typed_env_roots env Ω n R Σ (EMakeClosure fname captures)
        (closure_value_ty fdef captured_tys) Σ R []
  | TER_CallExpr_Fn : forall R R1 R' Σ Σ1 Σ' callee args u
      param_tys ret arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee (MkTy u (TFn param_tys ret))
        Σ1 R1 roots_callee ->
      typed_args_roots env Ω n R1 Σ1 args (params_of_tys param_tys)
        Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args) ret
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_Closure : forall R R1 R' Σ Σ1 Σ' callee args u
      env_lt param_tys ret arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee (MkTy u (TClosure env_lt param_tys ret))
        Σ1 R1 roots_callee ->
      typed_args_roots env Ω n R1 Σ1 args (params_of_tys param_tys)
        Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args) ret
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_TypeForall : forall R R1 R' Σ Σ1 Σ' callee args u
      type_params bounds body_ty param_tys ret_inner type_args arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots env Ω n R1 Σ1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args)
        (subst_type_params_ty type_args ret_inner)
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExprGeneric_TypeForall : forall R R1 R' Σ Σ1 Σ' callee args u
      type_params bounds body_ty param_tys ret_inner type_args arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee
        (MkTy u (TTypeForall type_params bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret_inner ->
      check_type_forall_bounds env bounds type_args = None ->
      typed_args_roots env Ω n R1 Σ1 args
        (params_of_tys (map (subst_type_params_ty type_args) param_tys))
        Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExprGeneric callee type_args args)
        (subst_type_params_ty type_args ret_inner)
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_MixedForall : forall R R1 R' Σ Σ1 Σ' callee args u u_body
      m bounds type_params type_bounds body_ty param_tys ret σ type_args
      arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee
        (MkTy u (TForall m bounds
          (MkTy u_body (TTypeForall type_params type_bounds body_ty))))
        Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      check_type_forall_bounds env (open_core_trait_bounds σ type_bounds) type_args = None ->
      contains_lbound_ty (open_bound_ty σ (subst_type_params_ty type_args ret)) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots env Ω n R1 Σ1 args
        (params_of_tys
          (map (open_bound_ty σ)
            (map (subst_type_params_ty type_args) param_tys)))
        Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ (subst_type_params_ty type_args ret))
        Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_Forall_Fn : forall R R1 R' Σ Σ1 Σ' callee args u
      m bounds body_ty param_tys ret σ arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TFn param_tys ret ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots env Ω n R1 Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ ret) Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_Forall_Closure : forall R R1 R' Σ Σ1 Σ' callee args u
      m bounds body_ty env_lt param_tys ret σ arg_roots roots_callee,
      typed_env_roots env Ω n R Σ callee
        (MkTy u (TForall m bounds body_ty)) Σ1 R1 roots_callee ->
      ty_core body_ty = TClosure env_lt param_tys ret ->
      contains_lbound_lifetime (open_bound_lifetime σ env_lt) = false ->
      contains_lbound_ty (open_bound_ty σ ret) = false ->
      contains_lbound_outlives (open_bound_outlives σ bounds) = false ->
      Forall (fun '(a, b) => outlives Ω a b) (open_bound_outlives σ bounds) ->
      typed_args_roots env Ω n R1 Σ1 args
        (params_of_tys (map (open_bound_ty σ) param_tys)) Σ' R' arg_roots ->
      typed_env_roots env Ω n R Σ (ECallExpr callee args)
        (open_bound_ty σ ret) Σ' R' (root_set_union roots_callee (root_sets_union arg_roots))
  | TER_CallExpr_MakeClosure : forall R R' Σ Σ' fname fdef captures
      env_lt captured_tys args σ arg_roots,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      check_make_closure_captures_sctx_with_env env Ω Σ captures
        (fn_captures fdef) = infer_ok (env_lt, captured_tys) ->
      typed_args_roots env Ω n R Σ args
        (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots ->
      Forall (fun '(a, b) => outlives Ω a b)
        (apply_lt_outlives σ (fn_outlives fdef)) ->
      typed_env_roots env Ω n R Σ
        (ECallExpr (EMakeClosure fname captures) args)
        (apply_lt_ty σ (fn_ret fdef)) Σ' R' (root_sets_union arg_roots)
  | TER_Struct : forall R R' Σ Σ' sname lts args fields sdef roots,
      lookup_struct sname env = Some sdef ->
      Datatypes.length lts = struct_lifetimes sdef ->
      Datatypes.length args = struct_type_params sdef ->
      check_struct_bounds env (struct_bounds sdef) args = None ->
      typed_fields_roots env Ω n lts args R Σ fields (struct_fields sdef) Σ' R' roots ->
      typed_env_roots env Ω n R Σ (EStruct sname lts args fields)
        (instantiate_struct_instance_ty sdef lts args) Σ' R' roots
  | TER_Enum : forall R R' Σ Σ' enum_name variant_name lts args payloads
      edef vdef payload_roots,
      lookup_enum enum_name env = Some edef ->
      lookup_enum_variant variant_name (enum_variants edef) = Some vdef ->
      Datatypes.length lts = enum_lifetimes edef ->
      Datatypes.length args = enum_type_params edef ->
      check_struct_bounds env (enum_bounds edef) args = None ->
      typed_args_roots env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args)
            (enum_variant_fields vdef))) Σ' R' payload_roots ->
      typed_env_roots env Ω n R Σ
        (EEnum enum_name variant_name lts args payloads)
        (instantiate_enum_ty edef lts args) Σ' R'
        (root_sets_union payload_roots)
  | TER_Match : forall R R1 R_payload R_head_payload R_out Σ Σ1
        Σ_head_payload Σ_head Σ_tail Γ_out scrut branches
        enum_name lts args edef v_head v_tail e_head T_scrut T_head Ts_tail
        roots_scrut roots_head roots_tail binders_head ps_head,
      typed_env_roots env Ω n R Σ scrut T_scrut Σ1 R1 roots_scrut ->
      ty_core T_scrut = TEnum enum_name lts args ->
      lookup_enum enum_name env = Some edef ->
      Datatypes.length lts = enum_lifetimes edef ->
      Datatypes.length args = enum_type_params edef ->
      check_struct_bounds env (enum_bounds edef) args = None ->
      first_unknown_variant_branch branches (enum_variants edef) = None ->
      enum_variants edef = v_head :: v_tail ->
      lookup_expr_branch_binders (enum_variant_name v_head) branches = Some binders_head ->
      match_payload_params binders_head lts args v_head = infer_ok ps_head ->
      params_names_nodup_b ps_head = true ->
      ctx_lookup_params_none_b ps_head Σ1 = true ->
      root_env_lookup_params_none_b ps_head R1 = true ->
      lookup_expr_branch (enum_variant_name v_head) branches = Some e_head ->
      R_payload = root_env_add_params_roots_same ps_head roots_scrut R1 ->
      typed_env_roots env Ω n R_payload (sctx_add_params ps_head Σ1)
        e_head T_head Σ_head_payload R_head_payload roots_head ->
      params_ok_sctx_b env ps_head Σ_head_payload = true ->
      roots_exclude_params ps_head roots_head ->
      R_out = root_env_remove_match_params ps_head R_head_payload ->
      root_env_excludes_params ps_head R_out ->
      Σ_head = sctx_remove_params ps_head Σ_head_payload ->
      typed_match_tail_roots env Ω n lts args R1 roots_scrut Σ1 branches v_tail
        (ty_core T_head) R_out Σ_tail Ts_tail roots_tail ->
      ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail) =
        Some Γ_out ->
      typed_env_roots env Ω n R Σ (EMatch scrut branches)
        (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head))
        (sctx_of_ctx Γ_out) R_out (root_sets_union (roots_head :: roots_tail))
  | TER_Let : forall R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      ty_compatible_b Ω T1 T = true ->
      root_env_lookup x R1 = None ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots env Ω n R Σ (ELet m x T e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TER_LetInfer : forall R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2,
      typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
      root_env_lookup x R1 = None ->
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Σ2 R2 roots2 ->
      sctx_check_ok env x T1 Σ2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      typed_env_roots env Ω n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Σ2) (root_env_remove x R2) roots2
  | TER_Drop : forall R R' Σ Σ' e T roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots env Ω n R Σ (EDrop e)
        (MkTy UUnrestricted TUnits) Σ' R' []
  | TER_Replace_Path : forall R R1 Σ Σ1 Σ2 p e_new T_old T_new
      x path roots_result roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      root_env_lookup x R = Some roots_result ->
      typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ1 x path = infer_ok tt ->
      sctx_restore_path Σ1 x path = infer_ok Σ2 ->
      typed_env_roots env Ω n R Σ (EReplace p e_new) T_old Σ2
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TER_Replace_Resolved : forall R R1 Σ Σ1 p e_new T_old T_new
      roots_result x roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      place_path p = None ->
      place_resolved_write_writable_chain env R Σ p ->
      place_resolved_write_target R p = Some x ->
      root_env_lookup x R = Some roots_result ->
      sctx_lookup_mut x Σ = Some MMutable ->
      writable_place_env_structural env Σ p ->
      typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_roots env Ω n R Σ (EReplace p e_new) T_old Σ1
        (root_env_update x (root_set_union roots_old roots_new) R1)
        roots_result
  | TER_Assign_Path : forall R R1 Σ Σ' p e_new T_old T_new
      x path roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = Some (x, path) ->
      writable_place_env_structural env Σ p ->
      typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      sctx_path_available Σ' x path = infer_ok tt ->
      typed_env_roots env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TER_Assign_Resolved : forall R R1 Σ Σ' p e_new T_old T_new
      x roots_old roots_new,
      typed_place_env_structural env Σ p T_old ->
      ty_usage T_old <> ULinear ->
      place_path p = None ->
      place_resolved_write_writable_chain env R Σ p ->
      place_resolved_write_target R p = Some x ->
      sctx_lookup_mut x Σ = Some MMutable ->
      writable_place_env_structural env Σ p ->
      typed_env_roots env Ω n R Σ e_new T_new Σ' R1 roots_new ->
      root_env_lookup x R1 = Some roots_old ->
      ty_compatible_b Ω T_new T_old = true ->
      typed_env_roots env Ω n R Σ (EAssign p e_new)
        (MkTy UUnrestricted TUnits) Σ'
        (root_env_update x (root_set_union roots_old roots_new) R1) []
  | TER_BorrowShared : forall R Σ p T,
      typed_place_env_structural env Σ p T ->
      typed_env_roots env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ R (root_of_place p)
  | TER_BorrowShared_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_borrow_roots R p = Some roots ->
      typed_env_roots env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ R roots
  | TER_BorrowShared_Resolved : forall R Σ p T roots x,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_resolved_roots R p = Some roots ->
      singleton_store_root roots = Some x ->
      typed_env_roots env Ω n R Σ (EBorrow RShared p)
        (MkTy UUnrestricted (TRef (LVar n) RShared T)) Σ R roots
  | TER_BorrowUnique : forall R Σ p T x path,
      typed_place_env_structural env Σ p T ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      typed_env_roots env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ R [RStore x]
  | TER_BorrowUnique_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_borrow_roots R p = Some roots ->
      typed_env_roots env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ R roots
  | TER_BorrowUnique_Resolved : forall R Σ p T roots x,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_resolved_roots R p = Some roots ->
      singleton_store_root roots = Some x ->
      typed_env_roots env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ R roots
  | TER_BorrowUnique_ResolvedTarget : forall R Σ p T x,
      typed_place_env_structural env Σ p T ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_resolved_write_writable_chain env R Σ p ->
      place_resolved_write_target R p = Some x ->
      typed_env_roots env Ω n R Σ (EBorrow RUnique p)
        (MkTy UAffine (TRef (LVar n) RUnique T)) Σ R [RStore x]
  | TER_DerefBorrowShared : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RShared p)) T Σ R roots
  | TER_DerefBorrowShared_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_root_lookup R p = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RShared p)) T Σ R roots
  | TER_DerefBorrowShared_Resolved : forall R Σ p T roots x,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_resolved_roots R p = Some roots ->
      singleton_store_root roots = Some x ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RShared p)) T Σ R roots
  | TER_DerefBorrowUnique : forall R Σ p T x path roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = Some (x, path) ->
      sctx_lookup_mut x Σ = Some MMutable ->
      root_env_lookup x R = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RUnique p)) T Σ R roots
  | TER_DerefBorrowUnique_Indirect : forall R Σ p T roots,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_root_lookup R p = Some roots ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RUnique p)) T Σ R roots
  | TER_DerefBorrowUnique_Resolved : forall R Σ p T roots x,
      typed_place_env_structural env Σ p T ->
      ty_usage T = UUnrestricted ->
      place_path p = None ->
      place_under_unique_ref_structural env Σ p ->
      place_resolved_roots R p = Some roots ->
      singleton_store_root roots = Some x ->
      typed_env_roots env Ω n R Σ (EDeref (EBorrow RUnique p)) T Σ R roots
  | TER_If : forall R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3
      T_cond T2 T3 roots_cond roots2 roots3,
      typed_env_roots env Ω n R Σ e1 T_cond Σ1 R1 roots_cond ->
      ty_core T_cond = TBooleans ->
      typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
      typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
      root_env_equiv R2 R3 ->
      typed_env_roots env Ω n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        Σ4 R2 (root_set_union roots2 roots3)
with typed_args_roots (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> list expr -> list param -> sctx -> root_env -> list root_set -> Prop :=
  | TERArgs_Nil : forall R Σ,
      typed_args_roots env Ω n R Σ [] [] Σ R []
  | TERArgs_Cons : forall R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest,
      typed_env_roots env Ω n R Σ e T_e Σ1 R1 roots ->
      ty_compatible_b Ω T_e (param_ty p) = true ->
      typed_args_roots env Ω n R1 Σ1 es ps Σ2 R2 roots_rest ->
      typed_args_roots env Ω n R Σ (e :: es) (p :: ps) Σ2 R2 (roots :: roots_rest)
with typed_fields_roots
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> root_env -> sctx -> list (string * expr) ->
      list field_def -> sctx -> root_env -> root_set -> Prop :=
  | TERFields_Nil : forall lts args R Σ fields,
      typed_fields_roots env Ω n lts args R Σ fields [] Σ R []
  | TERFields_Cons : forall lts args R R1 R2 Σ Σ1 Σ2 fields f rest
      e_field T_field roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field ->
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field ->
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) = true ->
      typed_fields_roots env Ω n lts args R1 Σ1 fields rest Σ2 R2 roots_rest ->
      typed_fields_roots env Ω n lts args R Σ fields (f :: rest) Σ2 R2
        (root_set_union roots_field roots_rest)
with typed_match_tail_roots
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : list lifetime -> list Ty -> root_env -> root_set -> sctx ->
      list (string * list ident * expr) -> list enum_variant_def ->
      TypeCore Ty -> root_env -> list sctx -> list Ty -> list root_set -> Prop :=
  | TERMatchTail_Nil : forall lts args R roots_scrut Σ branches expected_core R_out,
      typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches []
        expected_core R_out [] [] []
  | TERMatchTail_Cons : forall R R_payload Rv_payload Rv Σ branches v rest e T
      Σv_payload Σv R_out roots Σs Ts rootss expected_core
      binders ps lts args roots_scrut,
      lookup_expr_branch_binders (enum_variant_name v) branches = Some binders ->
      match_payload_params binders lts args v = infer_ok ps ->
      params_names_nodup_b ps = true ->
      ctx_lookup_params_none_b ps Σ = true ->
      root_env_lookup_params_none_b ps R = true ->
      lookup_expr_branch (enum_variant_name v) branches = Some e ->
      R_payload = root_env_add_params_roots_same ps roots_scrut R ->
      typed_env_roots env Ω n R_payload (sctx_add_params ps Σ)
        e T Σv_payload Rv_payload roots ->
      params_ok_sctx_b env ps Σv_payload = true ->
      roots_exclude_params ps roots ->
      Rv = root_env_remove_match_params ps Rv_payload ->
      root_env_excludes_params ps Rv ->
      Σv = sctx_remove_params ps Σv_payload ->
      ty_core T = expected_core ->
      root_env_equiv Rv R_out ->
      typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches rest
        expected_core R_out Σs Ts rootss ->
      typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches (v :: rest)
        expected_core R_out (Σv :: Σs) (T :: Ts) (roots :: rootss).

Scheme typed_env_roots_ind' := Induction for typed_env_roots Sort Prop
with typed_args_roots_ind' := Induction for typed_args_roots Sort Prop
with typed_fields_roots_ind' := Induction for typed_fields_roots Sort Prop
with typed_match_tail_roots_ind' := Induction for typed_match_tail_roots Sort Prop.
Combined Scheme typed_roots_ind
  from typed_env_roots_ind', typed_args_roots_ind', typed_fields_roots_ind',
    typed_match_tail_roots_ind'.

Lemma typed_args_env_structural_params_of_tys_map_param_ty :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural env Ω n Σ args ps Σ' ->
    typed_args_env_structural env Ω n Σ args
      (params_of_tys (map param_ty ps)) Σ'.
Proof.
  intros env Ω n Σ args ps Σ' Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma typed_args_roots_params_of_tys_map_param_ty :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    typed_args_roots env Ω n R Σ args
      (params_of_tys (map param_ty ps)) Σ' R' roots.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots Hargs.
  induction Hargs.
  - constructor.
  - simpl. econstructor; eauto.
Qed.

Lemma check_make_closure_captures_exact_sctx_implies_sctx :
  forall env Ω Σ captures params captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures params =
      infer_ok captured_tys ->
    check_make_closure_captures_sctx env Ω Σ captures params =
      infer_ok captured_tys.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros params captured_tys Hcheck;
    destruct params as [| cap params]; simpl in *; try discriminate.
  - exact Hcheck.
  - destruct (param_mutability cap) eqn:Hcap_mut; try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [_ Hcompat].
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures params)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    simpl. unfold binding_available_b.
    rewrite (IH params captured_rest Hrest).
    rewrite Hconsumed, Hmoved, Hcompat.
    reflexivity.
Qed.

Lemma lookup_expr_branch_local_store_names_in :
  forall x name branches e,
    lookup_expr_branch name branches = Some e ->
    In x (expr_local_store_names e) ->
    In x (match_branches_local_store_names branches).
Proof.
  intros x name branches.
  induction branches as [|[[name0 binders0] e0] rest IH]; intros e Hlookup Hin;
    simpl in Hlookup.
  - discriminate.
  - unfold match_branches_local_store_names. simpl.
    fold (match_branches_local_store_names_with expr_local_store_names rest).
    destruct (String.eqb name name0) eqn:Hname.
    + inversion Hlookup; subst.
      apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. apply in_or_app. right.
      unfold match_branches_local_store_names in IH.
      eapply IH; eauto.
Qed.

Lemma lookup_expr_branch_binders_local_store_names_in :
  forall x name branches binders,
    lookup_expr_branch_binders name branches = Some binders ->
    In x binders ->
    In x (match_branches_local_store_names branches).
Proof.
  intros x name branches.
  induction branches as [|[[name0 binders0] e0] rest IH];
    intros binders Hlookup Hin; simpl in Hlookup.
  - discriminate.
  - unfold match_branches_local_store_names. simpl.
    fold (match_branches_local_store_names_with expr_local_store_names rest).
    destruct (String.eqb name name0) eqn:Hname.
    + inversion Hlookup; subst.
      apply in_or_app. left. exact Hin.
    + apply in_or_app. right. apply in_or_app. right.
      unfold match_branches_local_store_names in IH.
      eapply IH; eauto.
Qed.

Lemma typed_roots_structural :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    typed_args_env_structural env Ω n Σ args ps Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    typed_match_tail_env_structural env Ω n lts args Σ branches variants
      expected_core Σs Ts).
Proof.
  intros env Ω n.
  apply typed_roots_ind;
    intros; try solve [econstructor; eauto].
  all: try solve [
    eapply TES_Deref_Expr;
    [ reflexivity
    | eapply TES_BorrowShared; eauto
    | assumption ]].
  all: try solve [
    eapply TES_Deref_Expr;
    [ reflexivity
    | eapply TES_BorrowUnique; eauto
    | assumption ]].
  all: try solve [
    eapply TES_Deref_Expr;
    [ reflexivity
    | eapply TES_BorrowUnique_Indirect; eauto
    | assumption ]].
Qed.

Lemma typed_env_roots_structural :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_structural env Ω n) R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_structural :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    typed_args_env_structural env Ω n Σ args ps Σ'.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_structural env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_structural :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ'.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj1 (proj2 (proj2 (typed_roots_structural env Ω n)))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Lemma typed_match_tail_roots_structural :
  forall env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    typed_match_tail_env_structural env Ω n lts args Σ branches variants
      expected_core Σs Ts.
Proof.
  intros env Ω n lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss H.
  exact (proj2 (proj2 (proj2 (typed_roots_structural env Ω n)))
    lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss H).
Qed.

Lemma typed_roots_no_shadow :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R') /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    root_env_no_shadow R ->
    True).
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros;
    try exact I;
    try solve [eauto using root_env_no_shadow_add, root_env_no_shadow_remove,
      root_env_no_shadow_update, root_env_add_params_roots_same_no_shadow,
      root_env_remove_match_params_no_shadow].
  all: try match goal with
  | Hscrut : root_env_no_shadow ?R -> root_env_no_shadow ?R1,
    Hbranch : root_env_no_shadow ?Rpayload -> root_env_no_shadow ?Rhead,
    Hbase : root_env_no_shadow ?R,
    Hpayload : ?Rpayload = root_env_add_params_roots_same ?ps ?roots ?R1,
    Hout : ?Rout = root_env_remove_match_params ?ps ?Rhead,
    Hfresh : root_env_lookup_params_none_b ?ps ?R1 = true,
    Hnodup : params_names_nodup_b ?ps = true
    |- root_env_no_shadow ?Rout =>
      subst;
      apply root_env_remove_match_params_no_shadow;
      apply Hbranch;
      apply root_env_add_params_roots_same_no_shadow;
      [ apply Hscrut; exact Hbase | exact Hfresh | exact Hnodup ]
  end.
Qed.

Lemma typed_env_roots_no_shadow :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots H.
  exact (proj1 (typed_roots_no_shadow env Ω n) R Σ e T Σ' R' roots H).
Qed.

Lemma typed_args_roots_no_shadow :
  forall env Ω n R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n R Σ args ps Σ' R' roots H.
  exact (proj1 (proj2 (typed_roots_no_shadow env Ω n))
    R Σ args ps Σ' R' roots H).
Qed.

Lemma typed_fields_roots_no_shadow :
  forall env Ω n lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_no_shadow R'.
Proof.
  intros env Ω n lts args R Σ fields defs Σ' R' roots H.
  exact (proj1 (proj2 (proj2 (typed_roots_no_shadow env Ω n)))
    lts args R Σ fields defs Σ' R' roots H).
Qed.

Theorem typed_roots_instantiate_fresh_mutual :
  forall env Ω n rho,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_env_roots env Ω n R0 Σ e T Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_args_roots env Ω n R0 Σ args ps Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        Forall2 root_set_equiv roots0
          (map (root_set_instantiate rho) roots)) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    forall R0,
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      exists R0' roots0,
        typed_fields_roots env Ω n lts args R0 Σ fields defs Σ' R0' roots0 /\
        root_env_no_shadow R0' /\
        root_env_equiv R0' (root_env_instantiate rho R') /\
        root_set_equiv roots0 (root_set_instantiate rho roots)) /\
  (forall lts args R roots_scrut Σ branches variants expected_core R_out Σs Ts rootss,
    typed_match_tail_roots env Ω n lts args R roots_scrut Σ branches variants expected_core
      R_out Σs Ts rootss ->
    root_subst_images_exclude_names (match_branches_local_store_names branches) rho ->
    forall roots_scrut0 R0 R0_out,
      root_set_equiv roots_scrut0 (root_set_instantiate rho roots_scrut) ->
      root_env_no_shadow R ->
      root_env_no_shadow R0 ->
      root_env_no_shadow R0_out ->
      root_env_equiv R0 (root_env_instantiate rho R) ->
      root_env_equiv R0_out (root_env_instantiate rho R_out) ->
      exists rootss0,
        typed_match_tail_roots env Ω n lts args R0 roots_scrut0 Σ branches variants expected_core
          R0_out Σs Ts rootss0 /\
        Forall2 root_set_equiv rootss0
          (map (root_set_instantiate rho) rootss)).
Proof.
  intros env Ω n rho.
  apply typed_roots_ind.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ i Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ f Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ b Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ x T roots Hplace Husage Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Var_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' x T roots Hplace Husage Hconsume Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_Var_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T root_name root_path place_roots Hplace Husage Hpath
      Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup root_name (root_env_instantiate rho R) =
      Some (root_set_instantiate rho place_roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      root_name (root_set_instantiate rho place_roots) HR0 Hlookup_inst)
      as [place_roots0 [Hlookup0 Hroots0]].
    exists R0, place_roots0. split; [| split; [| split]].
    + eapply TER_Place_Copy; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ Σ' p T root_name root_path place_roots Hplace Husage Hpath
      Hconsume Hlookup Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup root_name (root_env_instantiate rho R) =
      Some (root_set_instantiate rho place_roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      root_name (root_set_instantiate rho place_roots) HR0 Hlookup_inst)
      as [place_roots0 [Hlookup0 Hroots0]].
    exists R0, place_roots0. split; [| split; [| split]].
    + eapply TER_Place_Move; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R' Σ Σ' fname fdef args σ arg_roots Hin Hfname Hcaps
      Htypeparams Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TER_Call; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R' Σ Σ' fname fdef type_args args σ arg_roots Hin Hfname
      Hcaps Hlen Hbounds Hargs IHargs Houtlives Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_generic in Hfresh.
    destruct (IHargs Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TER_CallGeneric; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R Σ fname fdef Hin Hfname Hcaps Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TER_Fn; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures env_lt captured_tys Hin Hfname Hcaptures
      Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TER_MakeClosure; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R Σ fname fdef captures captured_tys Hin Hfname Hcaptures
      Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + eapply TER_MakeClosure_Static; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros R R1 R' Σ Σ1 Σ' callee args u param_tys ret arg_roots
      roots_callee Hcallee IHcallee Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_Fn; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u env_lt param_tys ret arg_roots
      roots_callee Hcallee IHcallee Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_Closure; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u type_params bounds body_ty
      param_tys ret_inner type_args arg_roots roots_callee
      Hcallee IHcallee Hbody Htf_bounds Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_TypeForall; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
       -- exact Hroots_callee0.
       -- eapply root_set_equiv_trans.
          ++ apply root_sets_union_equiv. exact Harg_roots0.
          ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u type_params bounds body_ty
      param_tys ret_inner type_args arg_roots roots_callee
      Hcallee IHcallee Hbody Htf_bounds Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr_generic in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExprGeneric_TypeForall; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
       -- exact Hroots_callee0.
       -- eapply root_set_equiv_trans.
          ++ apply root_sets_union_equiv. exact Harg_roots0.
          ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u u_body m bounds type_params
      type_bounds body_ty param_tys ret σ type_args arg_roots roots_callee
      Hcallee IHcallee Hbody Htf_bounds Hret_ok Hbounds_ok Hout Hargs IHargs
      Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_MixedForall; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u m bounds body_ty param_tys ret σ
      arg_roots roots_callee Hcallee IHcallee Hbody Hret_ok Hbounds_ok Hout
      Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_Forall_Fn; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R1 R' Σ Σ1 Σ' callee args u m bounds body_ty env_lt
      param_tys ret σ arg_roots roots_callee Hcallee IHcallee Hbody Henv_ok
      Hret_ok Hbounds_ok Hout Hargs IHargs Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_callee Hfresh_args].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; [exact Hcallee | exact HnsR]. }
    destruct (IHcallee Hfresh_callee R0 HnsR HnsR0 HR0)
      as [R10 [roots_callee0 [Hcallee0 [HnsR10 [HR10 Hroots_callee0]]]]].
    destruct (IHargs Hfresh_args R10 HnsR1 HnsR10 HR10)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_set_union roots_callee0 (root_sets_union arg_roots0)).
    split; [| split; [| split]].
    + eapply TER_CallExpr_Forall_Closure; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv.
        -- exact Hroots_callee0.
        -- eapply root_set_equiv_trans.
           ++ apply root_sets_union_equiv. exact Harg_roots0.
           ++ apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R R' Σ Σ' fname fdef captures env_lt captured_tys args σ
      arg_roots Hin Hfname Hcaptures Hargs IHargs Hout Hfresh R0 HnsR HnsR0
      HR0.
    rewrite expr_local_store_names_call_expr in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [_ Hfresh_args].
    destruct (IHargs Hfresh_args R0 HnsR HnsR0 HR0)
      as [R0' [arg_roots0 [Hargs0 [HnsR0' [HR0' Harg_roots0]]]]].
    exists R0', (root_sets_union arg_roots0). split; [| split; [| split]].
    + eapply TER_CallExpr_MakeClosure; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
      * apply root_sets_union_equiv. exact Harg_roots0.
      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R' Σ Σ' sname lts args fields sdef roots Hlookup Hlen_lts
      Hlen_args Hbounds Hfields IHfields Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_struct in Hfresh.
    destruct (IHfields Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [Hfields0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', roots0. split; [| split; [| split]].
    + eapply TER_Struct; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + exact Hroots0.
	  - intros R R' Σ Σ' enum_name variant_name lts args payloads edef vdef
	      payload_roots Hlookup Hvariant Hlen_lts Hlen_args Hbounds Hpayloads
	      IHpayloads Hfresh R0 HnsR HnsR0 HR0.
    rewrite expr_local_store_names_enum in Hfresh.
    destruct (IHpayloads Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [payload_roots0 [Hpayloads0 [HnsR0' [HR0' Hpayload_roots0]]]]].
    exists R0', (root_sets_union payload_roots0). split; [| split; [| split]].
    + eapply TER_Enum; eauto.
    + exact HnsR0'.
    + exact HR0'.
    + eapply root_set_equiv_trans.
	      * apply root_sets_union_equiv. exact Hpayload_roots0.
	      * apply root_set_equiv_sym. apply root_sets_instantiate_union_equiv.
  - intros R R1 R_payload R_head_payload R_out Σ Σ1 Σ_head_payload
      Σ_head Σ_tail Γ_out scrut branches enum_name lts args edef v_head
	      v_tail e_head T_scrut T_head Ts_tail roots_scrut roots_head
	      roots_tail binders_head ps_head Hscrut IHscrut Hcore Hlookup
	      Hlen_lts Hlen_args Hbounds Hunknown Hvariants
	      Hbinders_head Hpayload_head Hnodup_head
	      Hctx_fresh_head Hroot_fresh_head
      Hlookup_head HRpayload Hhead IHhead Hparams_ok_head Hroots_excl_head
      HRout Henv_excl_head HΣhead Htail IHtail Hmerge Hfresh R0 HnsR
      HnsR0 HR0.
    simpl in Hfresh.
    apply root_subst_images_exclude_names_app_inv in Hfresh.
    destruct Hfresh as [Hfresh_scrut Hfresh_branches].
    destruct (IHscrut Hfresh_scrut R0 HnsR HnsR0 HR0)
      as [R10 [roots_scrut0 [Hscrut0 [HnsR10 [HR10 Hroots_scrut0]]]]].
    assert (HnsR1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (Hfresh_R10 :
      root_env_lookup_params_none_b ps_head R10 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps_head :
      root_subst_images_exclude_names (ctx_names (params_ctx ps_head)) rho).
    {
      rewrite (match_payload_params_names binders_head lts args v_head ps_head
        Hpayload_head).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_head :
      root_subst_images_exclude_names (expr_local_store_names e_head) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh_branches.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps_head roots_scrut0 R10).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHhead Hfresh_head Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rhead0 [roots_head0 [Hhead0 [HnsRhead0 [HRhead0 Hroots_head0]]]]].
    assert (HnsRhead_payload : root_env_no_shadow R_head_payload).
    { eapply typed_env_roots_no_shadow; eassumption. }
    pose (Rout0 := root_env_remove_match_params ps_head Rhead0).
    assert (HnsRout0 : root_env_no_shadow Rout0).
    { unfold Rout0. apply root_env_remove_match_params_no_shadow. exact HnsRhead0. }
    assert (HRout0 : root_env_equiv Rout0 (root_env_instantiate rho R_out)).
    { subst R_out. unfold Rout0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh_branches roots_scrut0 R10 Rout0
      Hroots_scrut0 HnsR1 HnsR10 HnsRout0 HR10 HRout0)
      as [roots_tail0 [Htail0 Hroots_tail0]].
    exists Rout0, (root_sets_union (roots_head0 :: roots_tail0)).
    split; [| split; [| split]].
    + eapply TER_Match; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots_head0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRout0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
    + exact HnsRout0.
    + exact HRout0.
	    + eapply root_set_equiv_trans.
	      * apply root_sets_union_equiv.
	        simpl. constructor.
	        -- exact Hroots_head0.
	        -- exact Hroots_tail0.
      * apply root_set_equiv_sym.
        apply root_sets_instantiate_union_equiv.
	  - intros R R1 R2 Σ Σ1 Σ2 m x T T1 e1 e2 T2 roots1 roots2
	      He1 IHe1 Hcompat Hlookup_none He2 IHe2 Hcheck
      Hexcl_roots Hexcl_env Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - exact He2.
      - apply root_env_no_shadow_add; assumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TER_Let.
      * exact He10.
      * exact Hcompat.
      * exact Hlookup_R10_none.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R1 R2 Σ Σ1 Σ2 m x T1 e1 e2 T2 roots1 roots2
      He1 IHe1 Hlookup_none He2 IHe2 Hcheck
      Hexcl_roots Hexcl_env Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1) (x :: expr_local_store_names e2) rho
      Hfresh) as [Hfresh1 Hfresh_tail].
    destruct (root_subst_images_exclude_names_cons_inv
      x (expr_local_store_names e2) rho Hfresh_tail)
      as [Hfresh_x Hfresh2].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots10 [He10 [HnsR10 [HR10 Hroots10]]]]].
    assert (Hlookup_inst_none :
      root_env_lookup x (root_env_instantiate rho R1) = None).
    { apply root_env_lookup_instantiate_none. exact Hlookup_none. }
    assert (Hlookup_R10_none : root_env_lookup x R10 = None).
    { eapply root_env_equiv_lookup_none_r; eassumption. }
    assert (Hns_add : root_env_no_shadow (root_env_add x roots10 R10)).
    { apply root_env_no_shadow_add; assumption. }
    assert (Heq_add :
      root_env_equiv (root_env_add x roots10 R10)
        (root_env_instantiate rho (root_env_add x roots1 R1))).
    { eapply root_env_equiv_trans.
      - apply root_env_equiv_add.
        + exact Hroots10.
        + exact HR10.
      - apply root_env_equiv_sym.
        apply root_env_instantiate_add_equiv.
        + apply root_set_equiv_refl.
        + apply root_env_equiv_refl. }
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    assert (Hns_R2 : root_env_no_shadow R2).
    { eapply typed_env_roots_no_shadow.
      - exact He2.
      - apply root_env_no_shadow_add; assumption. }
    destruct (IHe2 Hfresh2 (root_env_add x roots10 R10)
      (root_env_no_shadow_add x roots1 R1 Hns_R1 Hlookup_none)
      Hns_add Heq_add)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    exists (root_env_remove x R20), roots20. split; [| split; [| split]].
    + eapply TER_LetInfer.
      * exact He10.
      * exact Hlookup_R10_none.
      * exact He20.
      * exact Hcheck.
      * eapply roots_exclude_equiv.
        -- apply root_set_equiv_sym. exact Hroots20.
        -- eapply root_set_instantiate_excludes_images; eassumption.
      * eapply root_env_excludes_equiv.
        -- apply root_env_equiv_sym.
           apply (root_env_equiv_remove x R20
             (root_env_instantiate rho R2)).
           ++ exact HnsR20.
           ++ apply root_env_instantiate_no_shadow. exact Hns_R2.
           ++ exact HR20.
        -- rewrite <- root_env_instantiate_remove.
           eapply root_env_instantiate_excludes_images; eassumption.
    + apply root_env_no_shadow_remove. exact HnsR20.
    + eapply root_env_equiv_trans.
      * apply root_env_equiv_remove.
        -- exact HnsR20.
        -- apply root_env_instantiate_no_shadow. exact Hns_R2.
        -- exact HR20.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_remove_equiv.
        -- exact Hns_R2.
        -- exact Hns_R2.
        -- apply root_env_equiv_refl.
    + exact Hroots20.
  - intros R R' Σ Σ' e T roots He IHe Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe Hfresh R0 HnsR HnsR0 HR0)
      as [R0' [roots0 [He0 [HnsR0' [HR0' Hroots0]]]]].
    exists R0', []. split; [| split; [| split]].
    + apply TER_Drop with (T := T) (roots := roots0). exact He0.
    + exact HnsR0'.
    + exact HR0'.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ1 Σ2 p e_new T_old T_new x path roots_result
      roots_old roots_new Hplace Hpath Hwritable Hlookup_result He_new IHe_new
      Hlookup_old Hcompat Havailable Hrestore Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TER_Replace_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ1 p e_new T_old T_new roots_result x roots_old roots_new
      Hplace Hpath Hshape Htarget Hlookup_result Hmut Hwritable He_new IHe_new
      Hlookup_old Hcompat Hfresh R0 HnsR HnsR0 HR0.
    assert (Htarget0 : place_resolved_write_target R0 p = Some x).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_target_instantiate. exact Htarget. }
    assert (Hshape0 : place_resolved_write_writable_chain env R0 Σ p).
    { eapply place_resolved_write_writable_chain_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_writable_chain_instantiate. exact Hshape. }
    assert (Hlookup_result_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots_result)).
    { apply root_env_lookup_instantiate. exact Hlookup_result. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots_result) HR0 Hlookup_result_inst)
      as [roots_result0 [Hlookup_result0 Hroots_result0]].
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      roots_result0.
    split; [| split; [| split]].
    + eapply TER_Replace_Resolved; eauto; exact Hshape0.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + exact Hroots_result0.
  - intros R R1 Σ Σ' p e_new T_old T_new x path roots_old roots_new
      Hplace Husage Hpath Hwritable He_new IHe_new Hlookup_old Hcompat
      Havailable Hfresh R0 HnsR HnsR0 HR0.
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TER_Assign_Path; eauto.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R R1 Σ Σ' p e_new T_old T_new x roots_old roots_new
      Hplace Husage Hpath Hshape Htarget Hmut Hwritable He_new IHe_new
      Hlookup_old Hcompat Hfresh R0 HnsR HnsR0 HR0.
    assert (Htarget0 : place_resolved_write_target R0 p = Some x).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_target_instantiate. exact Htarget. }
    assert (Hshape0 : place_resolved_write_writable_chain env R0 Σ p).
    { eapply place_resolved_write_writable_chain_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_writable_chain_instantiate. exact Hshape. }
    destruct (IHe_new Hfresh R0 HnsR HnsR0 HR0)
      as [R10 [roots_new0 [He_new0 [HnsR10 [HR10 Hroots_new0]]]]].
    assert (Hlookup_old_inst :
      root_env_lookup x (root_env_instantiate rho R1) =
      Some (root_set_instantiate rho roots_old)).
    { apply root_env_lookup_instantiate. exact Hlookup_old. }
    destruct (root_env_equiv_lookup_r R10 (root_env_instantiate rho R1)
      x (root_set_instantiate rho roots_old) HR10 Hlookup_old_inst)
      as [roots_old0 [Hlookup_old0 Hroots_old0]].
    exists (root_env_update x (root_set_union roots_old0 roots_new0) R10),
      [].
    split; [| split; [| split]].
    + eapply TER_Assign_Resolved; eauto; exact Hshape0.
    + apply root_env_no_shadow_update. exact HnsR10.
    + eapply root_env_equiv_trans with
        (R' := root_env_update x
          (root_set_union
            (root_set_instantiate rho roots_old)
            (root_set_instantiate rho roots_new))
          (root_env_instantiate rho R1)).
      * apply root_env_equiv_update.
        -- apply root_set_union_equiv; assumption.
        -- exact HR10.
      * apply root_env_equiv_sym.
        apply root_env_instantiate_update_union_equiv.
    + apply root_set_equiv_refl.
  - intros R Σ p T Hplace Hfresh R0 HnsR HnsR0 HR0.
    exists R0, (root_of_place p). split; [| split; [| split]].
    + constructor. exact Hplace.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_root_of_place_equiv.
  - intros R Σ p T roots Hplace Hpath Hborrow Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_borrow_roots_indirect R p Hpath). exact Hborrow. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_BorrowShared_Indirect; eauto.
      rewrite (place_borrow_roots_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots x Hplace Hpath Hresolved Hsingle
      Hfresh R0 HnsR HnsR0 HR0.
    destruct (place_resolved_roots_instantiate_singleton_equiv_result
      rho R R0 p roots x HnsR HnsR0 HR0 Hresolved Hsingle)
      as [roots0 [Hresolved0 [Hroots0 Hsingle0]]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_BorrowShared_Resolved; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path Hplace Hpath Hmut Hfresh R0 HnsR HnsR0 HR0.
    exists R0, [RStore x]. split; [| split; [| split]].
    + eapply TER_BorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_store_singleton_equiv.
  - intros R Σ p T roots Hplace Hpath Hunique Hborrow Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_borrow_roots_indirect R p Hpath). exact Hborrow. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_BorrowUnique_Indirect; eauto.
      rewrite (place_borrow_roots_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots x Hplace Hpath Hunique Hresolved Hsingle Hfresh R0
      HnsR HnsR0 HR0.
    destruct (place_resolved_roots_instantiate_singleton_equiv_result
      rho R R0 p roots x HnsR HnsR0 HR0 Hresolved Hsingle) as
      [roots0 [Hresolved0 [Hroots0 Hsingle0]]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_BorrowUnique_Resolved; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x Hplace Hpath Hunique Hchain Htarget Hfresh R0
      HnsR HnsR0 HR0.
    assert (Htarget0 : place_resolved_write_target R0 p = Some x).
    { eapply place_resolved_write_target_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_target_instantiate. exact Htarget. }
    assert (Hchain0 : place_resolved_write_writable_chain env R0 Σ p).
    { eapply place_resolved_write_writable_chain_equiv.
      - apply root_env_equiv_sym. exact HR0.
      - apply place_resolved_write_writable_chain_instantiate. exact Hchain. }
    exists R0, [RStore x]. split; [| split; [| split]].
    + eapply TER_BorrowUnique_ResolvedTarget; eauto.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_sym. apply root_set_instantiate_store_singleton_equiv.
  - intros R Σ p T x path roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowShared; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots Hplace Husage Hpath Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_root :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hlookup. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup_root. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowShared_Indirect; eauto.
      rewrite (place_root_lookup_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots x Hplace Husage Hpath Hresolved Hsingle
      Hfresh R0 HnsR HnsR0 HR0.
    destruct (place_resolved_roots_instantiate_singleton_equiv_result
      rho R R0 p roots x HnsR HnsR0 HR0 Hresolved Hsingle)
      as [roots0 [Hresolved0 [Hroots0 Hsingle0]]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowShared_Resolved; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T x path roots Hplace Husage Hpath Hmut Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_inst :
      root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      x (root_set_instantiate rho roots) HR0 Hlookup_inst)
      as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowUnique; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots Hplace Husage Hpath Hunique Hlookup
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hlookup_root :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hlookup. }
    assert (Hlookup_inst :
      root_env_lookup (root_provenance_place_name p) (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots)).
    { apply root_env_lookup_instantiate. exact Hlookup_root. }
    destruct (root_env_equiv_lookup_r R0 (root_env_instantiate rho R)
      (root_provenance_place_name p) (root_set_instantiate rho roots)
      HR0 Hlookup_inst) as [roots0 [Hlookup0 Hroots0]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowUnique_Indirect; eauto.
      rewrite (place_root_lookup_indirect R0 p Hpath). exact Hlookup0.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R Σ p T roots x Hplace Husage Hpath Hunique Hresolved Hsingle
      Hfresh R0 HnsR HnsR0 HR0.
    destruct (place_resolved_roots_instantiate_singleton_equiv_result
      rho R R0 p roots x HnsR HnsR0 HR0 Hresolved Hsingle)
      as [roots0 [Hresolved0 [Hroots0 Hsingle0]]].
    exists R0, roots0. split; [| split; [| split]].
    + eapply TER_DerefBorrowUnique_Resolved; eauto.
    + exact HnsR0.
    + exact HR0.
    + exact Hroots0.
  - intros R R1 R2 R3 Σ Σ1 Σ2 Σ3 Σ4 e1 e2 e3 T_cond T2 T3
      roots_cond roots2 roots3 He1 IHe1 Hcond He2 IHe2 He3 IHe3 Hcore
      Hmerge HR23 Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e1)
      (expr_local_store_names e2 ++ expr_local_store_names e3) rho
      Hfresh) as [Hfresh1 Hfresh23].
    destruct (root_subst_images_exclude_names_app_inv
      (expr_local_store_names e2) (expr_local_store_names e3) rho
      Hfresh23) as [Hfresh2 Hfresh3].
    destruct (IHe1 Hfresh1 R0 HnsR HnsR0 HR0)
      as [R10 [roots_cond0 [He10 [HnsR10 [HR10 Hroots_cond0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHe2 Hfresh2 R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots20 [He20 [HnsR20 [HR20 Hroots20]]]]].
    destruct (IHe3 Hfresh3 R10 Hns_R1 HnsR10 HR10)
      as [R30 [roots30 [He30 [HnsR30 [HR30 Hroots30]]]]].
    exists R20, (root_set_union roots20 roots30). split; [| split; [| split]].
    + eapply TER_If; eauto.
      eapply root_env_equiv_trans.
      * exact HR20.
      * eapply root_env_equiv_trans.
        -- apply root_env_equiv_instantiate. exact HR23.
        -- apply root_env_equiv_sym. exact HR30.
    + exact HnsR20.
    + exact HR20.
    + eapply root_set_equiv_trans.
      * apply root_set_union_equiv; eassumption.
      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros R Σ Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + constructor.
  - intros R R1 R2 Σ Σ1 Σ2 e es p ps T_e roots roots_rest
      He IHe Hcompat Hes IHes Hfresh R0 HnsR HnsR0 HR0.
    destruct (root_subst_images_exclude_names_args_cons_inv
      e es rho Hfresh) as [Hfresh_e Hfresh_es].
    destruct (IHe Hfresh_e R0 HnsR HnsR0 HR0)
      as [R10 [roots0 [He0 [HnsR10 [HR10 Hroots0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHes Hfresh_es R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hes0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (roots0 :: roots_rest0). split; [| split; [| split]].
    + eapply TERArgs_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
    + constructor; assumption.
  - intros lts args R Σ fields Hfresh R0 HnsR HnsR0 HR0.
    exists R0, []. split; [| split; [| split]].
    + constructor.
    + exact HnsR0.
    + exact HR0.
    + apply root_set_equiv_refl.
  - intros lts args R R1 R2 Σ Σ1 Σ2 fields f rest e_field T_field
      roots_field roots_rest Hlookup He_field IHe_field Hcompat Hfields IHfields
      Hfresh R0 HnsR HnsR0 HR0.
    assert (Hfresh_field :
      root_subst_images_exclude_names (expr_local_store_names e_field) rho).
    { unfold lookup_field_b in Hlookup.
      clear Hfields IHfields.
      induction fields as [| [field_name0 e0] fields IH]; simpl in *;
        try discriminate.
      destruct (String.eqb (field_name f) field_name0) eqn:Hfield.
      - inversion Hlookup. subst e0.
        apply root_subst_images_exclude_names_app_inv in Hfresh.
        exact (proj1 Hfresh).
      - apply IH.
        + exact Hlookup.
        + apply root_subst_images_exclude_names_app_inv in Hfresh.
          exact (proj2 Hfresh). }
    destruct (IHe_field Hfresh_field R0 HnsR HnsR0 HR0)
      as [R10 [roots_field0 [He_field0 [HnsR10 [HR10 Hroots_field0]]]]].
    assert (Hns_R1 : root_env_no_shadow R1).
    { eapply typed_env_roots_no_shadow; eassumption. }
    destruct (IHfields Hfresh R10 Hns_R1 HnsR10 HR10)
      as [R20 [roots_rest0 [Hfields0 [HnsR20 [HR20 Hroots_rest0]]]]].
    exists R20, (root_set_union roots_field0 roots_rest0). split; [| split; [| split]].
    + eapply TERFields_Cons; eauto.
    + exact HnsR20.
    + exact HR20.
	    + eapply root_set_equiv_trans.
	      * apply root_set_union_equiv; eassumption.
	      * apply root_set_equiv_sym. apply root_set_instantiate_union_equiv.
  - intros lts args R roots_scrut Σ branches expected_core R_out Hfresh
      roots_scrut0 R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0
      HR0_out.
    exists []. split.
    + constructor.
    + constructor.
	  - intros R R_payload Rv_payload Rv Σ branches v rest e T
	      Σv_payload Σv R_out roots Σs Ts rootss expected_core binders ps
	      lts args roots_scrut Hbinders Hpayload
	      Hnodup Hctx_fresh Hroot_fresh Hlookup HRpayload Htyped IHtyped
	      Hparams_ok Hroots_excl HRv Henv_excl HΣv Hcore Heq_tail Htail
	      IHtail Hfresh roots_scrut0
      R0 R0_out Hroots_scrut0 HnsR HnsR0 HnsR0_out HR0 HR0_out.
    assert (Hfresh_R0 : root_env_lookup_params_none_b ps R0 = true).
    { eapply root_env_lookup_params_none_b_instantiate_equiv; eassumption. }
    assert (Hfresh_ps :
      root_subst_images_exclude_names (ctx_names (params_ctx ps)) rho).
    {
      rewrite (match_payload_params_names binders lts args v ps Hpayload).
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_binders_local_store_names_in; eassumption.
    }
    assert (Hfresh_e :
      root_subst_images_exclude_names (expr_local_store_names e) rho).
    {
      eapply Forall_forall. intros x Hin.
      eapply root_subst_images_exclude_names_in.
      - exact Hfresh.
      - eapply lookup_expr_branch_local_store_names_in; eassumption.
    }
    assert (HnsRpayload : root_env_no_shadow R_payload).
    { subst R_payload. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    pose (Rpayload0 := root_env_add_params_roots_same ps roots_scrut0 R0).
    assert (HnsRpayload0 : root_env_no_shadow Rpayload0).
    { unfold Rpayload0. eapply root_env_add_params_roots_same_no_shadow; eauto. }
    assert (HRpayload0 :
      root_env_equiv Rpayload0 (root_env_instantiate rho R_payload)).
    { subst R_payload. unfold Rpayload0.
      eapply root_env_add_params_roots_same_instantiate_equiv; eauto. }
    destruct (IHtyped Hfresh_e Rpayload0 HnsRpayload HnsRpayload0 HRpayload0)
      as [Rv_payload0 [roots0 [Htyped0 [Hns_payload0 [HR_payload0 Hroots0]]]]].
    assert (HnsRv_payload : root_env_no_shadow Rv_payload).
    { eapply typed_env_roots_no_shadow; eassumption. }
    pose (Rv0 := root_env_remove_match_params ps Rv_payload0).
    assert (HnsRv0 : root_env_no_shadow Rv0).
    { unfold Rv0. apply root_env_remove_match_params_no_shadow. exact Hns_payload0. }
    assert (HRv0 : root_env_equiv Rv0 (root_env_instantiate rho Rv)).
    { subst Rv. unfold Rv0.
      eapply root_env_remove_match_params_instantiate_equiv; eauto. }
    destruct (IHtail Hfresh roots_scrut0 R0 R0_out Hroots_scrut0
      HnsR HnsR0 HnsR0_out HR0 HR0_out)
      as [rootss0 [Htail0 Hrootss0]].
    exists (roots0 :: rootss0). split.
    + eapply TERMatchTail_Cons; eauto.
      * eapply roots_exclude_params_equiv_local.
        -- apply root_set_equiv_sym. exact Hroots0.
        -- eapply roots_exclude_params_instantiate_local; eassumption.
      * eapply root_env_excludes_params_equiv_local.
        -- apply root_env_equiv_sym. exact HRv0.
        -- eapply root_env_excludes_params_instantiate_local; eassumption.
      * eapply root_env_equiv_trans.
        -- exact HRv0.
        -- eapply root_env_equiv_trans.
           ++ apply root_env_equiv_instantiate. exact Heq_tail.
           ++ apply root_env_equiv_sym. exact HR0_out.
    + simpl. constructor; assumption.
Qed.

Lemma typed_env_roots_instantiate_fresh :
  forall env Ω n rho R Σ e T Σ' R' roots R0,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_subst_images_exclude_names (expr_local_store_names e) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_env_roots env Ω n R0 Σ e T Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho R Σ e T Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (typed_roots_instantiate_fresh_mutual env Ω n rho)
    R Σ e T Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_args_roots_instantiate_fresh :
  forall env Ω n rho R Σ args ps Σ' R' roots R0,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_subst_images_exclude_names (args_local_store_names args) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_args_roots env Ω n R0 Σ args ps Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      Forall2 root_set_equiv roots0 (map (root_set_instantiate rho) roots).
Proof.
  intros env Ω n rho R Σ args ps Σ' R' roots R0 Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (typed_roots_instantiate_fresh_mutual env Ω n rho))
    R Σ args ps Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_fields_roots_instantiate_fresh :
  forall env Ω n rho lts args R Σ fields defs Σ' R' roots R0,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_subst_images_exclude_names (fields_local_store_names fields) rho ->
    root_env_no_shadow R ->
    root_env_no_shadow R0 ->
    root_env_equiv R0 (root_env_instantiate rho R) ->
    exists R0' roots0,
      typed_fields_roots env Ω n lts args R0 Σ fields defs Σ' R0' roots0 /\
      root_env_no_shadow R0' /\
      root_env_equiv R0' (root_env_instantiate rho R') /\
      root_set_equiv roots0 (root_set_instantiate rho roots).
Proof.
  intros env Ω n rho lts args R Σ fields defs Σ' R' roots R0
    Htyped Hfresh HnsR HnsR0 HR0.
  exact (proj1 (proj2 (proj2 (typed_roots_instantiate_fresh_mutual env Ω n rho)))
    lts args R Σ fields defs Σ' R' roots Htyped Hfresh R0 HnsR HnsR0 HR0).
Qed.

Lemma typed_env_structural_same_bindings :
  forall env Ω n Σ e T Σ',
    typed_env_structural env Ω n Σ e T Σ' ->
    sctx_same_bindings Σ Σ'
with typed_args_env_structural_same_bindings :
  forall env Ω n Σ args ps Σ',
    typed_args_env_structural env Ω n Σ args ps Σ' ->
    sctx_same_bindings Σ Σ'
with typed_fields_env_structural_same_bindings :
  forall env Ω n lts args Σ fields defs Σ',
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
    sctx_same_bindings Σ Σ'
with typed_match_tail_env_structural_same_bindings :
  forall env Ω n lts args Σ branches variants expected_core Σs Ts,
    typed_match_tail_env_structural env Ω n lts args Σ branches variants
      expected_core Σs Ts ->
    Forall (sctx_same_bindings Σ) Σs.
Proof.
  - intros env Ω n Σ e T Σ' Htyped.
    induction Htyped.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + eapply sctx_consume_path_same_bindings.
      match goal with
      | H : sctx_consume_path _ _ [] = infer_ok _ |- _ => exact H
      end.
    + apply sctx_same_bindings_refl.
    + eapply sctx_consume_path_same_bindings.
      match goal with
      | H : sctx_consume_path _ _ _ = infer_ok _ |- _ => exact H
      end.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + eapply typed_fields_env_structural_same_bindings.
      match goal with
      | H : typed_fields_env_structural _ _ _ _ _ _ _ _ _ |- _ => exact H
      end.
    + eapply typed_args_env_structural_same_bindings.
      match goal with
      | H : typed_args_env_structural _ _ _ _ _ _ _ |- _ => exact H
      end.
    + eapply sctx_same_bindings_remove_added.
      * exact IHHtyped1.
      * exact IHHtyped2.
    + eapply sctx_same_bindings_remove_added.
      * exact IHHtyped1.
      * exact IHHtyped2.
	    + exact IHHtyped.
	    + eapply sctx_same_bindings_trans.
      * exact IHHtyped.
      * eapply sctx_restore_path_same_bindings.
        match goal with
        | H : sctx_restore_path _ _ _ = infer_ok _ |- _ => exact H
        end.
    + exact IHHtyped.
    + exact IHHtyped.
    + exact IHHtyped.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + apply sctx_same_bindings_refl.
    + exact IHHtyped.
    + eapply sctx_same_bindings_trans.
      * eapply sctx_same_bindings_trans.
        -- exact IHHtyped1.
        -- exact IHHtyped2.
	      * eapply ctx_merge_same_bindings_left.
	        match goal with
	        | H : ctx_merge _ _ = Some _ |- _ => exact H
	        end.
	    + eapply sctx_same_bindings_trans.
	      * exact IHHtyped1.
	      * eapply sctx_same_bindings_trans.
	        -- subst; apply sctx_same_bindings_remove_added_params;
	           eapply typed_env_structural_same_bindings; eassumption.
	        -- match goal with
	           | Hremove : ?Σhead = sctx_remove_params ?ps ?Σpayload,
	             Hmerge : ctx_merge_many (ctx_of_sctx ?Σhead) _ = Some _ |- _ =>
	               rewrite <- Hremove;
	               eapply ctx_merge_many_same_bindings_left;
	               exact Hmerge
	           | Hmerge : ctx_merge_many
	               (ctx_of_sctx (sctx_remove_params ?ps ?Σpayload)) _ = Some _ |- _ =>
	               eapply ctx_merge_many_same_bindings_left;
	               exact Hmerge
	           end.
	    + eauto using typed_args_env_structural_same_bindings,
	        sctx_same_bindings_trans.
    + eauto using typed_args_env_structural_same_bindings,
        sctx_same_bindings_trans.
    + eauto using typed_args_env_structural_same_bindings,
        sctx_same_bindings_trans.
    + eauto using typed_args_env_structural_same_bindings,
        sctx_same_bindings_trans.
    + eauto using typed_args_env_structural_same_bindings,
        sctx_same_bindings_trans.
	    + eauto using typed_args_env_structural_same_bindings,
	      sctx_same_bindings_trans.
	    + eauto using typed_args_env_structural_same_bindings,
	      sctx_same_bindings_trans.
	    + eauto using typed_args_env_structural_same_bindings,
	      sctx_same_bindings_trans.
	    + eauto using typed_args_env_structural_same_bindings,
	      sctx_same_bindings_trans.
	    + eauto using typed_args_env_structural_same_bindings,
	      sctx_same_bindings_trans.
	  - intros env Ω n Σ args ps Σ' Htyped.
    induction Htyped.
    + apply sctx_same_bindings_refl.
    + eapply sctx_same_bindings_trans.
      * eapply typed_env_structural_same_bindings. exact H.
      * exact IHHtyped.
	  - intros env Ω n lts args Σ fields defs Σ' Htyped.
	    induction Htyped.
	    + apply sctx_same_bindings_refl.
	    + eapply sctx_same_bindings_trans.
	      * eapply typed_env_structural_same_bindings. exact H0.
	      * exact IHHtyped.
	  - intros env Ω n lts args Σ branches variants expected_core Σs Ts Htyped.
	    induction Htyped.
	    + constructor.
	    + constructor.
	      * subst.
	        apply sctx_same_bindings_remove_added_params.
	        eapply typed_env_structural_same_bindings. eassumption.
	      * exact IHHtyped.
Qed.

Lemma typed_env_structural_branch_type_eq :
  forall env Ω n Σ e2 T2 Σ2 e3 T3 Σ3,
    typed_env_structural env Ω n Σ e2 T2 Σ2 ->
    typed_env_structural env Ω n Σ e3 T3 Σ3 ->
    Forall2 sctx_entry_type_eq Σ2 Σ3.
Proof.
  intros env Ω n Σ e2 T2 Σ2 e3 T3 Σ3 Htyped_left Htyped_right.
  eapply sctx_same_bindings_common_type_eq.
  - eapply typed_env_structural_same_bindings. exact Htyped_left.
  - eapply typed_env_structural_same_bindings. exact Htyped_right.
Qed.

Inductive borrow_ok_env_structural (env : global_env)
    : path_borrow_state -> ctx -> expr -> path_borrow_state -> Prop :=
  | BOES_Unit : forall PBS Γ,
      borrow_ok_env_structural env PBS Γ EUnit PBS
  | BOES_Lit : forall PBS Γ l,
      borrow_ok_env_structural env PBS Γ (ELit l) PBS
  | BOES_Var : forall PBS Γ x,
      borrow_check_place_access env PBS Γ (PVar x) = infer_ok tt ->
      borrow_ok_env_structural env PBS Γ (EVar x) PBS
  | BOES_Fn : forall PBS Γ fname,
      borrow_ok_env_structural env PBS Γ (EFn fname) PBS
  | BOES_MakeClosure : forall PBS Γ fname captures,
      Forall (fun x => pbs_has_mut x [] PBS = false) captures ->
      borrow_ok_env_structural env PBS Γ (EMakeClosure fname captures) PBS
  | BOES_Place : forall PBS Γ p,
      borrow_check_place_access env PBS Γ p = infer_ok tt ->
      borrow_ok_env_structural env PBS Γ (EPlace p) PBS
  | BOES_Struct : forall PBS PBS' Γ sname lts args fields,
      borrow_ok_fields_env_structural env PBS Γ fields PBS' ->
      borrow_ok_env_structural env PBS Γ (EStruct sname lts args fields) PBS'
  | BOES_Enum : forall PBS PBS' Γ enum_name variant_name lts args payloads,
      borrow_ok_args_env_structural env PBS Γ payloads PBS' ->
      borrow_ok_env_structural env PBS Γ
        (EEnum enum_name variant_name lts args payloads) PBS'
  | BOES_Match : forall PBS PBS1 PBS2 Γ scrut name binders branch rest,
      borrow_ok_env_structural env PBS Γ scrut PBS1 ->
      borrow_ok_env_structural env PBS1
        (ctx_add_params (unrestricted_unit_params_of_binders binders) Γ)
        branch PBS2 ->
      Forall
        (fun branch0 =>
          borrow_ok_env_structural env PBS1
            (ctx_add_params
              (unrestricted_unit_params_of_binders (match_branch_binders branch0)) Γ)
            (match_branch_expr branch0) PBS2)
        rest ->
      borrow_ok_env_structural env PBS Γ (EMatch scrut ((name, binders, branch) :: rest)) PBS2
  | BOES_BorrowShared : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_mut x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RShared p) (PBShared x path :: PBS)
  | BOES_BorrowUnique : forall PBS Γ p x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ (EBorrow RUnique p) (PBMut x path :: PBS)
  | BOES_Write : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EReplace p e_new) PBS'
  | BOES_Assign : forall PBS PBS' Γ p e_new x path,
      borrow_target_of_place p = (x, path) ->
      pbs_has_any x path PBS = false ->
      borrow_ok_env_structural env PBS Γ e_new PBS' ->
      borrow_ok_env_structural env PBS Γ (EAssign p e_new) PBS'
  | BOES_Deref : forall PBS PBS' Γ e,
      match expr_ref_root e with
      | Some r => pbs_has_mut r [] PBS = false
      | None => True
      end ->
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDeref e) PBS'
  | BOES_Drop : forall PBS PBS' Γ e,
      borrow_ok_env_structural env PBS Γ e PBS' ->
      borrow_ok_env_structural env PBS Γ (EDrop e) PBS'
  | BOES_Let : forall PBS PBS1 PBS2 Γ m x T e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 (ctx_add_b x T m Γ) e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELet m x T e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_LetInfer : forall PBS PBS1 PBS2 Γ m x e1 e2,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS Γ (ELetInfer m x e1 e2)
        (pbs_remove_all (pbs_new_entries PBS PBS1) PBS2)
  | BOES_If : forall PBS PBS1 PBS2 PBS3 Γ e1 e2 e3,
      borrow_ok_env_structural env PBS Γ e1 PBS1 ->
      borrow_ok_env_structural env PBS1 Γ e2 PBS2 ->
      borrow_ok_env_structural env PBS1 Γ e3 PBS3 ->
      PBS2 = PBS3 ->
      borrow_ok_env_structural env PBS Γ (EIf e1 e2 e3) PBS2
  | BOES_Call : forall PBS PBS' Γ fname args,
      borrow_ok_args_env_structural env PBS Γ args PBS' ->
      borrow_ok_env_structural env PBS Γ (ECall fname args) PBS'
  | BOES_CallGeneric : forall PBS PBS' Γ fname type_args args,
      borrow_ok_args_env_structural env PBS Γ args PBS' ->
      borrow_ok_env_structural env PBS Γ (ECallGeneric fname type_args args) PBS'
  | BOES_CallExpr : forall PBS PBS1 PBS2 Γ callee args,
      borrow_ok_env_structural env PBS Γ callee PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ args PBS2 ->
      borrow_ok_env_structural env PBS Γ (ECallExpr callee args) PBS2
  | BOES_CallExprGeneric : forall PBS PBS1 PBS2 Γ callee type_args args,
      borrow_ok_env_structural env PBS Γ callee PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ args PBS2 ->
      borrow_ok_env_structural env PBS Γ
        (ECallExprGeneric callee type_args args) PBS2
with borrow_ok_args_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list expr -> path_borrow_state -> Prop :=
  | BOESArgs_Nil : forall PBS Γ,
      borrow_ok_args_env_structural env PBS Γ [] PBS
  | BOESArgs_Cons : forall PBS PBS1 PBS2 Γ e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_args_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_args_env_structural env PBS Γ (e :: rest) PBS2
with borrow_ok_fields_env_structural (env : global_env)
    : path_borrow_state -> ctx -> list (string * expr) -> path_borrow_state -> Prop :=
  | BOESFields_Nil : forall PBS Γ,
      borrow_ok_fields_env_structural env PBS Γ [] PBS
  | BOESFields_Cons : forall PBS PBS1 PBS2 Γ name e rest,
      borrow_ok_env_structural env PBS Γ e PBS1 ->
      borrow_ok_fields_env_structural env PBS1 Γ rest PBS2 ->
      borrow_ok_fields_env_structural env PBS Γ ((name, e) :: rest) PBS2.

Definition typed_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  exists T_body Γ_out,
    typed_env_structural (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Γ_out) /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Γ_out = true.

Definition env_fns_typed_structural (env : global_env) : Prop :=
  forall f, In f (env_fns env) -> typed_fn_env_structural env f.

Definition checked_fn_env_structural (env : global_env) (f : fn_def) : Prop :=
  typed_fn_env_structural env f /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Definition env_fns_checked_structural (env : global_env) : Prop :=
  forall f, In f (env_fns env) -> checked_fn_env_structural env f.

Lemma checked_fn_env_structural_typed :
  forall env f,
    checked_fn_env_structural env f ->
    typed_fn_env_structural env f.
Proof.
  intros env f Hchecked.
  exact (proj1 Hchecked).
Qed.

Lemma checked_fn_env_structural_params_nodup :
  forall env f,
    checked_fn_env_structural env f ->
    NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f Hchecked.
  exact (proj2 (proj2 Hchecked)).
Qed.

Lemma env_fns_checked_structural_typed :
  forall env,
    env_fns_checked_structural env ->
    env_fns_typed_structural env.
Proof.
  intros env Hchecked f Hin.
  apply checked_fn_env_structural_typed.
  apply Hchecked. exact Hin.
Qed.
