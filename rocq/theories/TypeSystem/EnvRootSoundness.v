From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program TypingRules
  RootProvenance TypeChecker EnvStructuralRules CheckerSoundness
  EnvTypingSoundness EnvBorrowSoundness.
From Stdlib Require Import Bool List String PeanoNat.
Import ListNotations.

Lemma root_set_eqb_true :
  forall a b,
    root_set_eqb a b = true ->
    a = b.
Proof.
  induction a as [| x xs IH]; intros b Heq; destruct b as [| y ys];
    simpl in Heq; try discriminate; try reflexivity.
  apply andb_true_iff in Heq as [Hxy Hxs].
  apply ident_eqb_eq in Hxy.
  apply IH in Hxs.
  subst. reflexivity.
Qed.

Lemma root_env_eqb_true :
  forall R1 R2,
    root_env_eqb R1 R2 = true ->
    R1 = R2.
Proof.
  induction R1 as [| [x1 roots1] rest1 IH]; intros R2 Heq;
    destruct R2 as [| [x2 roots2] rest2];
    simpl in Heq; try discriminate; try reflexivity.
  apply andb_true_iff in Heq as [Hhead Hrest].
  apply andb_true_iff in Hhead as [Hx Hroots].
  apply ident_eqb_eq in Hx.
  apply root_set_eqb_true in Hroots.
  apply IH in Hrest.
  subst. reflexivity.
Qed.

Lemma roots_exclude_b_sound :
  forall x roots,
    roots_exclude_b x roots = true ->
    roots_exclude x roots.
Proof.
  unfold roots_exclude_b, roots_exclude.
  intros x roots Hnot Hin.
  apply negb_true_iff in Hnot.
  assert (existsb (ident_eqb x) roots = true) as Hexists.
  { apply existsb_exists.
    exists x. split.
    - exact Hin.
    - apply ident_eqb_refl. }
  rewrite Hexists in Hnot. discriminate.
Qed.

Lemma root_env_excludes_b_sound :
  forall x R,
    root_env_excludes_b x R = true ->
    root_env_excludes x R.
Proof.
  unfold root_env_excludes.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros Hexcl z roots Hlookup Hneq;
    simpl in *; try discriminate.
  apply andb_true_iff in Hexcl as [Hhead Hrest].
  destruct (ident_eqb z y) eqn:Hz.
  - inversion Hlookup; subst roots_y; clear Hlookup.
    destruct (ident_eqb x y) eqn:Hxy.
    + apply ident_eqb_eq in Hxy. subst y.
      apply ident_eqb_eq in Hz. subst z.
      contradiction Hneq. reflexivity.
    + eapply roots_exclude_b_sound. exact Hhead.
  - eapply IH; eassumption.
Qed.

Lemma root_of_place_direct :
  forall p x path,
    place_path p = Some (x, path) ->
    root_of_place p = [x].
Proof.
  intros p x path Hpath.
  unfold root_of_place.
  rewrite Hpath.
  reflexivity.
Qed.

Fixpoint infer_env_fields_collect_roots fuel env Ω n lts args
    (R : root_env) (Σ : sctx) (fields : list (string * expr))
    (defs : list field_def)
    : infer_result (sctx * root_env * root_set) :=
  match defs with
  | [] => infer_ok (Σ, R, [])
  | f :: rest =>
      match lookup_field_b (field_name f) fields with
      | None => infer_err (ErrMissingField (field_name f))
      | Some e_field =>
          match infer_core_env_state_fuel_roots fuel env Ω n R Σ e_field with
          | infer_err err => infer_err err
          | infer_ok (T_field, Σ1, R1, roots_field) =>
              let T_expected := instantiate_struct_field_ty lts args f in
              if ty_compatible_b Ω T_field T_expected
              then
                match infer_env_fields_collect_roots fuel env Ω n lts args R1 Σ1 fields rest with
                | infer_err err => infer_err err
                | infer_ok (Σ2, R2, roots_rest) =>
                    infer_ok (Σ2, R2, root_set_union roots_field roots_rest)
                end
              else infer_err (compatible_error T_field T_expected)
          end
      end
  end.

Lemma infer_env_fields_collect_roots_eq :
  forall fuel env Ω n lts args fields defs R Σ,
    (fix go (Σ0 : sctx) (R0 : root_env) (defs0 : list field_def)
         : infer_result (sctx * root_env * root_set) :=
       match defs0 with
       | [] => infer_ok (Σ0, R0, [])
       | f :: rest =>
           match lookup_field_b (field_name f) fields with
           | None => infer_err (ErrMissingField (field_name f))
           | Some e_field =>
               match infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e_field with
               | infer_err err => infer_err err
               | infer_ok (T_field, Σ1, R1, roots_field) =>
                   let T_expected := instantiate_struct_field_ty lts args f in
                   if ty_compatible_b Ω T_field T_expected
                   then
                     match go Σ1 R1 rest with
                     | infer_err err => infer_err err
                     | infer_ok (Σ2, R2, roots_rest) =>
                         infer_ok (Σ2, R2, root_set_union roots_field roots_rest)
                     end
                   else infer_err (compatible_error T_field T_expected)
               end
           end
       end) Σ R defs =
    infer_env_fields_collect_roots fuel env Ω n lts args R Σ fields defs.
Proof.
  intros fuel env Ω n lts args fields defs.
  induction defs as [|f rest IH]; intros R Σ; simpl; try reflexivity.
  destruct (lookup_field_b (field_name f) fields) as [e_field |]; try reflexivity.
  destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_field)
    as [[[[T_field Σ1] R1] roots_field] | err]; try reflexivity.
  destruct (ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f));
    try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_fields_collect_roots_sound :
  forall fuel env Ω n lts args R Σ fields defs Σ' R' roots,
    infer_env_fields_collect_roots fuel env Ω n lts args R Σ fields defs =
      infer_ok (Σ', R', roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots.
Proof.
  intros fuel env Ω n lts args R Σ fields defs.
  revert R Σ.
  induction defs as [|f rest IH]; intros R Σ Σ' R' roots Hcollect Hexpr.
  - simpl in Hcollect. inversion Hcollect; subst. constructor.
  - simpl in Hcollect.
    destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try discriminate.
    destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_field)
      as [[[[T_field Σ1] R1] roots_field] | err] eqn:Hfield; try discriminate.
    destruct (ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f))
      eqn:Hcompat; try discriminate.
    destruct (infer_env_fields_collect_roots fuel env Ω n lts args R1 Σ1 fields rest)
      as [[[Σ2 R2] roots_rest] | err] eqn:Hrest; try discriminate.
    inversion Hcollect; subst.
    eapply TERFields_Cons.
    + exact Hlookup.
    + eapply Hexpr.
      exact Hfield.
    + exact Hcompat.
    + eapply IH.
      * exact Hrest.
      * intros R0 Σ0 e0 T0 Σ0' R0' roots0 Hinfer.
        eapply Hexpr. exact Hinfer.
Qed.

Theorem infer_core_env_state_fuel_roots_sound :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots.
Proof.
  induction fuel as [|fuel' IH]; intros env Ω n R Σ e T Σ' R' roots Hinfer.
  - simpl in Hinfer. discriminate.
  - destruct e; simpl in Hinfer; try discriminate.
    + inversion Hinfer; subst. constructor.
    + destruct l; inversion Hinfer; subst; constructor.
    + unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
      simpl in Hinfer.
      destruct (sctx_lookup i Σ) as [[Tvar st] |] eqn:Hlookup_s;
        try discriminate.
      destruct (binding_available_b st []) eqn:Havailable; try discriminate.
      destruct (root_env_lookup i R) as [roots0 |] eqn:Hlookup; try discriminate.
      destruct (usage_eqb (ty_usage Tvar) UUnrestricted) eqn:Husage.
      * inversion Hinfer; subst.
        eapply TER_Var_Copy.
        -- apply TPES_Var with (st := st); assumption.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hlookup.
      * destruct (sctx_consume_path Σ i []) as [Σc | err] eqn:Hconsume;
          try discriminate.
        inversion Hinfer; subst.
        eapply TER_Var_Move.
        -- apply TPES_Var with (st := st); assumption.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hconsume.
        -- exact Hlookup.
    + destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1)
        as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
      destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; try discriminate.
      destruct (root_env_lookup i R1) eqn:Hfresh; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n
          (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok env i t Σ2) eqn:Hcheck; simpl in Hinfer; try discriminate.
      destruct (roots_exclude_b i roots2) eqn:Hroots; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i (root_env_remove i R2)) eqn:Henv;
        simpl in Hinfer; try discriminate.
      inversion Hinfer; subst.
      eapply TER_Let.
      * eapply IH. exact He1.
      * exact Hcompat.
      * exact Hfresh.
      * eapply IH. exact He2.
      * exact Hcheck.
      * apply roots_exclude_b_sound. exact Hroots.
      * apply root_env_excludes_b_sound. exact Henv.
    + destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1)
        as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
      destruct (root_env_lookup i R1) eqn:Hfresh; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n
          (root_env_add i roots1 R1) (sctx_add i T1 m Σ1) e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok env i T1 Σ2) eqn:Hcheck; simpl in Hinfer; try discriminate.
      destruct (roots_exclude_b i roots2) eqn:Hroots; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i (root_env_remove i R2)) eqn:Henv;
        simpl in Hinfer; try discriminate.
      inversion Hinfer; subst.
      eapply TER_LetInfer.
      * eapply IH. exact He1.
      * exact Hfresh.
      * eapply IH. exact He2.
      * exact Hcheck.
      * apply roots_exclude_b_sound. exact Hroots.
      * apply root_env_excludes_b_sound. exact Henv.
    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TER_Fn; eassumption.
    + unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
      destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup; try discriminate.
      destruct (usage_eqb (ty_usage Tp) UUnrestricted) eqn:Husage.
      * inversion Hinfer; subst.
        eapply TER_Place_Copy.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hlookup.
      * destruct (sctx_consume_path Σ x path) as [Σc | err] eqn:Hconsume;
          try discriminate.
        inversion Hinfer; subst.
        eapply TER_Place_Move.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hpath.
        -- exact Hconsume.
        -- exact Hlookup.
    + destruct (lookup_struct s env) as [sdef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l) (struct_lifetimes sdef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (struct_type_params sdef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (struct_bounds sdef) l0) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (first_duplicate_field l1) as [dup |] eqn:Hdup; try discriminate.
      destruct (first_unknown_field l1 (struct_fields sdef)) as [unknown |] eqn:Hunknown;
        try discriminate.
      destruct (first_missing_field (struct_fields sdef) l1) as [missing |] eqn:Hmissing;
        try discriminate.
      rewrite infer_env_fields_collect_roots_eq in Hinfer.
      destruct (infer_env_fields_collect_roots fuel' env Ω n l l0 R Σ l1 (struct_fields sdef))
        as [[[Σfields Rfields] roots_fields] | err] eqn:Hfields; try discriminate.
      inversion Hinfer; subst.
      apply negb_false_iff in Hlts. apply Nat.eqb_eq in Hlts.
      apply negb_false_iff in Hargslen. apply Nat.eqb_eq in Hargslen.
      eapply TER_Struct.
      * exact Hlookup.
      * exact Hlts.
      * exact Hargslen.
      * exact Hbounds.
      * eapply infer_env_fields_collect_roots_sound.
        -- exact Hfields.
        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
           eapply IH. exact Hinfer0.
    + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Told | err] eqn:Hplace; try discriminate.
      destruct (root_env_lookup x R) as [roots_result |] eqn:Hroot_result; try discriminate.
      destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
      destruct mut; try discriminate.
      destruct (writable_place_b env Σ p) eqn:Hwrite; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e)
        as [[[[Tnew Σ1] R1] roots_new] | err] eqn:Hnew; try discriminate.
      destruct (root_env_lookup x R1) as [roots_old |] eqn:Hroot_old; try discriminate.
      destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
      destruct (sctx_path_available Σ1 x path) as [[] | err] eqn:Havailable; try discriminate.
      destruct (sctx_restore_path Σ1 x path) as [Σ2 | err] eqn:Hrestore; try discriminate.
      inversion Hinfer; subst.
      eapply TER_Replace_Path.
      * eapply infer_place_sctx_structural_sound. exact Hplace.
      * exact Hpath.
      * apply writable_place_b_sound. exact Hwrite.
      * exact Hroot_result.
      * eapply IH. exact Hnew.
      * exact Hroot_old.
      * exact Hcompat.
      * exact Havailable.
      * exact Hrestore.
    + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Told | err] eqn:Hplace; try discriminate.
      destruct (usage_eqb (ty_usage Told) ULinear) eqn:Hlinear; try discriminate.
      destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
      destruct mut; try discriminate.
      destruct (writable_place_b env Σ p) eqn:Hwrite; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e)
        as [[[[Tnew Σ1] R1] roots_new] | err] eqn:Hnew; try discriminate.
      destruct (root_env_lookup x R1) as [roots_old |] eqn:Hroot_old; try discriminate.
      destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
      destruct (sctx_path_available Σ1 x path) as [[] | err] eqn:Havailable; try discriminate.
      inversion Hinfer; subst.
      eapply TER_Assign_Path.
      * eapply infer_place_sctx_structural_sound. exact Hplace.
      * intro Hu. rewrite Hu in Hlinear. simpl in Hlinear. discriminate.
      * exact Hpath.
      * apply writable_place_b_sound. exact Hwrite.
      * eapply IH. exact Hnew.
      * exact Hroot_old.
      * exact Hcompat.
      * exact Havailable.
    + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct r.
      * inversion Hinfer; subst.
        replace [x] with (root_of_place p).
        -- eapply TER_BorrowShared.
           eapply infer_place_sctx_structural_sound. exact Hplace.
        -- eapply root_of_place_direct. exact Hpath.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        inversion Hinfer; subst.
        eapply TER_BorrowUnique.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- exact Hpath.
        -- exact Hmut.
    + destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e)
        as [[[[Te Σe] Re] roots_e] | err] eqn:He; try discriminate.
      inversion Hinfer; subst.
      eapply TER_Drop. eapply IH. exact He.
    + destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e1)
        as [[[[Tcond Σ1] R1] roots_cond] | err1] eqn:He1; try discriminate.
      destruct (ty_core_eqb (ty_core Tcond) TBooleans) eqn:Hbool; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n R1 Σ1 e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n R1 Σ1 e3)
        as [[[[T3 Σ3] R3] roots3] | err3] eqn:He3; try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3)) eqn:Hcore; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |] eqn:Hmerge;
        try discriminate.
      inversion Hinfer; subst.
      eapply TER_If.
      * eapply IH. exact He1.
      * apply ty_core_eqb_true. exact Hbool.
      * eapply IH. exact He2.
      * eapply IH. exact He3.
      * apply ty_core_eqb_true. exact Hcore.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Theorem infer_core_env_roots_sound :
  forall env Ω n R Γ e T Γ' R' roots,
    infer_core_env_roots env Ω n R Γ e = infer_ok (T, Γ', R', roots) ->
    typed_env_roots env Ω n R (sctx_of_ctx Γ) e T (sctx_of_ctx Γ') R' roots.
Proof.
  unfold infer_core_env_roots, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n R Γ e T Γ' R' roots Hinfer.
  destruct (infer_core_env_state_fuel_roots 10000 env Ω n R Γ e)
    as [[[[T0 Σ] R0] roots0] | err] eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_roots_sound. exact Hcore.
Qed.

Definition typed_fn_env_roots (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Γ_out,
    typed_env_roots env (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (params_ctx (fn_params f)))
      (fn_body f) T_body (sctx_of_ctx Γ_out) R_out roots /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Γ_out = true.

Definition checked_fn_env_roots (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  typed_fn_env_roots env f R0 R_out roots /\
  exists PBS',
    borrow_ok_env_structural env [] (params_ctx (fn_params f)) (fn_body f) PBS'.

Lemma typed_fn_env_roots_structural :
  forall env f R0 R_out roots,
    typed_fn_env_roots env f R0 R_out roots ->
    typed_fn_env_structural env f.
Proof.
  unfold typed_fn_env_roots, typed_fn_env_structural.
  intros env f R0 R_out roots Htyped.
  destruct Htyped as [T_body [Γ_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Γ_out.
  repeat split.
  - eapply typed_env_roots_structural. exact Htyped.
  - exact Hcompat.
  - exact Hparams.
Qed.

Lemma checked_fn_env_roots_structural :
  forall env f R0 R_out roots,
    checked_fn_env_roots env f R0 R_out roots ->
    checked_fn_env_structural env f.
Proof.
  unfold checked_fn_env_roots, checked_fn_env_structural.
  intros env f R0 R_out roots [Htyped Hborrow].
  split.
  - eapply typed_fn_env_roots_structural. exact Htyped.
  - exact Hborrow.
Qed.

Theorem infer_env_roots_sound :
  forall env f R0 T Γ_out R_out roots,
    infer_env_roots env f R0 = infer_ok (T, Γ_out, R_out, roots) ->
    typed_fn_env_roots env f R0 R_out roots.
Proof.
  unfold infer_env_roots, typed_fn_env_roots.
  intros env f R0 T Γ_out R_out roots Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (infer_core_env_roots env (fn_outlives f) (fn_lifetimes f)
      R0 (params_ctx (fn_params f)) (fn_body f))
    as [[[[T_body Γ_body] R_body] roots_body] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompat; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_body) eqn:Hparams; try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ_out.
  repeat split.
  - eapply infer_core_env_roots_sound. exact Hcore.
  - exact Hcompat.
  - exact Hparams.
Qed.

Theorem infer_full_env_roots_sound :
  forall env f R0 T Γ_out R_out roots,
    infer_full_env_roots env f R0 = infer_ok (T, Γ_out, R_out, roots) ->
    checked_fn_env_roots env f R0 R_out roots.
Proof.
  unfold infer_full_env_roots, checked_fn_env_roots.
  intros env f R0 T Γ_out R_out roots Hfull.
  destruct (infer_env_roots env f R0)
    as [[[[T0 Γ0] R1] roots1] | err] eqn:Hinfer; try discriminate.
  destruct (borrow_check_env env [] (params_ctx (fn_params f)) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  inversion Hfull; subst.
  split.
  - eapply infer_env_roots_sound. exact Hinfer.
  - exists PBS'. eapply borrow_check_env_structural_sound. exact Hborrow.
Qed.
