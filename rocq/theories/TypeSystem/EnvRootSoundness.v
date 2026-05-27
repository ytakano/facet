From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules
  RootProvenance TypeChecker EnvStructuralRules CheckerSoundness
  EnvTypingSoundness EnvBorrowSoundness AlphaRenaming.
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
  apply root_atom_eqb_eq in Hxy.
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

Lemma root_env_eqb_true_equiv :
  forall R1 R2,
    root_env_eqb R1 R2 = true ->
    root_env_equiv R1 R2.
Proof.
  intros R1 R2 Heq.
  apply root_env_eqb_true in Heq. subst R2.
  apply root_env_equiv_refl.
Qed.

Lemma roots_exclude_b_sound :
  forall x roots,
    roots_exclude_b x roots = true ->
    roots_exclude x roots.
Proof.
  unfold roots_exclude_b, roots_exclude.
  intros x roots Hnot Hin.
  apply negb_true_iff in Hnot.
  assert (existsb (root_atom_eqb (RStore x)) roots = true) as Hexists.
  { apply existsb_exists.
    exists (RStore x). split.
    - exact Hin.
    - apply root_atom_eqb_refl. }
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

Lemma roots_exclude_params_b_sound_local :
  forall ps roots,
    roots_exclude_params_b ps roots = true ->
    roots_exclude_params ps roots.
Proof.
  induction ps as [|p ps IH]; intros roots Hexcl; simpl in *.
  - constructor.
  - apply andb_true_iff in Hexcl as [Hhead Htail].
    constructor.
    + apply roots_exclude_b_sound. exact Hhead.
    + apply IH. exact Htail.
Qed.

Lemma root_env_excludes_params_b_sound_local :
  forall ps R,
    root_env_excludes_params_b ps R = true ->
    root_env_excludes_params ps R.
Proof.
  induction ps as [|p ps IH]; intros R Hexcl; simpl in *.
  - constructor.
  - apply andb_true_iff in Hexcl as [Hhead Htail].
    constructor.
    + apply root_env_excludes_b_sound. exact Hhead.
    + apply IH. exact Htail.
Qed.

Lemma root_of_place_direct :
  forall p x path,
    place_path p = Some (x, path) ->
    root_of_place p = [RStore x].
Proof.
  intros p x path Hpath.
  unfold root_of_place.
  rewrite Hpath.
  reflexivity.
Qed.

Fixpoint infer_env_args_collect_roots fuel env Ω n
    (R : root_env) (Σ : sctx) (args : list expr)
    : infer_result (list Ty * sctx * root_env * list root_set) :=
  match args with
  | [] => infer_ok ([], Σ, R, [])
  | e :: rest =>
      match infer_core_env_state_fuel_roots fuel env Ω n R Σ e with
      | infer_err err => infer_err err
      | infer_ok (T_e, Σ1, R1, roots_e) =>
          match infer_env_args_collect_roots fuel env Ω n R1 Σ1 rest with
          | infer_err err => infer_err err
          | infer_ok (tys, Σ2, R2, roots_rest) =>
              infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_rest)
          end
      end
  end.

Lemma infer_env_args_collect_roots_eq :
  forall fuel env Ω n args R Σ,
    (fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
         : infer_result (list Ty * sctx * root_env * list root_set) :=
       match as_ with
       | [] => infer_ok ([], Σ0, R0, [])
       | e' :: es =>
           match infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e' with
           | infer_err err => infer_err err
           | infer_ok (T_e, Σ1, R1, roots_e) =>
               match collect Σ1 R1 es with
               | infer_err err => infer_err err
               | infer_ok (tys, Σ2, R2, roots_es) =>
                   infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
               end
           end
       end) Σ R args =
    infer_env_args_collect_roots fuel env Ω n R Σ args.
Proof.
  intros fuel env Ω n args.
  induction args as [|e rest IH]; intros R Σ; simpl.
  - reflexivity.
  - destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He;
      try reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma infer_env_args_collect_roots_sound :
  forall fuel env Ω n R Σ args arg_tys params Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    check_args Ω arg_tys params = None ->
    typed_args_roots env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n R Σ args.
  revert R Σ.
  induction args as [|e rest IH]; intros R Σ arg_tys params Σ' R' arg_roots
      Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; try discriminate.
    constructor.
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He; try discriminate.
    destruct (infer_env_args_collect_roots fuel env Ω n R1 Σ1 rest)
      as [[[[tys Σ2] R2] roots_rest] | err] eqn:Htail; try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_b Ω T_e (param_ty p)) eqn:Hcompat; try discriminate.
    eapply TERArgs_Cons.
    + eapply Hexpr. exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * exact Hexpr.
      * exact Hcheck.
Qed.

Fixpoint infer_env_enum_payloads_collect_roots fuel env Ω n lts args
    (R : root_env) (Σ : sctx) (fields : list Ty) (payloads : list expr)
    : infer_result (sctx * root_env * root_set) :=
  match fields, payloads with
  | [], [] => infer_ok (Σ, R, [])
  | T_field :: fields', e_payload :: payloads' =>
      match infer_core_env_state_fuel_roots fuel env Ω n R Σ e_payload with
      | infer_err err => infer_err err
      | infer_ok (T_payload, Σ1, R1, roots_payload) =>
          let T_expected := instantiate_enum_variant_field_ty lts args T_field in
          if ty_compatible_b Ω T_payload T_expected
          then
            match infer_env_enum_payloads_collect_roots fuel env Ω n lts args
                    R1 Σ1 fields' payloads' with
            | infer_err err => infer_err err
            | infer_ok (Σ2, R2, roots_rest) =>
                infer_ok (Σ2, R2, root_set_union roots_payload roots_rest)
            end
          else infer_err (compatible_error T_payload T_expected)
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Lemma infer_env_enum_payloads_collect_roots_eq :
  forall fuel env Ω n lts args fields payloads R Σ,
    (fix go (Σ0 : sctx) (R0 : root_env)
        (fields0 : list Ty) (es : list expr)
        : infer_result (sctx * root_env * root_set) :=
       match fields0, es with
       | [], [] => infer_ok (Σ0, R0, [])
       | T_field :: fields', e_payload :: es' =>
           match infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e_payload with
           | infer_err err => infer_err err
           | infer_ok (T_payload, Σ1, R1, roots_payload) =>
               let T_expected :=
                 instantiate_enum_variant_field_ty lts args T_field in
               if ty_compatible_b Ω T_payload T_expected
               then
                 match go Σ1 R1 fields' es' with
                 | infer_err err => infer_err err
                 | infer_ok (Σ2, R2, roots_rest) =>
                     infer_ok (Σ2, R2, root_set_union roots_payload roots_rest)
                 end
               else infer_err (compatible_error T_payload T_expected)
           end
       | _, _ => infer_err ErrArityMismatch
       end) Σ R fields payloads =
    infer_env_enum_payloads_collect_roots fuel env Ω n lts args R Σ fields payloads.
Proof.
  intros fuel env Ω n lts args fields.
  induction fields as [|T_field rest IH]; intros payloads R Σ;
    destruct payloads as [|e_payload payloads']; simpl; try reflexivity.
  destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_payload)
    as [[[[T_payload Σ1] R1] roots_payload] | err] eqn:Hpayload;
    try reflexivity.
  destruct (ty_compatible_b Ω T_payload
    (instantiate_enum_variant_field_ty lts args T_field)); try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_enum_payloads_collect_roots_sound :
  forall fuel env Ω n lts args R Σ fields payloads Σ' R' roots,
    infer_env_enum_payloads_collect_roots fuel env Ω n lts args R Σ fields payloads =
      infer_ok (Σ', R', roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    exists payload_roots,
      typed_args_roots env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args) fields))
        Σ' R' payload_roots /\
      roots = root_sets_union payload_roots.
Proof.
  intros fuel env Ω n lts args R Σ fields.
  revert R Σ.
  induction fields as [|T_field rest IH]; intros R Σ payloads Σ' R' roots Hcollect Hexpr;
    destruct payloads as [|e_payload payloads']; simpl in Hcollect; try discriminate.
  - inversion Hcollect; subst. exists []. split; [constructor | reflexivity].
  - destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_payload)
      as [[[[T_payload Σ1] R1] roots_payload] | err] eqn:Hp; try discriminate.
    destruct (ty_compatible_b Ω T_payload
      (instantiate_enum_variant_field_ty lts args T_field)) eqn:Hcompat;
      try discriminate.
    destruct (infer_env_enum_payloads_collect_roots fuel env Ω n lts args
      R1 Σ1 rest payloads') as [[[Σ2 R2] roots_rest] | err] eqn:Hrest;
      try discriminate.
    inversion Hcollect; subst.
    destruct (IH R1 Σ1 payloads' Σ' R' roots_rest Hrest Hexpr)
      as [payload_roots [Hpayload_roots Hroots_rest]].
    exists (roots_payload :: payload_roots). split.
    + eapply TERArgs_Cons.
      * eapply Hexpr. exact Hp.
      * exact Hcompat.
      * exact Hpayload_roots.
    + simpl. rewrite Hroots_rest. reflexivity.
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

Fixpoint infer_env_args_collect_roots_shadow_safe fuel env Ω n
    (R : root_env) (Σ : sctx) (args : list expr)
    : infer_result (list Ty * sctx * root_env * list root_set) :=
  match args with
  | [] => infer_ok ([], Σ, R, [])
  | e :: rest =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e with
      | infer_err err => infer_err err
      | infer_ok (T_e, Σ1, R1, roots_e) =>
          match infer_env_args_collect_roots_shadow_safe
                  fuel env Ω n R1 Σ1 rest with
          | infer_err err => infer_err err
          | infer_ok (tys, Σ2, R2, roots_rest) =>
              infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_rest)
          end
      end
  end.

Lemma infer_env_args_collect_roots_shadow_safe_eq :
  forall fuel env Ω n args R Σ,
    (fix collect (Σ0 : sctx) (R0 : root_env) (as_ : list expr)
         : infer_result (list Ty * sctx * root_env * list root_set) :=
       match as_ with
       | [] => infer_ok ([], Σ0, R0, [])
       | e' :: es =>
           match infer_core_env_state_fuel_roots_shadow_safe
                   fuel env Ω n R0 Σ0 e' with
           | infer_err err => infer_err err
           | infer_ok (T_e, Σ1, R1, roots_e) =>
               match collect Σ1 R1 es with
               | infer_err err => infer_err err
               | infer_ok (tys, Σ2, R2, roots_es) =>
                   infer_ok (T_e :: tys, Σ2, R2, roots_e :: roots_es)
               end
           end
       end) Σ R args =
    infer_env_args_collect_roots_shadow_safe fuel env Ω n R Σ args.
Proof.
  intros fuel env Ω n args.
  induction args as [|e rest IH]; intros R Σ; simpl.
  - reflexivity.
  - destruct (infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He;
      try reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma infer_env_args_collect_roots_shadow_safe_sound :
  forall fuel env Ω n R Σ args arg_tys params Σ' R' arg_roots,
    infer_env_args_collect_roots_shadow_safe fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots_shadow_safe env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    check_args Ω arg_tys params = None ->
    typed_args_roots_shadow_safe env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n R Σ args.
  revert R Σ.
  induction args as [|e rest IH]; intros R Σ arg_tys params Σ' R' arg_roots
      Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; try discriminate.
    constructor.
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He; try discriminate.
    destruct (infer_env_args_collect_roots_shadow_safe fuel env Ω n R1 Σ1 rest)
      as [[[[tys Σ2] R2] roots_rest] | err] eqn:Htail; try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_b Ω T_e (param_ty p)) eqn:Hcompat; try discriminate.
    eapply TERSArgs_Cons.
    + eapply Hexpr. exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * exact Hexpr.
      * exact Hcheck.
Qed.

Fixpoint infer_env_enum_payloads_collect_roots_shadow_safe fuel env Ω n lts args
    (R : root_env) (Σ : sctx) (fields : list Ty) (payloads : list expr)
    : infer_result (sctx * root_env * root_set) :=
  match fields, payloads with
  | [], [] => infer_ok (Σ, R, [])
  | T_field :: fields', e_payload :: payloads' =>
      match infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e_payload with
      | infer_err err => infer_err err
      | infer_ok (T_payload, Σ1, R1, roots_payload) =>
          let T_expected := instantiate_enum_variant_field_ty lts args T_field in
          if ty_compatible_b Ω T_payload T_expected
          then
            match infer_env_enum_payloads_collect_roots_shadow_safe
                    fuel env Ω n lts args R1 Σ1 fields' payloads' with
            | infer_err err => infer_err err
            | infer_ok (Σ2, R2, roots_rest) =>
                infer_ok (Σ2, R2, root_set_union roots_payload roots_rest)
            end
          else infer_err (compatible_error T_payload T_expected)
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Lemma infer_env_enum_payloads_collect_roots_shadow_safe_eq :
  forall fuel env Ω n lts args fields payloads R Σ,
    (fix go (Σ0 : sctx) (R0 : root_env)
        (fields0 : list Ty) (es : list expr)
        : infer_result (sctx * root_env * root_set) :=
       match fields0, es with
       | [], [] => infer_ok (Σ0, R0, [])
       | T_field :: fields', e_payload :: es' =>
           match infer_core_env_state_fuel_roots_shadow_safe
                   fuel env Ω n R0 Σ0 e_payload with
           | infer_err err => infer_err err
           | infer_ok (T_payload, Σ1, R1, roots_payload) =>
               let T_expected :=
                 instantiate_enum_variant_field_ty lts args T_field in
               if ty_compatible_b Ω T_payload T_expected
               then
                 match go Σ1 R1 fields' es' with
                 | infer_err err => infer_err err
                 | infer_ok (Σ2, R2, roots_rest) =>
                     infer_ok (Σ2, R2, root_set_union roots_payload roots_rest)
                 end
               else infer_err (compatible_error T_payload T_expected)
           end
       | _, _ => infer_err ErrArityMismatch
       end) Σ R fields payloads =
    infer_env_enum_payloads_collect_roots_shadow_safe
      fuel env Ω n lts args R Σ fields payloads.
Proof.
  intros fuel env Ω n lts args fields.
  induction fields as [|T_field rest IH]; intros payloads R Σ;
    destruct payloads as [|e_payload payloads']; simpl; try reflexivity.
  destruct (infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e_payload)
    as [[[[T_payload Σ1] R1] roots_payload] | err] eqn:Hpayload;
    try reflexivity.
  destruct (ty_compatible_b Ω T_payload
    (instantiate_enum_variant_field_ty lts args T_field)); try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_enum_payloads_collect_roots_shadow_safe_sound :
  forall fuel env Ω n lts args R Σ fields payloads Σ' R' roots,
    infer_env_enum_payloads_collect_roots_shadow_safe
      fuel env Ω n lts args R Σ fields payloads =
      infer_ok (Σ', R', roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots_shadow_safe env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    exists payload_roots,
      typed_args_roots_shadow_safe env Ω n R Σ payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts args) fields))
        Σ' R' payload_roots /\
      roots = root_sets_union payload_roots.
Proof.
  intros fuel env Ω n lts args R Σ fields.
  revert R Σ.
  induction fields as [|T_field rest IH]; intros R Σ payloads Σ' R' roots Hcollect Hexpr;
    destruct payloads as [|e_payload payloads']; simpl in Hcollect; try discriminate.
  - inversion Hcollect; subst. exists []. split; [constructor | reflexivity].
  - destruct (infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e_payload)
      as [[[[T_payload Σ1] R1] roots_payload] | err] eqn:Hp; try discriminate.
    destruct (ty_compatible_b Ω T_payload
      (instantiate_enum_variant_field_ty lts args T_field)) eqn:Hcompat;
      try discriminate.
    destruct (infer_env_enum_payloads_collect_roots_shadow_safe fuel env Ω n lts args
      R1 Σ1 rest payloads') as [[[Σ2 R2] roots_rest] | err] eqn:Hrest;
      try discriminate.
    inversion Hcollect; subst.
    destruct (IH R1 Σ1 payloads' Σ' R' roots_rest Hrest Hexpr)
      as [payload_roots [Hpayload_roots Hroots_rest]].
    exists (roots_payload :: payload_roots). split.
    + eapply TERSArgs_Cons.
      * eapply Hexpr. exact Hp.
      * exact Hcompat.
      * exact Hpayload_roots.
    + simpl. rewrite Hroots_rest. reflexivity.
Qed.

Fixpoint infer_env_fields_collect_roots_shadow_safe fuel env Ω n lts args
    (R : root_env) (Σ : sctx) (fields : list (string * expr))
    (defs : list field_def)
    : infer_result (sctx * root_env * root_set) :=
  match defs with
  | [] => infer_ok (Σ, R, [])
  | f :: rest =>
      match lookup_field_b (field_name f) fields with
      | None => infer_err (ErrMissingField (field_name f))
      | Some e_field =>
          match infer_core_env_state_fuel_roots_shadow_safe
                  fuel env Ω n R Σ e_field with
          | infer_err err => infer_err err
          | infer_ok (T_field, Σ1, R1, roots_field) =>
              let T_expected := instantiate_struct_field_ty lts args f in
              if ty_compatible_b Ω T_field T_expected
              then
                match infer_env_fields_collect_roots_shadow_safe
                        fuel env Ω n lts args R1 Σ1 fields rest with
                | infer_err err => infer_err err
                | infer_ok (Σ2, R2, roots_rest) =>
                    infer_ok (Σ2, R2, root_set_union roots_field roots_rest)
                end
              else infer_err (compatible_error T_field T_expected)
          end
      end
  end.

Lemma infer_env_fields_collect_roots_shadow_safe_eq :
  forall fuel env Ω n lts args fields defs R Σ,
    (fix go (Σ0 : sctx) (R0 : root_env) (defs0 : list field_def)
         : infer_result (sctx * root_env * root_set) :=
       match defs0 with
       | [] => infer_ok (Σ0, R0, [])
       | f :: rest =>
           match lookup_field_b (field_name f) fields with
           | None => infer_err (ErrMissingField (field_name f))
           | Some e_field =>
               match infer_core_env_state_fuel_roots_shadow_safe
                       fuel env Ω n R0 Σ0 e_field with
               | infer_err err => infer_err err
               | infer_ok (T_field, Σ1, R1, roots_field) =>
                   let T_expected := instantiate_struct_field_ty lts args f in
                   if ty_compatible_b Ω T_field T_expected
                   then
                     match go Σ1 R1 rest with
                     | infer_err err => infer_err err
                     | infer_ok (Σ2, R2, roots_rest) =>
                         infer_ok (Σ2, R2,
                           root_set_union roots_field roots_rest)
                     end
                   else infer_err (compatible_error T_field T_expected)
               end
           end
       end) Σ R defs =
    infer_env_fields_collect_roots_shadow_safe
      fuel env Ω n lts args R Σ fields defs.
Proof.
  intros fuel env Ω n lts args fields defs.
  induction defs as [|f rest IH]; intros R Σ; simpl; try reflexivity.
  destruct (lookup_field_b (field_name f) fields) as [e_field |];
    try reflexivity.
  destruct (infer_core_env_state_fuel_roots_shadow_safe
              fuel env Ω n R Σ e_field)
    as [[[[T_field Σ1] R1] roots_field] | err]; try reflexivity.
  destruct (ty_compatible_b Ω T_field
              (instantiate_struct_field_ty lts args f));
    try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_fields_collect_roots_shadow_safe_sound :
  forall fuel env Ω n lts args R Σ fields defs Σ' R' roots,
    infer_env_fields_collect_roots_shadow_safe
      fuel env Ω n lts args R Σ fields defs =
      infer_ok (Σ', R', roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots_shadow_safe env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots.
Proof.
  intros fuel env Ω n lts args R Σ fields defs.
  revert R Σ.
  induction defs as [|f rest IH]; intros R Σ Σ' R' roots Hcollect Hexpr.
  - simpl in Hcollect. inversion Hcollect; subst. constructor.
  - simpl in Hcollect.
    destruct (lookup_field_b (field_name f) fields) as [e_field |]
      eqn:Hlookup; try discriminate.
    destruct (infer_core_env_state_fuel_roots_shadow_safe
                fuel env Ω n R Σ e_field)
      as [[[[T_field Σ1] R1] roots_field] | err] eqn:Hfield;
      try discriminate.
    destruct (ty_compatible_b Ω T_field
                (instantiate_struct_field_ty lts args f))
      eqn:Hcompat; try discriminate.
    destruct (infer_env_fields_collect_roots_shadow_safe
                fuel env Ω n lts args R1 Σ1 fields rest)
      as [[[Σ2 R2] roots_rest] | err] eqn:Hrest; try discriminate.
    inversion Hcollect; subst.
    eapply TERSFields_Cons.
    + exact Hlookup.
    + eapply Hexpr. exact Hfield.
    + exact Hcompat.
    + eapply IH.
      * exact Hrest.
      * intros R0 Σ0 e0 T0 Σ1' R1' roots1 Hinfer0.
        eapply Hexpr. exact Hinfer0.
Qed.

Theorem infer_core_env_state_fuel_roots_sound :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots.
Proof.
  induction fuel as [|fuel' IH]; intros env Ω n R Σ e T Σ' R' roots Hinfer.
  - simpl in Hinfer. discriminate.
		  - destruct e as [|l|i|m i t e1 e2|m i e1 e2|i|i l|p|i l|i l l0|e l|
		        s l l0 l1|s s0 l l0 l1|e l|p e|p e|r p|e|e|e1 e2 e3];
      simpl in Hinfer; try discriminate.
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
			      unfold no_captures_b in Hinfer.
				      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
			      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TER_Fn; eassumption.
			    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
			      destruct (check_make_closure_captures_sctx_with_env env Ω Σ l (fn_captures fdef))
			        as [[env_lt captured_tys] | err] eqn:Hcheck; try discriminate.
		      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TER_MakeClosure; eassumption.
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
	    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
	      unfold no_captures_b in Hinfer.
	      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
	      destruct (Nat.eqb (fn_type_params fdef) 0) eqn:Htypeparams; try discriminate.
	      rewrite infer_env_args_collect_roots_eq in Hinfer.
      destruct (infer_env_args_collect_roots fuel' env Ω n R Σ l)
        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
        try discriminate.
      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
          arg_tys (fn_params fdef)) as [σ_acc |] eqn:Hbuild; try discriminate.
	      destruct (check_args Ω arg_tys
	          (apply_lt_params (finalize_subst σ_acc) (fn_params fdef)))
	        as [err |] eqn:Hcheck; try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
        try discriminate.
      destruct (outlives_constraints_hold_b Ω
          (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)))
        eqn:Hout; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TER_Call with (fdef := fdef) (σ := finalize_subst σ_acc).
	      * exact Hin.
	      * exact Hname.
	      * exact Hcaps.
	      * apply Nat.eqb_eq. exact Htypeparams.
	      * eapply infer_env_args_collect_roots_sound.
	        -- exact Hcollect.
		        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
		           eapply IH. exact Hinfer0.
		        -- exact Hcheck.
		      * apply outlives_constraints_hold_b_sound. exact Hout.
			    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
	      unfold no_captures_b in Hinfer.
	      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
	      destruct (Nat.eqb (Datatypes.length l) (fn_type_params fdef)) eqn:Htypeparams;
	        try discriminate.
	      destruct (check_struct_bounds env (fn_bounds fdef) l) eqn:Hbounds; try discriminate.
	      rewrite infer_env_args_collect_roots_eq in Hinfer.
	      destruct (infer_env_args_collect_roots fuel' env Ω n R Σ l0)
	        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
	        try discriminate.
	      remember (apply_type_params l (fn_params fdef)) as ps_typed.
	      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
	          arg_tys ps_typed) as [σ_acc |] eqn:Hbuild; try discriminate.
	      destruct (check_args Ω arg_tys
	          (apply_lt_params (finalize_subst σ_acc) ps_typed))
	        as [err |] eqn:Hcheck; try discriminate.
	      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
	        try discriminate.
	      destruct (outlives_constraints_hold_b Ω
	          (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)))
	        eqn:Hout; try discriminate.
	      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TER_CallGeneric with (fdef := fdef) (σ := finalize_subst σ_acc).
	      * exact Hin.
	      * exact Hname.
	      * exact Hcaps.
	      * apply Nat.eqb_eq. exact Htypeparams.
	      * exact Hbounds.
	      * eapply infer_env_args_collect_roots_sound.
	        -- exact Hcollect.
	        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
	           eapply IH. exact Hinfer0.
	        -- exact Hcheck.
	      * apply outlives_constraints_hold_b_sound. exact Hout.
	    + destruct e; try discriminate.
      destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup;
        try discriminate.
      destruct (check_make_closure_captures_sctx_with_env env Ω Σ l0
        (fn_captures fdef)) as [[env_lt captured_tys] | err] eqn:Hcaptures;
        try discriminate.
      rewrite infer_env_args_collect_roots_eq in Hinfer.
      destruct (infer_env_args_collect_roots fuel' env Ω n R Σ l)
        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
        try discriminate.
      destruct (build_sigma (fn_lifetimes fdef)
        (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
        as [σ_acc |] eqn:Hbuild; try discriminate.
      remember (finalize_subst σ_acc) as σ.
      remember (apply_lt_params σ (fn_params fdef)) as ps_subst.
      destruct (check_args Ω arg_tys ps_subst) as [err |] eqn:Hcheck;
        try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) σ) eqn:Hwf;
        try discriminate.
      destruct (outlives_constraints_hold_b Ω
        (apply_lt_outlives σ (fn_outlives fdef))) eqn:Hout;
        try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TER_CallExpr_MakeClosure with (σ := finalize_subst σ_acc).
      * exact Hin.
      * exact Hname.
      * exact Hcaptures.
      * eapply infer_env_args_collect_roots_sound.
        -- exact Hcollect.
        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
           eapply IH. exact Hinfer0.
        -- exact Hcheck.
      * apply outlives_constraints_hold_b_sound. exact Hout.
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
    + destruct (lookup_enum s env) as [edef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l) (enum_lifetimes edef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (enum_type_params edef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (enum_bounds edef) l0) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (lookup_enum_variant s0 (enum_variants edef)) as [vdef |] eqn:Hvariant;
        try discriminate.
      rewrite infer_env_enum_payloads_collect_roots_eq in Hinfer.
      destruct (infer_env_enum_payloads_collect_roots fuel' env Ω n l l0 R Σ
        (enum_variant_fields vdef) l1) as [[[Σpayloads Rpayloads] roots_payloads] | err]
        eqn:Hpayloads; try discriminate.
      inversion Hinfer; subst.
      apply negb_false_iff in Hlts. apply Nat.eqb_eq in Hlts.
      apply negb_false_iff in Hargslen. apply Nat.eqb_eq in Hargslen.
      destruct (infer_env_enum_payloads_collect_roots_sound fuel' env Ω n l l0
        R Σ (enum_variant_fields vdef) l1 Σ' R' roots
        Hpayloads) as [payload_roots [Hpayload_roots Hroots]].
      { intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
        eapply IH. exact Hinfer0. }
      subst roots.
      eapply TER_Enum.
      * exact Hlookup.
      * exact Hvariant.
      * exact Hlts.
      * exact Hargslen.
      * exact Hbounds.
      * exact Hpayload_roots.
    + destruct (infer_core_env_state_fuel_roots fuel' env Ω n R Σ e)
        as [[[[T_scrut Σ1] R1] roots_scrut] | err_scrut] eqn:Hscrut;
        try discriminate.
      destruct (ty_core T_scrut) eqn:Hscrut_core; try discriminate.
      destruct (lookup_enum s env) as [edef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (enum_lifetimes edef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l1) (enum_type_params edef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (enum_bounds edef) l1) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (first_duplicate_branch l) as [dup |] eqn:Hdup; try discriminate.
      destruct (first_unknown_variant_branch l (enum_variants edef)) as [unknown |]
        eqn:Hunknown; try discriminate.
      destruct (first_missing_variant_branch (enum_variants edef) l) as [missing |]
        eqn:Hmissing; try discriminate.
      destruct (enum_variants edef) as [|v_head v_tail] eqn:Hvariants;
        try discriminate.
      simpl in Hinfer.
      destruct (lookup_expr_branch_binders (enum_variant_name v_head) l)
        as [binders_head |] eqn:Hbinders_head; try discriminate.
      destruct (lookup_branch_b (enum_variant_name v_head) l) as [e_head |]
        eqn:Hlookup_branch; try discriminate.
      destruct (match_payload_params binders_head l0 l1 v_head)
        as [ps_head | err_params_head] eqn:Hparams_head; try discriminate.
      destruct (params_names_nodup_b ps_head &&
          ctx_lookup_params_none_b ps_head Σ1 &&
          root_env_lookup_params_none_b ps_head R1) eqn:Hnodup_head;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots fuel' env Ω n
          (root_env_add_params_roots_same ps_head roots_scrut R1)
          (sctx_add_params ps_head Σ1) e_head)
        as [[[[T_head Σ_head_payload] R_head_payload] roots_head] | err_head] eqn:Hhead;
        try discriminate.
      destruct (params_ok_sctx_b env ps_head Σ_head_payload &&
          roots_exclude_params_b ps_head roots_head &&
          root_env_excludes_params_b ps_head
            (root_env_remove_match_params ps_head R_head_payload)) eqn:Hcleanup_head;
        try discriminate.
      remember
        ((fix infer_rest (T_head0 : Ty) (R_out0 : root_env)
            (defs0 : list enum_variant_def) {struct defs0}
            : infer_result (list sctx * list Ty * list root_set) :=
            match defs0 with
            | [] => infer_ok ([], [], [])
            | v0 :: rest0 =>
                match
                  match lookup_expr_branch_binders (enum_variant_name v0) l with
                  | Some binders =>
                      match lookup_branch_b (enum_variant_name v0) l with
                      | Some e_branch =>
                          match match_payload_params binders l0 l1 v0 with
                          | infer_ok ps =>
                              if params_names_nodup_b ps &&
                                 ctx_lookup_params_none_b ps Σ1 &&
                                 root_env_lookup_params_none_b ps R1
                              then
                                match infer_core_env_state_fuel_roots fuel' env Ω n
                                        (root_env_add_params_roots_same ps roots_scrut R1)
                                        (sctx_add_params ps Σ1) e_branch with
                                | infer_ok (T_branch, Σ_branch_payload,
                                            R_branch_payload, roots_branch) =>
                                    if params_ok_sctx_b env ps Σ_branch_payload &&
                                       roots_exclude_params_b ps roots_branch &&
                                       root_env_excludes_params_b ps
                                         (root_env_remove_match_params ps R_branch_payload)
                                    then infer_ok
                                      (T_branch,
                                       sctx_remove_params ps Σ_branch_payload,
                                       root_env_remove_match_params ps R_branch_payload,
                                       roots_branch)
                                    else infer_err ErrContextCheckFailed
                                | infer_err err => infer_err err
                                end
                              else infer_err ErrContextCheckFailed
                          | infer_err err => infer_err err
                          end
                      | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                      end
                  | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                  end
                with
                | infer_ok (T0, Σ0, R0, roots0) =>
                    if ty_core_eqb (ty_core T0) (ty_core T_head0)
                    then
                      infer_if_bool (root_env_eqb R0 R_out0)
                        match infer_rest T_head0 R_out0 rest0 with
                        | infer_err err => infer_err err
                        | infer_ok (Σs, Ts, rootss) =>
                            infer_ok (Σ0 :: Σs, T0 :: Ts, roots0 :: rootss)
                        end
                        (infer_err ErrContextCheckFailed)
                    else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head0))
                | infer_err err => infer_err err
                end
            end) T_head (root_env_remove_match_params ps_head R_head_payload) v_tail) as tail_result eqn:Htail.
      destruct tail_result as [[[Σ_tail Ts_tail] roots_tail] | err_tail];
        try discriminate.
      symmetry in Htail.
      assert (Htail_typed :
        typed_match_tail_roots env Ω n l0 l1 R1 roots_scrut Σ1 l v_tail
          (ty_core T_head) (root_env_remove_match_params ps_head R_head_payload)
          Σ_tail Ts_tail roots_tail).
      {
        clear Hinfer Hvariants Hunknown Hmissing Hdup.
        revert Σ_tail Ts_tail roots_tail Htail.
        induction v_tail as [|v rest IHtail];
          intros Σ_tail Ts_tail roots_tail Htail0; simpl in Htail0.
        - inversion Htail0; subst. constructor.
        -
          destruct (lookup_expr_branch_binders (enum_variant_name v) l)
            as [binders |] eqn:Hbinders0; try discriminate.
          destruct (lookup_branch_b (enum_variant_name v) l) as [e0 |]
            eqn:Hlookup0; try discriminate.
          destruct (match_payload_params binders l0 l1 v) as [ps | err_params]
            eqn:Hparams; try discriminate.
          destruct (params_names_nodup_b ps && ctx_lookup_params_none_b ps Σ1 &&
              root_env_lookup_params_none_b ps R1) eqn:Hparam_checks; try discriminate.
          destruct (infer_core_env_state_fuel_roots fuel' env Ω n
              (root_env_add_params_roots_same ps roots_scrut R1)
              (sctx_add_params ps Σ1) e0)
            as [[[[T0 Σ0] R0] roots0] | err0] eqn:Hinfer0; try discriminate.
          destruct (params_ok_sctx_b env ps Σ0 &&
              roots_exclude_params_b ps roots0 &&
              root_env_excludes_params_b ps (root_env_remove_match_params ps R0))
            eqn:Hcleanup_checks; try discriminate.
          destruct (ty_core_eqb (ty_core T0) (ty_core T_head)) eqn:Hcore0;
            try discriminate.
          destruct (root_env_eqb (root_env_remove_match_params ps R0)
              (root_env_remove_match_params ps_head R_head_payload))
            eqn:Hroot0; try discriminate.
          change (infer_if_bool true ?ok ?err) with ok in Htail0.
          remember
            ((fix infer_rest (T_head0 : Ty) (R_out0 : root_env)
                (defs0 : list enum_variant_def) {struct defs0}
                : infer_result (list sctx * list Ty * list root_set) :=
                match defs0 with
                | [] => infer_ok ([], [], [])
                | v0 :: rest0 =>
                    match
                      match lookup_expr_branch_binders (enum_variant_name v0) l with
                      | Some binders0 =>
                          match lookup_branch_b (enum_variant_name v0) l with
                          | Some e1 =>
                              match match_payload_params binders0 l0 l1 v0 with
                              | infer_ok ps0 =>
                                  if params_names_nodup_b ps0 &&
                                     ctx_lookup_params_none_b ps0 Σ1 &&
                                     root_env_lookup_params_none_b ps0 R1
                                  then
                                    match infer_core_env_state_fuel_roots fuel' env Ω n
                                            (root_env_add_params_roots_same ps0 roots_scrut R1)
                                            (sctx_add_params ps0 Σ1) e1 with
                                    | infer_ok (T1, Σ1_payload, R1_payload, roots1) =>
                                        if params_ok_sctx_b env ps0 Σ1_payload &&
                                           roots_exclude_params_b ps0 roots1 &&
                                           root_env_excludes_params_b ps0
                                             (root_env_remove_match_params ps0 R1_payload)
                                        then infer_ok
                                          (T1, sctx_remove_params ps0 Σ1_payload,
                                           root_env_remove_match_params ps0 R1_payload,
                                           roots1)
                                        else infer_err ErrContextCheckFailed
                                    | infer_err err => infer_err err
                                    end
                                  else infer_err ErrContextCheckFailed
                              | infer_err err => infer_err err
                              end
                          | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                          end
                      | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                      end
                    with
                    | infer_ok (T1, Σv, Rv, rootsv) =>
                        if ty_core_eqb (ty_core T1) (ty_core T_head0)
                        then
                          infer_if_bool (root_env_eqb Rv R_out0)
                            match infer_rest T_head0 R_out0 rest0 with
                            | infer_err err => infer_err err
                            | infer_ok (Σs, Ts, rootss) =>
                                infer_ok (Σv :: Σs, T1 :: Ts, rootsv :: rootss)
                            end
                            (infer_err ErrContextCheckFailed)
                        else infer_err (ErrTypeMismatch (ty_core T1) (ty_core T_head0))
                    | infer_err err => infer_err err
                    end
                end) T_head
                  (root_env_remove_match_params ps_head R_head_payload)
                  rest) as tail0 eqn:Htail_rest.
          destruct tail0 as [[[Σs Ts] rootss] | err_tail0]; try discriminate.
          inversion Htail0; subst.
          symmetry in Htail_rest.
          rewrite lookup_branch_b_lookup_expr_branch in Hlookup0.
	          eapply TERMatchTail_Cons with
	            (R_payload := root_env_add_params_roots_same ps roots_scrut R1)
            (Rv_payload := R0) (Rv := root_env_remove_match_params ps R0)
	            (Σv_payload := Σ0) (Σv := sctx_remove_params ps Σ0)
		            (Σs := Σs) (Ts := Ts) (rootss := rootss)
		            (T := T0) (e := e0) (binders := binders) (ps := ps)
		            (lts := l0) (args := l1) (roots_scrut := roots_scrut).
		          + exact Hbinders0.
	          + exact Hparams.
          + apply andb_prop in Hparam_checks as [Hnodup_rest Hrenv].
            apply andb_prop in Hnodup_rest as [Hnodup _]. exact Hnodup.
          + apply andb_prop in Hparam_checks as [Hnodup_rest Hrenv].
            apply andb_prop in Hnodup_rest as [_ Hctx]. exact Hctx.
          + apply andb_prop in Hparam_checks as [_ Hrenv]. exact Hrenv.
          + exact Hlookup0.
          + reflexivity.
          + eapply IH. exact Hinfer0.
          + apply andb_prop in Hcleanup_checks as [Hok_rest Hrexcl].
            apply andb_prop in Hok_rest as [Hok _]. exact Hok.
          + apply andb_prop in Hcleanup_checks as [Hok_rest _].
            apply andb_prop in Hok_rest as [_ Hexcl].
            apply roots_exclude_params_b_sound_local. exact Hexcl.
          + reflexivity.
          + apply andb_prop in Hcleanup_checks as [_ Hrexcl].
            apply root_env_excludes_params_b_sound_local. exact Hrexcl.
          + reflexivity.
          + apply ty_core_eqb_true. exact Hcore0.
          + apply root_env_eqb_true_equiv. exact Hroot0.
          + eapply IHtail. reflexivity.
      }
      destruct (ctx_merge_many
          (ctx_of_sctx (sctx_remove_params ps_head Σ_head_payload))
          (map ctx_of_sctx Σ_tail)) as [Γ_out |] eqn:Hmerge; try discriminate.
      assert (Hcalc :
        infer_core_env_state_fuel_roots (S fuel') env Ω n R Σ (EMatch e l) =
        infer_ok
          (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head),
           sctx_of_ctx Γ_out,
           root_env_remove_match_params ps_head R_head_payload,
           root_set_union roots_head (root_sets_union roots_tail))).
      {
        simpl in Hmissing.
        simpl.
        rewrite Hscrut, Hscrut_core, Hlookup, Hlts, Hargslen, Hbounds,
          Hdup, Hvariants.
        simpl.
        rewrite Hunknown, Hmissing.
        rewrite Hbinders_head, Hlookup_branch, Hparams_head, Hnodup_head,
          Hhead.
        simpl.
        destruct (params_ok_sctx_b env ps_head Σ_head_payload &&
            roots_exclude_params_b ps_head roots_head &&
            root_env_excludes_params_b ps_head
              (root_env_remove_match_params ps_head R_head_payload)) eqn:Hcleanup;
          [| rewrite Hcleanup_head in Hcleanup; discriminate].
        simpl.
        rewrite Htail.
        simpl.
        rewrite Hmerge.
        reflexivity.
      }
      inversion Hinfer; subst.
      rewrite lookup_branch_b_lookup_expr_branch in Hlookup_branch.
	      eapply TER_Match with
        (R1 := R1)
        (R_payload := root_env_add_params_roots_same ps_head roots_scrut R1)
        (R_head_payload := R_head_payload)
        (R_out := root_env_remove_match_params ps_head R_head_payload)
        (Σ1 := Σ1) (Σ_head_payload := Σ_head_payload)
        (Σ_head := sctx_remove_params ps_head Σ_head_payload)
        (Σ_tail := Σ_tail)
        (Γ_out := Γ_out) (edef := edef) (v_head := v_head)
        (v_tail := v_tail) (e_head := e_head) (T_scrut := T_scrut)
        (T_head := T_head) (Ts_tail := Ts_tail)
        (roots_scrut := roots_scrut) (roots_head := roots_head)
        (roots_tail := roots_tail)
        (binders_head := binders_head) (ps_head := ps_head);
        [ eapply IH; exact Hscrut
        | exact Hscrut_core
        | exact Hlookup
        | apply negb_false_iff in Hlts; apply Nat.eqb_eq in Hlts; exact Hlts
        | apply negb_false_iff in Hargslen; apply Nat.eqb_eq in Hargslen; exact Hargslen
	        | exact Hbounds
	        | rewrite Hvariants; exact Hunknown
	        | exact Hvariants
		        | exact Hbinders_head
        | exact Hparams_head
        | apply andb_prop in Hnodup_head as [Hnd_rest Hrenv]; apply andb_prop in Hnd_rest as [Hnd _]; exact Hnd
        | apply andb_prop in Hnodup_head as [Hnd_rest Hrenv]; apply andb_prop in Hnd_rest as [_ Hctx]; exact Hctx
        | apply andb_prop in Hnodup_head as [_ Hrenv]; exact Hrenv
        | exact Hlookup_branch
        | reflexivity
        | eapply IH; exact Hhead
        | apply andb_prop in Hcleanup_head as [Hok_rest Hrexcl]; apply andb_prop in Hok_rest as [Hok _]; exact Hok
        | apply andb_prop in Hcleanup_head as [Hok_rest _]; apply andb_prop in Hok_rest as [_ Hexcl]; apply roots_exclude_params_b_sound_local; exact Hexcl
        | reflexivity
        | apply andb_prop in Hcleanup_head as [_ Hrexcl]; apply root_env_excludes_params_b_sound_local; exact Hrexcl
        | reflexivity
        | exact Htail_typed
        | exact Hmerge ];
        try solve [eauto | reflexivity].
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
        replace [RStore x] with (root_of_place p).
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
    + destruct e; try discriminate.
      destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct (usage_eqb (ty_usage Tp) UUnrestricted) eqn:Husage; try discriminate.
      destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup; try discriminate.
      destruct r.
      * inversion Hinfer; subst.
        eapply TER_DerefBorrowShared.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hlookup.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        inversion Hinfer; subst.
        eapply TER_DerefBorrowUnique.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hmut.
        -- exact Hlookup.
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
      * apply root_env_eqb_true_equiv. exact Hroot_eq.
Qed.

Theorem infer_core_env_state_fuel_roots_shadow_safe_sound :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots.
Proof.
  induction fuel as [|fuel' IH]; intros env Ω n R Σ e T Σ' R' roots Hinfer.
  - simpl in Hinfer. discriminate.
	  - destruct e as [|l|i|m i t e1 e2|m i e1 e2|i|i l|p|i l|i l l0|e l|
	      s l l0 l1|s s0 l l0 l1|e l|p e|p e|r p|e|e|e1 e2 e3];
      simpl in Hinfer; try discriminate.
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
        eapply TERS_Var_Copy.
        -- apply TPES_Var with (st := st); assumption.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hlookup.
      * destruct (sctx_consume_path Σ i []) as [Σc | err] eqn:Hconsume;
          try discriminate.
        inversion Hinfer; subst.
        eapply TERS_Var_Move.
        -- apply TPES_Var with (st := st); assumption.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hconsume.
        -- exact Hlookup.
    + destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1)
        as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
      destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; try discriminate.
      destruct (root_env_lookup i R1) eqn:Hfresh; try discriminate.
      destruct (roots_exclude_b i roots1) eqn:Hroots1; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i R1) eqn:Henv1; simpl in Hinfer; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
          (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok env i t Σ2) eqn:Hcheck; simpl in Hinfer; try discriminate.
      destruct (roots_exclude_b i roots2) eqn:Hroots2; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i (root_env_remove i R2)) eqn:Henv2;
        simpl in Hinfer; try discriminate.
      inversion Hinfer; subst.
      eapply TERS_Let.
      * eapply IH. exact He1.
      * exact Hcompat.
      * exact Hfresh.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * eapply IH. exact He2.
      * exact Hcheck.
      * apply roots_exclude_b_sound. exact Hroots2.
      * apply root_env_excludes_b_sound. exact Henv2.
    + destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1)
        as [[[[T1 Σ1] R1] roots1] | err1] eqn:He1; try discriminate.
      destruct (root_env_lookup i R1) eqn:Hfresh; try discriminate.
      destruct (roots_exclude_b i roots1) eqn:Hroots1; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i R1) eqn:Henv1; simpl in Hinfer; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
          (root_env_add i roots1 R1) (sctx_add i T1 m Σ1) e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok env i T1 Σ2) eqn:Hcheck; simpl in Hinfer; try discriminate.
      destruct (roots_exclude_b i roots2) eqn:Hroots2; simpl in Hinfer; try discriminate.
      destruct (root_env_excludes_b i (root_env_remove i R2)) eqn:Henv2;
        simpl in Hinfer; try discriminate.
      inversion Hinfer; subst.
      eapply TERS_LetInfer.
      * eapply IH. exact He1.
      * exact Hfresh.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * eapply IH. exact He2.
      * exact Hcheck.
      * apply roots_exclude_b_sound. exact Hroots2.
      * apply root_env_excludes_b_sound. exact Henv2.
		    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
			      unfold no_captures_b in Hinfer.
				      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
			      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TERS_Fn; eassumption.
		    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
		      destruct (check_make_closure_captures_sctx_with_env env Ω Σ l (fn_captures fdef))
		        as [[env_lt captured_tys] | err] eqn:Hcheck; try discriminate.
	      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TERS_MakeClosure; eassumption.
	    + unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
      destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup; try discriminate.
      destruct (usage_eqb (ty_usage Tp) UUnrestricted) eqn:Husage.
      * inversion Hinfer; subst.
        eapply TERS_Place_Copy.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hlookup.
      * destruct (sctx_consume_path Σ x path) as [Σc | err] eqn:Hconsume;
          try discriminate.
        inversion Hinfer; subst.
        eapply TERS_Place_Move.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hpath.
        -- exact Hconsume.
        -- exact Hlookup.
	    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
	      unfold no_captures_b in Hinfer.
	      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
	      destruct (Nat.eqb (fn_type_params fdef) 0) eqn:Htypeparams; try discriminate.
	      rewrite infer_env_args_collect_roots_shadow_safe_eq in Hinfer.
      destruct (infer_env_args_collect_roots_shadow_safe fuel' env Ω n R Σ l)
        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
        try discriminate.
      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
          arg_tys (fn_params fdef)) as [σ_acc |] eqn:Hbuild; try discriminate.
	      destruct (check_args Ω arg_tys
	          (apply_lt_params (finalize_subst σ_acc) (fn_params fdef)))
	        as [err |] eqn:Hcheck; try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
        try discriminate.
      destruct (outlives_constraints_hold_b Ω
          (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)))
        eqn:Hout; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TERS_Call with (fdef := fdef) (σ := finalize_subst σ_acc).
	      * exact Hin.
	      * exact Hname.
	      * exact Hcaps.
	      * apply Nat.eqb_eq. exact Htypeparams.
	      * eapply infer_env_args_collect_roots_shadow_safe_sound.
	        -- exact Hcollect.
	        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
	           eapply IH. exact Hinfer0.
	        -- exact Hcheck.
	      * apply outlives_constraints_hold_b_sound. exact Hout.
	    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
	      unfold no_captures_b in Hinfer.
	      destruct (fn_captures fdef) as [| cap caps] eqn:Hcaps; try discriminate.
	      destruct (Nat.eqb (Datatypes.length l) (fn_type_params fdef)) eqn:Htypeparams;
	        try discriminate.
	      destruct (check_struct_bounds env (fn_bounds fdef) l) eqn:Hbounds; try discriminate.
	      rewrite infer_env_args_collect_roots_shadow_safe_eq in Hinfer.
	      destruct (infer_env_args_collect_roots_shadow_safe fuel' env Ω n R Σ l0)
	        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
	        try discriminate.
	      remember (apply_type_params l (fn_params fdef)) as ps_typed.
	      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
	          arg_tys ps_typed) as [σ_acc |] eqn:Hbuild; try discriminate.
	      destruct (check_args Ω arg_tys
	          (apply_lt_params (finalize_subst σ_acc) ps_typed))
	        as [err |] eqn:Hcheck; try discriminate.
	      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
	        try discriminate.
	      destruct (outlives_constraints_hold_b Ω
	          (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)))
	        eqn:Hout; try discriminate.
	      inversion Hinfer; subst.
	      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
	      eapply TERS_CallGeneric with (fdef := fdef) (σ := finalize_subst σ_acc).
	      * exact Hin.
	      * exact Hname.
	      * exact Hcaps.
	      * apply Nat.eqb_eq. exact Htypeparams.
	      * exact Hbounds.
	      * eapply infer_env_args_collect_roots_shadow_safe_sound.
	        -- exact Hcollect.
	        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
	           eapply IH. exact Hinfer0.
	        -- exact Hcheck.
	      * apply outlives_constraints_hold_b_sound. exact Hout.
	    + destruct e; try discriminate.
      destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup;
        try discriminate.
      destruct (check_make_closure_captures_sctx_with_env env Ω Σ l0
        (fn_captures fdef)) as [[env_lt captured_tys] | err] eqn:Hcaptures;
        try discriminate.
      rewrite infer_env_args_collect_roots_shadow_safe_eq in Hinfer.
      destruct (infer_env_args_collect_roots_shadow_safe fuel' env Ω n R Σ l)
        as [[[[arg_tys Σargs] Rargs] arg_roots] | err] eqn:Hcollect;
        try discriminate.
      destruct (build_sigma (fn_lifetimes fdef)
        (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
        as [σ_acc |] eqn:Hbuild; try discriminate.
      remember (finalize_subst σ_acc) as σ.
      remember (apply_lt_params σ (fn_params fdef)) as ps_subst.
      destruct (check_args Ω arg_tys ps_subst) as [err |] eqn:Hcheck;
        try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) σ) eqn:Hwf;
        try discriminate.
      destruct (outlives_constraints_hold_b Ω
        (apply_lt_outlives σ (fn_outlives fdef))) eqn:Hout;
        try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TERS_CallExpr_MakeClosure with (σ := finalize_subst σ_acc).
      * exact Hin.
      * exact Hname.
      * exact Hcaptures.
      * eapply infer_env_args_collect_roots_shadow_safe_sound.
        -- exact Hcollect.
        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
           eapply IH. exact Hinfer0.
        -- exact Hcheck.
      * apply outlives_constraints_hold_b_sound. exact Hout.
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
      rewrite infer_env_fields_collect_roots_shadow_safe_eq in Hinfer.
      destruct (infer_env_fields_collect_roots_shadow_safe fuel' env Ω n l l0 R Σ l1 (struct_fields sdef))
        as [[[Σfields Rfields] roots_fields] | err] eqn:Hfields; try discriminate.
      inversion Hinfer; subst.
      apply negb_false_iff in Hlts. apply Nat.eqb_eq in Hlts.
      apply negb_false_iff in Hargslen. apply Nat.eqb_eq in Hargslen.
      eapply TERS_Struct.
      * exact Hlookup.
      * exact Hlts.
      * exact Hargslen.
      * exact Hbounds.
      * eapply infer_env_fields_collect_roots_shadow_safe_sound.
        -- exact Hfields.
        -- intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
           eapply IH. exact Hinfer0.
    + destruct (lookup_enum s env) as [edef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l) (enum_lifetimes edef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (enum_type_params edef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (enum_bounds edef) l0) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (lookup_enum_variant s0 (enum_variants edef)) as [vdef |] eqn:Hvariant;
        try discriminate.
      rewrite infer_env_enum_payloads_collect_roots_shadow_safe_eq in Hinfer.
      destruct (infer_env_enum_payloads_collect_roots_shadow_safe fuel' env Ω n l l0 R Σ
        (enum_variant_fields vdef) l1) as [[[Σpayloads Rpayloads] roots_payloads] | err]
        eqn:Hpayloads; try discriminate.
      inversion Hinfer; subst.
      apply negb_false_iff in Hlts. apply Nat.eqb_eq in Hlts.
      apply negb_false_iff in Hargslen. apply Nat.eqb_eq in Hargslen.
      destruct (infer_env_enum_payloads_collect_roots_shadow_safe_sound
        fuel' env Ω n l l0 R Σ (enum_variant_fields vdef) l1
        Σ' R' roots Hpayloads)
        as [payload_roots [Hpayload_roots Hroots]].
      { intros R0 Σ0 e0 T0 Σ1 R1 roots1 Hinfer0.
        eapply IH. exact Hinfer0. }
      subst roots.
      eapply TERS_Enum.
      * exact Hlookup.
      * exact Hvariant.
      * exact Hlts.
      * exact Hargslen.
      * exact Hbounds.
      * exact Hpayload_roots.
    + destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e)
        as [[[[T_scrut Σ1] R1] roots_scrut] | err_scrut] eqn:Hscrut;
        try discriminate.
      destruct (ty_core T_scrut) eqn:Hscrut_core; try discriminate.
      destruct (lookup_enum s env) as [edef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (enum_lifetimes edef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l1) (enum_type_params edef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (enum_bounds edef) l1) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (first_duplicate_branch l) as [dup |] eqn:Hdup; try discriminate.
      destruct (first_unknown_variant_branch l (enum_variants edef)) as [unknown |]
        eqn:Hunknown; try discriminate.
      destruct (first_unsupported_match_payload l (enum_variants edef)) as [payload |]
        eqn:Hunsupported; try discriminate.
      destruct (first_unsupported_match_payload_none _ _ Hunsupported)
        as [Hbinders Hpayload].
      destruct (first_missing_variant_branch (enum_variants edef) l) as [missing |]
        eqn:Hmissing; try discriminate.
      destruct (enum_variants edef) as [|v_head v_tail] eqn:Hvariants;
        try discriminate.
      simpl in Hinfer.
      destruct (lookup_branch_b (enum_variant_name v_head) l) as [e_head |]
        eqn:Hlookup_branch.
      2: {
        destruct (lookup_expr_branch_binders (enum_variant_name v_head) l);
          discriminate.
      }
      assert (Hfields_head : enum_variant_fields v_head = []).
      {
        simpl in Hpayload.
        destruct (enum_variant_fields v_head) eqn:Hfields; [reflexivity | discriminate].
      }
      assert (Hbinders_head :
        lookup_expr_branch_binders (enum_variant_name v_head) l = Some []).
      {
        rewrite lookup_branch_b_lookup_expr_branch in Hlookup_branch.
        eapply first_payload_binder_branch_lookup_none; eassumption.
      }
      rewrite Hbinders_head in Hinfer.
      assert (Hparams_head :
        match_payload_params [] l0 l1 v_head = infer_ok []).
      {
        unfold match_payload_params, instantiate_enum_variant_field_tys.
        rewrite Hfields_head. simpl. reflexivity.
      }
      rewrite Hparams_head in Hinfer. simpl in Hinfer.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
          (sctx_add_params [] Σ1) e_head)
        as [[[[T_head Σ_head] R_out] roots_head] | err_head] eqn:Hhead;
        try discriminate.
      remember
        ((fix infer_rest (T_head0 : Ty) (R_out0 : root_env)
            (defs0 : list enum_variant_def) {struct defs0}
            : infer_result (list sctx * list Ty * list root_set) :=
            match defs0 with
            | [] => infer_ok ([], [], [])
            | v0 :: rest0 =>
                match
                  match lookup_expr_branch_binders (enum_variant_name v0) l with
                  | Some binders =>
                      match lookup_branch_b (enum_variant_name v0) l with
                      | Some e_branch =>
                          match match_payload_params binders l0 l1 v0 with
                          | infer_ok ps =>
                              if params_names_nodup_b ps &&
                                 ctx_lookup_params_none_b ps Σ1 &&
                                 root_env_lookup_params_none_b ps R1
                              then
                                match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                                        (root_env_add_params_roots_same ps roots_scrut R1)
                                        (sctx_add_params ps Σ1) e_branch with
                                | infer_ok (T_branch, Σ_branch_payload,
                                            R_branch_payload, roots_branch) =>
                                    if params_ok_sctx_b env ps Σ_branch_payload &&
                                       roots_exclude_params_b ps roots_branch &&
                                       root_env_excludes_params_b ps
                                         (root_env_remove_match_params ps R_branch_payload)
                                    then infer_ok
                                      (T_branch,
                                       sctx_remove_params ps Σ_branch_payload,
                                       root_env_remove_match_params ps R_branch_payload,
                                       roots_branch)
                                    else infer_err ErrContextCheckFailed
                                | infer_err err => infer_err err
                                end
                              else infer_err ErrContextCheckFailed
                          | infer_err err => infer_err err
                          end
                      | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                      end
                  | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                  end
                with
                | infer_ok (T0, Σ0, R0, roots0) =>
                    if ty_core_eqb (ty_core T0) (ty_core T_head0)
                    then
                      infer_if_bool (root_env_eqb R0 R_out0)
                        match infer_rest T_head0 R_out0 rest0 with
                        | infer_err err => infer_err err
                        | infer_ok (Σs, Ts, rootss) =>
                            infer_ok (Σ0 :: Σs, T0 :: Ts, roots0 :: rootss)
                        end
                        (infer_err ErrContextCheckFailed)
                    else infer_err (ErrTypeMismatch (ty_core T0) (ty_core T_head0))
                | infer_err err => infer_err err
                end
            end) T_head R_out v_tail) as tail_result eqn:Htail.
      destruct tail_result as [[[Σ_tail Ts_tail] roots_tail] | err_tail];
        try discriminate.
      symmetry in Htail.
      assert (Hpayload_tail : first_payload_variant v_tail = None).
      {
        simpl in Hpayload.
        destruct (enum_variant_fields v_head); try discriminate.
        exact Hpayload.
      }
      assert (Htail_typed :
        typed_match_tail_roots_shadow_safe env Ω n l0 l1 R1 roots_scrut Σ1 l v_tail
          (ty_core T_head) R_out Σ_tail Ts_tail roots_tail).
      {
        clear Hinfer Hvariants Hunknown Hmissing Hdup Hunsupported Hpayload.
        revert Σ_tail Ts_tail roots_tail Htail Hpayload_tail.
        induction v_tail as [|v rest IHtail];
          intros Σ_tail Ts_tail roots_tail Htail0 Hpayload0; simpl in Htail0.
        - inversion Htail0; subst. constructor.
        - simpl in Hpayload0.
          destruct (enum_variant_fields v) eqn:Hfields; try discriminate.
          destruct (lookup_expr_branch_binders (enum_variant_name v) l)
            as [binders |] eqn:Hbinders0; try discriminate.
          destruct (lookup_branch_b (enum_variant_name v) l) as [e0 |]
            eqn:Hlookup0; try discriminate.
          destruct (match_payload_params binders l0 l1 v) as [ps | err_params]
            eqn:Hparams; try discriminate.
          destruct (params_names_nodup_b ps && ctx_lookup_params_none_b ps Σ1 &&
              root_env_lookup_params_none_b ps R1) eqn:Hparam_checks; try discriminate.
          destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
              (root_env_add_params_roots_same ps roots_scrut R1)
              (sctx_add_params ps Σ1) e0)
            as [[[[T0 Σ0] R0] roots0] | err0] eqn:Hinfer0; try discriminate.
          destruct (params_ok_sctx_b env ps Σ0 &&
              roots_exclude_params_b ps roots0 &&
              root_env_excludes_params_b ps (root_env_remove_match_params ps R0))
            eqn:Hcleanup_checks; try discriminate.
          destruct (ty_core_eqb (ty_core T0) (ty_core T_head)) eqn:Hcore0;
            try discriminate.
          destruct (root_env_eqb (root_env_remove_match_params ps R0) R_out)
            eqn:Hroot0; try discriminate.
          change (infer_if_bool true ?ok ?err) with ok in Htail0.
          remember
            ((fix infer_rest (T_head0 : Ty) (R_out0 : root_env)
                (defs0 : list enum_variant_def) {struct defs0}
                : infer_result (list sctx * list Ty * list root_set) :=
                match defs0 with
                | [] => infer_ok ([], [], [])
                | v0 :: rest0 =>
                    match
                      match lookup_expr_branch_binders (enum_variant_name v0) l with
                      | Some binders0 =>
                          match lookup_branch_b (enum_variant_name v0) l with
                          | Some e1 =>
                              match match_payload_params binders0 l0 l1 v0 with
                              | infer_ok ps0 =>
                                  if params_names_nodup_b ps0 &&
                                     ctx_lookup_params_none_b ps0 Σ1 &&
                                     root_env_lookup_params_none_b ps0 R1
                                  then
                                    match infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n
                                            (root_env_add_params_roots_same ps0 roots_scrut R1)
                                            (sctx_add_params ps0 Σ1) e1 with
                                    | infer_ok (T1, Σ1_payload, R1_payload, roots1) =>
                                        if params_ok_sctx_b env ps0 Σ1_payload &&
                                           roots_exclude_params_b ps0 roots1 &&
                                           root_env_excludes_params_b ps0
                                             (root_env_remove_match_params ps0 R1_payload)
                                        then infer_ok
                                          (T1, sctx_remove_params ps0 Σ1_payload,
                                           root_env_remove_match_params ps0 R1_payload,
                                           roots1)
                                        else infer_err ErrContextCheckFailed
                                    | infer_err err => infer_err err
                                    end
                                  else infer_err ErrContextCheckFailed
                              | infer_err err => infer_err err
                              end
                          | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                          end
                      | None => infer_err (ErrMissingVariant (enum_variant_name v0))
                      end
                    with
                    | infer_ok (T1, Σv, Rv, rootsv) =>
                        if ty_core_eqb (ty_core T1) (ty_core T_head0)
                        then
                          infer_if_bool (root_env_eqb Rv R_out0)
                            match infer_rest T_head0 R_out0 rest0 with
                            | infer_err err => infer_err err
                            | infer_ok (Σs, Ts, rootss) =>
                                infer_ok (Σv :: Σs, T1 :: Ts, rootsv :: rootss)
                            end
                            (infer_err ErrContextCheckFailed)
                        else infer_err (ErrTypeMismatch (ty_core T1) (ty_core T_head0))
                    | infer_err err => infer_err err
                    end
                end) T_head R_out rest) as tail0 eqn:Htail_rest.
          destruct tail0 as [[[Σs Ts] rootss] | err_tail0]; try discriminate.
          inversion Htail0; subst.
          symmetry in Htail_rest.
          rewrite lookup_branch_b_lookup_expr_branch in Hlookup0.
          assert (Hbinders_nil : binders = []).
          {
            pose proof (first_payload_binder_branch_lookup_none
              l (enum_variant_name v) e0 Hbinders Hlookup0) as Hnone_lookup.
            rewrite Hbinders0 in Hnone_lookup. inversion Hnone_lookup. reflexivity.
          }
          subst binders.
          assert (Hps_nil : ps = []).
          {
            unfold match_payload_params, instantiate_enum_variant_field_tys in Hparams.
            rewrite Hfields in Hparams. simpl in Hparams.
            inversion Hparams. reflexivity.
          }
          subst ps.
          simpl in Hparam_checks, Hcleanup_checks.
	          eapply TERSMatchTail_Cons with
            (R_payload := R1) (Rv_payload := R0) (Rv := R0)
            (Σv_payload := Σ0) (Σv := Σ0)
	            (Σs := Σs) (Ts := Ts) (rootss := rootss)
	            (T := T0) (e := e0) (binders := []) (ps := [])
	            (lts := l0) (args := l1) (roots_scrut := roots_scrut).
		          + exact Hfields.
		          + reflexivity.
		          + exact Hbinders0.
	          + unfold match_payload_params, instantiate_enum_variant_field_tys.
            rewrite Hfields. simpl. reflexivity.
          + reflexivity.
          + reflexivity.
          + reflexivity.
          + exact Hlookup0.
          + reflexivity.
          + eapply IH. exact Hinfer0.
          + reflexivity.
          + constructor.
          + reflexivity.
          + constructor.
          + reflexivity.
          + apply ty_core_eqb_true. exact Hcore0.
          + apply root_env_eqb_true_equiv. exact Hroot0.
          + eapply IHtail.
            * reflexivity.
            * exact Hpayload0.
      }
      destruct (ctx_merge_many (ctx_of_sctx Σ_head) (map ctx_of_sctx Σ_tail))
        as [Γ_out |] eqn:Hmerge; try discriminate.
      inversion Hinfer; subst.
      rewrite lookup_branch_b_lookup_expr_branch in Hlookup_branch.
      change (typed_env_roots_shadow_safe env Ω n R Σ (EMatch e l)
        (MkTy (usage_max_tys_nonempty T_head Ts_tail) (ty_core T_head))
        (sctx_of_ctx Γ_out) R'
        (root_set_union roots_head (root_sets_union roots_tail))).
	      eapply TERS_Match with
        (R1 := R1) (R_payload := R1) (R_head_payload := R')
        (R_out := R') (Σ1 := Σ1) (Σ_head_payload := Σ_head)
        (Σ_head := Σ_head) (Σ_tail := Σ_tail)
        (Γ_out := Γ_out) (edef := edef) (v_head := v_head)
        (v_tail := v_tail) (e_head := e_head) (T_scrut := T_scrut)
        (T_head := T_head) (Ts_tail := Ts_tail)
        (roots_scrut := roots_scrut) (roots_head := roots_head)
        (roots_tail := roots_tail) (binders_head := []) (ps_head := []);
        [ eapply IH; exact Hscrut
        | exact Hscrut_core
        | exact Hlookup
        | apply negb_false_iff in Hlts; apply Nat.eqb_eq in Hlts; exact Hlts
        | apply negb_false_iff in Hargslen; apply Nat.eqb_eq in Hargslen; exact Hargslen
	        | exact Hbounds
	        | rewrite Hvariants; exact Hunknown
	        | exact Hvariants
		        | exact Hfields_head
		        | reflexivity
		        | exact Hbinders_head
	        | exact Hparams_head
        | reflexivity
        | reflexivity
        | reflexivity
        | exact Hlookup_branch
        | reflexivity
        | eapply IH; exact Hhead
        | reflexivity
        | constructor
        | reflexivity
        | constructor
        | reflexivity
        | exact Htail_typed
        | exact Hmerge ];
        try solve [eauto | reflexivity].
    + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Told | err] eqn:Hplace; try discriminate.
      destruct (root_env_lookup x R) as [roots_result |] eqn:Hroot_result; try discriminate.
      destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
      destruct mut; try discriminate.
      destruct (writable_place_b env Σ p) eqn:Hwrite; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e)
        as [[[[Tnew Σ1] R1] roots_new] | err] eqn:Hnew; try discriminate.
      destruct (root_env_lookup x R1) as [roots_old |] eqn:Hroot_old; try discriminate.
      destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
      destruct (sctx_path_available Σ1 x path) as [[] | err] eqn:Havailable; try discriminate.
      destruct (sctx_restore_path Σ1 x path) as [Σ2 | err] eqn:Hrestore; try discriminate.
      inversion Hinfer; subst.
      eapply TERS_Replace_Path.
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
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e)
        as [[[[Tnew Σ1] R1] roots_new] | err] eqn:Hnew; try discriminate.
      destruct (root_env_lookup x R1) as [roots_old |] eqn:Hroot_old; try discriminate.
      destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
      destruct (sctx_path_available Σ1 x path) as [[] | err] eqn:Havailable; try discriminate.
      inversion Hinfer; subst.
      eapply TERS_Assign_Path.
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
        replace [RStore x] with (root_of_place p).
        -- eapply TERS_BorrowShared.
           eapply infer_place_sctx_structural_sound. exact Hplace.
        -- eapply root_of_place_direct. exact Hpath.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        inversion Hinfer; subst.
        eapply TERS_BorrowUnique.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- exact Hpath.
        -- exact Hmut.
    + destruct e; try discriminate.
      destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
      destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct (usage_eqb (ty_usage Tp) UUnrestricted) eqn:Husage; try discriminate.
      destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup; try discriminate.
      destruct r.
      * inversion Hinfer; subst.
        eapply TERS_DerefBorrowShared.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hlookup.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        inversion Hinfer; subst.
        eapply TERS_DerefBorrowUnique.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
        -- exact Hpath.
        -- exact Hmut.
        -- exact Hlookup.
    + destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e)
        as [[[[Te Σe] Re] roots_e] | err] eqn:He; try discriminate.
      inversion Hinfer; subst.
      eapply TERS_Drop. eapply IH. exact He.
    + destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R Σ e1)
        as [[[[Tcond Σ1] R1] roots_cond] | err1] eqn:He1; try discriminate.
      destruct (ty_core_eqb (ty_core Tcond) TBooleans) eqn:Hbool; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e2)
        as [[[[T2 Σ2] R2] roots2] | err2] eqn:He2; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1 Σ1 e3)
        as [[[[T3 Σ3] R3] roots3] | err3] eqn:He3; try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3)) eqn:Hcore; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |] eqn:Hmerge;
        try discriminate.
      inversion Hinfer; subst.
      eapply TERS_If.
      * eapply IH. exact He1.
      * apply ty_core_eqb_true. exact Hbool.
      * eapply IH. exact He2.
      * eapply IH. exact He3.
      * apply ty_core_eqb_true. exact Hcore.
      * exact Hmerge.
      * apply root_env_eqb_true_equiv. exact Hroot_eq.
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

Theorem infer_core_env_roots_shadow_safe_sound :
  forall env Ω n R Γ e T Γ' R' roots,
    infer_core_env_roots_shadow_safe env Ω n R Γ e =
      infer_ok (T, Γ', R', roots) ->
    typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ) e T
      (sctx_of_ctx Γ') R' roots.
Proof.
  unfold infer_core_env_roots_shadow_safe, sctx_of_ctx, ctx_of_sctx.
  intros env Ω n R Γ e T Γ' R' roots Hinfer.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Ω n R Γ e)
    as [[[[T0 Σ] R0] roots0] | err] eqn:Hcore; try discriminate.
  inversion Hinfer; subst.
  eapply infer_core_env_state_fuel_roots_shadow_safe_sound. exact Hcore.
Qed.

Definition typed_fn_env_roots (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Γ_out,
    typed_env_roots (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Γ_out) R_out roots /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Γ_out = true.

Definition checked_fn_env_roots (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  typed_fn_env_roots env f R0 R_out roots /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

Definition typed_fn_env_roots_shadow_safe (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  exists T_body Γ_out,
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (sctx_of_ctx (fn_body_ctx f))
      (fn_body f) T_body (sctx_of_ctx Γ_out) R_out roots /\
    ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
    params_ok_env_b env (fn_params f) Γ_out = true.

Definition checked_fn_env_roots_shadow_safe (env : global_env) (f : fn_def)
    (R0 R_out : root_env) (roots : root_set) : Prop :=
  typed_fn_env_roots_shadow_safe env f R0 R_out roots /\
  (exists PBS',
    borrow_ok_env_structural env [] (fn_body_ctx f) (fn_body f) PBS') /\
  NoDup (ctx_names (params_ctx (fn_params f))).

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

Lemma typed_fn_env_roots_shadow_safe_roots :
  forall env f R0 R_out roots,
    typed_fn_env_roots_shadow_safe env f R0 R_out roots ->
    typed_fn_env_roots env f R0 R_out roots.
Proof.
  unfold typed_fn_env_roots_shadow_safe, typed_fn_env_roots.
  intros env f R0 R_out roots Htyped.
  destruct Htyped as [T_body [Γ_out [Htyped [Hcompat Hparams]]]].
  exists T_body, Γ_out.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma typed_fn_env_roots_shadow_safe_structural :
  forall env f R0 R_out roots,
    typed_fn_env_roots_shadow_safe env f R0 R_out roots ->
    typed_fn_env_structural env f.
Proof.
  intros env f R0 R_out roots Htyped.
  eapply typed_fn_env_roots_structural.
  eapply typed_fn_env_roots_shadow_safe_roots.
  exact Htyped.
Qed.

Lemma checked_fn_env_roots_shadow_safe_structural :
  forall env f R0 R_out roots,
    checked_fn_env_roots_shadow_safe env f R0 R_out roots ->
    checked_fn_env_structural env f.
Proof.
  unfold checked_fn_env_roots_shadow_safe, checked_fn_env_structural.
  intros env f R0 R_out roots [Htyped Hborrow].
  split.
  - eapply typed_fn_env_roots_shadow_safe_structural. exact Htyped.
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
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env_roots
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (fn_body_ctx f) (fn_body f))
    as [[[[T_body Γ_body] R_body] roots_body] | err] eqn:Hcore; try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompat; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_body) eqn:Hparams; try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ_out.
  repeat split.
  - exact (infer_core_env_roots_sound
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f)
      R0 (fn_body_ctx f) (fn_body f) T_body Γ_out R_out roots Hcore).
  - exact Hcompat.
  - exact Hparams.
Qed.

Theorem infer_env_roots_shadow_safe_sound :
  forall env f R0 T Γ_out R_out roots,
    infer_env_roots_shadow_safe env f R0 =
      infer_ok (T, Γ_out, R_out, roots) ->
    typed_fn_env_roots_shadow_safe env f R0 R_out roots.
Proof.
  unfold infer_env_roots_shadow_safe, typed_fn_env_roots_shadow_safe.
  intros env f R0 T Γ_out R_out roots Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try discriminate.
  destruct (infer_core_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f))
    as [[[[T_body Γ_body] R_body] roots_body] | err] eqn:Hcore;
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try discriminate.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f))
    eqn:Hcompat; try discriminate.
  destruct (params_ok_env_b env (fn_params f) Γ_body) eqn:Hparams;
    try discriminate.
  inversion Hinfer; subst.
  exists T_body, Γ_out.
  repeat split.
  - exact (infer_core_env_roots_shadow_safe_sound
      (global_env_with_local_bounds env (fn_bounds f))
      (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f)
      T_body Γ_out R_out roots Hcore).
  - exact Hcompat.
  - exact Hparams.
Qed.

Lemma infer_env_roots_shadow_safe_params_nodup :
  forall env f R0 T Γ' R' roots,
    infer_env_roots_shadow_safe env f R0 = infer_ok (T, Γ', R', roots) ->
    NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f R0 T Γ' R' roots Hinfer.
  unfold infer_env_roots_shadow_safe in Hinfer.
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

Lemma infer_env_roots_shadow_safe_binding_params_nodup :
  forall env f R0 T Γ' R' roots,
    infer_env_roots_shadow_safe env f R0 = infer_ok (T, Γ', R', roots) ->
    NoDup (ctx_names (params_ctx (fn_params f ++ fn_captures f))).
Proof.
  intros env f R0 T Γ' R' roots Hinfer.
  unfold infer_env_roots_shadow_safe in Hinfer.
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
  eapply duplicate_param_name_none_nodup_params_ctx. exact Hdup.
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
  destruct (borrow_check_env env [] (fn_body_ctx f) (fn_body f))
    as [PBS' | err] eqn:Hborrow; try discriminate.
  inversion Hfull; subst.
  split.
  - eapply infer_env_roots_sound. exact Hinfer.
  - split.
    + exists PBS'. eapply borrow_check_env_structural_sound. exact Hborrow.
    + eapply infer_env_roots_params_nodup. exact Hinfer.
Qed.
