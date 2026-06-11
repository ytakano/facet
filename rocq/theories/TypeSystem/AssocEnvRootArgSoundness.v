From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker RootProvenance
  EnvStructuralRules EnvRootSoundness AssocCompatibility AssocEnvStructural
  CheckerHrt.
From Stdlib Require Import List String.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware roots argument collector soundness                       *)
(* ------------------------------------------------------------------ *)

Lemma infer_env_args_collect_roots_assoc_checked_sound :
  forall fuel env Ω n R Σ args arg_tys params Σ' R' arg_roots,
    infer_env_args_collect_roots fuel env Ω n R Σ args =
      infer_ok (arg_tys, Σ', R', arg_roots) ->
    (forall R0 Σ0 e T Σ1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Σ0 e =
          infer_ok (T, Σ1, R1, roots1) ->
        typed_env_roots env Ω n R0 Σ0 e T Σ1 R1 roots1) ->
    check_args_assoc env Ω arg_tys params = None ->
    typed_args_roots_assoc env Ω n R Σ args params Σ' R' arg_roots.
Proof.
  intros fuel env Ω n R Σ args.
  revert R Σ.
  induction args as [|e rest IH]; intros R Σ arg_tys params Σ' R' arg_roots
      Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e)
      as [[[[T_e Σ1] R1] roots_e] | err] eqn:He; try discriminate.
    destruct (infer_env_args_collect_roots fuel env Ω n R1 Σ1 rest)
      as [[[[tys Σ2] R2] roots_rest] | err] eqn:Htail; try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_e (param_ty p)) eqn:Hcompat;
      try discriminate.
    eapply TERArgsAssoc_Cons.
    + eapply Hexpr. exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * exact Hexpr.
      * exact Hcheck.
Qed.

Fixpoint infer_env_enum_payloads_collect_roots_assoc fuel env Ω n lts variant_lts args
    (R : root_env) (Σ : sctx) (fields : list Ty) (payloads : list expr)
    : infer_result (sctx * root_env * root_set) :=
  match fields, payloads with
  | [], [] => infer_ok (Σ, R, [])
  | T_field :: fields, e_payload :: payloads =>
      match infer_core_env_state_fuel_roots fuel env Ω n R Σ e_payload with
      | infer_err err => infer_err err
      | infer_ok (T_payload, Σ1, R1, roots_payload) =>
          let T_expected := instantiate_enum_variant_field_ty lts variant_lts args T_field in
          if ty_compatible_assoc_b env Ω T_payload T_expected
          then
            match infer_env_enum_payloads_collect_roots_assoc fuel env Ω n lts variant_lts args
                    R1 Σ1 fields payloads with
            | infer_err err => infer_err err
            | infer_ok (Σ2, R2, roots_rest) =>
                infer_ok (Σ2, R2, root_set_union roots_payload roots_rest)
            end
          else infer_err (compatible_error T_payload T_expected)
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Lemma infer_env_enum_payloads_collect_roots_assoc_eq :
  forall fuel env Ω n lts variant_lts args fields payloads R Σ,
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
                 instantiate_enum_variant_field_ty lts variant_lts args T_field in
               if ty_compatible_assoc_b env Ω T_payload T_expected
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
    infer_env_enum_payloads_collect_roots_assoc
      fuel env Ω n lts variant_lts args R Σ fields payloads.
Proof.
  intros fuel env Ω n lts variant_lts args fields.
  induction fields as [|T_field rest IH]; intros payloads R Σ;
    destruct payloads as [|e_payload payloads']; simpl; try reflexivity.
  destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_payload)
    as [[[[T_payload Σ1] R1] roots_payload] | err] eqn:Hpayload;
    try reflexivity.
  destruct (ty_compatible_assoc_b env Ω T_payload
    (instantiate_enum_variant_field_ty lts variant_lts args T_field)); try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_enum_payloads_collect_roots_assoc_checked_sound :
  forall fuel env Ω n lts variant_lts args R Sigma fields payloads Sigma_out R_out roots,
    infer_env_enum_payloads_collect_roots_assoc fuel env Ω n lts variant_lts args R Sigma fields payloads =
      infer_ok (Sigma_out, R_out, roots) ->
    (forall R0 Sigma0 e T Sigma1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Sigma0 e =
          infer_ok (T, Sigma1, R1, roots1) ->
        typed_env_roots env Ω n R0 Sigma0 e T Sigma1 R1 roots1) ->
    exists payload_roots,
      typed_args_roots_assoc env Ω n R Sigma payloads
        (params_of_tys
          (map (instantiate_enum_variant_field_ty lts variant_lts args) fields))
        Sigma_out R_out payload_roots /\
      roots = root_sets_union payload_roots.
Proof.
  intros fuel env Ω n lts variant_lts args R Sigma fields.
  revert R Sigma.
  induction fields as [|T_field rest IH]; intros R Sigma payloads Sigma_out R_out roots Hcollect Hexpr;
    destruct payloads as [|e_payload payloads]; simpl in Hcollect; try discriminate.
  - inversion Hcollect; subst. exists []. split; [constructor | reflexivity].
  - destruct (infer_core_env_state_fuel_roots fuel env Ω n R Sigma e_payload)
      as [[[[T_payload Sigma1] R1] roots_payload] | err] eqn:Hp; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_payload
      (instantiate_enum_variant_field_ty lts variant_lts args T_field)) eqn:Hcompat;
      try discriminate.
    destruct (infer_env_enum_payloads_collect_roots_assoc fuel env Ω n lts variant_lts args
      R1 Sigma1 rest payloads) as [[[Sigma2 R2] roots_rest] | err] eqn:Hrest;
      try discriminate.
    inversion Hcollect; subst.
    destruct (IH R1 Sigma1 payloads Sigma_out R_out roots_rest Hrest Hexpr)
      as [payload_roots [Hpayload_roots Hroots_rest]].
    exists (roots_payload :: payload_roots). split.
    + eapply TERArgsAssoc_Cons.
      * eapply Hexpr. exact Hp.
      * exact Hcompat.
      * exact Hpayload_roots.
    + simpl. rewrite Hroots_rest. reflexivity.
Qed.

Fixpoint infer_env_fields_collect_roots_assoc fuel env Ω n lts args
    (R : root_env) (Sigma : sctx) (fields : list (string * expr))
    (defs : list field_def)
    : infer_result (sctx * root_env * root_set) :=
  match defs with
  | [] => infer_ok (Sigma, R, [])
  | f :: rest =>
      match lookup_field_b (field_name f) fields with
      | None => infer_err (ErrMissingField (field_name f))
      | Some e_field =>
          match infer_core_env_state_fuel_roots fuel env Ω n R Sigma e_field with
          | infer_err err => infer_err err
          | infer_ok (T_field, Sigma1, R1, roots_field) =>
              let T_expected := instantiate_struct_field_ty lts args f in
              if ty_compatible_assoc_b env Ω T_field T_expected
              then
                match infer_env_fields_collect_roots_assoc fuel env Ω n lts args
                        R1 Sigma1 fields rest with
                | infer_err err => infer_err err
                | infer_ok (Sigma2, R2, roots_rest) =>
                    infer_ok (Sigma2, R2, root_set_union roots_field roots_rest)
                end
              else infer_err (compatible_error T_field T_expected)
          end
      end
  end.

Lemma infer_env_fields_collect_roots_assoc_eq :
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
                   if ty_compatible_assoc_b env Ω T_field T_expected
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
    infer_env_fields_collect_roots_assoc
      fuel env Ω n lts args R Σ fields defs.
Proof.
  intros fuel env Ω n lts args fields defs.
  induction defs as [|f rest IH]; intros R Σ; simpl; try reflexivity.
  destruct (lookup_field_b (field_name f) fields) as [e_field |];
    try reflexivity.
  destruct (infer_core_env_state_fuel_roots fuel env Ω n R Σ e_field)
    as [[[[T_field Σ1] R1] roots_field] | err]; try reflexivity.
  destruct (ty_compatible_assoc_b env Ω T_field
    (instantiate_struct_field_ty lts args f)); try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma infer_env_fields_collect_roots_assoc_checked_sound :
  forall fuel env Ω n lts args R Sigma fields defs Sigma_out R_out roots,
    infer_env_fields_collect_roots_assoc fuel env Ω n lts args R Sigma fields defs =
      infer_ok (Sigma_out, R_out, roots) ->
    (forall R0 Sigma0 e T Sigma1 R1 roots1,
        infer_core_env_state_fuel_roots fuel env Ω n R0 Sigma0 e =
          infer_ok (T, Sigma1, R1, roots1) ->
        typed_env_roots env Ω n R0 Sigma0 e T Sigma1 R1 roots1) ->
    typed_fields_roots_assoc env Ω n lts args R Sigma fields defs
      Sigma_out R_out roots.
Proof.
  intros fuel env Ω n lts args R Sigma fields defs.
  revert R Sigma.
  induction defs as [|f rest IH]; intros R Sigma Sigma_out R_out roots Hcollect Hexpr.
  - simpl in Hcollect. inversion Hcollect; subst. constructor.
  - simpl in Hcollect.
    destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try discriminate.
    destruct (infer_core_env_state_fuel_roots fuel env Ω n R Sigma e_field)
      as [[[[T_field Sigma1] R1] roots_field] | err] eqn:Hfield; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_field
      (instantiate_struct_field_ty lts args f)) eqn:Hcompat; try discriminate.
    destruct (infer_env_fields_collect_roots_assoc fuel env Ω n lts args
      R1 Sigma1 fields rest) as [[[Sigma2 R2] roots_rest] | err] eqn:Hrest;
      try discriminate.
    inversion Hcollect; subst.
    eapply TERFieldsAssoc_Cons.
    + exact Hlookup.
    + eapply Hexpr. exact Hfield.
    + exact Hcompat.
    + eapply IH.
      * exact Hrest.
      * intros R0 Sigma0 e0 T0 Sigma0' R0' roots0 Hinfer.
        eapply Hexpr. exact Hinfer.
Qed.
