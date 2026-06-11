From Facet.TypeSystem Require Import
  Lifetime Types Syntax Program TypingRules TypeChecker EnvStructuralRules
  EnvTypingSoundness AssocCompatibility AssocEnvStructural CheckerHrt.
From Stdlib Require Import Bool List String.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Assoc-aware env argument collector soundness                         *)
(* ------------------------------------------------------------------ *)

Lemma infer_env_args_collect_assoc_checked_sound :
  forall fuel env Ω n Σ args arg_tys params Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T, Σ1) ->
        typed_env_structural env Ω n Σ0 e T Σ1) ->
    check_args_assoc env Ω arg_tys params = None ->
    typed_args_env_structural_assoc env Ω n Σ args params Σ'.
Proof.
  intros fuel env Ω n Σ args.
  revert Σ.
  induction args as [|e rest IH]; intros Σ arg_tys params Σ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e) as [[T_e Σ1] | err] eqn:He;
      try discriminate.
    destruct (infer_env_args_collect fuel env Ω n Σ1 rest) as [[tys Σ2] | err'] eqn:Htail;
      try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_e (param_ty p)) eqn:Hcompat;
      try discriminate.
    eapply TESArgsAssoc_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * intros Σ0 e0 T0 Σ0' Hin Hinfer0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hinfer0.
      * exact Hcheck.
Qed.

Fixpoint infer_env_enum_payloads_collect_assoc fuel env Ω n lts variant_lts args
    (Σ : sctx) (fields : list Ty) (payloads : list expr)
    : infer_result sctx :=
  match fields, payloads with
  | [], [] => infer_ok Σ
  | T_field :: fields, e_payload :: payloads =>
      match infer_core_env_state_fuel fuel env Ω n Σ e_payload with
      | infer_err err => infer_err err
      | infer_ok (T_payload, Σ1) =>
          let T_expected := instantiate_enum_variant_field_ty lts variant_lts args T_field in
          if ty_compatible_assoc_b env Ω T_payload T_expected
          then infer_env_enum_payloads_collect_assoc fuel env Ω n lts variant_lts args
                 Σ1 fields payloads
          else infer_err (compatible_error T_payload T_expected)
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Lemma infer_env_enum_payloads_collect_assoc_eq :
  forall fuel env Ω n lts variant_lts args fields payloads Σ,
    (fix go (Σ0 : sctx) (fields0 : list Ty) (es : list expr)
        : infer_result sctx :=
       match fields0, es with
       | [], [] => infer_ok Σ0
       | T_field :: fields', e_payload :: es' =>
           match infer_core_env_state_fuel fuel env Ω n Σ0 e_payload with
           | infer_err err => infer_err err
           | infer_ok (T_payload, Σ1) =>
               let T_expected :=
                 instantiate_enum_variant_field_ty lts variant_lts args T_field in
               if ty_compatible_assoc_b env Ω T_payload T_expected
               then go Σ1 fields' es'
               else infer_err (compatible_error T_payload T_expected)
           end
       | _, _ => infer_err ErrArityMismatch
       end) Σ fields payloads =
    infer_env_enum_payloads_collect_assoc
      fuel env Ω n lts variant_lts args Σ fields payloads.
Proof.
  intros fuel env Ω n lts variant_lts args fields.
  induction fields as [|T_field rest IH]; intros payloads Σ;
    destruct payloads as [|e_payload es]; simpl; try reflexivity.
  destruct (infer_core_env_state_fuel fuel env Ω n Σ e_payload)
    as [[T_payload Σ1] | err] eqn:Hpayload; try reflexivity.
  destruct (ty_compatible_assoc_b env Ω T_payload
    (instantiate_enum_variant_field_ty lts variant_lts args T_field));
    [rewrite IH |]; reflexivity.
Qed.

Lemma infer_env_enum_payloads_collect_assoc_checked_sound :
  forall fuel env Ω n lts variant_lts args Sigma fields payloads Sigma_out,
    forallb struct_expr payloads = true ->
    infer_env_enum_payloads_collect_assoc fuel env Ω n lts variant_lts args Sigma fields payloads =
      infer_ok Sigma_out ->
    (forall Sigma0 e T Sigma1,
        struct_expr e = true ->
        infer_core_env_state_fuel fuel env Ω n Sigma0 e = infer_ok (T, Sigma1) ->
        typed_env_structural env Ω n Sigma0 e T Sigma1) ->
    typed_args_env_structural_assoc env Ω n Sigma payloads
      (params_of_tys (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Sigma_out.
Proof.
  intros fuel env Ω n lts variant_lts args Sigma fields.
  revert Sigma.
  induction fields as [|T_field rest IH]; intros Sigma payloads Sigma_out Hpayloads Hcollect Hexpr;
    destruct payloads as [|e_payload payloads]; simpl in *; try discriminate.
  - inversion Hcollect; subst. constructor.
  - apply andb_true_iff in Hpayloads as [Hpayload Hpayloads].
    destruct (infer_core_env_state_fuel fuel env Ω n Sigma e_payload)
      as [[T_payload Sigma1] | err] eqn:Hp; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_payload
      (instantiate_enum_variant_field_ty lts variant_lts args T_field)) eqn:Hcompat;
      try discriminate.
    eapply TESArgsAssoc_Cons.
    + eapply Hexpr; eassumption.
    + exact Hcompat.
    + eapply IH; eassumption.
Qed.

Lemma infer_env_enum_payloads_collect_assoc_checked_call_sound :
  forall fuel env Ω n lts variant_lts args Sigma fields payloads Sigma_out,
    forallb call_expr payloads = true ->
    infer_env_enum_payloads_collect_assoc fuel env Ω n lts variant_lts args Sigma fields payloads =
      infer_ok Sigma_out ->
    (forall Sigma0 e T Sigma1,
        call_expr e = true ->
        infer_core_env_state_fuel fuel env Ω n Sigma0 e = infer_ok (T, Sigma1) ->
        typed_env_structural env Ω n Sigma0 e T Sigma1) ->
    typed_args_env_structural_assoc env Ω n Sigma payloads
      (params_of_tys (map (instantiate_enum_variant_field_ty lts variant_lts args) fields)) Sigma_out.
Proof.
  intros fuel env Ω n lts variant_lts args Sigma fields.
  revert Sigma.
  induction fields as [|T_field rest IH]; intros Sigma payloads Sigma_out Hpayloads Hcollect Hexpr;
    destruct payloads as [|e_payload payloads]; simpl in *; try discriminate.
  - inversion Hcollect; subst. constructor.
  - apply andb_true_iff in Hpayloads as [Hpayload Hpayloads].
    destruct (infer_core_env_state_fuel fuel env Ω n Sigma e_payload)
      as [[T_payload Sigma1] | err] eqn:Hp; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_payload
      (instantiate_enum_variant_field_ty lts variant_lts args T_field)) eqn:Hcompat;
      try discriminate.
    eapply TESArgsAssoc_Cons.
    + eapply Hexpr; eassumption.
    + exact Hcompat.
    + eapply IH; eassumption.
Qed.

Fixpoint infer_env_fields_collect_assoc fuel env Ω n lts args
    (Sigma : sctx) (fields : list (string * expr)) (defs : list field_def)
    : infer_result sctx :=
  match defs with
  | [] => infer_ok Sigma
  | f :: rest =>
      match lookup_field_b (field_name f) fields with
      | None => infer_err (ErrMissingField (field_name f))
      | Some e_field =>
          match infer_core_env_state_fuel fuel env Ω n Sigma e_field with
          | infer_err err => infer_err err
          | infer_ok (T_field, Sigma1) =>
              let T_expected := instantiate_struct_field_ty lts args f in
              if ty_compatible_assoc_b env Ω T_field T_expected
              then infer_env_fields_collect_assoc fuel env Ω n lts args
                     Sigma1 fields rest
              else infer_err (compatible_error T_field T_expected)
          end
      end
  end.

Lemma infer_env_fields_collect_assoc_eq :
  forall fuel env Ω n lts args fields defs Σ,
    (fix go (Σ0 : sctx) (defs0 : list field_def) : infer_result sctx :=
       match defs0 with
       | [] => infer_ok Σ0
       | f :: rest =>
           match lookup_field_b (field_name f) fields with
           | None => infer_err (ErrMissingField (field_name f))
           | Some e_field =>
               match infer_core_env_state_fuel fuel env Ω n Σ0 e_field with
               | infer_err err => infer_err err
               | infer_ok (T_field, Σ1) =>
                   let T_expected := instantiate_struct_field_ty lts args f in
                   if ty_compatible_assoc_b env Ω T_field T_expected
                   then go Σ1 rest
                   else infer_err (compatible_error T_field T_expected)
               end
           end
       end) Σ defs =
    infer_env_fields_collect_assoc fuel env Ω n lts args Σ fields defs.
Proof.
  intros fuel env Ω n lts args fields defs.
  induction defs as [|f rest IH]; intros Σ; simpl.
  - reflexivity.
  - destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try reflexivity.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e_field)
      as [[T_field Σ1] | err] eqn:Hfield; try reflexivity.
    destruct (ty_compatible_assoc_b env Ω T_field
      (instantiate_struct_field_ty lts args f)); [rewrite IH |]; reflexivity.
Qed.

Lemma infer_env_fields_collect_assoc_checked_sound :
  forall fuel env Ω n lts args Sigma fields defs Sigma_out,
    forallb (fun '(_, e_field) => struct_expr e_field) fields = true ->
    infer_env_fields_collect_assoc fuel env Ω n lts args Sigma fields defs =
      infer_ok Sigma_out ->
    (forall Sigma0 e T Sigma1,
        struct_expr e = true ->
        infer_core_env_state_fuel fuel env Ω n Sigma0 e =
          infer_ok (T, Sigma1) ->
        typed_env_structural env Ω n Sigma0 e T Sigma1) ->
    typed_fields_env_structural_assoc env Ω n lts args Sigma fields defs
      Sigma_out.
Proof.
  intros fuel env Ω n lts args Sigma fields defs.
  revert Sigma.
  induction defs as [|f rest IH]; intros Sigma Sigma_out Hfields Hcollect Hexpr;
    simpl in Hcollect.
  - inversion Hcollect; subst. constructor.
  - destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try discriminate.
    destruct (infer_core_env_state_fuel fuel env Ω n Sigma e_field)
      as [[T_field Sigma1] | err] eqn:Hfield; try discriminate.
    destruct (ty_compatible_assoc_b env Ω T_field
      (instantiate_struct_field_ty lts args f)) eqn:Hcompat; try discriminate.
    eapply TESFieldsAssoc_Cons.
    + exact Hlookup.
    + eapply Hexpr.
      * eapply lookup_field_b_struct_expr_true; eassumption.
      * exact Hfield.
    + exact Hcompat.
    + eapply IH.
      * exact Hfields.
      * exact Hcollect.
      * exact Hexpr.
Qed.
