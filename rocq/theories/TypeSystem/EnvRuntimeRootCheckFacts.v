From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export TypeSafety EnvRootSoundness.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma linear_obligation_paths_fuel_global_env_with_local_bounds :
  forall fuel env bounds T,
    linear_obligation_paths_fuel fuel
      (global_env_with_local_bounds env bounds) T =
    linear_obligation_paths_fuel fuel env T.
Proof.
  induction fuel as [| fuel IH]; intros env bounds T.
  - destruct T as [u core]. destruct u; destruct core; reflexivity.
  - destruct T as [u core]. destruct u; try reflexivity.
    destruct core; try reflexivity.
    simpl.
    change (lookup_struct s (global_env_with_local_bounds env bounds))
      with (lookup_struct s env).
    destruct (lookup_struct s env) as [sdef |]; [| reflexivity].
    destruct (Nat.eqb (Datatypes.length l) (struct_lifetimes sdef) &&
      Nat.eqb (Datatypes.length l0) (struct_type_params sdef));
      [| reflexivity].
    assert (Hgo :
      (fix go (fields : list field_def) : list field_path :=
        match fields with
        | [] => []
        | f :: rest =>
            prefix_obligation_paths [field_name f]
              (linear_obligation_paths_fuel fuel
                (global_env_with_local_bounds env bounds)
                (instantiate_struct_field_ty l l0 f)) ++ go rest
        end) (struct_fields sdef) =
      (fix go (fields : list field_def) : list field_path :=
        match fields with
        | [] => []
        | f :: rest =>
            prefix_obligation_paths [field_name f]
              (linear_obligation_paths_fuel fuel env
                (instantiate_struct_field_ty l l0 f)) ++ go rest
        end) (struct_fields sdef)).
    { induction (struct_fields sdef) as [| f fields IHfields]; simpl.
      - reflexivity.
      - rewrite IH. rewrite IHfields. reflexivity. }
    rewrite Hgo. reflexivity.
Qed.

Lemma linear_obligation_paths_global_env_with_local_bounds :
  forall env bounds T,
    linear_obligation_paths (global_env_with_local_bounds env bounds) T =
    linear_obligation_paths env T.
Proof.
  intros env bounds T.
  unfold linear_obligation_paths.
  change (Datatypes.length (env_structs (global_env_with_local_bounds env bounds)))
    with (Datatypes.length (env_structs env)).
  apply linear_obligation_paths_fuel_global_env_with_local_bounds.
Qed.

Lemma sctx_check_ok_global_env_with_local_bounds :
  forall env bounds x T Σ,
    sctx_check_ok (global_env_with_local_bounds env bounds) x T Σ =
    sctx_check_ok env x T Σ.
Proof.
  intros env bounds x T Σ.
  unfold sctx_check_ok, linear_scope_ok_b.
  destruct (ty_usage T); try reflexivity.
  destruct (sctx_lookup x Σ) as [[T0 st] |]; try reflexivity.
  rewrite linear_obligation_paths_global_env_with_local_bounds.
  reflexivity.
Qed.

Lemma params_ok_sctx_b_global_env_with_local_bounds :
  forall ps env bounds Σ,
    params_ok_sctx_b (global_env_with_local_bounds env bounds) ps Σ =
    params_ok_sctx_b env ps Σ.
Proof.
  induction ps as [| p ps IH]; intros env bounds Σ; simpl; auto.
  rewrite sctx_check_ok_global_env_with_local_bounds.
  rewrite IH. reflexivity.
Qed.

Lemma params_ok_env_b_global_env_with_local_bounds :
  forall env bounds ps Γ,
    params_ok_env_b (global_env_with_local_bounds env bounds) ps Γ =
    params_ok_env_b env ps Γ.
Proof.
  intros env bounds ps Γ.
  unfold params_ok_env_b.
  apply params_ok_sctx_b_global_env_with_local_bounds.
Qed.

Lemma infer_env_roots_global_env_with_local_bounds :
  forall env bounds f R0,
    infer_env_roots (global_env_with_local_bounds env bounds) f R0 =
    infer_env_roots env f R0.
Proof.
  intros env bounds f R0.
  unfold infer_env_roots. simpl.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f))
             (fn_outlives f))); try reflexivity.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try reflexivity.
  destruct (check_fn_binding_params (mk_region_ctx (fn_lifetimes f)) f);
    try reflexivity.
  change (global_env_with_local_bounds
    (global_env_with_local_bounds env bounds) (fn_bounds f))
    with (global_env_with_local_bounds env (fn_bounds f)).
  destruct (infer_core_env_roots
    (global_env_with_local_bounds env (fn_bounds f))
    (fn_outlives f) (fn_lifetimes f) R0 (fn_body_ctx f) (fn_body f))
    as [[[[T_body Γ_out] R_out] roots] | err]; try reflexivity.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body));
    try reflexivity.
  destruct (ty_compatible_b (fn_outlives f) T_body (fn_ret f));
    try reflexivity.
  rewrite (params_ok_env_b_global_env_with_local_bounds
    env bounds (fn_params f) Γ_out).
  reflexivity.
Qed.

Definition callee_body_root_check_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    infer_env_roots env fcall R_params =
      infer_ok (T_body, Γ_out, R_body, roots_body) /\
    preservation_ready_expr (fn_body fcall) /\
    roots_exclude_params_b (fn_params fcall) roots_body = true /\
    root_env_excludes_params_b (fn_params fcall) R_body = true.

Definition direct_call_callee_body_root_check_evidence
    (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    root_env_store_roots_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_check_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Lemma callee_body_root_ready_at_of_check_ready_at :
  forall env fcall R_params,
    callee_body_root_check_ready_at env fcall R_params ->
    callee_body_root_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hcheck.
  unfold callee_body_root_check_ready_at in Hcheck.
  destruct Hcheck as
    (T_body & Γ_out & R_body & roots_body &
      Hinfer & Hready & Hexclude_roots & Hexclude_env).
  pose proof (infer_env_roots_sound env fcall R_params T_body Γ_out
    R_body roots_body Hinfer) as Htyped_fn.
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as
    (T_body' & Γ_out' & Htyped & Hcompat & _).
  unfold callee_body_root_ready_at.
  exists T_body', Γ_out', R_body, roots_body.
  repeat split.
  - apply preservation_ready_implies_provenance_ready.
    exact Hready.
  - exact Hready.
  - exact Htyped.
  - exact Hcompat.
  - apply roots_exclude_params_b_sound.
    exact Hexclude_roots.
  - apply root_env_excludes_params_b_sound.
    exact Hexclude_env.
Qed.

Definition fn_root_summary_check_ready
    (env : global_env) (fdef : fn_def) : Prop :=
  exists T_body Γ_out R_body roots_body,
    infer_env_roots env fdef (initial_root_env_for_fn fdef) =
      infer_ok (T_body, Γ_out, R_body, roots_body) /\
    preservation_ready_expr (fn_body fdef) /\
    roots_exclude_params_b (fn_params fdef) roots_body = true /\
    root_env_excludes_params_b (fn_params fdef) R_body = true.

Definition env_fns_root_summary_check_ready (env : global_env) : Prop :=
  forall fdef,
    In fdef (env_fns env) ->
    fn_root_summary_check_ready env fdef.

Definition direct_call_callee_body_root_check_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_summary_check_ready env ->
  direct_call_callee_body_root_check_evidence env.

Lemma fn_root_summary_check_ready_global_env_with_local_bounds :
  forall env bounds fdef,
    fn_root_summary_check_ready env fdef ->
    fn_root_summary_check_ready
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef Hsummary.
  unfold fn_root_summary_check_ready in *.
  destruct Hsummary as
    (T_body & Γ_out & R_body & roots_body &
      Hinfer & Hready & Hexclude_roots & Hexclude_env).
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  rewrite infer_env_roots_global_env_with_local_bounds.
  exact Hinfer.
Qed.

Lemma env_fns_root_summary_check_ready_global_env_with_local_bounds :
  forall env bounds,
    env_fns_root_summary_check_ready env ->
    env_fns_root_summary_check_ready
      (global_env_with_local_bounds env bounds).
Proof.
  intros env bounds Hsummary fdef Hin.
  simpl in Hin.
  apply fn_root_summary_check_ready_global_env_with_local_bounds.
  exact (Hsummary fdef Hin).
Qed.

Lemma callee_body_root_ready_at_of_fn_root_summary_check :
  forall env fdef,
    fn_root_summary_check_ready env fdef ->
    callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).
Proof.
  intros env fdef Hsummary.
  unfold fn_root_summary_check_ready in Hsummary.
  destruct Hsummary as
    (T_body & Γ_out & R_body & roots_body &
      Hinfer & Hready & Hexclude_roots & Hexclude_env).
  apply callee_body_root_ready_at_of_check_ready_at.
  unfold callee_body_root_check_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_ready_at_of_env_root_summary_check :
  forall env fdef,
    env_fns_root_summary_check_ready env ->
    In fdef (env_fns env) ->
    callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).
Proof.
  intros env fdef Hsummary Hin.
  apply callee_body_root_ready_at_of_fn_root_summary_check.
  exact (Hsummary fdef Hin).
Qed.

Lemma env_fns_root_summary_evidence_of_check :
  forall env,
    env_fns_root_summary_check_ready env ->
    env_fns_root_summary_evidence env.
Proof.
  intros env Hsummary fname fdef Hlookup.
  unfold env_fns_root_summary_evidence, callee_body_root_summary.
  apply callee_body_root_ready_at_of_env_root_summary_check.
  - exact Hsummary.
  - apply lookup_fn_in_name in Hlookup.
    exact (proj1 Hlookup).
Qed.

Lemma direct_call_callee_body_root_evidence_of_check :
  forall env,
    direct_call_callee_body_root_check_evidence env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hcheck Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall
    σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  apply callee_body_root_ready_at_of_check_ready_at.
  eapply Hcheck; eassumption.
Qed.
