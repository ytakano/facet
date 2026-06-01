From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export TypeSafety EnvRootSoundness.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma moved_path_satisfies_obligation_b_whole_path :
  forall moved_paths obligation,
    moved_path_satisfies_obligation_b ([] :: moved_paths) obligation = true.
Proof.
  intros moved_paths obligation. unfold moved_path_satisfies_obligation_b.
  simpl. reflexivity.
Qed.

Lemma moved_paths_satisfy_obligations_b_whole_path :
  forall moved_paths obligations,
    moved_paths_satisfy_obligations_b ([] :: moved_paths) obligations = true.
Proof.
  intros moved_paths obligations. induction obligations as [| obligation rest IH];
    simpl.
  - reflexivity.
  - exact IH.
Qed.

Lemma moved_paths_satisfy_prefix_obligations_b_whole_path :
  forall moved_paths prefix obligations,
    moved_paths_satisfy_obligations_b
      ([] :: moved_paths) (prefix_obligation_paths prefix obligations) = true.
Proof.
  intros moved_paths prefix obligations.
  apply moved_paths_satisfy_obligations_b_whole_path.
Qed.

Lemma path_prefix_b_nil_right_true :
  forall p,
    path_prefix_b p [] = true ->
    p = [].
Proof.
  intros p Hprefix. destruct p as [| x xs]; simpl in *; congruence.
Qed.

Lemma moved_path_satisfies_empty_obligation_in_whole :
  forall moved_paths,
    moved_path_satisfies_obligation_b moved_paths [] = true ->
    In [] moved_paths.
Proof.
  intros moved_paths. unfold moved_path_satisfies_obligation_b.
  induction moved_paths as [| moved rest IH]; simpl; intros Hsat;
    try discriminate.
  apply orb_true_iff in Hsat as [Hprefix | Hrest].
  - left. apply path_prefix_b_nil_right_true. exact Hprefix.
  - right. apply IH. exact Hrest.
Qed.

Lemma moved_path_satisfies_obligation_b_of_in_whole :
  forall moved_paths obligation,
    In [] moved_paths ->
    moved_path_satisfies_obligation_b moved_paths obligation = true.
Proof.
  intros moved_paths obligation Hin. unfold moved_path_satisfies_obligation_b.
  induction moved_paths as [| moved rest IH]; simpl in *; [contradiction |].
  destruct Hin as [Hwhole | Hin].
  - subst moved. reflexivity.
  - rewrite IH by exact Hin. destruct (path_prefix_b moved obligation); reflexivity.
Qed.

Lemma moved_paths_satisfy_obligations_b_of_in_whole :
  forall moved_paths obligations,
    In [] moved_paths ->
    moved_paths_satisfy_obligations_b moved_paths obligations = true.
Proof.
  intros moved_paths obligations Hin.
  induction obligations as [| obligation rest IH]; simpl; auto.
  rewrite moved_path_satisfies_obligation_b_of_in_whole by exact Hin.
  exact IH.
Qed.

Lemma moved_paths_satisfy_obligations_b_of_empty_obligation :
  forall moved_paths obligations,
    moved_paths_satisfy_obligations_b moved_paths [[]] = true ->
    moved_paths_satisfy_obligations_b moved_paths obligations = true.
Proof.
  intros moved_paths obligations Hempty. simpl in Hempty.
  apply andb_true_iff in Hempty as [Hsat _].
  apply moved_paths_satisfy_obligations_b_of_in_whole.
  apply moved_path_satisfies_empty_obligation_in_whole. exact Hsat.
Qed.

Lemma path_prefix_b_trans :
  forall p q r,
    path_prefix_b p q = true ->
    path_prefix_b q r = true ->
    path_prefix_b p r = true.
Proof.
  induction p as [| px ps IH]; intros q r Hpq Hqr; simpl in *; auto.
  destruct q as [| qx qs]; simpl in Hpq; try discriminate.
  destruct r as [| rx rs]; simpl in Hqr; try discriminate.
  apply andb_true_iff in Hpq as [Hpx Hpq].
  apply andb_true_iff in Hqr as [Hqx Hqr].
  apply String.eqb_eq in Hpx. subst qx.
  apply String.eqb_eq in Hqx. subst rx.
  simpl. rewrite String.eqb_refl. simpl.
  eapply IH; eassumption.
Qed.

Lemma moved_path_satisfies_obligation_b_prefix :
  forall moved_paths old_obligation new_obligation,
    path_prefix_b old_obligation new_obligation = true ->
    moved_path_satisfies_obligation_b moved_paths old_obligation = true ->
    moved_path_satisfies_obligation_b moved_paths new_obligation = true.
Proof.
  intros moved_paths old_obligation new_obligation Hprefix Hsat.
  unfold moved_path_satisfies_obligation_b in *.
  induction moved_paths as [| moved rest IH]; simpl in *; try discriminate.
  apply orb_true_iff in Hsat as [Hmoved | Hrest].
  - rewrite (path_prefix_b_trans moved old_obligation new_obligation Hmoved Hprefix).
    reflexivity.
  - rewrite (IH Hrest). destruct (path_prefix_b moved new_obligation); reflexivity.
Qed.

Definition obligation_refines (old_obligations new_obligations : list field_path) : Prop :=
  forall new_obligation,
    In new_obligation new_obligations ->
    exists old_obligation,
      In old_obligation old_obligations /\
      path_prefix_b old_obligation new_obligation = true.

Lemma moved_paths_satisfy_obligations_b_in :
  forall moved_paths obligations obligation,
    moved_paths_satisfy_obligations_b moved_paths obligations = true ->
    In obligation obligations ->
    moved_path_satisfies_obligation_b moved_paths obligation = true.
Proof.
  intros moved_paths obligations. induction obligations as [| obligation rest IH];
    intros target Hsat Hin; simpl in *; [contradiction |].
  apply andb_true_iff in Hsat as [Hhead Htail].
  destruct Hin as [Heq | Hin].
  - subst target. exact Hhead.
  - eapply IH; eassumption.
Qed.

Lemma moved_paths_satisfy_obligations_b_refines :
  forall moved_paths old_obligations new_obligations,
    obligation_refines old_obligations new_obligations ->
    moved_paths_satisfy_obligations_b moved_paths old_obligations = true ->
    moved_paths_satisfy_obligations_b moved_paths new_obligations = true.
Proof.
  intros moved_paths old_obligations new_obligations Hrefines Hsat_old.
  induction new_obligations as [| new_obligation rest IH]; simpl; auto.
  assert (Hin_head : In new_obligation (new_obligation :: rest)) by (left; reflexivity).
  destruct (Hrefines new_obligation Hin_head) as
    [old_obligation [Hin_old Hprefix]].
  assert (Hsat_old_obligation :
    moved_path_satisfies_obligation_b moved_paths old_obligation = true).
  { eapply moved_paths_satisfy_obligations_b_in; eassumption. }
  rewrite (moved_path_satisfies_obligation_b_prefix
    moved_paths old_obligation new_obligation Hprefix Hsat_old_obligation).
  apply IH. intros target Hin_target.
  apply Hrefines. right. exact Hin_target.
Qed.

Lemma path_prefix_b_refl :
  forall p,
    path_prefix_b p p = true.
Proof.
  induction p as [| x xs IH]; simpl; auto.
  rewrite String.eqb_refl. exact IH.
Qed.

Lemma path_prefix_b_app_same_prefix :
  forall prefix p q,
    path_prefix_b p q = true ->
    path_prefix_b (prefix ++ p) (prefix ++ q) = true.
Proof.
  induction prefix as [| x xs IH]; intros p q Hprefix; simpl; auto.
  rewrite String.eqb_refl. simpl. apply IH. exact Hprefix.
Qed.

Lemma prefix_obligation_paths_in :
  forall prefix obligations obligation,
    In obligation obligations ->
    In (prefix ++ obligation) (prefix_obligation_paths prefix obligations).
Proof.
  intros prefix obligations obligation Hin.
  induction obligations as [| head rest IH]; simpl in *; [contradiction |].
  destruct Hin as [Heq | Hin].
  - subst head. left. reflexivity.
  - right. apply IH. exact Hin.
Qed.

Lemma obligation_refines_refl :
  forall obligations,
    obligation_refines obligations obligations.
Proof.
  unfold obligation_refines. intros obligations obligation Hin.
  exists obligation. split; [exact Hin | apply path_prefix_b_refl].
Qed.

Lemma obligation_refines_app :
  forall old1 old2 new1 new2,
    obligation_refines old1 new1 ->
    obligation_refines old2 new2 ->
    obligation_refines (old1 ++ old2) (new1 ++ new2).
Proof.
  unfold obligation_refines.
  intros old1 old2 new1 new2 Href1 Href2 obligation Hin.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (Href1 obligation Hin) as [old [Hold Hprefix]].
    exists old. split; [apply in_app_iff; left; exact Hold | exact Hprefix].
  - destruct (Href2 obligation Hin) as [old [Hold Hprefix]].
    exists old. split; [apply in_app_iff; right; exact Hold | exact Hprefix].
Qed.

Lemma obligation_refines_prefix_obligation_paths :
  forall prefix old_obligations new_obligations,
    obligation_refines old_obligations new_obligations ->
    obligation_refines
      (prefix_obligation_paths prefix old_obligations)
      (prefix_obligation_paths prefix new_obligations).
Proof.
  unfold obligation_refines.
  intros prefix old_obligations new_obligations Hrefines target Hin.
  induction new_obligations as [| new_obligation rest IH]; simpl in Hin;
    [contradiction |].
  destruct Hin as [Htarget | Hin].
  - subst target.
    destruct (Hrefines new_obligation (or_introl eq_refl)) as
      [old_obligation [Hold Hprefix]].
    exists (prefix ++ old_obligation). split.
    + apply prefix_obligation_paths_in. exact Hold.
    + apply path_prefix_b_app_same_prefix. exact Hprefix.
  - apply IH.
    + intros target' Htarget'. apply Hrefines. right. exact Htarget'.
    + exact Hin.
Qed.

Lemma obligation_refines_nil_right :
  forall old_obligations,
    obligation_refines old_obligations [].
Proof.
  unfold obligation_refines. intros old_obligations target Hin. contradiction.
Qed.

Lemma obligation_refines_field_prefix_go :
  forall fields old_obligations_of new_obligations_of,
    (forall f,
      In f fields ->
      obligation_refines (old_obligations_of f) (new_obligations_of f)) ->
    obligation_refines
      ((fix go (fields : list field_def) : list field_path :=
          match fields with
          | [] => []
          | f :: rest =>
              prefix_obligation_paths [field_name f] (old_obligations_of f) ++
              go rest
          end) fields)
      ((fix go (fields : list field_def) : list field_path :=
          match fields with
          | [] => []
          | f :: rest =>
              prefix_obligation_paths [field_name f] (new_obligations_of f) ++
              go rest
          end) fields).
Proof.
  induction fields as [| f rest IH]; intros old_obligations_of new_obligations_of Hpoint;
    simpl.
  - apply obligation_refines_nil_right.
  - apply obligation_refines_app.
    + apply obligation_refines_prefix_obligation_paths.
      apply Hpoint. left. reflexivity.
    + apply IH. intros f' Hin. apply Hpoint. right. exact Hin.
Qed.

Lemma obligation_refines_singleton_empty_left :
  forall new_obligations,
    obligation_refines [[]] new_obligations.
Proof.
  unfold obligation_refines. intros new_obligations target Hin.
  exists []. split; [left; reflexivity | reflexivity].
Qed.

Lemma linear_obligation_paths_fuel_subst_tparam_refines :
  forall fuel env type_args u i,
    obligation_refines
      (linear_obligation_paths_fuel fuel env (MkTy u (TParam i)))
      (linear_obligation_paths_fuel fuel env
        (subst_type_params_ty type_args (MkTy u (TParam i)))).
Proof.
  intros fuel env type_args u i. destruct u; destruct fuel;
    cbn [linear_obligation_paths_fuel subst_type_params_ty ty_usage ty_core].
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core].
    + apply obligation_refines_singleton_empty_left.
    + apply obligation_refines_refl.
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core].
    + apply obligation_refines_singleton_empty_left.
    + apply obligation_refines_refl.
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core];
      apply obligation_refines_nil_right.
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core];
      apply obligation_refines_nil_right.
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core];
      apply obligation_refines_nil_right.
  - destruct (nth_error type_args i) as [[u' core] |];
      cbn [linear_obligation_paths_fuel ty_usage ty_core];
      apply obligation_refines_nil_right.
Qed.

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
