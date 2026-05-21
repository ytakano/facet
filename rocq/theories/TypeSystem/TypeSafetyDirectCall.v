From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosure.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Function environment lookup facts                                   *)
(* ------------------------------------------------------------------ *)

Lemma lookup_fn_typed_structural :
  forall env fname f_lookup,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    env_fns_typed_structural env ->
    typed_fn_env_structural env f_lookup.
Proof.
  intros env fname f_lookup Hlookup Henv_typed.
  destruct (lookup_fn_in_name fname (env_fns env) f_lookup Hlookup)
    as [Hin_lookup _].
  apply Henv_typed. exact Hin_lookup.
Qed.

Lemma fn_body_ctx_eq_params_ctx_when_no_captures :
  forall f,
    fn_captures f = [] ->
    fn_body_ctx f = params_ctx (fn_params f).
Proof.
  intros f Hcaps.
  unfold fn_body_ctx, fn_body_params.
  rewrite Hcaps.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures :
  forall env Ω n R f e T Σ' R' roots,
    fn_captures f = [] ->
    typed_env_roots env Ω n R (sctx_of_ctx (fn_body_ctx f))
      e T Σ' R' roots ->
    typed_env_roots env Ω n R (sctx_of_ctx (params_ctx (fn_params f)))
      e T Σ' R' roots.
Proof.
  intros env Ω n R f e T Σ' R' roots Hcaps Htyped.
  rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures f Hcaps).
  exact Htyped.
Qed.

Lemma typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures :
  forall env Ω n R f e T Σ' R' roots,
    fn_captures f = [] ->
    typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx (fn_body_ctx f))
      e T Σ' R' roots ->
    typed_env_roots_shadow_safe env Ω n R
      (sctx_of_ctx (params_ctx (fn_params f))) e T Σ' R' roots.
Proof.
  intros env Ω n R f e T Σ' R' roots Hcaps Htyped.
  rewrite <- (fn_body_ctx_eq_params_ctx_when_no_captures f Hcaps).
  exact Htyped.
Qed.

Lemma NoDup_map_eq :
  forall (A B : Type) (f : A -> B) (xs : list A) x y,
    NoDup (map f xs) ->
    In x xs ->
    In y xs ->
    f x = f y ->
    x = y.
Proof.
  intros A B f xs.
  induction xs as [| z zs IH]; intros x y Hnodup Hinx Hiny Heq.
  - contradiction.
  - simpl in Hnodup. inversion Hnodup; subst.
    simpl in Hinx, Hiny.
    destruct Hinx as [Hx | Hinx]; destruct Hiny as [Hy | Hiny].
    + subst. reflexivity.
    + subst x.
      exfalso. apply H1.
      rewrite Heq. apply in_map. exact Hiny.
    + subst y.
      exfalso. apply H1.
      rewrite <- Heq. apply in_map. exact Hinx.
    + eapply IH; eassumption.
Qed.

Definition fn_env_unique_by_name (env : global_env) : Prop :=
  forall f1 f2,
    In f1 (env_fns env) ->
    In f2 (env_fns env) ->
    fn_name f1 = fn_name f2 ->
    f1 = f2.

Lemma fn_name_strings_nodup_unique_by_name :
  forall env,
    NoDup (fn_name_strings (env_fns env)) ->
    fn_env_unique_by_name env.
Proof.
  unfold fn_env_unique_by_name, fn_name_strings.
  intros env Hnodup f1 f2 Hin1 Hin2 Hname.
  eapply (NoDup_map_eq fn_def string
    (fun f => fst (fn_name f)) (env_fns env) f1 f2);
    try eassumption.
  simpl. rewrite Hname. reflexivity.
Qed.

Lemma top_level_names_unique_b_fn_env_unique_by_name :
  forall env,
    top_level_names_unique_b env = true ->
    fn_env_unique_by_name env.
Proof.
  intros env Hunique.
  apply fn_name_strings_nodup_unique_by_name.
  apply top_level_names_unique_b_fn_names_nodup.
  exact Hunique.
Qed.

Lemma lookup_fn_unique_by_name :
  forall env fname f_lookup f_typed,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    In f_typed (env_fns env) ->
    fn_name f_typed = fname ->
    fn_env_unique_by_name env ->
    f_lookup = f_typed.
Proof.
  intros env fname f_lookup f_typed Hlookup Hin_typed Hname_typed Hunique.
  destruct (lookup_fn_in_name fname (env_fns env) f_lookup Hlookup)
    as [Hin_lookup Hname_lookup].
  apply Hunique; try assumption.
  rewrite Hname_lookup. symmetry. exact Hname_typed.
Qed.

Lemma lookup_fn_none_not_in_name :
  forall fname fenv fdef,
    lookup_fn fname fenv = None ->
    In fdef fenv ->
    fn_name fdef <> fname.
Proof.
  intros fname fenv.
  induction fenv as [| f rest IH]; intros fdef Hlookup Hin; simpl in *.
  - contradiction.
  - destruct (ident_eqb fname (fn_name f)) eqn:Hname; try discriminate.
    destruct Hin as [Hin | Hin].
    + subst fdef. intros Hcontra.
      apply ident_eqb_neq in Hname. apply Hname. symmetry. exact Hcontra.
    + eapply IH; eassumption.
Qed.

Lemma lookup_fn_in_unique_by_name :
  forall env fname fdef,
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_env_unique_by_name env ->
    lookup_fn fname (env_fns env) = Some fdef.
Proof.
  intros env fname fdef Hin Hname Hunique.
  destruct (lookup_fn fname (env_fns env)) as [f_lookup |] eqn:Hlookup.
  - f_equal. eapply lookup_fn_unique_by_name; eassumption.
  - exfalso.
    pose proof (lookup_fn_none_not_in_name fname (env_fns env) fdef
                  Hlookup Hin) as Hneq.
    apply Hneq. exact Hname.
Qed.

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs_core :
  forall env (Ω : outlives_ctx) s s_args Σ_args fdef fcall σ s_body vs ret
      used' T_body Γ_out R_body roots_body frame_final,
    store_typed env s_args Σ_args ->
    store_ref_targets_preserved env s s_args ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval_args_values_have_types env Ω s_args vs (fn_params fcall) ->
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx Γ_out) s_body s_args ->
    store_param_scope (fn_params fcall) s_body frame_final ->
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) ->
    value_has_type env s_body ret T_body ->
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body ->
    store_roots_within R_body s_body ->
    value_roots_within roots_body ret ->
    store_no_shadow s_body ->
    root_env_no_shadow R_body ->
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body) /\
    exists locals,
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
    store_remove_params (fn_params fcall) s_body = s_args /\
    value_roots_within roots_body ret.
Proof.
  intros env Ω s s_args Σ_args fdef fcall σ s_body vs ret used' T_body
    Γ_out R_body roots_body frame_final Hstore_args Hpres_args Hrename
    Hargs_fcall Hframe_scope Hscope_body Hstore_body Hv_body Hpres_body
    Hroots_body Hret_roots Hshadow_body Hrn_body Hsame_body Hcompat_body
    Hexclude_ret Hexclude_env.
  destruct (eval_call_body_cleanup_preserves_value_and_refs_frame_core
              env Ω s_args Σ_args fdef fcall σ s_body vs ret used' T_body
              Γ_out R_body roots_body frame_final Hstore_args Hrename
              Hargs_fcall Hframe_scope Hscope_body Hstore_body Hv_body
              Hpres_body Hroots_body Hret_roots Hshadow_body Hrn_body
              Hsame_body Hcompat_body Hexclude_ret Hexclude_env)
    as [Hstore_final Hcleanup].
  destruct Hcleanup as [Hstore_prefix Hcleanup].
  destruct Hcleanup as [Hroots_final Hcleanup].
  destruct Hcleanup as [Hshadow_final Hcleanup].
  destruct Hcleanup as [Hrn_final Hcleanup].
  destruct Hcleanup as [Hv_final Hcleanup].
  destruct Hcleanup as [Hpres_args_final [locals Hcleanup]].
  destruct Hcleanup as [Hremoved [Hret_exclude
    [Hstore_exclude [Hremoved_exact Hret_roots_final]]]].
  repeat split; try assumption.
  - eapply store_ref_targets_preserved_trans; eassumption.
  - exists locals. repeat split; assumption.
Qed.

Definition direct_call_callee_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    exists T_body Γ_out R_params R_body roots_body,
      store_roots_within R_params
        (bind_params (fn_params fcall) vs s_args) /\
      store_no_shadow (bind_params (fn_params fcall) vs s_args) /\
      root_env_no_shadow R_params /\
      root_env_covers_params (fn_params fcall) R_params /\
      provenance_ready_expr (fn_body fcall) /\
      preservation_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
        (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    preservation_ready_expr (fn_body fcall) /\
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    preservation_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_provenance_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_provenance_ready_at
    (env : global_env) (fcall : fn_def) (R_params : root_env) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body.

Definition callee_body_root_shadow_provenance_ready_at_result_subset
    (env : global_env) (fcall : fn_def) (R_params : root_env)
    (roots_bound : root_set) : Prop :=
  exists T_body Γ_out R_body roots_body,
    provenance_ready_expr (fn_body fcall) /\
    typed_env_roots_shadow_safe env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (fn_body_ctx fcall))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
    roots_exclude_params (fn_params fcall) roots_body /\
    root_env_excludes_params (fn_params fcall) R_body /\
    root_set_stores_subset roots_body roots_bound.

Lemma callee_body_root_ready_at_of_shadow_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_ready_at env fcall R_params ->
    callee_body_root_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_ready_at in Hshadow.
  destruct Hshadow as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Hready & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_provenance_ready_at env fcall R_params ->
    callee_body_root_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hshadow.
  unfold callee_body_root_shadow_provenance_ready_at in Hshadow.
  destruct Hshadow as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; try assumption.
  eapply typed_env_roots_shadow_safe_roots. exact Htyped.
Qed.

Lemma callee_body_root_provenance_ready_at_of_ready_at :
  forall env fcall R_params,
    callee_body_root_ready_at env fcall R_params ->
    callee_body_root_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & _ & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_shadow_provenance_ready_at_of_ready_at :
  forall env fcall R_params,
    callee_body_root_shadow_ready_at env fcall R_params ->
    callee_body_root_shadow_provenance_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hready.
  unfold callee_body_root_shadow_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & _ & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_shadow_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma callee_body_root_shadow_ready_at_of_provenance_and_preservation :
  forall env fcall R_params,
    callee_body_root_shadow_provenance_ready_at env fcall R_params ->
    preservation_ready_expr (fn_body fcall) ->
    callee_body_root_shadow_ready_at env fcall R_params.
Proof.
  intros env fcall R_params Hprov_ready Hpres_ready.
  unfold callee_body_root_shadow_provenance_ready_at in Hprov_ready.
  destruct Hprov_ready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov & Htyped & Hcompat & Hexclude_roots & Hexclude_env).
  unfold callee_body_root_shadow_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Definition callee_body_root_summary (env : global_env) (fdef : fn_def)
    : Prop :=
  callee_body_root_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_summary (env : global_env) (fdef : fn_def)
    : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_provenance_ready_at env fdef (initial_root_env_for_fn fdef).

Definition callee_body_root_shadow_provenance_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  NoDup (ctx_names (params_ctx (fn_params fdef))) /\
  callee_body_root_shadow_provenance_ready_at env fdef
    (initial_root_env_for_fn fdef).

Definition env_fns_root_summary_evidence (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_summary env fdef.

Definition env_fns_root_shadow_summary_evidence (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_summary env fdef.

Definition env_fns_root_provenance_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_provenance_summary env fdef.

Definition env_fns_root_shadow_provenance_summary_evidence
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_provenance_summary env fdef.

Lemma env_fns_root_shadow_summary_evidence_in_unique :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    fn_env_unique_by_name env ->
    forall fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_summary env fdef.
Proof.
  intros env Hsummary Hunique fname fdef Hin Hname.
  unfold env_fns_root_shadow_summary_evidence in Hsummary.
  eapply Hsummary.
  eapply lookup_fn_in_unique_by_name; eassumption.
Qed.

Lemma env_fns_root_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_summary, callee_body_root_shadow_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [_ Hready].
  eapply callee_body_root_ready_at_of_shadow_ready_at.
  exact Hready.
Qed.

Lemma env_fns_root_shadow_provenance_summary_evidence_of_shadow :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    env_fns_root_shadow_provenance_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_summary_evidence in Hshadow.
  unfold callee_body_root_shadow_summary,
    callee_body_root_shadow_provenance_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [Hnodup Hready].
  split.
  - exact Hnodup.
  - eapply callee_body_root_shadow_provenance_ready_at_of_ready_at.
    exact Hready.
Qed.

Lemma env_fns_root_provenance_summary_evidence_of_shadow_provenance :
  forall env,
    env_fns_root_shadow_provenance_summary_evidence env ->
    env_fns_root_provenance_summary_evidence env.
Proof.
  intros env Hshadow fname fdef Hlookup.
  unfold env_fns_root_shadow_provenance_summary_evidence in Hshadow.
  unfold callee_body_root_provenance_summary,
    callee_body_root_shadow_provenance_summary in *.
  destruct (Hshadow fname fdef Hlookup) as [_ Hready].
  eapply callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at.
  exact Hready.
Qed.

Lemma env_fns_root_shadow_summary_evidence_of_provenance_and_preservation :
  forall env,
    env_fns_root_shadow_provenance_summary_evidence env ->
    env_fns_preservation_ready env ->
    env_fns_root_shadow_summary_evidence env.
Proof.
  intros env Hprov Hpres fname fdef Hlookup.
  unfold env_fns_root_shadow_provenance_summary_evidence in Hprov.
  unfold callee_body_root_shadow_provenance_summary,
    callee_body_root_shadow_summary in *.
  destruct (Hprov fname fdef Hlookup) as [Hnodup Hready].
  split.
  - exact Hnodup.
  - eapply callee_body_root_shadow_ready_at_of_provenance_and_preservation.
    + exact Hready.
    + apply Hpres.
      destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
        as [Hin _].
      exact Hin.
Qed.

Definition direct_call_callee_body_root_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_shadow_summary_bridge
    (env : global_env) : Prop :=
  env_fns_root_shadow_summary_evidence env ->
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_shadow_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Definition direct_call_callee_body_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_ready_at env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args).

Lemma direct_call_callee_body_root_evidence_of_summary_bridge :
  forall env,
    env_fns_root_summary_evidence env ->
    direct_call_callee_body_root_summary_bridge env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply Hbridge; eassumption.
Qed.

Lemma direct_call_callee_body_root_evidence_of_shadow_summary_bridge :
  forall env,
    env_fns_root_shadow_summary_evidence env ->
    direct_call_callee_body_root_shadow_summary_bridge env ->
    direct_call_callee_body_root_evidence env.
Proof.
  intros env Hsummary Hbridge Ω n R Σ Σ_args R_args arg_roots fname args
    fdef fcall σ s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  eapply callee_body_root_ready_at_of_shadow_ready_at.
  eapply Hbridge; eassumption.
Qed.
