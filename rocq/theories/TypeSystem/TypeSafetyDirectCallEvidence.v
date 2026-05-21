From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyDirectCallBody.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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

Lemma direct_call_callee_body_root_shadow_summary_bridge_of_unique_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    direct_call_callee_body_root_shadow_summary_bridge env.
Proof.
  intros Hroot_names Hroot_keys env Hunique Hsummary Ω n R Σ Σ_args
    R_args arg_roots fname args fdef fcall σ s s_args vs used' Hin Hfname
    Hcaps Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename.
  destruct (env_fns_root_shadow_summary_evidence_in_unique
              env Hsummary Hunique fname fdef Hin Hfname)
    as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov_body & Hready_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { rewrite <- (apply_lt_params_length σ (fn_params fdef)).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply
      (eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core
        Hroot_names Hroot_keys);
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply
        (eval_args_root_names_excludes_params_ready_with_preservation_core
          Hroot_names);
        eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hready_fcall : preservation_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_preservation_ready_body; eassumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_ready_at.
  exists T_body, Γ_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
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
      callee_body_root_shadow_provenance_ready_at_result_subset env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (root_sets_union arg_roots).
Proof.
  intros Hroot_names Hroot_keys env Ω n R Σ Σ_args R_args arg_roots args
    fdef fcall σ s s_args vs used' Hsummary Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  unfold callee_body_root_shadow_provenance_summary in Hsummary.
  destruct Hsummary as [Hnodup_fdef Hready].
  unfold callee_body_root_shadow_provenance_ready_at in Hready.
  destruct Hready as
    (T_body & Γ_out & R_body & roots_body &
      Hprov_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  destruct (alpha_rename_fn_def_initial_support_facts
              (store_names s_args) fdef fcall used' Hrename Hnodup_fdef)
    as (rho & used_params & Hparams_rename & Hbody_rename &
        Halpha_params & Hrn_initial & Hrn_initial_r & Hinitial_equiv &
        Hkeys_initial & Hroots_initial & Hnocoll_initial & Hctx_used &
        Hrange_used & Hdisj).
  destruct (alpha_rename_fn_def_static_fields
              (store_names s_args) fdef fcall used' Hrename)
    as [_ [Hlts [Houts [Hcaps_eq Hret]]]].
  assert (Htyped_body_params :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (fn_body fdef) T_body (sctx_of_ctx Γ_out) R_body roots_body).
  { eapply typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures;
      eassumption. }
  clear Htyped_body. rename Htyped_body_params into Htyped_body.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fdef)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_body. }
  assert (Hkeys_body : root_env_sctx_keys_named R_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hkeys_expr _].
    eapply Hkeys_expr; eassumption. }
  assert (Hroots_body_named :
    root_env_sctx_roots_named R_body (sctx_of_ctx Γ_out) /\
    root_set_sctx_roots_named roots_body (sctx_of_ctx Γ_out)).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    eapply Hroots_expr; eassumption. }
  destruct Hroots_body_named as [Hroots_env_body Hroots_set_body].
  assert (Hrn_body : root_env_no_shadow R_body).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped_body.
    - exact Hrn_initial. }
  assert (Hnocoll_body :
    rename_no_collision_on rho (root_env_names R_body)).
  { eapply rename_no_collision_on_root_env_names_from_typed_support;
      eassumption. }
  destruct (alpha_rename_typed_env_roots_shadow_safe_full_support_forward
              env (fn_outlives fdef) (fn_lifetimes fdef) rho
              (initial_root_env_for_fn fdef)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fdef)))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fdef) (fn_body fcall) used_params used'
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Htyped_body Halpha_params Hrn_initial Hrn_initial_r
              Hinitial_equiv Hkeys_initial Hroots_initial
              Hnocoll_initial Hnocoll_body Hctx_used Hrange_used Hdisj
              Hbody_rename)
    as (Γ_out_r & R_body_r & roots_body_r &
        Htyped_renamed & Halpha_out & Hrn_body_r & Hbody_equiv &
        Hroots_equiv).
  assert (Hexclude_roots_renamed :
    roots_exclude_params (fn_params fcall) roots_body_r).
  { eapply roots_exclude_params_rename_from_typed_support; eassumption. }
  assert (Hexclude_env_renamed :
    root_env_excludes_params (fn_params fcall) R_body_r).
  { eapply root_env_excludes_params_rename_from_typed_support.
    - exact Halpha_params.
    - exact Halpha_out.
    - exact Hsame_body.
    - exact Hnodup_fdef.
    - exact Hrn_body.
    - exact Hbody_equiv.
    - exact Hkeys_body.
    - exact Hroots_env_body.
    - exact Hexclude_env. }
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hlen_arg_roots_fdef :
    List.length arg_roots = List.length (fn_params fdef)).
  { rewrite <- (apply_lt_params_length σ (fn_params fdef)).
    eapply typed_args_roots_arg_roots_length. exact Htyped_args. }
  assert (Hlen_arg_roots_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Hparams_alpha).
    exact Hlen_arg_roots_fdef. }
  assert (Hrn_call_empty :
    root_env_no_shadow (call_param_root_env (fn_params fcall) arg_roots [])).
  { apply call_param_root_env_no_shadow.
    - eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename.
    - simpl. constructor. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params (fn_params fdef) arg_roots)
        (initial_root_env_for_params_origin
          (fn_params fdef) (fn_params fcall)))
      (call_param_root_env (fn_params fcall) arg_roots [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  assert (Harg_roots_named :
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots).
  { destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
              Hprov_args Hstore Hroots Hshadow Hrn Hnamed Htyped_args)
      as [_ Harg_roots_named].
    exact Harg_roots_named. }
  assert (Hsubst_fresh :
    root_subst_images_exclude_names (expr_local_store_names (fn_body fcall))
      (root_subst_of_params (fn_params fdef) arg_roots)).
  { eapply root_subst_of_params_images_exclude_names_from_store_roots.
    - exact Harg_roots_named.
    - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
      exact Hrename. }
  destruct (typed_env_roots_shadow_safe_instantiate_fresh
              env (fn_outlives fdef) (fn_lifetimes fdef)
              (root_subst_of_params (fn_params fdef) arg_roots)
              (initial_root_env_for_params_origin
                (fn_params fdef) (fn_params fcall))
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
              (call_param_root_env (fn_params fcall) arg_roots [])
              Htyped_renamed Hsubst_fresh Hrn_initial_r Hrn_call_empty)
    as (R_body_inst & roots_body_inst &
        Htyped_inst & Hrn_body_inst & Hbody_inst_equiv &
        Hroots_inst_equiv).
  { apply root_env_equiv_sym. exact Hinitial_inst_equiv. }
  assert (Hfresh_params :
    params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Harg_roots_exclude :
    Forall (roots_exclude_params (fn_params fcall)) arg_roots).
  { eapply root_sets_store_roots_named_excludes_params; eassumption. }
  assert (Himages_exclude :
    forall x,
      In x (ctx_names (params_ctx (fn_params fcall))) ->
      root_subst_images_exclude x
        (root_subst_of_params (fn_params fdef) arg_roots)).
  { intros x Hin_x.
    apply root_subst_of_params_images_exclude.
    eapply Forall_impl; [| exact Harg_roots_exclude].
    intros roots_i Hroots_i.
    apply Hroots_i. exact Hin_x. }
  assert (Hexclude_roots_inst :
    roots_exclude_params (fn_params fcall) roots_body_inst).
  { eapply roots_exclude_params_equiv.
    - apply root_set_equiv_sym. exact Hroots_inst_equiv.
    - eapply roots_exclude_params_instantiate.
      + exact Hexclude_roots_renamed.
      + exact Himages_exclude. }
  assert (Hexclude_env_inst :
    root_env_excludes_params (fn_params fcall) R_body_inst).
  { eapply root_env_excludes_params_equiv.
    - apply root_env_equiv_sym. exact Hbody_inst_equiv.
    - eapply root_env_excludes_params_instantiate.
      + exact Hexclude_env_renamed.
      + exact Himages_exclude. }
  assert (Htail_fresh :
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall))).
  { eapply
      (eval_args_root_tail_fresh_names_for_fresh_call_with_preservation_core
        Hroot_names Hroot_keys);
      eassumption. }
  assert (Htyped_tail :
    typed_env_roots_shadow_safe env (fn_outlives fdef) (fn_lifetimes fdef)
      (call_param_root_env (fn_params fcall) arg_roots [] ++
        root_env_remove_params (fn_params fcall) R_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body Γ_out_r
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)
      roots_body_inst).
  { eapply typed_env_roots_shadow_safe_tail_frame; eassumption. }
  assert (Htail_exclude :
    root_env_excludes_params (fn_params fcall)
      (root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_remove_params_excludes_params.
    - eapply typed_args_roots_no_shadow; eassumption.
    - eapply
        (eval_args_root_names_excludes_params_ready_with_preservation_core
          Hroot_names);
        eassumption. }
  assert (Hexclude_env_tail :
    root_env_excludes_params (fn_params fcall)
      (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args)).
  { apply root_env_excludes_params_app; assumption. }
  assert (Hprov_fcall : provenance_ready_expr (fn_body fcall)).
  { eapply alpha_rename_fn_def_provenance_ready_body; eassumption. }
  assert (Hsame_body_r :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall))) Γ_out_r).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped_renamed. }
  assert (Hroots_set_body_r :
    root_set_sctx_roots_named roots_body_r Γ_out_r).
  { destruct (typed_roots_shadow_safe_sctx_roots_named_mutual env
                (fn_outlives fdef) (fn_lifetimes fdef)) as [Hroots_expr _].
    destruct (Hroots_expr
                (initial_root_env_for_params_origin
                  (fn_params fdef) (fn_params fcall))
                (sctx_of_ctx (params_ctx (fn_params fcall)))
                (fn_body fcall) T_body Γ_out_r R_body_r roots_body_r
                Htyped_renamed Hrn_initial_r
                (initial_root_env_for_params_origin_sctx_roots_named
                  (fn_params fdef) (fn_params fcall)))
      as [_ Hroots_set].
    exact Hroots_set. }
  assert (Hroots_body_r_no_store : root_set_no_store roots_body_r).
  { eapply root_set_no_store_of_sctx_named_excludes_params; eassumption. }
  assert (Hsubset_inst :
    root_set_stores_subset roots_body_inst (root_sets_union arg_roots)).
  { eapply root_set_stores_subset_equiv.
    - exact Hroots_inst_equiv.
    - eapply root_set_instantiate_no_store_stores_subset_root_sets_union.
      exact Hroots_body_r_no_store. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite Hcaps_eq. exact Hcaps. }
  unfold callee_body_root_shadow_provenance_ready_at_result_subset.
  exists T_body, Γ_out_r,
    (R_body_inst ++ root_env_remove_params (fn_params fcall) R_args),
    roots_body_inst.
  repeat split; try assumption;
    try (rewrite call_param_root_env_app_tail; unfold sctx_of_ctx;
         rewrite Houts; rewrite Hlts;
         rewrite (fn_body_ctx_eq_params_ctx_when_no_captures
                    fcall Hcaps_call);
         exact Htyped_tail);
    try (rewrite Houts; rewrite Hret; exact Hcompat_body).
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      args fdef fcall (σ : list lifetime) s s_args vs used',
      callee_body_root_shadow_provenance_summary env fdef ->
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
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  intros Hroot_names Hroot_keys env Ω n R Σ Σ_args R_args arg_roots args
    fdef fcall σ s s_args vs used' Hsummary Hcaps Htyped_args Heval_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename.
  destruct
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset_with_preservation_core
      Hroot_names Hroot_keys env Ω n R Σ Σ_args R_args arg_roots args
      fdef fcall σ s s_args vs used' Hsummary Hcaps Htyped_args Heval_args
      Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
    as (T_body & Γ_out & R_body & roots_body &
        Hprov_body & Htyped_body & Hcompat_body &
        Hexclude_roots & Hexclude_env & _).
  unfold callee_body_root_shadow_provenance_ready_at.
  exists T_body, Γ_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique_with_preservation_core :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env,
    fn_env_unique_by_name env ->
    env_fns_root_shadow_provenance_summary_evidence env ->
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
      callee_body_root_shadow_provenance_ready_at env fcall
        (call_param_root_env (fn_params fcall) arg_roots R_args).
Proof.
  intros Hroot_names Hroot_keys env Hunique Hsummary Ω n R Σ Σ_args
    R_args arg_roots fname args fdef fcall σ s s_args vs used' Hin Hfname
    Hcaps Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename.
  eapply
    (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_preservation_core
      Hroot_names Hroot_keys);
    try eassumption.
  eapply Hsummary.
  eapply lookup_fn_in_unique_by_name; eassumption.
Qed.

