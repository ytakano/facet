From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness
  CheckerRootSidecars.
From Facet.TypeSystem Require Export TypeSafetyDirectCallEvidence.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition eval_preserves_typing_synthetic_direct_call_ready_statement : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.

Theorem eval_preserves_typing_direct_call_roots_ready_without_env_ready_with_preservation_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Htyping_roots Htyping_ready Hroots_ready Hframe_scope_ready
    Htyping_roots_prefix_ready Hparam_scope_ready env s e s' v Heval Ω n R
    Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hcallee_roots.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    destruct (proj1 Htyping_roots
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hstore Hroots Hshadow Hrn Htyped)
      as [Hstore' [Hv [Hpres _]]].
    repeat split; assumption.
  - dependent destruction Heval.
    dependent destruction Htyped.
    try solve
      [ eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
        eauto ].
    match goal with
    | Hready_args0 : preservation_ready_args ?args_call |- _ =>
        pose proof (preservation_ready_args_implies_provenance_ready_closure
                      args_call Hready_args0) as Hprov_args
    end.
    repeat match goal with
    | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
        Some ?f_runtime,
      Hin : In ?f_typed (env_fns env) |- _ =>
        pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
          f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
        subst f_runtime
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : fn_name ?f_typed = ?fname_call |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin Hname Hunique) as Hsame;
        subst f_typed
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : ?fname_call = fn_name ?f_typed |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
        subst f_typed
    end.
    match goal with
    | Htyped_args : typed_args_roots ?env_call ?Ω_call ?n_call ?R_call ?Σ_call ?args_call
        ?params_inst ?Σ_args_call ?R_args_call ?arg_roots,
      Heval_args : eval_args ?env_call ?s_call ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns ?env_call),
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (Hcallee_roots Ω_call n_call R_call Σ_call
                      Σ_args_call R_args_call arg_roots
                      (fn_name fdef) args_call fdef fcall σ s s_args vs
                      used' Hin eq_refl Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_ready_at env fcall
            (call_param_root_env (fn_params fcall) arg_roots R_args_call)
            Hbody_ready) as Hbody_prov_ready;
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eassumption
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hfname : fn_name ?fdef = ?fname_call,
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (Hcallee_roots Ω n R Σ Σ' R' arg_roots
                      fname_call args_call fdef fcall σ s s_args vs
                      used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_ready_at env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_ready) as Hbody_prov_ready;
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eassumption
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof (Hcallee_roots Ω n R Σ Σ' R' arg_roots
                      (fn_name fdef) args_call fdef fcall σ s s_args vs
                      used' Hin eq_refl Hcaps Htyped_args Heval_args Hprov_args
                      Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_ready_at env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_ready) as Hbody_prov_ready;
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eassumption
    | _ =>
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eauto
    end; eauto.
Qed.

Theorem eval_preserves_typing_direct_call_roots_synthetic_ready_with_old_evidence_with_preservation_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_evidence env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Htyping_roots Htyping_ready Hroots_ready Hframe_scope_ready
    Htyping_roots_prefix_ready Hparam_scope_ready env s e s' v Heval Ω n R
    Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hold_evidence _.
  eapply
    (eval_preserves_typing_direct_call_roots_ready_without_env_ready_with_preservation_core
      Htyping_roots Htyping_ready Hroots_ready Hframe_scope_ready
      Htyping_roots_prefix_ready Hparam_scope_ready);
    eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_ready_with_preservation_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_preservation_ready env ->
      direct_call_callee_body_root_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Htyping_roots Htyping_ready Hroots_ready Hframe_scope_ready
    Htyping_roots_prefix_ready Hparam_scope_ready env s e s' v Heval Ω n R
    Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique _ Hcallee_roots.
  eapply
    (eval_preserves_typing_direct_call_roots_ready_without_env_ready_with_preservation_core
      Htyping_roots Htyping_ready Hroots_ready Hframe_scope_ready
      Htyping_roots_prefix_ready Hparam_scope_ready);
    eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready_with_preservation_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_provenance_summary_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Htyping_roots Htyping_ready Hroots_ready Hroot_names Hroot_keys
    Hframe_scope_ready Htyping_roots_prefix_ready Hparam_scope_ready env s e
    s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Htyped Hunique Hsummary.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    destruct (proj1 Htyping_roots
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hstore Hroots Hshadow Hrn Htyped)
      as [Hstore' [Hv [Hpres _]]].
    repeat split; assumption.
  - dependent destruction Heval.
    dependent destruction Htyped.
    match goal with
    | Hready_args0 : preservation_ready_args ?args_call |- _ =>
        pose proof (preservation_ready_args_implies_provenance_ready_closure
                      args_call Hready_args0) as Hprov_args
    end.
    repeat match goal with
    | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
        Some ?f_runtime,
      Hin : In ?f_typed (env_fns env) |- _ =>
        pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
          f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
        subst f_runtime
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : fn_name ?f_typed = ?fname_call |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin Hname Hunique) as Hsame;
        subst f_typed
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : ?fname_call = fn_name ?f_typed |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
        subst f_typed
    end.
    match goal with
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hfname : fn_name ?fdef = ?fname_call,
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof
          (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique_with_preservation_core
            Hroot_names Hroot_keys env Hunique Hsummary Ω n R Σ Σ' R'
            arg_roots fname_call args_call fdef fcall σ s s_args vs
            used' Hin Hfname Hcaps Htyped_args Heval_args Hprov_args
            Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_shadow_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at
            env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_shadow_ready) as Hbody_ready;
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eassumption
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Hin : In ?fdef (env_fns env),
      Hcaps : fn_captures ?fdef = [] |- _ =>
        pose proof
          (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_unique_with_preservation_core
            Hroot_names Hroot_keys env Hunique Hsummary Ω n R Σ Σ' R'
            arg_roots (fn_name fdef) args_call fdef fcall σ s s_args vs
            used' Hin eq_refl Hcaps Htyped_args Heval_args Hprov_args
            Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
          as Hbody_shadow_ready;
        pose proof
          (callee_body_root_provenance_ready_at_of_shadow_provenance_ready_at
            env fcall
            (call_param_root_env (fn_params fcall) arg_roots R')
            Hbody_shadow_ready) as Hbody_ready;
        eapply
          (eval_direct_call_body_provenance_ready_preserves_typing_with_preservation_core
            Htyping_ready Hroots_ready Hframe_scope_ready
            Htyping_roots_prefix_ready
            Hparam_scope_ready);
          eassumption
    end.
Qed.

Lemma eval_call_expr_fn_as_call :
  forall env s s' v fname args,
    eval env s (ECallExpr (EFn fname) args) s' v ->
    eval env s (ECall fname args) s' v.
Proof.
  intros env s s' v fname args Heval.
  dependent destruction Heval.
  match goal with
  | Hcallee : eval _ _ (EFn _) _ (VClosure _ _) |- _ =>
      dependent destruction Hcallee
  end.
  simpl in *.
  match goal with
  | Hlookup_fn : lookup_fn ?fname_call (env_fns env) = Some ?fdef_fn,
    Hcaps_fn : fn_captures ?fdef_fn = [],
    Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?fdef,
    Hargs : eval_args env s args ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
      (?fcall, ?used'),
    Hbody : eval env (bind_params (fn_params ?fcall) ?vs ?s_args)
      (fn_body ?fcall) ?s_body ?ret |- _ =>
      assert (Hsame : fdef_fn = fdef)
        by (eapply lookup_fn_deterministic; eassumption);
      subst fdef;
      assert (Hcaps_call : fn_captures fcall = [])
        by (rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef_fn fcall used' Hrename);
            exact Hcaps_fn);
      rewrite Hcaps_call;
      simpl;
      eapply Eval_Call;
      [ exact Hlookup | exact Hcaps_fn | exact Hargs | exact Hrename | exact Hbody ]
  end.
Qed.

Lemma eval_direct_call_target_expr_as_call :
  forall env s raw_body s' v fname args synthetic_body,
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) ->
    synthetic_body = ECall fname args ->
    eval env s raw_body s' v ->
    eval env s synthetic_body s' v.
Proof.
  intros env s raw_body s' v fname args synthetic_body Htarget Hsynthetic
    Heval.
  subst synthetic_body.
  unfold direct_call_target_expr in Htarget.
  destruct raw_body; try discriminate.
  - inversion Htarget; subst. exact Heval.
  - destruct raw_body; try discriminate.
    inversion Htarget; subst.
    apply eval_call_expr_fn_as_call. exact Heval.
Qed.

Lemma eval_synthetic_direct_call_body_from_ready_evidence :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args
      s_body vs ret used',
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
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
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    exists fname_body args_body synthetic_body T_body Γ_out R_body roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) /\
      synthetic_body = ECall fname_body args_body /\
      preservation_direct_call_ready_expr synthetic_body /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body /\
      eval env (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret.
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ
    s s_args s_body vs ret used' Hevidence Hin Hfname Hcaps Htyped_args
    Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename
    Heval_body.
  pose proof
    (Hevidence Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ
      s s_args vs used' Hin Hfname Hcaps Htyped_args Heval_args
      Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename)
    as Hbody_ready.
  unfold callee_body_root_synthetic_direct_call_ready_at in Hbody_ready.
  destruct Hbody_ready as
    (fname_body & args_body & synthetic_body & T_body & Γ_out &
      R_body & roots_body & Htarget & Hsynthetic & Hready_body &
      Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env).
  exists fname_body, args_body, synthetic_body, T_body, Γ_out, R_body,
    roots_body.
  repeat split; try assumption.
  eapply eval_direct_call_target_expr_as_call; eassumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots fdef,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      callee_body_root_shadow_provenance_summary env fdef ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Htyping_ready Hroots_ready Hroot_names Hroot_keys
    Hframe_scope_ready Htyping_roots_prefix_ready Hparam_scope_ready env s s'
    v fname args Heval Ω n R Σ T Σ' R' roots fdef Hready_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hin_summary
    Hfname_summary Hcallee_summary.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  | Hin : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call,
    Hin0 : In ?f_summary (env_fns env),
    Hname0 : fn_name ?f_summary = ?fname_call |- _ =>
      pose proof (Hunique f_typed f_summary Hin Hin0
        (eq_trans Hname (eq_sym Hname0))) as Hsame;
      subst f_typed
  end.
  assert (Hcaps_fdef1 : fn_captures fdef1 = []) by assumption.
  match goal with
  | Htyped_args : typed_args_roots ?env_call ?Ω_call ?n_call ?R_call
      ?Σ_call ?args_call ?params_inst ?Σ_args_call ?R_args_call ?arg_roots,
    Heval_args : eval_args ?env_call ?s_call ?args_call ?s_args ?vs,
    Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef_call =
      (?fcall, ?used') |- _ =>
    pose proof
      (direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset_with_preservation_core
        Hroot_names Hroot_keys env_call Ω_call n_call R_call Σ_call
        Σ_args_call R_args_call arg_roots args_call
        fdef_call fcall σ s s_args vs used' Hcallee_summary Hcaps_fdef1
        Htyped_args Heval_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed
          Hkeys Hrename)
        as Hbody_shadow_ready;
      unfold callee_body_root_shadow_provenance_ready_at_result_subset
        in Hbody_shadow_ready;
      destruct Hbody_shadow_ready
        as (T_body & Γ_out & R_body & roots_body &
            Hprov_body & Htyped_shadow_body & Hcompat_body &
            Hexclude_ret & Hexclude_env & Hresult_subset);
      assert (Hcaps_call : fn_captures fcall = [])
        by (rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef_call fcall used' Hrename);
            exact Hcaps_fdef1);
      pose proof (typed_env_roots_shadow_safe_roots
          (global_env_with_local_bounds env (fn_bounds fcall))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R')
          (sctx_of_ctx (fn_body_ctx fcall))
          (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body
          Htyped_shadow_body) as Htyped_body_ctx;
      pose proof
        (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
          (global_env_with_local_bounds env (fn_bounds fcall))
          (fn_outlives fcall) (fn_lifetimes fcall)
          (call_param_root_env (fn_params fcall) arg_roots R')
          fcall (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
          roots_body Hcaps_call Htyped_body_ctx) as Htyped_body
  end.
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef1)) Σ'
              Hready_args Hstore
	              (typed_args_roots_structural env Ω n R Σ args
	                (apply_lt_params σ (fn_params fdef1)) Σ' R'
	                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
	              (apply_lt_params σ (fn_params fdef1)) Σ' R'
	              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef1 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef1))
  by (eapply eval_args_values_have_types_apply_lt_params_inv;
      exact Hargs_subst).
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall))
  by (eapply eval_args_values_have_types_params_alpha;
      [ exact Hparams_alpha | exact Hargs_unsubst_fdef ]).
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall))))
  by (eapply alpha_rename_fn_def_params_nodup_ctx_names;
      exact H2).
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args)
  by (eapply alpha_rename_fn_def_params_fresh_in_store;
      exact H2).
  destruct (eval_args_bind_params_call_param_root_env_ready
	              env s args s_args vs Ω n R Σ
	              (apply_lt_params σ (fn_params fdef1)) Σ' R' arg_roots
	              (fn_params fcall) H1 Hprov_args H7
	              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  destruct
    (eval_direct_call_body_cleanup_preserves_value_and_refs_with_preservation_core
      Htyping_ready Hroots_ready Hframe_scope_ready
      Htyping_roots_prefix_ready
      Hparam_scope_ready
      env Ω n R Σ Σ' R' arg_roots (fn_name fdef1) args
	      fdef1 fcall σ s s_args s_body vs ret used' T_body
	      Γ_out (call_param_root_env (fn_params fcall) arg_roots R')
	      R_body roots_body Hstore Hroots Hshadow Hrn Hprov_args
	      Hready_args H7 H1 H2 Hroots_bind
      Hshadow_bind Hrn_params Hcover_params Hprov_body
      Htyped_body Hcompat_body Hexclude_ret Hexclude_env
      Heval)
    as [_ [Hstore_final [_ [_ [_ [_ [Hv_final
          [Hpres_final Hcleanup_tail]]]]]]]].
  destruct Hcleanup_tail
    as [frame_final [locals_final
        [_ [_ [_ [_ [Hremoved_exact Hret_roots_body]]]]]]].
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Hroots_args.
  - eapply direct_call_value_roots_within_store_subset; eassumption.
  - rewrite Hremoved_exact. exact Hshadow_args.
Qed.
