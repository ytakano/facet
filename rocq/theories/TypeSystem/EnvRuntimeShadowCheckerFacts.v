From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeShadowSummaryFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma existsb_ident_eqb_false_notin :
  forall x xs,
    existsb (ident_eqb x) xs = false ->
    ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; intros Hexists Hin.
  - contradiction.
  - simpl in Hexists.
    apply orb_false_iff in Hexists as [Hy Hys].
    destruct Hin as [Hin | Hin].
    + subst y. rewrite ident_eqb_refl in Hy. discriminate.
    + eapply IH; eassumption.
Qed.

Lemma store_lookup_none_not_in_store_names :
  forall x s,
    store_lookup x s = None ->
    ~ In x (store_names s).
Proof.
  intros x s Hlookup Hin.
  induction s as [| se rest IH]; simpl in Hin; try contradiction.
  simpl in Hlookup.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - discriminate.
  - destruct Hin as [Hin | Hin].
    + subst x. rewrite ident_eqb_refl in Heq. discriminate.
    + apply IH; assumption.
Qed.

Lemma args_free_vars_checker_eq :
  forall args,
    args_free_vars_checker args = args_free_vars_ts args.
Proof.
  induction args as [| e rest IH]; unfold args_free_vars_checker in *;
    simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma local_captured_call_target_expr_sound :
  forall e fname captures args m x T direct_body let_body,
    local_captured_call_target_expr e =
      Some (fname, captures, args, m, x, T, direct_body, let_body) ->
    e =
      ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args) /\
    direct_body = ECallExpr (EMakeClosure fname captures) args /\
    let_body = ELet m x T (EMakeClosure fname captures) direct_body /\
    ty_usage T = UUnrestricted /\
    ~ In x captures /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args).
Proof.
  intros e fname captures args m x T direct_body let_body Htarget.
  unfold local_captured_call_target_expr in Htarget.
  destruct e as
    [| lit | z | m0 x0 T0 e1 e2 | m0 x0 e1 e2 | fname_value
     | fname_make captures_make | p | fname_direct args_direct
     | callee args_call | sname lts tys fields
     | p e_new | p e_new | rk p | e | e | e1 e2 e3];
    try discriminate.
  destruct e1 as
    [| lit1 | z1 | m1 x1 T1 e11 e12 | m1 x1 e11 e12
     | fname_value1 | fname_make captures_make | p1
     | fname1 args1 | callee1 args1 | sname1 lts1 tys1 fields1
     | p1 e_new1 | p1 e_new1 | rk1 p1 | e1 | e1 | e11 e12 e13];
    try discriminate.
  destruct e2 as
    [| lit2 | z2 | m2 x2 T2 e21 e22 | m2 x2 e21 e22
     | fname_value2 | fname_make2 captures_make2 | p2
     | fname2 args2 | callee2 args2 | sname2 lts2 tys2 fields2
     | p2 e_new2 | p2 e_new2 | rk2 p2 | e2 | e2 | e21 e22 e23];
    try discriminate.
  destruct callee2 as
    [| litc | y | mc xc Tc ec1 ec2 | mc xc ec1 ec2
     | fnamec | fname_makec captures_makec | pc
     | fnamec argsc | calleec argsc | snamec ltsc tysc fieldsc
     | pc e_newc | pc e_newc | rkc pc | ec | ec | ec1 ec2 ec3];
    try discriminate.
  destruct
    (ident_eqb x0 y &&
     usage_eqb (ty_usage T0) UUnrestricted &&
     negb (existsb (ident_eqb x0) captures_make) &&
     negb (existsb (ident_eqb x0) (args_free_vars_checker args2)) &&
     negb (existsb (ident_eqb x0) (args_local_store_names args2)))
    eqn:Hguards; try discriminate.
  inversion Htarget; subst; clear Htarget.
  apply andb_true_iff in Hguards as [Hguards Hlocal].
  apply andb_true_iff in Hguards as [Hguards Hfree].
  apply andb_true_iff in Hguards as [Hguards Hcaps].
  apply andb_true_iff in Hguards as [Hid Husage].
  apply ident_eqb_eq in Hid. subst y.
  apply usage_eqb_true in Husage.
  apply negb_true_iff in Hcaps.
  apply negb_true_iff in Hfree.
  apply negb_true_iff in Hlocal.
  repeat split; try reflexivity; try exact Husage.
  - eapply existsb_ident_eqb_false_notin. exact Hcaps.
  - rewrite <- args_free_vars_checker_eq.
    eapply existsb_ident_eqb_false_notin. exact Hfree.
  - eapply existsb_ident_eqb_false_notin. exact Hlocal.
Qed.

Lemma callee_hidden_capture_args_disjoint_b_sound :
  forall callee args,
    callee_hidden_capture_args_disjoint_b callee args = true ->
    callee_hidden_capture_args_disjoint callee args.
Proof.
  intros callee args Hcheck.
  unfold callee_hidden_capture_args_disjoint_b in Hcheck.
  unfold callee_hidden_capture_args_disjoint.
  apply Forall_forall.
  intros x Hin Harg.
  apply forallb_forall with (x := x) in Hcheck; [| exact Hin].
  apply negb_true_iff in Hcheck.
  assert (Hexists :
    existsb (ident_eqb x) (args_local_store_names args) = true).
  { apply existsb_exists.
    exists x. split; [exact Harg|].
    apply ident_eqb_refl. }
  rewrite Hexists in Hcheck. discriminate.
Qed.

Lemma fn_params_roots_exclude_b_sound :
  forall ps roots,
    fn_params_roots_exclude_b ps roots = true ->
    roots_exclude_params ps roots.
Proof.
  intros ps roots Hexclude.
  apply roots_exclude_params_b_sound.
  unfold roots_exclude_params_b, fn_params_roots_exclude_b in *.
  exact Hexclude.
Qed.

Lemma fn_params_root_env_excludes_b_sound :
  forall ps R,
    fn_params_root_env_excludes_b ps R = true ->
    root_env_excludes_params ps R.
Proof.
  intros ps R Hexclude.
  apply root_env_excludes_params_b_sound.
  unfold root_env_excludes_params_b, fn_params_root_env_excludes_b in *.
  exact Hexclude.
Qed.

Lemma check_fn_root_shadow_summary_sound :
  forall env fdef,
    check_fn_root_shadow_summary env fdef = true ->
    callee_body_root_shadow_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_fn fdef))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    unfold callee_body_root_shadow_ready_at.
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply preservation_ready_implies_provenance_ready.
      apply preservation_ready_expr_b_sound. exact Hready.
    + apply preservation_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_provenance_summary env fdef = true ->
    callee_body_root_shadow_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_provenance_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_fn fdef))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    unfold callee_body_root_shadow_provenance_ready_at.
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply provenance_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_direct_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_direct_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_direct_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_direct_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_provenance_summary env fdef) eqn:Hold.
  - left. apply check_fn_root_shadow_provenance_summary_sound. exact Hold.
  - right.
    destruct (direct_call_target_expr (fn_body fdef))
      as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env
      (fn_with_body fdef synthetic_body)
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env (fn_with_body fdef synthetic_body)
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists fname, args, (fn_body fdef), synthetic_body, fcallee,
      T_body, Γ_out, R_out, roots.
    split; [reflexivity|].
    split; [exact Htarget|].
    split.
    { unfold direct_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      - inversion Htarget. reflexivity.
      - destruct e; try discriminate.
        inversion Htarget. reflexivity. }
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [apply check_fn_root_shadow_provenance_summary_sound; exact Hcallee|].
    split.
    { change (NoDup
        (ctx_names
          (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
      eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_non_capturing_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_non_capturing_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_non_capturing_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_non_capturing_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_direct_call_provenance_summary env fdef)
    eqn:Hold.
  - left. apply check_fn_root_shadow_direct_call_provenance_summary_sound.
    exact Hold.
  - right.
    destruct (local_fn_value_call_target_expr (fn_body fdef))
      as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env
      (fn_with_body fdef synthetic_body)
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env (fn_with_body fdef synthetic_body)
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists fname, args, (fn_body fdef), synthetic_body, fcallee,
      T_body, Γ_out, R_out, roots.
    split; [reflexivity|].
    split; [exact Htarget|].
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [apply check_fn_root_shadow_provenance_summary_sound; exact Hcallee|].
    split.
    { change (NoDup
        (ctx_names
          (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
      eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_captured_callee_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_callee_provenance_summary env fdef = true ->
    callee_body_root_shadow_captured_callee_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_callee_provenance_summary in Hcheck.
  apply andb_true_iff in Hcheck as [Hready Hsummary].
  destruct (infer_env_roots_shadow_safe env fdef
    (initial_root_env_for_params (fn_params fdef ++ fn_captures fdef)))
    as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
    try discriminate.
  apply andb_true_iff in Hsummary as [Hroots Henv].
  split.
  - eapply infer_env_roots_shadow_safe_binding_params_nodup. exact Hinfer.
  - pose proof (infer_env_roots_shadow_safe_sound
                  env fdef
                  (initial_root_env_for_params
                    (fn_params fdef ++ fn_captures fdef))
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    exists T_body, Γ_out, R_out, roots.
    repeat split.
    + apply provenance_ready_expr_b_sound. exact Hready.
    + exact Htyped.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma direct_call_target_expr_ok_is_call_early :
  forall fuel env Ω n R Σ e T Σ' R' roots fname args synthetic_body,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    direct_call_target_expr e = Some (fname, args, synthetic_body) ->
    e = ECall fname args /\ synthetic_body = ECall fname args.
Proof.
  intros fuel env Ω n R Σ e T Σ' R' roots fname args synthetic_body
    Hinfer Htarget.
  unfold direct_call_target_expr in Htarget.
  destruct e; try discriminate.
  - inversion Htarget; subst. split; reflexivity.
  - destruct e; try discriminate.
    destruct fuel; simpl in Hinfer; discriminate.
Qed.

Lemma captured_call_target_expr_ok_is_make_closure_call_early :
  forall fuel env Ω n R Σ e T Σ' R' roots fname captures args,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    captured_call_target_expr e = Some (fname, captures, args) ->
    e = ECallExpr (EMakeClosure fname captures) args.
Proof.
  intros fuel env Ω n R Σ e T Σ' R' roots fname captures args
    Hinfer Htarget.
  unfold captured_call_target_expr in Htarget.
  destruct e; try discriminate.
  destruct e; try discriminate.
  inversion Htarget. reflexivity.
Qed.

Lemma check_expr_root_shadow_captured_call_provenance_summary_fuel_sound_early :
  forall fuel env Ω n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Ω n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_captured_call_provenance_summary_fuel
      fuel env Ω n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Ω n R Σ e T Σ' R' roots
    Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_captured_call_provenance_summary_fuel]
      in Hcheck.
    rewrite Hinfer in Hcheck.
    apply orb_true_iff in Hcheck as [Hnon_if | Hif].
    + apply orb_true_iff in Hnon_if as [Hprov_or_direct | Hcaptured].
      * apply orb_true_iff in Hprov_or_direct as [Hprov | Hdirect].
        -- eexists. eapply ERSCE_Provenance.
           ++ apply provenance_ready_expr_b_sound. exact Hprov.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
        -- destruct (direct_call_target_expr e)
             as [[[fname args] synthetic_body] |] eqn:Htarget;
             try discriminate.
           apply andb_true_iff in Hdirect as [Hready_args Hdirect].
           destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
             eqn:Hlookup_b; try discriminate.
           apply andb_true_iff in Hdirect as [Hcallee Hsynthetic_ok].
           destruct (infer_core_env_state_fuel_roots_shadow_safe
             (S fuel') env Ω n R Σ synthetic_body)
             as [[[[T_syn Σ_syn] R_syn] roots_syn] | err]
             eqn:Hsynthetic; try discriminate.
           destruct (direct_call_target_expr_ok_is_call_early
             (S fuel') env Ω n R Σ e T Σ' R' roots fname args
             synthetic_body Hinfer Htarget)
             as [He Hsynthetic_body].
           subst e synthetic_body.
           rewrite Hinfer in Hsynthetic. inversion Hsynthetic; subst.
           destruct (lookup_fn_b_sound fname (env_fns env) fcallee
             Hlookup_b) as [Hin_callee Hname_callee].
           eexists. eapply ERSCE_DirectCall.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply preservation_ready_args_b_sound. exact Hready_args.
           ++ exact Hin_callee.
           ++ exact Hname_callee.
           ++ apply check_fn_root_shadow_provenance_summary_sound.
              exact Hcallee.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
           ++ eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
              exact Hinfer.
      * destruct (captured_call_target_expr e)
          as [[[fname captures] args] |] eqn:Htarget; try discriminate.
        apply andb_true_iff in Hcaptured as [Hready_args Hcaptured].
        destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
          eqn:Hlookup_b; try discriminate.
        apply andb_true_iff in Hcaptured as [Hcaptured_head Hcallee].
        apply andb_true_iff in Hcaptured_head as [Hlt Hdisjoint].
        apply PeanoNat.Nat.eqb_eq in Hlt.
        destruct (check_make_closure_captures_exact_sctx_with_env env Ω Σ
          captures (fn_captures fcallee)) as [[env_lt captured_tys] | err]
          eqn:Hcaptures; try discriminate.
        destruct (capture_root_bound R captures (fn_captures fcallee))
          as [capture_roots |] eqn:Hcapture_bound; try discriminate.
        pose proof (captured_call_target_expr_ok_is_make_closure_call_early
          (S fuel') env Ω n R Σ e T Σ' R' roots fname captures args
          Hinfer Htarget) as He.
        subst e.
        destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
          as [Hin_callee Hname_callee].
        pose proof
          (check_fn_root_shadow_captured_callee_provenance_summary_sound
            env fcallee Hcallee) as Hcallee_summary.
        destruct Hcallee_summary as
          [Hnodup_binding
           (T_body & Γ_out & R_body & roots_body & Hprov_body &
            Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env)].
        eexists. eapply ERSCE_CapturedCall.
        -- apply preservation_ready_args_b_sound. exact Hready_args.
        -- exact Hin_callee.
        -- exact Hname_callee.
        -- exact Hlt.
        -- apply callee_hidden_capture_args_disjoint_b_sound.
           exact Hdisjoint.
        -- exact Hcaptures.
        -- exact Hnodup_binding.
        -- exact Hprov_body.
        -- exact Htyped_body.
        -- exact Hcompat_body.
        -- exact Hexclude_roots.
        -- exact Hexclude_env.
        -- exact Hcapture_bound.
        -- eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
           exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hif.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err] eqn:Hcond;
        try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans)
        eqn:Hcond_core; try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e2) as [[[[T2 Σ2] R2] roots2] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Ω n R1
        Σ1 e3) as [[[[T3 Σ3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2 R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |]
        eqn:Hmerge; try discriminate.
      apply andb_true_iff in Hif as [Hif_head Helse_check].
      apply andb_true_iff in Hif_head as [Hif_head Hthen_check].
      apply andb_true_iff in Hif_head as [Hcond_bool Hprov_cond].
      destruct (IH env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 Hthen
        Hthen_check) as [ret_roots2 Hthen_summary].
      destruct (IH env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      eexists. eapply ERSCE_If.
      * apply provenance_ready_expr_b_sound. exact Hprov_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_captured_call_provenance_summary_sound_early :
  forall env Ω n R Γ e T Γ' R' roots,
    infer_core_env_roots_shadow_safe env Ω n R Γ e =
      infer_ok (T, Γ', R', roots) ->
    check_expr_root_shadow_captured_call_provenance_summary
      env Ω n R Γ e = true ->
    exists ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Ω n R (sctx_of_ctx Γ) e T (sctx_of_ctx Γ') R' roots ret_roots.
Proof.
  unfold check_expr_root_shadow_captured_call_provenance_summary,
    infer_core_env_roots_shadow_safe.
  intros env Ω n R Γ e T Γ' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Ω n R
    (sctx_of_ctx Γ) e) as [[[[T0 Σ0] R0] roots0] | err] eqn:Hstate;
    try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_captured_call_provenance_summary_fuel_sound_early;
    eassumption.
Qed.

Lemma check_fn_root_shadow_captured_call_provenance_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_provenance_summary env fdef = true ->
    callee_body_root_shadow_captured_call_provenance_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_provenance_summary in Hcheck.
  destruct (check_fn_root_shadow_non_capturing_call_provenance_summary env fdef)
    eqn:Hold.
  - left. apply check_fn_root_shadow_non_capturing_call_provenance_summary_sound.
    exact Hold.
  - apply orb_true_iff in Hcheck as [Hcheck | Hlocal_check].
    apply orb_true_iff in Hcheck as [Hcheck | Hif_check].
    + right. left.
    destruct (captured_call_target_expr (fn_body fdef))
      as [[[fname captures] args] |] eqn:Htarget; try discriminate.
    apply andb_true_iff in Hcheck as [Hready_args Hrest].
    destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee_head Hrest].
    apply andb_true_iff in Hcallee_head as [Hlt Hdisjoint].
    apply PeanoNat.Nat.eqb_eq in Hlt.
    destruct (check_make_closure_captures_exact_sctx_with_env env
      (fn_outlives fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      captures
      (fn_captures fcallee)) as [[env_lt captured_tys] | err]
      eqn:Hcaptures;
      try discriminate.
    apply andb_true_iff in Hrest as [Hcallee Hsummary].
    destruct (infer_env_roots_shadow_safe env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_check Γ_check] R_out] roots] | err] eqn:Hinfer;
      try discriminate.
    apply andb_true_iff in Hsummary as [Hroots Henv].
    destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
      as [Hin_callee Hname_callee].
    pose proof (infer_env_roots_shadow_safe_sound
                  env fdef
                  (initial_root_env_for_fn fdef)
                  T_check Γ_check R_out roots Hinfer) as Htyped_fn.
    unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
    destruct Htyped_fn as
      (T_body & Γ_out & Htyped & Hcompat & _).
    assert (Hbody :
      fn_body fdef = ECallExpr (EMakeClosure fname captures) args).
    { unfold captured_call_target_expr in Htarget.
      destruct (fn_body fdef); try discriminate.
      destruct e; try discriminate.
      inversion Htarget. reflexivity. }
    exists fname, captures, args, fcallee, env_lt, captured_tys,
      T_body, Γ_out, R_out, roots.
    split; [exact Hbody|].
    split; [reflexivity|].
    split; [apply preservation_ready_args_b_sound; exact Hready_args|].
    split; [exact Hin_callee|].
    split; [exact Hname_callee|].
    split; [exact Hlt|].
    split.
    { apply callee_hidden_capture_args_disjoint_b_sound.
      exact Hdisjoint. }
    split; [exact Hcaptures|].
    split.
    { apply check_fn_root_shadow_captured_callee_provenance_summary_sound.
      exact Hcallee. }
    split.
    { eapply infer_env_roots_shadow_safe_params_nodup. exact Hinfer. }
    split; [exact Htyped|].
    split; [exact Hcompat|].
    split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
    apply fn_params_root_env_excludes_b_sound. exact Henv.
    + right. right. left.
      destruct (fn_body fdef) eqn:Hbody_if; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fdef)
        (fn_lifetimes fdef)
        (initial_root_env_for_fn fdef)
        (fn_body_ctx fdef)
        (EIf e1 e2 e3))
        as [[[[T_body Γ_out] R_body] roots_body] | err]
        eqn:Hcore; try discriminate.
      destruct (infer_env_roots_shadow_safe env fdef
        (initial_root_env_for_fn fdef))
        as [[[[T_env Γ_env] R_env] roots_env] | err]
        eqn:Hinfer_env; try discriminate.
      apply andb_true_iff in Hif_check as [Hif_head Henv].
      apply andb_true_iff in Hif_head as [Hif_head Hroots].
      apply andb_true_iff in Hif_head as [Hexpr Hcompat].
      destruct
        (check_expr_root_shadow_captured_call_provenance_summary_sound_early
          env (fn_outlives fdef) (fn_lifetimes fdef)
          (initial_root_env_for_fn fdef) (fn_body_ctx fdef)
          (EIf e1 e2 e3) T_body Γ_out R_body roots_body Hcore Hexpr)
        as [ret_roots Hexpr_summary].
      exists T_body, Γ_out, R_body, roots_body, ret_roots.
      repeat split.
      * eapply infer_env_roots_shadow_safe_params_nodup.
        exact Hinfer_env.
      * exact Hexpr_summary.
      * exact Hcompat.
      * apply fn_params_roots_exclude_b_sound. exact Hroots.
      * apply fn_params_root_env_excludes_b_sound. exact Henv.
    + right. right. right.
      destruct (local_captured_call_target_expr (fn_body fdef))
        as [[[[[[[[fname captures] args] m] x] T] direct_body]
              let_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hlocal_check as [Hready_args Hrest].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
        eqn:Hlookup_b; try discriminate.
      apply andb_true_iff in Hrest as [Hcallee_head Hrest].
      apply andb_true_iff in Hcallee_head as [Hcallee_head Hnot_cap_name].
      apply andb_true_iff in Hcallee_head as [Hlt Hdisjoint].
      apply PeanoNat.Nat.eqb_eq in Hlt.
      apply negb_true_iff in Hnot_cap_name.
      destruct (check_make_closure_captures_exact_sctx_with_env env
        (fn_outlives fdef)
        (sctx_of_ctx (fn_body_ctx fdef))
        captures
        (fn_captures fcallee)) as [[env_lt captured_tys] | err]
        eqn:Hcaptures;
        try discriminate.
      apply andb_true_iff in Hrest as [Hcallee Hsummary].
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef direct_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_direct_check Γ_direct_check] R_direct] roots_direct] | err]
        eqn:Hinfer_direct; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef let_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_let_check Γ_let_check] R_let] roots_let] | err]
        eqn:Hinfer_let; try discriminate.
      apply andb_true_iff in Hsummary as [Hroots Henv].
      destruct (lookup_fn_b_sound fname (env_fns env) fcallee Hlookup_b)
        as [Hin_callee Hname_callee].
      destruct (local_captured_call_target_expr_sound
                  (fn_body fdef) fname captures args m x T direct_body
                  let_body Htarget)
        as (Hbody & Hdirect & Hlet & Husage & Hnot_caps & Hnot_free &
            Hnot_local).
      pose proof (infer_env_roots_shadow_safe_sound
                    env (fn_with_body fdef direct_body)
                    (initial_root_env_for_fn fdef)
                    T_direct_check Γ_direct_check R_direct roots_direct
                    Hinfer_direct) as Htyped_direct_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_direct_fn.
      destruct Htyped_direct_fn as
        (T_direct_body & Γ_direct_out & Htyped_direct & Hcompat_direct & _).
      cbn in Htyped_direct, Hcompat_direct.
      pose proof (infer_env_roots_shadow_safe_sound
                    env (fn_with_body fdef let_body)
                    (initial_root_env_for_fn fdef)
                    T_let_check Γ_let_check R_let roots_let
                    Hinfer_let) as Htyped_let_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_let_fn.
      destruct Htyped_let_fn as
        (T_let_body & Γ_let_out & Htyped_let & _).
      cbn in Htyped_let.
      exists fname, captures, args, m, x, T, direct_body, let_body,
        fcallee, env_lt, captured_tys, T_direct_body, Γ_direct_out, R_direct,
        roots_direct, T_let_body, Γ_let_out, R_let, roots_let.
      split; [exact Hbody|].
      split; [reflexivity|].
      split; [exact Hdirect|].
      split; [exact Hlet|].
      split; [exact Husage|].
      split; [exact Hnot_caps|].
      split.
      { eapply existsb_ident_eqb_false_notin. exact Hnot_cap_name. }
      split; [exact Hnot_free|].
      split; [exact Hnot_local|].
      split; [apply preservation_ready_args_b_sound; exact Hready_args|].
      split; [exact Hin_callee|].
      split; [exact Hname_callee|].
      split; [exact Hlt|].
      split.
      { apply callee_hidden_capture_args_disjoint_b_sound.
        exact Hdisjoint. }
      split; [exact Hcaptures|].
      split.
      { apply check_fn_root_shadow_captured_callee_provenance_summary_sound.
        exact Hcallee. }
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef direct_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup.
        exact Hinfer_direct. }
      split; [exact Htyped_direct|].
      split; [exact Hcompat_direct|].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots|].
      split; [apply fn_params_root_env_excludes_b_sound; exact Henv|].
      exact Htyped_let.
Qed.

Lemma check_env_root_shadow_summary_ready :
  forall env,
    check_env_root_shadow_summary env = true ->
    env_fns_root_shadow_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_provenance_summary_ready :
  forall env,
    check_env_root_shadow_provenance_summary env = true ->
    env_fns_root_shadow_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_direct_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_direct_call_provenance_summary env = true ->
    env_fns_root_shadow_direct_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_direct_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_direct_call_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_non_capturing_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_non_capturing_call_provenance_summary env = true ->
    env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_non_capturing_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_non_capturing_call_provenance_summary_sound.
  exact Hcheck.
Qed.

Lemma check_env_root_shadow_captured_call_provenance_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_provenance_summary env = true ->
    env_fns_root_shadow_captured_call_provenance_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_provenance_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_provenance_summary_sound.
  exact Hcheck.
Qed.
