From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeGenericDirectFuelRuntimeFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Inductive expr_root_shadow_store_safe_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSS_Exact : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_captured_call_provenance_summary_exact
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots
  | ERSS_FunctionValueCall : forall R Σ x args T_callee Gamma_callee
      R_callee roots_callee T Σ' R' roots,
      preservation_ready_args args ->
      infer_core_env_roots_shadow_safe env Omega n R (ctx_of_sctx Σ)
        (EVar x) = infer_ok
          (T_callee, Gamma_callee, R_callee, roots_callee) ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSS_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSS_If : forall R R1 R2 R3 Σ Σ1 Sigma2 Sigma3 Sigma4
      e1 e2 e3 T_cond T2 T3 roots_cond roots2 roots3 ret_roots2 ret_roots3,
      provenance_ready_expr e1 ->
      typed_env_roots_shadow_safe env Omega n R Σ e1 T_cond Σ1 R1
        roots_cond ->
      ty_core T_cond = TBooleans ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e2 T2 Sigma2 R2 roots2 ret_roots2 ->
      expr_root_shadow_store_safe_summary
        env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 ret_roots3 ->
      ty_core T2 = ty_core T3 ->
      ctx_merge (ctx_of_sctx Sigma2) (ctx_of_sctx Sigma3) = Some Sigma4 ->
      R2 = R3 ->
      expr_root_shadow_store_safe_summary
        env Omega n R Σ (EIf e1 e2 e3)
        (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2))
        (sctx_of_ctx Sigma4) R2 (root_set_union roots2 roots3)
        (root_set_union ret_roots2 ret_roots3).

Lemma expr_root_shadow_store_safe_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - eapply expr_root_shadow_captured_call_provenance_summary_exact_typed.
    exact H.
  - exact H2.
  - eapply TERS_Let; eauto.
  - subst R3. eapply TERS_If; eauto. apply root_env_equiv_refl.
Qed.
Definition callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, synthetic_body) /\
    synthetic_body = ECallGeneric fname type_args args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    preservation_ready_expr
      (subst_type_params_expr type_args (fn_body fcallee)) /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname type_args args T_hidden raw_body synthetic_body fcallee T_body Gamma_out
      R_body roots_body,
    fn_body fdef = raw_body /\
    let_bound_generic_direct_call_target_expr raw_body =
      Some (fname, type_args, args, T_hidden, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    Datatypes.length type_args = fn_type_params fcallee /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fcallee) type_args = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fcallee type_args /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_hidden (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists b fname_then type_args_then args_then fname_else type_args_else
      args_else raw_body synthetic_body fthen felse T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    if_literal_generic_direct_call_target_expr raw_body =
      Some (b, fname_then, type_args_then, args_then,
        fname_else, type_args_else, args_else, synthetic_body) /\
    store_safe_function_value_call_args env args_then /\
    store_safe_function_value_call_args env args_else /\
    In fthen (env_fns env) /\
    fn_name fthen = fname_then /\
    In felse (env_fns env) /\
    fn_name felse = fname_else /\
    Datatypes.length type_args_then = fn_type_params fthen /\
    Datatypes.length type_args_else = fn_type_params felse /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds fthen) type_args_then = None /\
    check_struct_bounds (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_bounds felse) type_args_else = None /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 fthen type_args_then /\
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10000 felse type_args_else /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists x fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_body fdef = raw_body /\
    local_fn_value_call_target_expr_with_binder raw_body =
      Some (x, fname, args, synthetic_body) /\
    store_safe_function_value_call_args env args /\
    ~ In x (args_free_vars_ts args) /\
    ~ In x (args_local_store_names args) /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fcallee /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Definition callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  exists fname args raw_body synthetic_body fcallee T_body Gamma_out R_body
      roots_body,
    fn_captures fdef = [] /\
    fn_body fdef = raw_body /\
    direct_call_target_expr raw_body = Some (fname, args, synthetic_body) /\
    synthetic_body = ECall fname args /\
    store_safe_function_value_call_args env args /\
    In fcallee (env_fns env) /\
    fn_name fcallee = fname /\
    fn_captures fcallee = [] /\
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    typed_env_roots_shadow_safe
      (global_env_with_local_bounds env (fn_bounds fdef))
      (fn_outlives fdef)
      (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma subst_type_params_trait_ref_nil : forall tr,
  subst_type_params_trait_ref [] tr = tr.
Proof.
  intros tr. destruct tr as [name args].
  unfold subst_type_params_trait_ref. simpl.
  rewrite map_subst_type_params_ty_nil. reflexivity.
Qed.

Lemma subst_type_params_trait_bound_nil : forall b,
  subst_type_params_trait_bound [] b = b.
Proof.
  intros b. destruct b as [idx traits].
  unfold subst_type_params_trait_bound. simpl.
  f_equal.
  induction traits as [| tr traits IH]; simpl; auto.
  rewrite subst_type_params_trait_ref_nil, IH. reflexivity.
Qed.

Lemma subst_type_params_trait_bounds_nil : forall bounds,
  subst_type_params_trait_bounds [] bounds = bounds.
Proof.
  induction bounds as [| b bounds IH]; simpl; auto.
  rewrite subst_type_params_trait_bound_nil, IH. reflexivity.
Qed.

Lemma callee_body_root_shadow_captured_call_generic_direct_instantiated_nil_fuel :
  forall env fdef,
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef ->
    callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
      env 10001 fdef [].
Proof.
  intros env fdef Hsummary.
  destruct Hsummary as
    (fname & type_args & args & raw_body & synthetic_body & fcallee &
      T_body & Gamma_out & R_body & roots_body & Hbody & Htarget &
      Hsynthetic & Hsafe & Hin & Hname & Harity & Hbounds & Hcallee_ready &
      Hcallee_summary & Hnodup & Htyped & Hcompat & Hexcl_roots & Hexcl_env).
  eapply CBRSSNI_GenericDirect with
    (raw_body := raw_body) (synthetic_body := synthetic_body)
    (fcallee := fcallee) (T_body := T_body) (Gamma_out := Gamma_out)
    (R_body := R_body) (roots_body := roots_body).
  - rewrite subst_type_params_expr_nil. symmetry. exact Hbody.
  - exact Htarget.
  - exact Hsynthetic.
  - exact Hsafe.
  - exact Hin.
  - exact Hname.
  - exact Harity.
  - rewrite subst_type_params_trait_bounds_nil. exact Hbounds.
  - exact Hcallee_summary.
  - rewrite apply_type_params_nil. exact Hnodup.
  - rewrite subst_type_params_trait_bounds_nil.
    rewrite subst_type_params_ctx_nil.
    exact Htyped.
  - rewrite subst_type_params_ty_nil. exact Hcompat.
  - rewrite apply_type_params_nil. exact Hexcl_roots.
  - rewrite apply_type_params_nil. exact Hexcl_env.
Qed.

Definition callee_body_root_shadow_captured_call_store_safe_summary
    (env : global_env) (fdef : fn_def) : Prop :=
  callee_body_root_shadow_captured_call_provenance_summary env fdef \/
  callee_body_root_shadow_captured_call_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_let_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_generic_direct_if_literal_narrow_store_safe_summary
    env fdef \/
  callee_body_root_shadow_captured_call_local_fn_value_generic_direct_narrow_store_safe_summary
    env fdef \/
  exists T_body Gamma_out R_body roots_body ret_roots,
    NoDup (ctx_names (params_ctx (fn_params fdef))) /\
    expr_root_shadow_store_safe_narrow_summary_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef)
      (sctx_of_ctx (fn_body_ctx fdef))
      (fn_body fdef) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      ret_roots /\
    ty_compatible_b (fn_outlives fdef) T_body (fn_ret fdef) = true /\
    roots_exclude_params (fn_params fdef) roots_body /\
    root_env_excludes_params (fn_params fdef) R_body.

Lemma check_fn_root_shadow_generic_direct_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_generic_direct_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_generic_direct_narrow_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hgeneric.
  unfold check_fn_root_shadow_generic_direct_store_safe_summary in Hgeneric.
  destruct (generic_direct_call_target_expr (fn_body fdef))
    as [[[[fname type_args] args] synthetic_body] |] eqn:Htarget;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Hsafe_args Hgeneric].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
    try discriminate.
  apply andb_true_iff in Hgeneric as [Htype_params Hgeneric].
  apply Nat.eqb_eq in Htype_params.
  destruct (check_struct_bounds
    (global_env_with_local_bounds env (fn_bounds fdef))
    (fn_bounds fcallee) type_args)
    as [bounds_err |] eqn:Hbounds; try discriminate.
  remember (global_env_with_local_bounds env
    (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
    as callee_body_env.
  destruct (infer_core_env_roots_shadow_safe callee_body_env
    (fn_outlives fcallee) (fn_lifetimes fcallee)
    (initial_root_env_for_fn fcallee)
    (subst_type_params_ctx type_args (fn_body_ctx fcallee))
    (subst_type_params_expr type_args (fn_body fcallee)))
    as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
    eqn:Hcallee_core; try discriminate.
  destruct (infer_env_roots_shadow_safe env fcallee
    (initial_root_env_for_fn fcallee))
    as [[[[T_callee_env Gamma_callee_env] R_callee_env]
          roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hgeneric.
  destruct Hgeneric as
    [[[[[[[Hcallee_ready Hcallee_expr] Hcallee_compat] Hcallee_roots]
         Hcallee_env_excl] Hcompat] Hroots] Henv].
  apply lookup_fn_b_sound in Hlookup_b.
  destruct Hlookup_b as [Hin_callee Hname_callee].
  pose proof
    (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
      env fcallee type_args Hcallee_expr) as Hcallee_summary.
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  exists fname, type_args, args, (fn_body fdef), synthetic_body, fcallee,
    T_body_actual, Gamma_out_actual, R_body, roots_body.
  split; [reflexivity |].
  split; [exact Htarget |].
  split.
  { unfold generic_direct_call_target_expr in Htarget.
    destruct (fn_body fdef); try discriminate.
    inversion Htarget. reflexivity. }
  split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
  split; [exact Hin_callee |].
  split; [exact Hname_callee |].
  split; [exact Htype_params |].
  split; [exact Hbounds |].
  split.
  { apply preservation_ready_expr_b_sound. exact Hcallee_ready. }
  split; [exact Hcallee_summary |].
  split.
  { change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
  split; [exact Htyped_body |].
  split; [exact Hcompat_body |].
  split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
  apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef = true ->
    callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary
      env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
    in Hcheck.
  destruct (fn_captures fdef) as [| capture captures] eqn:Hcaptures;
    try discriminate.
  destruct (direct_call_target_expr (fn_body fdef))
    as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
  apply andb_true_iff in Hcheck as [Hsafe_args Hcheck].
  destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
    try discriminate.
  destruct (fn_captures fcallee) as [| callee_capture callee_captures]
    eqn:Hcallee_captures; try discriminate.
  destruct (infer_env_roots_shadow_safe env
    (fn_with_body fdef synthetic_body)
    (initial_root_env_for_fn fdef))
    as [[[[T_body Gamma_body] R_body] roots_body] | err]
    eqn:Hbody_env; try discriminate.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hcompat Hroots] Henv].
  apply lookup_fn_b_sound in Hlookup_b.
  destruct Hlookup_b as [Hin_callee Hname_callee].
  pose proof (infer_env_roots_shadow_safe_sound env
    (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
    T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
  unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
  destruct Htyped_fn as
    (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
  exists fname, args, (fn_body fdef), synthetic_body, fcallee,
    T_body_actual, Gamma_out_actual, R_body, roots_body.
  split; [exact Hcaptures |].
  split; [reflexivity |].
  split; [exact Htarget |].
  split.
  { unfold direct_call_target_expr in Htarget.
    destruct (fn_body fdef); try discriminate.
    - inversion Htarget. reflexivity.
    - destruct e; try discriminate.
      inversion Htarget. reflexivity. }
  split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
  split; [exact Hin_callee |].
  split; [exact Hname_callee |].
  split; [exact Hcallee_captures |].
  split.
  { change (NoDup
      (ctx_names
        (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
    eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
  split; [exact Htyped_body |].
  split; [exact Hcompat_body |].
  split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
  apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Lemma check_fn_root_shadow_captured_call_store_safe_summary_sound :
  forall env fdef,
    check_fn_root_shadow_captured_call_store_safe_summary env fdef = true ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.
Proof.
  intros env fdef Hcheck.
  unfold check_fn_root_shadow_captured_call_store_safe_summary in Hcheck.
  apply orb_true_iff in Hcheck as [Hprefix_local | Hnarrow].
  - apply orb_true_iff in Hprefix_local as [Hprefix_if | Hlocal].
    { apply orb_true_iff in Hprefix_if as [Hprefix_let | Hif].
      - apply orb_true_iff in Hprefix_let as [Hprefix | Hlet].
        + apply orb_true_iff in Hprefix as [Hhead | Hgeneric].
      { apply orb_true_iff in Hhead as [Hold | Hdirect].
        * left. apply check_fn_root_shadow_captured_call_provenance_summary_sound.
        exact Hold.
        * right. left.
      destruct (direct_call_target_expr (fn_body fdef))
        as [[[fname args] synthetic_body] |] eqn:Htarget; try discriminate.
      apply andb_true_iff in Hdirect as [Hready_args Hdirect].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hdirect.
      destruct Hdirect as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      destruct (check_expr_root_shadow_store_safe_narrow_summary_sound
        env (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee) (fn_body_ctx fcallee)
        (fn_body fcallee) T_callee Gamma_callee R_callee roots_callee
        Hcallee_core Hcallee_expr) as [ret_roots_callee Hcallee_summary].
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split.
      { unfold direct_call_target_expr in Htarget.
        destruct (fn_body fdef); try discriminate.
        - inversion Htarget. reflexivity.
        - destruct e; try discriminate.
          inversion Htarget. reflexivity. }
      split; [apply store_safe_function_value_call_args_b_sound; exact Hready_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split.
      { exists T_callee, Gamma_callee, R_callee, roots_callee,
          ret_roots_callee.
        repeat split.
        - eapply infer_env_roots_shadow_safe_params_nodup.
          exact Hcallee_env.
        - exact Hcallee_summary.
        - exact Hcallee_compat.
        - apply fn_params_roots_exclude_b_sound. exact Hcallee_roots.
        - apply fn_params_root_env_excludes_b_sound. exact Hcallee_env_excl. }
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      }
      { right. right. left.
        eapply check_fn_root_shadow_generic_direct_store_safe_summary_sound.
        exact Hgeneric.
      }
        + right. right. right. left.
      destruct (let_bound_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[fname type_args] args] T_hidden] synthetic_body] |]
        eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hlet as [Hsafe_args Hlet].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |] eqn:Hlookup_b;
        try discriminate.
      apply andb_true_iff in Hlet as [Htype_params Hlet].
      apply Nat.eqb_eq in Htype_params.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fcallee) type_args)
        as [bounds_err |] eqn:Hbounds; try discriminate.
      remember (global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args (fn_bounds fcallee)))
        as callee_body_env.
      destruct (infer_core_env_roots_shadow_safe callee_body_env
        (fn_outlives fcallee) (fn_lifetimes fcallee)
        (initial_root_env_for_fn fcallee)
        (subst_type_params_ctx type_args (fn_body_ctx fcallee))
        (subst_type_params_expr type_args (fn_body fcallee)))
        as [[[[T_callee Gamma_callee] R_callee] roots_callee] | err]
        eqn:Hcallee_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fcallee
        (initial_root_env_for_fn fcallee))
        as [[[[T_callee_env Gamma_callee_env] R_callee_env]
              roots_callee_env] | err] eqn:Hcallee_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlet.
      destruct Hlet as
        [[[[[[Hcallee_expr Hcallee_compat] Hcallee_roots]
             Hcallee_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fcallee type_args Hcallee_expr) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists fname, type_args, args, T_hidden, (fn_body fdef), synthetic_body,
        fcallee, T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Htype_params |].
      split; [exact Hbounds |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
      - right. right. right. right. left.
      destruct (if_literal_generic_direct_call_target_expr (fn_body fdef))
        as [[[[[[[[b fname_then] type_args_then] args_then] fname_else]
                type_args_else] args_else] synthetic_body] |] eqn:Htarget;
        try discriminate.
      apply andb_true_iff in Hif as [Hsafes Hif].
      apply andb_true_iff in Hsafes as [Hsafe_then Hsafe_else].
      destruct (lookup_fn_b fname_then (env_fns env)) as [fthen |]
        eqn:Hlookup_then; try discriminate.
      destruct (lookup_fn_b fname_else (env_fns env)) as [felse |]
        eqn:Hlookup_else; try discriminate.
      apply andb_true_iff in Hif as [Htype_params_pair Hif].
      apply andb_true_iff in Htype_params_pair as
        [Htype_params_then Htype_params_else].
      apply Nat.eqb_eq in Htype_params_then.
      apply Nat.eqb_eq in Htype_params_else.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds fthen) type_args_then) as [bounds_then |]
        eqn:Hbounds_then; try discriminate.
      destruct (check_struct_bounds
        (global_env_with_local_bounds env (fn_bounds fdef))
        (fn_bounds felse) type_args_else) as [bounds_else |]
        eqn:Hbounds_else; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives fthen) (fn_lifetimes fthen)
        (initial_root_env_for_fn fthen)
        (subst_type_params_ctx type_args_then (fn_body_ctx fthen))
        (subst_type_params_expr type_args_then (fn_body fthen)))
        as [[[[T_then Gamma_then] R_then] roots_then] | err]
        eqn:Hthen_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env fthen
        (initial_root_env_for_fn fthen))
        as [[[[T_then_env Gamma_then_env] R_then_env]
              roots_then_env] | err] eqn:Hthen_env; try discriminate.
      destruct (infer_core_env_roots_shadow_safe env
        (fn_outlives felse) (fn_lifetimes felse)
        (initial_root_env_for_fn felse)
        (subst_type_params_ctx type_args_else (fn_body_ctx felse))
        (subst_type_params_expr type_args_else (fn_body felse)))
        as [[[[T_else Gamma_else] R_else] roots_else] | err]
        eqn:Helse_core; try discriminate.
      destruct (infer_env_roots_shadow_safe env felse
        (initial_root_env_for_fn felse))
        as [[[[T_else_env Gamma_else_env] R_else_env]
              roots_else_env] | err] eqn:Helse_env; try discriminate.
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hif.
      destruct Hif as
        [[[[[[[[[[Hthen_expr Hthen_compat] Hthen_roots]
                Hthen_env_excl] Helse_expr] Helse_compat] Helse_roots]
            Helse_env_excl] Hcompat] Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_then.
      destruct Hlookup_then as [Hin_then Hname_then].
      apply lookup_fn_b_sound in Hlookup_else.
      destruct Hlookup_else as [Hin_else Hname_else].
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env fthen type_args_then Hthen_expr) as Hthen_summary.
      pose proof
        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_sound
          env felse type_args_else Helse_expr) as Helse_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists b, fname_then, type_args_then, args_then, fname_else,
        type_args_else, args_else, (fn_body fdef), synthetic_body, fthen,
        felse, T_body_actual, Gamma_out_actual, R_body, roots_body.
      repeat split; try reflexivity; try eassumption;
        try (apply store_safe_function_value_call_args_b_sound; eassumption);
        try (apply fn_params_roots_exclude_b_sound; eassumption);
        try (apply fn_params_root_env_excludes_b_sound; eassumption).
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
    }
    { right. right. right. right. right. left.
      destruct (local_fn_value_call_target_expr_with_binder (fn_body fdef))
        as [[[[x fname] args] synthetic_body] |] eqn:Htarget; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[[Hsafe_args Hnot_free_b] Hnot_local_b] Hlocal].
      destruct (lookup_fn_b fname (env_fns env)) as [fcallee |]
        eqn:Hlookup_b; try discriminate.
      apply andb_true_iff in Hlocal as [Hcallee_generic Hlocal].
      destruct (infer_env_roots_shadow_safe env
        (fn_with_body fdef synthetic_body)
        (initial_root_env_for_fn fdef))
        as [[[[T_body Gamma_body] R_body] roots_body] | err]
        eqn:Hbody_env; try discriminate.
      repeat rewrite andb_true_iff in Hlocal.
      destruct Hlocal as [[Hcompat Hroots] Henv].
      apply lookup_fn_b_sound in Hlookup_b.
      destruct Hlookup_b as [Hin_callee Hname_callee].
      pose proof
        (check_fn_root_shadow_generic_direct_store_safe_summary_sound
          env fcallee Hcallee_generic) as Hcallee_summary.
      pose proof (infer_env_roots_shadow_safe_sound env
        (fn_with_body fdef synthetic_body) (initial_root_env_for_fn fdef)
        T_body Gamma_body R_body roots_body Hbody_env) as Htyped_fn.
      unfold typed_fn_env_roots_shadow_safe in Htyped_fn.
      destruct Htyped_fn as
        (T_body_actual & Gamma_out_actual & Htyped_body & Hcompat_body & _).
      exists x, fname, args, (fn_body fdef), synthetic_body, fcallee,
        T_body_actual, Gamma_out_actual, R_body, roots_body.
      split; [reflexivity |].
      split; [exact Htarget |].
      split; [apply store_safe_function_value_call_args_b_sound; exact Hsafe_args |].
      split.
      { rewrite <- args_free_vars_checker_eq.
        apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_free_b. }
      split.
      { apply ident_in_b_false_not_in. apply negb_true_iff.
        exact Hnot_local_b. }
      split; [exact Hin_callee |].
      split; [exact Hname_callee |].
      split; [exact Hcallee_summary |].
      split.
      { change (NoDup
          (ctx_names
            (params_ctx (fn_params (fn_with_body fdef synthetic_body))))).
        eapply infer_env_roots_shadow_safe_params_nodup. exact Hbody_env. }
      split; [exact Htyped_body |].
      split; [exact Hcompat_body |].
      split; [apply fn_params_roots_exclude_b_sound; exact Hroots |].
      apply fn_params_root_env_excludes_b_sound. exact Henv.
    }
  - right. right. right. right. right. right.
    destruct (infer_core_env_roots_shadow_safe_checked env
      (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef))
      as [[[[T_body Gamma_body] R_body] roots_body] | err] eqn:Hcore;
      try discriminate.
    destruct (infer_env_roots_shadow_safe_checked env fdef
      (initial_root_env_for_fn fdef))
      as [[[[T_env Gamma_env] R_env] roots_env] | err] eqn:Hinfer_env;
      try discriminate.
    repeat rewrite andb_true_iff in Hnarrow.
    destruct Hnarrow as [[[Hexpr Hcompat] Hroots] Henv].
    destruct (check_expr_root_shadow_store_safe_narrow_summary_checked_sound
      env (fn_outlives fdef) (fn_lifetimes fdef)
      (initial_root_env_for_fn fdef) (fn_body_ctx fdef) (fn_body fdef)
      T_body Gamma_body R_body roots_body Hcore Hexpr)
      as [ret_roots Hsummary].
    exists T_body, Gamma_body, R_body, roots_body, ret_roots.
    repeat split.
    + eapply infer_env_roots_shadow_safe_checked_params_nodup.
      exact Hinfer_env.
    + exact Hsummary.
    + exact Hcompat.
    + apply fn_params_roots_exclude_b_sound. exact Hroots.
    + apply fn_params_root_env_excludes_b_sound. exact Henv.
Qed.

Definition env_fns_root_shadow_captured_call_store_safe_summary_check_ready
    (env : global_env) : Prop :=
  forall fname fdef,
    lookup_fn fname (env_fns env) = Some fdef ->
    callee_body_root_shadow_captured_call_store_safe_summary env fdef.

Lemma check_env_root_shadow_captured_call_store_safe_summary_ready :
  forall env,
    check_env_root_shadow_captured_call_store_safe_summary env = true ->
    env_fns_root_shadow_captured_call_store_safe_summary_check_ready env.
Proof.
  intros env Hcheck fname fdef Hlookup.
  unfold check_env_root_shadow_captured_call_store_safe_summary in Hcheck.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  apply forallb_forall with (x := fdef) in Hcheck; [| exact Hin].
  apply check_fn_root_shadow_captured_call_store_safe_summary_sound.
  exact Hcheck.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_fuel_sound :
  forall fuel env Omega n R Σ e T Σ' R' roots,
    infer_core_env_state_fuel_roots_shadow_safe fuel env Omega n R Σ e =
      infer_ok (T, Σ', R', roots) ->
    check_expr_root_shadow_store_safe_summary_fuel
      fuel env Omega n R Σ e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R Σ e T Σ' R' roots ret_roots.
Proof.
  induction fuel as [| fuel' IH]; intros env Omega n R Σ e T Σ' R'
    roots Hinfer Hcheck.
  - simpl in Hinfer. discriminate.
  - cbn [check_expr_root_shadow_store_safe_summary_fuel] in Hcheck.
    rewrite Hinfer in Hcheck.
    repeat (apply orb_true_iff in Hcheck as [Hcheck | Hcheck]).
    + destruct (check_expr_root_shadow_captured_call_provenance_summary_fuel_sound
        (S fuel') env Omega n R Σ e T Σ' R' roots Hinfer Hcheck)
        as [ret_roots Hexact].
      exists ret_roots. apply ERSS_Exact. exact Hexact.
    + destruct e; try discriminate.
      apply andb_true_iff in Hcheck as [Hready_args Hsupported].
      pose proof
        (check_supported_non_type_generic_function_value_call_expr_sound
          env Omega n R (ctx_of_sctx Σ) e l Hsupported)
        as Hsupported_prop.
      destruct Hsupported_prop as
        (x & T_callee & Gamma_callee & R_callee & roots_callee &
         Hcallee & _ & Hinfer_callee & Hcallee_shape).
      subst e.
      exists roots.
      eapply ERSS_FunctionValueCall.
      * apply preservation_ready_args_b_sound. exact Hready_args.
      * exact Hinfer_callee.
      * exact Hcallee_shape.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hinfer.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T1 Σ1] R1] roots1] | err] eqn:Hbound;
        try discriminate.
      destruct (ty_compatible_b Omega T1 t) eqn:Hcompat;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Hcheck].
      destruct (IH env Omega n R Σ e1 T1 Σ1 R1 roots1 Hbound Hhead)
        as [ret_roots1 Hbound_summary].
      destruct (root_env_lookup i R1) as [roots_x |] eqn:Hlookup_x;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hfresh Hcheck].
      apply andb_true_iff in Hfresh as [Hroots1 Henv1].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n
        (root_env_add i roots1 R1) (sctx_add i t m Σ1) e2)
        as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hbody;
        try discriminate.
      repeat rewrite andb_true_iff in Hcheck.
      destruct Hcheck as [[[[Hfreei_ret Hsctx_oki] Hroots2i] Henv2i]
        Hbody_check].
      destruct (IH env Omega n (root_env_add i roots1 R1)
        (sctx_add i t m Σ1) e2 T2i Sigma2i R2i roots2i Hbody
        Hbody_check) as [ret_roots Hbody_summary].
      simpl in Hinfer.
      rewrite Hroots1, Henv1, Hsctx_oki, Hroots2i, Henv2i in Hinfer.
      inversion Hinfer; subst; clear Hinfer.
      exists ret_roots.
      eapply ERSS_Let.
      * exact Hbound_summary.
      * exact Hcompat.
      * exact Hlookup_x.
      * apply roots_exclude_b_sound. exact Hroots1.
      * apply root_env_excludes_b_sound. exact Henv1.
      * exact Hbody_summary.
      * exact Hfreei_ret.
      * exact Hsctx_oki.
      * apply roots_exclude_b_sound. exact Hroots2i.
      * apply root_env_excludes_b_sound. exact Henv2i.
    + destruct e; try discriminate.
      simpl in Hinfer, Hcheck.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R
        Σ e1) as [[[[T_cond Σ1] R1] roots_cond] | err]
        eqn:Hcond; try discriminate.
      destruct (ty_core_eqb (ty_core T_cond) TBooleans) eqn:Hcond_core;
        try discriminate.
      apply andb_true_iff in Hcheck as [Hhead Helse_check].
      apply andb_true_iff in Hhead as [Hhead Hthen_check].
      apply andb_true_iff in Hhead as [Hcond_bool Hready_cond].
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e2) as [[[[T2i Sigma2i] R2i] roots2i] | err] eqn:Hthen;
        try discriminate.
      destruct (infer_core_env_state_fuel_roots_shadow_safe fuel' env Omega n R1
        Σ1 e3) as [[[[T3 Sigma3] R3] roots3] | err] eqn:Helse;
        try discriminate.
      destruct (ty_core_eqb (ty_core T2i) (ty_core T3))
        eqn:Hbranch_core; try discriminate.
      destruct (root_env_eqb R2i R3) eqn:Hroot_eq; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Sigma2i) (ctx_of_sctx Sigma3))
        as [Sigma4 |] eqn:Hmerge; try discriminate.
      destruct (IH env Omega n R1 Σ1 e2 T2i Sigma2i R2i roots2i Hthen
        Hthen_check) as [ret_roots2i Hthen_summary].
      destruct (IH env Omega n R1 Σ1 e3 T3 Sigma3 R3 roots3 Helse
        Helse_check) as [ret_roots3 Helse_summary].
      inversion Hinfer; subst; clear Hinfer.
      exists (root_set_union ret_roots2i ret_roots3).
      eapply ERSS_If.
      * apply provenance_ready_expr_b_sound. exact Hready_cond.
      * eapply infer_core_env_state_fuel_roots_shadow_safe_sound.
        exact Hcond.
      * apply ty_core_eqb_true. exact Hcond_core.
      * exact Hthen_summary.
      * exact Helse_summary.
      * apply ty_core_eqb_true. exact Hbranch_core.
      * exact Hmerge.
      * apply root_env_eqb_true. exact Hroot_eq.
Qed.

Lemma check_expr_root_shadow_store_safe_summary_sound :
  forall env Omega n R Gamma e T Gamma' R' roots,
    infer_core_env_roots_shadow_safe env Omega n R Gamma e =
      infer_ok (T, Gamma', R', roots) ->
    check_expr_root_shadow_store_safe_summary
      env Omega n R Gamma e = true ->
    exists ret_roots,
      expr_root_shadow_store_safe_summary
        env Omega n R (sctx_of_ctx Gamma) e T (sctx_of_ctx Gamma') R'
        roots ret_roots.
Proof.
  unfold check_expr_root_shadow_store_safe_summary,
    infer_core_env_roots_shadow_safe.
  intros env Omega n R Gamma e T Gamma' R' roots Hinfer Hcheck.
  destruct (infer_core_env_state_fuel_roots_shadow_safe 10000 env Omega n R
    (sctx_of_ctx Gamma) e) as [[[[T0 Sigma0] R0] roots0] | err]
    eqn:Hstate; try discriminate.
  inversion Hinfer; subst.
  eapply check_expr_root_shadow_store_safe_summary_fuel_sound;
    eassumption.
Qed.

