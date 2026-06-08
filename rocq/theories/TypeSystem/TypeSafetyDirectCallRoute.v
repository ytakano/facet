From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness
  CheckerRootSidecars.
From Facet.TypeSystem Require Export TypeSafetyDirectCallEvidence
  TypeSafetyStoreSafeFunctionValueCallFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition eval_preserves_typing_roots_synthetic_direct_call_ready_statement : Prop :=
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
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

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

Definition eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement
    : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_direct_call_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.

Definition eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_ready_args args ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.

Definition eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.

Definition eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_ready_args args ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.

Definition eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement
    : Prop :=
  forall env s fname args s' v,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.

Definition eval_preserves_synthetic_direct_call_ready_summary_call_package_statement
    : Prop :=
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement /\
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement.

Definition eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement
    : Prop :=
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement /\
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement.

Lemma eval_preserves_synthetic_direct_call_ready_summary_call_package_prefix :
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement.
Proof.
  intros [Hprefix _]. exact Hprefix.
Qed.

Lemma eval_preserves_synthetic_direct_call_ready_summary_call_package_scope :
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement.
Proof.
  intros [_ Hscope]. exact Hscope.
Qed.

Lemma eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement_of_prefix :
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement.
Proof.
  intros Hprefix env s fname args s' v Heval Ω n R Σ T Σ' R' roots
    Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
    Hsummary Hbridge.
  eapply Hprefix; try eassumption.
  eapply store_typed_prefix_exact. exact Hstore.
Qed.

Lemma eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_prefix :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement.
Proof.
  intros Hscope env s fname args s' v Heval Ω n R Σ T Σ' R' roots
    ps frame Hready_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
    Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
  eapply Hscope; try eassumption.
  eapply store_typed_prefix_exact. exact Hstore.
Qed.

Lemma eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_prefix :
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement.
Proof.
  intros Hpackage. split.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement_of_prefix.
    exact (eval_preserves_synthetic_direct_call_ready_summary_call_package_prefix
      Hpackage).
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_prefix.
    exact (eval_preserves_synthetic_direct_call_ready_summary_call_package_scope
      Hpackage).
Qed.

Lemma eval_args_preserves_root_names_keys_ready_prefix_ctx :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  forall env s args s_args vs
      (Ω : outlives_ctx) (n : nat) R Σ ps Σ_args R_args arg_roots,
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed_prefix env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_keys_named R Σ ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots /\
    root_env_store_keys_named R_args s_args.
Proof.
  intros Hprefix_ready env s args s_args vs Ω n R Σ ps Σ_args R_args
    arg_roots Heval_args Hready_args Hstore Hroots Hshadow Hrn Hctx_roots
    Hctx_keys Htyped_args.
  destruct (proj1 (proj2 Hprefix_ready)
              env s args s_args vs Heval_args Ω n R Σ ps Σ_args R_args
              arg_roots Hready_args Hstore Hroots Hshadow Hrn Htyped_args)
    as [Hstore_args _].
  destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Ω n))
              R Σ args ps Σ_args R_args arg_roots Htyped_args Hrn
              Hctx_roots)
    as [_ Harg_roots_ctx_named].
  pose proof (proj1 (proj2 (typed_roots_ctx_keys_named_mutual env Ω n))
                R Σ args ps Σ_args R_args arg_roots Htyped_args Hrn
                Hctx_keys) as Hctx_keys_args.
  split.
  - clear Htyped_args.
    induction Harg_roots_ctx_named as [| roots_i rest Hctx_named_i _ IH].
    + constructor.
    + constructor.
      * eapply root_set_ctx_roots_named_store_typed_prefix; eassumption.
      * exact IH.
  - eapply root_env_ctx_keys_named_store_typed_prefix; eassumption.
Qed.

Definition preservation_ready_expr_static_runtime_named_statement : Prop :=
  forall env s e (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
    preservation_ready_expr e ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_roots_within R' s /\
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s /\
    root_env_store_keys_named R' s.

Lemma root_env_lookup_store_roots_named_direct_route :
  forall R s x roots,
    root_env_store_roots_named R s ->
    root_env_lookup x R = Some roots ->
    root_set_store_roots_named roots s.
Proof.
  unfold root_env_store_roots_named, root_set_store_roots_named.
  intros R s x roots Hnamed Hlookup z Hin.
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_store_roots_named_single_of_store_roots_within_direct_route :
  forall R s x,
    store_roots_within R s ->
    In x (store_names s) ->
    root_set_store_roots_named [RStore x] s.
Proof.
  intros R s x Hwithin Hin.
  destruct (store_roots_within_name_lookup_some R s x Hwithin Hin) as [_ _].
  apply root_set_store_roots_named_single. exact Hin.
Qed.

Lemma root_env_store_keys_named_update_env_direct_route :
  forall R s x roots,
    root_env_store_keys_named R s ->
    root_env_store_keys_named (root_env_update x roots R) s.
Proof.
  unfold root_env_store_keys_named.
  intros R s x roots Hkeys.
  apply root_env_keys_named_update. exact Hkeys.
Qed.

Lemma place_borrow_roots_store_roots_named_direct_route :
  forall R s p roots,
    root_env_store_roots_named R s ->
    root_set_store_roots_named (root_of_place p) s ->
    place_borrow_roots R p = Some roots ->
    root_set_store_roots_named roots s.
Proof.
  intros R s p roots Henv Hplace Hborrow.
  unfold place_borrow_roots in Hborrow.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - inversion Hborrow; subst roots. exact Hplace.
  - assert (Hlookup :
      root_env_lookup (root_provenance_place_name p) R = Some roots).
    { rewrite <- (place_root_lookup_indirect R p Hpath). exact Hborrow. }
    eapply root_env_lookup_store_roots_named_direct_route; eassumption.
Qed.

Lemma resolve_root_set_fuel_store_roots_named_direct_route :
  forall fuel R s roots out,
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    resolve_root_set_fuel fuel R roots = Some out ->
    root_set_store_roots_named out s.
Proof.
  induction fuel as [| fuel IH]; intros R s roots out Henv Hroots Hres;
    simpl in Hres; try discriminate.
  destruct (singleton_store_root roots) as [x |] eqn:Hsingle.
  - destruct (root_env_lookup x R) as [env_roots |] eqn:Hlookup.
    + assert (Henv_roots : root_set_store_roots_named env_roots s)
        by (eapply root_env_lookup_store_roots_named_direct_route;
            eassumption).
      destruct (singleton_store_root env_roots) as [y |] eqn:Henv_single.
      * destruct (ident_eqb x y) eqn:Hxy.
        -- inversion Hres; subst out. exact Hroots.
        -- eapply IH; eassumption.
      * eapply IH; eassumption.
    + inversion Hres; subst out. exact Hroots.
  - inversion Hres; subst out. exact Hroots.
Qed.

Lemma place_resolved_roots_store_roots_named_direct_route :
  forall R s p roots,
    root_env_store_roots_named R s ->
    root_set_store_roots_named (root_of_place p) s ->
    place_resolved_roots R p = Some roots ->
    root_set_store_roots_named roots s.
Proof.
  intros R s p roots Henv Hplace Hresolved.
  unfold place_resolved_roots in Hresolved.
  destruct (place_borrow_roots R p) as [borrow_roots |] eqn:Hborrow;
    try discriminate.
  assert (Hborrow_named : root_set_store_roots_named borrow_roots s).
  { eapply place_borrow_roots_store_roots_named_direct_route; eassumption. }
  unfold resolve_root_set in Hresolved.
  eapply resolve_root_set_fuel_store_roots_named_direct_route; eassumption.
Qed.

Inductive preservation_ready_expr_static_runtime_named_leaf : expr -> Prop :=
  | PRSRN_Unit :
      preservation_ready_expr_static_runtime_named_leaf EUnit
  | PRSRN_Lit : forall lit,
      preservation_ready_expr_static_runtime_named_leaf (ELit lit)
  | PRSRN_Var : forall x,
      preservation_ready_expr_static_runtime_named_leaf (EVar x)
  | PRSRN_Fn : forall fname,
      preservation_ready_expr_static_runtime_named_leaf (EFn fname)
  | PRSRN_Place : forall p x path,
      place_path p = Some (x, path) ->
      preservation_ready_expr_static_runtime_named_leaf (EPlace p).

Lemma preservation_ready_expr_static_runtime_named_leaf_complete :
  forall env s e (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
    preservation_ready_expr_static_runtime_named_leaf e ->
    preservation_ready_expr e ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_roots_within R' s /\
    root_env_store_roots_named R' s /\
    root_set_store_roots_named roots s /\
    root_env_store_keys_named R' s.
Proof.
  intros env s e Ω n R Σ T Σ' R' roots Hleaf Hready Htyped _ Hwithin
    Hnamed Hkeys.
  inversion Hleaf; subst; inversion Htyped; subst;
    repeat split; try assumption; try apply root_set_store_roots_named_nil;
    try (eapply root_env_lookup_store_roots_named_direct_route; eassumption).
Qed.

Lemma root_env_store_roots_named_direct_route_store_names_eq :
  forall R s s',
    store_names s' = store_names s ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  unfold root_env_store_roots_named.
  intros R s s' Hnames Hnamed x roots z Hlookup Hin.
  rewrite Hnames. eapply Hnamed; eassumption.
Qed.

Lemma root_set_store_roots_named_direct_route_store_names_eq :
  forall roots s s',
    store_names s' = store_names s ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  unfold root_set_store_roots_named.
  intros roots s s' Hnames Hnamed z Hin.
  rewrite Hnames. eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_direct_route_store_names_eq :
  forall R s s',
    store_names s' = store_names s ->
    root_env_store_keys_named R s ->
    root_env_store_keys_named R s'.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R s s' Hnames Hkeys x Hin.
  rewrite Hnames. eapply Hkeys; eassumption.
Qed.

Lemma typed_args_roots_preservation_ready_static_runtime_named :
  preservation_ready_expr_static_runtime_named_statement ->
  forall env s args (Ω : outlives_ctx) (n : nat) R Σ ps Σ_args R_args
      arg_roots,
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    root_env_no_shadow R ->
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_roots_within R_args s /\
    root_env_store_roots_named R_args s /\
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots /\
    root_env_store_keys_named R_args s.
Proof.
  intros Hexpr env s args Ω n R Σ ps Σ_args R_args arg_roots Hready
    Htyped Hrn Hwithin Hnamed Hkeys.
  revert Hready Hrn Hwithin Hnamed Hkeys.
  induction Htyped as
    [R0 Σ0
    | R0 R1 R2 Σ0 Σ1 Σ2 e es p ps0 T_e roots roots_rest
        Htyped_e Hcompat Htyped_rest IH];
    intros Hready Hrn Hwithin Hnamed Hkeys.
  - dependent destruction Hready.
    repeat split; try constructor; assumption.
  - dependent destruction Hready.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    destruct (Hexpr env s e Ω n R0 Σ0 T_e Σ1 R1 roots H
                Htyped_e Hrn Hwithin Hnamed Hkeys)
      as [Hwithin1 [Hnamed1 [Hroots_named Hkeys1]]].
    destruct (IH Hready Hrn1 Hwithin1 Hnamed1 Hkeys1)
      as [Hwithin2 [Hnamed2 [Hroots_rest_named Hkeys2]]].
    repeat split; try assumption.
    constructor; assumption.
Qed.

Lemma eval_args_preserves_root_names_keys_preservation_ready_runtime_with_static_expr :
  preservation_ready_expr_static_runtime_named_statement ->
  forall env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots,
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    root_env_no_shadow R ->
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    typed_args_roots env Ω n R Σ args ps Σ_args R_args arg_roots ->
    root_env_store_roots_named R_args s_args /\
    Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots /\
    root_env_store_keys_named R_args s_args.
Proof.
  intros Hexpr env s args s_args vs Ω n R Σ ps Σ_args R_args arg_roots
    Heval_args Hready Hrn Hwithin Hnamed Hkeys Htyped.
  pose proof (proj1 (proj2 preservation_ready_eval_store_names_mutual)
                env s args s_args vs Heval_args Hready) as Hnames.
  destruct (typed_args_roots_preservation_ready_static_runtime_named
              Hexpr env s args Ω n R Σ ps Σ_args R_args arg_roots
              Hready Htyped Hrn Hwithin Hnamed Hkeys)
    as [_ [Hnamed_args [Hroots_named Hkeys_args]]].
  repeat split.
  - eapply root_env_store_roots_named_direct_route_store_names_eq;
      eassumption.
  - eapply Forall_impl; [| exact Hroots_named].
    intros roots Hroot_named.
    eapply root_set_store_roots_named_direct_route_store_names_eq;
      eassumption.
  - eapply root_env_store_keys_named_direct_route_store_names_eq;
      eassumption.
Qed.

Lemma eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement_of_call_statement :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement.
Proof.
  intros Hprefix_ready Hcall env s e s' v Heval Ω n R Σ T Σ' R' roots
    Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hevidence.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    exact (proj1 Hprefix_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots Hprov Hstore Hroots Hshadow Hrn Htyped).
  - eapply Hcall; eassumption.
Qed.

Lemma eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement_of_call_statement :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement.
Proof.
  intros Hframe_ready Hparam_ready Hcall env s e s' v Heval Ω n R Σ T Σ'
    R' roots ps frame Hready Htyped Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    destruct (proj1 Hframe_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots ps frame Hprov Htyped Hcover Hroots Hshadow Hrn Hframe Hfresh)
      as [_ [_ [_ [_ [Hframe' _]]]]].
    destruct (proj1 Hparam_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots ps frame Hprov Htyped Hcover Hparam) as [frame' Hparam'].
    split; [exact Hframe' | exists frame'; exact Hparam'].
  - eapply Hcall; eassumption.
Qed.


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

Lemma direct_call_target_expr_same_is_call :
  forall raw_body fname args,
    direct_call_target_expr raw_body = Some (fname, args, raw_body) ->
    raw_body = ECall fname args.
Proof.
  intros raw_body fname args Htarget.
  unfold direct_call_target_expr in Htarget.
  destruct raw_body; try discriminate.
  - inversion Htarget. reflexivity.
  - destruct raw_body; try discriminate.
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

Lemma eval_synthetic_direct_call_body_scope_inputs_from_ready_evidence :
  eval_preserves_typing_ready_mutual_statement ->
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
    preservation_ready_args args ->
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
      eval (global_env_with_local_bounds env (fn_bounds fcall))
        (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret /\
      eval_args_values_have_types env Ω s_args vs (fn_params fcall) /\
      store_roots_within
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (bind_params (fn_params fcall) vs s_args) /\
      store_no_shadow (bind_params (fn_params fcall) vs s_args) /\
      root_env_no_shadow
        (call_param_root_env (fn_params fcall) arg_roots R_args) /\
      root_env_covers_params (fn_params fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args) /\
      store_frame_scope (fn_params fcall)
        (sctx_of_ctx (params_ctx (fn_params fcall)))
        (bind_params (fn_params fcall) vs s_args) s_args /\
      store_frame_static_fresh
        (sctx_of_ctx (params_ctx (fn_params fcall))) s_args /\
      store_param_scope (fn_params fcall)
        (bind_params (fn_params fcall) vs s_args) s_args.
Proof.
  intros Htyping_ready env Ω n R Σ Σ_args R_args arg_roots fname args fdef
    fcall σ s s_args s_body vs ret used' Hevidence Hin Hfname Hcaps
    Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename Heval_body.
  destruct
    (eval_synthetic_direct_call_body_from_ready_evidence
      env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ s s_args
      s_body vs ret used' Hevidence Hin Hfname Hcaps Htyped_args Heval_args
      Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename Heval_body)
    as (fname_body & args_body & synthetic_body & T_body & Γ_out &
        R_body & roots_body & Htarget & Hsynthetic & Hready_body &
        Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Heval_synthetic).
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  destruct
    (eval_args_bind_params_call_param_root_env_ready
      env s args s_args vs Ω n R Σ
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots
      (fn_params fcall) Heval_args Hprov_args Htyped_args Hroots Hshadow Hrn
      Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]].
  assert (Heval_synthetic_body_env :
    eval (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_synthetic. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh
      (sctx_of_ctx (params_ctx (fn_params fcall))) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  assert (Hscope_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  exists fname_body, args_body, synthetic_body, T_body, Γ_out, R_body,
    roots_body.
  repeat split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_scope_callback_from_ready_evidence :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
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
    preservation_ready_args args ->
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
    forall fname_body args_body synthetic_body T_body Gamma_out R_body
        roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final.
Proof.
  intros Hscope_synthetic Htyping_ready env Ω n R Σ Σ_args R_args
    arg_roots fname args fdef fcall σ s s_args s_body vs ret used'
    Hevidence Hin Hfname Hcaps Htyped_args Heval_args Hready_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename Heval_body
    fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
    Htarget _Hsynthetic Htyped_body.
  destruct
    (eval_synthetic_direct_call_body_scope_inputs_from_ready_evidence
      Htyping_ready env Ω n R Σ Σ_args R_args arg_roots fname args fdef
      fcall σ s s_args s_body vs ret used' Hevidence Hin Hfname Hcaps
      Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow
      Hrn Hnamed Hkeys Hrename Heval_body)
    as (fname_body0 & args_body0 & synthetic_body0 & T_body0 & Γ_out0 &
        R_body0 & roots_body0 & Htarget0 & _Hsynthetic0 & Hready_body0 &
        _Htyped_body0 & _Hcompat_body & _Hexclude_roots & _Hexclude_env &
        Heval_synthetic_body_env & _Hargs_fcall & Hroots_bind &
        Hshadow_bind & Hrn_bind & Hcover_params & Hframe_start &
        Hframe_fresh_start & Hparam_start).
  rewrite Htarget in Htarget0.
  inversion Htarget0; subst fname_body0 args_body0 synthetic_body0; clear Htarget0.
  subst synthetic_body.
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hcaps_call Htyped_body) as Htyped_body_params.
  destruct (Hscope_synthetic
              (global_env_with_local_bounds env (fn_bounds fcall))
              (bind_params (fn_params fcall) vs s_args)
              (ECall fname_body args_body) s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hready_body0 Htyped_body_params
              Hcover_params Hroots_bind Hshadow_bind Hrn_bind
              Hframe_start Hframe_fresh_start Hparam_start)
    as [Hframe_final [frame_final Hparam_final]].
  exists frame_final.
  split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_scope_callback_from_call_statement_ready_evidence :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
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
    preservation_ready_args args ->
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
    forall fname_body args_body synthetic_body T_body Gamma_out R_body
        roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final.
Proof.
  intros Hscope_call Htyping_ready env Ω n R Σ Σ_args R_args
    arg_roots fname args fdef fcall σ s s_args s_body vs ret used'
    Hevidence Hin Hfname Hcaps Htyped_args Heval_args Hready_args
    Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename Heval_body
    fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
    Htarget _Hsynthetic Htyped_body.
  destruct
    (eval_synthetic_direct_call_body_scope_inputs_from_ready_evidence
      Htyping_ready env Ω n R Σ Σ_args R_args arg_roots fname args fdef
      fcall σ s s_args s_body vs ret used' Hevidence Hin Hfname Hcaps
      Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow
      Hrn Hnamed Hkeys Hrename Heval_body)
    as (fname_body0 & args_body0 & synthetic_body0 & T_body0 & Γ_out0 &
        R_body0 & roots_body0 & Htarget0 & _Hsynthetic0 & Hready_body0 &
        _Htyped_body0 & _Hcompat_body & _Hexclude_roots & _Hexclude_env &
        Heval_synthetic_body_env & _Hargs_fcall & Hroots_bind &
        Hshadow_bind & Hrn_bind & Hcover_params & Hframe_start &
        Hframe_fresh_start & Hparam_start).
  rewrite Htarget in Htarget0.
  inversion Htarget0; subst fname_body0 args_body0 synthetic_body0; clear Htarget0.
  subst synthetic_body.
  assert (Hready_args_body : preservation_ready_args args_body).
  { dependent destruction Hready_body0.
    - inversion H.
    - exact H. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out)
      R_body roots_body Hcaps_call Htyped_body) as Htyped_body_params.
  destruct (Hscope_call
              (global_env_with_local_bounds env (fn_bounds fcall))
              (bind_params (fn_params fcall) vs s_args)
              fname_body args_body s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Gamma_out) R_body roots_body
              (fn_params fcall) s_args Hready_args_body Htyped_body_params
              Hcover_params Hroots_bind Hshadow_bind Hrn_bind
              Hframe_start Hframe_fresh_start Hparam_start)
    as [Hframe_final [frame_final Hparam_final]].
  exists frame_final.
  split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_cleanup_prefix_package_from_ready_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args
      s_body vs ret used',
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
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
        synthetic_body s_body ret /\
      store_typed env s_args Σ_args /\
      store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
      value_has_type env s_body ret T_body /\
      store_ref_targets_preserved env
        (bind_params (fn_params fcall) vs s_args) s_body /\
      store_roots_within R_body s_body /\
      value_roots_within roots_body ret /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      eval_args_values_have_types env Ω s_args vs (fn_params fcall) /\
      sctx_same_bindings
        (sctx_of_ctx (params_ctx (fn_params fcall)))
        (sctx_of_ctx Γ_out) /\
      forall frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Γ_out) s_body s_args ->
        store_param_scope (fn_params fcall) s_body frame_final ->
        store_typed env (store_remove_params (fn_params fcall) s_body)
          Σ_args /\
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
  intros Hsynthetic_route Htyping_ready Hroots_ready env Ω n R Σ Σ_args
    R_args arg_roots fname args fdef fcall σ s s_args s_body vs ret used'
    Hevidence Hevidence_body_env Hunique Hin Hfname Hcaps Htyped_args
    Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
    Hnamed_bind Hkeys_bind Heval_body.
  destruct
    (eval_synthetic_direct_call_body_from_ready_evidence
      env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ s s_args
      s_body vs ret used' Hevidence Hin Hfname Hcaps Htyped_args Heval_args
      Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename Heval_body)
    as (fname_body & args_body & synthetic_body & T_body & Γ_out &
        R_body & roots_body & Htarget & Hsynthetic & Hready_body &
        Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Heval_synthetic).
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Heval_synthetic_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_synthetic. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env.
    unfold fn_env_unique_by_name in *; simpl; exact Hunique. }
  assert (Hcaps_call_for_route : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hcaps_call_for_route Htyped_body) as Htyped_body_params_for_route.
  destruct (Hsynthetic_route body_env
              (bind_params (fn_params fcall) vs s_args)
              synthetic_body s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Γ_out) R_body roots_body Hready_body
              Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
              Hnamed_bind Hkeys_bind
              Htyped_body_params_for_route Hunique_body_env Hevidence_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
        [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Γ_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hcaps_call Htyped_body) as Htyped_body_params.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body_params. }
  exists fname_body, args_body, synthetic_body, T_body, Γ_out, R_body,
    roots_body.
  do 18 (split; [assumption|]).
  intros frame_final0 Hframe_scope Hscope_body.
  eapply eval_direct_call_body_cleanup_preserves_value_and_refs_core;
    eassumption.
Qed.

Lemma eval_synthetic_direct_call_body_cleanup_prefix_package_from_call_statement_ready_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args
      s_body vs ret used',
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
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
        synthetic_body s_body ret /\
      store_typed env s_args Σ_args /\
      store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
      value_has_type env s_body ret T_body /\
      store_ref_targets_preserved env
        (bind_params (fn_params fcall) vs s_args) s_body /\
      store_roots_within R_body s_body /\
      value_roots_within roots_body ret /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      eval_args_values_have_types env Ω s_args vs (fn_params fcall) /\
      sctx_same_bindings
        (sctx_of_ctx (params_ctx (fn_params fcall)))
        (sctx_of_ctx Γ_out) /\
      forall frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Γ_out) s_body s_args ->
        store_param_scope (fn_params fcall) s_body frame_final ->
        store_typed env (store_remove_params (fn_params fcall) s_body)
          Σ_args /\
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
  intros Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ_args
    R_args arg_roots fname args fdef fcall σ s s_args s_body vs ret used'
    Hevidence Hevidence_body_env Hunique Hin Hfname Hcaps Htyped_args
    Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
    Hnamed_bind Hkeys_bind Heval_body.
  destruct
    (eval_synthetic_direct_call_body_from_ready_evidence
      env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ s s_args
      s_body vs ret used' Hevidence Hin Hfname Hcaps Htyped_args Heval_args
      Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Hrename Heval_body)
    as (fname_body & args_body & synthetic_body & T_body & Γ_out &
        R_body & roots_body & Htarget & Hsynthetic & Hready_body &
        Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Heval_synthetic).
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Heval_synthetic_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_synthetic. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env.
    unfold fn_env_unique_by_name in *; simpl; exact Hunique. }
  assert (Hcaps_call_for_route : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hcaps_call_for_route Htyped_body) as Htyped_body_params_for_route.
  subst synthetic_body.
  assert (Hready_args_body : preservation_ready_args args_body).
  { dependent destruction Hready_body.
    - inversion H.
    - exact H. }
  destruct (Hsynthetic_call_route body_env
              (bind_params (fn_params fcall) vs s_args)
              fname_body args_body s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Γ_out) R_body roots_body Hready_args_body
              Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
              Hnamed_bind Hkeys_bind
              Htyped_body_params_for_route Hunique_body_env Hevidence_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
        [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Γ_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (ECall fname_body args_body) T_body (sctx_of_ctx Γ_out) R_body roots_body
      Hcaps_call Htyped_body) as Htyped_body_params.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body_params. }
  exists fname_body, args_body, (ECall fname_body args_body), T_body, Γ_out, R_body,
    roots_body.
  do 18 (split; [try assumption; try reflexivity|]).
  intros frame_final0 Hframe_scope Hscope_body.
  eapply eval_direct_call_body_cleanup_preserves_value_and_refs_core;
    eassumption.
Qed.


Lemma eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args arg_roots
      (fname : ident) args fdef fcall (sigma : list lifetime) s s_args
      s_body vs ret used',
    callee_body_root_shadow_synthetic_direct_call_ready_at_result_subset
      env fcall (call_param_root_env (fn_params fcall) arg_roots R_args)
      (root_sets_union arg_roots) ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    (forall fname_body args_body synthetic_body T_body Gamma_out R_body roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final) ->
    exists fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
        frame_final locals,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) /\
      synthetic_body = ECall fname_body args_body /\
      preservation_direct_call_ready_expr synthetic_body /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body /\
      root_set_stores_subset roots_body (root_sets_union arg_roots) /\
      eval env (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret /\
      store_typed env s_args Sigma_args /\
      store_typed env (store_remove_params (fn_params fcall) s_body)
        Sigma_args /\
      store_typed_prefix env s_body (sctx_of_ctx Gamma_out) /\
      store_roots_within R_body s_body /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret (apply_lt_ty sigma (fn_ret fdef)) /\
      store_ref_targets_preserved env s
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = s_args /\
      value_roots_within roots_body ret.
Proof.
  intros Hsynthetic_route Htyping_ready Hroots_ready env Omega n R Sigma
    Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args s_body
    vs ret used' Hresult_subset Hevidence_body_env Hunique Hin Hfname Hcaps
    Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Heval_body Hscopes.
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at_result_subset
    in Hresult_subset.
  destruct Hresult_subset as
    (fname_body & args_body & synthetic_body & T_body & Gamma_out & R_body &
      roots_body & Htarget & Hsynthetic & Hready_body & Htyped_shadow_body &
      Hcompat_body & Hexclude_roots & Hexclude_env & Hresult_subset).
  pose proof (typed_env_roots_shadow_safe_roots
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (fn_body_ctx fcall)) synthetic_body T_body
      (sctx_of_ctx Gamma_out) R_body roots_body Htyped_shadow_body)
    as Htyped_body.
  assert (Heval_synthetic :
    eval env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { eapply eval_direct_call_target_expr_as_call; eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Heval_synthetic_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_synthetic. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env.
    unfold fn_env_unique_by_name in *; simpl; exact Hunique. }
  assert (Hcaps_call_for_route : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body
      Hcaps_call_for_route Htyped_body) as Htyped_body_params_for_route.
  destruct (Hsynthetic_route body_env
              (bind_params (fn_params fcall) vs s_args)
              synthetic_body s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Gamma_out) R_body roots_body Hready_body
              Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
              Hnamed_bind Hkeys_bind
              Htyped_body_params_for_route Hunique_body_env Hevidence_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
        [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Gamma_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Omega n Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args
              Hready_args Hstore
              (typed_args_roots_structural env Omega n R Sigma args
                (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body
      Hcaps_call Htyped_body) as Htyped_body_params.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body_params. }
  destruct (Hscopes fname_body args_body synthetic_body T_body Gamma_out
              R_body roots_body Htarget Hsynthetic Htyped_body)
    as [frame_final [Hframe_scope Hparam_scope]].
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs_core
              env Omega s s_args Sigma_args fdef fcall sigma s_body vs ret
              used' T_body Gamma_out R_body roots_body frame_final
              Hstore_args Hpres_args Hrename Hargs_fcall Hframe_scope
              Hparam_scope Hstore_body_env Hv_body_env Hpres_body_env
              Hroots_body Hret_roots Hshadow_body Hrn_body Hsame_body
              Hcompat_body Hexclude_roots Hexclude_env)
    as [Hstore_final [Hstore_prefix [Hroots_final [Hshadow_final [Hrn_final
          [Hv_final [Hpres_final [locals Htail]]]]]]]].
  destruct Htail as [Hremoved [Hret_exclude [Hstore_exclude
      [Hremoved_exact Hret_roots_final]]]].
  exists fname_body, args_body, synthetic_body, T_body, Gamma_out, R_body,
    roots_body, frame_final, locals.
  repeat split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args arg_roots
      (fname : ident) args fdef fcall (sigma : list lifetime) s s_args
      s_body vs ret used',
    callee_body_root_shadow_synthetic_direct_call_ready_at_result_subset
      env fcall (call_param_root_env (fn_params fcall) arg_roots R_args)
      (root_sets_union arg_roots) ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    (forall fname_body args_body synthetic_body T_body Gamma_out R_body roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final) ->
    exists fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
        frame_final locals,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) /\
      synthetic_body = ECall fname_body args_body /\
      preservation_direct_call_ready_expr synthetic_body /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body /\
      root_set_stores_subset roots_body (root_sets_union arg_roots) /\
      eval env (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret /\
      store_typed env s_args Sigma_args /\
      store_typed env (store_remove_params (fn_params fcall) s_body)
        Sigma_args /\
      store_typed_prefix env s_body (sctx_of_ctx Gamma_out) /\
      store_roots_within R_body s_body /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret (apply_lt_ty sigma (fn_ret fdef)) /\
      store_ref_targets_preserved env s
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = s_args /\
      value_roots_within roots_body ret.
Proof.
  intros Hsynthetic_call_route Htyping_ready Hroots_ready env Omega n R Sigma
    Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args s_body
    vs ret used' Hresult_subset Hevidence_body_env Hunique Hin Hfname Hcaps
    Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Heval_body Hscopes.
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at_result_subset
    in Hresult_subset.
  destruct Hresult_subset as
    (fname_body & args_body & synthetic_body & T_body & Gamma_out & R_body &
      roots_body & Htarget & Hsynthetic & Hready_body & Htyped_shadow_body &
      Hcompat_body & Hexclude_roots & Hexclude_env & Hresult_subset).
  pose proof (typed_env_roots_shadow_safe_roots
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (sctx_of_ctx (fn_body_ctx fcall)) synthetic_body T_body
      (sctx_of_ctx Gamma_out) R_body roots_body Htyped_shadow_body)
    as Htyped_body.
  assert (Heval_synthetic :
    eval env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { eapply eval_direct_call_target_expr_as_call; eassumption. }
  pose (body_env := global_env_with_local_bounds env (fn_bounds fcall)).
  assert (Heval_synthetic_body_env :
    eval body_env (bind_params (fn_params fcall) vs s_args)
      synthetic_body s_body ret).
  { subst body_env.
    eapply direct_call_eval_global_env_with_local_bounds.
    exact Heval_synthetic. }
  assert (Hunique_body_env : fn_env_unique_by_name body_env).
  { subst body_env.
    unfold fn_env_unique_by_name in *; simpl; exact Hunique. }
  assert (Hcaps_call_for_route : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body
      Hcaps_call_for_route Htyped_body) as Htyped_body_params_for_route.
  subst synthetic_body.
  assert (Hready_args_body : preservation_ready_args args_body).
  { dependent destruction Hready_body.
    - inversion H.
    - exact H. }
  destruct (Hsynthetic_call_route body_env
              (bind_params (fn_params fcall) vs s_args)
              fname_body args_body s_body ret Heval_synthetic_body_env
              (fn_outlives fcall) (fn_lifetimes fcall)
              (call_param_root_env (fn_params fcall) arg_roots R_args)
              (sctx_of_ctx (params_ctx (fn_params fcall))) T_body
              (sctx_of_ctx Gamma_out) R_body roots_body Hready_args_body
              Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind
              Hnamed_bind Hkeys_bind
              Htyped_body_params_for_route Hunique_body_env Hevidence_body_env)
    as [Hstore_body [Hv_body [Hpres_body [Hroots_body [Hret_roots
        [Hshadow_body Hrn_body]]]]]].
  assert (Hstore_body_env :
    store_typed_prefix env s_body (sctx_of_ctx Gamma_out)).
  { subst body_env.
    eapply direct_call_store_typed_prefix_clear_global_env_local_bounds.
    exact Hstore_body. }
  assert (Hv_body_env : value_has_type env s_body ret T_body).
  { subst body_env.
    eapply direct_call_value_has_type_clear_global_env_local_bounds.
    exact Hv_body. }
  assert (Hpres_body_env :
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body).
  { subst body_env.
    eapply direct_call_store_ref_targets_preserved_clear_global_env_local_bounds.
    exact Hpres_body. }
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Omega n Sigma
              (apply_lt_params sigma (fn_params fdef)) Sigma_args
              Hready_args Hstore
              (typed_args_roots_structural env Omega n R Sigma args
                (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hcaps_call : fn_captures fcall = []).
  { rewrite (alpha_rename_fn_def_captures
              (store_names s_args) fdef fcall used' Hrename).
    exact Hcaps. }
  pose proof
    (typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures
      (global_env_with_local_bounds env (fn_bounds fcall))
      (fn_outlives fcall) (fn_lifetimes fcall)
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      fcall (ECall fname_body args_body) T_body (sctx_of_ctx Gamma_out) R_body roots_body
      Hcaps_call Htyped_body) as Htyped_body_params.
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Gamma_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body_params. }
  destruct (Hscopes fname_body args_body (ECall fname_body args_body) T_body Gamma_out
              R_body roots_body Htarget eq_refl Htyped_body)
    as [frame_final [Hframe_scope Hparam_scope]].
  destruct (eval_direct_call_body_cleanup_preserves_value_and_refs_core
              env Omega s s_args Sigma_args fdef fcall sigma s_body vs ret
              used' T_body Gamma_out R_body roots_body frame_final
              Hstore_args Hpres_args Hrename Hargs_fcall Hframe_scope
              Hparam_scope Hstore_body_env Hv_body_env Hpres_body_env
              Hroots_body Hret_roots Hshadow_body Hrn_body Hsame_body
              Hcompat_body Hexclude_roots Hexclude_env)
    as [Hstore_final [Hstore_prefix [Hroots_final [Hshadow_final [Hrn_final
          [Hv_final [Hpres_final [locals Htail]]]]]]]].
  destruct Htail as [Hremoved [Hret_exclude [Hstore_exclude
      [Hremoved_exact Hret_roots_final]]]].
  exists fname_body, args_body, (ECall fname_body args_body), T_body, Gamma_out, R_body,
    roots_body, frame_final, locals.
  repeat split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_cleanup_prefix_from_ready_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args arg_roots
      (fname : ident) args fdef fcall (sigma : list lifetime) s s_args
      s_body vs ret used',
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    (forall fname_body args_body synthetic_body T_body Gamma_out R_body roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final) ->
    exists fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
        frame_final locals,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) /\
      synthetic_body = ECall fname_body args_body /\
      preservation_direct_call_ready_expr synthetic_body /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body /\
      eval env (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret /\
      store_typed env s_args Sigma_args /\
      store_typed env (store_remove_params (fn_params fcall) s_body)
        Sigma_args /\
      store_typed_prefix env s_body (sctx_of_ctx Gamma_out) /\
      store_roots_within R_body s_body /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret (apply_lt_ty sigma (fn_ret fdef)) /\
      store_ref_targets_preserved env s
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = s_args /\
      value_roots_within roots_body ret.
Proof.
  intros Hsynthetic_route Htyping_ready Hroots_ready env Omega n R Sigma
    Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args s_body
    vs ret used' Hevidence Hevidence_body_env Hunique Hin Hfname Hcaps
    Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Heval_body Hscopes.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_package_from_ready_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Omega n R Sigma
      Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args
      s_body vs ret used' Hevidence Hevidence_body_env Hunique Hin Hfname
      Hcaps Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots
      Hshadow Hrn Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind
      Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind Heval_body)
    as (fname_body & args_body & synthetic_body & T_body & Gamma_out &
        R_body & roots_body & Htarget & Hsynthetic & Hready_body &
        Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Heval_synthetic & Hstore_args & _Hstore_prefix_body & _Hv_body &
        _Hpres_body & _Hroots_body & _Hret_roots & _Hshadow_body &
        _Hrn_body & _Hargs_fcall & _Hsame_body & Hcleanup).
  destruct (Hscopes fname_body args_body synthetic_body T_body Gamma_out
              R_body roots_body Htarget Hsynthetic Htyped_body)
    as [frame_final [Hframe_scope Hparam_scope]].
  destruct (Hcleanup frame_final Hframe_scope Hparam_scope)
    as [Hstore_final [Hstore_prefix [Hroots_final [Hshadow_final [Hrn_final
          [Hv_final [Hpres_final [locals Htail]]]]]]]].
  destruct Htail as [Hremoved [Hret_exclude [Hstore_exclude
      [Hremoved_exact Hret_roots_final]]]].
  exists fname_body, args_body, synthetic_body, T_body, Gamma_out, R_body,
    roots_body, frame_final, locals.
  repeat split; assumption.
Qed.

Lemma eval_synthetic_direct_call_body_cleanup_prefix_from_call_statement_ready_evidence :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args arg_roots
      (fname : ident) args fdef fcall (sigma : list lifetime) s s_args
      s_body vs ret used',
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall)) ->
    fn_env_unique_by_name env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    preservation_ready_args args ->
    provenance_ready_args args ->
    store_typed env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall))) ->
    store_roots_within
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow
      (call_param_root_env (fn_params fcall) arg_roots R_args) ->
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (bind_params (fn_params fcall) vs s_args) ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    (forall fname_body args_body synthetic_body T_body Gamma_out R_body roots_body,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) ->
      synthetic_body = ECall fname_body args_body ->
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body ->
      exists frame_final,
        store_frame_scope (fn_params fcall)
          (sctx_of_ctx Gamma_out) s_body s_args /\
        store_param_scope (fn_params fcall) s_body frame_final) ->
    exists fname_body args_body synthetic_body T_body Gamma_out R_body roots_body
        frame_final locals,
      direct_call_target_expr (fn_body fcall) =
        Some (fname_body, args_body, synthetic_body) /\
      synthetic_body = ECall fname_body args_body /\
      preservation_direct_call_ready_expr synthetic_body /\
      typed_env_roots (global_env_with_local_bounds env (fn_bounds fcall))
        (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (fn_body_ctx fcall))
        synthetic_body T_body (sctx_of_ctx Gamma_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body /\
      eval env (bind_params (fn_params fcall) vs s_args)
        synthetic_body s_body ret /\
      store_typed env s_args Sigma_args /\
      store_typed env (store_remove_params (fn_params fcall) s_body)
        Sigma_args /\
      store_typed_prefix env s_body (sctx_of_ctx Gamma_out) /\
      store_roots_within R_body s_body /\
      store_no_shadow s_body /\
      root_env_no_shadow R_body /\
      value_has_type env (store_remove_params (fn_params fcall) s_body)
        ret (apply_lt_ty sigma (fn_ret fdef)) /\
      store_ref_targets_preserved env s
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body) /\
      store_remove_params (fn_params fcall) s_body = s_args /\
      value_roots_within roots_body ret.
Proof.
  intros Hsynthetic_call_route Htyping_ready Hroots_ready env Omega n R Sigma
    Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args s_body
    vs ret used' Hevidence Hevidence_body_env Hunique Hin Hfname Hcaps
    Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots Hshadow Hrn
    Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind Hshadow_bind
    Hrn_bind Hnamed_bind Hkeys_bind Heval_body Hscopes.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_package_from_call_statement_ready_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Omega n R Sigma
      Sigma_args R_args arg_roots fname args fdef fcall sigma s s_args
      s_body vs ret used' Hevidence Hevidence_body_env Hunique Hin Hfname
      Hcaps Htyped_args Heval_args Hready_args Hprov_args Hstore Hroots
      Hshadow Hrn Hnamed Hkeys Hrename Hstore_bind_body_env Hroots_bind
      Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind Heval_body)
    as (fname_body & args_body & synthetic_body & T_body & Gamma_out &
        R_body & roots_body & Htarget & Hsynthetic & Hready_body &
        Htyped_body & Hcompat_body & Hexclude_roots & Hexclude_env &
        Heval_synthetic & Hstore_args & _Hstore_prefix_body & _Hv_body &
        _Hpres_body & _Hroots_body & _Hret_roots & _Hshadow_body &
        _Hrn_body & _Hargs_fcall & _Hsame_body & Hcleanup).
  destruct (Hscopes fname_body args_body synthetic_body T_body Gamma_out
              R_body roots_body Htarget Hsynthetic Htyped_body)
    as [frame_final [Hframe_scope Hparam_scope]].
  destruct (Hcleanup frame_final Hframe_scope Hparam_scope)
    as [Hstore_final [Hstore_prefix [Hroots_final [Hshadow_final [Hrn_final
          [Hv_final [Hpres_final [locals Htail]]]]]]]].
  destruct Htail as [Hremoved [Hret_exclude [Hstore_exclude
      [Hremoved_exact Hret_roots_final]]]].
  exists fname_body, args_body, synthetic_body, T_body, Gamma_out, R_body,
    roots_body, frame_final, locals.
  repeat split; assumption.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_preservation_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      (forall Σ_args R_args arg_roots fname_call fdef fcall σ s_args s_body vs ret used',
        In fdef (env_fns env) ->
        fn_name fdef = fname_call ->
        fn_captures fdef = [] ->
        typed_args_roots env Ω n R Σ args
          (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
        eval_args env s args s_args vs ->
        provenance_ready_args args ->
        alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
        eval env (bind_params (fn_params fcall) vs s_args)
          (fn_body fcall) s_body ret ->
        root_env_store_roots_named
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (bind_params (fn_params fcall) vs s_args) /\
        root_env_store_keys_named
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (bind_params (fn_params fcall) vs s_args)) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready env s
    s' v fname args Heval Ω n R Σ T Σ' R' roots Hready_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hevidence
    Hevidence_body_env Hbind_named.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (Hbind_named Σ' R' arg_roots (fn_name fdef0) fdef0 fcall σ
              s_args s_body vs ret used' H3 eq_refl H0 H7 H1 Hprov_args
              H2 Heval) as [Hnamed_bind Hkeys_bind].
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args s_body vs ret used'
      Hevidence H3 eq_refl H0 H7 H1 Hready_args Hprov_args Hstore
      Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_ready_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body vs ret
      used' Hevidence (Hevidence_body_env fcall) Hunique H3 eq_refl H0
      H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env
      Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind Heval
      Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body &
        _Gamma_out & _R_body & roots_body & _frame_final & _locals &
        _Htarget & _Hsynthetic & _Hready_body & _Htyped_body &
        _Hcompat_body & _Hexclude_roots & _Hexclude_env &
        _Heval_synthetic & _Hstore_args & Hstore_final &
        _Hstore_prefix & _Hroots_body & _Hshadow_body & _Hrn_body &
        Hv_final & Hpres_final & _Hremoved & _Hret_exclude &
        _Hstore_exclude & Hremoved_exact & Hret_roots).
  split; [ exact Hstore_final | ].
  split; [ exact Hv_final | ].
  split; [ exact Hpres_final | ].
  split; [ rewrite Hremoved_exact; exact Hroots_args | ].
  split; [ rewrite Hremoved_exact; exact Hshadow_args | ].
  split; [ exact Hrn_args | ].
  exists roots_body.
  exact Hret_roots.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      (forall Σ_args R_args arg_roots fname_call fdef fcall σ s_args s_body vs ret used',
        In fdef (env_fns env) ->
        fn_name fdef = fname_call ->
        fn_captures fdef = [] ->
        typed_args_roots env Ω n R Σ args
          (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
        eval_args env s args s_args vs ->
        provenance_ready_args args ->
        alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
        eval env (bind_params (fn_params fcall) vs s_args)
          (fn_body fcall) s_body ret ->
        root_env_store_roots_named
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (bind_params (fn_params fcall) vs s_args) /\
        root_env_store_keys_named
          (call_param_root_env (fn_params fcall) arg_roots R_args)
          (bind_params (fn_params fcall) vs s_args)) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready env s
    s' v fname args Heval Ω n R Σ T Σ' R' roots Hready_args Hstore
    Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hevidence
    Hevidence_body_env Hbind_named.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (Hbind_named Σ' R' arg_roots (fn_name fdef0) fdef0 fcall σ
              s_args s_body vs ret used' H3 eq_refl H0 H7 H1 Hprov_args
              H2 Heval) as [Hnamed_bind Hkeys_bind].
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args s_body vs ret used'
      Hevidence H3 eq_refl H0 H7 H1 Hready_args Hprov_args Hstore
      Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_call_statement_ready_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body vs ret
      used' Hevidence (Hevidence_body_env fcall) Hunique H3 eq_refl H0
      H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env
      Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind Hkeys_bind Heval
      Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body &
        _Gamma_out & _R_body & roots_body & _frame_final & _locals &
        _Htarget & _Hsynthetic & _Hready_body & _Htyped_body &
        _Hcompat_body & _Hexclude_roots & _Hexclude_env &
        _Heval_synthetic & _Hstore_args & Hstore_final &
        _Hstore_prefix & _Hroots_body & _Hshadow_body & _Hrn_body &
        Hv_final & Hpres_final & _Hremoved & _Hret_exclude &
        _Hstore_exclude & Hremoved_exact & Hret_roots).
  split; [ exact Hstore_final | ].
  split; [ exact Hv_final | ].
  split; [ exact Hpres_final | ].
  split; [ rewrite Hremoved_exact; exact Hroots_args | ].
  split; [ rewrite Hremoved_exact; exact Hshadow_args | ].
  split; [ exact Hrn_args | ].
  exists roots_body.
  exact Hret_roots.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_named_bind_facts_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ' R'
    roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hevidence Hevidence_body_env.
  eapply
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_preservation_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  intros Σ_args R_args arg_roots fname_call fdef fcall σ s_args
    s_body vs ret used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hrename _Heval_body.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [_ Hrn_args]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed
              Htyped_args)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs Heval_args Ω n R Σ
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys
                Htyped_args) as Hkeys_args.
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  split.
  - eapply root_env_store_roots_named_call_param_bind_params;
      eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params;
      eassumption.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ' R'
    roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hevidence Hevidence_body_env.
  eapply
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_core
      Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  intros Σ_args R_args arg_roots fname_call fdef fcall σ s_args
    s_body vs ret used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hrename _Heval_body.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [_ Hrn_args]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed
              Htyped_args)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs Heval_args Ω n R Σ
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys
                Htyped_args) as Hkeys_args.
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  split.
  - eapply root_env_store_roots_named_call_param_bind_params;
      eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params;
      eassumption.
Qed.

Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_named_bind_facts_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    env s s' v fname args Heval Ω n R Σ T Σ' R' roots Hsafe_args
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hevidence
    Hevidence_body_env.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  eapply
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_preservation_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  intros Σ_args R_args arg_roots fname_call fdef fcall σ s_args
    s_body vs ret used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hrename _Heval_body.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [_ Hrn_args]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  split.
  - eapply root_env_store_roots_named_call_param_bind_params;
      eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params;
      eassumption.
Qed.

Theorem eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      direct_call_callee_body_root_synthetic_direct_call_ready_evidence env ->
      (forall fcall,
        direct_call_callee_body_root_synthetic_direct_call_ready_evidence
          (global_env_with_local_bounds env (fn_bounds fcall))) ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    env s s' v fname args Heval Ω n R Σ T Σ' R' roots Hsafe_args
    Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique Hevidence
    Hevidence_body_env.
  pose proof (store_safe_function_value_call_args_preservation_ready
                env args Hsafe_args) as Hready_args.
  eapply
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_core
      Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready);
    try eassumption.
  intros Σ_args R_args arg_roots fname_call fdef fcall σ s_args
    s_body vs ret used' Hin Hfname Hcaps Htyped_args Heval_args
    Hprov_args Hrename _Heval_body.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [_ Hrn_args]]].
  destruct (store_safe_function_value_call_args_typed_roots_store_named
              env Ω n R Σ args
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots s s_args vs Hsafe_args Htyped_args Heval_args
              Hnamed Hkeys)
    as [Hnamed_args [Harg_roots_named Hkeys_args]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [_ [Hargs_subst _]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  split.
  - eapply root_env_store_roots_named_call_param_bind_params;
      eassumption.
  - eapply root_env_store_keys_named_call_param_bind_params;
      eassumption.
Qed.

Lemma callee_body_root_shadow_synthetic_direct_call_ready_summary_global_env_with_local_bounds :
  forall env bounds fdef,
    callee_body_root_shadow_synthetic_direct_call_ready_summary env fdef ->
    callee_body_root_shadow_synthetic_direct_call_ready_summary
      (global_env_with_local_bounds env bounds) fdef.
Proof.
  intros env bounds fdef [Hnodup Hready].
  split; [exact Hnodup |].
  unfold callee_body_root_shadow_synthetic_direct_call_ready_at in *.
  destruct Hready as
    (fname & args & synthetic_body & T_body & Gamma_out & R_body & roots_body &
      Htarget & Hsynthetic & Hready_body & Htyped_body & Hcompat_body &
      Hexclude_roots & Hexclude_env).
  exists fname, args, synthetic_body, T_body, Gamma_out, R_body, roots_body.
  repeat split; assumption.
Qed.

Lemma env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds :
  forall env bounds,
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence
      (global_env_with_local_bounds env bounds).
Proof.
  intros env bounds Hsummary fname fdef Hlookup.
  change (lookup_fn fname (env_fns env) = Some fdef) in Hlookup.
  eapply callee_body_root_shadow_synthetic_direct_call_ready_summary_global_env_with_local_bounds.
  exact (Hsummary fname fdef Hlookup).
Qed.

Lemma callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary :
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env (Omega : outlives_ctx) (n : nat) R Sigma Sigma_args R_args
      arg_roots fname args fdef fcall (sigma : list lifetime) s s_args vs used',
    fn_env_unique_by_name env ->
    env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    fn_captures fdef = [] ->
    typed_args_roots env Omega n R Sigma args
      (apply_lt_params sigma (fn_params fdef)) Sigma_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    store_typed env s Sigma ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    callee_body_root_shadow_synthetic_direct_call_ready_at_result_subset
      env fcall
      (call_param_root_env (fn_params fcall) arg_roots R_args)
      (root_sets_union arg_roots).
Proof.
  intros Hroot_names Hroot_keys env Omega n R Sigma Sigma_args R_args
    arg_roots fname args fdef fcall sigma s s_args vs used' Hunique
    Hsummary Hin Hfname Hcaps Htyped_args Heval_args Hprov_args Hstore Hroots
    Hshadow Hrn Hnamed Hkeys Hrename.
  eapply
    (direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_summary_with_result_subset_with_preservation_core
      Hroot_names Hroot_keys);
    try eassumption.
  eapply Hsummary.
  eapply lookup_fn_in_unique_by_name; eassumption.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Sigma T Sigma' R' roots,
      preservation_ready_args args ->
      store_typed env s Sigma ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Sigma (ECall fname args) T Sigma' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Sigma' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      exists roots_body,
        value_roots_within roots_body v.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Sigma T Sigma' R'
    roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hsummary Hbridge.
  eapply
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_named_bind_facts_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
      Hroot_names Hroot_keys);
    try eassumption.
  - eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
      eassumption.
  - intros fcall.
    eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
    + eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    + eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      * exact Hroot_names.
      * exact Hroot_keys.
      * unfold fn_env_unique_by_name in *; simpl; exact Hunique.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  forall env s s' v fname args,
    eval env s (ECall fname args) s' v ->
    forall (Omega : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Omega n R Σ (ECall fname args) T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s s' v fname args Heval Omega n R Σ T
    Σ' R' roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [Hroots_args [_ [Hshadow_args Hrn_args]]].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Omega n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Omega n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Omega s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Omega s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs H1 Omega n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed H7)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs H1 Omega n R Σ
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys H7)
    as Hkeys_args.
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
    - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Omega n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H0 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Omega n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary H3 eq_refl H0 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Omega n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H0 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & Hresult_subset & _Heval_synthetic &
        _Hstore_args & Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & Hv_final & Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & Hret_roots).
  repeat split; try assumption.
  - rewrite Hremoved_exact. exact Hroots_args.
  - eapply direct_call_value_roots_within_store_subset; eassumption.
  - rewrite Hremoved_exact. exact Hshadow_args.
Qed.


Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement_of_final_roots_bridge :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys env s fname args s' v Heval Ω n R Σ T Σ' R'
    roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
    Hsummary Hbridge.
  destruct
    (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core
      Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
      Hroot_names Hroot_keys env s s' v fname args Heval Ω n R Σ T Σ'
      R' roots Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
      Hunique Hsummary Hbridge)
    as [Hstore' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
  repeat split; try assumption.
  eapply store_typed_prefix_exact. exact Hstore'.
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hready_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed H7)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs H1 Ω n R Σ
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys H7)
    as Hkeys_args.
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
    - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_evidence
      Hsynthetic_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement.
Proof.
  intros Hsynthetic_call_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hready_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed H7)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs H1 Ω n R Σ
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys H7)
    as Hkeys_args.
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
    - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_ready_evidence
      Hscope_synthetic Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_routes_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement.
Proof.
  intros Hsynthetic_call_route Hscope_call Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready env s fname args s' v
    Heval Ω n R Σ T Σ' R' roots ps frame Hready_args Hstore Hnamed Hkeys
    Htyped Hunique Hsummary Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh
    Hparam.
  pose proof (preservation_ready_args_implies_provenance_ready_closure
                args Hready_args) as Hprov_args.
  dependent destruction Heval.
  dependent destruction Htyped.
  simpl in *.
  repeat match goal with
  | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
      Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env) |- _ =>
      pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
        f_runtime f_typed Hlookup Hin0 eq_refl Hunique) as Hsame;
      subst f_runtime
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : fn_name ?f_typed = ?fname_call |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 Hname Hunique) as Hsame;
      subst f_typed
  | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
    Hin0 : In ?f_typed (env_fns env),
    Hname : ?fname_call = fn_name ?f_typed |- _ =>
      pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
        Hlookup Hin0 (eq_sym Hname) Hunique) as Hsame;
      subst f_typed
  end.
  destruct (proj1 (proj2 Hframe_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hroots Hshadow Hrn
              Hframe Hfresh)
    as [_ [_ [_ [_ [Hframe_args _]]]]].
  destruct (proj1 (proj2 Hparam_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots ps frame Hprov_args H7 Hcover Hparam)
    as [frame_args Hparam_args].
  destruct (proj1 (proj2 Htyping_ready)
              env s args s_args vs H1 Ω n Σ
              (apply_lt_params σ (fn_params fdef0)) Σ'
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots H7))
    as [_ [Hargs_subst _]].
  destruct (proj1 (proj2 Hroots_ready)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hroots Hshadow Hrn H7)
    as [_ [_ [_ Hrn_args]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef0 fcall used' H2) as Hshape.
  destruct Hshape as [_ [_ Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef0)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact H2. }
  assert (Hfresh_params : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact H2. }
  destruct (eval_args_bind_params_call_param_root_env_ready
              env s args s_args vs Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R' arg_roots
              (fn_params fcall) H1 Hprov_args H7
              Hroots Hshadow Hrn Hnodup Hfresh_params Hargs_fcall)
    as [Hroots_bind [Hshadow_bind [Hrn_bind _Hcover_bind]]].
  destruct (proj1 (proj2 Hroot_names)
              env s args s_args vs H1 Ω n R Σ
              (apply_lt_params σ (fn_params fdef0)) Σ' R'
              arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hnamed H7)
    as [Hnamed_args Harg_roots_named].
  pose proof (proj1 (proj2 Hroot_keys)
                env s args s_args vs H1 Ω n R Σ
                (apply_lt_params σ (fn_params fdef0)) Σ' R'
                arg_roots Hprov_args Hstore Hroots Hshadow Hrn Hkeys H7)
    as Hkeys_args.
  assert (Hnamed_bind :
    root_env_store_roots_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_roots_named_call_param_bind_params;
      eassumption. }
  assert (Hkeys_bind :
    root_env_store_keys_named
      (call_param_root_env (fn_params fcall) arg_roots R')
      (bind_params (fn_params fcall) vs s_args)).
  { eapply root_env_store_keys_named_call_param_bind_params;
      eassumption. }
  assert (Hstore_bind_env :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hstore_bind_body_env :
    store_typed_prefix (global_env_with_local_bounds env (fn_bounds fcall))
      (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply direct_call_store_typed_prefix_global_env_with_local_bounds.
    exact Hstore_bind_env. }
  assert (Hevidence :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence env).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
      eassumption. }
  assert (Hevidence_body_env :
    direct_call_callee_body_root_synthetic_direct_call_ready_evidence
      (global_env_with_local_bounds env (fn_bounds fcall))).
  { eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge.
    - eapply env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds.
      exact Hsummary.
    - eapply direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_unique_with_preservation_core.
      + exact Hroot_names.
      + exact Hroot_keys.
      + unfold fn_env_unique_by_name in *; simpl; exact Hunique.
  }
  pose proof
    (eval_synthetic_direct_call_body_scope_callback_from_call_statement_ready_evidence
      Hscope_call Htyping_ready env Ω n R Σ Σ' R'
      arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hevidence H3 eq_refl H5 H7 H1 Hready_args Hprov_args
      Hstore Hroots Hshadow Hrn Hnamed Hkeys H2 Heval) as Hscopes.
  pose proof
    (callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_env_summary
      Hroot_names Hroot_keys env Ω n R Σ Σ' R' arg_roots
      (fn_name fdef0) args fdef0 fcall σ s s_args vs used' Hunique
      Hsummary H3 eq_refl H5 H7 H1 Hprov_args Hstore Hroots Hshadow Hrn
      Hnamed Hkeys H2) as Hbody_result_subset.
  destruct
    (eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence
      Hsynthetic_call_route Htyping_ready Hroots_ready env Ω n R Σ Σ'
      R' arg_roots (fn_name fdef0) args fdef0 fcall σ s s_args s_body
      vs ret used' Hbody_result_subset Hevidence_body_env Hunique H3 eq_refl
      H5 H7 H1 Hready_args Hprov_args Hstore Hroots Hshadow Hrn Hnamed Hkeys
      H2 Hstore_bind_body_env Hroots_bind Hshadow_bind Hrn_bind Hnamed_bind
      Hkeys_bind Heval Hscopes)
    as (_fname_body & _args_body & _synthetic_body & _T_body & _Gamma_out &
        _R_body & _roots_body & _frame_final & _locals & _Htarget &
        _Hsynthetic & _Hready_body & _Htyped_body & _Hcompat_body &
        _Hexclude_roots & _Hexclude_env & _Hresult_subset & _Heval_synthetic &
        _Hstore_args & _Hstore_final & _Hstore_prefix & _Hroots_body &
        _Hshadow_body & _Hrn_body & _Hv_final & _Hpres_final & _Hremoved &
        _Hret_exclude & _Hstore_exclude & Hremoved_exact & _Hret_roots).
  split.
  - rewrite Hremoved_exact. exact Hframe_args.
  - exists frame_args. rewrite Hremoved_exact. exact Hparam_args.
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_final_roots_and_cleanup :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement.
Proof.
  intros Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
    Hroot_names Hroot_keys Hframe_ready Hparam_ready.
  split.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_exact_call_statement_of_final_roots_bridge;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup;
      eassumption.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement_of_call_statement :
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement.
Proof.
  intros Hcall env s fname args s' v Heval Ω n R Σ T Σ' R' roots
    Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
    Hsummary Hbridge.
  eapply Hcall; try eassumption.
  eapply direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_shadow_summary_bridge;
    eassumption.
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement_of_call_statement :
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement.
Proof.
  intros Hcall env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps
    frame Hready_args _Hstore _Hnamed _Hkeys Htyped _Hunique _Hsummary
    _Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
  eapply Hcall; eassumption.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_prefix_narrow_core :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement ->
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
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Hprefix_ready Hsummary_call env s e s' v Heval Ω n R Σ T Σ' R'
    roots Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
    Hsummary Hbridge.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    exact (proj1 Hprefix_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots Hprov (store_typed_prefix_exact env s Σ Hstore) Hroots Hshadow
      Hrn Htyped).
  - eapply Hsummary_call; try eassumption.
    eapply store_typed_prefix_exact. exact Hstore.
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_with_summary_bridge_narrow_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros Hframe_ready Hparam_ready Hsummary_call env s e s' v Heval Ω n R Σ
    T Σ' R' roots ps frame Hready Hstore Hnamed Hkeys Htyped Hunique Hsummary
    Hbridge Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    destruct (proj1 Hframe_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots ps frame Hprov Htyped Hcover Hroots Hshadow Hrn Hframe Hfresh)
      as [_ [_ [_ [_ [Hframe' _]]]]].
    destruct (proj1 Hparam_ready env s e s' v Heval Ω n R Σ T Σ' R'
      roots ps frame Hprov Htyped Hcover Hparam) as [frame' Hparam'].
    split; [exact Hframe' | exists frame'; exact Hparam'].
  - eapply Hsummary_call; try eassumption.
    eapply store_typed_prefix_exact. exact Hstore.
Qed.


Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_package_prefix_narrow_core :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
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
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Hprefix_ready Hpackage.
  eapply eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_prefix_narrow_core.
  - exact Hprefix_ready.
  - exact (eval_preserves_synthetic_direct_call_ready_summary_call_package_prefix
      Hpackage).
Qed.

Theorem eval_preserves_frame_param_scope_synthetic_direct_call_ready_with_summary_bridge_package_narrow_core :
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame'.
Proof.
  intros Hframe_ready Hparam_ready Hpackage.
  eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_with_summary_bridge_narrow_core.
  - exact Hframe_ready.
  - exact Hparam_ready.
  - exact (eval_preserves_synthetic_direct_call_ready_summary_call_package_scope
      Hpackage).
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_with_summary_bridge_package_narrow_core :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  (forall env s e s' v,
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
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      root_env_store_roots_named R s ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      store_param_scope ps s frame ->
      store_frame_scope ps Σ' s' frame /\
      exists frame', store_param_scope ps s' frame').
Proof.
  intros Hprefix_ready Hframe_ready Hparam_ready Hpackage.
  split.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_package_prefix_narrow_core;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_with_summary_bridge_package_narrow_core;
      eassumption.
Qed.

Theorem eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_package_narrow_core :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_call_package_statement ->
  eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement.
Proof.
  intros Hprefix_ready Hframe_ready Hparam_ready Hpackage.
  pose proof
    (eval_preserves_synthetic_direct_call_ready_with_summary_bridge_package_narrow_core
      Hprefix_ready Hframe_ready Hparam_ready Hpackage)
    as [Hprefix Hscope].
  split.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots
      Hready_args Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped Hunique
      Hsummary Hbridge.
    eapply Hprefix; try eassumption.
    apply PDCR_Call. exact Hready_args.
  - intros env s fname args s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hready_args Hstore Hnamed Hkeys Htyped Hunique Hsummary Hbridge
      Hcover Hroots Hshadow Hrn Hframe Hfresh Hparam.
    eapply Hscope; try eassumption.
    apply PDCR_Call. exact Hready_args.
Qed.

Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
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
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Htyping_roots Hsynthetic_route Hscope_synthetic Htyping_ready
    Hroots_ready Hroot_names Hroot_keys env s e s' v Heval Ω n R Σ T
    Σ' R' roots Hready Hstore Hroots Hshadow Hrn Hnamed Hkeys Htyped
    Hunique Hsummary Hbridge.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof
      (preservation_ready_expr_implies_provenance_ready_direct_call
        e Hpres_ready) as Hprov.
    exact (proj1 Htyping_roots env s e s' v Heval Ω n R Σ T Σ' R'
      roots Hprov Hstore Hroots Hshadow Hrn Htyped).
  - eapply
      (eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core
        Hsynthetic_route Hscope_synthetic Htyping_ready Hroots_ready
        Hroot_names Hroot_keys);
      eassumption.
Qed.


Theorem eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_narrow_core :
  eval_preserves_typing_roots_ready_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement ->
  eval_preserves_frame_scope_roots_ready_mutual_statement ->
  eval_preserves_param_scope_roots_ready_mutual_statement ->
  eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement ->
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_root_names_ready_mutual_statement ->
  eval_preserves_root_keys_named_ready_mutual_statement ->
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
      env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence env ->
      direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R'.
Proof.
  intros Htyping_roots Hprefix_ready Hprefix_call Hframe_ready
    Hparam_ready Hscope_call Htyping_ready Hroots_ready Hroot_names
    Hroot_keys.
  eapply eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_core.
  - exact Htyping_roots.
  - eapply eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement_of_call_statement;
      eassumption.
  - eapply eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement_of_call_statement;
      eassumption.
  - exact Htyping_ready.
  - exact Hroots_ready.
  - exact Hroot_names.
  - exact Hroot_keys.
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
