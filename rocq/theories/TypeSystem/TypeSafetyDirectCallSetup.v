From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyClosure.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition eval_preserves_typing_roots_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').

Definition eval_preserves_typing_ready_prefix_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').

Lemma preservation_ready_expr_implies_provenance_ready_direct_call :
  forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e.
Proof.
  assert (Hmut :
    (forall e,
      preservation_ready_expr e ->
      provenance_ready_expr e) /\
    (forall args,
      preservation_ready_args args ->
      provenance_ready_args args) /\
    (forall fields,
      preservation_ready_fields fields ->
      provenance_ready_fields fields) /\
    (forall branches,
      preservation_ready_match_branches branches ->
      provenance_ready_match_branches branches)).
  { apply preservation_ready_mutind_closure;
      try solve [econstructor; eauto]. }
  exact (proj1 Hmut).
Qed.

Lemma direct_call_value_roots_within_store_subset :
  forall roots v roots',
    value_roots_within roots v ->
    root_set_stores_subset roots roots' ->
    value_roots_within roots' v.
Proof.
  assert (Hmut :
    (forall roots v,
      value_roots_within roots v ->
      forall roots',
        root_set_stores_subset roots roots' ->
        value_roots_within roots' v) /\
    (forall R se,
      store_entry_roots_within R se -> True) /\
    (forall R s,
      store_roots_within R s -> True) /\
    (forall roots fields,
      value_fields_roots_within roots fields ->
      forall roots',
        root_set_stores_subset roots roots' ->
        value_fields_roots_within roots' fields)).
	  { apply value_roots_within_mutind; intros; try solve [constructor; eauto].
	    - constructor.
	      + match goal with
	        | Hexclude_payload : forall root, roots_exclude root ?roots0 ->
	            Forall (value_refs_exclude_root root) ?values,
	          Hsubset : root_set_stores_subset ?roots0 ?roots1 |- _ =>
	            apply Forall_forall; intros v Hin;
	            apply value_roots_within_from_refs_exclude;
	            intros root Hexclude;
	            pose proof (Hexclude_payload root
	              (roots_exclude_stores_subset root roots0 roots1 Hsubset Hexclude))
	              as Hall;
	            eapply Forall_forall in Hall; eauto
	        end.
	      + intros root Hexclude.
	      match goal with
	      | Hvalue : forall root, roots_exclude root _ -> _ |- _ =>
	          apply Hvalue
      end.
      unfold roots_exclude in *.
      intros Hin.
      apply Hexclude.
      apply H. exact Hin.
    - constructor.
      intros root Hexclude.
      match goal with
      | Hvalue : forall root, roots_exclude root _ -> _ |- _ =>
          apply Hvalue
      end.
      unfold roots_exclude in *.
      intros Hin.
      apply Hexclude.
      apply H. exact Hin. }
  intros roots v roots' Hwithin Hsubset.
  exact (proj1 Hmut roots v Hwithin roots' Hsubset).
Qed.

Lemma captured_call_frame_root_tail_fresh_names_for_fresh_call :
  forall env captured Rcap s_args R_args fdef fcall used',
    captured_call_frame_ready env captured Rcap s_args R_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) (Rcap ++ R_args))
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env captured Rcap s_args R_args fdef fcall used'
    Hframe Hrename x Hin.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [_ [_ [_ [Hrn_tail [Hnamed_tail Hkeys_tail]]]]].
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names (captured ++ s_args))).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x (Rcap ++ R_args) = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x (Rcap ++ R_args)).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes; assumption.
Qed.

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
