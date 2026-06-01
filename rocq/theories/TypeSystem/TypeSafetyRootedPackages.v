From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness
  TypeSafetyRootFacts.
From Facet.TypeSystem Require Export TypeSafetyClosureRuntimeArgsFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Record rooted_eval_result
    (R' : root_env) (s' : store) (roots : root_set) (v : value) : Prop := {
  rooted_eval_store_roots : store_roots_within R' s';
  rooted_eval_value_roots : value_roots_within roots v;
  rooted_eval_store_no_shadow : store_no_shadow s';
  rooted_eval_root_env_no_shadow : root_env_no_shadow R'
}.

Record rooted_args_result
    (R' : root_env) (s' : store) (roots : list root_set)
    (vs : list value) : Prop := {
  rooted_args_store_roots : store_roots_within R' s';
  rooted_args_value_roots : Forall2 value_roots_within roots vs;
  rooted_args_store_no_shadow : store_no_shadow s';
  rooted_args_root_env_no_shadow : root_env_no_shadow R'
}.

Record rooted_fields_result
    (R' : root_env) (s' : store) (roots : root_set)
    (values : list (string * value)) : Prop := {
  rooted_fields_store_roots : store_roots_within R' s';
  rooted_fields_value_roots : value_fields_roots_within roots values;
  rooted_fields_store_no_shadow : store_no_shadow s';
  rooted_fields_root_env_no_shadow : root_env_no_shadow R'
}.

Record typed_rooted_eval_result
    (env : global_env) (s s' : store) (v : value) (T : Ty)
    (Σ' : sctx) (R' : root_env) (roots : root_set) : Prop := {
  typed_rooted_eval_store_prefix : store_typed_prefix env s' Σ';
  typed_rooted_eval_value_type : value_has_type env s' v T;
  typed_rooted_eval_refs_preserved : store_ref_targets_preserved env s s';
  typed_rooted_eval_roots : rooted_eval_result R' s' roots v
}.

Definition eval_preserves_typed_rooted_eval_statement : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_rooted_eval_result env s s' v T Σ' R' roots.

Lemma typed_rooted_eval_capture_ref_free_empty_roots :
  forall env s s' v T Σ' R' roots,
    typed_rooted_eval_result env s s' v T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    value_roots_within [] v.
Proof.
  intros env s s' v T Σ' R' roots Htyped Hfree.
  eapply value_has_type_runtime_rootless_empty_roots.
  - exact (typed_rooted_eval_value_type _ _ _ _ _ _ _ _ Htyped).
  - eapply capture_ref_free_ty_b_runtime_rootless. exact Hfree.
Qed.

Definition eval_preserves_typing_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').

Definition eval_preserves_roots_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').

Definition eval_preserves_roots_ready_mutual_package_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      rooted_eval_result R' s' roots v) /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      rooted_args_result R' s' roots vs) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      rooted_fields_result R' s' roots values).

Lemma eval_preserves_roots_ready_mutual_statement_to_package :
  eval_preserves_roots_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_package_statement.
Proof.
  intros Hplain.
  destruct Hplain as [Hex [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hex env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a
      T_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped)
      as [Hroots' [Hvalue [Hshadow' Hrn']]].
    constructor; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
        ps_a Σ_b R_b roots_a
        Hready Hroots Hshadow Hrn Htyped)
        as [Hroots' [Hvalues [Hshadow' Hrn']]].
      constructor; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
        n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots
        Hshadow Hrn Htyped)
        as [Hroots' [Hvalues [Hshadow' Hrn']]].
      constructor; assumption.
Qed.

Lemma eval_preserves_roots_ready_mutual_package_statement_to_plain :
  eval_preserves_roots_ready_mutual_package_statement ->
  eval_preserves_roots_ready_mutual_statement.
Proof.
  intros Hpackage.
  destruct Hpackage as [Hex [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
    destruct (Hex env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a
      T_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped) as
      [Hroots' Hvalue Hshadow' Hrn'].
    repeat split; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
        ps_a Σ_b R_b roots_a Hready
        Hroots Hshadow Hrn Htyped) as
        [Hroots' Hvalues Hshadow' Hrn'].
      repeat split; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
        n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hready Hroots Hshadow
        Hrn Htyped) as
        [Hroots' Hvalues Hshadow' Hrn'].
      repeat split; assumption.
Qed.

Definition eval_preserves_root_names_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      Forall (fun roots => root_set_store_roots_named roots s') roots) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_roots_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_roots_named R' s' /\
      root_set_store_roots_named roots s').

Definition eval_preserves_root_keys_named_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      root_env_store_keys_named R' s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      root_env_store_keys_named R s ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_store_keys_named R' s').

Scheme preservation_ready_expr_ind_closure :=
  Induction for preservation_ready_expr Sort Prop
with preservation_ready_args_ind_closure :=
  Induction for preservation_ready_args Sort Prop
with preservation_ready_fields_ind_closure :=
  Induction for preservation_ready_fields Sort Prop
with preservation_ready_match_branches_ind_closure :=
  Induction for preservation_ready_match_branches Sort Prop.
Combined Scheme preservation_ready_mutind_closure
  from preservation_ready_expr_ind_closure, preservation_ready_args_ind_closure,
       preservation_ready_fields_ind_closure,
       preservation_ready_match_branches_ind_closure.

Lemma preservation_ready_args_implies_provenance_ready_closure :
  forall args,
    preservation_ready_args args ->
    provenance_ready_args args.
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
  exact (proj1 (proj2 Hmut)).
Qed.
