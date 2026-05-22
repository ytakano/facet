From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootedPackages TypeSafetyFrameScopeReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Definition eval_preserves_frame_scope_roots_ready_mutual_statement : Prop :=
  frame_scope_roots_ready_expr_preservation /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame).

Definition eval_preserves_typing_roots_ready_prefix_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
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
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
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
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').

Record typed_rooted_args_result
    (env : global_env) (Ω : outlives_ctx) (s s' : store)
    (vs : list value) (ps : list param) (Σ' : sctx)
    (R' : root_env) (roots : list root_set) : Prop := {
  typed_rooted_args_store_prefix : store_typed_prefix env s' Σ';
  typed_rooted_args_values_types :
    eval_args_values_have_types env Ω s' vs ps;
  typed_rooted_args_refs_preserved : store_ref_targets_preserved env s s';
  typed_rooted_args_roots : rooted_args_result R' s' roots vs
}.

Record typed_rooted_fields_result
    (env : global_env) (s s' : store) (lts : list lifetime)
    (args : list Ty) (values : list (string * value))
    (defs : list field_def) (Σ' : sctx) (R' : root_env)
    (roots : root_set) : Prop := {
  typed_rooted_fields_store_prefix : store_typed_prefix env s' Σ';
  typed_rooted_fields_values_types :
    struct_fields_have_type env s' lts args values defs;
  typed_rooted_fields_refs_preserved : store_ref_targets_preserved env s s';
  typed_rooted_fields_roots : rooted_fields_result R' s' roots values
}.

Definition eval_preserves_typing_roots_ready_prefix_mutual_package_statement
    : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_rooted_eval_result env s s' v T Σ' R' roots) /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      typed_rooted_args_result env Ω s s' vs ps Σ' R' roots) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      typed_rooted_fields_result env s s' lts args values defs Σ' R' roots).

Lemma eval_preserves_typing_roots_ready_prefix_mutual_statement_to_package :
  eval_preserves_typing_roots_ready_prefix_mutual_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement.
Proof.
  intros [Hexpr [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
    destruct (Hexpr env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a
                Σ_a T_a Σ_b R_b roots_a
                Hprov Hprefix Hroots Hshadow Hrn Htyped)
      as [Hprefix' [Hv [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
    constructor.
    + exact Hprefix'.
    + exact Hv.
    + exact Hpres.
    + constructor; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
                  ps_a Σ_b R_b roots_a
                  Hprov Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' [Hvs [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
      constructor.
      * exact Hprefix'.
      * exact Hvs.
      * exact Hpres.
      * constructor; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow
      Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
                  n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov
                  Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' [Hvalues [Hpres [Hroots' [Hvroots [Hshadow' Hrn']]]]]].
      constructor.
      * exact Hprefix'.
      * exact Hvalues.
      * exact Hpres.
      * constructor; assumption.
Qed.

Lemma eval_preserves_typing_roots_ready_prefix_mutual_package_statement_to_plain :
  eval_preserves_typing_roots_ready_prefix_mutual_package_statement ->
  eval_preserves_typing_roots_ready_prefix_mutual_statement.
Proof.
  intros [Hexpr [Hargs Hfields]].
  split.
  - intros env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a Σ_a T_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
    destruct (Hexpr env_a st_a expr_a st_b val_a Heval Ω_a n_a R_a
                Σ_a T_a Σ_b R_b roots_a
                Hprov Hprefix Hroots Hshadow Hrn Htyped)
      as [Hprefix' Hv Hpres Hrooted].
    destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
    repeat split; assumption.
  - split.
    + intros env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a ps_a
      Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow Hrn Htyped.
      destruct (Hargs env_a st_a args_a st_b vs_a Heval Ω_a n_a R_a Σ_a
                  ps_a Σ_b R_b roots_a
                  Hprov Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' Hvs Hpres Hrooted].
      destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
      repeat split; assumption.
    + intros env_a st_a fields_a defs_a st_b values_a Heval Ω_a n_a lts_a
      ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov Hprefix Hroots Hshadow
      Hrn Htyped.
      destruct (Hfields env_a st_a fields_a defs_a st_b values_a Heval Ω_a
                  n_a lts_a ty_args_a R_a Σ_a Σ_b R_b roots_a Hprov
                  Hprefix Hroots Hshadow Hrn Htyped)
        as [Hprefix' Hvalues Hpres Hrooted].
      destruct Hrooted as [Hroots' Hvroots Hshadow' Hrn'].
      repeat split; assumption.
Qed.

Definition eval_preserves_param_scope_roots_ready_mutual_statement : Prop :=
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
        ps frame,
      provenance_ready_args args ->
      typed_args_roots env Ω n R Σ args params Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
        ps frame,
      provenance_ready_fields fields ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      root_env_covers_params ps R ->
      store_param_scope ps s frame ->
      exists frame', store_param_scope ps s' frame').
