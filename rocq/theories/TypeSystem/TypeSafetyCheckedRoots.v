From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRoots TypeSafetyRootFacts TypeSafetyRootedPackages
  TypeSafetyRootsReadyMutual.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Inductive typed_env_roots_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERC_Conservative : forall R Σ e T Σ' R' roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' roots
  | TERC_CaptureRefFreeResult : forall R Σ e T Σ' R' roots,
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' [].

Inductive typed_env_roots_shadow_safe_checked
    (env : global_env) (Ω : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set -> Prop :=
  | TERSC_Conservative : forall R Σ e T Σ' R' roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots
  | TERSC_CaptureRefFreeResult : forall R Σ e T Σ' R' roots,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' [].

Lemma typed_env_roots_checked_of_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped.
  apply TERC_Conservative. exact Htyped.
Qed.

Lemma typed_env_roots_checked_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply TERC_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_checked_underlying_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    exists roots0,
      typed_env_roots env Ω n R Σ e T Σ' R' roots0 /\
      (roots = roots0 \/
        (roots = [] /\ capture_ref_free_ty_b env T = true)).
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped Hfree].
  - exists roots0. split; [exact Htyped | left; reflexivity].
  - exists roots0. split; [exact Htyped | right; split; reflexivity || exact Hfree].
Qed.

Lemma typed_env_roots_checked_prune_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked Hfree.
  destruct (typed_env_roots_checked_underlying_roots env Ω n R Σ e T Σ' R' roots
    Hchecked) as [roots0 [Htyped _]].
  eapply typed_env_roots_checked_capture_ref_free; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_checked_of_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped.
  apply TERSC_Conservative. exact Htyped.
Qed.

Lemma typed_env_roots_shadow_safe_checked_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply TERSC_CaptureRefFreeResult; eassumption.
Qed.

Lemma typed_env_roots_shadow_safe_checked_underlying_roots :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    exists roots0,
      typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots0 /\
      (roots = roots0 \/
        (roots = [] /\ capture_ref_free_ty_b env T = true)).
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped Hfree].
  - exists roots0. split; [exact Htyped | left; reflexivity].
  - exists roots0. split; [exact Htyped | right; split; reflexivity || exact Hfree].
Qed.

Lemma typed_env_roots_shadow_safe_checked_prune_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked Hfree.
  destruct (typed_env_roots_shadow_safe_checked_underlying_roots
    env Ω n R Σ e T Σ' R' roots Hchecked) as [roots0 [Htyped _]].
  eapply typed_env_roots_shadow_safe_checked_capture_ref_free; eassumption.
Qed.

Lemma typed_env_roots_checked_empty_of_shadow_safe_capture_ref_free :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    capture_ref_free_ty_b env T = true ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' [].
Proof.
  intros env Ω n R Σ e T Σ' R' roots Htyped Hfree.
  eapply typed_env_roots_checked_capture_ref_free.
  - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
  - exact Hfree.
Qed.

Lemma typed_env_roots_checked_structural :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  destruct Hchecked as [? ? ? ? ? ? ? Htyped | ? ? ? ? ? ? ? Htyped _];
    eapply typed_env_roots_structural; exact Htyped.
Qed.

Lemma typed_env_roots_shadow_safe_checked_checked :
  forall env Ω n R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe_checked env Ω n R Σ e T Σ' R' roots ->
    typed_env_roots_checked env Ω n R Σ e T Σ' R' roots.
Proof.
  intros env Ω n R Σ e T Σ' R' roots Hchecked.
  destruct Hchecked as [? ? ? ? ? ? ? Htyped | ? ? ? ? ? ? ? Htyped Hfree].
  - apply TERC_Conservative.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped.
  - eapply TERC_CaptureRefFreeResult.
    + eapply typed_env_roots_shadow_safe_roots. exact Htyped.
    + exact Hfree.
Qed.

Theorem eval_preserves_roots_ready_prefix_checked_expr :
  eval_preserves_typing_ready_prefix_for_roots_ready_statement ->
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots_checked env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s'.
Proof.
  intros Hpres env s e s' v Heval Ω n R Σ T Σ' R' roots
    Hprov Hready Hstore Hroots Hshadow Hrn Hchecked.
  destruct Hchecked as
    [R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped
    |R0 Σ0 e0 T0 Σ0' R0' roots0 Htyped Hfree].
  - eapply (proj1 (eval_preserves_roots_ready_prefix_mutual_with_preservation_core
      Hpres)); eassumption.
  - destruct (proj1 Hpres env s e0 s' v Heval Ω n Σ0 T0 Σ0'
        Hready Hstore
        (typed_env_roots_structural env Ω n R0 Σ0 e0 T0 Σ0' R0' roots0
          Htyped)) as [Hstore' [Hv_typed Hrefs]].
    destruct (proj1 eval_preserves_roots_ready_mutual env s e0 s' v Heval
        Ω n R0 Σ0 T0 Σ0' R0' roots0 Hprov Hroots Hshadow Hrn Htyped)
      as [Hroots' [_ [Hshadow' Hrn']]].
    repeat split; try assumption.
    eapply value_has_type_runtime_rootless_empty_roots.
    + exact Hv_typed.
    + eapply capture_ref_free_ty_b_runtime_rootless. exact Hfree.
Qed.
