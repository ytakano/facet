From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness
  TypeSafetyHiddenFrame TypeSafetyClosure TypeSafetyDirectCall
  TypeSafetyCapturedCall TypeSafetyDirectPlace TypeSafetyLocalFacts.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Theorem eval_preserves_root_names_ready_mutual_core :
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
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
Proof.
  intros Hpreserve.
  split.
  - intros env s e s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Hnamed Htyped.
    destruct (proj1 Hpreserve
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' _].
    assert (Hctx_named : root_env_ctx_roots_named R Σ)
      by (eapply root_env_store_roots_named_to_ctx; eassumption).
    destruct (proj1 (typed_roots_ctx_roots_named_mutual env Ω n)
                R Σ e T Σ' R' roots Htyped Hrn Hctx_named)
      as [Henv_named Hroot_named].
    split.
    + eapply root_env_ctx_roots_named_store_typed; eassumption.
    + eapply root_set_ctx_roots_named_store_typed; eassumption.
  - split.
    + intros env s args s' vs Heval Ω n R Σ ps Σ' R' roots Hready
        Hstore Hroots Hnodup Hrn Hnamed Htyped.
      destruct (proj1 (proj2 Hpreserve)
                  env s args s' vs Heval Ω n R Σ ps Σ' R' roots
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' _].
      assert (Hctx_named : root_env_ctx_roots_named R Σ)
        by (eapply root_env_store_roots_named_to_ctx; eassumption).
      destruct (proj1 (proj2 (typed_roots_ctx_roots_named_mutual env Ω n))
                  R Σ args ps Σ' R' roots Htyped Hrn Hctx_named)
        as [Henv_named Hroots_named].
      split.
      * eapply root_env_ctx_roots_named_store_typed; eassumption.
      * eapply root_sets_ctx_roots_named_store_typed; eassumption.
    + intros env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
        roots Hready Hstore Hroots Hnodup Hrn Hnamed Htyped.
      destruct (proj2 (proj2 Hpreserve)
                  env s fields defs s' values Heval Ω n lts args R Σ Σ'
                  R' roots Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' _].
      assert (Hctx_named : root_env_ctx_roots_named R Σ)
        by (eapply root_env_store_roots_named_to_ctx; eassumption).
      destruct (proj1 (proj2 (proj2
                  (typed_roots_ctx_roots_named_mutual env Ω n)))
                  lts args R Σ fields defs Σ' R' roots Htyped Hrn
                  Hctx_named)
        as [Henv_named Hroot_named].
      split.
      * eapply root_env_ctx_roots_named_store_typed; eassumption.
      * eapply root_set_ctx_roots_named_store_typed; eassumption.
Qed.

Theorem eval_preserves_root_keys_named_ready_mutual_core :
  ((forall env s e s' v,
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
      root_env_no_shadow R')) ->
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
Proof.
  intros Hpreserve.
  split.
  - intros env s e s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Hnamed Htyped.
    destruct (proj1 Hpreserve
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' _].
    assert (Hctx_named : root_env_ctx_keys_named R Σ)
      by (eapply root_env_store_keys_named_to_ctx; eassumption).
    pose proof (proj1 (typed_roots_ctx_keys_named_mutual env Ω n)
                  R Σ e T Σ' R' roots Htyped Hrn Hctx_named)
      as Henv_named.
    eapply root_env_ctx_keys_named_store_typed; eassumption.
  - split.
    + intros env s args s' vs Heval Ω n R Σ ps Σ' R' roots Hready
        Hstore Hroots Hnodup Hrn Hnamed Htyped.
      destruct (proj1 (proj2 Hpreserve)
                  env s args s' vs Heval Ω n R Σ ps Σ' R' roots
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' _].
      assert (Hctx_named : root_env_ctx_keys_named R Σ)
        by (eapply root_env_store_keys_named_to_ctx; eassumption).
      pose proof (proj1 (proj2 (typed_roots_ctx_keys_named_mutual env Ω n))
                    R Σ args ps Σ' R' roots Htyped Hrn Hctx_named)
        as Henv_named.
      eapply root_env_ctx_keys_named_store_typed; eassumption.
    + intros env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
        roots Hready Hstore Hroots Hnodup Hrn Hnamed Htyped.
      destruct (proj2 (proj2 Hpreserve)
                  env s fields defs s' values Heval Ω n lts args R Σ Σ'
                  R' roots Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' _].
      assert (Hctx_named : root_env_ctx_keys_named R Σ)
        by (eapply root_env_store_keys_named_to_ctx; eassumption).
      pose proof (proj1 (proj2 (proj2
                    (typed_roots_ctx_keys_named_mutual env Ω n)))
                    lts args R Σ fields defs Σ' R' roots Htyped Hrn
                    Hctx_named)
        as Henv_named.
      eapply root_env_ctx_keys_named_store_typed; eassumption.
Qed.

Lemma root_env_store_keys_named_excludes_names :
  forall R s names,
    root_env_store_keys_named R s ->
    Forall (fun x => ~ In x (store_names s)) names ->
    forall x, In x names -> root_env_lookup x R = None.
Proof.
  intros R s names Hnamed Hfresh x Hin.
  eapply root_env_store_keys_named_lookup_excludes_name.
  - exact Hnamed.
  - apply (proj1 (Forall_forall _ _) Hfresh). exact Hin.
Qed.
