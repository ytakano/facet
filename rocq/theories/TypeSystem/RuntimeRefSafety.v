From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness TypeSafety EnvRootSoundness
  EnvRuntimeSafety.
From Stdlib Require Import List.
Import ListNotations.

Lemma runtime_typing_refs_wf :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    runtime_refs_wf env s v) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    Forall (fun fv => runtime_refs_wf env s (snd fv)) fields).
Proof.
  intros env s.
  apply runtime_typing_ind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - eapply RRW_Ref; eassumption.
  - constructor. constructor.
  - constructor. constructor.
  - assumption.
  - constructor.
  - constructor; assumption.
Qed.

Lemma value_has_type_runtime_refs_wf :
  forall env s v T,
    value_has_type env s v T ->
    runtime_refs_wf env s v.
Proof.
  intros env s v T Htyped.
  exact (proj1 (runtime_typing_refs_wf env s) v T Htyped).
Qed.

Lemma struct_fields_have_type_runtime_refs_wf :
  forall env s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    Forall (fun fv => runtime_refs_wf env s (snd fv)) fields.
Proof.
  intros env s lts args fields defs Htyped.
  exact (proj2 (runtime_typing_refs_wf env s)
    lts args fields defs Htyped).
Qed.

Lemma store_typed_entries_refs_wf :
  forall env s entries Σ,
    Forall2 (store_entry_typed env s) entries Σ ->
    Forall (store_entry_refs_wf env s) entries.
Proof.
  intros env s entries Σ Htyped.
  induction Htyped as [|se ce s_tail Σ_tail Hentry _ IH].
  - constructor.
  - destruct se as [x T v st].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [_ [_ [_ Hv]]].
    constructor.
    + constructor. eapply value_has_type_runtime_refs_wf. exact Hv.
    + exact IH.
Qed.

Lemma store_typed_refs_wf :
  forall env s Σ,
    store_typed env s Σ ->
    store_refs_wf env s.
Proof.
  intros env s Σ Htyped.
  unfold store_typed in Htyped.
  unfold store_refs_wf.
  eapply store_typed_entries_refs_wf. exact Htyped.
Qed.

Theorem eval_no_dangling_refs_roots_ready :
  forall env s e s' v Ω n R Σ T Σ' R' roots,
    eval env s e s' v ->
    provenance_ready_expr e ->
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    runtime_refs_wf env s' v /\ store_refs_wf env s'.
Proof.
  intros env s e s' v Ω n R Σ T Σ' R' roots
    Heval Hready Hstore Hroots Hstore_shadow Hroot_shadow Htyped.
  destruct (proj1 eval_preserves_typing_roots_ready_mutual
      env s e s' v Heval
      Ω n R Σ T Σ' R' roots
      Hready Hstore Hroots Hstore_shadow Hroot_shadow Htyped)
    as [Hstore' [Hv _]].
  split.
  - eapply value_has_type_runtime_refs_wf. exact Hv.
  - eapply store_typed_refs_wf. exact Hstore'.
Qed.

Theorem infer_full_env_roots_no_dangling_refs_ready :
  forall env f R0 T Γ' R' roots s s' v,
    infer_full_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
    initial_store_for_fn env f s ->
    provenance_ready_expr (fn_body f) ->
    store_roots_within R0 s ->
    store_no_shadow s ->
    root_env_no_shadow R0 ->
    eval env s (fn_body f) s' v ->
    runtime_refs_wf env s' v /\ store_refs_wf env s'.
Proof.
  intros env f R0 T Γ' R' roots s s' v
    Hinfer Hstore Hready Hroots Hstore_shadow Hroot_shadow Heval.
  pose proof (infer_full_env_roots_sound env f R0 T Γ' R' roots Hinfer)
    as [Htyped_fn _].
  unfold typed_fn_env_roots in Htyped_fn.
  destruct Htyped_fn as [T_body [Γ_out [Htyped _]]].
  unfold initial_store_for_fn in Hstore.
  eapply eval_no_dangling_refs_roots_ready.
  - exact Heval.
  - exact Hready.
  - exact Hstore.
  - exact Hroots.
  - exact Hstore_shadow.
  - exact Hroot_shadow.
  - exact Htyped.
Qed.
