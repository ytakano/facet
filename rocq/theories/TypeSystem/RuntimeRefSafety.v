From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness TypeSafety EnvRootSoundness
  EnvRuntimeSafety.
From Stdlib Require Import List String.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Direct runtime reference membership                                  *)
(* ------------------------------------------------------------------ *)

(* This slice tracks direct references contained in values and stores.
   Captured closure refs need scoped closure-store invariants and are
   intentionally deferred here. *)
Inductive refs_in_value : value -> ident -> field_path -> Prop :=
  | RIV_Struct : forall name fields x path,
      refs_in_fields fields x path ->
      refs_in_value (VStruct name fields) x path
  | RIV_Ref : forall x path,
      refs_in_value (VRef x path) x path
with refs_in_store_entry : store_entry -> ident -> field_path -> Prop :=
  | RISE_Entry : forall sx T v st x path,
      refs_in_value v x path ->
      refs_in_store_entry (MkStoreEntry sx T v st) x path
with refs_in_store : store -> ident -> field_path -> Prop :=
  | RIS_Head : forall se rest x path,
      refs_in_store_entry se x path ->
      refs_in_store (se :: rest) x path
  | RIS_Tail : forall se rest x path,
      refs_in_store rest x path ->
      refs_in_store (se :: rest) x path
with refs_in_fields : list (string * value) -> ident -> field_path -> Prop :=
  | RIF_Head : forall name v rest x path,
      refs_in_value v x path ->
      refs_in_fields ((name, v) :: rest) x path
  | RIF_Tail : forall fv rest x path,
      refs_in_fields rest x path ->
      refs_in_fields (fv :: rest) x path.

Scheme refs_in_value_ind' := Induction for refs_in_value Sort Prop
with refs_in_store_entry_ind' := Induction for refs_in_store_entry Sort Prop
with refs_in_store_ind' := Induction for refs_in_store Sort Prop
with refs_in_fields_ind' := Induction for refs_in_fields Sort Prop.
Combined Scheme refs_in_mutind
  from refs_in_value_ind', refs_in_store_entry_ind',
       refs_in_store_ind', refs_in_fields_ind'.

Lemma runtime_refs_wf_ref_target :
  forall env s x path,
    runtime_refs_wf env s (VRef x path) ->
    exists se v T,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v /\
      type_lookup_path env (se_ty se) path = Some T.
Proof.
  intros env s x path Hwf.
  inversion Hwf; subst.
  exists se, v, T.
  split; [assumption | split; assumption].
Qed.

Lemma runtime_refs_wf_refs_in_value_target :
  forall env s v x path,
    runtime_refs_wf env s v ->
    refs_in_value v x path ->
    exists se v_target T,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T
with runtime_refs_wf_refs_in_fields_target :
  forall env s fields x path,
    Forall (fun fv => runtime_refs_wf env s (snd fv)) fields ->
    refs_in_fields fields x path ->
    exists se v_target T,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T.
Proof.
  - intros env s v x path Hwf Hrefs.
    destruct Hrefs.
    + inversion Hwf; subst.
      eapply runtime_refs_wf_refs_in_fields_target; eassumption.
    + eapply runtime_refs_wf_ref_target. exact Hwf.
  - intros env s fields x path Hwf_fields Hrefs.
    destruct Hrefs.
    + inversion Hwf_fields; subst.
      eapply runtime_refs_wf_refs_in_value_target; eassumption.
    + inversion Hwf_fields; subst.
      eapply runtime_refs_wf_refs_in_fields_target; eassumption.
Qed.

Lemma store_entry_refs_wf_refs_in_target :
  forall env s se x path,
    store_entry_refs_wf env s se ->
    refs_in_store_entry se x path ->
    exists se_target v_target T,
      store_lookup x s = Some se_target /\
      value_lookup_path (se_val se_target) path = Some v_target /\
      type_lookup_path env (se_ty se_target) path = Some T.
Proof.
  intros env s se x path Hwf Hrefs.
  destruct Hrefs.
  inversion Hwf; subst.
  eapply runtime_refs_wf_refs_in_value_target; eassumption.
Qed.

Lemma store_refs_wf_refs_in_store_target_aux :
  forall env s_lookup s x path,
    Forall (store_entry_refs_wf env s_lookup) s ->
    refs_in_store s x path ->
    exists se v_target T,
      store_lookup x s_lookup = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T.
Proof.
  intros env s_lookup s x path Hwf Hrefs.
  induction Hrefs.
  - inversion Hwf; subst.
    eapply store_entry_refs_wf_refs_in_target; eassumption.
  - inversion Hwf; subst.
    eapply IHHrefs.
    match goal with
    | H : Forall _ rest |- _ => exact H
    end.
Qed.

Lemma store_refs_wf_refs_in_store_target :
  forall env s x path,
    store_refs_wf env s ->
    refs_in_store s x path ->
    exists se v_target T,
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v_target /\
      type_lookup_path env (se_ty se) path = Some T.
Proof.
  intros env s x path Hwf Hrefs.
  eapply store_refs_wf_refs_in_store_target_aux; eassumption.
Qed.

Lemma value_roots_within_refs_in :
  forall roots v x path,
    value_roots_within roots v ->
    refs_in_value v x path ->
    In x roots
with value_fields_roots_within_refs_in :
  forall roots fields x path,
    value_fields_roots_within roots fields ->
    refs_in_fields fields x path ->
    In x roots.
Proof.
  - intros roots v x path Hwithin Hrefs.
    destruct Hrefs.
    + inversion Hwithin; subst.
      eapply value_fields_roots_within_refs_in; eassumption.
    + inversion Hwithin; subst. assumption.
  - intros roots fields x path Hwithin Hrefs.
    destruct Hrefs.
    + inversion Hwithin; subst.
      eapply value_roots_within_refs_in; eassumption.
    + inversion Hwithin; subst.
      eapply value_fields_roots_within_refs_in; eassumption.
Qed.

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
