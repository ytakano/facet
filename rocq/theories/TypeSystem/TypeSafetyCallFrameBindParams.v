From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCallFrameParams.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma store_names_bind_params :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_names (bind_params ps vs s) =
      ctx_names (params_ctx ps) ++ store_names s.
Proof.
  intros env Ω s vs ps Hargs.
  induction Hargs as [| v vs p ps T_actual _ _ _ IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma store_remove_params_bind_params :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_remove_params ps (bind_params ps vs s) = s.
Proof.
  intros env Ω s vs ps Hargs.
  induction Hargs as [| v vs p ps T_actual _ _ _ IH].
  - reflexivity.
  - simpl. rewrite ident_eqb_refl. exact IH.
Qed.

Lemma store_remove_params_app :
  forall ps caps s,
    store_remove_params (ps ++ caps) s =
      store_remove_params caps (store_remove_params ps s).
Proof.
  induction ps as [| p ps IH]; intros caps s.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma store_names_remove_params_bind_params :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_names (store_remove_params ps (bind_params ps vs s)) =
      store_names s.
Proof.
  intros env Ω s vs ps Hargs.
  rewrite (store_remove_params_bind_params env Ω s vs ps Hargs).
  reflexivity.
Qed.

Lemma store_typed_remove_params_bind_params :
  forall env Ω s Σ vs ps,
    store_typed env s Σ ->
    eval_args_values_have_types env Ω s vs ps ->
    store_typed env (store_remove_params ps (bind_params ps vs s)) Σ.
Proof.
  intros env Ω s Σ vs ps Htyped Hargs.
  rewrite (store_remove_params_bind_params env Ω s vs ps Hargs).
  exact Htyped.
Qed.

Inductive store_param_prefix : list param -> store -> store -> Prop :=
  | SPP_Nil : forall s,
      store_param_prefix [] s s
  | SPP_Cons : forall p ps v st s_param s,
      store_param_prefix ps s_param s ->
      store_param_prefix (p :: ps)
        (MkStoreEntry (param_name p) (param_ty p) v st :: s_param)
        s.

Lemma store_param_prefix_bind_params :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_param_prefix ps (bind_params ps vs s) s.
Proof.
  intros env Ω s vs ps Hargs.
  induction Hargs as [| v vs p ps T_actual _ _ _ IH].
  - constructor.
  - simpl. constructor. exact IH.
Qed.

Lemma store_param_prefix_append_frame :
  forall ps s_param frame frame_tail,
    store_param_prefix ps s_param frame_tail ->
    store_param_prefix ps (s_param ++ frame) (frame_tail ++ frame).
Proof.
  intros ps s_param frame frame_tail Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH].
  - constructor.
  - simpl. constructor. exact IH.
Qed.

Lemma store_param_prefix_app :
  forall ps caps s_param frame tail,
    store_param_prefix ps s_param frame ->
    store_param_prefix caps frame tail ->
    store_param_prefix (ps ++ caps) s_param tail.
Proof.
  intros ps caps s_param frame tail Hps Hcaps.
  induction Hps as [s | p ps v st s_param s _ IH].
  - exact Hcaps.
  - simpl. constructor. exact (IH Hcaps).
Qed.

Lemma store_typed_entries_params_store_param_prefix :
  forall env full captured caps,
    sctx_of_store captured = sctx_of_ctx (params_ctx caps) ->
    Forall2 (store_entry_typed env full) captured (params_ctx caps) ->
    store_param_prefix caps captured [].
Proof.
  intros env full captured.
  induction captured as [| se captured IH]; intros caps Hshape Htyped;
    destruct caps as [| cap caps]; simpl in Htyped, Hshape; inversion Htyped; subst.
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct cap as [pname pty pmut].
    injection Hshape as Hhead Htail_shape.
    subst sx sT sst pname.
    simpl in *.
    constructor.
    eapply IH.
    + exact H1.
    + exact H4.
Qed.

Lemma captured_params_store_typed_store_param_prefix :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    store_param_prefix caps captured [].
Proof.
  intros env captured caps Htyped.
  unfold captured_params_store_typed, store_typed in Htyped.
  destruct Htyped as [Htyped Hshape].
  eapply store_typed_entries_params_store_param_prefix.
  - exact Hshape.
  - exact Htyped.
Qed.

Definition captured_params_store_typed_in_frame
    (env : global_env) (captured frame : store) (caps : list param) : Prop :=
  Forall2 (store_entry_typed env (captured ++ frame))
    captured (params_ctx caps) /\
  sctx_of_store captured = sctx_of_ctx (params_ctx caps).

Definition captured_call_frame_params_ready_in_frame
    (env : global_env) (captured : store) (Rcap : root_env)
    (s_args : store) (R_args : root_env) (caps : list param) : Prop :=
  captured_call_frame_ready_in_frame env captured Rcap s_args R_args /\
  captured_params_store_typed_in_frame env captured s_args caps.

Lemma captured_params_store_typed_in_frame_store_param_prefix :
  forall env captured frame caps,
    captured_params_store_typed_in_frame env captured frame caps ->
    store_param_prefix caps captured [].
Proof.
  intros env captured frame caps Htyped.
  unfold captured_params_store_typed_in_frame in Htyped.
  destruct Htyped as [Htyped Hshape].
  eapply store_typed_entries_params_store_param_prefix.
  - exact Hshape.
  - exact Htyped.
Qed.

Lemma captured_params_store_typed_in_frame_prefix_frame :
  forall env captured caps frame,
    captured_params_store_typed_in_frame env captured frame caps ->
    store_typed_prefix env (captured ++ frame)
      (sctx_of_ctx (params_ctx caps)).
Proof.
  intros env captured caps frame Htyped.
  unfold captured_params_store_typed_in_frame, store_typed_prefix in *.
  destruct Htyped as [Htyped _].
  exists captured, frame.
  split; [reflexivity | exact Htyped].
Qed.

Lemma captured_params_store_typed_in_frame_from_self :
  forall env captured caps frame,
    captured_params_store_typed env captured caps ->
    captured_params_store_typed_in_frame env captured frame caps.
Proof.
  intros env captured caps frame Htyped.
  unfold captured_params_store_typed, captured_params_store_typed_in_frame,
    store_typed in *.
  destruct Htyped as [Htyped Hshape].
  split.
  - eapply store_typed_entries_store_preserved.
    + exact Htyped.
    + apply store_ref_targets_preserved_app_left.
  - exact Hshape.
Qed.

Lemma captured_call_frame_params_ready_in_frame_from_self :
  forall env captured Rcap s_args R_args caps,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    captured_call_frame_params_ready_in_frame
      env captured Rcap s_args R_args caps.
Proof.
  intros env captured Rcap s_args R_args caps [Hframe Htyped].
  split.
  - eapply captured_call_frame_ready_in_frame_from_self. exact Hframe.
  - eapply captured_params_store_typed_in_frame_from_self. exact Htyped.
Qed.

Lemma copy_capture_store_exact_with_env_params_store_typed_in_frame :
  forall Ω env s Σ captures caps captured env_lt captured_tys frame,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (captured ++ frame) ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    captured_params_store_typed_in_frame env captured frame caps.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys frame
    Hstore Hpres Hcopy Hcheck.
  unfold captured_params_store_typed_in_frame.
  pose proof
    (copy_capture_store_as_captured_entries_typed_with_env_preserved
      Ω env (captured ++ frame) s Σ captures caps captured env_lt
      captured_tys Hstore Hpres Hcopy Hcheck) as Htyped.
  pose proof
    (copy_capture_store_exact_with_env_sctx_of_store
      Ω env s Σ captures caps captured env_lt captured_tys
      Hstore Hcopy Hcheck) as Heq.
  rewrite Heq in Htyped.
  split; [exact Htyped | exact Heq].
Qed.

Lemma captured_params_store_typed_prefix_frame :
  forall env captured caps frame,
    captured_params_store_typed env captured caps ->
    store_typed_prefix env (captured ++ frame)
      (sctx_of_ctx (params_ctx caps)).
Proof.
  intros env captured caps frame Htyped.
  unfold captured_params_store_typed, store_typed_prefix in *.
  destruct Htyped as [Htyped _].
  exists captured, frame.
  split; [reflexivity |].
  eapply store_typed_entries_store_preserved.
  - exact Htyped.
  - apply store_ref_targets_preserved_app_left.
Qed.

Lemma store_names_store_param_prefix :
  forall ps s_param s,
    store_param_prefix ps s_param s ->
    store_names s_param = ctx_names (params_ctx ps) ++ store_names s.
Proof.
  intros ps s_param s Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
