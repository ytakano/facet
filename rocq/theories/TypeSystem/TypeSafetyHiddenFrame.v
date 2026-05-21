From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma NoDup_app_left_ts : forall (xs ys : list ident),
  NoDup (xs ++ ys) ->
  NoDup xs.
Proof.
  intros xs ys Hnodup.
  induction xs as [| x xs IH]; simpl in *.
  - constructor.
  - inversion Hnodup; subst.
    constructor.
    + intro Hin. apply H1. apply in_or_app. left. exact Hin.
    + apply IH. exact H2.
Qed.

Lemma NoDup_app_right_ts : forall (xs ys : list ident),
  NoDup (xs ++ ys) ->
  NoDup ys.
Proof.
  intros xs ys Hnodup.
  induction xs as [| x xs IH]; simpl in *.
  - exact Hnodup.
  - inversion Hnodup; subst. apply IH. exact H2.
Qed.

Fixpoint ty_compatible_refl (Ω : outlives_ctx) (T : Ty)
    {struct T} : ty_compatible Ω T T :=
  match T with
  | MkTy u (TRef l RShared Tinner) =>
      TC_Ref_Shared Ω u u l l Tinner Tinner
        (US_refl u) (Outlives_refl Ω l) (ty_compatible_refl Ω Tinner)
  | MkTy u (TRef l RUnique Tinner) =>
      TC_Ref_Unique Ω u u l l Tinner
        (US_refl u) (Outlives_refl Ω l)
  | MkTy u (TFn params ret) =>
      let fix go (xs : list Ty)
          : Forall2 (fun expected actual => ty_compatible Ω expected actual)
              xs xs :=
        match xs with
        | [] =>
            @Forall2_nil Ty Ty
              (fun expected actual => ty_compatible Ω expected actual)
        | x :: xs' =>
            @Forall2_cons Ty Ty
              (fun expected actual => ty_compatible Ω expected actual)
              x x xs' xs' (ty_compatible_refl Ω x) (go xs')
        end in
      TC_Fn Ω u u params params ret ret
        (US_refl u) (go params) (ty_compatible_refl Ω ret)
  | MkTy u (TClosure l params ret) =>
      let fix go (xs : list Ty)
          : Forall2 (fun expected actual => ty_compatible Ω expected actual)
              xs xs :=
        match xs with
        | [] =>
            @Forall2_nil Ty Ty
              (fun expected actual => ty_compatible Ω expected actual)
        | x :: xs' =>
            @Forall2_cons Ty Ty
              (fun expected actual => ty_compatible Ω expected actual)
              x x xs' xs' (ty_compatible_refl Ω x) (go xs')
        end in
      TC_Closure Ω u u l l params params ret ret
        (US_refl u) (Outlives_refl Ω l) (go params) (ty_compatible_refl Ω ret)
  | MkTy u (TForall n Ω_forall body) =>
      TC_Forall Ω u u n Ω_forall body body
        (US_refl u) (ty_compatible_refl Ω body)
  | MkTy u core =>
      TC_Core Ω u u core core (US_refl u) eq_refl
  end.

Lemma value_roots_within_excludes :
  (forall roots v,
    value_roots_within roots v ->
    forall root,
      roots_exclude root roots ->
      value_refs_exclude_root root v) /\
  (forall R se,
    store_entry_roots_within R se ->
    forall root,
      root_env_excludes root R ->
      se_name se <> root ->
      store_entry_refs_exclude_root root se) /\
  (forall R s,
    store_roots_within R s ->
    forall root,
      root_env_excludes root R ->
      (forall se, In se s -> se_name se <> root) ->
      store_refs_exclude_root root s) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall root,
      roots_exclude root roots ->
      value_fields_refs_exclude_root root fields).
Proof.
  apply value_roots_within_mutind; intros;
    try solve [constructor; eauto].
  - econstructor.
    destruct (ident_eqb root x) eqn:Hroot; try reflexivity.
    apply ident_eqb_eq in Hroot. subst x. contradiction.
  - constructor. constructor.
  - constructor.
    { eapply H; eauto.
      eapply H2. simpl. left. reflexivity. }
    { eapply H0; eauto.
      intros se0 Hin. eapply H2. simpl. right. exact Hin. }
Qed.

Lemma value_roots_exclude_root :
  forall roots v root,
    value_roots_within roots v ->
    roots_exclude root roots ->
    value_refs_exclude_root root v.
Proof.
  intros roots v root Hwithin Hexclude.
  exact (proj1 value_roots_within_excludes roots v Hwithin root Hexclude).
Qed.

Lemma NoDup_app_not_in_right_ts : forall (xs ys : list ident) x,
  NoDup (xs ++ ys) ->
  In x xs ->
  ~ In x ys.
Proof.
  intros xs ys x Hnodup Hin Hiny.
  induction xs as [| y xs IH]; simpl in *.
  - contradiction.
  - inversion Hnodup; subst.
    destruct Hin as [Heq | Hin].
    + subst y. apply H1. apply in_or_app. right. exact Hiny.
    + apply IH.
      * exact H2.
      * exact Hin.
Qed.

Lemma root_env_lookup_app_left :
  forall x R1 R2 roots,
    root_env_lookup x R1 = Some roots ->
    root_env_lookup x (R1 ++ R2) = Some roots.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 roots Hlookup;
    simpl; simpl in Hlookup; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - exact Hlookup.
  - apply IH. exact Hlookup.
Qed.

Lemma root_env_lookup_app_right :
  forall x R1 R2,
    root_env_lookup x R1 = None ->
    root_env_lookup x (R1 ++ R2) = root_env_lookup x R2.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 Hlookup;
    simpl; simpl in Hlookup; try reflexivity.
  destruct (ident_eqb x y) eqn:Heq.
  - discriminate.
  - apply IH. exact Hlookup.
Qed.

Lemma root_env_names_app :
  forall R1 R2,
    root_env_names (R1 ++ R2) = root_env_names R1 ++ root_env_names R2.
Proof.
  intros R1.
  induction R1 as [| [x roots] rest IH]; intros R2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma root_env_no_shadow_app :
  forall R1 R2,
    root_env_no_shadow R1 ->
    root_env_no_shadow R2 ->
    (forall x,
      root_env_lookup x R1 = None \/
      root_env_lookup x R2 = None) ->
    root_env_no_shadow (R1 ++ R2).
Proof.
  unfold root_env_no_shadow.
  intros R1.
  induction R1 as [| [x roots] rest IH]; intros R2 Hrn1 Hrn2 Hdisj;
    simpl in *.
  - exact Hrn2.
  - inversion Hrn1 as [| ? ? Hnotin Hrn_tail]; subst.
    constructor.
    + intros Hin.
      rewrite root_env_names_app in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hnotin. exact Hin.
      * specialize (Hdisj x).
        simpl in Hdisj.
        rewrite ident_eqb_refl in Hdisj.
        destruct Hdisj as [Hnone | Hnone]; try discriminate.
        eapply root_env_lookup_none_not_in_names; eassumption.
    + apply IH.
      * exact Hrn_tail.
      * exact Hrn2.
      * intros y.
        specialize (Hdisj y).
        simpl in Hdisj.
        destruct (ident_eqb y x); try exact Hdisj.
        right. destruct Hdisj as [Hbad | Hnone]; try discriminate.
        exact Hnone.
Qed.

Lemma root_env_no_shadow_app_lookup_right_none :
  forall R1 R2 x roots,
    root_env_no_shadow (R1 ++ R2) ->
    root_env_lookup x R2 = Some roots ->
    root_env_lookup x R1 = None.
Proof.
  intros R1 R2 x roots Hrn Hlookup_right.
  destruct (root_env_lookup x R1) as [roots_left |] eqn:Hlookup_left;
    try reflexivity.
  exfalso.
  unfold root_env_no_shadow in Hrn.
  rewrite root_env_names_app in Hrn.
  eapply (NoDup_app_not_in_right_ts (root_env_names R1)
            (root_env_names R2) x Hrn).
  - eapply root_env_lookup_some_in_names. exact Hlookup_left.
  - eapply root_env_lookup_some_in_names. exact Hlookup_right.
Qed.

Lemma root_env_excludes_app :
  forall x R1 R2,
    root_env_excludes x R1 ->
    root_env_excludes x R2 ->
    root_env_excludes x (R1 ++ R2).
Proof.
  unfold root_env_excludes.
  intros x R1 R2 Hexcl1 Hexcl2 y roots Hlookup Hyx.
  destruct (root_env_lookup y R1) as [roots1 |] eqn:Hlookup1.
  - rewrite (root_env_lookup_app_left y R1 R2 roots1 Hlookup1)
      in Hlookup.
    inversion Hlookup. subst roots1. eapply Hexcl1; eassumption.
  - rewrite (root_env_lookup_app_right y R1 R2 Hlookup1) in Hlookup.
    eapply Hexcl2; eassumption.
Qed.

Definition store_no_shadow (s : store) : Prop :=
  NoDup (store_names s).

Definition captured_store_runtime_ready
    (env : global_env) (captured : store) (Rcap : root_env) : Prop :=
  captured_store_typed env captured /\
  store_roots_within Rcap captured /\
  store_no_shadow captured /\
  root_env_no_shadow Rcap /\
  root_env_store_roots_named Rcap captured /\
  root_env_store_keys_named Rcap captured.

Definition captured_call_frame_ready
    (env : global_env) (captured : store) (Rcap : root_env)
    (s_args : store) (R_args : root_env) : Prop :=
  captured_store_runtime_ready env captured Rcap /\
  store_roots_within R_args s_args /\
  store_no_shadow (captured ++ s_args) /\
  root_env_no_shadow (Rcap ++ R_args) /\
  root_env_store_roots_named (Rcap ++ R_args) (captured ++ s_args) /\
  root_env_store_keys_named (Rcap ++ R_args) (captured ++ s_args).

Definition captured_params_store_typed
    (env : global_env) (captured : store) (caps : list param) : Prop :=
  store_typed env captured (sctx_of_ctx (params_ctx caps)).

Definition captured_call_frame_params_ready
    (env : global_env) (captured : store) (Rcap : root_env)
    (s_args : store) (R_args : root_env) (caps : list param) : Prop :=
  captured_call_frame_ready env captured Rcap s_args R_args /\
  captured_params_store_typed env captured caps.

Lemma check_make_closure_captures_exact_sctx_sound :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    typed_captures Ω Σ captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - injection Hcheck as <-.
    split; constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    destruct (IH caps captured_rest Hrest) as [Htyped_tail Htys_tail].
    assert (Havailable : binding_available_b st [] = true).
    { unfold binding_available_b.
      rewrite Hconsumed, Hmoved. reflexivity. }
    assert (HTeq : T = param_ty cap).
    { apply ty_eqb_true. exact Hty_eq. }
    subst T.
    split.
    + eapply TCap_Cons.
      * unfold sctx_lookup in Hlookup.
        eapply ctx_lookup_state_available_nil_lookup; eassumption.
      * exact Hmut.
      * apply usage_eqb_true. exact Husage.
      * apply (capture_ref_free_ty_b_ty_ref_free env (param_ty cap)).
        exact Href_free.
      * apply ty_compatible_refl.
      * exact Htyped_tail.
    + simpl. rewrite Htys_tail. reflexivity.
Qed.

Lemma binding_available_nil_fresh :
  forall st,
    binding_available_b st [] = true ->
    st = binding_state_of_bool false.
Proof.
  intros [consumed moved] Havailable.
  unfold binding_available_b in Havailable.
  destruct consumed; simpl in Havailable; try discriminate.
  destruct moved as [| p moved']; simpl in Havailable; try discriminate.
  reflexivity.
Qed.

Lemma copy_capture_store_exact_sctx_of_store :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps).
Proof.
  intros Ω env s Σ captures.
  induction captures as [| x captures IH]; intros caps captured captured_tys
    Hstore Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest_tys | err] eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    apply andb_true_iff in Hcopy_ok.
    destruct Hcopy_ok as [Hruntime_available _].
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [_ _]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    apply binding_available_nil_fresh in Hruntime_available.
    simpl.
    rewrite Hruntime_available.
    change (sctx_of_ctx (param_ctx_entry cap :: params_ctx caps)) with
      ((param_name cap, param_ty cap, binding_state_of_bool false,
        param_mutability cap) :: sctx_of_ctx (params_ctx caps)).
    rewrite Hcap_mut.
    f_equal.
    + rewrite <- H0, Hty_eq. reflexivity.
    + eapply IH.
      * exact Hstore.
      * exact Hcopy_rest.
      * exact Hrest_check.
Qed.

Lemma captured_store_typed_as_params :
  forall env captured caps,
    captured_store_typed env captured ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps) ->
    captured_params_store_typed env captured caps.
Proof.
  intros env captured caps Htyped Heq.
  unfold captured_store_typed, captured_params_store_typed in *.
  rewrite <- Heq.
  exact Htyped.
Qed.

Lemma copy_capture_store_exact_params_store_typed :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    captured_store_typed env captured ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_params_store_typed env captured caps.
Proof.
  intros Ω env s Σ captures caps captured captured_tys
    Hstore Hcaptured Hcopy Hcheck.
  eapply captured_store_typed_as_params.
  - exact Hcaptured.
  - eapply (copy_capture_store_exact_sctx_of_store
      Ω env s Σ captures caps captured captured_tys); eassumption.
Qed.

Lemma copy_capture_store_as_store_names :
  forall captures caps s captured,
    copy_capture_store_as captures caps s = Some captured ->
    store_names captured = ctx_names (params_ctx caps).
Proof.
  induction captures as [| x captures IH]; intros caps s captured Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    simpl. rewrite (IH caps s captured_rest Hcopy_rest). reflexivity.
Qed.

Lemma copy_capture_store_as_captured_entries_typed_rootless :
  forall Ω env s_target s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured) /\
    Forall (fun se => value_roots_within [] (se_val se)) captured.
Proof.
  intros Ω env s_target s Σ captures.
  revert s_target.
  induction captures as [| x captures IH]; intros s_target caps captured captured_tys
    Hstore Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-.
    split; constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest_tys | err] eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    assert (Hrootless_T : runtime_rootless_ty env T).
    { apply capture_ref_free_ty_b_runtime_rootless. exact Href_free. }
    assert (Hrootless : runtime_rootless_ty env (se_ty se)).
    { rewrite <- H0. exact Hrootless_T. }
    assert (Hvalue_target : value_has_type env s_target (se_val se) (se_ty se)).
    { eapply value_has_type_runtime_rootless_store_any.
      - exact Hvalue.
      - exact Hrootless. }
    destruct (IH s_target caps captured_rest captured_rest_tys
                Hstore Hcopy_rest Hrest_check)
      as [Htyped_tail Hroots_tail].
    split.
    + simpl. constructor.
      * exact (conj eq_refl
          (conj eq_refl
            (conj (binding_state_refines_refl (se_state se))
              Hvalue_target))).
      * exact Htyped_tail.
    + simpl. constructor.
      * eapply value_has_type_runtime_rootless_empty_roots.
        -- exact Hvalue_target.
        -- exact Hrootless.
      * exact Hroots_tail.
Qed.

Lemma copy_capture_store_as_captured_store_typed_rootless :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_store_typed env captured /\
    Forall (fun se => value_roots_within [] (se_val se)) captured.
Proof.
  intros Ω env s Σ captures caps captured captured_tys Hstore Hcopy Hcheck.
  unfold captured_store_typed.
  eapply copy_capture_store_as_captured_entries_typed_rootless; eassumption.
Qed.

Lemma captured_store_runtime_ready_empty :
  forall env,
    captured_store_runtime_ready env [] [].
Proof.
  intros env.
  unfold captured_store_runtime_ready.
  repeat split.
  - unfold captured_store_typed, store_typed. constructor.
  - constructor.
  - unfold store_no_shadow. constructor.
  - unfold root_env_no_shadow. constructor.
  - unfold root_env_store_roots_named.
    intros x roots z Hlookup _. simpl in Hlookup. discriminate.
  - unfold root_env_store_keys_named, root_env_keys_named.
    intros x Hin. simpl in Hin. contradiction.
Qed.

Lemma captured_call_frame_ready_empty :
  forall env s_args R_args,
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    captured_call_frame_ready env [] [] s_args R_args.
Proof.
  intros env s_args R_args Hroots Hshadow Hrn Hnamed Hkeys.
  unfold captured_call_frame_ready.
  split.
  - apply captured_store_runtime_ready_empty.
  - repeat split.
    + exact Hroots.
    + simpl. exact Hshadow.
    + simpl. exact Hrn.
    + simpl. exact Hnamed.
    + simpl. exact Hkeys.
Qed.

Fixpoint empty_root_env_for_store (s : store) : root_env :=
  match s with
  | [] => []
  | se :: rest => (se_name se, []) :: empty_root_env_for_store rest
  end.

Lemma root_env_lookup_empty_root_env_for_store :
  forall s x,
    In x (store_names s) ->
    root_env_lookup x (empty_root_env_for_store s) = Some [].
Proof.
  induction s as [| se rest IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst x. rewrite ident_eqb_refl. reflexivity.
    + destruct (ident_eqb x (se_name se)) eqn:Heq.
      * reflexivity.
      * apply IH. exact Hin.
Qed.

Lemma root_env_lookup_empty_root_env_for_store_none :
  forall s x,
    ~ In x (store_names s) ->
    root_env_lookup x (empty_root_env_for_store s) = None.
Proof.
  induction s as [| se rest IH]; intros x Hfresh; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    exfalso. apply Hfresh. left. reflexivity.
  - apply IH.
    intros Hin. apply Hfresh. right. exact Hin.
Qed.

Lemma root_env_names_empty_root_env_for_store :
  forall s,
    root_env_names (empty_root_env_for_store s) = store_names s.
Proof.
  induction s as [| se rest IH]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma root_env_no_shadow_empty_root_env_for_store :
  forall s,
    store_no_shadow s ->
    root_env_no_shadow (empty_root_env_for_store s).
Proof.
  unfold store_no_shadow, root_env_no_shadow.
  intros s Hshadow.
  rewrite root_env_names_empty_root_env_for_store.
  exact Hshadow.
Qed.

Lemma root_env_store_roots_named_empty_root_env_for_store :
  forall s,
    root_env_store_roots_named (empty_root_env_for_store s) s.
Proof.
  unfold root_env_store_roots_named.
  intros s x roots z Hlookup Hin.
  destruct s as [| se rest].
  - simpl in Hlookup. discriminate.
  - destruct roots as [| r roots].
    + contradiction.
    + assert (Hin_names : In x (store_names (se :: rest))).
      { rewrite <- root_env_names_empty_root_env_for_store.
        eapply root_env_lookup_some_in_names. exact Hlookup. }
      rewrite root_env_lookup_empty_root_env_for_store in Hlookup
        by exact Hin_names.
      inversion Hlookup.
Qed.

Lemma root_env_store_keys_named_empty_root_env_for_store :
  forall s,
    root_env_store_keys_named (empty_root_env_for_store s) s.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros s x Hin.
  rewrite root_env_names_empty_root_env_for_store in Hin.
  exact Hin.
Qed.

Lemma store_names_app :
  forall s1 s2,
    store_names (s1 ++ s2) = store_names s1 ++ store_names s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_no_shadow_app :
  forall s1 s2,
    store_no_shadow s1 ->
    store_no_shadow s2 ->
    (forall x, In x (store_names s1) -> ~ In x (store_names s2)) ->
    store_no_shadow (s1 ++ s2).
Proof.
  unfold store_no_shadow.
  intros s1.
  induction s1 as [| se rest IH]; intros s2 Hshadow1 Hshadow2 Hdisj;
    simpl in *.
  - exact Hshadow2.
  - inversion Hshadow1 as [| x xs Hnotin Hshadow_tail]; subst.
    constructor.
    + rewrite store_names_app.
      intros Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hnotin. exact Hin.
      * apply (Hdisj (se_name se)).
        -- simpl. left. reflexivity.
        -- exact Hin.
    + apply IH.
      * exact Hshadow_tail.
      * exact Hshadow2.
      * intros x Hin_rest.
        apply Hdisj. simpl. right. exact Hin_rest.
Qed.

Lemma store_roots_within_weaken_lookup :
  forall R R' s,
    store_roots_within R s ->
    (forall x roots,
      In x (store_names s) ->
      root_env_lookup x R = Some roots ->
      root_env_lookup x R' = Some roots) ->
    store_roots_within R' s.
Proof.
  intros R R' s Hroots.
  induction Hroots as [R | R se rest Hentry Hrest IH]; intros Hpreserve.
  - constructor.
  - inversion Hentry as [R0 sx sT sv sst roots Hlookup Hvalue]; subst.
    constructor.
    + econstructor.
      * apply Hpreserve.
        -- simpl. left. reflexivity.
        -- exact Hlookup.
      * exact Hvalue.
    + apply IH.
      intros x roots_x Hname Hlookup_x.
      apply Hpreserve.
      * simpl. right. exact Hname.
      * exact Hlookup_x.
Qed.

Lemma store_roots_within_empty_root_env_for_store :
  forall s,
    store_no_shadow s ->
    Forall (fun se => value_roots_within [] (se_val se)) s ->
    store_roots_within (empty_root_env_for_store s) s.
Proof.
  induction s as [| se rest IH]; intros Hshadow Hvalues; simpl in *.
  - constructor.
  - inversion Hvalues as [| se0 rest0 Hvalue Htail]; subst.
    inversion Hshadow as [| x xs Hnotin Hshadow_tail]; subst.
    destruct se as [sx sT sv sst].
    constructor.
    + econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * exact Hvalue.
    + eapply store_roots_within_weaken_lookup.
      * apply IH; assumption.
      * intros x roots Hin Hlookup.
        simpl.
        destruct (ident_eqb x sx) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst x.
           exfalso. apply Hnotin. exact Hin.
        -- exact Hlookup.
Qed.

Lemma copy_capture_store_as_captured_store_runtime_ready :
  forall Ω env s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    NoDup (ctx_names (params_ctx caps)) ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    captured_store_runtime_ready env captured
      (empty_root_env_for_store captured).
Proof.
  intros Ω env s Σ captures caps captured captured_tys
    Hstore Hnodup Hcopy Hcheck.
  destruct (copy_capture_store_as_captured_store_typed_rootless
              Ω env s Σ captures caps captured captured_tys
              Hstore Hcopy Hcheck)
    as [Htyped Hroots_values].
  assert (Hshadow : store_no_shadow captured).
  { unfold store_no_shadow.
    rewrite (copy_capture_store_as_store_names captures caps s captured Hcopy).
    exact Hnodup. }
  unfold captured_store_runtime_ready.
  repeat split.
  - exact Htyped.
  - apply store_roots_within_empty_root_env_for_store; assumption.
  - exact Hshadow.
  - apply root_env_no_shadow_empty_root_env_for_store. exact Hshadow.
  - apply root_env_store_roots_named_empty_root_env_for_store.
  - apply root_env_store_keys_named_empty_root_env_for_store.
Qed.

Lemma store_roots_with_empty_roots_exclude_root :
  forall R s root,
    store_roots_within R s ->
    (forall x roots,
      In x (store_names s) ->
      root_env_lookup x R = Some roots ->
      roots = []) ->
    store_refs_exclude_root root s.
Proof.
  intros R s root Hwithin Hempty.
  induction Hwithin as [R|R se rest Hentry Hrest IH].
  - constructor.
  - constructor.
    + inversion Hentry; subst.
      assert (Hroots_empty : roots = []).
      { eapply Hempty.
        - simpl. left. reflexivity.
        - exact H. }
      subst roots.
      constructor.
      eapply value_roots_exclude_root.
      * exact H0.
      * unfold roots_exclude. intros Hin. contradiction.
    + apply IH.
      intros x roots Hin Hlookup.
      eapply Hempty.
      * simpl. right. exact Hin.
      * exact Hlookup.
Qed.

Lemma store_roots_within_empty_root_env_refs_exclude_root :
  forall s root,
    store_roots_within (empty_root_env_for_store s) s ->
    store_refs_exclude_root root s.
Proof.
  intros s root Hwithin.
  eapply store_roots_with_empty_roots_exclude_root.
  - exact Hwithin.
  - intros x roots Hin Hlookup.
    rewrite (root_env_lookup_empty_root_env_for_store s x Hin) in Hlookup.
    inversion Hlookup. reflexivity.
Qed.

Lemma captured_store_runtime_ready_empty_refs_exclude_root :
  forall env captured root,
    captured_store_runtime_ready env captured
      (empty_root_env_for_store captured) ->
    store_refs_exclude_root root captured.
Proof.
  intros env captured root Hready.
  unfold captured_store_runtime_ready in Hready.
  destruct Hready as [_ [Hroots _]].
  eapply store_roots_within_empty_root_env_refs_exclude_root.
  exact Hroots.
Qed.

Lemma copied_captured_closure_roots_empty :
  forall Ω env s Σ fname captures fdef captured captured_tys,
    store_typed env s Σ ->
    lookup_fn fname (env_fns env) = Some fdef ->
    NoDup (ctx_names (params_ctx (fn_captures fdef))) ->
    copy_capture_store_as captures (fn_captures fdef) s = Some captured ->
    check_make_closure_captures_exact_sctx env Ω Σ captures
      (fn_captures fdef) = infer_ok captured_tys ->
    value_roots_within [] (VClosure fname captured).
Proof.
  intros Ω env s Σ fname captures fdef captured captured_tys Hstore
    Hlookup Hnodup Hcopy Hcheck.
  constructor.
  intros root _.
  pose proof
    (copy_capture_store_as_captured_store_runtime_ready
      Ω env s Σ captures (fn_captures fdef) captured captured_tys
      Hstore Hnodup Hcopy Hcheck) as Hready.
  eapply captured_store_runtime_ready_empty_refs_exclude_root.
  exact Hready.
Qed.

Lemma root_env_store_roots_named_app :
  forall R1 R2 s1 s2,
    root_env_store_roots_named R1 s1 ->
    root_env_store_roots_named R2 s2 ->
    (forall x roots,
      root_env_lookup x R2 = Some roots ->
      root_env_lookup x R1 = None) ->
    root_env_store_roots_named (R1 ++ R2) (s1 ++ s2).
Proof.
  unfold root_env_store_roots_named.
  intros R1 R2 s1 s2 Hnamed1 Hnamed2 _ x roots z Hlookup Hin.
  destruct (root_env_lookup x R1) as [roots1 |] eqn:Hlookup1.
  - rewrite (root_env_lookup_app_left x R1 R2 roots1 Hlookup1)
      in Hlookup.
    inversion Hlookup; subst roots1.
    rewrite store_names_app. apply in_or_app. left.
    eapply Hnamed1; eassumption.
  - rewrite (root_env_lookup_app_right x R1 R2 Hlookup1) in Hlookup.
    rewrite store_names_app. apply in_or_app. right.
    eapply Hnamed2; eassumption.
Qed.

Lemma root_env_store_keys_named_app :
  forall R1 R2 s1 s2,
    root_env_store_keys_named R1 s1 ->
    root_env_store_keys_named R2 s2 ->
    root_env_store_keys_named (R1 ++ R2) (s1 ++ s2).
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  intros R1 R2 s1 s2 Hkeys1 Hkeys2 x Hin.
  rewrite root_env_names_app in Hin.
  rewrite store_names_app.
  apply in_app_or in Hin.
  apply in_or_app.
  destruct Hin as [Hin | Hin].
  - left. apply Hkeys1. exact Hin.
  - right. apply Hkeys2. exact Hin.
Qed.

Lemma store_roots_within_app :
  forall R1 R2 s1 s2,
    store_roots_within R1 s1 ->
    store_roots_within R2 s2 ->
    (forall x roots,
      root_env_lookup x R2 = Some roots ->
      root_env_lookup x R1 = None) ->
    store_roots_within (R1 ++ R2) (s1 ++ s2).
Proof.
  intros R1 R2 s1 s2 Hroots1.
  revert R2 s2.
  induction Hroots1 as [R1 | R1 se rest Hentry Hrest IH];
    intros R2 s2 Hroots2 Hdisj.
  - simpl.
    eapply store_roots_within_weaken_lookup.
    + exact Hroots2.
    + intros x roots _ Hlookup.
      specialize (Hdisj x roots Hlookup).
      rewrite (root_env_lookup_app_right x R1 R2 Hdisj).
      exact Hlookup.
  - simpl. constructor.
    + inversion Hentry as [R0 sx sT sv sst roots Hlookup Hvalue]; subst.
      econstructor.
      * eapply root_env_lookup_app_left. exact Hlookup.
      * exact Hvalue.
    + apply IH.
      * exact Hroots2.
      * intros x roots Hlookup2.
        specialize (Hdisj x roots Hlookup2).
        exact Hdisj.
  Unshelve.
  all: eauto.
Qed.

Lemma captured_call_frame_ready_compose :
  forall env captured Rcap s_args R_args,
    captured_store_runtime_ready env captured Rcap ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    (forall x, In x (store_names captured) -> ~ In x (store_names s_args)) ->
    (forall x, root_env_lookup x Rcap = None \/
      root_env_lookup x R_args = None) ->
    captured_call_frame_ready env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hcap_ready Hroots_args
    Hshadow_args Hrn_args Hnamed_args Hkeys_args Hstore_disj Hroot_disj.
  unfold captured_store_runtime_ready in Hcap_ready.
  destruct Hcap_ready as
    [Hcap_typed
      [Hroots_cap
        [Hshadow_cap
          [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  unfold captured_call_frame_ready, captured_store_runtime_ready.
  repeat split.
  - exact Hcap_typed.
  - exact Hroots_cap.
  - exact Hshadow_cap.
  - exact Hrn_cap.
  - exact Hnamed_cap.
  - exact Hkeys_cap.
  - exact Hroots_args.
  - apply store_no_shadow_app; assumption.
  - apply root_env_no_shadow_app; assumption.
  - apply root_env_store_roots_named_app; try assumption.
    intros x roots Hlookup_args.
    specialize (Hroot_disj x).
    destruct Hroot_disj as [Hnone_cap | Hnone_args].
    + exact Hnone_cap.
    + rewrite Hlookup_args in Hnone_args. discriminate.
  - apply root_env_store_keys_named_app; assumption.
Qed.

Lemma store_lookup_some_in_store_names :
  forall x s se,
    store_lookup x s = Some se ->
    In x (store_names s).
Proof.
  intros x s.
  induction s as [| se_head rest IH]; intros se Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (ident_eqb x (se_name se_head)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hlookup.
Qed.

Lemma store_ref_targets_preserved_app_left :
  forall env s1 s2,
    store_ref_targets_preserved env s1 (s1 ++ s2).
Proof.
  unfold store_ref_targets_preserved.
  intros env s1 s2 x path se v T Hlookup Hvalue Htype.
  exists se, v. repeat split; try assumption.
  apply store_lookup_app_some. exact Hlookup.
Qed.

Lemma store_ref_targets_preserved_app_right :
  forall env s1 s2,
    (forall x, In x (store_names s2) -> store_lookup x s1 = None) ->
    store_ref_targets_preserved env s2 (s1 ++ s2).
Proof.
  unfold store_ref_targets_preserved.
  intros env s1 s2 Hdisj x path se v T Hlookup Hvalue Htype.
  exists se, v. repeat split; try assumption.
  rewrite (store_lookup_app_none x s1 s2).
  - exact Hlookup.
  - apply Hdisj. eapply store_lookup_some_in_store_names. exact Hlookup.
Qed.

Lemma store_typed_entries_store_preserved :
  forall env s s' entries Σ,
    Forall2 (store_entry_typed env s) entries Σ ->
    store_ref_targets_preserved env s s' ->
    Forall2 (store_entry_typed env s') entries Σ.
Proof.
  intros env s s' entries Σ Htyped Hpres.
  induction Htyped as [| se ce entries_tail Σ_tail Hentry _ IH].
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hstate Hvalue]]].
    constructor.
    + simpl. repeat split; try assumption.
      eapply value_has_type_store_preserved; eassumption.
    + exact IH.
Qed.

Lemma store_typed_entries_app :
  forall env s entries1 Σ1 entries2 Σ2,
    Forall2 (store_entry_typed env s) entries1 Σ1 ->
    Forall2 (store_entry_typed env s) entries2 Σ2 ->
    Forall2 (store_entry_typed env s)
      (entries1 ++ entries2) (Σ1 ++ Σ2).
Proof.
  intros env s entries1 Σ1 entries2 Σ2 Htyped1 Htyped2.
  induction Htyped1 as [| se ce entries_tail Σ_tail Hentry _ IH].
  - exact Htyped2.
  - simpl. constructor; assumption.
Qed.

Lemma sctx_of_store_app :
  forall s1 s2,
    sctx_of_store (s1 ++ s2) = sctx_of_store s1 ++ sctx_of_store s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_typed_app :
  forall env s1 Σ1 s2 Σ2,
    store_typed env s1 Σ1 ->
    store_typed env s2 Σ2 ->
    store_ref_targets_preserved env s1 (s1 ++ s2) ->
    store_ref_targets_preserved env s2 (s1 ++ s2) ->
    store_typed env (s1 ++ s2) (Σ1 ++ Σ2).
Proof.
  unfold store_typed.
  intros env s1 Σ1 s2 Σ2 Htyped1 Htyped2 Hpres1 Hpres2.
  apply store_typed_entries_app.
  - eapply store_typed_entries_store_preserved; eassumption.
  - eapply store_typed_entries_store_preserved; eassumption.
Qed.

Lemma store_no_shadow_app_lookup_right_none :
  forall s1 s2 x,
    store_no_shadow (s1 ++ s2) ->
    In x (store_names s2) ->
    store_lookup x s1 = None.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2 x Hshadow Hin2;
    simpl in *.
  - reflexivity.
  - inversion Hshadow as [| ? ? Hnotin Hshadow_tail]; subst.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      exfalso. apply Hnotin.
      rewrite store_names_app. apply in_or_app. right. exact Hin2.
    + eapply IH; eassumption.
Qed.

Lemma captured_call_frame_store_typed :
  forall env captured Rcap s_args R_args Σ_args,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    store_typed env s_args Σ_args ->
    store_typed env (captured ++ s_args)
      (sctx_of_store captured ++ Σ_args).
Proof.
  intros env captured Rcap s_args R_args Σ_args Hready Htyped_args.
  unfold captured_call_frame_ready, captured_store_runtime_ready in Hready.
  destruct Hready as
    [[Htyped_cap _] [_ [Hshadow_frame _]]].
  eapply store_typed_app.
  - exact Htyped_cap.
  - exact Htyped_args.
  - apply store_ref_targets_preserved_app_left.
  - apply store_ref_targets_preserved_app_right.
    intros x Hin.
    eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma captured_call_frame_params_store_typed :
  forall env captured Rcap s_args R_args caps Σ_args,
    captured_call_frame_params_ready env captured Rcap s_args R_args caps ->
    store_typed env s_args Σ_args ->
    store_typed env (captured ++ s_args)
      (sctx_of_ctx (params_ctx caps) ++ Σ_args).
Proof.
  intros env captured Rcap s_args R_args caps Σ_args Hready Htyped_args.
  destruct Hready as [Hframe_ready Htyped_cap].
  unfold captured_call_frame_ready in Hframe_ready.
  destruct Hframe_ready as [_ [_ [Hshadow_frame _]]].
  eapply store_typed_app.
  - exact Htyped_cap.
  - exact Htyped_args.
  - apply store_ref_targets_preserved_app_left.
  - apply store_ref_targets_preserved_app_right.
    intros x Hin.
    eapply store_no_shadow_app_lookup_right_none; eassumption.
Qed.

Lemma store_update_state_not_in_names :
  forall x f s,
    ~ In x (store_names s) ->
    store_update_state x f s = None.
Proof.
  intros x f s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_update_val_not_in_names :
  forall x v s,
    ~ In x (store_names s) ->
    store_update_val x v s = None.
Proof.
  intros x v s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_update_path_not_in_names :
  forall x path v s,
    ~ In x (store_names s) ->
    store_update_path x path v s = None.
Proof.
  intros x path v s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_mark_used_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_mark_used x s = s.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_remove x s = s.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - rewrite IH; try reflexivity.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_lookup_store_add_same :
  forall x T v s,
    store_lookup x (store_add x T v s) =
    Some (MkStoreEntry x T v (binding_state_of_bool false)).
Proof.
  intros x T v s.
  unfold store_add. simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma store_lookup_store_add_diff :
  forall x y T v s,
    x <> y ->
    store_lookup x (store_add y T v s) = store_lookup x s.
Proof.
  intros x y T v s Hneq.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma store_mark_used_store_add_diff :
  forall x y T v s,
    x <> y ->
    store_mark_used x (store_add y T v s) =
    store_add y T v (store_mark_used x s).
Proof.
  intros x y T v s Hneq.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma store_update_state_store_add_diff :
  forall x y f T v s s',
    x <> y ->
    store_update_state x f s = Some s' ->
    store_update_state x f (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y f T v s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_update_val_store_add_diff :
  forall x y T v v_new s s',
    x <> y ->
    store_update_val x v_new s = Some s' ->
    store_update_val x v_new (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y T v v_new s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_update_path_store_add_diff :
  forall x y path T v v_new s s',
    x <> y ->
    store_update_path x path v_new s = Some s' ->
    store_update_path x path v_new (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y path T v v_new s s' Hneq Hupdate.
  unfold store_add. simpl.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite Hupdate. reflexivity.
Qed.

Lemma store_restore_path_store_add_diff :
  forall x y path T v s s',
    x <> y ->
    store_restore_path x path s = Some s' ->
    store_restore_path x path (store_add y T v s) =
    Some (store_add y T v s').
Proof.
  intros x y path T v s s' Hneq Hrestore.
  unfold store_restore_path in *.
  eapply store_update_state_store_add_diff; eassumption.
Qed.

Lemma store_update_state_store_add_inv :
  forall x y f T v s s_hidden',
    x <> y ->
    store_update_state x f (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_state x f s = Some s'.
Proof.
  intros x y f T v s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_state x f s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_update_val_store_add_inv :
  forall x y T v v_new s s_hidden',
    x <> y ->
    store_update_val x v_new (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_val x v_new s = Some s'.
Proof.
  intros x y T v v_new s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_val x v_new s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_update_path_store_add_inv :
  forall x y path T v v_new s s_hidden',
    x <> y ->
    store_update_path x path v_new (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_update_path x path v_new s = Some s'.
Proof.
  intros x y path T v v_new s s_hidden' Hneq Hupdate.
  unfold store_add in Hupdate. simpl in Hupdate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - destruct (store_update_path x path v_new s) as [s' |] eqn:Hbase;
      try discriminate.
    inversion Hupdate; subst.
    exists s'. split; reflexivity.
Qed.

Lemma store_restore_path_store_add_inv :
  forall x y path T v s s_hidden',
    x <> y ->
    store_restore_path x path (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_restore_path x path s = Some s'.
Proof.
  intros x y path T v s s_hidden' Hneq Hrestore.
  unfold store_restore_path in *.
  eapply store_update_state_store_add_inv; eassumption.
Qed.

Lemma store_consume_path_store_add_inv :
  forall x y path T v s s_hidden',
    x <> y ->
    store_consume_path x path (store_add y T v s) = Some s_hidden' ->
    exists s',
      s_hidden' = store_add y T v s' /\
      store_consume_path x path s = Some s'.
Proof.
  intros x y path T v s s_hidden' Hneq Hconsume.
  unfold store_consume_path in *.
  rewrite store_lookup_store_add_diff in Hconsume by exact Hneq.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_store_add_inv; eassumption.
Qed.

Lemma value_fields_refs_exclude_lookup :
  forall root fields fname v,
    value_fields_refs_exclude_root root fields ->
    (let fix lookup (fields0 : list (string * value)) : option value :=
       match fields0 with
       | [] => None
       | (name, fv) :: tail =>
           if String.eqb fname name then Some fv else lookup tail
       end in lookup fields) = Some v ->
    value_refs_exclude_root root v.
Proof.
  intros root fields.
  induction fields as [| [name fv] tail IH]; intros fname v Hfields Hlookup;
    simpl in Hlookup; try discriminate.
  inversion Hfields; subst.
  destruct (String.eqb fname name) eqn:Hname.
  - inversion Hlookup; subst. assumption.
  - eapply IH; eassumption.
Qed.

Lemma value_refs_exclude_lookup_ref_neq :
  forall root v path x rpath,
    value_refs_exclude_root root v ->
    value_lookup_path v path = Some (VRef x rpath) ->
    x <> root.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v x rpath Hexcl Hlookup.
  - simpl in Hlookup. inversion Hlookup; subst v.
    inversion Hexcl; subst.
    match goal with
    | Hneqb : ident_eqb root x = false |- _ =>
        apply ident_eqb_neq in Hneqb;
        intros Heq; apply Hneqb; symmetry; exact Heq
    end.
  - simpl in Hlookup.
    destruct v; try discriminate.
    inversion Hexcl; subst.
    destruct
      ((fix lookup (fields0 : list (string * value)) : option value :=
          match fields0 with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name then Some fv else lookup tail
          end) l) as [fv |] eqn:Hfield; try discriminate.
    eapply IH.
    + eapply value_fields_refs_exclude_lookup; eassumption.
    + exact Hlookup.
Qed.

Lemma value_refs_exclude_lookup_path :
  forall root v path v_path,
    value_refs_exclude_root root v ->
    value_lookup_path v path = Some v_path ->
    value_refs_exclude_root root v_path.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v v_path Hexcl Hlookup.
  - simpl in Hlookup. inversion Hlookup; subst. exact Hexcl.
  - simpl in Hlookup.
    destruct v; try discriminate.
    inversion Hexcl; subst.
    destruct
      ((fix lookup (fields0 : list (string * value)) : option value :=
          match fields0 with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name then Some fv else lookup tail
          end) l) as [fv |] eqn:Hfield; try discriminate.
    eapply IH.
    + eapply value_fields_refs_exclude_lookup; eassumption.
    + exact Hlookup.
Qed.

Lemma store_refs_exclude_lookup :
  forall root s y se,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    store_entry_refs_exclude_root root se.
Proof.
  intros root s.
  induction s as [| se_head rest IH]; intros y se Hexcl Hlookup;
    simpl in Hlookup; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb y (se_name se_head)) eqn:Hy.
  - inversion Hlookup; subst. assumption.
  - eapply IH; eassumption.
Qed.

Lemma store_refs_exclude_lookup_value :
  forall root s y se,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    value_refs_exclude_root root (se_val se).
Proof.
  intros root s y se Hrefs Hlookup.
  pose proof (store_refs_exclude_lookup root s y se Hrefs Hlookup) as Hentry.
  destruct se as [sx sT sv sst].
  inversion Hentry; subst. assumption.
Qed.

Lemma store_refs_exclude_lookup_ref_neq :
  forall root s y se path x rpath,
    store_refs_exclude_root root s ->
    store_lookup y s = Some se ->
    value_lookup_path (se_val se) path = Some (VRef x rpath) ->
    x <> root.
Proof.
  intros root s.
  induction s as [| [sx sT sv sst] rest IH]; intros y se path x rpath Hexcl
    Hlookup Hvalue; simpl in Hlookup; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb y sx) eqn:Hy.
  - inversion Hlookup; subst se.
    match goal with
    | Hentry : store_entry_refs_exclude_root root (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    match goal with
    | Hvalue_excl : value_refs_exclude_root root sv |- _ =>
        eapply value_refs_exclude_lookup_ref_neq; eassumption
    end.
  - eapply IH; eassumption.
Qed.

Lemma store_mark_used_refs_exclude_root :
  forall root x s,
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_mark_used x s).
Proof.
  intros root x s Hexcl.
  induction Hexcl as [| [sx sT sv sst] rest Hentry Hrest IH];
    simpl; try constructor.
  inversion Hentry; subst.
  destruct (ident_eqb x sx).
  - constructor.
    + constructor. assumption.
    + exact Hrest.
  - constructor.
    + constructor. assumption.
    + exact IH.
Qed.

Lemma store_update_state_refs_exclude_root :
  forall root x f s s',
    store_refs_exclude_root root s ->
    store_update_state x f s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x f s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - inversion Hupdate; subst.
    match goal with
    | Hentry : store_entry_refs_exclude_root root
        (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    constructor.
    + constructor. assumption.
    + assumption.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma store_restore_path_refs_exclude_root :
  forall root x path s s',
    store_refs_exclude_root root s ->
    store_restore_path x path s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path s s' Hexcl Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_update_state_refs_exclude_root; eassumption.
Qed.

Lemma store_consume_path_refs_exclude_root :
  forall root x path s s',
    store_refs_exclude_root root s ->
    store_consume_path x path s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path s s' Hexcl Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_refs_exclude_root; eassumption.
Qed.

Lemma store_update_val_refs_exclude_root :
  forall root x v_new s s',
    value_refs_exclude_root root v_new ->
    store_refs_exclude_root root s ->
    store_update_val x v_new s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x v_new s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hv Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - inversion Hupdate; subst.
    constructor.
    + constructor. exact Hv.
    + assumption.
  - destruct (store_update_val x v_new rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma value_update_path_refs_exclude_root :
  forall root v path v_new v',
    value_refs_exclude_root root v ->
    value_refs_exclude_root root v_new ->
    value_update_path v path v_new = Some v' ->
    value_refs_exclude_root root v'.
Proof.
  intros root v path.
  revert v.
  induction path as [| fname rest IH]; intros v v_new v' Hv Hvnew Hupdate.
  - destruct v; simpl in Hupdate; inversion Hupdate; subst; exact Hvnew.
  - destruct v; simpl in Hupdate; try discriminate.
    inversion Hv; subst.
    destruct
      ((fix update (fields : list (string * value)) :
          option (list (string * value)) :=
          match fields with
          | [] => None
          | (name, fv) :: tail =>
              if String.eqb fname name
              then match value_update_path fv rest v_new with
                   | Some fv' => Some ((name, fv') :: tail)
                   | None => None
                   end
              else match update tail with
                   | Some tail' => Some ((name, fv) :: tail')
                   | None => None
                   end
          end) l) as [fields' |] eqn:Hfields; try discriminate.
    assert (Hfields_excl :
      forall fields fields',
        value_fields_refs_exclude_root root fields ->
        (fix update (fields0 : list (string * value)) :
            option (list (string * value)) :=
            match fields0 with
            | [] => None
            | (name, fv) :: tail =>
                if String.eqb fname name
                then match value_update_path fv rest v_new with
                     | Some fv' => Some ((name, fv') :: tail)
                     | None => None
                     end
                else match update tail with
                     | Some tail' => Some ((name, fv) :: tail')
                     | None => None
                     end
            end) fields = Some fields' ->
        value_fields_refs_exclude_root root fields').
    { clear Hfields.
      induction fields as [| [name fv] tail IHfields];
        intros fields_out Hfields_excl Hupd; simpl in Hupd; try discriminate.
      inversion Hfields_excl; subst.
      destruct (String.eqb fname name) eqn:Hname.
      - destruct (value_update_path fv rest v_new) as [fv' |] eqn:Hfv;
          try discriminate.
        inversion Hupd; subst.
        constructor.
        + eapply IH.
          * eassumption.
          * exact Hvnew.
          * exact Hfv.
        + assumption.
      - destruct
          ((fix update (fields0 : list (string * value)) :
              option (list (string * value)) :=
              match fields0 with
              | [] => None
              | (name0, fv0) :: tail0 =>
                  if String.eqb fname name0
                  then match value_update_path fv0 rest v_new with
                       | Some fv' => Some ((name0, fv') :: tail0)
                       | None => None
                       end
                  else match update tail0 with
                       | Some tail' => Some ((name0, fv0) :: tail')
                       | None => None
                       end
              end) tail) as [tail' |] eqn:Htail; try discriminate.
        inversion Hupd; subst.
        constructor.
        + assumption.
        + eapply IHfields.
          * eassumption.
          * reflexivity. }
    inversion Hupdate; subst.
    constructor.
    eapply Hfields_excl; eassumption.
Qed.

Lemma store_update_path_refs_exclude_root :
  forall root x path v_new s s',
    value_refs_exclude_root root v_new ->
    store_refs_exclude_root root s ->
    store_update_path x path v_new s = Some s' ->
    store_refs_exclude_root root s'.
Proof.
  intros root x path v_new s.
  induction s as [| [sx sT sv sst] rest IH]; intros s' Hv Hexcl Hupdate;
    simpl in Hupdate; try discriminate.
  inversion Hexcl; subst.
  destruct (ident_eqb x sx) eqn:Hx.
  - destruct (value_update_path sv path v_new) as [sv' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate; subst.
    match goal with
    | Hentry : store_entry_refs_exclude_root root
        (MkStoreEntry sx sT sv sst) |- _ =>
        inversion Hentry; subst
    end.
    constructor.
    + constructor.
      eapply value_update_path_refs_exclude_root.
      * eassumption.
      * exact Hv.
      * exact Hvalue.
    + assumption.
  - destruct (store_update_path x path v_new rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma eval_place_store_add_strip :
  forall s p y path x T hidden,
    place_name p <> x ->
    store_refs_exclude_root x s ->
    eval_place (store_add x T hidden s) p y path ->
    y <> x /\ eval_place s p y path.
Proof.
  intros s p.
  induction p as [z | p IH | p IH]; intros y path x T hidden
    Hplace_fresh Hrefs Heval.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    split; try assumption.
    eapply EvalPlace_Var.
    match goal with
    | Hlookup : store_lookup _ (store_add x T hidden s) = Some _ |- _ =>
        rewrite store_lookup_store_add_diff in Hlookup by exact Hplace_fresh;
        exact Hlookup
    end.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    match goal with
    | Hplace : eval_place (store_add x T hidden s) p ?r ?rpath |- _ =>
        destruct (IH r rpath x T hidden Hplace_fresh Hrefs Hplace)
          as [Hrneq Heval_base]
    end.
    match goal with
    | Hlookup : store_lookup ?r (store_add x T hidden s) = Some _ |- _ =>
        rewrite store_lookup_store_add_diff in Hlookup by exact Hrneq
    end.
    split.
    + eapply store_refs_exclude_lookup_ref_neq; eassumption.
    + eapply EvalPlace_Deref; eassumption.
  - inversion Heval; subst.
    simpl in Hplace_fresh.
    match goal with
    | Hplace : eval_place (store_add x T hidden s) p ?x0 ?path0 |- _ =>
        destruct (IH x0 path0 x T hidden Hplace_fresh Hrefs Hplace)
          as [Hneq Heval_base]
    end.
    split; try assumption.
    apply EvalPlace_Field. exact Heval_base.
Qed.

Lemma fields_local_store_names_in_expr :
  forall fname e fields x,
    In (fname, e) fields ->
    In x (expr_local_store_names e) ->
    In x (fields_local_store_names fields).
Proof.
  intros fname e fields x Hin Hx.
  induction fields as [| [fname' e'] rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + inversion Hin; subst. apply in_or_app. left. exact Hx.
    + apply in_or_app. right. apply IH. exact Hin.
Qed.

Scheme hidden_frame_eval_ind' := Induction for eval Sort Prop
with hidden_frame_eval_args_ind' := Induction for eval_args Sort Prop
with hidden_frame_eval_struct_fields_ind' :=
  Induction for eval_struct_fields Sort Prop.

Combined Scheme hidden_frame_eval_eval_args_eval_struct_fields_ind
  from hidden_frame_eval_ind',
       hidden_frame_eval_args_ind',
       hidden_frame_eval_struct_fields_ind'.

Fixpoint args_free_vars_ts (args : list expr) : list ident :=
  match args with
  | [] => []
  | e :: rest => free_vars_expr e ++ args_free_vars_ts rest
  end.

Fixpoint fields_free_vars_ts (fields : list (string * expr)) : list ident :=
  match fields with
  | [] => []
  | (_, e) :: rest => free_vars_expr e ++ fields_free_vars_ts rest
  end.

Lemma args_free_vars_ts_cons_notin :
  forall x e rest,
    ~ In x (args_free_vars_ts (e :: rest)) ->
    ~ In x (free_vars_expr e) /\ ~ In x (args_free_vars_ts rest).
Proof.
  intros x e rest Hnotin. simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma fields_free_vars_ts_cons_notin :
  forall x name e rest,
    ~ In x (fields_free_vars_ts ((name, e) :: rest)) ->
    ~ In x (free_vars_expr e) /\ ~ In x (fields_free_vars_ts rest).
Proof.
  intros x name e rest Hnotin. simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma args_local_store_names_cons_notin :
  forall x e rest,
    ~ In x (args_local_store_names (e :: rest)) ->
    ~ In x (expr_local_store_names e) /\
    ~ In x (args_local_store_names rest).
Proof.
  intros x e rest Hnotin.
  unfold args_local_store_names in *.
  simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma fields_local_store_names_cons_notin :
  forall x name e rest,
    ~ In x (fields_local_store_names ((name, e) :: rest)) ->
    ~ In x (expr_local_store_names e) /\
    ~ In x (fields_local_store_names rest).
Proof.
  intros x name e rest Hnotin.
  unfold fields_local_store_names in *.
  simpl in Hnotin.
  split; intros Hin; apply Hnotin; apply in_or_app;
    [left | right]; exact Hin.
Qed.

Lemma lookup_expr_field_in :
  forall lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    exists field_name, In (field_name, e) fields.
Proof.
  intros lookup_name fields.
  induction fields as [| [name expr] rest IH]; intros e Hlookup;
    simpl in Hlookup; try discriminate.
  destruct (String.eqb lookup_name name) eqn:Hname.
  - inversion Hlookup; subst. exists name. left. reflexivity.
  - destruct (IH e Hlookup) as [field_name Hin].
    exists field_name. right. exact Hin.
Qed.

Lemma fields_free_vars_ts_in_expr :
  forall field_name e fields x,
    In (field_name, e) fields ->
    In x (free_vars_expr e) ->
    In x (fields_free_vars_ts fields).
Proof.
  intros field_name e fields x Hin Hx.
  induction fields as [| [name expr] rest IH]; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - inversion Hin; subst. apply in_or_app. left. exact Hx.
  - apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma fields_free_vars_ts_lookup_notin :
  forall x lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    ~ In x (fields_free_vars_ts fields) ->
    ~ In x (free_vars_expr e).
Proof.
  intros x lookup_name fields e Hlookup Hnotin Hin.
  destruct (lookup_expr_field_in lookup_name fields e Hlookup)
    as [field_name Hfield].
  apply Hnotin.
  eapply fields_free_vars_ts_in_expr; eassumption.
Qed.

Lemma fields_local_store_names_lookup_notin :
  forall x lookup_name fields e,
    lookup_expr_field lookup_name fields = Some e ->
    ~ In x (fields_local_store_names fields) ->
    ~ In x (expr_local_store_names e).
Proof.
  intros x lookup_name fields e Hlookup Hnotin Hin.
  destruct (lookup_expr_field_in lookup_name fields e Hlookup)
    as [field_name Hfield].
  apply Hnotin.
  eapply fields_local_store_names_in_expr; eassumption.
Qed.

Theorem hidden_frame_eval_strip_mutual :
  (forall env s e s_hidden' v,
    eval env s e s_hidden' v ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_expr e ->
      ~ In x (free_vars_expr e) ->
      ~ In x (expr_local_store_names e) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval env s_base e s' v /\
        store_refs_exclude_root x s' /\
        value_refs_exclude_root x v) /\
  (forall env s args s_hidden' vs,
    eval_args env s args s_hidden' vs ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_args args ->
      ~ In x (args_free_vars_ts args) ->
      ~ In x (args_local_store_names args) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval_args env s_base args s' vs /\
        store_refs_exclude_root x s' /\
        Forall (value_refs_exclude_root x) vs) /\
  (forall env s fields defs s_hidden' values,
    eval_struct_fields env s fields defs s_hidden' values ->
    forall x T hidden s_base,
      s = store_add x T hidden s_base ->
      preservation_ready_fields fields ->
      ~ In x (fields_free_vars_ts fields) ->
      ~ In x (fields_local_store_names fields) ->
      store_refs_exclude_root x s_base ->
      exists s',
        s_hidden' = store_add x T hidden s' /\
        eval_struct_fields env s_base fields defs s' values /\
        store_refs_exclude_root x s' /\
        value_fields_refs_exclude_root x values).
Proof.
  assert (Hmut : forall env,
    (forall s e s_hidden' v,
      eval env s e s_hidden' v ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval env s_base e s' v /\
          store_refs_exclude_root x s' /\
          value_refs_exclude_root x v) /\
    (forall s args s_hidden' vs,
      eval_args env s args s_hidden' vs ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval_args env s_base args s' vs /\
          store_refs_exclude_root x s' /\
          Forall (value_refs_exclude_root x) vs) /\
    (forall s fields defs s_hidden' values,
      eval_struct_fields env s fields defs s_hidden' values ->
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s',
          s_hidden' = store_add x T hidden s' /\
          eval_struct_fields env s_base fields defs s' values /\
          store_refs_exclude_root x s' /\
          value_fields_refs_exclude_root x values)).
  { intro env.
  apply (hidden_frame_eval_eval_args_eval_struct_fields_ind env
    (fun s e s' v _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_expr e ->
        ~ In x (free_vars_expr e) ->
        ~ In x (expr_local_store_names e) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval env s_base e s_base' v /\
          store_refs_exclude_root x s_base' /\
          value_refs_exclude_root x v)
    (fun s args s' vs _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_args args ->
        ~ In x (args_free_vars_ts args) ->
        ~ In x (args_local_store_names args) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval_args env s_base args s_base' vs /\
          store_refs_exclude_root x s_base' /\
          Forall (value_refs_exclude_root x) vs)
    (fun s fields defs s' values _ =>
      forall x T hidden s_base,
        s = store_add x T hidden s_base ->
        preservation_ready_fields fields ->
        ~ In x (fields_free_vars_ts fields) ->
        ~ In x (fields_local_store_names fields) ->
        store_refs_exclude_root x s_base ->
        exists s_base',
          s' = store_add x T hidden s_base' /\
          eval_struct_fields env s_base fields defs s_base' values /\
          store_refs_exclude_root x s_base' /\
          value_fields_refs_exclude_root x values)).
  - intros s x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. destruct lit; repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s lit x T hidden s_base Hs Hready _ _ Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s y se Hlookup Hconsume x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    subst s.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Var_Copy; eassumption.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s y se Hlookup Hconsume Hused x T hidden s_base Hs Hready
      Hfree _ Hrefs.
    subst s.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists (store_mark_used y s_base). repeat split.
    + rewrite store_mark_used_store_add_diff by exact Hyx. reflexivity.
    + eapply Eval_Var_Consume; eassumption.
    + apply store_mark_used_refs_exclude_root. exact Hrefs.
    + exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
  - intros s p y path se Ty v Heval_place Hlookup Havail Hty Hneeds
      Hvalue x T hidden s_base Hs Hready Hfree _ Hrefs.
    subst s. inversion Hready; subst; clear Hready.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    exists s_base. repeat split; try assumption.
    + eapply Eval_Place_Copy; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' p y path se Ty v Heval_place Hlookup Havail Hty
      Hneeds Hvalue Hconsume x T hidden s_base Hs Hready Hfree _ Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (store_consume_path_store_add_inv y x path T hidden s_base s'
                Hyx Hconsume) as [s_base' [Hs' Hconsume_base]].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Place_Consume; eassumption.
    + eapply store_consume_path_refs_exclude_root; eassumption.
    + eapply value_refs_exclude_lookup_path.
      * exact (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup).
      * exact Hvalue.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IH x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_fields fields |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' Hvalues]]]].
    exists s_base'. split; try assumption.
    split.
    + subst s'. eapply Eval_Struct; eassumption.
    + split; try assumption.
      constructor. exact Hvalues.
  - intros s s1 s2 m y Ty e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s' e v Heval IH x T hidden s_base Hs Hready Hfree
      Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree Hlocal Hrefs)
      as [s_base' [Hs' [Heval_base [Hrefs' _]]]].
    exists s_base'. repeat split; try assumption.
    + eapply Eval_Drop. exact Heval_base.
    + constructor.
  - intros s s1 s2 s3 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate Hrestore x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_val_store_add_inv y x T hidden v_new s1_base s2
                Hyx Hupdate) as [s2_base [Hs2 Hupdate_base]].
    subst s2.
    destruct (store_restore_path_store_add_inv y x [] T hidden s2_base s3
                Hyx Hrestore) as [s3_base [Hs3 Hrestore_base]].
    exists s3_base. repeat split; try assumption.
    + eapply Eval_Replace; eassumption.
    + eapply store_restore_path_refs_exclude_root.
      * eapply store_update_val_refs_exclude_root; eassumption.
      * exact Hrestore_base.
    + exact (store_refs_exclude_lookup_value x s_base y old_e Hrefs Hlookup).
  - intros s s1 s2 y old_e e_new v_new Hlookup Heval_new IH
      Hupdate x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hyx : y <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    rewrite store_lookup_store_add_diff in Hlookup by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_val_store_add_inv y x T hidden v_new s1_base s2
                Hyx Hupdate) as [s2_base [Hs2 Hupdate_base]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign; eassumption.
    + eapply store_update_val_refs_exclude_root; eassumption.
    + constructor.
  - intros s s1 s2 s3 p y path old_v e_new v_new Heval_place
      Hlookup_path Heval_new IH Hupdate Hrestore x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    unfold store_lookup_path in Hlookup_path.
    rewrite store_lookup_store_add_diff in Hlookup_path by exact Hyx.
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_path_store_add_inv y x path T hidden v_new
                s1_base s2 Hyx Hupdate)
      as [s2_base [Hs2 Hupdate_base]].
    subst s2.
    destruct (store_restore_path_store_add_inv y x path T hidden s2_base s3
                Hyx Hrestore) as [s3_base [Hs3 Hrestore_base]].
    exists s3_base. repeat split; try assumption.
    + eapply Eval_Replace_Place; eassumption.
    + eapply store_restore_path_refs_exclude_root.
      * eapply store_update_path_refs_exclude_root; eassumption.
      * exact Hrestore_base.
    + destruct (store_lookup y s_base) as [se |] eqn:Hlookup_base;
        simpl in Hlookup_path; try discriminate.
      pose proof (store_refs_exclude_lookup_value x s_base y se Hrefs Hlookup_base)
        as Hse_refs.
      pose proof (value_refs_exclude_lookup_path x (se_val se) path old_v
                    Hse_refs Hlookup_path) as Hold_refs.
      exact Hold_refs.
  - intros s s1 s2 p y path e_new v_new Heval_place Heval_new IH
      Hupdate x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    destruct (IH x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr _ |- _ => exact H
                end)
                ltac:(simpl in Hfree; intros Hin; apply Hfree;
                      right; exact Hin)
                ltac:(match goal with
                | H : ~ In x (expr_local_store_names _) |- _ => exact H
                end) Hrefs)
      as [s1_base [Hs1 [Heval_base [Hrefs1 Hvnew]]]].
    subst s1.
    destruct (store_update_path_store_add_inv y x path T hidden v_new
                s1_base s2 Hyx Hupdate)
      as [s2_base [Hs2 Hupdate_base]].
    exists s2_base. repeat split; try assumption.
    + eapply Eval_Assign_Place; eassumption.
    + eapply store_update_path_refs_exclude_root; eassumption.
    + constructor.
  - intros s p y path rk Heval_place x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hplace_fresh : place_name p <> x).
    { intros Heq. apply Hfree. subst. simpl. left. reflexivity. }
    destruct (eval_place_store_add_strip s_base p y path x T hidden
                Hplace_fresh Hrefs Heval_place)
      as [Hyx Hplace_base].
    exists s_base. repeat split; try assumption.
    + eapply Eval_Borrow; eassumption.
    + constructor. apply ident_eqb_neq. intros Heq. apply Hyx. symmetry. exact Heq.
  - intros s r p y path se v Ty Has_place Heval_place Hlookup Hvalue
      Hty Husage x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s_r r y path se v Ty Hnot_place Heval_r IHr Hlookup
      Hvalue Hty Husage x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps x T hidden s_base Hs Hready
      Hfree Hlocal Hrefs.
    subst s. exists s_base. repeat split; try assumption.
    + eapply Eval_Fn; eassumption.
    + constructor. constructor.
  - intros s fname captures captured fdef Hlookup Hcopy x T hidden
      s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    subst s1.
    assert (Hfree_then : ~ In x (free_vars_expr e2)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (Hlocal_then : ~ In x (expr_local_store_names e2)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    destruct (IHthen x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e2 |- _ => exact H
                end) Hfree_then Hlocal_then Hrefs1)
      as [s2_base [Hs2 [Heval_then_base [Hrefs2 Hv]]]].
    exists s2_base. repeat split; try assumption.
    subst s2. eapply Eval_If_True; eassumption.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    assert (Hfree_cond : ~ In x (free_vars_expr e1)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. left. exact Hin. }
    assert (Hlocal_cond : ~ In x (expr_local_store_names e1)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. left. exact Hin. }
    destruct (IHcond x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e1 |- _ => exact H
                end) Hfree_cond Hlocal_cond Hrefs)
      as [s1_base [Hs1 [Heval_cond_base [Hrefs1 _]]]].
    subst s1.
    assert (Hfree_else : ~ In x (free_vars_expr e3)).
    { simpl in Hfree. intros Hin. apply Hfree. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    assert (Hlocal_else : ~ In x (expr_local_store_names e3)).
    { simpl in Hlocal. intros Hin. apply Hlocal. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    destruct (IHelse x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e3 |- _ => exact H
                end) Hfree_else Hlocal_else Hrefs1)
      as [s2_base [Hs2 [Heval_else_base [Hrefs2 Hv]]]].
    exists s2_base. repeat split; try assumption.
    subst s2. eapply Eval_If_False; eassumption.
  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody x T hidden s_base Hs
      Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s s_fn s_args s_body callee args fname captured fdef fcall
      vs ret used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    inversion Hready.
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_args IHargs
      x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. inversion Hready; subst.
    destruct (args_free_vars_ts_cons_notin x e es Hfree)
      as [Hfree_e Hfree_es].
    destruct (args_local_store_names_cons_notin x e es Hlocal)
      as [Hlocal_e Hlocal_es].
    destruct (IHe x T hidden s_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_expr e |- _ => exact H
                end) Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    subst s1.
    destruct (IHargs x T hidden s1_base eq_refl
                ltac:(match goal with
                | H : preservation_ready_args es |- _ => exact H
                end) Hfree_es Hlocal_es Hrefs1)
      as [s2_base [Hs2 [Heval_args_base [Hrefs2 Hvs]]]].
    exists s2_base. repeat split; try assumption.
    + subst s2. eapply EvalArgs_Cons; eassumption.
    + constructor; assumption.
  - intros s x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s. exists s_base. repeat split; try constructor; assumption.
  - intros s s1 s2 fields f rest e v values Hlookup Heval_e IHe
      Heval_fields IHfields x T hidden s_base Hs Hready Hfree Hlocal Hrefs.
    subst s.
    assert (Hready_e : preservation_ready_expr e).
    { eapply preservation_ready_fields_lookup; eassumption. }
    assert (Hfree_e : ~ In x (free_vars_expr e)).
    { eapply fields_free_vars_ts_lookup_notin; eassumption. }
    assert (Hlocal_e : ~ In x (expr_local_store_names e)).
    { eapply fields_local_store_names_lookup_notin; eassumption. }
    destruct (IHe x T hidden s_base eq_refl Hready_e Hfree_e Hlocal_e Hrefs)
      as [s1_base [Hs1 [Heval_e_base [Hrefs1 Hv]]]].
    subst s1.
    destruct (IHfields x T hidden s1_base eq_refl Hready Hfree Hlocal Hrefs1)
      as [s2_base [Hs2 [Heval_fields_base [Hrefs2 Hvalues]]]].
    exists s2_base. repeat split; try assumption.
    + subst s2. eapply EvalStructFields_Cons; eassumption.
    + constructor; assumption.
  }
  repeat split; intros env; destruct (Hmut env) as [Heval [Hargs Hfields]]; eauto.
Qed.

Lemma preservation_ready_eval_args_hidden_frame_strip :
  forall env s args s_hidden' vs x T hidden,
    eval_args env (store_add x T hidden s) args s_hidden' vs ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s ->
    exists s',
      s_hidden' = store_add x T hidden s' /\
      eval_args env s args s' vs /\
      store_refs_exclude_root x s' /\
      Forall (value_refs_exclude_root x) vs.
Proof.
  intros env s args s_hidden' vs x T hidden Heval Hready Hfree Hlocal Hrefs.
  destruct hidden_frame_eval_strip_mutual as [_ [Hargs _]].
  eapply (Hargs env (store_add x T hidden s) args s_hidden' vs Heval
            x T hidden s eq_refl); eassumption.
Qed.

Lemma store_refs_exclude_root_app :
  forall root s1 s2,
    store_refs_exclude_root root s1 ->
    store_refs_exclude_root root s2 ->
    store_refs_exclude_root root (s1 ++ s2).
Proof.
  intros root s1.
  induction s1 as [| se rest IH]; intros s2 H1 H2; simpl.
  - exact H2.
  - inversion H1; subst. constructor; eauto.
Qed.

Lemma store_add_refs_exclude_root :
  forall root x T v s,
    value_refs_exclude_root root v ->
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (store_add x T v s).
Proof.
  intros root x T v s Hv Hs.
  unfold store_add. constructor.
  - constructor. exact Hv.
  - exact Hs.
Qed.

Lemma bind_params_refs_exclude_root :
  forall root ps vs s,
    Forall (value_refs_exclude_root root) vs ->
    store_refs_exclude_root root s ->
    store_refs_exclude_root root (bind_params ps vs s).
Proof.
  intros root ps.
  induction ps as [| p ps IH]; intros vs s Hvs Hs;
    destruct vs as [| v vs']; simpl; try exact Hs.
  inversion Hvs; subst.
  apply store_add_refs_exclude_root; eauto.
Qed.

Lemma store_remove_store_add_same :
  forall x T v s,
    store_remove x (store_add x T v s) = s.
Proof.
  intros x T v s.
  unfold store_add. simpl. rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma store_remove_commute_neq :
  forall x y s,
    x <> y ->
    store_remove x (store_remove y s) =
      store_remove y (store_remove x s).
Proof.
  intros x y s Hneq.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb y (se_name se)) eqn:Hy;
    destruct (ident_eqb x (se_name se)) eqn:Hx; simpl.
  - apply ident_eqb_eq in Hy. apply ident_eqb_eq in Hx.
    subst. contradiction.
  - rewrite Hy. reflexivity.
  - rewrite Hx. reflexivity.
  - rewrite Hy, Hx. rewrite IH. reflexivity.
Qed.

Lemma store_remove_params_store_remove_commute :
  forall ps x s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove x (store_remove_params ps s) =
      store_remove_params ps (store_remove x s).
Proof.
  induction ps as [| p ps IH]; intros x s Hnotin; simpl.
  - reflexivity.
  - rewrite store_remove_commute_neq.
    + rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
    + intros Heq. apply Hnotin. left. exact Heq.
Qed.

Lemma store_remove_params_store_add_non_param :
  forall ps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove_params ps (store_add x T v s) =
      store_add x T v (store_remove_params ps s).
Proof.
  induction ps as [| p ps IH]; intros x T v s Hnotin; simpl.
  - reflexivity.
  - unfold store_add. simpl.
    destruct (ident_eqb (param_name p) x) eqn:Hpx.
    + apply ident_eqb_eq in Hpx. subst x.
      contradiction Hnotin. left. reflexivity.
    + change (MkStoreEntry x T v (binding_state_of_bool false) ::
        store_remove (param_name p) s)
        with (store_add x T v (store_remove (param_name p) s)).
      rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_hidden_after_params :
  forall ps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_remove x (store_remove_params ps (store_add x T v s)) =
      store_remove_params ps s.
Proof.
  intros ps x T v s Hnotin.
  rewrite store_remove_params_store_add_non_param by exact Hnotin.
  rewrite store_remove_store_add_same. reflexivity.
Qed.

Lemma store_remove_hidden_after_param_groups :
  forall ps caps x T v s,
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (ctx_names (params_ctx caps)) ->
    store_remove x
      (store_remove_params caps
        (store_remove_params ps (store_add x T v s))) =
      store_remove_params caps (store_remove_params ps s).
Proof.
  intros ps caps x T v s Hnotin_ps Hnotin_caps.
  rewrite store_remove_params_store_add_non_param by exact Hnotin_ps.
  rewrite store_remove_params_store_add_non_param by exact Hnotin_caps.
  rewrite store_remove_store_add_same. reflexivity.
Qed.

Lemma alpha_rename_fn_def_params_not_in_used :
  forall used f fr used' x,
    alpha_rename_fn_def used f = (fr, used') ->
    In x used ->
    ~ In x (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros used f fr used' x Hrename Hused Hin.
  pose proof (alpha_rename_fn_def_params_fresh_used
                used f fr used' Hrename x Hin) as Hfresh.
  exact (Hfresh Hused).
Qed.

Lemma alpha_rename_fn_def_body_local_store_names_not_in_used :
  forall used f fr used' x,
    alpha_rename_fn_def used f = (fr, used') ->
    In x used ->
    ~ In x (expr_local_store_names (fn_body fr)).
Proof.
  intros used f fr used' x Hrename Hused Hin.
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                used f fr used' Hrename) as Hfresh.
  pose proof (proj1 (Forall_forall _ _) Hfresh x Hin) as Hnotin.
  exact (Hnotin Hused).
Qed.

Lemma eval_let_make_closure_captured_call_args_strip :
  forall env s s_final m x T fname captures args ret,
    ty_usage T = UUnrestricted ->
    eval env s
      (ELet m x T (EMakeClosure fname captures)
        (ECallExpr (EVar x) args)) s_final ret ->
    preservation_ready_args args ->
    ~ In x (args_free_vars_ts args) ->
    ~ In x (args_local_store_names args) ->
    store_refs_exclude_root x s ->
    exists captured fdef s_args_hidden s_args vs fcall used' s_body,
      lookup_fn fname (env_fns env) = Some fdef /\
      copy_capture_store_as captures (fn_captures fdef) s = Some captured /\
      s_args_hidden = store_add x T (VClosure fname captured) s_args /\
      eval_args env s args s_args vs /\
      store_refs_exclude_root x s_args /\
      Forall (value_refs_exclude_root x) vs /\
      alpha_rename_fn_def (store_names (captured ++ s_args_hidden)) fdef =
        (fcall, used') /\
      eval env (bind_params (fn_params fcall) vs (captured ++ s_args_hidden))
        (fn_body fcall) s_body ret /\
      s_final =
        store_remove x
          (store_remove_params (fn_captures fcall)
            (store_remove_params (fn_params fcall) s_body)).
Proof.
  intros env s s_final m x T fname captures args ret Husage Heval Hready
    Hfree Hlocal Hrefs.
  inversion Heval; subst; clear Heval.
  match goal with
  | Hmake : eval _ _ (EMakeClosure _ _) _ _ |- _ =>
      inversion Hmake; subst; clear Hmake
  end.
  match goal with
  | Hcall : eval _ _ (ECallExpr (EVar x) args) _ _ |- _ =>
      inversion Hcall; subst; clear Hcall
  end.
  match goal with
  | Hcallee : eval _ _ (EVar x) _ _ |- _ =>
      inversion Hcallee; subst; clear Hcallee
  end.
  - match goal with
    | Hlookup_var : store_lookup x
        (store_add x T (VClosure fname ?captured) ?s_base) =
        Some ?se |- _ =>
        rewrite store_lookup_store_add_same in Hlookup_var;
        inversion Hlookup_var; subst se; clear Hlookup_var
    end.
    repeat match goal with
    | Hvalue : se_val _ = VClosure _ _ |- _ =>
        simpl in Hvalue; inversion Hvalue; subst; clear Hvalue
    end.
    match goal with
    | Hlookup_make : lookup_fn ?fname_call (env_fns env) = Some ?fdef_make,
      Hlookup_call : lookup_fn ?fname_call (env_fns env) = Some ?fdef_call |- _ =>
        assert (Hfdef_same : fdef_call = fdef_make)
        by (eapply lookup_fn_deterministic; eassumption);
        subst fdef_call
    end.
    match goal with
    | Heval_args : eval_args _ _ _ _ _ |- _ =>
        destruct (preservation_ready_eval_args_hidden_frame_strip
                    env s1 args s_args vs x T (VClosure fname0 captured0)
                    Heval_args Hready Hfree Hlocal Hrefs)
          as [s_args_base [Hs_args_hidden
            [Heval_args_base [Hrefs_args Hvs_refs]]]]
    end.
    subst s_args.
    exists captured0, fdef,
      (store_add x T (VClosure fname0 captured0) s_args_base),
      s_args_base, vs, fcall, used', s_body.
    repeat split; try eassumption.
  - match goal with
    | Hlookup_var : store_lookup x
        (store_add x T (VClosure fname ?captured) ?s_base) =
        Some ?se |- _ =>
        rewrite store_lookup_store_add_same in Hlookup_var;
        inversion Hlookup_var; subst se; clear Hlookup_var
    end.
    match goal with
    | Hconsume : needs_consume _ = true |- _ =>
        simpl in Hconsume;
        unfold needs_consume in Hconsume;
        rewrite Husage in Hconsume;
        discriminate
    end.
Qed.

Definition params_fresh_in_store (ps : list param) (s : store) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names s).

Lemma ctx_names_params_ctx_apply_lt_params :
  forall σ ps,
    ctx_names (params_ctx (apply_lt_params σ ps)) =
    ctx_names (params_ctx ps).
Proof.
  intros σ ps.
  induction ps as [| p ps IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma apply_lt_params_length :
  forall σ ps,
    List.length (apply_lt_params σ ps) = List.length ps.
Proof.
  intros σ ps.
  unfold apply_lt_params.
  rewrite length_map. reflexivity.
Qed.

Lemma params_fresh_in_store_apply_lt_params :
  forall σ ps s,
    params_fresh_in_store ps s ->
    params_fresh_in_store (apply_lt_params σ ps) s.
Proof.
  unfold params_fresh_in_store.
  intros σ ps s Hfresh x Hin.
  rewrite ctx_names_params_ctx_apply_lt_params in Hin.
  exact (Hfresh x Hin).
Qed.

Lemma params_ctx_names_nodup_apply_lt_params :
  forall σ ps,
    NoDup (ctx_names (params_ctx ps)) ->
    NoDup (ctx_names (params_ctx (apply_lt_params σ ps))).
Proof.
  intros σ ps Hnodup.
  rewrite ctx_names_params_ctx_apply_lt_params.
  exact Hnodup.
Qed.

Lemma alpha_rename_fn_def_params_fresh_in_store :
  forall s f fr used',
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    params_fresh_in_store (fn_params fr) s.
Proof.
  unfold params_fresh_in_store.
  intros s f fr used' Hrename x Hin.
  eapply alpha_rename_fn_def_params_fresh_used.
  - exact Hrename.
  - exact Hin.
Qed.

Lemma alpha_rename_fn_def_params_nodup_ctx_names :
  forall s f fr used',
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    NoDup (ctx_names (params_ctx (fn_params fr))).
Proof.
  intros s f fr used' Hrename.
  eapply alpha_rename_fn_def_params_nodup.
  exact Hrename.
Qed.

Lemma params_fresh_in_store_tail :
  forall p ps s,
    params_fresh_in_store (p :: ps) s ->
    params_fresh_in_store ps s.
Proof.
  unfold params_fresh_in_store.
  intros p ps s Hfresh x Hin.
  apply Hfresh. simpl. right. exact Hin.
Qed.

Lemma params_fresh_in_store_head :
  forall p ps s,
    params_fresh_in_store (p :: ps) s ->
    ~ In (param_name p) (store_names s).
Proof.
  unfold params_fresh_in_store.
  intros p ps s Hfresh.
  apply Hfresh. simpl. left. reflexivity.
Qed.

Lemma params_ctx_names_nodup_tail :
  forall p ps,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    NoDup (ctx_names (params_ctx ps)).
Proof.
  intros p ps Hnodup.
  simpl in Hnodup. inversion Hnodup; subst. assumption.
Qed.

Lemma params_ctx_names_nodup_head_not_tail :
  forall p ps,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    ~ In (param_name p) (ctx_names (params_ctx ps)).
Proof.
  intros p ps Hnodup.
  simpl in Hnodup. inversion Hnodup; subst. assumption.
Qed.

Lemma store_typed_names :
  forall env s Σ,
    store_typed env s Σ ->
    store_names s = ctx_names Σ.
Proof.
  intros env s Σ Htyped.
  induction Htyped as [| se ce s_tail Σ_tail Hentry _ IH].
  - reflexivity.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname _].
    simpl. rewrite Hname, IH. reflexivity.
Qed.

Lemma store_lookup_not_in_names :
  forall x s,
    ~ In x (store_names s) ->
    store_lookup x s = None.
Proof.
  intros x s Hnotin.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    contradiction Hnotin. left. reflexivity.
  - apply IH.
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_lookup_none_not_in_names :
  forall x s,
    store_lookup x s = None ->
    ~ In x (store_names s).
Proof.
  intros x s Hlookup.
  induction s as [| se rest IH]; simpl in *.
  - intros Hin. exact Hin.
  - destruct (ident_eqb x (se_name se)) eqn:Heq; try discriminate.
    intros [Hin | Hin].
    + subst x. rewrite ident_eqb_refl in Heq. discriminate.
    + apply (IH Hlookup Hin).
Qed.

Lemma check_make_closure_captures_exact_sctx_params_fresh_in_store :
  forall env Ω s Σ captures caps captured_tys,
    store_typed env s Σ ->
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    params_fresh_in_store caps s.
Proof.
  intros env Ω s Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys
    Hstore Hcheck;
    destruct caps as [| cap caps]; simpl in Hcheck; try discriminate.
  - unfold params_fresh_in_store. intros y Hin. contradiction.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hcheck;
      try discriminate.
    destruct (sctx_lookup (param_name cap) Σ) as [[Tcap stcap] |]
      eqn:Hcap_lookup; try discriminate.
    destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
    destruct (st_consumed st) eqn:Hconsumed; try discriminate.
    destruct (st_moved_paths st) as [| moved moved_rest] eqn:Hmoved;
      try discriminate.
    destruct (sctx_lookup_mut x Σ) as [m |] eqn:Hmut; try discriminate.
    destruct m; try discriminate.
    destruct (usage_eqb (ty_usage T) UUnrestricted) eqn:Husage;
      try discriminate.
    destruct (capture_ref_free_ty_b env T) eqn:Href_free; try discriminate.
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    destruct (check_make_closure_captures_exact_sctx env Ω Σ captures caps)
      as [captured_rest | err] eqn:Hrest; try discriminate.
    injection Hcheck as <-.
    unfold params_fresh_in_store.
    intros y Hin.
    simpl in Hin. destruct Hin as [Hin | Hin].
    + subst y.
      intros Hin_store.
      apply (sctx_lookup_none_not_in_names (param_name cap) Σ Hcap_lookup).
      rewrite (store_typed_names env s Σ Hstore) in Hin_store.
      exact Hin_store.
    + eapply IH.
      * exact Hstore.
      * exact Hrest.
      * exact Hin.
Qed.

Inductive eval_args_values_have_types
    (env : global_env) (Ω : outlives_ctx) (s : store)
    : list value -> list param -> Prop :=
  | AHT_Nil :
      eval_args_values_have_types env Ω s [] []
  | AHT_Cons : forall v vs p ps T_actual,
      value_has_type env s v T_actual ->
      ty_compatible Ω T_actual (param_ty p) ->
      eval_args_values_have_types env Ω s vs ps ->
      eval_args_values_have_types env Ω s (v :: vs) (p :: ps).

Lemma eval_args_values_have_types_length :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    List.length vs = List.length ps.
Proof.
  intros env Ω s vs ps Hargs.
  induction Hargs; simpl; congruence.
Qed.

Lemma eval_args_values_have_types_store_preserved :
  forall env Ω s s' vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_ref_targets_preserved env s s' ->
    eval_args_values_have_types env Ω s' vs ps.
Proof.
  intros env Ω s s' vs ps Hargs Hpres.
  induction Hargs as [| v vs p ps T_actual Hvalue Hcompat _ IH].
  - constructor.
  - eapply AHT_Cons with (T_actual := T_actual).
    + eapply value_has_type_store_preserved; eassumption.
    + exact Hcompat.
    + exact IH.
Qed.

Lemma eval_args_values_have_types_apply_lt_params_inv :
  forall env Ω s vs σ ps,
    eval_args_values_have_types env Ω s vs (apply_lt_params σ ps) ->
    eval_args_values_have_types env Ω s vs ps.
Proof.
  intros env Ω s vs σ ps.
  revert vs.
  induction ps as [| p ps IH]; intros vs Hargs; simpl in Hargs.
  - inversion Hargs; subst. constructor.
  - inversion Hargs as [| v vs' p_subst ps_subst T_actual Hvalue Hcompat Htail];
      subst; clear Hargs.
    simpl in Hcompat.
    eapply AHT_Cons with (T_actual := param_ty p).
    + eapply VHT_LifetimeEquiv.
      * eapply value_has_type_compatible.
        -- exact Hvalue.
        -- exact Hcompat.
      * apply ty_lifetime_equiv_sym.
        apply ty_lifetime_equiv_apply_lt_ty.
    + apply ty_compatible_refl.
    + apply IH. exact Htail.
Qed.

Lemma eval_args_values_have_types_params_alpha :
  forall env Ω s vs ps psr,
    params_alpha ps psr ->
    eval_args_values_have_types env Ω s vs ps ->
    eval_args_values_have_types env Ω s vs psr.
Proof.
  intros env Ω s vs ps psr Halpha Hargs.
  revert vs Hargs.
  induction Halpha as [| p pr ps psr Hshape Halpha IH];
    intros vs Hargs.
  - inversion Hargs; subst. constructor.
  - inversion Hargs as [| v vs_tail p0 ps0 T_actual Hv Hcompat Htail];
      subst; clear Hargs.
    destruct Hshape as [_ Hty].
    eapply AHT_Cons with (T_actual := T_actual).
    + exact Hv.
    + rewrite <- Hty. exact Hcompat.
    + apply IH. exact Htail.
Qed.

Lemma alpha_rename_fn_def_call_bind_params_premises :
  forall env Ω s vs σ f fr used',
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (fn_params f)) ->
    same_fn_shape f fr ->
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    NoDup (ctx_names (params_ctx (apply_lt_params σ (fn_params fr)))) /\
    params_fresh_in_store (apply_lt_params σ (fn_params fr)) s /\
    eval_args_values_have_types env Ω s vs
      (apply_lt_params σ (fn_params fr)).
Proof.
  intros env Ω s vs σ f fr used' Hargs Hshape Hrename.
  destruct Hshape as [_ [_ Hparams_alpha]].
  repeat split.
  - apply params_ctx_names_nodup_apply_lt_params.
    eapply alpha_rename_fn_def_params_nodup_ctx_names.
    exact Hrename.
  - apply params_fresh_in_store_apply_lt_params.
    eapply alpha_rename_fn_def_params_fresh_in_store.
    exact Hrename.
  - eapply eval_args_values_have_types_params_alpha.
    + apply params_alpha_apply_lt_compat.
      exact Hparams_alpha.
    + exact Hargs.
Qed.

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
    Forall2 (store_entry_typed env full) captured (params_ctx caps) ->
    store_param_prefix caps captured [].
Proof.
  intros env full captured.
  induction captured as [| se captured IH]; intros caps Htyped;
    destruct caps as [| cap caps]; simpl in Htyped; inversion Htyped; subst.
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct cap as [pname pty pmut].
    simpl in H2.
    destruct H2 as [Hname [Hty [_ _]]].
    simpl in *. subst sx sT.
    constructor.
    eapply IH. exact H4.
Qed.

Lemma captured_params_store_typed_store_param_prefix :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    store_param_prefix caps captured [].
Proof.
  intros env captured caps Htyped.
  unfold captured_params_store_typed, store_typed in Htyped.
  eapply store_typed_entries_params_store_param_prefix.
  exact Htyped.
Qed.

Lemma captured_params_store_typed_prefix_frame :
  forall env captured caps frame,
    captured_params_store_typed env captured caps ->
    store_typed_prefix env (captured ++ frame)
      (sctx_of_ctx (params_ctx caps)).
Proof.
  intros env captured caps frame Htyped.
  unfold captured_params_store_typed, store_typed_prefix in *.
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

Fixpoint root_env_add_params_roots
    (ps : list param) (roots : list root_set) (R : root_env) : root_env :=
  match ps, roots with
  | p :: ps', roots_p :: roots' =>
      root_env_add (param_name p) roots_p
        (root_env_add_params_roots ps' roots' R)
  | _, _ => R
  end.

Lemma root_env_lookup_add_eq :
  forall x roots R,
    root_env_lookup x (root_env_add x roots R) = Some roots.
Proof.
  intros x roots R. unfold root_env_add. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma root_env_lookup_add_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup y (root_env_add x roots R) = root_env_lookup y R.
Proof.
  intros x y roots R Hneq. unfold root_env_add. simpl.
  destruct (ident_eqb y x) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y. contradiction Hneq. reflexivity.
  - reflexivity.
Qed.

Lemma root_env_lookup_update_eq :
  forall x roots R roots_old,
    root_env_lookup x R = Some roots_old ->
    root_env_lookup x (root_env_update x roots R) = Some roots.
Proof.
  intros x roots R.
  induction R as [| [y roots_y] rest IH]; intros roots_old Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - simpl. rewrite Heq. reflexivity.
  - simpl. rewrite Heq. exact (IH roots_old Hlookup).
Qed.

Lemma root_env_lookup_update_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup y (root_env_update x roots R) = root_env_lookup y R.
Proof.
  intros x y roots R Hneq.
  induction R as [| [z roots_z] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x z) eqn:Hxz; simpl.
  - destruct (ident_eqb y z) eqn:Hyz.
    + apply ident_eqb_eq in Hxz. apply ident_eqb_eq in Hyz.
      subst z. subst y. contradiction Hneq. reflexivity.
    + reflexivity.
  - destruct (ident_eqb y z); try reflexivity.
    exact IH.
Qed.

Lemma root_env_lookup_remove_neq :
  forall x y R,
    x <> y ->
    root_env_lookup y (root_env_remove x R) = root_env_lookup y R.
Proof.
  intros x y R Hneq.
  induction R as [| [z roots_z] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x z) eqn:Hxz.
  - apply ident_eqb_eq in Hxz. subst z.
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y. contradiction Hneq. reflexivity.
    + reflexivity.
  - simpl.
    destruct (ident_eqb y z); try reflexivity.
    exact IH.
Qed.

Lemma root_env_equiv_app :
  forall R1 R1' R2 R2',
    root_env_equiv R1 R1' ->
    root_env_equiv R2 R2' ->
    root_env_equiv (R1 ++ R2) (R1' ++ R2').
Proof.
  unfold root_env_equiv.
  intros R1 R1' R2 R2' Heq1 Heq2 x.
  specialize (Heq1 x).
  specialize (Heq2 x).
  destruct (root_env_lookup x R1) as [roots1 |] eqn:Hlookup1;
    destruct (root_env_lookup x R1') as [roots1' |] eqn:Hlookup1';
    try contradiction.
  - rewrite (root_env_lookup_app_left x R1 R2 roots1 Hlookup1).
    rewrite (root_env_lookup_app_left x R1' R2' roots1' Hlookup1').
    exact Heq1.
  - rewrite (root_env_lookup_app_right x R1 R2 Hlookup1).
    rewrite (root_env_lookup_app_right x R1' R2' Hlookup1').
    exact Heq2.
Qed.

Lemma root_env_remove_lookup_none :
  forall x R,
    root_env_lookup x R = None ->
    root_env_remove x R = R.
Proof.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros Hlookup; simpl in *.
  - reflexivity.
  - destruct (ident_eqb x y); try discriminate.
    rewrite IH by exact Hlookup. reflexivity.
Qed.

Lemma root_env_remove_app_left :
  forall x R1 R2,
    root_env_lookup x R2 = None ->
    root_env_remove x (R1 ++ R2) = root_env_remove x R1 ++ R2.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 Hlookup_tail;
    simpl in *.
  - apply root_env_remove_lookup_none. exact Hlookup_tail.
  - destruct (ident_eqb x y); try reflexivity.
    rewrite IH by exact Hlookup_tail. reflexivity.
Qed.

Lemma root_env_update_app_left :
  forall x roots R1 R2 roots_old,
    root_env_lookup x R1 = Some roots_old ->
    root_env_update x roots (R1 ++ R2) =
      root_env_update x roots R1 ++ R2.
Proof.
  intros x roots R1.
  induction R1 as [| [y roots_y] rest IH]; intros R2 roots_old Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y); try reflexivity.
  rewrite IH with (roots_old := roots_old) by exact Hlookup.
  reflexivity.
Qed.

Fixpoint root_env_remove_params (ps : list param) (R : root_env)
    : root_env :=
  match ps with
  | [] => R
  | p :: ps' => root_env_remove_params ps' (root_env_remove (param_name p) R)
  end.

Definition call_param_root_env
    (ps : list param) (arg_roots : list root_set) (R_tail : root_env)
    : root_env :=
  root_env_add_params_roots ps arg_roots
    (root_env_remove_params ps R_tail).

Lemma root_env_add_params_roots_app_tail :
  forall ps roots_list R_tail,
    root_env_add_params_roots ps roots_list R_tail =
      root_env_add_params_roots ps roots_list [] ++ R_tail.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R_tail;
    destruct roots_list as [| roots roots_list]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma root_env_remove_params_empty :
  forall ps,
    root_env_remove_params ps [] = [].
Proof.
  induction ps as [| p ps IH]; simpl; try reflexivity.
  exact IH.
Qed.

Lemma root_env_remove_params_app_left :
  forall ps R1 R2,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R2 = None) ->
    root_env_remove_params ps (R1 ++ R2) =
      root_env_remove_params ps R1 ++ R2.
Proof.
  induction ps as [| p ps IH]; intros R1 R2 Hlookup_tail; simpl.
  - reflexivity.
  - rewrite root_env_remove_app_left.
    + apply IH. intros x Hin.
      apply Hlookup_tail. right. exact Hin.
    + apply Hlookup_tail. left. reflexivity.
Qed.

Lemma call_param_root_env_app_tail :
  forall ps roots_list R_tail,
    call_param_root_env ps roots_list R_tail =
      call_param_root_env ps roots_list [] ++
        root_env_remove_params ps R_tail.
Proof.
  intros ps roots_list R_tail.
  unfold call_param_root_env at 1 2.
  rewrite root_env_remove_params_empty.
  apply root_env_add_params_roots_app_tail.
Qed.

Lemma root_env_add_params_roots_app_roots :
  forall ps qs roots_ps roots_qs R,
    List.length roots_ps = List.length ps ->
    root_env_add_params_roots (ps ++ qs) (roots_ps ++ roots_qs) R =
      root_env_add_params_roots ps roots_ps
        (root_env_add_params_roots qs roots_qs R).
Proof.
  induction ps as [| p ps IH]; intros qs roots_ps roots_qs R Hlen;
    destruct roots_ps as [| roots roots_ps]; simpl in *; try discriminate.
  - reflexivity.
  - inversion Hlen as [Hlen_tail].
    rewrite IH by exact Hlen_tail.
    reflexivity.
Qed.

Lemma root_env_add_params_roots_preserves_equiv :
  forall ps roots_list R R',
    root_env_equiv R R' ->
    root_env_equiv
      (root_env_add_params_roots ps roots_list R)
      (root_env_add_params_roots ps roots_list R').
Proof.
  induction ps as [| p ps IH]; intros roots_list R R' Heq;
    destruct roots_list as [| roots roots_list]; simpl.
  - exact Heq.
  - exact Heq.
  - exact Heq.
  - apply root_env_equiv_add.
    + apply root_set_equiv_refl.
    + apply IH. exact Heq.
Qed.

Lemma call_param_root_env_app_roots :
  forall ps qs roots_ps roots_qs R,
    List.length roots_ps = List.length ps ->
    call_param_root_env (ps ++ qs) (roots_ps ++ roots_qs) R =
      root_env_add_params_roots ps roots_ps
        (root_env_add_params_roots qs roots_qs
          (root_env_remove_params (ps ++ qs) R)).
Proof.
  intros ps qs roots_ps roots_qs R Hlen.
  unfold call_param_root_env.
  apply root_env_add_params_roots_app_roots. exact Hlen.
Qed.

Lemma params_alpha_refl_ts :
  forall ps,
    params_alpha ps ps.
Proof.
  apply params_alpha_refl.
Qed.

Lemma params_alpha_app_ts :
  forall ps psr qs qsr,
    params_alpha ps psr ->
    params_alpha qs qsr ->
    params_alpha (ps ++ qs) (psr ++ qsr).
Proof.
  intros ps psr qs qsr Halpha_ps Halpha_qs.
  induction Halpha_ps as [| p pr ps psr Hshape Halpha_tail IH];
    simpl.
  - exact Halpha_qs.
  - constructor; assumption.
Qed.

Lemma alpha_rename_fn_def_binding_params_alpha_ts :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    params_alpha (fn_params f ++ fn_captures f)
      (fn_params fr ++ fn_captures fr).
Proof.
  intros used f fr used' Hrename.
  apply params_alpha_app_ts.
  - pose proof (alpha_rename_fn_def_shape used f fr used' Hrename)
      as [_ [_ Hparams_alpha]].
    exact Hparams_alpha.
  - rewrite <- (alpha_rename_fn_def_captures used f fr used' Hrename).
    apply params_alpha_refl_ts.
Qed.

Lemma root_env_remove_app_right_lookup_none :
  forall x R1 R2,
    root_env_lookup x R1 = None ->
    root_env_remove x (R1 ++ R2) = R1 ++ root_env_remove x R2.
Proof.
  intros x R1.
  induction R1 as [| [y roots_y] R1 IH]; intros R2 Hlookup; simpl in *.
  - reflexivity.
  - destruct (ident_eqb x y) eqn:Heq; try discriminate.
    rewrite IH by exact Hlookup.
    reflexivity.
Qed.

Lemma root_env_remove_params_lookup_none_self :
  forall ps R,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R = None) ->
    root_env_remove_params ps R = R.
Proof.
  induction ps as [| p ps IH]; intros R Hfresh; simpl.
  - reflexivity.
  - rewrite root_env_remove_lookup_none.
    + apply IH. intros x Hin.
      apply Hfresh. right. exact Hin.
    + apply Hfresh. left. reflexivity.
Qed.

Lemma root_env_remove_params_app_right_lookup_none :
  forall ps R1 R2,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R1 = None) ->
    root_env_remove_params ps (R1 ++ R2) =
      R1 ++ root_env_remove_params ps R2.
Proof.
  induction ps as [| p ps IH]; intros R1 R2 Hfresh; simpl.
  - reflexivity.
  - rewrite root_env_remove_app_right_lookup_none.
    + rewrite IH.
      * reflexivity.
      * intros x Hin. apply Hfresh. right. exact Hin.
    + apply Hfresh. left. reflexivity.
Qed.

Lemma captured_call_runtime_root_env_tail_decompose :
  forall ps arg_roots Rcap R_args,
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x Rcap = None) ->
    call_param_root_env ps arg_roots (Rcap ++ R_args) =
      call_param_root_env ps arg_roots Rcap ++
        root_env_remove_params ps R_args.
Proof.
  intros ps arg_roots Rcap R_args Hfresh_cap.
  unfold call_param_root_env.
  rewrite (root_env_remove_params_app_right_lookup_none
             ps Rcap R_args Hfresh_cap).
  rewrite (root_env_remove_params_lookup_none_self
             ps Rcap Hfresh_cap).
  rewrite (root_env_add_params_roots_app_tail
             ps arg_roots (Rcap ++ root_env_remove_params ps R_args)).
  rewrite (root_env_add_params_roots_app_tail ps arg_roots Rcap).
  rewrite app_assoc.
  reflexivity.
Qed.

Definition root_env_tail_fresh_names (R_tail : root_env)
    (names : list ident) : Prop :=
  forall x,
    In x names ->
    root_env_lookup x R_tail = None /\ root_env_excludes x R_tail.

Lemma root_env_tail_fresh_names_app_l :
  forall R_tail names1 names2,
    root_env_tail_fresh_names R_tail (names1 ++ names2) ->
    root_env_tail_fresh_names R_tail names1.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail names1 names2 Hfresh x Hin.
  apply Hfresh. apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_app_r :
  forall R_tail names1 names2,
    root_env_tail_fresh_names R_tail (names1 ++ names2) ->
    root_env_tail_fresh_names R_tail names2.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail names1 names2 Hfresh x Hin.
  apply Hfresh. apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_cons_head :
  forall R_tail x names,
    root_env_tail_fresh_names R_tail (x :: names) ->
    root_env_lookup x R_tail = None /\ root_env_excludes x R_tail.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail x names Hfresh.
  apply Hfresh. left. reflexivity.
Qed.

Lemma root_env_tail_fresh_names_cons_tail :
  forall R_tail x names,
    root_env_tail_fresh_names R_tail (x :: names) ->
    root_env_tail_fresh_names R_tail names.
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail x names Hfresh y Hin.
  apply Hfresh. right. exact Hin.
Qed.

Lemma root_env_tail_fresh_names_lookup_field :
  forall R_tail fname fields e,
    lookup_field_b fname fields = Some e ->
    root_env_tail_fresh_names R_tail (fields_local_store_names fields) ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e).
Proof.
  unfold root_env_tail_fresh_names.
  intros R_tail fname fields e Hlookup Hfresh x Hin.
  apply Hfresh.
  eapply fields_local_store_names_in_expr.
  - eapply lookup_field_b_success. exact Hlookup.
  - exact Hin.
Qed.

Theorem typed_roots_shadow_safe_tail_frame_mutual :
  forall env Ω n R_tail,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
    typed_env_roots_shadow_safe env Ω n (R ++ R_tail) Σ e T Σ'
      (R' ++ R_tail) roots) /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots_shadow_safe env Ω n R Σ args ps Σ' R' roots ->
    root_env_tail_fresh_names R_tail (args_local_store_names args) ->
    typed_args_roots_shadow_safe env Ω n (R ++ R_tail) Σ args ps Σ'
      (R' ++ R_tail) roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots_shadow_safe env Ω n lts args R Σ fields defs
      Σ' R' roots ->
    root_env_tail_fresh_names R_tail (fields_local_store_names fields) ->
    typed_fields_roots_shadow_safe env Ω n lts args (R ++ R_tail) Σ
      fields defs Σ' (R' ++ R_tail) roots).
Proof.
  intros env Ω n R_tail.
  apply typed_roots_shadow_safe_ind; intros; simpl in *.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - eapply TERS_Var_Copy; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Var_Move; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Place_Copy; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Place_Move; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_Call; eauto.
  - eapply TERS_Fn; eauto.
  - eapply TERS_MakeClosure; eauto.
  - eapply TERS_CallExpr_MakeClosure; eauto.
  - eapply TERS_Struct; eauto.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply TERS_Let.
    + apply H. exact Hfresh1.
    + exact e.
    + rewrite root_env_lookup_app_right by exact e0.
      exact Htail_lookup.
    + exact r.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply H0. exact Hfresh2.
    + exact e3.
    + exact r1.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_tail.
    destruct (root_env_tail_fresh_names_cons_head _ _ _ Hfresh_tail)
      as [Htail_lookup Htail_excl].
    pose proof (root_env_tail_fresh_names_cons_tail _ _ _ Hfresh_tail)
      as Hfresh2.
    replace (root_env_remove x R2 ++ R_tail)
      with (root_env_remove x (R2 ++ R_tail)).
    eapply TERS_LetInfer.
    + apply H. exact Hfresh1.
    + rewrite root_env_lookup_app_right by exact e.
      exact Htail_lookup.
    + exact r.
    + apply root_env_excludes_app; assumption.
    + replace (root_env_add x roots1 R1 ++ R_tail)
        with (root_env_add x roots1 (R1 ++ R_tail)) by reflexivity.
      apply H0. exact Hfresh2.
    + exact e0.
    + exact r1.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      apply root_env_excludes_app; assumption.
    + rewrite root_env_remove_app_left by exact Htail_lookup.
      reflexivity.
  - eapply TERS_Drop. eauto.
  - replace (root_env_update x (root_set_union roots_old roots_new) R1 ++
        R_tail)
      with (root_env_update x (root_set_union roots_old roots_new)
        (R1 ++ R_tail)).
    eapply TERS_Replace_Path; eauto.
    + eapply root_env_lookup_app_left; eassumption.
    + eapply root_env_lookup_app_left; eassumption.
    + rewrite root_env_update_app_left with (roots_old := roots_old)
        by eassumption.
      reflexivity.
  - replace (root_env_update x (root_set_union roots_old roots_new) R1 ++
        R_tail)
      with (root_env_update x (root_set_union roots_old roots_new)
        (R1 ++ R_tail)).
    eapply TERS_Assign_Path; eauto.
    + eapply root_env_lookup_app_left; eassumption.
    + rewrite root_env_update_app_left with (roots_old := roots_old)
        by eassumption.
      reflexivity.
  - eapply TERS_BorrowShared; eauto.
  - eapply TERS_BorrowUnique; eauto.
  - eapply TERS_DerefBorrowShared; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - eapply TERS_DerefBorrowUnique; eauto.
    eapply root_env_lookup_app_left; eassumption.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H2) as Hfresh1.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H2) as Hfresh_tail.
    pose proof (root_env_tail_fresh_names_app_l _ _ _ Hfresh_tail) as Hfresh2.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ Hfresh_tail) as Hfresh3.
    eapply TERS_If.
    + apply H. exact Hfresh1.
    + exact e.
    + apply H0. exact Hfresh2.
    + apply H1. exact Hfresh3.
    + exact e0.
    + exact e4.
    + apply root_env_equiv_app.
      * exact r.
      * apply root_env_equiv_refl.
  - constructor.
  - pose proof (root_env_tail_fresh_names_app_l _ _ _ H1) as Hfresh_e.
    pose proof (root_env_tail_fresh_names_app_r _ _ _ H1) as Hfresh_es.
    eapply TERSArgs_Cons.
    + apply H. exact Hfresh_e.
    + exact e0.
    + apply H0. exact Hfresh_es.
  - constructor.
  - eapply TERSFields_Cons.
    + exact e.
    + apply H. eapply root_env_tail_fresh_names_lookup_field; eassumption.
    + exact e0.
    + apply H0. exact H1.
Qed.

Lemma typed_env_roots_shadow_safe_tail_frame :
  forall env Ω n R_tail R Σ e T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ e T Σ' R' roots ->
    root_env_tail_fresh_names R_tail (expr_local_store_names e) ->
    typed_env_roots_shadow_safe env Ω n (R ++ R_tail) Σ e T Σ'
      (R' ++ R_tail) roots.
Proof.
  intros env Ω n R_tail.
  exact (proj1 (typed_roots_shadow_safe_tail_frame_mutual env Ω n R_tail)).
Qed.

Lemma root_env_remove_params_no_shadow :
  forall ps R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_remove_params ps R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R Hnodup; simpl.
  - exact Hnodup.
  - apply IH. apply root_env_no_shadow_remove. exact Hnodup.
Qed.

Lemma root_env_lookup_remove_params_not_in :
  forall ps R x,
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_remove_params ps R) =
      root_env_lookup x R.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hnotin; simpl in *.
  - reflexivity.
  - rewrite IH.
    + rewrite root_env_lookup_remove_neq.
      * reflexivity.
      * intros Heq. subst x. apply Hnotin. left. reflexivity.
    + intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_lookup_remove_params_none_preserved :
  forall ps R x,
    root_env_lookup x R = None ->
    root_env_lookup x (root_env_remove_params ps R) = None.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hlookup; simpl.
  - exact Hlookup.
  - apply IH.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      rewrite root_env_remove_lookup_none by exact Hlookup.
      exact Hlookup.
    + rewrite root_env_lookup_remove_neq.
      * exact Hlookup.
      * intros Hcontra. subst x.
        rewrite ident_eqb_refl in Heq. discriminate.
Qed.

Lemma root_env_remove_params_lookup_none :
  forall ps R x,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_remove_params ps R) = None.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R x Hnodup Hrn Hin; simpl in *.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct Hin as [Hin | Hin].
    + subst x.
      rewrite root_env_lookup_remove_params_not_in.
      * apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
      * exact Hnotin.
    + eapply IH.
      * exact Hnodup_tail.
      * apply root_env_no_shadow_remove. exact Hrn.
      * exact Hin.
Qed.

Lemma root_env_add_params_roots_lookup_not_in :
  forall ps roots_list R x,
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (root_env_add_params_roots ps roots_list R) =
      root_env_lookup x R.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x Hnotin;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin. left. reflexivity.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_add_params_roots_covers_lookup :
  forall ps roots_list R x,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    In x (ctx_names (params_ctx ps)) ->
    exists roots,
      root_env_lookup x (root_env_add_params_roots ps roots_list R) =
        Some roots.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x Hnodup Hlen Hin;
    destruct roots_list as [| roots roots_list]; simpl in *; try discriminate.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    inversion Hlen as [Hlen_tail].
    destruct Hin as [Hin | Hin].
    + subst x. exists roots. simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl.
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * apply ident_eqb_eq in Heq. subst x. contradiction.
      * eapply IH; eassumption.
Qed.

Lemma root_env_add_params_roots_lookup_remove_neq :
  forall ps roots_list R x y,
    x <> y ->
    root_env_lookup x (root_env_add_params_roots ps roots_list
      (root_env_remove y R)) =
    root_env_lookup x (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R x y Hneq;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - apply root_env_lookup_remove_neq. intros Heq. apply Hneq. symmetry. exact Heq.
  - destruct (ident_eqb x (param_name p)) eqn:Heq; try reflexivity.
    apply IH. exact Hneq.
Qed.

Lemma root_set_instantiate_single_param_equiv :
  forall rho x roots,
    root_subst_lookup x rho = roots ->
    root_set_equiv (root_set_instantiate rho [RParam x]) roots.
Proof.
  intros rho x roots Hlookup.
  simpl. rewrite Hlookup.
  eapply root_set_equiv_trans.
  - apply root_set_union_equiv_app.
  - simpl. rewrite app_nil_r. apply root_set_equiv_refl.
Qed.

Lemma root_env_instantiate_cons_initial_origin_notin :
  forall x roots rho ps_orig ps_current,
    ~ In x (ctx_names (params_ctx ps_orig)) ->
    root_env_instantiate ((x, roots) :: rho)
      (initial_root_env_for_params_origin ps_orig ps_current) =
    root_env_instantiate rho
      (initial_root_env_for_params_origin ps_orig ps_current).
Proof.
  intros x roots rho ps_orig.
  induction ps_orig as [| p ps_orig IH]; intros ps_current Hnotin;
    destruct ps_current as [| pc ps_current]; simpl in *; try reflexivity.
  assert (Hneq : param_name p <> x).
  { intros Heq. apply Hnotin. left. exact Heq. }
  assert (Htail : ~ In x (ctx_names (params_ctx ps_orig))).
  { intros Hin. apply Hnotin. right. exact Hin. }
  destruct (ident_eqb (param_name p) x) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction.
  - rewrite IH; [reflexivity | exact Htail].
Qed.

Lemma root_env_instantiate_initial_origin_equiv_add_params_roots :
  forall ps_orig ps_current arg_roots,
    params_alpha ps_orig ps_current ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length arg_roots = List.length ps_orig ->
    root_env_equiv
      (root_env_instantiate (root_subst_of_params ps_orig arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_current))
      (root_env_add_params_roots ps_current arg_roots []).
Proof.
  intros ps_orig ps_current arg_roots Halpha Hnodup.
  revert arg_roots.
  induction Halpha as [| p pr ps psr Hshape Halpha_tail IH];
    intros arg_roots Hlen.
  - destruct arg_roots as [| roots arg_roots]; simpl in Hlen; try discriminate.
    simpl. apply root_env_equiv_refl.
  - destruct arg_roots as [| roots arg_roots]; simpl in Hlen; try discriminate.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    inversion Hlen as [Hlen_tail].
    unfold root_env_equiv. intros x. simpl.
    destruct (ident_eqb x (param_name pr)) eqn:Heq.
    + rewrite ident_eqb_refl.
      eapply root_set_equiv_trans.
      * apply root_set_union_equiv_app.
      * simpl. rewrite app_nil_r. apply root_set_equiv_refl.
    + rewrite root_env_instantiate_cons_initial_origin_notin.
      * specialize (IH Hnodup_tail arg_roots Hlen_tail).
        unfold root_env_equiv in IH.
        apply IH.
      * exact Hnotin.
Qed.

Lemma root_env_add_params_roots_equiv_call_param_root_env :
  forall ps roots_list R_tail,
    List.length roots_list = List.length ps ->
    root_env_equiv
      (root_env_add_params_roots ps roots_list R_tail)
      (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R_tail Hlen;
    destruct roots_list as [| roots roots_list]; simpl in *; try discriminate.
  - apply root_env_equiv_refl.
  - inversion Hlen as [Hlen_tail].
    unfold root_env_equiv. intros x. simpl.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply root_set_equiv_refl.
    + apply ident_eqb_neq in Heq.
      specialize (IH roots_list (root_env_remove (param_name p) R_tail)
        Hlen_tail).
      unfold root_env_equiv in IH.
      specialize (IH x).
      rewrite root_env_add_params_roots_lookup_remove_neq in IH by exact Heq.
      exact IH.
Qed.

Lemma root_env_instantiate_initial_origin_equiv_call_param_root_env_empty :
  forall ps_orig ps_current arg_roots,
    params_alpha ps_orig ps_current ->
    NoDup (ctx_names (params_ctx ps_orig)) ->
    List.length arg_roots = List.length ps_orig ->
    root_env_equiv
      (root_env_instantiate (root_subst_of_params ps_orig arg_roots)
        (initial_root_env_for_params_origin ps_orig ps_current))
      (call_param_root_env ps_current arg_roots []).
Proof.
  intros ps_orig ps_current arg_roots Halpha Hnodup Hlen.
  pose proof Halpha as Halpha_len.
  assert (Hlen_current : List.length arg_roots = List.length ps_current).
  { assert (Hparams_len : List.length ps_orig = List.length ps_current).
    { clear Halpha Hnodup Hlen arg_roots.
      induction Halpha_len; simpl; try reflexivity.
      f_equal. exact IHHalpha_len. }
    rewrite <- Hparams_len. exact Hlen. }
  eapply root_env_equiv_trans.
  - eapply root_env_instantiate_initial_origin_equiv_add_params_roots;
      eassumption.
  - apply root_env_add_params_roots_equiv_call_param_root_env.
    exact Hlen_current.
Qed.

Lemma root_env_add_params_roots_no_shadow :
  forall ps roots_list R,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup x R = None) ->
    root_env_no_shadow (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros roots_list R Hnodup Hrn Hfresh;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - exact Hrn.
  - exact Hrn.
  - exact Hrn.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    apply root_env_no_shadow_add.
    + apply IH.
      * exact Hnodup_tail.
      * exact Hrn.
      * intros x Hin. apply Hfresh. right. exact Hin.
    + rewrite root_env_add_params_roots_lookup_not_in.
      * apply Hfresh. left. reflexivity.
      * exact Hnotin.
Qed.

Lemma call_param_root_env_no_shadow :
  forall ps roots R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R_tail ->
    root_env_no_shadow (call_param_root_env ps roots R_tail).
Proof.
  intros ps roots R_tail Hnodup Hrn.
  unfold call_param_root_env.
  apply root_env_add_params_roots_no_shadow.
  - exact Hnodup.
  - apply root_env_remove_params_no_shadow. exact Hrn.
  - intros x Hin.
    eapply root_env_remove_params_lookup_none; eassumption.
Qed.

Lemma empty_root_env_for_store_param_prefix :
  forall ps s_param s,
    store_param_prefix ps s_param s ->
    empty_root_env_for_store s_param =
      root_env_add_params_roots ps (repeat [] (List.length ps))
        (empty_root_env_for_store s).
Proof.
  intros ps s_param s Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Inductive store_param_scope : list param -> store -> store -> Prop :=
  | SPS_Prefix : forall ps s_param s,
      store_param_prefix ps s_param s ->
      store_param_scope ps s_param s
  | SPS_Local : forall ps se s_param s,
      ~ In (se_name se) (ctx_names (params_ctx ps)) ->
      store_param_scope ps s_param s ->
      store_param_scope ps
        (se :: s_param)
        s.

Lemma store_param_scope_bind_params :
  forall env Ω s vs ps,
    eval_args_values_have_types env Ω s vs ps ->
    store_param_scope ps (bind_params ps vs s) s.
Proof.
  intros env Ω s vs ps Hargs.
  constructor.
  eapply store_param_prefix_bind_params. exact Hargs.
Qed.

Lemma store_param_scope_add :
  forall ps s_param s x T v,
    ~ In x (ctx_names (params_ctx ps)) ->
    store_param_scope ps s_param s ->
    store_param_scope ps
      (store_add x T v s_param)
      s.
Proof.
  intros ps s_param s x T v Hnotin Hscope.
  unfold store_add.
  constructor; assumption.
Qed.

Inductive store_frame_scope (ps : list param) (Σ : sctx) :
    store -> store -> Prop :=
  | SFS_Prefix : forall s_param frame,
      store_param_prefix ps s_param frame ->
      store_frame_scope ps Σ s_param frame
  | SFS_Local : forall se s_param frame,
      ~ In (se_name se) (ctx_names (params_ctx ps)) ->
      In (se_name se) (ctx_names Σ) ->
      store_frame_scope ps Σ s_param frame ->
      store_frame_scope ps Σ (se :: s_param) frame.

Lemma store_frame_scope_bind_params :
  forall env Ω s vs ps Σ,
    eval_args_values_have_types env Ω s vs ps ->
    store_frame_scope ps Σ (bind_params ps vs s) s.
Proof.
  intros env Ω s vs ps Σ Hargs.
  constructor.
  eapply store_param_prefix_bind_params. exact Hargs.
Qed.

Lemma store_frame_scope_add :
  forall ps Σ s_param frame x T v,
    ~ In x (ctx_names (params_ctx ps)) ->
    In x (ctx_names Σ) ->
    store_frame_scope ps Σ s_param frame ->
    store_frame_scope ps Σ
      (store_add x T v s_param)
      frame.
Proof.
  intros ps Σ s_param frame x T v Hnotin Hin Hscope.
  unfold store_add.
  constructor; assumption.
Qed.

Lemma store_frame_scope_weaken_names :
  forall ps Σ Σ' s frame,
    (forall x, In x (ctx_names Σ) -> In x (ctx_names Σ')) ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps Σ' s frame.
Proof.
  intros ps Σ Σ' s frame Hnames Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin Hscope IH].
  - constructor. exact Hprefix.
  - econstructor 2.
    + exact Hnotin.
    + apply Hnames. exact Hin.
    + exact IH.
Qed.

Lemma store_frame_scope_add_weaken :
  forall ps Σ Σ' s frame x T v,
    ~ In x (ctx_names (params_ctx ps)) ->
    In x (ctx_names Σ') ->
    (forall y, In y (ctx_names Σ) -> In y (ctx_names Σ')) ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps Σ' (store_add x T v s) frame.
Proof.
  intros ps Σ Σ' s frame x T v Hnotin Hin Hnames Hscope.
  apply store_frame_scope_add.
  - exact Hnotin.
  - exact Hin.
  - eapply store_frame_scope_weaken_names; eassumption.
Qed.

Lemma store_frame_scope_param_scope :
  forall ps Σ s frame,
    store_frame_scope ps Σ s frame ->
    store_param_scope ps s frame.
Proof.
  intros ps Σ s frame Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin _ _ IH].
  - constructor. exact Hprefix.
  - constructor; assumption.
Qed.

Lemma store_frame_scope_same_names :
  forall ps Σ Σ' s frame,
    ctx_names Σ' = ctx_names Σ ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps Σ' s frame.
Proof.
  intros ps Σ Σ' s frame Hnames Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin Hscope IH].
  - constructor. exact Hprefix.
  - econstructor 2.
    + exact Hnotin.
    + rewrite Hnames. exact Hin.
    + exact IH.
Qed.

Lemma store_frame_scope_same_bindings :
  forall ps Σ Σ' s frame,
    sctx_same_bindings Σ Σ' ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps Σ' s frame.
Proof.
  intros ps Σ Σ' s frame Hsame Hscope.
  eapply store_frame_scope_same_names.
  - apply sctx_same_bindings_names_alpha. exact Hsame.
  - exact Hscope.
Qed.

Definition store_frame_static_fresh (Σ : sctx) (frame : store) : Prop :=
  forall x,
    In x (ctx_names Σ) ->
    ~ In x (store_names frame).

Lemma store_param_prefix_frame_static_fresh :
  forall ps s_param frame,
    store_param_prefix ps s_param frame ->
    store_no_shadow s_param ->
    store_frame_static_fresh (sctx_of_ctx (params_ctx ps)) frame.
Proof.
  unfold store_no_shadow, store_frame_static_fresh.
  intros ps s_param frame Hprefix Hshadow x Hin Hframe.
  unfold sctx_of_ctx in Hin.
  rewrite (store_names_store_param_prefix ps s_param frame Hprefix)
    in Hshadow.
  induction (ctx_names (params_ctx ps)) as [| y ys IH] in Hshadow, Hin |- *.
  - contradiction.
  - simpl in Hin.
    inversion Hshadow as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct Hin as [Hin | Hin].
    + subst y. apply Hnotin. apply in_or_app. right. exact Hframe.
    + eapply IH; eassumption.
Qed.

Lemma sctx_lookup_in_ctx_names :
  forall x Σ T st,
    sctx_lookup x Σ = Some (T, st) ->
    In x (ctx_names Σ).
Proof.
  unfold sctx_lookup.
  intros x Σ.
  induction Σ as [| [[[y Ty] sty] my] rest IH]; intros T st Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    left. reflexivity.
  - right. eapply IH. exact Hlookup.
Qed.

Lemma store_frame_static_fresh_same_names :
  forall Σ Σ' frame,
    ctx_names Σ' = ctx_names Σ ->
    store_frame_static_fresh Σ frame ->
    store_frame_static_fresh Σ' frame.
Proof.
  intros Σ Σ' frame Hnames Hfresh x Hin.
  apply Hfresh. rewrite <- Hnames. exact Hin.
Qed.

Lemma store_frame_static_fresh_same_bindings :
  forall Σ Σ' frame,
    sctx_same_bindings Σ Σ' ->
    store_frame_static_fresh Σ frame ->
    store_frame_static_fresh Σ' frame.
Proof.
  intros Σ Σ' frame Hsame Hfresh.
  eapply store_frame_static_fresh_same_names.
  - apply sctx_same_bindings_names_alpha. exact Hsame.
  - exact Hfresh.
Qed.

Lemma store_frame_static_fresh_add :
  forall Σ frame x T m,
    store_frame_static_fresh Σ frame ->
    ~ In x (store_names frame) ->
    store_frame_static_fresh (sctx_add x T m Σ) frame.
Proof.
  unfold store_frame_static_fresh, sctx_add, ctx_add.
  intros Σ frame x T m Hfresh Hnotin y Hin.
  simpl in Hin. destruct Hin as [Heq | Hin].
  - subst y. exact Hnotin.
  - apply Hfresh. exact Hin.
Qed.

Lemma ctx_names_remove_in :
  forall x y Σ,
    In y (ctx_names (sctx_remove x Σ)) ->
    In y (ctx_names Σ).
Proof.
  unfold sctx_remove.
  intros x y Σ.
  induction Σ as [| [[[z T] st] m] rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct (ident_eqb x z) eqn:Heq.
    + right. exact Hin.
    + simpl in Hin. destruct Hin as [Heq_y | Hin].
      * left. exact Heq_y.
      * right. apply IH. exact Hin.
Qed.

Lemma ctx_names_remove_preserve_neq :
  forall x y Σ,
    x <> y ->
    In y (ctx_names Σ) ->
    In y (ctx_names (sctx_remove x Σ)).
Proof.
  unfold sctx_remove.
  intros x y Σ Hneq.
  induction Σ as [| [[[z T] st] m] rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y.
      destruct (ident_eqb x z) eqn:Hxz.
      * apply ident_eqb_eq in Hxz. exfalso. apply Hneq. exact Hxz.
      * simpl. left. reflexivity.
    + destruct (ident_eqb x z) eqn:Hxz.
      * exact Hin.
      * simpl. right. apply IH. exact Hin.
Qed.

Lemma store_frame_static_fresh_remove :
  forall Σ frame x,
    store_frame_static_fresh Σ frame ->
    store_frame_static_fresh (sctx_remove x Σ) frame.
Proof.
  unfold store_frame_static_fresh.
  intros Σ frame x Hfresh y Hin.
  apply Hfresh. eapply ctx_names_remove_in. exact Hin.
Qed.

Lemma params_fresh_in_store_frame_static_fresh :
  forall ps frame,
    params_fresh_in_store ps frame ->
    store_frame_static_fresh (sctx_of_ctx (params_ctx ps)) frame.
Proof.
  unfold params_fresh_in_store, store_frame_static_fresh, sctx_of_ctx.
  intros ps frame Hfresh x Hin.
  apply Hfresh. exact Hin.
Qed.

Lemma lookup_fn_in_name :
  forall fname fenv f_lookup,
    lookup_fn fname fenv = Some f_lookup ->
    In f_lookup fenv /\ fn_name f_lookup = fname.
Proof.
  intros fname fenv.
  induction fenv as [| f rest IH]; intros f_lookup Hlookup.
  - simpl in Hlookup. discriminate.
  - simpl in Hlookup.
    destruct (ident_eqb fname (fn_name f)) eqn:Hname.
    + inversion Hlookup; subst f_lookup.
      split.
      * left. reflexivity.
      * symmetry. apply ident_eqb_eq. exact Hname.
    + destruct (IH f_lookup Hlookup) as [Hin Hfn].
      split.
      * right. exact Hin.
      * exact Hfn.
Qed.

Lemma lookup_fn_checked_structural :
  forall env fname f_lookup,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    env_fns_checked_structural env ->
    checked_fn_env_structural env f_lookup.
Proof.
  intros env fname f_lookup Hlookup Henv_checked.
  destruct (lookup_fn_in_name fname (env_fns env) f_lookup)
    as [Hin_lookup _]; [exact Hlookup |].
  apply Henv_checked. exact Hin_lookup.
Qed.

Lemma lookup_fn_checked_structural_typed :
  forall env fname f_lookup,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    env_fns_checked_structural env ->
    typed_fn_env_structural env f_lookup.
Proof.
  intros env fname f_lookup Hlookup Henv_checked.
  eapply checked_fn_env_structural_typed.
  eapply lookup_fn_checked_structural; eassumption.
Qed.

Lemma lookup_fn_checked_structural_params_nodup :
  forall env fname f_lookup,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    env_fns_checked_structural env ->
    NoDup (ctx_names (params_ctx (fn_params f_lookup))).
Proof.
  intros env fname f_lookup Hlookup Henv_checked.
  eapply checked_fn_env_structural_params_nodup.
  eapply lookup_fn_checked_structural; eassumption.
Qed.

Lemma typed_place_type_direct_lookup :
  forall env Σ p T x path T_root st,
    typed_place_type_env_structural env Σ p T ->
    place_path p = Some (x, path) ->
    sctx_lookup x Σ = Some (T_root, st) ->
    type_lookup_path env T_root path = Some T.
Proof.
  intros env Σ p T x path T_root st Htyped.
  revert x path T_root st.
  induction Htyped; intros x0 path T_root st0 Hpath Hlookup.
  - simpl in Hpath.
    inversion Hpath; subst x0 path.
    rewrite H in Hlookup.
    inversion Hlookup; subst T_root st0.
    reflexivity.
  - simpl in Hpath. discriminate.
  - simpl in Hpath.
    destruct (place_path p) as [[root parent_path] |] eqn:Hparent; try discriminate.
    inversion Hpath; subst x0 path.
    rewrite type_lookup_path_app.
    rewrite (IHHtyped root parent_path T_root st0 eq_refl Hlookup).
    simpl.
    rewrite H, H0, H1.
    reflexivity.
Qed.

Lemma typed_place_direct_lookup :
  forall env Σ p T x path,
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x, path) ->
    exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      binding_available_b st path = true /\
      type_lookup_path env T_root path = Some T.
Proof.
  intros env Σ p T x path Htyped.
  induction Htyped; intros Hpath.
  - simpl in Hpath.
    inversion Hpath; subst x path.
    exists T, st. repeat split; assumption.
  - simpl in Hpath. discriminate.
  - rewrite H3 in Hpath.
    inversion Hpath; subst x0 path0.
    exists T_root, st.
    repeat split; try assumption.
    eapply typed_place_type_direct_lookup.
    + econstructor; eassumption.
    + exact H3.
    + exact H4.
  - rewrite H3 in Hpath. discriminate.
Qed.

Lemma eval_place_matches_place_path :
  forall s p x_eval path_eval x path,
    eval_place s p x_eval path_eval ->
    place_path p = Some (x, path) ->
    x_eval = x /\ path_eval = path.
Proof.
  intros s p x_eval path_eval x path Heval.
  revert x path.
  induction Heval; intros x0 path0 Hpath.
  - simpl in Hpath. inversion Hpath; subst. split; reflexivity.
  - simpl in Hpath.
    destruct (place_path p) as [[root root_path] |] eqn:Hparent; try discriminate.
    inversion Hpath; subst x0 path0.
    destruct (IHHeval root root_path eq_refl) as [Hx Hpath_eq].
    subst. split; reflexivity.
  - simpl in Hpath. discriminate.
Qed.

Lemma lookup_field_b_lookup_expr_field :
  forall name fields,
    lookup_field_b name fields = lookup_expr_field name fields.
Proof.
  intros name fields.
  unfold lookup_field_b.
  induction fields as [|[fname e] rest IH]; simpl.
  - reflexivity.
  - destruct (String.eqb name fname); [reflexivity | exact IH].
Qed.

Scheme eval_ind' := Induction for eval Sort Prop
with eval_args_ind' := Induction for eval_args Sort Prop
with eval_struct_fields_ind' := Induction for eval_struct_fields Sort Prop.

Combined Scheme eval_eval_args_eval_struct_fields_ind
  from eval_ind', eval_args_ind', eval_struct_fields_ind'.

Inductive provenance_ready_expr : expr -> Prop :=
  | ProvReady_Unit :
      provenance_ready_expr EUnit
  | ProvReady_Lit : forall lit,
      provenance_ready_expr (ELit lit)
  | ProvReady_Var : forall x,
      provenance_ready_expr (EVar x)
  | ProvReady_Fn : forall fname,
      provenance_ready_expr (EFn fname)
  | ProvReady_Place_Direct : forall p x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr (EPlace p)
  | ProvReady_Borrow : forall rk p x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr (EBorrow rk p)
  | ProvReady_Struct : forall sname lts args fields,
      provenance_ready_fields fields ->
      provenance_ready_expr (EStruct sname lts args fields)
  | ProvReady_Let : forall m x T e1 e2,
      provenance_ready_expr e1 ->
      provenance_ready_expr e2 ->
      provenance_ready_expr (ELet m x T e1 e2)
  | ProvReady_LetInfer : forall m x e1 e2,
      provenance_ready_expr e1 ->
      provenance_ready_expr e2 ->
      provenance_ready_expr (ELetInfer m x e1 e2)
  | ProvReady_Drop : forall e,
      provenance_ready_expr e ->
      provenance_ready_expr (EDrop e)
  | ProvReady_Assign : forall p e_new x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr e_new ->
      provenance_ready_expr (EAssign p e_new)
  | ProvReady_Replace : forall p e_new x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr e_new ->
      provenance_ready_expr (EReplace p e_new)
  | ProvReady_If : forall e1 e2 e3,
      provenance_ready_expr e1 ->
      provenance_ready_expr e2 ->
      provenance_ready_expr e3 ->
      provenance_ready_expr (EIf e1 e2 e3)
  | ProvReady_DerefBorrow : forall rk p x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr (EDeref (EBorrow rk p))
with provenance_ready_args : list expr -> Prop :=
  | ProvReadyArgs_Nil :
      provenance_ready_args []
  | ProvReadyArgs_Cons : forall e rest,
      provenance_ready_expr e ->
      provenance_ready_args rest ->
      provenance_ready_args (e :: rest)
with provenance_ready_fields : list (string * expr) -> Prop :=
  | ProvReadyFields_Nil :
      provenance_ready_fields []
  | ProvReadyFields_Cons : forall name e rest,
      provenance_ready_expr e ->
      provenance_ready_fields rest ->
      provenance_ready_fields ((name, e) :: rest).

Scheme preservation_ready_expr_ind' :=
  Induction for preservation_ready_expr Sort Prop
with preservation_ready_args_ind' :=
  Induction for preservation_ready_args Sort Prop
with preservation_ready_fields_ind' :=
  Induction for preservation_ready_fields Sort Prop.
Combined Scheme preservation_ready_mutind
  from preservation_ready_expr_ind', preservation_ready_args_ind',
       preservation_ready_fields_ind'.

Lemma preservation_ready_implies_provenance_ready_mutual :
  (forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e) /\
  (forall args,
    preservation_ready_args args ->
    provenance_ready_args args) /\
  (forall fields,
    preservation_ready_fields fields ->
    provenance_ready_fields fields).
Proof.
  apply preservation_ready_mutind;
    try solve [econstructor; eauto].
Qed.

Lemma preservation_ready_implies_provenance_ready :
  forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e.
Proof.
  exact (proj1 preservation_ready_implies_provenance_ready_mutual).
Qed.

Lemma preservation_ready_args_implies_provenance_ready :
  forall args,
    preservation_ready_args args ->
    provenance_ready_args args.
Proof.
  exact (proj1 (proj2 preservation_ready_implies_provenance_ready_mutual)).
Qed.

Lemma preservation_ready_fields_implies_provenance_ready :
  forall fields,
    preservation_ready_fields fields ->
    provenance_ready_fields fields.
Proof.
  exact (proj2 (proj2 preservation_ready_implies_provenance_ready_mutual)).
Qed.

Lemma alpha_rename_provenance_ready_expr :
  forall ρ used e er used',
    alpha_rename_expr ρ used e = (er, used') ->
    provenance_ready_expr e ->
    provenance_ready_expr er
with alpha_rename_provenance_ready_args :
  forall ρ used args argsr used',
    (fix go (used0 : list ident) (args0 : list expr)
        {struct args0} : list expr * list ident :=
       match args0 with
       | [] => ([], used0)
       | arg :: rest =>
           let (arg', used1) := alpha_rename_expr ρ used0 arg in
           let (rest', used2) := go used1 rest in
           (arg' :: rest', used2)
       end) used args = (argsr, used') ->
    provenance_ready_args args ->
    provenance_ready_args argsr
with alpha_rename_provenance_ready_fields :
  forall ρ used fields fieldsr used',
    (fix go (used0 : list ident) (fields0 : list (string * expr))
        {struct fields0} : list (string * expr) * list ident :=
       match fields0 with
       | [] => ([], used0)
       | (fname, e) :: rest =>
           let (e', used1) := alpha_rename_expr ρ used0 e in
           let (rest', used2) := go used1 rest in
           ((fname, e') :: rest', used2)
       end) used fields = (fieldsr, used') ->
    provenance_ready_fields fields ->
    provenance_ready_fields fieldsr.
Proof.
  - intros ρ used e er used' Hrename Hready.
    destruct Hready; simpl in Hrename.
    + inversion Hrename; subst. constructor.
    + inversion Hrename; subst. constructor.
    + inversion Hrename; subst. constructor.
    + inversion Hrename; subst. constructor.
    + inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_Place_Direct. exact Hpath.
    + inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_Borrow. exact Hpath.
    + destruct
        ((fix go (used0 : list ident) (fields0 : list (string * expr))
             {struct fields0} : list (string * expr) * list ident :=
            match fields0 with
            | [] => ([], used0)
            | (fname, e) :: rest =>
                let (e', used1) := alpha_rename_expr ρ used0 e in
                let (rest', used2) := go used1 rest in
                ((fname, e') :: rest', used2)
            end) used fields)
        as [fieldsr used_fields] eqn:Hfields.
      inversion Hrename; subst.
      apply ProvReady_Struct.
      eapply alpha_rename_provenance_ready_fields; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: ρ)
        (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
          x :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      inversion Hrename; subst.
      apply ProvReady_Let.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: ρ)
        (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
          x :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      inversion Hrename; subst.
      apply ProvReady_LetInfer.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
      inversion Hrename; subst.
      apply ProvReady_Drop.
      eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_Assign.
      * exact Hpath.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_Replace.
      * exact Hpath.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
      inversion Hrename; subst.
      apply ProvReady_If.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + simpl in Hrename.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_DerefBorrow. exact Hpath.
  - intros ρ used args argsr used' Hrename Hready.
    destruct Hready as [| arg rest Harg Hrest]; simpl in Hrename.
    + inversion Hrename; subst. constructor.
    + destruct (alpha_rename_expr ρ used arg) as [ar used1] eqn:Harg_ren.
      destruct
        ((fix go (used0 : list ident) (args0 : list expr)
             {struct args0} : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg0 :: rest0 =>
                let (arg', used2) := alpha_rename_expr ρ used0 arg0 in
                let (rest', used3) := go used2 rest0 in
                (arg' :: rest', used3)
            end) used1 rest)
        as [restr used2] eqn:Hrest_ren.
      inversion Hrename; subst.
      constructor.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_args; eauto.
  - intros ρ used fields fieldsr used' Hrename Hready.
    destruct Hready as [| name e rest He Hrest]; simpl in Hrename.
    + inversion Hrename; subst. constructor.
    + destruct (alpha_rename_expr ρ used e) as [er used1] eqn:He_ren.
      destruct
        ((fix go (used0 : list ident) (fields0 : list (string * expr))
             {struct fields0} : list (string * expr) * list ident :=
            match fields0 with
            | [] => ([], used0)
            | (fname, e0) :: rest0 =>
                let (e', used2) := alpha_rename_expr ρ used0 e0 in
                let (rest', used3) := go used2 rest0 in
                ((fname, e') :: rest', used3)
            end) used1 rest)
        as [restr used2] eqn:Hrest_ren.
      inversion Hrename; subst.
      constructor.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_fields; eauto.
Qed.

Lemma alpha_rename_fn_def_provenance_ready_body :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    provenance_ready_expr (fn_body f) ->
    provenance_ready_expr (fn_body fr).
Proof.
  intros used f fr used' Hrename Hready.
  unfold alpha_rename_fn_def in Hrename.
  destruct (alpha_rename_params [] (param_names (fn_params f) ++
             param_names (fn_captures f) ++
             free_vars_expr (fn_body f) ++ used) (fn_params f))
    as [[paramsr ρ] used1] eqn:Hparams.
  destruct (alpha_rename_expr ρ used1 (fn_body f)) as [bodyr used2]
    eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply alpha_rename_provenance_ready_expr; eauto.
Qed.

Lemma provenance_ready_fields_lookup :
  forall fields name e,
    provenance_ready_fields fields ->
    lookup_expr_field name fields = Some e ->
    provenance_ready_expr e.
Proof.
  intros fields name e Hready.
  induction Hready as [| fname field_expr rest Hexpr _ IH];
    simpl; intros Hlookup.
  - discriminate.
  - destruct (String.eqb name fname) eqn:Hname.
    + inversion Hlookup; subst. exact Hexpr.
    + apply IH. exact Hlookup.
Qed.

Lemma roots_exclude_root_sets_union :
  forall x roots_list,
    Forall (roots_exclude x) roots_list ->
    roots_exclude x (root_sets_union roots_list).
Proof.
  intros x roots_list Hexclude.
  induction Hexclude as [| roots roots_list Hroot Hrest IH]; simpl.
  - unfold roots_exclude. intros Hin. contradiction.
  - apply roots_exclude_union; assumption.
Qed.

Lemma roots_exclude_root_sets_union_app_repeat_nil :
  forall x roots_list n,
    roots_exclude x (root_sets_union roots_list) ->
    roots_exclude x (root_sets_union (roots_list ++ repeat [] n)).
Proof.
  intros x roots_list n Hexclude.
  unfold roots_exclude in *.
  intros Hin.
  induction roots_list as [| roots rest IH] in n, Hexclude, Hin |- *.
  - simpl in Hin.
    induction n as [| n IHn]; simpl in Hin.
    + exact Hin.
    + apply IHn. exact Hin.
  - simpl in *.
    apply root_set_union_in_inv in Hin.
    destruct Hin as [Hin | Hin].
    + apply Hexclude. apply root_set_union_in_l. exact Hin.
    + apply IH with (n := n).
      * intros Hrest.
        apply Hexclude. apply root_set_union_in_r. exact Hrest.
      * exact Hin.
Qed.

Lemma value_roots_exclude_root_forall2 :
  forall roots_list values x,
    Forall2 value_roots_within roots_list values ->
    Forall (roots_exclude x) roots_list ->
    Forall (value_refs_exclude_root x) values.
Proof.
  intros roots_list values x Hroots Hexclude.
  induction Hroots as [| roots v roots_list values Hroot Hroots IH];
    inversion Hexclude; subst.
  - constructor.
  - constructor.
    + eapply value_roots_exclude_root; eassumption.
    + apply IH. assumption.
Qed.

Lemma store_names_in_store_entry :
  forall s se,
    In se s ->
    In (se_name se) (store_names s).
Proof.
  induction s as [| se_head rest IH]; intros se Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst se_head. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma store_roots_exclude_root :
  forall R s root,
    store_roots_within R s ->
    root_env_excludes root R ->
    (forall se, In se s -> se_name se <> root) ->
    store_refs_exclude_root root s.
Proof.
  intros R s root Hwithin Hexclude Hnames.
  exact (proj1 (proj2 (proj2 value_roots_within_excludes))
    R s Hwithin root Hexclude Hnames).
Qed.

Definition root_env_covers_sctx (Σ : sctx) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names Σ) ->
    exists roots, root_env_lookup x R = Some roots.

Definition root_env_covers_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    exists roots, root_env_lookup x R = Some roots.

Lemma root_env_covers_sctx_equiv :
  forall Σ R R',
    root_env_equiv R R' ->
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ R'.
Proof.
  unfold root_env_covers_sctx.
  intros Σ R R' Heq Hcovers x Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  exists roots'. exact Hlookup'.
Qed.

Lemma root_env_covers_params_equiv :
  forall ps R R',
    root_env_equiv R R' ->
    root_env_covers_params ps R ->
    root_env_covers_params ps R'.
Proof.
  unfold root_env_covers_params.
  intros ps R R' Heq Hcovers x Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
    as [roots' [Hlookup' _]].
  exists roots'. exact Hlookup'.
Qed.

Lemma root_env_covers_params_app_inv_l :
  forall ps caps R,
    root_env_covers_params (ps ++ caps) R ->
    root_env_covers_params ps R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers x Hin.
  apply Hcovers.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_covers_params_app_inv_r :
  forall ps caps R,
    root_env_covers_params (ps ++ caps) R ->
    root_env_covers_params caps R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers x Hin.
  apply Hcovers.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_covers_params_app :
  forall ps caps R,
    root_env_covers_params ps R ->
    root_env_covers_params caps R ->
    root_env_covers_params (ps ++ caps) R.
Proof.
  unfold root_env_covers_params.
  intros ps caps R Hcovers_ps Hcovers_caps x Hin.
  rewrite params_ctx_app, ctx_names_app in Hin.
  apply in_app_or in Hin as [Hin | Hin].
  - apply Hcovers_ps. exact Hin.
  - apply Hcovers_caps. exact Hin.
Qed.

Lemma captured_params_store_typed_empty_root_env_covers :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    root_env_covers_params caps (empty_root_env_for_store captured).
Proof.
  intros env captured caps Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  unfold root_env_covers_params.
  intros x Hin.
  exists [].
  apply root_env_lookup_empty_root_env_for_store.
  rewrite (store_names_store_param_prefix caps captured [] Hprefix).
  rewrite app_nil_r. exact Hin.
Qed.

Lemma empty_root_env_for_captured_params_equiv :
  forall env captured caps,
    captured_params_store_typed env captured caps ->
    root_env_equiv (empty_root_env_for_store captured)
      (root_env_add_params_roots caps (repeat [] (List.length caps)) []).
Proof.
  intros env captured caps Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  rewrite (empty_root_env_for_store_param_prefix caps captured [] Hprefix).
  simpl. apply root_env_equiv_refl.
Qed.

Lemma captured_params_store_typed_empty_root_env_app_covers :
  forall env captured caps R_tail,
    captured_params_store_typed env captured caps ->
    root_env_covers_params caps
      (empty_root_env_for_store captured ++ R_tail).
Proof.
  intros env captured caps R_tail Htyped.
  unfold root_env_covers_params.
  intros x Hin.
  destruct (captured_params_store_typed_empty_root_env_covers
              env captured caps Htyped x Hin) as [roots Hlookup].
  exists roots. eapply root_env_lookup_app_left. exact Hlookup.
Qed.

Definition roots_exclude_params (ps : list param) (roots : root_set) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    roots_exclude x roots.

Definition root_env_excludes_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    root_env_excludes x R.

Lemma roots_exclude_params_app_inv_l :
  forall ps caps roots,
    roots_exclude_params (ps ++ caps) roots ->
    roots_exclude_params ps roots.
Proof.
  unfold roots_exclude_params.
  intros ps caps roots Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma roots_exclude_params_app_inv_r :
  forall ps caps roots,
    roots_exclude_params (ps ++ caps) roots ->
    roots_exclude_params caps roots.
Proof.
  unfold roots_exclude_params.
  intros ps caps roots Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma root_env_excludes_params_app_inv_l :
  forall ps caps R,
    root_env_excludes_params (ps ++ caps) R ->
    root_env_excludes_params ps R.
Proof.
  unfold root_env_excludes_params.
  intros ps caps R Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. left. exact Hin.
Qed.

Lemma root_env_excludes_params_app_inv_r :
  forall ps caps R,
    root_env_excludes_params (ps ++ caps) R ->
    root_env_excludes_params caps R.
Proof.
  unfold root_env_excludes_params.
  intros ps caps R Hexcl x Hin.
  apply Hexcl.
  rewrite params_ctx_app, ctx_names_app.
  apply in_or_app. right. exact Hin.
Qed.

Lemma empty_root_env_for_store_params_fresh_lookup_none :
  forall ps s x,
    params_fresh_in_store ps s ->
    In x (ctx_names (params_ctx ps)) ->
    root_env_lookup x (empty_root_env_for_store s) = None.
Proof.
  intros ps s x Hfresh Hin.
  apply root_env_lookup_empty_root_env_for_store_none.
  exact (Hfresh x Hin).
Qed.

Lemma root_env_excludes_params_empty_root_env_for_store :
  forall ps s,
    root_env_excludes_params ps (empty_root_env_for_store s).
Proof.
  unfold root_env_excludes_params, root_env_excludes, roots_exclude.
  intros ps s x _ y roots Hlookup _ Hin.
  assert (Hy_names : In y (store_names s)).
  { rewrite <- root_env_names_empty_root_env_for_store.
    eapply root_env_lookup_some_in_names. exact Hlookup. }
  rewrite root_env_lookup_empty_root_env_for_store in Hlookup
    by exact Hy_names.
  inversion Hlookup; subst roots.
  contradiction.
Qed.

Lemma root_set_no_store_of_sctx_named_excludes_params :
  forall ps Σ roots,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    root_set_sctx_roots_named roots Σ ->
    roots_exclude_params ps roots ->
    root_set_no_store roots.
Proof.
  unfold root_set_no_store, roots_exclude_params, roots_exclude.
  intros ps Σ roots Hsame Hnamed Hexclude z Hin.
  assert (Hz_ctx : In z (ctx_names Σ)).
  { apply Hnamed. exact Hin. }
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha (params_ctx ps) Σ Hsame).
    reflexivity. }
  rewrite Hnames in Hz_ctx.
  eapply Hexclude; eassumption.
Qed.

Lemma roots_exclude_params_rename :
  forall rho ps psr roots rootsr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    (forall x y,
      In x (ctx_names (params_ctx ps)) ->
      In (RStore y) roots ->
      y <> x ->
      lookup_rename y rho <> lookup_rename x rho) ->
    roots_exclude_params ps roots ->
    roots_exclude_params psr rootsr.
Proof.
  unfold roots_exclude_params.
  intros rho ps psr roots rootsr Halpha Hnodup Heq Hnocoll Hexcl xr Hinr.
  destruct (ctx_alpha_renamed_name_preimage rho
              (sctx_of_ctx (params_ctx ps))
              (sctx_of_ctx (params_ctx psr)) xr Halpha Hnodup Hinr)
    as [x [Hinx Hlookup]].
  subst xr.
  eapply roots_exclude_equiv.
  - apply root_set_equiv_sym. exact Heq.
  - apply roots_exclude_rename.
    + intros y Hy Hyx. eapply Hnocoll; eassumption.
    + apply Hexcl. exact Hinx.
Qed.

Lemma root_env_excludes_params_rename :
  forall rho ps psr R Rr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    (forall x y,
      In x (ctx_names (params_ctx ps)) ->
      In y (root_env_names R) ->
      y <> x ->
      lookup_rename y rho <> lookup_rename x rho) ->
    (forall x y roots z,
      In x (ctx_names (params_ctx ps)) ->
      root_env_lookup y R = Some roots ->
      y <> x ->
      In (RStore z) roots ->
      z <> x ->
      lookup_rename z rho <> lookup_rename x rho) ->
    root_env_excludes_params ps R ->
    root_env_excludes_params psr Rr.
Proof.
  unfold root_env_excludes_params.
  intros rho ps psr R Rr Halpha Hnodup Hrn Heq Hkey_nocoll Hroot_nocoll
    Hexcl xr Hinr.
  destruct (ctx_alpha_renamed_name_preimage rho
              (sctx_of_ctx (params_ctx ps))
              (sctx_of_ctx (params_ctx psr)) xr Halpha Hnodup Hinr)
    as [x [Hinx Hlookup]].
  subst xr.
  eapply root_env_excludes_equiv.
  - apply root_env_equiv_sym. exact Heq.
  - eapply root_env_excludes_rename.
    + exact Hrn.
    + intros y Hy Hyx. eapply Hkey_nocoll; eassumption.
    + intros y roots z Hlookup_y Hyx Hin_z Hzx.
      eapply Hroot_nocoll; eassumption.
    + apply Hexcl. exact Hinx.
Qed.

Lemma roots_exclude_params_instantiate :
  forall ps rho roots,
    roots_exclude_params ps roots ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_subst_images_exclude x rho) ->
    roots_exclude_params ps (root_set_instantiate rho roots).
Proof.
  unfold roots_exclude_params.
  intros ps rho roots Hexcl Himages x Hin.
  apply root_set_instantiate_excludes_images.
  - apply Hexcl. exact Hin.
  - apply Himages. exact Hin.
Qed.

Lemma root_env_excludes_params_instantiate :
  forall ps rho R,
    root_env_excludes_params ps R ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      root_subst_images_exclude x rho) ->
    root_env_excludes_params ps (root_env_instantiate rho R).
Proof.
  unfold root_env_excludes_params.
  intros ps rho R Hexcl Himages x Hin.
  apply root_env_instantiate_excludes_images.
  - apply Hexcl. exact Hin.
  - apply Himages. exact Hin.
Qed.

Lemma root_env_excludes_params_app :
  forall ps R1 R2,
    root_env_excludes_params ps R1 ->
    root_env_excludes_params ps R2 ->
    root_env_excludes_params ps (R1 ++ R2).
Proof.
  unfold root_env_excludes_params.
  intros ps R1 R2 Hexcl1 Hexcl2 x Hin.
  apply root_env_excludes_app.
  - apply Hexcl1. exact Hin.
  - apply Hexcl2. exact Hin.
Qed.

Lemma roots_exclude_params_equiv :
  forall ps roots roots',
    root_set_equiv roots roots' ->
    roots_exclude_params ps roots ->
    roots_exclude_params ps roots'.
Proof.
  unfold roots_exclude_params.
  intros ps roots roots' Heq Hexcl x Hin.
  exact (roots_exclude_equiv x roots roots' Heq (Hexcl x Hin)).
Qed.

Lemma root_env_excludes_params_equiv :
  forall ps R R',
    root_env_equiv R R' ->
    root_env_excludes_params ps R ->
    root_env_excludes_params ps R'.
Proof.
  unfold root_env_excludes_params.
  intros ps R R' Heq Hexcl x Hin.
  exact (root_env_excludes_equiv x R R' Heq (Hexcl x Hin)).
Qed.

Lemma roots_exclude_params_rename_from_typed_support :
  forall rho ps psr Σ Σr roots rootsr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    ctx_alpha rho Σ Σr ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_set_sctx_roots_named roots Σ ->
    roots_exclude_params ps roots ->
    roots_exclude_params psr rootsr.
Proof.
  intros rho ps psr Σ Σr roots rootsr Halpha_params Halpha_out
    Hsame Hnodup Heq Hroots_named Hexcl.
  eapply roots_exclude_params_rename; try eassumption.
  intros x y Hx Hy Hyx.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_out : NoDup (ctx_names Σ)).
  { rewrite Hnames. exact Hnodup. }
  assert (Hnodup_ren : NoDup (ctx_names Σr)).
  { eapply ctx_alpha_nodup_names; eassumption. }
  eapply ctx_alpha_no_collision_on with (Σ := Σ) (Σr := Σr).
  - exact Halpha_out.
  - exact Hnodup_out.
  - exact Hnodup_ren.
  - rewrite Hnames. exact Hx.
  - apply Hroots_named. exact Hy.
  - exact Hyx.
Qed.

Lemma root_env_excludes_params_rename_from_typed_support :
  forall rho ps psr Σ Σr R Rr,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    ctx_alpha rho Σ Σr ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow R ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_env_sctx_keys_named R Σ ->
    root_env_sctx_roots_named R Σ ->
    root_env_excludes_params ps R ->
    root_env_excludes_params psr Rr.
Proof.
  intros rho ps psr Σ Σr R Rr Halpha_params Halpha_out Hsame Hnodup
    Hrn Heq Hkeys Hroots Hexcl.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_out : NoDup (ctx_names Σ)).
  { rewrite Hnames. exact Hnodup. }
  assert (Hnodup_ren : NoDup (ctx_names Σr)).
  { eapply ctx_alpha_nodup_names; eassumption. }
  assert (Hnocoll : rename_no_collision_on rho (ctx_names Σ)).
  { eapply ctx_alpha_no_collision_on; eassumption. }
  eapply root_env_excludes_params_rename; try eassumption.
  - intros x y Hx Hy Hyx.
    eapply Hnocoll.
    + rewrite Hnames. exact Hx.
    + apply Hkeys. exact Hy.
    + exact Hyx.
  - intros x y roots z Hx Hlookup Hyx Hz Hzx.
    eapply Hnocoll.
    + rewrite Hnames. exact Hx.
    + eapply Hroots; eassumption.
    + exact Hzx.
Qed.

Lemma rename_no_collision_on_root_env_names_from_typed_support :
  forall rho ps psr Σ R,
    ctx_alpha rho
      (sctx_of_ctx (params_ctx ps))
      (sctx_of_ctx (params_ctx psr)) ->
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_sctx_keys_named R Σ ->
    rename_no_collision_on rho (root_env_names R).
Proof.
  unfold rename_no_collision_on, rename_no_collision_for.
  intros rho ps psr Σ R Halpha Hsame Hnodup Hkeys x Hx y Hy Hyx.
  assert (Hnames : ctx_names Σ = ctx_names (params_ctx ps)).
  { unfold sctx_of_ctx in Hsame.
    rewrite (sctx_same_bindings_names_alpha
      (params_ctx ps) Σ Hsame). reflexivity. }
  assert (Hnodup_ren :
    NoDup (ctx_names (sctx_of_ctx (params_ctx psr)))).
  { eapply ctx_alpha_nodup_names.
    - exact Halpha.
    - unfold sctx_of_ctx. exact Hnodup. }
  eapply ctx_alpha_no_collision_on.
  - exact Halpha.
  - unfold sctx_of_ctx. exact Hnodup.
  - exact Hnodup_ren.
  - unfold sctx_of_ctx. rewrite <- Hnames. apply Hkeys. exact Hx.
  - unfold sctx_of_ctx. rewrite <- Hnames. apply Hkeys. exact Hy.
  - exact Hyx.
Qed.

Lemma root_env_store_roots_named_excludes_params :
  forall ps R s,
    root_env_store_roots_named R s ->
    params_fresh_in_store ps s ->
    root_env_excludes_params ps R.
Proof.
  unfold root_env_store_roots_named, params_fresh_in_store,
    root_env_excludes_params, root_env_excludes, roots_exclude.
  intros ps R s Hnamed Hfresh x Hparam y roots Hlookup Hyx Hin.
  apply (Hfresh x Hparam).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_roots_named_excludes_name :
  forall R s x,
    root_env_store_roots_named R s ->
    ~ In x (store_names s) ->
    root_env_excludes x R.
Proof.
  unfold root_env_store_roots_named, root_env_excludes, roots_exclude.
  intros R s x Hnamed Hfresh y roots Hlookup Hyx Hin.
  apply Hfresh.
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_lookup_excludes_name :
  forall R s x,
    root_env_store_keys_named R s ->
    ~ In x (store_names s) ->
    root_env_lookup x R = None.
Proof.
  intros R s x Hnamed Hfresh.
  destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
    try reflexivity.
  exfalso. apply Hfresh.
  eapply root_env_keys_named_lookup; eassumption.
Qed.

Lemma root_set_store_roots_named_excludes_params :
  forall ps roots s,
    root_set_store_roots_named roots s ->
    params_fresh_in_store ps s ->
    roots_exclude_params ps roots.
Proof.
  unfold root_set_store_roots_named, params_fresh_in_store,
    roots_exclude_params, roots_exclude.
  intros ps roots s Hnamed Hfresh x Hparam Hin.
  apply (Hfresh x Hparam).
  apply Hnamed. exact Hin.
Qed.

Lemma root_set_store_roots_named_excludes_name :
  forall roots s x,
    root_set_store_roots_named roots s ->
    ~ In x (store_names s) ->
    roots_exclude x roots.
Proof.
  unfold root_set_store_roots_named, roots_exclude.
  intros roots s x Hnamed Hfresh Hin.
  apply Hfresh.
  apply Hnamed. exact Hin.
Qed.

Lemma root_subst_of_params_images_exclude_names_from_store_roots :
  forall ps arg_roots names s,
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots ->
    Forall (fun x => ~ In x (store_names s)) names ->
    root_subst_images_exclude_names names
      (root_subst_of_params ps arg_roots).
Proof.
  intros ps arg_roots names s Hnamed Hfresh.
  induction Hfresh as [| x names Hx Hfresh IH].
  - constructor.
  - constructor.
    + apply root_subst_of_params_images_exclude.
      eapply Forall_impl; [| exact Hnamed].
      intros roots Hroot.
      apply (root_set_store_roots_named_excludes_name roots s x).
      * exact Hroot.
      * exact Hx.
    + exact IH.
Qed.

Lemma alpha_rename_fn_def_body_root_subst_images_exclude_names_from_store_roots :
  forall f fr used' arg_roots s,
    alpha_rename_fn_def (store_names s) f = (fr, used') ->
    Forall (fun roots => root_set_store_roots_named roots s) arg_roots ->
    root_subst_images_exclude_names
      (expr_local_store_names (fn_body fr))
      (root_subst_of_params (fn_params fr) arg_roots).
Proof.
  intros f fr used' arg_roots s Hrename Hnamed.
  eapply root_subst_of_params_images_exclude_names_from_store_roots.
  - exact Hnamed.
  - eapply alpha_rename_fn_def_body_local_store_names_fresh_used.
    exact Hrename.
Qed.

Lemma root_sets_store_roots_named_excludes_params :
  forall ps roots_list s,
    Forall (fun roots => root_set_store_roots_named roots s) roots_list ->
    params_fresh_in_store ps s ->
    Forall (roots_exclude_params ps) roots_list.
Proof.
  intros ps roots_list s Hnamed Hfresh.
  induction Hnamed as [| roots roots_list Hroot Hnamed IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_excludes_params; eassumption.
    + exact IH.
Qed.

Definition value_refs_exclude_params (ps : list param) (v : value) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    value_refs_exclude_root x v.

Definition store_refs_exclude_params (ps : list param) (s : store) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    store_refs_exclude_root x s.

Definition roots_exclude_params_b (ps : list param) (roots : root_set) : bool :=
  forallb (fun x => roots_exclude_b x roots) (ctx_names (params_ctx ps)).

Definition root_env_excludes_params_b (ps : list param) (R : root_env) : bool :=
  forallb (fun x => root_env_excludes_b x R) (ctx_names (params_ctx ps)).

Lemma roots_exclude_b_sound_ts :
  forall x roots,
    roots_exclude_b x roots = true ->
    roots_exclude x roots.
Proof.
  unfold roots_exclude_b, roots_exclude.
  intros x roots Hexclude Hin.
  apply negb_true_iff in Hexclude.
  assert (existsb (root_atom_eqb (RStore x)) roots = true) as Hexists.
  { apply existsb_exists.
    exists (RStore x). split.
    - exact Hin.
    - apply root_atom_eqb_refl. }
  rewrite Hexists in Hexclude. discriminate.
Qed.

Lemma root_env_excludes_b_sound_ts :
  forall x R,
    root_env_excludes_b x R = true ->
    root_env_excludes x R.
Proof.
  unfold root_env_excludes.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros Hexclude z roots
    Hlookup Hneq; simpl in *; try discriminate.
  apply andb_true_iff in Hexclude as [Hhead Hrest].
  destruct (ident_eqb z y) eqn:Hz.
  - inversion Hlookup; subst roots_y; clear Hlookup.
    destruct (ident_eqb x y) eqn:Hxy.
    + apply ident_eqb_eq in Hxy. subst y.
      apply ident_eqb_eq in Hz. subst z.
      contradiction Hneq. reflexivity.
    + eapply roots_exclude_b_sound_ts. exact Hhead.
  - eapply IH; eassumption.
Qed.

Lemma roots_exclude_params_b_sound :
  forall ps roots,
    roots_exclude_params_b ps roots = true ->
    roots_exclude_params ps roots.
Proof.
  assert (Hnames :
    forall names roots,
      forallb (fun x => roots_exclude_b x roots) names = true ->
      forall x, In x names -> roots_exclude x roots).
  { induction names as [| y ys IH]; intros roots Hparams x Hin;
      simpl in *; try contradiction.
    apply andb_true_iff in Hparams as [Hhead Htail].
    destruct Hin as [Hin | Hin].
    - subst x. eapply roots_exclude_b_sound_ts. exact Hhead.
    - eapply IH; eassumption. }
  unfold roots_exclude_params_b, roots_exclude_params.
  intros ps roots Hparams x Hin.
  eapply Hnames; eassumption.
Qed.

Lemma root_env_excludes_params_b_sound :
  forall ps R,
    root_env_excludes_params_b ps R = true ->
    root_env_excludes_params ps R.
Proof.
  assert (Hnames :
    forall names R,
      forallb (fun x => root_env_excludes_b x R) names = true ->
      forall x, In x names -> root_env_excludes x R).
  { induction names as [| y ys IH]; intros R Hparams x Hin;
      simpl in *; try contradiction.
    apply andb_true_iff in Hparams as [Hhead Htail].
    destruct Hin as [Hin | Hin].
    - subst x. eapply root_env_excludes_b_sound_ts. exact Hhead.
    - eapply IH; eassumption. }
  unfold root_env_excludes_params_b, root_env_excludes_params.
  intros ps R Hparams x Hin.
  eapply Hnames; eassumption.
Qed.

Lemma root_env_covers_sctx_update :
  forall Σ R x roots,
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ (root_env_update x roots R).
Proof.
  intros Σ R x roots Hcovers y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots.
    eapply root_env_lookup_update_eq. exact Hlookup.
  - exists roots_old.
    rewrite root_env_lookup_update_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_sctx_add :
  forall Σ R x roots,
    root_env_covers_sctx Σ R ->
    root_env_covers_sctx Σ (root_env_add x roots R).
Proof.
  intros Σ R x roots Hcovers y Hy.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots. apply root_env_lookup_add_eq.
  - destruct (Hcovers y Hy) as [roots_old Hlookup].
    exists roots_old.
    rewrite root_env_lookup_add_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_sctx_remove_non_name :
  forall Σ R x,
    root_env_covers_sctx Σ R ->
    ~ In x (ctx_names Σ) ->
    root_env_covers_sctx Σ (root_env_remove x R).
Proof.
  intros Σ R x Hcovers Hnotin y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  exists roots_old.
  rewrite root_env_lookup_remove_neq.
  - exact Hlookup.
  - intros Heq. subst y. contradiction.
Qed.

Lemma root_env_covers_sctx_lookup_none_not_in :
  forall Σ R x,
    root_env_covers_sctx Σ R ->
    root_env_lookup x R = None ->
    ~ In x (ctx_names Σ).
Proof.
  intros Σ R x Hcovers Hlookup_none Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  rewrite Hlookup_none in Hlookup. discriminate.
Qed.

Lemma root_env_covers_params_sctx_of_params :
  forall ps R,
    root_env_covers_params ps R ->
    root_env_covers_sctx (sctx_of_ctx (params_ctx ps)) R.
Proof.
  unfold root_env_covers_params, root_env_covers_sctx, sctx_of_ctx.
  intros ps R Hcovers x Hin.
  apply Hcovers. exact Hin.
Qed.

Lemma root_env_covers_params_update :
  forall ps R x roots,
    root_env_covers_params ps R ->
    root_env_covers_params ps (root_env_update x roots R).
Proof.
  intros ps R x roots Hcovers y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots.
    eapply root_env_lookup_update_eq. exact Hlookup.
  - exists roots_old.
    rewrite root_env_lookup_update_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_params_add :
  forall ps R x roots,
    root_env_covers_params ps R ->
    root_env_covers_params ps (root_env_add x roots R).
Proof.
  intros ps R x roots Hcovers y Hy.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    exists roots. apply root_env_lookup_add_eq.
  - destruct (Hcovers y Hy) as [roots_old Hlookup].
    exists roots_old.
    rewrite root_env_lookup_add_neq.
    + exact Hlookup.
    + apply ident_eqb_neq. exact Heq.
Qed.

Lemma root_env_covers_params_remove_non_param :
  forall ps R x,
    root_env_covers_params ps R ->
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_covers_params ps (root_env_remove x R).
Proof.
  intros ps R x Hcovers Hnotin y Hy.
  destruct (Hcovers y Hy) as [roots_old Hlookup].
  exists roots_old.
  rewrite root_env_lookup_remove_neq.
  - exact Hlookup.
  - intros Heq. subst y. contradiction.
Qed.

Lemma root_env_covers_params_lookup_none_not_in :
  forall ps R x,
    root_env_covers_params ps R ->
    root_env_lookup x R = None ->
    ~ In x (ctx_names (params_ctx ps)).
Proof.
  intros ps R x Hcovers Hlookup_none Hin.
  destruct (Hcovers x Hin) as [roots Hlookup].
  rewrite Hlookup_none in Hlookup. discriminate.
Qed.

Lemma root_env_covers_params_add_params_roots :
  forall ps roots_list R,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    root_env_covers_params ps (root_env_add_params_roots ps roots_list R).
Proof.
  intros ps roots_list R Hnodup Hlen x Hin.
  eapply root_env_add_params_roots_covers_lookup; eassumption.
Qed.

Lemma call_param_root_env_covers_params :
  forall ps roots_list R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length roots_list = List.length ps ->
    root_env_covers_params ps (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hnodup Hlen.
  unfold call_param_root_env.
  apply root_env_covers_params_add_params_roots.
  - exact Hnodup.
  - exact Hlen.
Qed.

Lemma captured_call_runtime_root_env_covers_params_captures :
  forall env captured caps ps arg_roots R_tail,
    NoDup (ctx_names (params_ctx ps)) ->
    List.length arg_roots = List.length ps ->
    captured_params_store_typed env captured caps ->
    root_env_covers_params (ps ++ caps)
      (call_param_root_env ps arg_roots
        (empty_root_env_for_store captured ++ R_tail)).
Proof.
  intros env captured caps ps arg_roots R_tail Hnodup Hlen Hcaptured.
  apply root_env_covers_params_app.
  - apply call_param_root_env_covers_params; assumption.
  - unfold root_env_covers_params.
    intros x Hin_caps.
    assert (Hident_dec : forall a b : ident, {a = b} + {a <> b}).
    { decide equality; [apply Nat.eq_dec | apply string_dec]. }
    destruct (in_dec Hident_dec x (ctx_names (params_ctx ps)))
      as [Hin_ps | Hnotin_ps].
    + apply call_param_root_env_covers_params; assumption.
    + destruct (captured_params_store_typed_empty_root_env_app_covers
                  env captured caps R_tail Hcaptured x Hin_caps)
        as [roots Hlookup_tail].
      exists roots.
      unfold call_param_root_env.
      rewrite root_env_add_params_roots_lookup_not_in by exact Hnotin_ps.
      rewrite root_env_lookup_remove_params_not_in by exact Hnotin_ps.
      exact Hlookup_tail.
Qed.

Lemma root_env_excludes_remove_no_shadow :
  forall x y R,
    root_env_no_shadow R ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_remove y R).
Proof.
  unfold root_env_excludes.
  intros x y R Hrn Hexcl z roots Hlookup Hneq.
  destruct (ident_eqb z y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst z.
    rewrite root_env_lookup_remove_eq_no_shadow in Hlookup; try discriminate.
    exact Hrn.
  - eapply Hexcl.
    + rewrite (root_env_lookup_remove_neq y z R) in Hlookup.
      * exact Hlookup.
      * intros Hz. subst z. rewrite ident_eqb_refl in Heq. discriminate.
    + exact Hneq.
Qed.

Lemma root_env_remove_params_preserves_excludes :
  forall ps x R,
    root_env_no_shadow R ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_remove_params ps R).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros x R Hrn Hexcl; simpl.
  - exact Hexcl.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + apply root_env_excludes_remove_no_shadow; assumption.
Qed.

Lemma root_env_remove_params_preserves_excludes_params :
  forall remove_ps protected_ps R,
    root_env_no_shadow R ->
    root_env_excludes_params protected_ps R ->
    root_env_excludes_params protected_ps
      (root_env_remove_params remove_ps R).
Proof.
  intros remove_ps.
  induction remove_ps as [| p remove_ps IH];
    intros protected_ps R Hrn Hexcl; simpl.
  - exact Hexcl.
  - apply IH.
    + apply root_env_no_shadow_remove. exact Hrn.
    + unfold root_env_excludes_params in *.
      intros x Hin.
      apply root_env_excludes_remove_no_shadow.
      * exact Hrn.
      * apply Hexcl. exact Hin.
Qed.

Lemma root_env_remove_params_excludes_params :
  forall ps R_tail,
    root_env_no_shadow R_tail ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps (root_env_remove_params ps R_tail).
Proof.
  intros ps R_tail Hrn Hexcl.
  eapply root_env_remove_params_preserves_excludes_params; eassumption.
Qed.

Lemma captured_call_runtime_args_tail_excludes_binding_params :
  forall ps caps R_args s_args,
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    params_fresh_in_store (ps ++ caps) s_args ->
    root_env_excludes_params (ps ++ caps)
      (root_env_remove_params ps R_args).
Proof.
  intros ps caps R_args s_args Hrn Hnamed Hfresh.
  eapply root_env_remove_params_preserves_excludes_params.
  - exact Hrn.
  - eapply root_env_store_roots_named_excludes_params; eassumption.
Qed.

Lemma captured_call_runtime_args_tail_fresh_names_for_fresh_call :
  forall env captured s_args R_args fdef fcall used',
    captured_call_frame_ready env captured
      (empty_root_env_for_store captured) s_args R_args ->
    alpha_rename_fn_def (store_names (captured ++ s_args)) fdef =
      (fcall, used') ->
    root_env_tail_fresh_names
      (root_env_remove_params (fn_params fcall) R_args)
      (expr_local_store_names (fn_body fcall)).
Proof.
  unfold root_env_tail_fresh_names.
  intros env captured s_args R_args fdef fcall used'
    Hframe Hrename x Hin.
  unfold captured_call_frame_ready in Hframe.
  destruct Hframe as [_ [_ [_ [Hrn_tail [Hnamed_tail Hkeys_tail]]]]].
  assert (Hrn_args : root_env_no_shadow R_args).
  { unfold root_env_no_shadow in *.
    rewrite root_env_names_app in Hrn_tail.
    eapply NoDup_app_right_ts. exact Hrn_tail. }
  assert (Hnamed_args :
    root_env_store_roots_named R_args (captured ++ s_args)).
  { unfold root_env_store_roots_named in *.
    intros y roots z Hlookup_args Hin_root.
    eapply Hnamed_tail.
    - assert (Hlookup_cap :
        root_env_lookup y (empty_root_env_for_store captured) = None).
      { eapply root_env_no_shadow_app_lookup_right_none; eassumption. }
      rewrite (root_env_lookup_app_right y
        (empty_root_env_for_store captured) R_args Hlookup_cap).
      exact Hlookup_args.
    - exact Hin_root. }
  assert (Hkeys_args :
    root_env_store_keys_named R_args (captured ++ s_args)).
  { unfold root_env_store_keys_named, root_env_keys_named in *.
    intros y Hin_names.
    apply Hkeys_tail.
    rewrite root_env_names_app.
    apply in_or_app. right. exact Hin_names. }
  pose proof (alpha_rename_fn_def_body_local_store_names_fresh_used
                (store_names (captured ++ s_args)) fdef fcall used'
                Hrename)
    as Hfresh_names.
  assert (Hfresh_x : ~ In x (store_names (captured ++ s_args))).
  { apply (proj1 (Forall_forall _ _) Hfresh_names). exact Hin. }
  assert (Hlookup : root_env_lookup x R_args = None).
  { eapply root_env_store_keys_named_lookup_excludes_name; eassumption. }
  assert (Hexcl : root_env_excludes x R_args).
  { eapply root_env_store_roots_named_excludes_name; eassumption. }
  split.
  - apply root_env_lookup_remove_params_none_preserved. exact Hlookup.
  - apply root_env_remove_params_preserves_excludes; assumption.
Qed.

Lemma captured_call_runtime_root_env_binding_split_equiv :
  forall env captured ps caps arg_roots,
    captured_params_store_typed env captured caps ->
    params_fresh_in_store ps captured ->
    List.length arg_roots = List.length ps ->
    root_env_equiv
      (call_param_root_env ps arg_roots
        (empty_root_env_for_store captured))
      (call_param_root_env (ps ++ caps)
        (arg_roots ++ repeat [] (List.length caps)) []).
Proof.
  intros env captured ps caps arg_roots Hcaptured Hfresh Hlen.
  rewrite (call_param_root_env_app_roots ps caps arg_roots
             (repeat [] (List.length caps)) [] Hlen).
  unfold call_param_root_env at 1.
  rewrite (root_env_remove_params_lookup_none_self
             ps (empty_root_env_for_store captured)).
  - eapply root_env_add_params_roots_preserves_equiv.
    rewrite root_env_remove_params_empty.
    eapply empty_root_env_for_captured_params_equiv. exact Hcaptured.
  - intros x Hin.
    eapply empty_root_env_for_store_params_fresh_lookup_none; eassumption.
Qed.

Lemma captured_call_binding_runtime_root_env_equiv :
  forall env captured fdef fcall used used' arg_roots,
    alpha_rename_fn_def used fdef = (fcall, used') ->
    NoDup (ctx_names (params_ctx
      (fn_params fdef ++ fn_captures fdef))) ->
    List.length arg_roots = List.length (fn_params fdef) ->
    captured_params_store_typed env captured (fn_captures fcall) ->
    params_fresh_in_store (fn_params fcall) captured ->
    root_env_equiv
      (call_param_root_env (fn_params fcall) arg_roots
        (empty_root_env_for_store captured))
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall))).
Proof.
  intros env captured fdef fcall used used' arg_roots Hrename Hnodup
    Hlen_args Hcaptured Hfresh.
  pose proof (alpha_rename_fn_def_binding_params_alpha_ts
                used fdef fcall used' Hrename) as Halpha_binding.
  pose proof (alpha_rename_fn_def_shape used fdef fcall used' Hrename)
    as [_ [_ Halpha_params]].
  assert (Hlen_args_fcall :
    List.length arg_roots = List.length (fn_params fcall)).
  { rewrite <- (params_alpha_length _ _ Halpha_params).
    exact Hlen_args. }
  assert (Hcaps_eq :
    fn_captures fcall = fn_captures fdef).
  { rewrite <- (alpha_rename_fn_def_captures
                  used fdef fcall used' Hrename).
    reflexivity. }
  assert (Hlen_binding :
    List.length
      (arg_roots ++ repeat [] (List.length (fn_captures fdef))) =
    List.length (fn_params fdef ++ fn_captures fdef)).
  { rewrite length_app, repeat_length, length_app.
    rewrite Hlen_args. reflexivity. }
  assert (Hinitial_inst_equiv :
    root_env_equiv
      (root_env_instantiate
        (root_subst_of_params
          (fn_params fdef ++ fn_captures fdef)
          (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
        (initial_root_env_for_params_origin
          (fn_params fdef ++ fn_captures fdef)
          (fn_params fcall ++ fn_captures fcall)))
      (call_param_root_env (fn_params fcall ++ fn_captures fcall)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))) [])).
  { eapply root_env_instantiate_initial_origin_equiv_call_param_root_env_empty;
      eassumption. }
  eapply (root_env_equiv_trans
    (call_param_root_env (fn_params fcall) arg_roots
      (empty_root_env_for_store captured))
    (call_param_root_env (fn_params fcall ++ fn_captures fcall)
      (arg_roots ++ repeat [] (List.length (fn_captures fdef))) [])
    (root_env_instantiate
      (root_subst_of_params
        (fn_params fdef ++ fn_captures fdef)
        (arg_roots ++ repeat [] (List.length (fn_captures fdef))))
      (initial_root_env_for_params_origin
        (fn_params fdef ++ fn_captures fdef)
        (fn_params fcall ++ fn_captures fcall)))).
  - rewrite <- Hcaps_eq.
    eapply captured_call_runtime_root_env_binding_split_equiv;
      eassumption.
  - apply root_env_equiv_sym. exact Hinitial_inst_equiv.
Qed.

Lemma root_env_excludes_add :
  forall x y roots R,
    roots_exclude x roots ->
    root_env_excludes x R ->
    root_env_excludes x (root_env_add y roots R).
Proof.
  unfold root_env_excludes.
  intros x y roots R Hroots Hexcl z roots_z Hlookup Hneq.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb z y) eqn:Heq.
  - inversion Hlookup; subst roots_z. exact Hroots.
  - eapply Hexcl.
    + exact Hlookup.
    + exact Hneq.
Qed.

Lemma root_env_add_params_roots_preserves_excludes_params :
  forall add_ps roots_list protected_ps R_tail,
    Forall (roots_exclude_params protected_ps) roots_list ->
    root_env_excludes_params protected_ps R_tail ->
    root_env_excludes_params protected_ps
      (root_env_add_params_roots add_ps roots_list R_tail).
Proof.
  intros add_ps.
  induction add_ps as [| p add_ps IH];
    intros roots_list protected_ps R_tail Hroots Hexcl;
    destruct roots_list as [| roots roots_list]; simpl in *.
  - exact Hexcl.
  - exact Hexcl.
  - exact Hexcl.
  - inversion Hroots as [| ? ? Hroot Hroots_tail]; subst.
    unfold root_env_excludes_params in *.
    intros x Hin.
    apply root_env_excludes_add.
    + apply Hroot. exact Hin.
    + exact (IH roots_list protected_ps R_tail Hroots_tail Hexcl x Hin).
Qed.

Lemma root_env_add_params_roots_excludes_params :
  forall ps roots_list R_tail,
    Forall (roots_exclude_params ps) roots_list ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps
      (root_env_add_params_roots ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hroots Hexcl.
  eapply root_env_add_params_roots_preserves_excludes_params; eassumption.
Qed.

Lemma call_param_root_env_excludes_params :
  forall ps roots_list R_tail,
    root_env_no_shadow R_tail ->
    Forall (roots_exclude_params ps) roots_list ->
    root_env_excludes_params ps R_tail ->
    root_env_excludes_params ps
      (call_param_root_env ps roots_list R_tail).
Proof.
  intros ps roots_list R_tail Hrn Hroots Hexcl.
  unfold call_param_root_env.
  apply root_env_add_params_roots_excludes_params.
  - exact Hroots.
  - apply root_env_remove_params_excludes_params; assumption.
Qed.

Lemma store_remove_params_cons_non_param :
  forall ps se s,
    ~ In (se_name se) (ctx_names (params_ctx ps)) ->
    store_remove_params ps (se :: s) =
      se :: store_remove_params ps s.
Proof.
  intros ps se.
  induction ps as [| p ps IH].
  - intros s Hnotin. reflexivity.
  - intros s Hnotin. simpl in *.
    destruct (ident_eqb (param_name p) (se_name se)) eqn:Heq.
    + apply ident_eqb_eq in Heq. contradiction Hnotin.
      left. exact Heq.
    + rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_params_store_param_scope :
  forall ps s_param s,
    store_param_scope ps s_param s ->
    exists locals,
      store_remove_params ps s_param = locals ++ s.
Proof.
  intros ps s_param s Hscope.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hnotin _ IH].
  - induction Hprefix as [s | p ps v st s_param s _ IH].
    + exists []. reflexivity.
    + simpl. rewrite ident_eqb_refl. exact IH.
  - simpl. rewrite store_remove_params_cons_non_param.
    + destruct IH as [locals IH].
      exists (se :: locals). rewrite IH. reflexivity.
    + exact Hnotin.
Qed.

Lemma store_remove_in_store :
  forall x s se,
    In se (store_remove x s) ->
    In se s.
Proof.
  intros x s.
  induction s as [| se_head rest IH]; intros se Hin;
    simpl in *; try contradiction.
  destruct (ident_eqb x (se_name se_head)) eqn:Heq.
  - right. exact Hin.
  - simpl in Hin. destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + right. apply IH. exact Hin.
Qed.

Lemma store_remove_params_in_store :
  forall ps s se,
    In se (store_remove_params ps s) ->
    In se s.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros s se Hin; simpl in *.
  - exact Hin.
  - apply store_remove_in_store with (x := param_name p).
    eapply IH. exact Hin.
Qed.

Lemma store_remove_roots_within_same_env :
  forall R s x,
    store_roots_within R s ->
    store_roots_within R (store_remove x s).
Proof.
  intros R s x Hwithin.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - constructor.
  - destruct (ident_eqb x (se_name se)).
    + exact Hrest.
    + constructor; assumption.
Qed.

Lemma store_remove_params_roots_within_same_env :
  forall ps R s,
    store_roots_within R s ->
    store_roots_within R (store_remove_params ps s).
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros R s Hwithin; simpl.
  - exact Hwithin.
  - apply IH. apply store_remove_roots_within_same_env. exact Hwithin.
Qed.

Lemma store_names_add :
  forall x T v s,
    store_names (store_add x T v s) = x :: store_names s.
Proof.
  reflexivity.
Qed.

Lemma store_names_mark_used :
  forall x s,
    store_names (store_mark_used x s) = store_names s.
Proof.
  intros x s.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)); simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma store_names_update_state :
  forall x f s s',
    store_update_state x f s = Some s' ->
    store_names s' = store_names s.
Proof.
  intros x f s.
  induction s as [| se rest IH]; intros s' Hupdate; simpl in Hupdate;
    try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate; subst. simpl. reflexivity.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst. simpl.
    rewrite (IH rest' eq_refl). reflexivity.
Qed.

Lemma store_names_update_val :
  forall x v s s',
    store_update_val x v s = Some s' ->
    store_names s' = store_names s.
Proof.
  intros x v s.
  induction s as [| se rest IH]; intros s' Hupdate; simpl in Hupdate;
    try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate; subst. simpl. reflexivity.
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst. simpl.
    rewrite (IH rest' eq_refl). reflexivity.
Qed.

Lemma store_names_update_path :
  forall x path v s s',
    store_update_path x path v s = Some s' ->
    store_names s' = store_names s.
Proof.
  intros x path v s.
  induction s as [| se rest IH]; intros s' Hupdate; simpl in Hupdate;
    try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - destruct (value_update_path (se_val se) path v) as [v' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate; subst. simpl. reflexivity.
  - destruct (store_update_path x path v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst. simpl.
    rewrite (IH rest' eq_refl). reflexivity.
Qed.

Lemma store_no_shadow_add :
  forall x T v s,
    store_no_shadow s ->
    store_lookup x s = None ->
    store_no_shadow (store_add x T v s).
Proof.
  unfold store_no_shadow.
  intros x T v s Hnodup Hlookup.
  rewrite store_names_add.
  constructor.
  - eapply store_lookup_none_not_in_names. exact Hlookup.
  - exact Hnodup.
Qed.

Lemma store_no_shadow_remove :
  forall x s,
    store_no_shadow s ->
    store_no_shadow (store_remove x s).
Proof.
  unfold store_no_shadow.
  intros x s.
  induction s as [| se rest IH]; intros Hnodup; simpl in *.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct (ident_eqb x (se_name se)).
    + exact Hnodup_tail.
    + simpl. constructor.
      * intros Hin. apply Hnotin.
        clear -Hin.
        induction rest as [| se' rest IHrest]; simpl in *.
        -- contradiction.
        -- destruct (ident_eqb x (se_name se')).
           ++ right. exact Hin.
           ++ destruct Hin as [Hin | Hin].
              ** left. exact Hin.
              ** right. apply IHrest. exact Hin.
      * apply IH. exact Hnodup_tail.
Qed.

Lemma store_no_shadow_mark_used :
  forall x s,
    store_no_shadow s ->
    store_no_shadow (store_mark_used x s).
Proof.
  unfold store_no_shadow.
  intros x s Hnodup.
  rewrite store_names_mark_used. exact Hnodup.
Qed.

Lemma store_no_shadow_update_state :
  forall x f s s',
    store_no_shadow s ->
    store_update_state x f s = Some s' ->
    store_no_shadow s'.
Proof.
  unfold store_no_shadow.
  intros x f s s' Hnodup Hupdate.
  rewrite (store_names_update_state x f s s' Hupdate). exact Hnodup.
Qed.

Lemma store_no_shadow_update_val :
  forall x v s s',
    store_no_shadow s ->
    store_update_val x v s = Some s' ->
    store_no_shadow s'.
Proof.
  unfold store_no_shadow.
  intros x v s s' Hnodup Hupdate.
  rewrite (store_names_update_val x v s s' Hupdate). exact Hnodup.
Qed.

Lemma store_no_shadow_update_path :
  forall x path v s s',
    store_no_shadow s ->
    store_update_path x path v s = Some s' ->
    store_no_shadow s'.
Proof.
  unfold store_no_shadow.
  intros x path v s s' Hnodup Hupdate.
  rewrite (store_names_update_path x path v s s' Hupdate). exact Hnodup.
Qed.

Lemma store_entry_name_in_store_names :
  forall se s,
    In se s ->
    In (se_name se) (store_names s).
Proof.
  intros se s Hin.
  induction s as [| se' rest IH]; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - subst se'. left. reflexivity.
  - right. apply IH. exact Hin.
Qed.

Lemma store_no_shadow_remove_no_name :
  forall x s,
    store_no_shadow s ->
    forall se,
      In se (store_remove x s) ->
      se_name se <> x.
Proof.
  intros x s Hnodup se Hin.
  unfold store_no_shadow in Hnodup.
  induction s as [| se' rest IH]; simpl in *; try contradiction.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  destruct (ident_eqb x (se_name se')) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    intros Hsame. apply Hnotin.
    rewrite <- Hsame.
    eapply store_entry_name_in_store_names. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst se'. intros Hsame. subst x.
      rewrite ident_eqb_refl in Heq. discriminate.
    + apply IH; assumption.
Qed.

Lemma store_no_shadow_remove_lookup_none :
  forall x s,
    store_no_shadow s ->
    store_lookup x (store_remove x s) = None.
Proof.
  intros x s Hnodup.
  unfold store_no_shadow in Hnodup.
  induction s as [| se rest IH]; simpl in *; try reflexivity.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    apply store_lookup_not_in_names. exact Hnotin.
  - simpl. rewrite Heq. apply IH. exact Hnodup_tail.
Qed.

Lemma store_remove_params_no_param_names :
  forall ps s,
    NoDup (ctx_names (params_ctx ps)) ->
    store_no_shadow s ->
    forall x,
      In x (ctx_names (params_ctx ps)) ->
      forall se,
        In se (store_remove_params ps s) ->
        se_name se <> x.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros s Hnodup Hshadow x Hin se Hse.
  - simpl in Hin. contradiction.
  - simpl in Hnodup, Hin.
    inversion Hnodup as [| ? ? Hhead_notin Hnodup_tail]; subst.
    destruct Hin as [Hin | Hin].
    + subst x.
      apply store_no_shadow_remove_no_name with (s := s).
      * exact Hshadow.
      * eapply store_remove_params_in_store. exact Hse.
    + eapply IH.
      * exact Hnodup_tail.
      * apply store_no_shadow_remove. exact Hshadow.
      * exact Hin.
      * exact Hse.
Qed.

Lemma value_roots_exclude_params :
  forall ps roots v,
    value_roots_within roots v ->
    roots_exclude_params ps roots ->
    value_refs_exclude_params ps v.
Proof.
  unfold value_refs_exclude_params, roots_exclude_params.
  intros ps roots v Hwithin Hexclude x Hin.
  eapply value_roots_exclude_root.
  - exact Hwithin.
  - apply Hexclude. exact Hin.
Qed.

Lemma store_roots_exclude_params :
  forall ps R s,
    store_roots_within R s ->
    root_env_excludes_params ps R ->
    (forall x,
      In x (ctx_names (params_ctx ps)) ->
      forall se, In se s -> se_name se <> x) ->
    store_refs_exclude_params ps s.
Proof.
  unfold store_refs_exclude_params, root_env_excludes_params.
  intros ps R s Hwithin Hexclude Hnames x Hin.
  eapply store_roots_exclude_root.
  - exact Hwithin.
  - apply Hexclude. exact Hin.
  - intros se Hse. apply Hnames with (x := x); assumption.
Qed.

Lemma store_roots_within_named_fresh_refs_exclude_root :
  forall R s root,
    store_roots_within R s ->
    root_env_store_roots_named R s ->
    ~ In root (store_names s) ->
    store_refs_exclude_root root s.
Proof.
  intros R s root Hroots Hnamed Hfresh.
  eapply store_roots_exclude_root.
  - exact Hroots.
  - unfold root_env_store_roots_named, root_env_excludes, roots_exclude in *.
    intros y roots Hlookup _ Hin.
    apply Hfresh. eapply Hnamed; eassumption.
  - intros se Hin Heq. apply Hfresh.
    rewrite <- Heq. apply store_names_in_store_entry. exact Hin.
Qed.

Lemma root_set_union_in_right :
  forall x roots_left roots_right,
    In x roots_right ->
    In x (root_set_union roots_left roots_right).
Proof.
  intros x roots_left roots_right Hin.
  induction roots_left as [| y ys IH]; simpl; try assumption.
  destruct (existsb (root_atom_eqb y) roots_right).
  - apply IH.
  - right. apply IH.
Qed.

Lemma root_set_union_in_left :
  forall x roots_left roots_right,
    In x roots_left ->
    In x (root_set_union roots_left roots_right).
Proof.
  intros x roots_left roots_right Hin.
  induction roots_left as [| y ys IH]; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - subst y.
    destruct (existsb (root_atom_eqb x) roots_right) eqn:Hexists.
    + apply root_set_union_in_right.
      apply existsb_exists in Hexists.
      destruct Hexists as [z [Hz_in Hz_eq]].
      apply root_atom_eqb_eq in Hz_eq. subst z. exact Hz_in.
    + simpl. left. reflexivity.
  - destruct (existsb (root_atom_eqb y) roots_right).
    + apply IH. exact Hin.
    + simpl. right. apply IH. exact Hin.
Qed.

Lemma value_roots_within_weaken :
  (forall roots v,
    value_roots_within roots v ->
    forall roots',
      (forall x, In x roots -> In x roots') ->
      value_roots_within roots' v) /\
  (forall R se,
    store_entry_roots_within R se ->
    forall R',
      (forall x roots, root_env_lookup x R = Some roots ->
        exists roots', root_env_lookup x R' = Some roots' /\
          forall y, In y roots -> In y roots') ->
      store_entry_roots_within R' se) /\
  (forall R s,
    store_roots_within R s ->
    forall R',
      (forall x roots, root_env_lookup x R = Some roots ->
        exists roots', root_env_lookup x R' = Some roots' /\
          forall y, In y roots -> In y roots') ->
      store_roots_within R' s) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall roots',
      (forall x, In x roots -> In x roots') ->
      value_fields_roots_within roots' fields).
Proof.
  apply value_roots_within_mutind; intros; try solve [constructor; eauto].
  - constructor.
    intros root Hexclude.
    apply s.
    unfold roots_exclude in *.
    intros Hin.
    apply Hexclude.
    apply H. exact Hin.
  - destruct (H0 sx roots e) as [roots' [Hlookup Hincl]].
    eapply SERW_Entry.
    + exact Hlookup.
    + eapply H. exact Hincl.
Qed.

Lemma root_env_store_roots_named_weaken_store :
  forall R s s',
    root_env_store_roots_named R s ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    root_env_store_roots_named R s'.
Proof.
  unfold root_env_store_roots_named.
  intros R s s' Hnamed Hincl x roots z Hlookup Hin.
  apply Hincl. eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_roots_named_weaken_ctx :
  forall R Σ Σ',
    root_env_ctx_roots_named R Σ ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    root_env_ctx_roots_named R Σ'.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ Σ' Hnamed Hincl x roots z Hlookup Hin.
  apply Hincl. eapply Hnamed; eassumption.
Qed.

Lemma root_set_store_roots_named_weaken_store :
  forall roots s s',
    root_set_store_roots_named roots s ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    root_set_store_roots_named roots s'.
Proof.
  unfold root_set_store_roots_named.
  intros roots s s' Hnamed Hincl z Hin.
  apply Hincl. apply Hnamed. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_weaken_ctx :
  forall roots Σ Σ',
    root_set_ctx_roots_named roots Σ ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots Σ Σ' Hnamed Hincl z Hin.
  apply Hincl. apply Hnamed. exact Hin.
Qed.

Lemma root_set_store_roots_named_nil :
  forall s,
    root_set_store_roots_named [] s.
Proof.
  unfold root_set_store_roots_named.
  intros s z Hin. contradiction.
Qed.

Lemma root_set_ctx_roots_named_nil :
  forall Σ,
    root_set_ctx_roots_named [] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ z Hin. contradiction.
Qed.

Lemma root_set_store_roots_named_single :
  forall s x,
    In x (store_names s) ->
    root_set_store_roots_named [RStore x] s.
Proof.
  unfold root_set_store_roots_named.
  intros s x Hin_store z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin. subst z. exact Hin_store.
Qed.

Lemma root_set_ctx_roots_named_single :
  forall Σ x,
    In x (ctx_names Σ) ->
    root_set_ctx_roots_named [RStore x] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ x Hin_ctx z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin. subst z. exact Hin_ctx.
Qed.

Lemma root_set_store_roots_named_param_single :
  forall s x,
    root_set_store_roots_named [RParam x] s.
Proof.
  unfold root_set_store_roots_named.
  intros s x z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin.
  - contradiction.
Qed.

Lemma root_set_ctx_roots_named_param_single :
  forall Σ x,
    root_set_ctx_roots_named [RParam x] Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros Σ x z Hin.
  simpl in Hin.
  destruct Hin as [Hin | Hin].
  - inversion Hin.
  - contradiction.
Qed.

Lemma root_set_store_roots_named_equiv :
  forall roots roots' s,
    root_set_equiv roots roots' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots' s.
Proof.
  unfold root_set_store_roots_named.
  intros roots roots' s Heq Hnamed z Hin.
  apply Hnamed. apply Heq. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_equiv :
  forall roots roots' Σ,
    root_set_equiv roots roots' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots' Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots roots' Σ Heq Hnamed z Hin.
  apply Hnamed. apply Heq. exact Hin.
Qed.

Lemma store_roots_within_equiv :
  forall R R' s,
    root_env_equiv R R' ->
    store_roots_within R s ->
    store_roots_within R' s.
Proof.
  intros R R' s Heq Hroots.
  eapply (proj2 (proj2 value_roots_within_weaken)).
  - exact Hroots.
  - intros x roots Hlookup.
    destruct (root_env_equiv_lookup_l R R' x roots Heq Hlookup)
      as [roots' [Hlookup' Hroots_equiv]].
    exists roots'. split.
    + exact Hlookup'.
    + intros atom Hin.
      apply Hroots_equiv. exact Hin.
Qed.

Lemma root_set_store_roots_named_union :
  forall roots_left roots_right s,
    root_set_store_roots_named roots_left s ->
    root_set_store_roots_named roots_right s ->
    root_set_store_roots_named
      (root_set_union roots_left roots_right) s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hleft Hright z Hin.
  apply root_set_union_in_inv in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hleft. exact Hin.
  - apply Hright. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named roots_left Σ ->
    root_set_ctx_roots_named roots_right Σ ->
    root_set_ctx_roots_named
      (root_set_union roots_left roots_right) Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hleft Hright z Hin.
  apply root_set_union_in_inv in Hin.
  destruct Hin as [Hin | Hin].
  - apply Hleft. exact Hin.
  - apply Hright. exact Hin.
Qed.

Lemma root_set_store_roots_named_union_inv_l :
  forall roots_left roots_right s,
    root_set_store_roots_named (root_set_union roots_left roots_right) s ->
    root_set_store_roots_named roots_left s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_l. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union_inv_l :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named (root_set_union roots_left roots_right) Σ ->
    root_set_ctx_roots_named roots_left Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_l. exact Hin.
Qed.

Lemma root_set_store_roots_named_union_inv_r :
  forall roots_left roots_right s,
    root_set_store_roots_named (root_set_union roots_left roots_right) s ->
    root_set_store_roots_named roots_right s.
Proof.
  unfold root_set_store_roots_named.
  intros roots_left roots_right s Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_r. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_union_inv_r :
  forall roots_left roots_right Σ,
    root_set_ctx_roots_named (root_set_union roots_left roots_right) Σ ->
    root_set_ctx_roots_named roots_right Σ.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots_left roots_right Σ Hnamed z Hin.
  apply Hnamed. apply root_set_union_in_r. exact Hin.
Qed.

Lemma root_sets_store_roots_named_union :
  forall sets s,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    root_set_store_roots_named (root_sets_union sets) s.
Proof.
  intros sets s Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH]; simpl.
  - apply root_set_store_roots_named_nil.
  - apply root_set_store_roots_named_union; assumption.
Qed.

Lemma root_sets_union_store_roots_named_excludes_name :
  forall roots_list s x,
    Forall (fun roots => root_set_store_roots_named roots s) roots_list ->
    ~ In x (store_names s) ->
    roots_exclude x (root_sets_union roots_list).
Proof.
  intros roots_list s x Hnamed Hfresh.
  apply roots_exclude_root_sets_union.
  induction Hnamed as [| roots roots_list Hroot Hrest IH].
  - constructor.
  - constructor.
    + unfold root_set_store_roots_named, roots_exclude in *.
      intros Hin. apply Hfresh. apply Hroot. exact Hin.
    + exact IH.
Qed.

Lemma root_sets_ctx_roots_named_union :
  forall sets Σ,
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    root_set_ctx_roots_named (root_sets_union sets) Σ.
Proof.
  intros sets Σ Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH]; simpl.
  - apply root_set_ctx_roots_named_nil.
  - apply root_set_ctx_roots_named_union; assumption.
Qed.

Lemma root_sets_store_roots_named_weaken_store :
  forall sets s s',
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    (forall z, In z (store_names s) -> In z (store_names s')) ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s s' Hsets Hincl.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_weaken_store; eassumption.
    + apply IH.
Qed.

Lemma root_sets_ctx_roots_named_weaken_ctx :
  forall sets Σ Σ',
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    (forall z, In z (ctx_names Σ) -> In z (ctx_names Σ')) ->
    Forall (fun roots => root_set_ctx_roots_named roots Σ') sets.
Proof.
  intros sets Σ Σ' Hsets Hincl.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_ctx_roots_named_weaken_ctx; eassumption.
    + apply IH.
Qed.

Lemma store_update_state_names :
  forall s x f s',
    store_update_state x f s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x f s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x f rest' Htail). reflexivity.
Qed.

Lemma store_update_val_names :
  forall s x v s',
    store_update_val x v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x v rest' Htail). reflexivity.
Qed.

Lemma store_update_path_names :
  forall s x path v s',
    store_update_path x path v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x path v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - destruct (value_update_path (se_val se) path v) as [v' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate. reflexivity.
  - destruct (store_update_path x path v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x path v rest' Htail). reflexivity.
Qed.

Lemma store_restore_path_names :
  forall s x path s',
    store_restore_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_restore_path.
  intros s x path s' Hrestore.
  eapply store_update_state_names. exact Hrestore.
Qed.

Lemma store_consume_path_names :
  forall s x path s',
    store_consume_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_consume_path.
  intros s x path s' Hconsume.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_names. exact Hconsume.
Qed.

Lemma root_env_store_roots_named_store_add :
  forall R s x T v,
    root_env_store_roots_named R s ->
    root_env_store_roots_named R (store_add x T v s).
Proof.
  intros R s x T v Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_set_store_roots_named_store_add :
  forall roots s x T v,
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots (store_add x T v s).
Proof.
  intros roots s x T v Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_store_roots_named_add_env_store_add :
  forall R s x roots T v,
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_add x roots R)
      (store_add x T v s).
Proof.
  intros R s x roots T v Henv Hroots.
  unfold root_env_store_roots_named.
  intros y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. simpl. right.
    apply Hroots. exact Hin.
  - simpl. right. eapply Henv; eassumption.
Qed.

Lemma root_env_store_keys_named_add_env_store_add :
  forall R s x roots T v,
    root_env_store_keys_named R s ->
    root_env_store_keys_named (root_env_add x roots R)
      (store_add x T v s).
Proof.
  intros R s x roots T v Hkeys.
  unfold root_env_store_keys_named.
  apply root_env_keys_named_add.
  - simpl. left. reflexivity.
  - eapply root_env_keys_named_weaken.
    + exact Hkeys.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_store_roots_named_store_remove_excluding :
  forall R s x,
    (forall y roots,
      root_env_lookup y R = Some roots ->
      roots_exclude x roots) ->
    root_env_store_roots_named R s ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    root_env_store_roots_named R (store_remove x s).
Proof.
  unfold root_env_store_roots_named.
  intros R s x Hexcludes Hnamed Hremain y roots z Hlookup Hin.
  apply Hremain.
  - eapply Hnamed; eassumption.
  - intros Heq. subst z.
    unfold roots_exclude in Hexcludes.
    eapply Hexcludes; eassumption.
Qed.

Lemma root_set_store_roots_named_store_remove_excluding :
  forall roots s x,
    roots_exclude x roots ->
    root_set_store_roots_named roots s ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    root_set_store_roots_named roots (store_remove x s).
Proof.
  unfold root_set_store_roots_named, roots_exclude.
  intros roots s x Hexclude Hnamed Hremain z Hin.
  apply Hremain.
  - apply Hnamed. exact Hin.
  - intros Heq. subst z. apply Hexclude. exact Hin.
Qed.

Lemma root_env_store_roots_named_store_mark_used :
  forall R s x,
    root_env_store_roots_named R s ->
    root_env_store_roots_named R (store_mark_used x s).
Proof.
  intros R s x Hnamed.
  assert (Hincl :
    forall z,
      In z (store_names s) ->
      In z (store_names (store_mark_used x s))).
  {
    clear Hnamed.
    induction s as [| se rest IH]; intros z Hin; simpl in *; try contradiction.
    destruct (ident_eqb x (se_name se)); simpl in *.
    - exact Hin.
    - destruct Hin as [Hin | Hin].
      + left. exact Hin.
      + right. apply IH. exact Hin.
  }
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - exact Hincl.
Qed.

Lemma root_set_store_roots_named_store_mark_used :
  forall roots s x,
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots (store_mark_used x s).
Proof.
  intros roots s x Hnamed.
  assert (Hincl :
    forall z,
      In z (store_names s) ->
      In z (store_names (store_mark_used x s))).
  {
    clear roots Hnamed.
    induction s as [| se rest IH]; intros z Hin; simpl in *; try contradiction.
    destruct (ident_eqb x (se_name se)); simpl in *.
    - exact Hin.
    - destruct Hin as [Hin | Hin].
      + left. exact Hin.
      + right. apply IH. exact Hin.
  }
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - exact Hincl.
Qed.

Lemma root_sets_store_roots_named_store_add :
  forall sets s x T v,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_add x T v s))
      sets.
Proof.
  intros sets s x T v Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + apply root_set_store_roots_named_store_add. exact Hroot.
    + apply IH.
Qed.

Lemma root_sets_store_roots_named_store_mark_used :
  forall sets s x,
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_mark_used x s))
      sets.
Proof.
  intros sets s x Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + apply root_set_store_roots_named_store_mark_used. exact Hroot.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_state :
  forall R s x f s',
    store_update_state x f s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x f s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_state_names s x f s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_state :
  forall roots s x f s',
    store_update_state x f s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x f s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_state_names s x f s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_state :
  forall sets s x f s',
    store_update_state x f s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x f s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_state; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_val :
  forall R s x v s',
    store_update_val x v s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x v s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_val_names s x v s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_val :
  forall roots s x v s',
    store_update_val x v s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x v s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_val_names s x v s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_val :
  forall sets s x v s',
    store_update_val x v s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x v s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_val; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_update_path :
  forall R s x path v s',
    store_update_path x path v s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path v s' Hupdate Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_path_names s x path v s' Hupdate).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_update_path :
  forall roots s x path v s',
    store_update_path x path v s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path v s' Hupdate Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_update_path_names s x path v s' Hupdate).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_update_path :
  forall sets s x path v s',
    store_update_path x path v s = Some s' ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    Forall (fun roots => root_set_store_roots_named roots s') sets.
Proof.
  intros sets s x path v s' Hupdate Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_store_roots_named_store_update_path; eassumption.
    + apply IH.
Qed.

Lemma root_env_store_roots_named_store_restore_path :
  forall R s x path s',
    store_restore_path x path s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path s' Hrestore Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_restore_path_names s x path s' Hrestore).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_restore_path :
  forall roots s x path s',
    store_restore_path x path s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path s' Hrestore Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_restore_path_names s x path s' Hrestore).
    exact Hin.
Qed.

Lemma root_env_store_roots_named_store_consume_path :
  forall R s x path s',
    store_consume_path x path s = Some s' ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named R s'.
Proof.
  intros R s x path s' Hconsume Hnamed.
  eapply root_env_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_consume_path_names s x path s' Hconsume).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_store_consume_path :
  forall roots s x path s',
    store_consume_path x path s = Some s' ->
    root_set_store_roots_named roots s ->
    root_set_store_roots_named roots s'.
Proof.
  intros roots s x path s' Hconsume Hnamed.
  eapply root_set_store_roots_named_weaken_store.
  - exact Hnamed.
  - intros z Hin. rewrite (store_consume_path_names s x path s' Hconsume).
    exact Hin.
Qed.

Lemma root_sets_store_roots_named_store_remove_excluding :
  forall sets s x,
    Forall (roots_exclude x) sets ->
    Forall (fun roots => root_set_store_roots_named roots s) sets ->
    (forall z,
      In z (store_names s) ->
      z <> x ->
      In z (store_names (store_remove x s))) ->
    Forall
      (fun roots => root_set_store_roots_named roots (store_remove x s))
      sets.
Proof.
  intros sets s x Hexcludes Hsets Hremain.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - inversion Hexcludes as [| ? ? Hexclude Hrest_excludes]. subst.
    constructor.
    + eapply root_set_store_roots_named_store_remove_excluding; eassumption.
    + apply IH. exact Hrest_excludes.
Qed.

Lemma root_env_store_roots_named_add_env :
  forall R s x roots,
    root_env_store_roots_named R s ->
    (forall z, In (RStore z) roots -> In z (store_names s)) ->
    root_env_store_roots_named (root_env_add x roots R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x roots Hnamed Hroots y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
  - eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_roots_named_add_env :
  forall R Σ x roots,
    root_env_ctx_roots_named R Σ ->
    (forall z, In (RStore z) roots -> In z (ctx_names Σ)) ->
    root_env_ctx_roots_named (root_env_add x roots R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x roots Hnamed Hroots y roots_y z Hlookup Hin.
  unfold root_env_add in Hlookup. simpl in Hlookup.
  destruct (ident_eqb y x) eqn:Hyx.
  - inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
  - eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_roots_named_add_env_named :
  forall R s x roots,
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_add x roots R) s.
Proof.
  intros R s x roots Henv Hroots.
  apply root_env_store_roots_named_add_env.
  - exact Henv.
  - exact Hroots.
Qed.

Lemma root_env_ctx_roots_named_add_env_named :
  forall R Σ x roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_add x roots R) Σ.
Proof.
  intros R Σ x roots Henv Hroots.
  apply root_env_ctx_roots_named_add_env.
  - exact Henv.
  - exact Hroots.
Qed.

Lemma root_env_store_roots_named_remove_env :
  forall R s x,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_roots_named (root_env_remove x R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x Hnodup Hnamed y roots z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - apply ident_eqb_eq in Hxr. subst r.
    eapply Hnamed.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        exfalso. apply Hr_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hyx. exact Hlookup.
    + exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_ctx_roots_named_remove_env :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named (root_env_remove x R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x Hnodup Hnamed y roots z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - apply ident_eqb_eq in Hxr. subst r.
    eapply Hnamed.
    + simpl.
      destruct (ident_eqb y x) eqn:Hyx.
      * apply ident_eqb_eq in Hyx. subst y.
        exfalso. apply Hr_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup.
      * rewrite Hyx. exact Hlookup.
    + exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_store_roots_named_update_env :
  forall R s x roots,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    (forall z, In (RStore z) roots -> In z (store_names s)) ->
    root_env_store_roots_named (root_env_update x roots R) s.
Proof.
  unfold root_env_store_roots_named.
  intros R s x roots Hnodup Hnamed Hroots y roots_y z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y.
      eapply Hnamed.
      * simpl. rewrite Hyp. reflexivity.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_ctx_roots_named_update_env :
  forall R Σ x roots,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    (forall z, In (RStore z) roots -> In z (ctx_names Σ)) ->
    root_env_ctx_roots_named (root_env_update x roots R) Σ.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ x roots Hnodup Hnamed Hroots y roots_y z Hlookup Hin.
  induction R as [| [r roots_r] rest IH]; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hr_notin Hnodup_tail]; subst.
  destruct (ident_eqb x r) eqn:Hxr.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y. apply Hroots. exact Hin.
    + eapply Hnamed.
      * simpl. rewrite Hyp. exact Hlookup.
      * exact Hin.
  - simpl in Hlookup.
    destruct (ident_eqb y r) eqn:Hyp.
    + inversion Hlookup. subst roots_y.
      eapply Hnamed.
      * simpl. rewrite Hyp. reflexivity.
      * exact Hin.
    + apply IH.
      * unfold root_env_no_shadow. exact Hnodup_tail.
      * intros y0 roots0 z0 Hlookup0 Hin0.
        eapply Hnamed.
        -- simpl. destruct (ident_eqb y0 r) eqn:Hy0r.
           ++ apply ident_eqb_eq in Hy0r. subst y0.
              exfalso. apply Hr_notin.
              eapply root_env_lookup_some_in_names. exact Hlookup0.
           ++ rewrite Hy0r. exact Hlookup0.
        -- exact Hin0.
      * exact Hlookup.
Qed.

Lemma root_env_store_roots_named_update_env_named :
  forall R s x roots,
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_set_store_roots_named roots s ->
    root_env_store_roots_named (root_env_update x roots R) s.
Proof.
  intros R s x roots Hrn Henv Hroots.
  apply root_env_store_roots_named_update_env; assumption.
Qed.

Lemma root_env_ctx_roots_named_update_env_named :
  forall R Σ x roots,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_update x roots R) Σ.
Proof.
  intros R Σ x roots Hrn Henv Hroots.
  apply root_env_ctx_roots_named_update_env; assumption.
Qed.

Lemma store_roots_within_lookup_none :
  forall R s x,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    store_lookup x s = None.
Proof.
  intros R s x Hwithin Hlookup_none.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - reflexivity.
  - inversion Hentry; subst.
    destruct (ident_eqb x sx) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst sx.
      rewrite Hlookup_none in H. discriminate.
    + simpl. rewrite Heq. apply IH. exact Hlookup_none.
Qed.

Lemma store_roots_within_lookup_value :
  forall R s x se roots,
    store_roots_within R s ->
    store_lookup x s = Some se ->
    root_env_lookup x R = Some roots ->
    value_roots_within roots (se_val se).
Proof.
  intros R s x se roots Hwithin Hlookup Hroot.
  revert x se roots Hlookup Hroot.
  induction Hwithin as [R | R se_head rest Hentry Hrest IH];
    intros x se roots Hlookup Hroot; simpl in Hlookup; try discriminate.
  destruct se_head as [sx sT sv sst].
  simpl in Hlookup.
  inversion Hentry; subst.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    inversion Hlookup; subst se.
    match goal with
    | Hlookup_se : root_env_lookup sx R = Some ?roots_se,
      Hvalue_se : value_roots_within ?roots_se sv |- _ =>
        rewrite Hroot in Hlookup_se;
        inversion Hlookup_se; subst;
        exact Hvalue_se
    end.
  - eapply IH; eassumption.
Qed.

Lemma value_lookup_path_roots_within :
  forall roots v path v_path,
    value_roots_within roots v ->
    value_lookup_path v path = Some v_path ->
    value_roots_within roots v_path.
Proof.
  intros roots v path.
  revert roots v.
  induction path as [| f rest IH]; intros roots v v_path Hwithin Hlookup;
    simpl in Hlookup.
  - inversion Hlookup; subst. exact Hwithin.
  - inversion Hwithin; subst; try discriminate.
    simpl in Hlookup.
    remember (
      fix lookup (fields0 : list (string * value)) : option value :=
        match fields0 with
        | [] => None
        | (name, fv) :: tail =>
            if String.eqb f name then Some fv else lookup tail
        end) as lookup.
    assert (Hfields :
      forall fs fv,
        value_fields_roots_within roots fs ->
        lookup fs = Some fv ->
        value_roots_within roots fv).
    { intros fs. subst lookup.
      induction fs as [| [fname fv] tail IHfields]; intros fv_path
        Hfields_roots Hfields_lookup; simpl in Hfields_lookup; try discriminate.
      inversion Hfields_roots; subst.
      destruct (String.eqb f fname) eqn:Hname.
      - inversion Hfields_lookup; subst. assumption.
      - eapply IHfields; eassumption. }
    destruct (lookup fields) as [fv |] eqn:Hfield_lookup; try discriminate.
    eapply IH.
    + eapply Hfields; eassumption.
    + exact Hlookup.
Qed.

Lemma store_roots_within_add_env :
  forall R s x roots,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    store_roots_within (root_env_add x roots R) s.
Proof.
  intros R s x roots Hwithin Hfresh.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite (root_env_lookup_add_neq x sx roots R).
        -- exact H.
        -- intros Heq. subst sx. rewrite Hfresh in H. discriminate.
      * exact H0.
    + apply IH. exact Hfresh.
Qed.

Lemma store_add_roots_within :
  forall R s x T v roots,
    store_roots_within R s ->
    root_env_lookup x R = None ->
    value_roots_within roots v ->
    store_roots_within (root_env_add x roots R) (store_add x T v s).
Proof.
  intros R s x T v roots Hstore Hfresh Hvalue.
  unfold store_add.
  constructor.
  - exact (SERW_Entry (root_env_add x roots R) x T v
      (binding_state_of_bool false) roots
      (root_env_lookup_add_eq x roots R) Hvalue).
  - apply store_roots_within_add_env; assumption.
Qed.

Lemma store_add_fresh_ref_targets_preserved :
  forall env s x T v,
    store_lookup x s = None ->
    store_ref_targets_preserved env s (store_add x T v s).
Proof.
  unfold store_ref_targets_preserved.
  intros env s x T v Hfresh y path se v_old T_old Hlookup Hvalue Htype.
  exists se, v_old.
  repeat split; try assumption.
  unfold store_add. simpl.
  destruct (ident_eqb y x) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    rewrite Hlookup in Hfresh. discriminate.
  - exact Hlookup.
Qed.

Lemma store_roots_within_remove_env :
  forall R s x,
    store_roots_within R s ->
    (forall se, In se s -> se_name se <> x) ->
    store_roots_within (root_env_remove x R) s.
Proof.
  intros R s x Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite (root_env_lookup_remove_neq x sx R).
        -- exact H.
        -- intros Hsame. subst sx.
           apply (Hnames (MkStoreEntry x sT sv sst)).
           ++ simpl. left. reflexivity.
           ++ reflexivity.
      * exact H0.
    + apply IH.
      intros se Hin. apply Hnames. simpl. right. exact Hin.
Qed.

Lemma store_remove_roots_within :
  forall R s x,
    store_roots_within R s ->
    (forall se, In se (store_remove x s) -> se_name se <> x) ->
    store_roots_within (root_env_remove x R) (store_remove x s).
Proof.
  intros R s x Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - constructor.
  - destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply store_roots_within_remove_env.
      * exact Hrest.
      * intros se0 Hin. apply Hnames. simpl. rewrite Heq. exact Hin.
    + constructor.
      * inversion Hentry; subst.
        eapply SERW_Entry.
        -- rewrite (root_env_lookup_remove_neq x sx R).
           ++ exact H.
           ++ intros Hsame. subst sx.
              rewrite ident_eqb_refl in Heq. discriminate.
        -- exact H0.
      * apply IH.
        intros se0 Hin. apply Hnames. simpl.
        rewrite Heq. right. exact Hin.
Qed.

Lemma store_update_state_roots_within :
  forall R s x f s',
    store_roots_within R s ->
    store_update_state x f s = Some s' ->
    store_roots_within R s'.
Proof.
  intros R s x f s' Hwithin Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate; subst. inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry; eassumption.
    + exact Hrest.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate; subst.
    constructor; eauto.
Qed.

Lemma store_mark_used_roots_within :
  forall R s x,
    store_roots_within R s ->
    store_roots_within R (store_mark_used x s).
Proof.
  intros R s x Hwithin.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; simpl.
  - constructor.
  - destruct (ident_eqb x (se_name se)); inversion Hentry; subst.
    + constructor.
      * econstructor; eassumption.
      * exact Hrest.
    + constructor.
      * econstructor; eassumption.
      * exact IH.
Qed.

Lemma root_env_ctx_roots_named_store_typed :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_ctx_roots_named R Σ ->
    root_env_store_roots_named R s.
Proof.
  unfold root_env_ctx_roots_named, root_env_store_roots_named.
  intros env s Σ R Htyped Hnamed x roots z Hlookup Hin.
  rewrite (store_typed_names env s Σ Htyped).
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_ctx_roots_named_store_typed :
  forall env s Σ roots,
    store_typed env s Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_set_store_roots_named roots s.
Proof.
  unfold root_set_ctx_roots_named, root_set_store_roots_named.
  intros env s Σ roots Htyped Hnamed z Hin.
  rewrite (store_typed_names env s Σ Htyped).
  apply Hnamed. exact Hin.
Qed.

Lemma root_sets_ctx_roots_named_store_typed :
  forall env s Σ sets,
    store_typed env s Σ ->
    Forall (fun roots => root_set_ctx_roots_named roots Σ) sets ->
    Forall (fun roots => root_set_store_roots_named roots s) sets.
Proof.
  intros env s Σ sets Htyped Hsets.
  induction Hsets as [| roots rest Hroot Hrest IH].
  - constructor.
  - constructor.
    + eapply root_set_ctx_roots_named_store_typed; eassumption.
    + apply IH.
Qed.

Lemma store_typed_sctx_no_shadow :
  forall env s Σ,
    store_typed env s Σ ->
    store_no_shadow s ->
    sctx_no_shadow Σ.
Proof.
  unfold store_no_shadow, sctx_no_shadow.
  intros env s Σ Htyped Hnodup.
  rewrite <- (store_typed_names env s Σ Htyped).
  exact Hnodup.
Qed.

Lemma store_typed_store_no_shadow :
  forall env s Σ,
    store_typed env s Σ ->
    sctx_no_shadow Σ ->
    store_no_shadow s.
Proof.
  unfold store_no_shadow, sctx_no_shadow.
  intros env s Σ Htyped Hnodup.
  rewrite (store_typed_names env s Σ Htyped).
  exact Hnodup.
Qed.

Lemma store_roots_within_update_env_neq :
  forall R s x roots_update,
    store_roots_within R s ->
    (forall se, In se s -> se_name se <> x) ->
    store_roots_within (root_env_update x roots_update R) s.
Proof.
  intros R s x roots_update Hwithin Hnames.
  induction Hwithin as [R | R se rest Hentry Hrest IH].
  - constructor.
  - inversion Hentry; subst.
    constructor.
    + eapply SERW_Entry.
      * rewrite root_env_lookup_update_neq.
        -- exact H.
        -- intros Hsame. subst sx.
           apply (Hnames (MkStoreEntry x sT sv sst)).
           ++ simpl. left. reflexivity.
           ++ reflexivity.
      * exact H0.
    + apply IH.
      intros se0 Hin. apply Hnames. simpl. right. exact Hin.
Qed.

Lemma value_roots_within_union_l :
  forall roots_old roots_new v,
    value_roots_within roots_old v ->
    value_roots_within (root_set_union roots_old roots_new) v.
Proof.
  intros roots_old roots_new v Hwithin.
  eapply (proj1 value_roots_within_weaken).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_left. exact Hin.
Qed.

Lemma value_roots_within_union_r :
  forall roots_old roots_new v,
    value_roots_within roots_new v ->
    value_roots_within (root_set_union roots_old roots_new) v.
Proof.
  intros roots_old roots_new v Hwithin.
  eapply (proj1 value_roots_within_weaken).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_right. exact Hin.
Qed.

Lemma value_fields_roots_within_union_l :
  forall roots_old roots_new fields,
    value_fields_roots_within roots_old fields ->
    value_fields_roots_within (root_set_union roots_old roots_new) fields.
Proof.
  intros roots_old roots_new fields Hwithin.
  eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_left. exact Hin.
Qed.

Lemma value_fields_roots_within_union_r :
  forall roots_old roots_new fields,
    value_fields_roots_within roots_new fields ->
    value_fields_roots_within (root_set_union roots_old roots_new) fields.
Proof.
  intros roots_old roots_new fields Hwithin.
  eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
  - exact Hwithin.
  - intros x Hin. apply root_set_union_in_right. exact Hin.
Qed.

Lemma value_update_path_roots_within_union :
  forall roots_old roots_new v path v_new v',
    value_roots_within roots_old v ->
    value_roots_within roots_new v_new ->
    value_update_path v path v_new = Some v' ->
    value_roots_within (root_set_union roots_old roots_new) v'.
Proof.
  intros roots_old roots_new v path.
  revert roots_old roots_new v.
  induction path as [| f rest IH]; intros roots_old roots_new v v_new v'
    Hwithin_old Hwithin_new Hupdate; simpl in Hupdate.
  - destruct v; simpl in Hupdate; injection Hupdate as Hsame; subst v';
      apply value_roots_within_union_r; exact Hwithin_new.
  - inversion Hwithin_old; subst; try discriminate.
    simpl in Hupdate.
    remember (
      fix update (fields0 : list (string * value)) : option (list (string * value)) :=
        match fields0 with
        | [] => None
        | (name, fv) :: tail =>
            if String.eqb f name
            then match value_update_path fv rest v_new with
                 | Some fv' => Some ((name, fv') :: tail)
                 | None => None
                 end
            else match update tail with
                 | Some tail' => Some ((name, fv) :: tail')
                 | None => None
                 end
        end) as update.
    assert (Hfields :
      forall fs fs',
        value_fields_roots_within roots_old fs ->
        update fs = Some fs' ->
        value_fields_roots_within (root_set_union roots_old roots_new) fs').
    { intros fs. subst update.
      induction fs as [| [fname fv] tail IHfields];
        intros fs' Hfields_roots Hfields_update; simpl in Hfields_update.
      - discriminate.
      - inversion Hfields_roots; subst.
        destruct (String.eqb f fname) eqn:Hname.
        + destruct (value_update_path fv rest v_new) as [fv' |] eqn:Hfv_update;
            try discriminate.
          inversion Hfields_update; subst.
          constructor.
          * eapply IH; eauto.
          * eapply (proj2 (proj2 (proj2 value_roots_within_weaken))).
            -- match goal with
               | H : value_fields_roots_within roots_old tail |- _ => exact H
               end.
            -- intros x Hin. apply root_set_union_in_left. exact Hin.
        + destruct ((
            fix update (fields0 : list (string * value)) : option (list (string * value)) :=
              match fields0 with
              | [] => None
              | (name0, fv0) :: tail0 =>
                  if String.eqb f name0
                  then match value_update_path fv0 rest v_new with
                       | Some fv' => Some ((name0, fv') :: tail0)
                       | None => None
                       end
                  else match update tail0 with
                       | Some tail' => Some ((name0, fv0) :: tail')
                       | None => None
                       end
              end) tail) as [tail' |] eqn:Htail_update; try discriminate.
          inversion Hfields_update; subst.
          constructor.
          * apply value_roots_within_union_l.
            match goal with
            | H : value_roots_within roots_old fv |- _ => exact H
            end.
          * eapply IHfields; eauto. }
    destruct (update fields) as [fields' |] eqn:Hfields_update; try discriminate.
    inversion Hupdate; subst.
    constructor.
    eapply Hfields; eauto.
Qed.

Lemma store_update_val_roots_within_union :
  forall R s x v s' roots_old roots_new,
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_lookup x R = Some roots_old ->
    value_roots_within roots_new v ->
    store_update_val x v s = Some s' ->
    store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) s'.
Proof.
  intros R s x v s' roots_old roots_new Hwithin Hnodup
    Hlookup_x Hvalue Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  unfold store_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  inversion Hentry as [R0 sx sT sv sst roots Hlookup_se Hvalue_se]; subst R0 se.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst sx.
    rewrite ident_eqb_refl in Hupdate.
    rewrite Hlookup_x in Hlookup_se. inversion Hlookup_se; subst roots.
    inversion Hupdate; subst.
    assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT v sst)).
    { exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        x sT v sst (root_set_union roots_old roots_new)
        (root_env_lookup_update_eq x (root_set_union roots_old roots_new)
          R roots_old Hlookup_x)
        (value_roots_within_union_r roots_old roots_new v Hvalue)). }
    assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest).
    { eapply (store_roots_within_update_env_neq R rest x
        (root_set_union roots_old roots_new)).
      * exact Hrest.
      * intros se Hin Hsame.
        apply Hnotin.
        pose proof (store_entry_name_in_store_names se rest Hin) as Hin_name.
        rewrite Hsame in Hin_name. exact Hin_name. }
    exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT v sst) rest Hentry_up Hrest_up).
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail.
    + simpl in Hupdate. rewrite Heq in Hupdate.
      inversion Hupdate; subst.
    assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry sx sT sv sst)).
    { assert (Hlookup_up :
        root_env_lookup sx
          (root_env_update x (root_set_union roots_old roots_new) R) =
        Some roots).
      { rewrite root_env_lookup_update_neq.
        - exact Hlookup_se.
        - intros Hsame. subst sx. rewrite ident_eqb_refl in Heq. discriminate. }
      exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        sx sT sv sst roots Hlookup_up Hvalue_se). }
    assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest').
    { apply IH.
      * unfold store_no_shadow. exact Hnodup_tail.
      * exact Hlookup_x.
      * reflexivity. }
    exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry sx sT sv sst) rest' Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Heq in Hupdate. discriminate.
Qed.

Lemma store_update_path_roots_within_union :
  forall R s x path v_new s' roots_old roots_new,
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_lookup x R = Some roots_old ->
    value_roots_within roots_new v_new ->
    store_update_path x path v_new s = Some s' ->
    store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) s'.
Proof.
  intros R s x path v_new s' roots_old roots_new Hwithin Hnodup
    Hlookup_x Hvalue_new Hupdate.
  revert s' Hupdate.
  induction Hwithin as [R | R se rest Hentry Hrest IH]; intros s' Hupdate;
    simpl in Hupdate; try discriminate.
  unfold store_no_shadow in Hnodup. simpl in Hnodup.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  inversion Hentry as [R0 sx sT sv sst roots Hlookup_se Hvalue_se]; subst R0 se.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst sx.
    rewrite ident_eqb_refl in Hupdate.
    rewrite Hlookup_x in Hlookup_se. inversion Hlookup_se; subst roots.
    destruct (value_update_path sv path v_new) as [sv' |] eqn:Hvalue_update.
    + simpl in Hupdate. rewrite Hvalue_update in Hupdate.
      inversion Hupdate; subst.
      assert (Hentry_up : store_entry_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT sv' sst)).
      { exact (SERW_Entry
        (root_env_update x (root_set_union roots_old roots_new) R)
        x sT sv' sst (root_set_union roots_old roots_new)
        (root_env_lookup_update_eq x (root_set_union roots_old roots_new)
          R roots_old Hlookup_x)
        (value_update_path_roots_within_union
          roots_old roots_new sv path v_new sv'
          Hvalue_se Hvalue_new Hvalue_update)). }
      assert (Hrest_up : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R) rest).
      { eapply (store_roots_within_update_env_neq R rest x
        (root_set_union roots_old roots_new)).
        * exact Hrest.
        * intros se Hin Hsame.
        apply Hnotin.
        pose proof (store_entry_name_in_store_names se rest Hin) as Hin_name.
        rewrite Hsame in Hin_name. exact Hin_name. }
      exact (SRW_Cons
      (root_env_update x (root_set_union roots_old roots_new) R)
      (MkStoreEntry x sT sv' sst) rest Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Hvalue_update in Hupdate. discriminate.
  - destruct (store_update_path x path v_new rest) as [rest' |] eqn:Htail.
    + simpl in Hupdate. rewrite Heq in Hupdate.
      inversion Hupdate; subst.
      assert (Hentry_up : store_entry_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R)
        (MkStoreEntry sx sT sv sst)).
      { assert (Hlookup_up :
          root_env_lookup sx
            (root_env_update x (root_set_union roots_old roots_new) R) =
          Some roots).
        { rewrite root_env_lookup_update_neq.
          - exact Hlookup_se.
          - intros Hsame. subst sx. rewrite ident_eqb_refl in Heq. discriminate. }
        exact (SERW_Entry
          (root_env_update x (root_set_union roots_old roots_new) R)
          sx sT sv sst roots Hlookup_up Hvalue_se). }
      assert (Hrest_up : store_roots_within
        (root_env_update x (root_set_union roots_old roots_new) R) rest').
      { apply IH.
        * unfold store_no_shadow. exact Hnodup_tail.
        * exact Hlookup_x.
        * reflexivity. }
      exact (SRW_Cons
        (root_env_update x (root_set_union roots_old roots_new) R)
        (MkStoreEntry sx sT sv sst) rest' Hentry_up Hrest_up).
    + simpl in Hupdate. rewrite Heq in Hupdate. discriminate.
Qed.

Lemma eval_place_lookup_path_roots_within :
  forall R s p x_static path_static x_eval path_eval old_v roots,
    store_roots_within R s ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    root_env_lookup x_static R = Some roots ->
    value_roots_within roots old_v.
Proof.
  intros R s p x_static path_static x_eval path_eval old_v roots
    Hwithin Hpath_static Heval_place Hlookup_path Hroot_lookup.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  unfold store_lookup_path in Hlookup_path.
  destruct (store_lookup x_static s) as [se |] eqn:Hstore_lookup; try discriminate.
  eapply value_lookup_path_roots_within.
  - eapply store_roots_within_lookup_value; eassumption.
  - exact Hlookup_path.
Qed.

Lemma eval_place_update_path_roots_within_union :
  forall R1 s s1 s2 p x_static path_static x_eval path_eval
      v_new roots_old roots_new,
    store_roots_within R1 s1 ->
    store_no_shadow s1 ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    root_env_lookup x_static R1 = Some roots_old ->
    value_roots_within roots_new v_new ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_roots_within
      (root_env_update x_static (root_set_union roots_old roots_new) R1) s2.
Proof.
  intros R1 s s1 s2 p x_static path_static x_eval path_eval
    v_new roots_old roots_new Hwithin Hnodup Hpath_static Heval_place
    Hroot_lookup Hvalue_new Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  eapply store_update_path_roots_within_union; eassumption.
Qed.

Lemma lookup_alpha_rename_fn_def_typed_structural :
  forall env fname fdef fcall used used',
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    typed_fn_env_structural env fcall.
Proof.
  intros env fname fdef fcall used used' Hlookup Henv_checked Hrename.
  eapply alpha_rename_fn_def_typed_structural_forward.
  - exact Hrename.
  - eapply lookup_fn_checked_structural_params_nodup; eassumption.
  - eapply lookup_fn_checked_structural_typed; eassumption.
Qed.

Lemma typed_fn_env_structural_body :
  forall env f,
    typed_fn_env_structural env f ->
    exists T_body Γ_out,
      typed_env_structural env (fn_outlives f) (fn_lifetimes f)
        (sctx_of_ctx (fn_body_ctx f))
        (fn_body f) T_body (sctx_of_ctx Γ_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Γ_out = true.
Proof.
  intros env f Htyped.
  unfold typed_fn_env_structural in Htyped.
  exact Htyped.
Qed.

Lemma root_env_store_roots_named_to_ctx :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_store_roots_named R s ->
    root_env_ctx_roots_named R Σ.
Proof.
  unfold root_env_store_roots_named, root_env_ctx_roots_named.
  intros env s Σ R Hstore Hnamed x roots z Hlookup Hin.
  rewrite <- (store_typed_names env s Σ Hstore).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_store_keys_named_to_ctx :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_store_keys_named R s ->
    root_env_ctx_keys_named R Σ.
Proof.
  unfold root_env_store_keys_named, root_env_ctx_keys_named.
  intros env s Σ R Hstore Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite <- (store_typed_names env s Σ Hstore).
    exact Hin.
Qed.

Lemma root_env_ctx_keys_named_store_typed :
  forall env s Σ R,
    store_typed env s Σ ->
    root_env_ctx_keys_named R Σ ->
    root_env_store_keys_named R s.
Proof.
  unfold root_env_store_keys_named, root_env_ctx_keys_named.
  intros env s Σ R Hstore Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite (store_typed_names env s Σ Hstore).
    exact Hin.
Qed.

Lemma root_set_store_roots_named_to_ctx :
  forall env s Σ roots,
    store_typed env s Σ ->
    root_set_store_roots_named roots s ->
    root_set_ctx_roots_named roots Σ.
Proof.
  unfold root_set_store_roots_named, root_set_ctx_roots_named.
  intros env s Σ roots Hstore Hnamed z Hin.
  rewrite <- (store_typed_names env s Σ Hstore).
  apply Hnamed. exact Hin.
Qed.

Lemma ctx_names_remove_preserve_neq_root_names :
  forall x y Σ,
    x <> y ->
    In y (ctx_names Σ) ->
    In y (ctx_names (sctx_remove x Σ)).
Proof.
  unfold sctx_remove.
  intros x y Σ Hneq.
  induction Σ as [| [[[z T] st] m] rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y.
      destruct (ident_eqb x z) eqn:Hxz.
      * apply ident_eqb_eq in Hxz. exfalso. apply Hneq. exact Hxz.
      * simpl. left. reflexivity.
    + destruct (ident_eqb x z).
      * exact Hin.
      * simpl. right. apply IH. exact Hin.
Qed.

Lemma root_set_ctx_roots_named_remove_ctx_excluding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots (sctx_remove x Σ).
Proof.
  unfold root_set_ctx_roots_named, roots_exclude.
  intros roots Σ x Hexclude Hnamed z Hin.
  apply ctx_names_remove_preserve_neq_root_names.
  - intros Heq. subst z. apply Hexclude. exact Hin.
  - apply Hnamed. exact Hin.
Qed.

Lemma root_env_ctx_roots_named_remove_ctx_excluding :
  forall R Σ x,
    (forall y roots,
      root_env_lookup y R = Some roots ->
      roots_exclude x roots) ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R (sctx_remove x Σ).
Proof.
  unfold root_env_ctx_roots_named, roots_exclude.
  intros R Σ x Hexclude Hnamed y roots z Hlookup Hin.
  apply ctx_names_remove_preserve_neq_root_names.
  - intros Heq. subst z. eapply Hexclude; eassumption.
  - eapply Hnamed; eassumption.
Qed.

Lemma sctx_lookup_in_ctx_names_root_names :
  forall x Σ T st,
    sctx_lookup x Σ = Some (T, st) ->
    In x (ctx_names Σ).
Proof.
  unfold sctx_lookup.
  intros x Σ.
  induction Σ as [| [[[y Ty] sty] my] rest IH]; intros T st Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    left. reflexivity.
  - right. eapply IH. exact Hlookup.
Qed.

Lemma typed_place_type_root_name_in_ctx_names :
  forall env Σ p T,
    typed_place_type_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_root_names. exact H.
  - exact IHHtyped.
  - exact IHHtyped.
Qed.

Lemma typed_place_root_name_in_ctx_names :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    In (root_provenance_place_name p) (ctx_names Σ).
Proof.
  intros env Σ p T Htyped.
  induction Htyped; simpl.
  - eapply sctx_lookup_in_ctx_names_root_names. exact H.
  - exact IHHtyped.
  - eapply typed_place_type_root_name_in_ctx_names. exact H.
  - eapply typed_place_type_root_name_in_ctx_names. exact H.
Qed.

Lemma root_of_place_ctx_roots_named :
  forall env Σ p T,
    typed_place_env_structural env Σ p T ->
    root_set_ctx_roots_named (root_of_place p) Σ.
Proof.
  intros env Σ p T Htyped.
  unfold root_of_place.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - apply root_set_ctx_roots_named_single.
    destruct (typed_place_direct_lookup env Σ p T x path Htyped Hpath)
      as [T_root [st [Hlookup _]]].
    eapply sctx_lookup_in_ctx_names_root_names. exact Hlookup.
  - apply root_set_ctx_roots_named_single.
    eapply typed_place_root_name_in_ctx_names. exact Htyped.
Qed.

Lemma root_env_lookup_ctx_roots_named :
  forall R Σ x roots,
    root_env_lookup x R = Some roots ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ.
Proof.
  unfold root_env_ctx_roots_named, root_set_ctx_roots_named.
  intros R Σ x roots Hlookup Hnamed z Hin.
  eapply Hnamed; eassumption.
Qed.

Lemma root_set_ctx_roots_named_same_bindings :
  forall roots Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  unfold root_set_ctx_roots_named.
  intros roots Σ Σ' Hsame Hnamed z Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  apply Hnamed. exact Hin.
Qed.

Lemma root_env_ctx_roots_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R Σ'.
Proof.
  unfold root_env_ctx_roots_named.
  intros R Σ Σ' Hsame Hnamed x roots z Hlookup Hin.
  rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
  eapply Hnamed; eassumption.
Qed.

Lemma root_env_ctx_keys_named_same_bindings :
  forall R Σ Σ',
    sctx_same_bindings Σ Σ' ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R Σ'.
Proof.
  unfold root_env_ctx_keys_named.
  intros R Σ Σ' Hsame Hkeys.
  eapply root_env_keys_named_weaken.
  - exact Hkeys.
  - intros x Hin.
    rewrite (sctx_same_bindings_names_alpha Σ Σ' Hsame).
    exact Hin.
Qed.

Lemma root_set_ctx_roots_named_consume_path :
  forall roots Σ x path Σ',
    sctx_consume_path Σ x path = infer_ok Σ' ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  intros roots Σ x path Σ' Hconsume Hnamed.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply sctx_consume_path_same_bindings. exact Hconsume.
  - exact Hnamed.
Qed.

Lemma root_env_lookup_ctx_roots_named_consume_path :
  forall R Σ y roots x path Σ',
    root_env_lookup y R = Some roots ->
    root_env_ctx_roots_named R Σ ->
    sctx_consume_path Σ x path = infer_ok Σ' ->
    root_set_ctx_roots_named roots Σ'.
Proof.
  intros R Σ y roots x path Σ' Hlookup Henv_named Hconsume.
  eapply root_set_ctx_roots_named_consume_path.
  - exact Hconsume.
  - eapply root_env_lookup_ctx_roots_named; eassumption.
Qed.

Lemma root_env_ctx_roots_named_add_binding :
  forall R Σ x T m roots,
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots Σ ->
    root_env_ctx_roots_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Henv Hroots.
  apply root_env_ctx_roots_named_add_env_named.
  - eapply root_env_ctx_roots_named_weaken_ctx.
    + exact Henv.
    + intros z Hin. simpl. right. exact Hin.
  - eapply root_set_ctx_roots_named_weaken_ctx.
    + exact Hroots.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_ctx_keys_named_add_binding :
  forall R Σ x T m roots,
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_add x roots R)
      (sctx_add x T m Σ).
Proof.
  intros R Σ x T m roots Hkeys.
  unfold root_env_ctx_keys_named.
  apply root_env_keys_named_add.
  - simpl. left. reflexivity.
  - eapply root_env_keys_named_weaken.
    + exact Hkeys.
    + intros z Hin. simpl. right. exact Hin.
Qed.

Lemma root_env_remove_excludes_roots_exclude :
  forall R x y roots,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_lookup y (root_env_remove x R) = Some roots ->
    roots_exclude x roots.
Proof.
  intros R x y roots Hrn Hexcl Hlookup.
  apply Hexcl with (y := y).
  - exact Hlookup.
  - intros Heq. subst y.
    rewrite root_env_lookup_remove_eq_no_shadow in Hlookup by exact Hrn.
    discriminate.
Qed.

Lemma root_env_ctx_roots_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_excludes x (root_env_remove x R) ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  intros R Σ x Hrn Hexcl Henv.
  apply root_env_ctx_roots_named_remove_ctx_excluding.
  - intros y roots Hlookup.
    eapply root_env_remove_excludes_roots_exclude; eassumption.
  - apply root_env_ctx_roots_named_remove_env; assumption.
Qed.

Lemma root_env_ctx_keys_named_remove_binding :
  forall R Σ x,
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_remove x R) (sctx_remove x Σ).
Proof.
  unfold root_env_ctx_keys_named.
  intros R Σ x Hrn Hkeys.
  induction R as [| [z roots] rest IH]; intros y Hin; simpl in *;
    try contradiction.
  unfold root_env_no_shadow in Hrn. simpl in Hrn.
  inversion Hrn as [| ? ? Hz_notin Hrn_tail]; subst.
  destruct (ident_eqb x z) eqn:Hxz.
  - apply ident_eqb_eq in Hxz. subst z.
    apply ctx_names_remove_preserve_neq_root_names.
    + intros Heq. subst y. contradiction.
    + apply Hkeys. right. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hy | Hin].
    + subst y.
      apply ctx_names_remove_preserve_neq_root_names.
      * intros Heq. subst z. rewrite ident_eqb_refl in Hxz. discriminate.
      * apply Hkeys. left. reflexivity.
    + apply IH.
      * exact Hrn_tail.
      * intros w Hw. apply Hkeys. right. exact Hw.
      * exact Hin.
Qed.

Lemma root_set_ctx_roots_named_remove_binding :
  forall roots Σ x,
    roots_exclude x roots ->
    root_set_ctx_roots_named roots Σ ->
    root_set_ctx_roots_named roots (sctx_remove x Σ).
Proof.
  intros roots Σ x Hexcl Hroots.
  apply root_set_ctx_roots_named_remove_ctx_excluding; assumption.
Qed.

Lemma root_env_ctx_roots_named_update_union :
  forall R Σ x roots_old roots_new,
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_set_ctx_roots_named roots_old Σ ->
    root_set_ctx_roots_named roots_new Σ ->
    root_env_ctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ.
Proof.
  intros R Σ x roots_old roots_new Hrn Henv Hold Hnew.
  apply root_env_ctx_roots_named_update_env_named.
  - exact Hrn.
  - exact Henv.
  - apply root_set_ctx_roots_named_union; assumption.
Qed.

Lemma root_env_ctx_keys_named_update :
  forall R Σ x roots,
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named (root_env_update x roots R) Σ.
Proof.
  intros R Σ x roots Hkeys.
  unfold root_env_ctx_keys_named.
  apply root_env_keys_named_update.
  exact Hkeys.
Qed.

Lemma root_env_ctx_roots_named_update_union_restore_path :
  forall R Σ1 Σ2 x path roots_old roots_new,
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ1 ->
    root_set_ctx_roots_named roots_old Σ1 ->
    root_set_ctx_roots_named roots_new Σ1 ->
    root_env_ctx_roots_named
      (root_env_update x (root_set_union roots_old roots_new) R) Σ2.
Proof.
  intros R Σ1 Σ2 x path roots_old roots_new Hrestore Hrn Henv Hold Hnew.
  eapply root_env_ctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - apply root_env_ctx_roots_named_update_union; assumption.
Qed.

Lemma root_env_lookup_result_ctx_roots_named_after_typed :
  forall env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_ctx_roots_named R Σ ->
    typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    root_set_ctx_roots_named roots_result Σ1.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 R1 roots_new x roots_result
    Hlookup Henv Htyped.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped.
  - eapply root_env_lookup_ctx_roots_named; eassumption.
Qed.

Lemma root_env_lookup_result_ctx_roots_named_after_typed_restore_path :
  forall env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
      roots_result,
    root_env_lookup x R = Some roots_result ->
    root_env_ctx_roots_named R Σ ->
    typed_env_roots env Ω n R Σ e_new T_new Σ1 R1 roots_new ->
    sctx_restore_path Σ1 x path = infer_ok Σ2 ->
    root_set_ctx_roots_named roots_result Σ2.
Proof.
  intros env Ω n R Σ e_new T_new Σ1 Σ2 R1 roots_new x path
    roots_result Hlookup Henv Htyped Hrestore.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply sctx_restore_path_same_bindings. exact Hrestore.
  - eapply root_env_lookup_result_ctx_roots_named_after_typed;
      eassumption.
Qed.

Lemma root_store_single_ctx_roots_named_of_place_path :
  forall env Σ p T x path,
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x, path) ->
    root_set_ctx_roots_named [RStore x] Σ.
Proof.
  intros env Σ p T x path Htyped Hpath.
  apply root_set_ctx_roots_named_single.
  destruct (typed_place_direct_lookup env Σ p T x path Htyped Hpath)
    as [T_root [st [Hlookup _]]].
  eapply sctx_lookup_in_ctx_names_root_names. exact Hlookup.
Qed.

Lemma root_set_ctx_roots_named_ctx_merge_left :
  forall roots Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots Σ2 ->
    root_set_ctx_roots_named roots Σ4.
Proof.
  intros roots Σ2 Σ3 Σ4 Hmerge Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_env_ctx_roots_named_ctx_merge_left :
  forall R Σ2 Σ3 Σ4,
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_env_ctx_roots_named R Σ2 ->
    root_env_ctx_roots_named R Σ4.
Proof.
  intros R Σ2 Σ3 Σ4 Hmerge Henv.
  eapply root_env_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_left. exact Hmerge.
  - exact Henv.
Qed.

Lemma root_set_ctx_roots_named_ctx_merge_right :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots3 Σ3 ->
    root_set_ctx_roots_named roots3 Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply ctx_merge_same_bindings_right.
    + eapply sctx_same_bindings_trans.
      * apply sctx_same_bindings_sym.
        eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact Htyped2.
      * eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact Htyped3.
    + exact Hmerge.
  - exact Hroots.
Qed.

Lemma root_set_ctx_roots_named_if_merge :
  forall env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2
      e3 T3 Σ3 R3 roots3 Σ4,
    typed_env_roots env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 ->
    typed_env_roots env Ω n R1 Σ1 e3 T3 Σ3 R3 roots3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    root_set_ctx_roots_named roots2 Σ2 ->
    root_set_ctx_roots_named roots3 Σ3 ->
    root_set_ctx_roots_named (root_set_union roots2 roots3) Σ4.
Proof.
  intros env Ω n R1 Σ1 e2 T2 Σ2 R2 roots2 e3 T3 Σ3 R3
    roots3 Σ4 Htyped2 Htyped3 Hmerge Hroots2 Hroots3.
  apply root_set_ctx_roots_named_union.
  - eapply root_set_ctx_roots_named_ctx_merge_left; eassumption.
  - eapply root_set_ctx_roots_named_ctx_merge_right.
    + exact Htyped2.
    + exact Htyped3.
    + exact Hmerge.
    + exact Hroots3.
Qed.

Lemma root_set_ctx_roots_named_typed_args_tail :
  forall env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest,
    typed_args_roots env Ω n R1 Σ1 args ps Σ2 R2 roots_rest ->
    root_set_ctx_roots_named roots Σ1 ->
    root_set_ctx_roots_named roots Σ2.
Proof.
  intros env Ω n Σ1 R1 roots args ps Σ2 R2 roots_rest Htyped_args Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_args_env_structural_same_bindings.
    eapply typed_args_roots_structural. exact Htyped_args.
  - exact Hroots.
Qed.

Lemma root_set_ctx_roots_named_typed_fields_tail :
  forall env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest,
    typed_fields_roots env Ω n lts ty_args R1 Σ1 fields defs Σ2 R2
      roots_rest ->
    root_set_ctx_roots_named roots Σ1 ->
    root_set_ctx_roots_named roots Σ2.
Proof.
  intros env Ω n lts ty_args Σ1 R1 roots fields defs Σ2 R2 roots_rest
    Htyped_fields Hroots.
  eapply root_set_ctx_roots_named_same_bindings.
  - eapply typed_fields_env_structural_same_bindings.
    eapply typed_fields_roots_structural. exact Htyped_fields.
  - exact Hroots.
Qed.

Lemma typed_args_roots_arg_roots_length :
  forall env Ω n R Σ args ps Σ' R' arg_roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' arg_roots ->
    List.length arg_roots = List.length ps.
Proof.
  intros env Ω n R Σ args ps Σ' R' arg_roots Htyped_args.
  induction Htyped_args; simpl; auto.
Qed.

Lemma typed_fields_roots_cons_inv_ts :
  forall env Ω n lts args R Σ fields f rest Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields (f :: rest) Σ' R' roots ->
    exists e_field T_field Σ1 R1 roots_field roots_rest,
      lookup_field_b (field_name f) fields = Some e_field /\
      typed_env_roots env Ω n R Σ e_field T_field Σ1 R1 roots_field /\
      ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f) =
        true /\
      typed_fields_roots env Ω n lts args R1 Σ1 fields rest
        Σ' R' roots_rest /\
      roots = root_set_union roots_field roots_rest.
Proof.
  intros env Ω n lts args R Σ fields f rest Σ' R' roots Htyped.
  inversion Htyped; subst.
  exists e_field, T_field, Σ1, R1, roots_field, roots_rest.
  repeat split; assumption.
Qed.

Theorem typed_roots_ctx_roots_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    root_set_ctx_roots_named roots Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    Forall (fun roots => root_set_ctx_roots_named roots Σ') roots) /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_ctx_roots_named R' Σ' /\
    root_set_ctx_roots_named roots Σ').
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; try solve
    [ split; try assumption; apply root_set_ctx_roots_named_nil ].
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split.
    + eapply root_env_ctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_env_lookup_ctx_roots_named_consume_path; eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split.
    + eapply root_env_ctx_roots_named_same_bindings.
      * eapply sctx_consume_path_same_bindings. eassumption.
      * assumption.
    + eapply root_env_lookup_ctx_roots_named_consume_path; eassumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ') ?arg_roots,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IH Hrn Henv) as [Henv_args Hroots_args];
        split; [exact Henv_args | apply root_sets_ctx_roots_named_union; exact Hroots_args]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R' ?Σ' /\
        root_set_ctx_roots_named ?roots ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Henv_add :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_ctx_roots_named_add_binding; assumption. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    split.
    + apply root_env_ctx_roots_named_remove_binding; assumption.
    + apply root_set_ctx_roots_named_remove_binding; assumption.
  - destruct (H H1 H2) as [Henv1 Hroots1].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Henv_add :
      root_env_ctx_roots_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_ctx_roots_named_add_binding; assumption. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    destruct (H0 Hrn_add Henv_add) as [Henv2 Hroots2].
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    split.
    + apply root_env_ctx_roots_named_remove_binding; assumption.
    + apply root_set_ctx_roots_named_remove_binding; assumption.
  - destruct (H H0 H1) as [Henv Hroots].
    split; [exact Henv | apply root_set_ctx_roots_named_nil].
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ1)
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    split.
    + eapply root_env_ctx_roots_named_update_union_restore_path;
        eassumption.
    + eapply root_env_lookup_result_ctx_roots_named_after_typed_restore_path;
        eassumption.
  - destruct (H H0 H1) as [Henv1 Hroots_new].
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hroots_old : root_set_ctx_roots_named roots_old Σ')
      by (eapply root_env_lookup_ctx_roots_named; eassumption).
    split.
    + eapply root_env_ctx_roots_named_update_union; eassumption.
    + apply root_set_ctx_roots_named_nil.
  - split; try assumption.
    eapply root_of_place_ctx_roots_named. eassumption.
  - split; try assumption.
    eapply root_store_single_ctx_roots_named_of_place_path; eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - split; try assumption.
    eapply root_env_lookup_ctx_roots_named; eassumption.
  - match goal with
    | IHcond : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_cond ?Σ1,
      IHthen : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        root_set_ctx_roots_named ?roots2 ?Σ2,
      IHelse : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R3 ?Σ3 /\
        root_set_ctx_roots_named ?roots3 ?Σ3,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHcond Hrn Henv) as [Henv1 _];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHthen Hrn1 Henv1) as [Henv2 Hroots2];
        destruct (IHelse Hrn1 Henv1) as [_ Hroots3];
        split;
        [ eapply root_env_ctx_roots_named_ctx_merge_left; eassumption
        | eapply root_set_ctx_roots_named_if_merge; eassumption ]
    end.
  - split; try assumption. constructor.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots ?Σ1,
      IHargs : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        Forall (fun roots => root_set_ctx_roots_named roots ?Σ2) ?roots_rest,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHargs Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | constructor; [| exact Hroots_rest]];
        eapply root_set_ctx_roots_named_typed_args_tail; eassumption
    end.
  - match goal with
    | IHexpr : root_env_no_shadow ?R ->
        root_env_ctx_roots_named ?R ?Σ ->
        root_env_ctx_roots_named ?R1 ?Σ1 /\
        root_set_ctx_roots_named ?roots_field ?Σ1,
      IHfields : root_env_no_shadow ?R1 ->
        root_env_ctx_roots_named ?R1 ?Σ1 ->
        root_env_ctx_roots_named ?R2 ?Σ2 /\
        root_set_ctx_roots_named ?roots_rest ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_roots_named ?R ?Σ |- _ =>
        destruct (IHexpr Hrn Henv) as [Henv1 Hroot];
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        destruct (IHfields Hrn1 Henv1) as [Henv2 Hroots_rest];
        split; [exact Henv2 | apply root_set_ctx_roots_named_union; [| exact Hroots_rest]];
        eapply root_set_ctx_roots_named_typed_fields_tail; eassumption
    end.
Qed.

Theorem typed_roots_ctx_keys_named_mutual :
  forall env Ω n,
  (forall R Σ e T Σ' R' roots,
    typed_env_roots env Ω n R Σ e T Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ') /\
  (forall R Σ args ps Σ' R' roots,
    typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ') /\
  (forall lts args R Σ fields defs Σ' R' roots,
    typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
    root_env_no_shadow R ->
    root_env_ctx_keys_named R Σ ->
    root_env_ctx_keys_named R' Σ').
Proof.
  intros env Ω n.
  apply typed_roots_ind; intros; try assumption.
  - eapply root_env_ctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - eapply root_env_ctx_keys_named_same_bindings.
    + eapply sctx_consume_path_same_bindings. eassumption.
    + assumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hkeys_add :
      root_env_ctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T m Σ1)).
    { apply root_env_ctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    apply root_env_ctx_keys_named_remove_binding; assumption.
  - pose proof (H H1 H2) as Hkeys1.
    assert (Hrn1 : root_env_no_shadow R1)
      by (eapply typed_env_roots_no_shadow; eassumption).
    assert (Hkeys_add :
      root_env_ctx_keys_named (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1)).
    { apply root_env_ctx_keys_named_add_binding. exact Hkeys1. }
    assert (Hrn_add : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    pose proof (H0 Hrn_add Hkeys_add) as Hkeys2.
    assert (Hrn2 : root_env_no_shadow R2)
      by (eapply typed_env_roots_no_shadow; eassumption).
    apply root_env_ctx_keys_named_remove_binding; assumption.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        exact (IH Hrn Henv)
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hrestore : sctx_restore_path ?Σ1 ?x ?path = infer_ok ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        eapply root_env_ctx_keys_named_same_bindings;
        [ eapply sctx_restore_path_same_bindings; exact Hrestore
        | exact (IH Hrn Henv) ]
    end.
  - match goal with
    | IH : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ',
      Hrn : root_env_no_shadow ?R,
      Henv : root_env_ctx_keys_named ?R ?Σ |- _ =>
        apply root_env_ctx_keys_named_update;
        exact (IH Hrn Henv)
    end.
  - repeat match goal with
    | Hstep : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R' ?Σ',
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        let Hkeys' := fresh "Hkeys_step" in
        let Hrn' := fresh "Hrn_step" in
        pose proof (Hstep Hrn Hkeys) as Hkeys';
        assert (Hrn' : root_env_no_shadow R')
          by (eapply typed_env_roots_no_shadow; eassumption);
        clear Hstep
    end.
    eapply root_env_ctx_keys_named_same_bindings.
    + eapply ctx_merge_same_bindings_left. eassumption.
    + eassumption.
  - match goal with
    | Htyped1 : typed_env_roots env Ω n ?R ?Σ _ _ ?Σ1 ?R1 _,
      Hexpr : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hargs : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hexpr Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (Hargs Hrn1 Hkeys1)
    end.
  - match goal with
    | Hfield : root_env_no_shadow ?R ->
        root_env_ctx_keys_named ?R ?Σ ->
        root_env_ctx_keys_named ?R1 ?Σ1,
      Hrest : root_env_no_shadow ?R1 ->
        root_env_ctx_keys_named ?R1 ?Σ1 ->
        root_env_ctx_keys_named ?R2 ?Σ2,
      Hrn : root_env_no_shadow ?R,
      Hkeys : root_env_ctx_keys_named ?R ?Σ |- _ =>
        pose proof (Hfield Hrn Hkeys) as Hkeys1;
        assert (Hrn1 : root_env_no_shadow R1)
          by (eapply typed_env_roots_no_shadow; eassumption);
        exact (Hrest Hrn1 Hkeys1)
    end.
Qed.

Theorem eval_preserves_roots_ready_mutual :
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
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
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
    (forall s args s' vs,
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
    (forall s fields defs s' values,
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
        root_env_no_shadow R')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s i Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s f Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s b Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    dependent destruction Htyped.
    all: repeat split; try assumption;
      eapply store_roots_within_lookup_value; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    dependent destruction Htyped.
    all: repeat split; try (apply store_mark_used_roots_within; exact Hroots);
      try (eapply store_roots_within_lookup_value; eassumption);
      try (apply store_no_shadow_mark_used; exact Hnodup);
      try exact Hrn.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hroots Hnodup Hrn Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    all: repeat split; try assumption;
      match goal with
      | Hpath_typed : place_path ?p_typed = Some (?root, ?path_typed),
        Heval_p : eval_place ?s_typed ?p_typed ?x_eval0 ?path_eval0,
        Hvalue_path : value_lookup_path (se_val ?se0) ?path_eval0 = Some ?v_target,
        Hroot_lookup : root_env_lookup ?root ?Rcur = Some ?roots_cur
        |- value_roots_within ?roots_cur ?v_target =>
          destruct (eval_place_matches_place_path s_typed p_typed x_eval0 path_eval0
                      root path_typed Heval_p Hpath_typed) as [Hx Hpath];
          subst x_eval0 path_eval0;
          eapply value_lookup_path_roots_within;
          [ eapply store_roots_within_lookup_value; eassumption
          | exact Hvalue_path ]
      end.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: repeat split; try exact Hrn;
      try
        (unfold store_consume_path in Hstore_consume;
         destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
           try discriminate;
         destruct (binding_available_b (se_state se0) path_eval);
           try discriminate;
         eapply store_update_state_roots_within; eassumption);
      try
        (unfold store_consume_path in Hstore_consume;
         destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
           try discriminate;
         destruct (binding_available_b (se_state se0) path_eval);
           try discriminate;
         eapply store_no_shadow_update_state; eassumption);
      match goal with
      | Hpath_typed : place_path ?p_typed = Some (?root, ?path_typed),
        Heval_p : eval_place ?s_typed ?p_typed ?x_eval0 ?path_eval0,
        Hvalue_path : value_lookup_path (se_val ?se0) ?path_eval0 = Some ?v_target,
        Hroot_lookup : root_env_lookup ?root ?Rcur = Some ?roots_cur
        |- value_roots_within ?roots_cur ?v_target =>
          destruct (eval_place_matches_place_path s_typed p_typed x_eval0 path_eval0
                      root path_typed Heval_p Hpath_typed) as [Hx Hpath];
          subst x_eval0 path_eval0;
          eapply value_lookup_path_roots_within;
          [ eapply store_roots_within_lookup_value; eassumption
          | exact Hvalue_path ]
      end.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_struct name env = Some ?sdef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst sdef_typed
    end.
    match goal with
    | Hready_fields : provenance_ready_fields fields,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ fields
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hroots Hnodup Hrn Htyped_fields)
          as [Hroots' [Hvals [Hnodup' Hrn']]]
    end.
    repeat split; try assumption.
    constructor. exact Hvals.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready1 : provenance_ready_expr e1,
      Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_expr ?Σ1_expr
        ?R1_expr ?roots1_expr |- _ =>
        destruct (IH1 Ω n R Σ T1_expr Σ1_expr R1_expr roots1_expr
                    Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1 [Hv1 [Hnodup1 Hrn1]]]
    end.
    assert (Hfresh_store : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_ann v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_nodup : store_no_shadow (store_add x T_ann v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    match goal with
    | Hready2 : provenance_ready_expr e2,
      Htyped2 : typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T_ann m Σ1) e2 ?T_body ?Σ2_body ?R2_body
        ?roots2_body |- _ =>
        destruct (IH2 Ω n (root_env_add x roots1 R1)
                    (sctx_add x T_ann m Σ1) T_body Σ2_body R2_body
                    roots2_body Hready2 Hadd_roots Hadd_nodup Hadd_rn Htyped2)
          as [Hroots2 [Hv2 [Hnodup2 Hrn2]]]
    end.
    repeat split.
    + eapply store_remove_roots_within.
      * exact Hroots2.
      * apply store_no_shadow_remove_no_name. exact Hnodup2.
    + exact Hv2.
    + apply store_no_shadow_remove. exact Hnodup2.
    + apply root_env_no_shadow_remove. exact Hrn2.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ_e ?R_e ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ_e R_e roots_e Hready_e
                    Hroots Hnodup Hrn Htyped_e)
          as [Hroots' [_ [Hnodup' Hrn']]]
    end.
    repeat split; try assumption; constructor.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    assert (Hroots2 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s2).
    { eapply store_update_val_roots_within_union; eassumption. }
    assert (Hnodup2 : store_no_shadow s2)
      by (eapply store_no_shadow_update_val; eassumption).
    assert (Hroots3 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s3).
    { unfold store_restore_path in Hrestore.
      eapply store_update_state_roots_within; eassumption. }
    assert (Hnodup3 : store_no_shadow s3).
    { unfold store_restore_path in Hrestore.
      eapply store_no_shadow_update_state; eassumption. }
    repeat split; try assumption.
    + eapply store_roots_within_lookup_value.
      * exact Hroots.
      * exact Hlookup.
      * match goal with
        | Hroot_lookup : root_env_lookup _ R = Some roots |- _ =>
            exact Hroot_lookup
        end.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    repeat split.
    + eapply store_update_val_roots_within_union; eassumption.
    + constructor.
    + eapply store_no_shadow_update_val; eassumption.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    assert (Hroots2 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s2).
    { eapply eval_place_update_path_roots_within_union.
      - exact Hroots1.
      - exact Hnodup1.
      - match goal with
        | Hpath_static : place_path _ = Some _ |- _ =>
            exact Hpath_static
        end.
      - exact Heval_place.
      - exact H7.
      - exact Hvnew.
      - exact Hupdate. }
    assert (Hnodup2 : store_no_shadow s2)
      by (eapply store_no_shadow_update_path; eassumption).
    assert (Hroots3 : store_roots_within
      (root_env_update x (root_set_union roots_old roots_new) R1) s3).
    { unfold store_restore_path in Hrestore.
      eapply store_update_state_roots_within; eassumption. }
    assert (Hnodup3 : store_no_shadow s3).
    { unfold store_restore_path in Hrestore.
      eapply store_no_shadow_update_state; eassumption. }
    repeat split; try assumption.
    + eapply eval_place_lookup_path_roots_within.
      * exact Hroots.
      * match goal with
        | Hpath_static : place_path p = Some (x, path) |- _ =>
            exact Hpath_static
        end.
      * exact Heval_place.
      * exact Hlookup_old.
      * match goal with
        | Hroot_lookup : root_env_lookup x R = Some roots |- _ =>
            exact Hroot_lookup
        end.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new0 ?Σ1_new
        ?R1_new ?roots_new0 |- _ =>
        destruct (IHnew Ω n R Σ T_new0 Σ1_new R1_new roots_new0
                    Hready_new Hroots Hnodup Hrn Htyped_new)
          as [Hroots1 [Hvnew [Hnodup1 Hrn1]]]
    end.
    repeat split.
    + eapply eval_place_update_path_roots_within_union; eassumption.
    + constructor.
    + eapply store_no_shadow_update_path; eassumption.
    + apply root_env_no_shadow_update. exact Hrn1.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + repeat split; try assumption.
      match goal with
      | Hpath_static : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_matches_place_path s p x path
                      x_static path_static Heval_place Hpath_static)
            as [Hx Hpath];
          subst x path;
          unfold root_of_place;
          rewrite Hpath_static;
          constructor; simpl; left; reflexivity
      end.
    + repeat split; try assumption.
      match goal with
      | Hpath_static : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_matches_place_path s p x path
                      x_static path_static Heval_place Hpath_static)
            as [Hx Hpath];
          subst x path;
          constructor; simpl; left; reflexivity
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn
      Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped.
    + repeat split; try assumption.
      match goal with
      | Hevalp : eval_place ?s0 ?p0 ?x0 ?path0,
        Hlookup0 : store_lookup ?x0 ?s0 = Some ?se0,
        Hvalue0 : value_lookup_path (se_val ?se0) ?path0 = Some ?v0 |- _ =>
          assert (Hlookup_path : store_lookup_path x0 path0 s0 = Some v0)
            by (unfold store_lookup_path; rewrite Hlookup0; exact Hvalue0);
          eapply eval_place_lookup_path_roots_within; eassumption
      end.
    + repeat split; try assumption.
      match goal with
      | Hevalp : eval_place ?s0 ?p0 ?x0 ?path0,
        Hlookup0 : store_lookup ?x0 ?s0 = Some ?se0,
        Hvalue0 : value_lookup_path (se_val ?se0) ?path0 = Some ?v0 |- _ =>
          assert (Hlookup_path : store_lookup_path x0 path0 s0 = Some v0)
            by (unfold store_lookup_path; rewrite Hlookup0; exact Hvalue0);
          eapply eval_place_lookup_path_roots_within; eassumption
      end.
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hroots.
    + constructor.
    + exact Hnodup.
    + exact Hrn.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R' roots
      Hready _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond0 ?Σ1_cond
        ?R1_cond ?roots_cond0 |- _ =>
        destruct (IHcond Ω n R Σ T_cond0 Σ1_cond R1_cond roots_cond0
                    Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]]
    end.
    match goal with
    | Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1_cond ?Σ1_cond e2
        ?T2_then ?Σ2_then ?R2_then ?roots2_then |- _ =>
        destruct (IHthen Ω n R1_cond Σ1_cond T2_then Σ2_then R2_then
                    roots2_then Hready_then Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hroots2 [Hv2 [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    + apply value_roots_within_union_l. exact Hv2.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond0 ?Σ1_cond
        ?R1_cond ?roots_cond0 |- _ =>
        destruct (IHcond Ω n R Σ T_cond0 Σ1_cond R1_cond roots_cond0
                    Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]]
    end.
    match goal with
    | Hready_else : provenance_ready_expr e3,
      Htyped_else : typed_env_roots env Ω n ?R1_cond ?Σ1_cond e3
        ?T3_else ?Σ3_else ?R3_else ?roots3_else |- _ =>
	        destruct (IHelse Ω n R1_cond Σ1_cond T3_else Σ3_else R3_else
	                    roots3_else Hready_else Hroots1 Hnodup1 Hrn1 Htyped_else)
	          as [Hroots3 [Hv3 [Hnodup3 Hrn3]]]
	    end.
	    assert (Hrn2 : root_env_no_shadow R')
	      by (eapply typed_env_roots_no_shadow; eassumption).
	    assert (Hroots3_out : store_roots_within R' s2).
	    { eapply store_roots_within_equiv.
	      - apply root_env_equiv_sym. eassumption.
	      - exact Hroots3. }
	    repeat split.
	    + exact Hroots3_out.
	    + apply value_roots_within_union_r. exact Hv3.
	    + exact Hnodup3.
	    + exact Hrn2.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots Hready _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1_e ?R1_e ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1_e ?Σ1_e es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1_e R1_e roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [Hv [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1_e Σ1_e ps_rest Σ' R' roots_rest
                    Hready_rest Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hroots2 [Hvs [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    constructor; assumption.
  - intros s Ω n lts args0 R Σ Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots Hready
      Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1_field
        ?R1_field ?roots_field,
      Htyped_rest : typed_fields_roots env Ω n lts args0 ?R1_field ?Σ1_field
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1_field R1_field roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [Hv [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args0 R1_field Σ1_field Σ' R' roots_rest
                    Hready Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hroots2 [Hvals [Hnodup2 Hrn2]]]
    end.
    repeat split; try assumption.
    constructor.
    + apply value_roots_within_union_l. exact Hv.
    + apply value_fields_roots_within_union_r. exact Hvals.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hroots Hnodup Hrn Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hroots Hnodup Hrn Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Lemma store_param_prefix_remove_non_param :
  forall ps s_param s x,
    store_param_prefix ps s_param s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_param_prefix ps (store_remove x s_param) (store_remove x s).
Proof.
  intros ps s_param s x Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH]; intros Hnotin.
  - constructor.
  - simpl in Hnotin.
    simpl.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin. left. reflexivity.
    + constructor. apply IH.
      intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_param_scope_remove_non_param :
  forall ps s_param s x,
    store_param_scope ps s_param s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    exists frame',
      store_param_scope ps (store_remove x s_param) frame'.
Proof.
  intros ps s_param s x Hscope Hnotin.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH].
  - exists (store_remove x s).
    constructor.
    eapply store_param_prefix_remove_non_param; eassumption.
  - simpl.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + exists s. exact Hscope_tail.
    + destruct (IH Hnotin) as [frame' Hscope'].
      exists frame'.
      constructor; assumption.
Qed.


Lemma store_param_prefix_update_state :
  forall ps s_param s x f s',
    store_param_prefix ps s_param s ->
    store_update_state x f s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x f s' Hprefix.
  revert x f s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x f s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_state x f s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x f s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_mark_used :
  forall ps s_param s x,
    store_param_prefix ps s_param s ->
    exists frame',
      store_param_prefix ps (store_mark_used x s_param) frame'.
Proof.
  intros ps s_param s x Hprefix.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH].
  - exists (store_mark_used x s). constructor.
  - simpl.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + exists s. constructor. exact Hprefix_tail.
    + destruct IH as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_update_val :
  forall ps s_param s x v_new s',
    store_param_prefix ps s_param s ->
    store_update_val x v_new s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x v_new s' Hprefix.
  revert x v_new s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x v_new s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_val x v_new s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x v_new s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_update_path :
  forall ps s_param s x path v_new s',
    store_param_prefix ps s_param s ->
    store_update_path x path v_new s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path v_new s' Hprefix.
  revert x path v_new s'.
  induction Hprefix as [s | p ps v st s_param s Hprefix_tail IH];
    intros x path v_new s' Hupdate.
  - exists s'. constructor.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Hx.
    + destruct (value_update_path v path v_new) as [v' |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst s'.
      exists s. constructor. exact Hprefix_tail.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x path v_new s_param' Htail) as [frame' Hprefix'].
      exists frame'. constructor. exact Hprefix'.
Qed.

Lemma store_param_prefix_restore_path :
  forall ps s_param s x path s',
    store_param_prefix ps s_param s ->
    store_restore_path x path s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path s' Hprefix Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_param_prefix_update_state; eassumption.
Qed.

Lemma store_param_prefix_consume_path :
  forall ps s_param s x path s',
    store_param_prefix ps s_param s ->
    store_consume_path x path s_param = Some s' ->
    exists frame',
      store_param_prefix ps s' frame'.
Proof.
  intros ps s_param s x path s' Hprefix Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_param_prefix_update_state; eassumption.
Qed.

Lemma store_param_scope_update_state :
  forall ps s_param s x f s',
    store_param_scope ps s_param s ->
    store_update_state x f s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x f s' Hscope.
  revert x f s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x f s' Hupdate.
  - destruct (store_param_prefix_update_state
      ps s_param s x f s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_state x f s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x f s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_mark_used :
  forall ps s_param s x,
    store_param_scope ps s_param s ->
    exists frame',
      store_param_scope ps (store_mark_used x s_param) frame'.
Proof.
  intros ps s_param s x Hscope.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH].
  - destruct (store_param_prefix_mark_used
      ps s_param s x Hprefix) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + exists s. constructor; assumption.
    + destruct IH as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_update_val :
  forall ps s_param s x v_new s',
    store_param_scope ps s_param s ->
    store_update_val x v_new s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x v_new s' Hscope.
  revert x v_new s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x v_new s' Hupdate.
  - destruct (store_param_prefix_update_val
      ps s_param s x v_new s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_val x v_new s_param) as [s_param' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x v_new s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_update_path :
  forall ps s_param s x path v_new s',
    store_param_scope ps s_param s ->
    store_update_path x path v_new s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path v_new s' Hscope.
  revert x path v_new s'.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s Hse_notin Hscope_tail IH];
    intros x path v_new s' Hupdate.
  - destruct (store_param_prefix_update_path
      ps s_param s x path v_new s' Hprefix Hupdate) as [frame' Hprefix'].
    exists frame'. constructor. exact Hprefix'.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Hx.
    + destruct (value_update_path (se_val se) path v_new) as [v' |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst s'.
      exists s. constructor; assumption.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH x path v_new s_param' Htail) as [frame' Hscope'].
      exists frame'. constructor; assumption.
Qed.

Lemma store_param_scope_restore_path :
  forall ps s_param s x path s',
    store_param_scope ps s_param s ->
    store_restore_path x path s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path s' Hscope Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_param_scope_update_state; eassumption.
Qed.

Lemma store_param_scope_consume_path :
  forall ps s_param s x path s',
    store_param_scope ps s_param s ->
    store_consume_path x path s_param = Some s' ->
    exists frame',
      store_param_scope ps s' frame'.
Proof.
  intros ps s_param s x path s' Hscope Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_param_scope_update_state; eassumption.
Qed.

Theorem eval_preserves_param_scope_roots_ready_mutual :
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
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
          ps frame,
        provenance_ready_expr e ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ params Σ' R' roots
          ps frame,
        provenance_ready_args args ->
        typed_args_roots env Ω n R Σ args params Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots
          ps frame,
        provenance_ready_fields fields ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        root_env_covers_params ps R ->
        store_param_scope ps s frame ->
        root_env_covers_params ps R' /\
        exists frame', store_param_scope ps s' frame')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s i Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s f Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s b Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover Hscope.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst.
    all: split; [exact Hcover | eapply store_param_scope_mark_used; exact Hscope].
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      ps frame Hready Htyped Hcover Hscope.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: split; [exact Hcover | eapply store_param_scope_consume_path; eassumption].
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_struct name env = Some ?sdef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst sdef_typed
    end.
    match goal with
    | Hready_fields : provenance_ready_fields fields,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ fields
        (struct_fields sdef) Σ' R' roots |- _ =>
        exact (IHfields Ω n lts args R Σ Σ' R' roots ps frame
          Hready_fields Htyped_fields Hcover Hscope)
    end.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IH1 Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption) Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    pose proof (root_env_covers_params_lookup_none_not_in
                  ps _ x Hcover1 ltac:(eassumption)) as Hnotin.
    pose proof (root_env_covers_params_add
                  ps _ x roots1 Hcover1) as Hcover_add.
    pose proof (store_param_scope_add
                  ps s1 frame1 x T_ann v1 Hnotin Hscope1) as Hscope_add.
    destruct (IH2 Ω n _ _ _ _ _ _ ps frame1
                ltac:(eassumption) ltac:(eassumption)
                Hcover_add Hscope_add)
      as [Hcover2 [frame2 Hscope2]].
    split.
    + eapply root_env_covers_params_remove_non_param; eassumption.
    + eapply store_param_scope_remove_non_param; eassumption.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        exact (IH Ω n R Σ T_e Σ' R' roots_e ps frame
                 Hready_e Htyped_e Hcover Hscope)
    end.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_val
                    ps s1 frame1 x v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        destruct (store_param_scope_restore_path
                    ps s2 frame2 x [] s3 Hscope2 Hrestore)
          as [frame3 Hscope3];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame3; exact Hscope3 ]
    end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_val
                    ps s1 frame1 x v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame2; exact Hscope2 ]
    end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_path
                    ps s1 frame1 x_eval path_eval v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        destruct (store_param_scope_restore_path
                    ps s2 frame2 x_eval path_eval s3 Hscope2 Hrestore)
          as [frame3 Hscope3];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame3; exact Hscope3 ]
    end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    assert (Hready_new : provenance_ready_expr e_new) by assumption.
    match goal with
    | Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        destruct (store_param_scope_update_path
                    ps s1 frame1 x_eval path_eval v_new s2 Hscope1 Hupdate)
          as [frame2 Hscope2];
        split;
        [ apply root_env_covers_params_update; exact Hcover1
        | exists frame2; exact Hscope2 ]
    end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    all: split; [exact Hcover | exists frame; exact Hscope].
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame Hready _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Heval_r; subst.
    inversion Htyped; subst;
      try solve [split; [exact Hcover | exists frame; exact Hscope]].
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 Htyped1 Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    exact (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2 ps frame1
             Hready2 Htyped2 Hcover1 Hscope1).
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    dependent destruction Htyped.
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 Htyped1 Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3 ps frame1
                Hready3 Htyped3 Hcover1 Hscope1)
      as [Hcover3 [frame3 Hscope3]].
    split.
    + eapply root_env_covers_params_equiv.
      * apply root_env_equiv_sym. exact H2.
      * exact Hcover3.
    + exists frame3. exact Hscope3.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots ps frame Hready _ _ _.
    inversion Hready.
  - intros s Ω n R Σ params Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ params Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?params_rest
        ?Σ2 ?R2 ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e ps frame
                    Hready_e Htyped_e Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        exact (IHrest Ω n R1 Σ1 params_rest Σ' R' roots_rest ps frame1
                 Hready_rest Htyped_rest Hcover1 Hscope1)
    end.
  - intros s Ω n lts args0 R Σ Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots ps frame
      Hready Htyped Hcover Hscope.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    destruct (typed_fields_roots_cons_inv_ts env Ω n lts args0 R Σ
                fields f rest Σ' R' roots Htyped)
      as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
    rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
    rewrite Hlookup_typed in Hlookup_expr.
    inversion Hlookup_expr; subst e_field.
    destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                Hready_field Htyped_field Hcover Hscope)
      as [Hcover1 [frame1 Hscope1]].
    exact (IHrest Ω n lts args0 R1 Σ1 Σ' R' roots_rest ps frame1
             Hready Htyped_rest Hcover1 Hscope1).
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0'
      roots0 ps0 frame0 Hready Htyped Hcover Hscope.
    destruct (Hmut env0) as [Hexpr [_ _]].
    destruct (Hexpr s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0'
                roots0 ps0 frame0 Hready Htyped Hcover Hscope)
      as [_ Hscope'].
    exact Hscope'.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 params0
        Σ0' R0' roots0 ps0 frame0 Hready Htyped Hcover Hscope.
      destruct (Hmut env0) as [_ [Hargs _]].
      destruct (Hargs s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 params0
                  Σ0' R0' roots0 ps0 frame0 Hready Htyped Hcover Hscope)
        as [_ Hscope'].
      exact Hscope'.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 ps0 frame0 Hready Htyped
        Hcover Hscope.
      destruct (Hmut env0) as [_ [_ Hfields]].
      destruct (Hfields s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
                  args0 R0 Σ0 Σ0' R0' roots0 ps0 frame0 Hready Htyped
                  Hcover Hscope)
        as [_ Hscope'].
      exact Hscope'.
Qed.

Definition frame_scope_roots_ready_result
    (ps : list param) (R : root_env) (Σ : sctx) (s : store)
    (frame : store) : Prop :=
  root_env_covers_params ps R /\
  store_roots_within R s /\
  store_no_shadow s /\
  root_env_no_shadow R /\
  store_frame_scope ps Σ s frame /\
  store_frame_static_fresh Σ frame.

Definition frame_scope_roots_ready_expr_preservation : Prop :=
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
        ps frame,
      provenance_ready_expr e ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      root_env_covers_params ps R ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      store_frame_scope ps Σ s frame ->
      store_frame_static_fresh Σ frame ->
      frame_scope_roots_ready_result ps R' Σ' s' frame.

Theorem eval_preserves_frame_scope_roots_ready_args_fields_from_expr :
  frame_scope_roots_ready_expr_preservation ->
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
Proof.
  intros Hexpr.
  split.
  - intros env s args s' vs Heval.
    induction Heval as [s | s s1 s2 e es v vs Heval_e Heval_rest IHrest];
      intros Ω n R Σ params Σ' R' roots ps frame Hready Htyped
        Hcover Hroots Hshadow Hrn Hscope Hfresh.
    + inversion Htyped; subst.
      repeat split; assumption.
    + dependent destruction Hready.
      dependent destruction Htyped.
      match goal with
      | Hready_e : provenance_ready_expr _,
        Hready_rest : provenance_ready_args _,
        Htyped_e : typed_env_roots env Ω n R Σ _ ?T_e ?Σ1 ?R1 ?roots_e,
        Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 _ ?params_rest
          ?Σ2 ?R2 ?roots_rest |- _ =>
          destruct (Hexpr env s e s1 v Heval_e Ω n R Σ T_e Σ1 R1
                      roots_e ps frame Hready_e Htyped_e Hcover Hroots
                      Hshadow Hrn Hscope Hfresh)
            as [Hcover1 [Hroots1 [Hshadow1 [Hrn1 [Hscope1 Hfresh1]]]]];
          exact (IHrest Ω n R1 Σ1 params_rest Σ2 R2 roots_rest ps frame
                   Hready_rest Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                   Hscope1 Hfresh1)
      end.
  - intros env s fields defs s' values Heval.
    induction Heval as
      [s | s s1 s2 fields f rest e v values Hlookup_expr Heval_field
        Heval_rest IHrest];
      intros Ω n lts args R Σ Σ' R' roots ps frame Hready Htyped
        Hcover Hroots Hshadow Hrn Hscope Hfresh.
    + inversion Htyped; subst.
      repeat split; assumption.
    + pose proof (provenance_ready_fields_lookup fields (field_name f) e
                    Hready Hlookup_expr) as Hready_field.
      destruct (typed_fields_roots_cons_inv_ts env Ω n lts args R Σ
                  fields f rest Σ' R' roots Htyped)
        as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
      rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
      rewrite Hlookup_typed in Hlookup_expr.
      inversion Hlookup_expr; subst e_field.
      destruct (Hexpr env s e s1 v Heval_field Ω n R Σ T_field Σ1
                  R1 roots_field ps frame Hready_field Htyped_field
                  Hcover Hroots Hshadow Hrn Hscope Hfresh)
        as [Hcover1 [Hroots1 [Hshadow1 [Hrn1 [Hscope1 Hfresh1]]]]].
      exact (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest ps frame
               Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
               Hscope1 Hfresh1).
Qed.

Lemma store_param_prefix_update_state_same_frame :
  forall ps s_param frame x f s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_state x f s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x f s' Hprefix.
  revert x f s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x f s' Hnotin Hupdate.
  - rewrite store_update_state_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_state x f s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_mark_used_same_frame :
  forall ps s_param frame x,
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_param_prefix ps (store_mark_used x s_param) frame.
Proof.
  intros ps s_param frame x Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hnotin.
  - rewrite store_mark_used_not_in_names; [constructor | exact Hnotin].
  - simpl. destruct (ident_eqb x (param_name p)); constructor.
    + exact Hprefix.
    + apply IH. exact Hnotin.
Qed.

Lemma store_param_prefix_update_val_same_frame :
  forall ps s_param frame x v_new s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_val x v_new s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x v_new s' Hprefix.
  revert x v_new s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x v_new s' Hnotin Hupdate.
  - rewrite store_update_val_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_val x v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_update_path_same_frame :
  forall ps s_param frame x path v_new s',
    store_param_prefix ps s_param frame ->
    ~ In x (store_names frame) ->
    store_update_path x path v_new s_param = Some s' ->
    store_param_prefix ps s' frame.
Proof.
  intros ps s_param frame x path v_new s' Hprefix.
  revert x path v_new s'.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros x path v_new s' Hnotin Hupdate.
  - rewrite store_update_path_not_in_names in Hupdate; try assumption.
    discriminate.
  - simpl in Hupdate.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + destruct (value_update_path v path v_new) as [v' |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst. constructor. exact Hprefix.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst. constructor.
      eapply IH; eassumption.
Qed.

Lemma store_param_prefix_remove_non_param_same_frame :
  forall ps s_param frame x,
    store_param_prefix ps s_param frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names frame) ->
    store_param_prefix ps (store_remove x s_param) frame.
Proof.
  intros ps s_param frame x Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hnotin_param Hnotin_frame.
  - rewrite store_remove_not_in_names; [constructor | exact Hnotin_frame].
  - simpl in Hnotin_param.
    simpl. destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      contradiction Hnotin_param. left. reflexivity.
    + constructor. apply IH.
      * intros Hin. apply Hnotin_param. right. exact Hin.
      * exact Hnotin_frame.
Qed.

Lemma store_frame_scope_update_state :
  forall ps Σ s_param frame x f s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_state x f s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x f s' HinΣ Hfresh Hscope.
  revert x f s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x f s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_state_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_state x f s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2.
      * exact Hnotin.
      * exact Hin_se.
      * eapply IH.
        -- exact Hfresh.
        -- exact HinΣ.
        -- exact Htail.
Qed.

Lemma store_frame_scope_mark_used :
  forall ps Σ s_param frame x,
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_frame_scope ps Σ (store_mark_used x s_param) frame.
Proof.
  intros ps Σ s_param frame x HinΣ Hfresh Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_mark_used_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
  - simpl.
    destruct (ident_eqb x (se_name se)).
    + econstructor; eassumption.
    + econstructor 2.
      * exact Hnotin.
      * exact Hin_se.
      * exact (IH Hfresh).
Qed.

Lemma store_frame_scope_update_val :
  forall ps Σ s_param frame x v_new s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_val x v_new s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x v_new s' HinΣ Hfresh Hscope.
  revert x v_new s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x v_new s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_val_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_val x v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2; try eassumption.
      eapply IH; eassumption.
Qed.

Lemma store_frame_scope_update_path :
  forall ps Σ s_param frame x path v_new s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_update_path x path v_new s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path v_new s' HinΣ Hfresh Hscope.
  revert x path v_new s' HinΣ.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin Hin_se Hscope_tail IH];
    intros x path v_new s' HinΣ Hupdate.
  - constructor.
    eapply store_param_prefix_update_path_same_frame.
    + exact Hprefix.
    + apply Hfresh. exact HinΣ.
    + exact Hupdate.
  - simpl in Hupdate.
    destruct (ident_eqb x (se_name se)) eqn:Heq.
    + destruct (value_update_path (se_val se) path v_new) as [v' |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst.
      econstructor; eassumption.
    + destruct (store_update_path x path v_new s_param) as [s_param' |]
        eqn:Htail; try discriminate.
      inversion Hupdate; subst.
      econstructor 2; try eassumption.
      eapply IH; eassumption.
Qed.

Lemma store_frame_scope_restore_path :
  forall ps Σ s_param frame x path s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_restore_path x path s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path s' HinΣ Hfresh Hscope Hrestore.
  unfold store_restore_path in Hrestore.
  eapply store_frame_scope_update_state; eassumption.
Qed.

Lemma store_frame_scope_consume_path :
  forall ps Σ s_param frame x path s',
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    store_consume_path x path s_param = Some s' ->
    store_frame_scope ps Σ s' frame.
Proof.
  intros ps Σ s_param frame x path s' HinΣ Hfresh Hscope Hconsume.
  unfold store_consume_path in Hconsume.
  destruct (store_lookup x s_param) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_frame_scope_update_state; eassumption.
Qed.

Lemma store_frame_scope_remove_non_param :
  forall ps Σ s_param frame x,
    In x (ctx_names Σ) ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s_param frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_frame_scope ps Σ (store_remove x s_param) frame.
Proof.
  intros ps Σ s_param frame x HinΣ Hfresh Hscope Hnotin.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_remove_non_param_same_frame.
    + exact Hprefix.
    + exact Hnotin.
    + apply Hfresh. exact HinΣ.
  - simpl. destruct (ident_eqb x (se_name se)) eqn:Heq.
    + exact Hscope_tail.
    + econstructor 2.
      * exact Hse_notin.
      * exact Hin_se.
      * apply IH. exact Hfresh.
Qed.

Lemma store_frame_scope_remove_context_absent :
  forall ps Σ s frame x,
    ~ In x (store_names s) ->
    store_frame_scope ps Σ s frame ->
    store_frame_scope ps (sctx_remove x Σ) s frame.
Proof.
  intros ps Σ s frame x Hnotin Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor. exact Hprefix.
  - simpl in Hnotin.
    econstructor 2.
    + exact Hse_notin.
    + apply ctx_names_remove_preserve_neq.
      * intros Heq. subst x. apply Hnotin. left. reflexivity.
      * exact Hin_se.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_frame_scope_remove_non_param_sctx_remove :
  forall ps Σ s frame x,
    In x (ctx_names Σ) ->
    store_no_shadow s ->
    store_frame_static_fresh Σ frame ->
    store_frame_scope ps Σ s frame ->
    ~ In x (ctx_names (params_ctx ps)) ->
    store_frame_scope ps (sctx_remove x Σ) (store_remove x s) frame.
Proof.
  intros ps Σ s frame x HinΣ Hshadow Hfresh Hscope Hnotin.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hse_notin Hin_se Hscope_tail IH].
  - constructor.
    eapply store_param_prefix_remove_non_param_same_frame.
    + exact Hprefix.
    + exact Hnotin.
    + apply Hfresh. exact HinΣ.
  - simpl in Hshadow.
    inversion Hshadow as [| ? ? Hhead_notin Htail_shadow]; subst.
    simpl. destruct (ident_eqb x (se_name se)) eqn:Heq.
    + apply store_frame_scope_remove_context_absent.
      * apply ident_eqb_eq in Heq. subst x. exact Hhead_notin.
      * exact Hscope_tail.
    + econstructor 2.
      * exact Hse_notin.
      * apply ctx_names_remove_preserve_neq.
        -- apply ident_eqb_neq in Heq. exact Heq.
        -- exact Hin_se.
      * apply IH.
        -- exact Htail_shadow.
        -- exact Hfresh.
Qed.


Lemma store_param_prefix_lookup_param_or_frame :
  forall ps s_param frame x se,
    store_param_prefix ps s_param frame ->
    store_lookup x s_param = Some se ->
    In x (ctx_names (params_ctx ps)) \/
    store_lookup x frame = Some se.
Proof.
  intros ps s_param frame x se Hprefix.
  induction Hprefix as [frame | p ps v st s_param frame Hprefix IH];
    intros Hlookup.
  - right. exact Hlookup.
  - simpl in Hlookup.
    destruct (ident_eqb x (param_name p)) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst x.
      left. simpl. left. reflexivity.
    + destruct (IH Hlookup) as [Hin | Hframe].
      * left. simpl. right. exact Hin.
      * right. exact Hframe.
Qed.

Lemma store_frame_scope_lookup_absent_in_frame :
  forall ps Σ s frame x,
    store_frame_scope ps Σ s frame ->
    store_lookup x s = None ->
    ~ In x (ctx_names (params_ctx ps)) ->
    ~ In x (store_names frame).
Proof.
  intros ps Σ s frame x Hscope.
  induction Hscope as
    [s_param frame Hprefix
    | se s_param frame Hnotin _ Hscope_tail IH];
    intros Hlookup Hnotparam.
  - intros Hin_frame.
    pose proof (store_lookup_none_not_in_names x s_param Hlookup)
      as Hnotin_s_param.
    apply Hnotin_s_param.
    rewrite (store_names_store_param_prefix ps s_param frame Hprefix).
    apply in_or_app. right. exact Hin_frame.
  - simpl in Hlookup.
    destruct (ident_eqb x (se_name se)); try discriminate.
    eapply IH; eassumption.
Qed.


Lemma sctx_path_available_success :
  forall Σ x path,
    sctx_path_available Σ x path = infer_ok tt ->
    exists T st,
      sctx_lookup x Σ = Some (T, st) /\
      binding_available_b st path = true.
Proof.
  intros Σ x path Havailable.
  unfold sctx_path_available in Havailable.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b st path) eqn:Hbinding; try discriminate.
  inversion Havailable; subst.
  exists T, st. split.
  - reflexivity.
  - exact Hbinding.
Qed.


Theorem eval_preserves_frame_scope_roots_ready_mutual :
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
Proof.
  assert (Hframe : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots
          ps frame,
        provenance_ready_expr e ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        root_env_covers_params ps R ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        store_frame_scope ps Σ s frame ->
        store_frame_static_fresh Σ frame ->
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame) /\
    (forall s args s' vs,
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
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame) /\
    (forall s fields defs s' values,
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
        root_env_covers_params ps R' /\
        store_frame_scope ps Σ' s' frame /\
        store_frame_static_fresh Σ' frame)).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s i Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s f Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s b Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst;
      repeat split; try exact Hcover; try exact Hscope; try exact Hfresh;
      try (eapply store_frame_scope_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hscope ]);
      try (eapply store_frame_static_fresh_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hfresh ]).
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      ps frame _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst.
    + destruct (typed_place_direct_lookup env _ (PVar x) _ x []
                  ltac:(eassumption) eq_refl)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_used :
        store_frame_scope ps _ (store_mark_used x s) frame)
        by (eapply store_frame_scope_mark_used;
            [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
            | exact Hfresh | exact Hscope ]).
      repeat split; assumption.
    + destruct (typed_place_direct_lookup env _ (PVar x) _ x []
                  ltac:(eassumption) eq_refl)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_used :
        store_frame_scope ps _ (store_mark_used x s) frame)
        by (eapply store_frame_scope_mark_used;
            [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
            | exact Hfresh | exact Hscope ]).
      repeat split; try assumption.
      * eapply store_frame_scope_same_bindings.
        -- match goal with
           | Hconsume_ctx : sctx_consume_path _ _ _ = infer_ok _ |- _ =>
               eapply sctx_consume_path_same_bindings; exact Hconsume_ctx
           end.
        -- exact Hscope_used.
      * eapply store_frame_static_fresh_same_bindings.
        -- match goal with
           | Hconsume_ctx : sctx_consume_path _ _ _ = infer_ok _ |- _ =>
               eapply sctx_consume_path_same_bindings; exact Hconsume_ctx
           end.
        -- exact Hfresh.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      ps frame Hready Htyped Hcover _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst;
      repeat split; try exact Hcover; try exact Hscope; try exact Hfresh;
      try (eapply store_frame_scope_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hscope ]);
      try (eapply store_frame_static_fresh_same_bindings;
           [ eapply sctx_consume_path_same_bindings; eassumption
           | exact Hfresh ]).
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover
      _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    + destruct (eval_place_matches_place_path s p x_eval path_eval x0 path0
                  Heval_place H3) as [Hx Hpath]; subst x_eval path_eval.
      destruct (typed_place_direct_lookup env Σ' p T x0 path0 H1 H3)
        as [T_root [st [Hlookup_ctx _]]].
      repeat split.
      * exact Hcover.
      * eapply (store_frame_scope_consume_path ps Σ' s frame x0 path0 s').
        -- eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
        -- exact Hfresh.
        -- exact Hscope.
        -- exact Hstore_consume.
      * exact Hfresh.
    + destruct (eval_place_matches_place_path s p x_eval path_eval x0 path0
                  Heval_place H3) as [Hx Hpath]; subst x_eval path_eval.
      destruct (typed_place_direct_lookup env Σ p T x0 path0 H1 H3)
        as [T_root [st [Hlookup_ctx _]]].
      assert (Hscope_consume : store_frame_scope ps Σ s' frame).
      { eapply (store_frame_scope_consume_path ps Σ s frame x0 path0 s').
        - eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
        - exact Hfresh.
        - exact Hscope.
        - exact Hstore_consume. }
      repeat split.
      * exact Hcover.
      * eapply store_frame_scope_same_bindings.
        -- eapply sctx_consume_path_same_bindings. exact H4.
        -- exact Hscope_consume.
      * eapply store_frame_static_fresh_same_bindings.
        -- eapply sctx_consume_path_same_bindings. exact H4.
        -- exact Hfresh.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_struct name env = Some ?sdef_typed |- _ =>
        rewrite Hlookup in Hlookup_typed; inversion Hlookup_typed; subst sdef_typed
    end.
    match goal with
    | Hready_fields : provenance_ready_fields fields,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ fields
        (struct_fields sdef) Σ' R' roots |- _ =>
        exact (IHfields Ω n lts args R Σ Σ' R' roots ps frame
                 Hready_fields Htyped_fields Hcover Hroots Hshadow Hrn
                 Hscope Hfresh)
    end.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1 v1
                Heval1 Ω n R Σ T1 Σ1 R1 roots1 Hready1 Hroots
                Hshadow Hrn H4)
      as [Hroots1 [Hv1_roots [Hshadow1 Hrn1]]].
    destruct (IH1 Ω n R Σ T1 Σ1 R1 roots1 ps frame Hready1 H4
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    pose proof (root_env_covers_params_lookup_none_not_in
                  ps R1 x Hcover1
                  ltac:(match goal with
                    | H : root_env_lookup x R1 = None |- _ => exact H
                    end)) as Hnotin.
    assert (Hlookup_fresh : store_lookup x s1 = None)
      by (eapply store_roots_within_lookup_none; eassumption).
    assert (Hnot_frame : ~ In x (store_names frame))
      by (eapply store_frame_scope_lookup_absent_in_frame; eassumption).
    assert (Hadd_roots :
      store_roots_within (root_env_add x roots1 R1)
        (store_add x T_ann v1 s1))
      by (eapply store_add_roots_within; eassumption).
    assert (Hadd_shadow :
      store_no_shadow (store_add x T_ann v1 s1))
      by (apply store_no_shadow_add; assumption).
    assert (Hadd_rn :
      root_env_no_shadow (root_env_add x roots1 R1))
      by (apply root_env_no_shadow_add; assumption).
    assert (Hscope_add :
      store_frame_scope ps (sctx_add x T_ann m Σ1)
        (store_add x T_ann v1 s1) frame)
      by (eapply store_frame_scope_add_weaken;
          [ exact Hnotin
          | simpl; left; reflexivity
          | intros y Hy; simpl; right; exact Hy
          | exact Hscope1 ]).
    assert (Hfresh_add :
      store_frame_static_fresh (sctx_add x T_ann m Σ1) frame)
      by (eapply store_frame_static_fresh_add; eassumption).
    assert (Htyped_body :
      typed_env_roots env Ω n (root_env_add x roots1 R1)
        (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots).
    { match goal with
      | H : typed_env_roots env Ω n (root_env_add x roots1 R1)
              (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots |- _ =>
          exact H
      end. }
    destruct (proj1 eval_preserves_roots_ready_mutual env
                (store_add x T_ann v1 s1) e2 s2 v2 Heval2
                Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots Hready2
                Hadd_roots Hadd_shadow Hadd_rn Htyped_body)
      as [Hroots2 [_ [Hshadow2 Hrn2]]].
    destruct (IH2 Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots ps frame
                Hready2 Htyped_body
                (root_env_covers_params_add ps R1 x roots1 Hcover1)
                Hadd_roots Hadd_shadow Hadd_rn Hscope_add Hfresh_add)
      as [Hcover2 [Hscope2 Hfresh2]].
    assert (Hin_x_Σ2 : In x (ctx_names Σ2)).
    { pose proof (typed_env_structural_same_bindings env Ω n
                    (sctx_add x T_ann m Σ1) e2 T Σ2
                    (typed_env_roots_structural env Ω n
                      (root_env_add x roots1 R1)
                      (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots
                      Htyped_body))
        as Hsame_body.
      pose proof (sctx_same_bindings_names_alpha
                    (sctx_add x T_ann m Σ1) Σ2 Hsame_body) as Hnames.
      rewrite Hnames. simpl. left. reflexivity. }
    repeat split.
    + eapply root_env_covers_params_remove_non_param; eassumption.
    + eapply store_frame_scope_remove_non_param_sctx_remove; eassumption.
    + apply store_frame_static_fresh_remove. exact Hfresh2.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        exact (IH Ω n R Σ T_e Σ' R' roots_e ps frame Hready_e
                 Htyped_e Hcover Hroots Hshadow Hrn Hscope Hfresh)
    end.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    destruct (IHnew Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption)
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (sctx_path_available_success _ x [] ltac:(eassumption))
      as [T_root [st [Hlookup_ctx _]]].
    assert (Hscope2 : store_frame_scope ps _ s2 frame)
      by (eapply store_frame_scope_update_val;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope1 | exact Hupdate ]).
    assert (Hscope3 : store_frame_scope ps _ s3 frame)
      by (eapply store_frame_scope_restore_path;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope2 | exact Hrestore ]).
    repeat split.
    + apply root_env_covers_params_update. exact Hcover1.
    + eapply store_frame_scope_same_bindings.
      * eapply sctx_restore_path_same_bindings. eassumption.
      * exact Hscope3.
    + eapply store_frame_static_fresh_same_bindings.
      * eapply sctx_restore_path_same_bindings. eassumption.
      * exact Hfresh1.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    destruct (IHnew Ω n _ _ _ _ _ _ ps frame
                ltac:(eassumption) ltac:(eassumption)
                Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (sctx_path_available_success _ x [] ltac:(eassumption))
      as [T_root [st [Hlookup_ctx _]]].
    repeat split.
    + apply root_env_covers_params_update. exact Hcover1.
    + eapply store_frame_scope_update_val.
      * eapply sctx_lookup_in_ctx_names. exact Hlookup_ctx.
      * exact Hfresh1.
      * exact Hscope1.
      * exact Hupdate.
    + exact Hfresh1.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new,
      Havailable : sctx_path_available ?Σ1 x path = infer_ok tt,
      Hrestore_ctx : sctx_restore_path ?Σ1 x path = infer_ok Σ' |- _ =>
        destruct (eval_place_matches_place_path s p x_eval path_eval x path
                    Heval_place H) as [Hx_eval Hpath_eval];
        subst x_eval path_eval;
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ1 x path Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        assert (Hscope2 : store_frame_scope ps Σ1 s2 frame)
          by (eapply store_frame_scope_update_path;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh1 | exact Hscope1 | exact Hupdate ]);
        assert (Hscope3 : store_frame_scope ps Σ1 s3 frame)
          by (eapply store_frame_scope_restore_path;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh1 | exact Hscope2 | exact Hrestore ]);
        repeat split;
        [ apply root_env_covers_params_update; exact Hcover1
        | eapply store_frame_scope_same_bindings;
          [ eapply sctx_restore_path_same_bindings; exact Hrestore_ctx
          | exact Hscope3 ]
        | eapply store_frame_static_fresh_same_bindings;
          [ eapply sctx_restore_path_same_bindings; exact Hrestore_ctx
          | exact Hfresh1 ] ]
    end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hready_path : place_path p = Some (x, path),
      Htyped_path : place_path p = Some (?x_typed, ?path_typed) |- _ =>
        rewrite Hready_path in Htyped_path;
        inversion Htyped_path; subst x_typed path_typed; clear Htyped_path
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new,
      Havailable : sctx_path_available Σ' x path = infer_ok tt |- _ =>
        destruct (eval_place_matches_place_path s p x_eval path_eval x path
                    Heval_place H) as [Hx_eval Hpath_eval];
        subst x_eval path_eval;
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ' x path Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        repeat split;
        [ apply root_env_covers_params_update; exact Hcover1
        | eapply store_frame_scope_update_path;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope1 | exact Hupdate ]
        | exact Hfresh1 ]
    end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover _ _ _ Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; repeat split; assumption.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame Hready _ _ _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Heval_r; subst.
    inversion Htyped; subst; try solve [repeat split; assumption].
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots ps frame
      _ Htyped Hcover _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; try assumption; constructor.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1
        ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 ?Σ1 e2 ?T2 ?Σ2
        ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hshadow Hrn Htyped_cond)
          as [Hroots1 [_ [Hshadow1 Hrn1]]];
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                    Hready_cond Htyped_cond Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2 ps frame
                    Hready_then Htyped_then Hcover1 Hroots1 Hshadow1 Hrn1
                    Hscope1 Hfresh1)
          as [Hcover2 [Hscope2 Hfresh2]];
        repeat split;
        [ exact Hcover2
        | eapply store_frame_scope_same_bindings;
          [ eapply ctx_merge_same_bindings_left; exact Hmerge
          | exact Hscope2 ]
        | eapply store_frame_static_fresh_same_bindings;
          [ eapply ctx_merge_same_bindings_left; exact Hmerge
          | exact Hfresh2 ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hroots
      Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                roots_cond Hready1 Hroots Hshadow Hrn H2)
      as [Hroots1 [_ [Hshadow1 Hrn1]]].
    destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                Hready1 H2 Hcover Hroots Hshadow Hrn Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3 ps frame
                Hready3 H5 Hcover1 Hroots1 Hshadow1 Hrn1
                Hscope1 Hfresh1)
      as [Hcover3 [Hscope3 Hfresh3]].
    assert (Hsame_then_else : sctx_same_bindings Σ2 Σ3).
    { eapply sctx_same_bindings_trans.
      - apply sctx_same_bindings_sym.
        eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact H4.
      - eapply typed_env_structural_same_bindings.
        eapply typed_env_roots_structural. exact H5. }
    repeat split.
    + eapply root_env_covers_params_equiv.
      * apply root_env_equiv_sym. exact H14.
      * exact Hcover3.
    + eapply store_frame_scope_same_bindings.
      * eapply ctx_merge_same_bindings_right.
        -- exact Hsame_then_else.
        -- exact H13.
      * exact Hscope3.
    + eapply store_frame_static_fresh_same_bindings.
      * eapply ctx_merge_same_bindings_right.
        -- exact Hsame_then_else.
        -- exact H13.
      * exact Hfresh3.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots ps frame Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots ps frame Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ params Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ params Σ' R' roots ps frame Hready Htyped Hcover
      Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    dependent destruction Htyped.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?params_rest
        ?Σ2 ?R2 ?roots_rest |- _ =>
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e Hready_e
                    Hroots Hshadow Hrn Htyped_e)
          as [Hroots1 [_ [Hshadow1 Hrn1]]];
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e ps frame Hready_e
                    Htyped_e Hcover Hroots Hshadow Hrn Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        exact (IHrest Ω n R1 Σ1 params_rest Σ2 R2 roots_rest ps frame
                 Hready_rest Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                 Hscope1 Hfresh1)
    end.
  - intros s Ω n lts args0 R Σ Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args0 R Σ Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    destruct (typed_fields_roots_cons_inv_ts env Ω n lts args0 R Σ
                fields f rest Σ' R' roots Htyped)
      as (e_field & T_field & Σ1 & R1 & roots_field & roots_rest &
        Hlookup_typed & Htyped_field & _ & Htyped_rest & _).
    rewrite lookup_field_b_lookup_expr_field in Hlookup_typed.
    rewrite Hlookup_typed in Hlookup_expr.
    inversion Hlookup_expr; subst e_field.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                Hready_field Hroots Hshadow Hrn Htyped_field)
      as [Hroots1 [_ [Hshadow1 Hrn1]]].
    destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                Hready_field Htyped_field Hcover Hroots Hshadow Hrn
                Hscope Hfresh)
      as [Hcover1 [Hscope1 Hfresh1]].
    exact (IHrest Ω n lts args0 R1 Σ1 Σ' R' roots_rest ps frame
             Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
             Hscope1 Hfresh1).
  }
  assert (Hexpr : frame_scope_roots_ready_expr_preservation).
  { intros env s e s' v Heval Ω n R Σ T Σ' R' roots ps frame
      Hready Htyped Hcover Hroots Hshadow Hrn Hscope Hfresh.
    destruct (proj1 eval_preserves_roots_ready_mutual env s e s' v
                Heval Ω n R Σ T Σ' R' roots Hready Hroots Hshadow
                Hrn Htyped)
      as [Hroots' [_ [Hshadow' Hrn']]].
    destruct (Hframe env) as [Hframe_expr _].
    destruct (Hframe_expr s e s' v Heval Ω n R Σ T Σ' R' roots
                ps frame Hready Htyped Hcover Hroots Hshadow Hrn
                Hscope Hfresh)
      as [Hcover' [Hscope' Hfresh']].
    repeat split; assumption. }
  split.
  - exact Hexpr.
  - exact (eval_preserves_frame_scope_roots_ready_args_fields_from_expr Hexpr).
Qed.


Lemma store_frame_scope_remove_non_param_after_same_bindings :
  forall ps Σ_body Σ_after s frame x,
    In x (ctx_names Σ_body) ->
    store_frame_static_fresh Σ_body frame ->
    store_frame_scope ps Σ_body s frame ->
    store_no_shadow s ->
    ~ In x (ctx_names (params_ctx ps)) ->
    sctx_same_bindings Σ_after (sctx_remove x Σ_body) ->
    store_frame_scope ps Σ_after (store_remove x s) frame.
Proof.
  intros ps Σ_body Σ_after s frame x Hin Hfresh Hscope Hshadow Hnotin Hsame.
  eapply store_frame_scope_same_names.
  - symmetry. apply sctx_same_bindings_names_alpha. exact Hsame.
  - eapply store_frame_scope_remove_non_param_sctx_remove; eassumption.
Qed.

Lemma sctx_same_bindings_params_ctx_names :
  forall ps Σ,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    ctx_names Σ = ctx_names (params_ctx ps).
Proof.
  intros ps Σ Hsame.
  pose proof (sctx_same_bindings_names_alpha
                (sctx_of_ctx (params_ctx ps)) Σ Hsame) as Hnames.
  unfold sctx_of_ctx in Hnames. exact Hnames.
Qed.

Lemma store_frame_scope_no_local_under_params :
  forall ps Σ se s_param frame,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    ~ In (se_name se) (ctx_names (params_ctx ps)) ->
    In (se_name se) (ctx_names Σ) ->
    store_frame_scope ps Σ (se :: s_param) frame ->
    False.
Proof.
  intros ps Σ se s_param frame Hsame Hnotin HinΣ _.
  apply Hnotin.
  rewrite <- (sctx_same_bindings_params_ctx_names ps Σ Hsame).
  exact HinΣ.
Qed.

Lemma store_remove_params_cleanup_excludes :
  forall ps s_body frame R roots v,
    store_param_scope ps s_body frame ->
    store_roots_within R s_body ->
    value_roots_within roots v ->
    store_no_shadow s_body ->
    NoDup (ctx_names (params_ctx ps)) ->
    roots_exclude_params ps roots ->
    root_env_excludes_params ps R ->
    exists locals,
      store_remove_params ps s_body = locals ++ frame /\
      value_refs_exclude_params ps v /\
      store_refs_exclude_params ps (store_remove_params ps s_body).
Proof.
  intros ps s_body frame R roots v Hscope Hstore Hvalue Hshadow Hnodup
    Hexclude_roots Hexclude_env.
  destruct (store_remove_params_store_param_scope ps s_body frame Hscope)
    as [locals Hremoved].
  exists locals.
  repeat split.
  - exact Hremoved.
  - eapply value_roots_exclude_params; eassumption.
  - eapply store_roots_exclude_params.
    + apply store_remove_params_roots_within_same_env. exact Hstore.
    + exact Hexclude_env.
    + intros x Hin se Hse.
      eapply store_remove_params_no_param_names; eassumption.
Qed.

Lemma value_has_type_store_remove_params_excluding :
  forall ps env s v T,
    value_has_type env s v T ->
    value_refs_exclude_params ps v ->
    value_has_type env (store_remove_params ps s) v T.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros env s v T Hvalue Hexclude.
  - exact Hvalue.
  - simpl.
    apply IH.
    + eapply value_has_type_store_remove_excluding_root.
      * exact Hvalue.
      * apply Hexclude. simpl. left. reflexivity.
    + intros x Hin.
      apply Hexclude. simpl. right. exact Hin.
Qed.

Lemma store_ref_targets_preserved_remove_params_after_absent :
  forall ps env s s',
    store_ref_targets_preserved env s s' ->
    params_fresh_in_store ps s ->
    store_ref_targets_preserved env s (store_remove_params ps s').
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros env s s' Hpres Hfresh.
  - exact Hpres.
  - simpl.
    apply IH.
    + eapply store_ref_targets_preserved_remove_after_absent_root.
      * exact Hpres.
      * apply store_lookup_not_in_names.
        eapply params_fresh_in_store_head. exact Hfresh.
    + eapply params_fresh_in_store_tail. exact Hfresh.
Qed.

Lemma store_names_store_param_scope :
  forall ps s_param s,
    store_param_scope ps s_param s ->
    exists local_names,
      store_names s_param =
        local_names ++ ctx_names (params_ctx ps) ++ store_names s.
Proof.
  intros ps s_param s Hscope.
  induction Hscope as
    [ps s_param s Hprefix
    | ps se s_param s _ _ IH].
  - exists [].
    rewrite (store_names_store_param_prefix ps s_param s Hprefix).
    reflexivity.
  - destruct IH as [local_names IH].
    exists (se_name se :: local_names).
    simpl. rewrite IH. reflexivity.
Qed.

Lemma store_remove_params_store_param_prefix :
  forall ps s_param s,
    store_param_prefix ps s_param s ->
    store_remove_params ps s_param = s.
Proof.
  intros ps s_param s Hprefix.
  induction Hprefix as [s | p ps v st s_param s _ IH].
  - reflexivity.
  - simpl. rewrite ident_eqb_refl. exact IH.
Qed.

Lemma captured_params_store_typed_remove_app :
  forall env captured caps frame,
    captured_params_store_typed env captured caps ->
    store_remove_params caps (captured ++ frame) = frame.
Proof.
  intros env captured caps frame Htyped.
  pose proof (captured_params_store_typed_store_param_prefix
                env captured caps Htyped) as Hprefix.
  pose proof (store_param_prefix_append_frame
                caps captured frame [] Hprefix) as Hprefix_frame.
  simpl in Hprefix_frame.
  eapply store_remove_params_store_param_prefix.
  exact Hprefix_frame.
Qed.

Lemma captured_params_store_typed_remove_hidden_app :
  forall env captured caps x T v frame,
    captured_params_store_typed env captured caps ->
    store_remove x
      (store_remove_params caps (captured ++ store_add x T v frame)) =
      frame.
Proof.
  intros env captured caps x T v frame Htyped.
  rewrite captured_params_store_typed_remove_app with (env := env)
    by exact Htyped.
  apply store_remove_store_add_same.
Qed.

Lemma store_remove_params_store_frame_scope_exact :
  forall ps Σ s_param frame,
    sctx_same_bindings (sctx_of_ctx (params_ctx ps)) Σ ->
    store_param_scope ps s_param frame ->
    store_frame_scope ps Σ s_param frame ->
    store_remove_params ps s_param = frame.
Proof.
  intros ps Σ s_param frame Hsame Hparam_scope Hframe_scope.
  induction Hframe_scope as
    [s_param frame Hprefix
    | se s_param frame Hnotin HinΣ Hframe_scope_tail IH].
  - eapply store_remove_params_store_param_prefix. exact Hprefix.
  - exfalso.
    apply Hnotin.
    rewrite <- (sctx_same_bindings_params_ctx_names ps Σ Hsame).
    exact HinΣ.
Qed.

Lemma store_typed_remove_params_store_param_prefix :
  forall env ps s_param s Σ,
    store_typed env s Σ ->
    store_param_prefix ps s_param s ->
    store_typed env (store_remove_params ps s_param) Σ.
Proof.
  intros env ps s_param s Σ Htyped Hprefix.
  rewrite (store_remove_params_store_param_prefix ps s_param s Hprefix).
  exact Htyped.
Qed.
