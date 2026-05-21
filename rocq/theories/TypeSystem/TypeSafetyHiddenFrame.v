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
