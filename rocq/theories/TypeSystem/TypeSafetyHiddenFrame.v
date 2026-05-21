From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
