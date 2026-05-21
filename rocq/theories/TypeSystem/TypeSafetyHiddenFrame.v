From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts.
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

