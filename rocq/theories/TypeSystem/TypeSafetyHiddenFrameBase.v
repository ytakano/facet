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

Definition captured_store_runtime_ready_in_frame
    (env : global_env) (captured : store) (Rcap : root_env)
    (frame : store) : Prop :=
  Forall2 (store_entry_typed env (captured ++ frame))
    captured (sctx_of_store captured) /\
  store_roots_within Rcap captured /\
  store_no_shadow captured /\
  root_env_no_shadow Rcap /\
  root_env_store_roots_named Rcap (captured ++ frame) /\
  root_env_store_keys_named Rcap captured.

Definition captured_call_frame_ready_in_frame
    (env : global_env) (captured : store) (Rcap : root_env)
    (s_args : store) (R_args : root_env) : Prop :=
  captured_store_runtime_ready_in_frame env captured Rcap s_args /\
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

Fixpoint copy_capture_roots_as
    (captures : list ident) (caps : list param) (R : root_env)
    : option root_env :=
  match captures, caps with
  | [], [] => Some []
  | x :: captures', cap :: caps' =>
      match root_env_lookup x R, copy_capture_roots_as captures' caps' R with
      | Some roots, Some Rcap =>
          Some ((param_name cap, roots) :: Rcap)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition capture_value_roots (v : value) : root_set :=
  match v with
  | VRef x _ => [RStore x]
  | _ => []
  end.

Fixpoint capture_store_root_sets (captured : store) : list root_set :=
  match captured with
  | [] => []
  | se :: rest =>
      capture_value_roots (se_val se) :: capture_store_root_sets rest
  end.

Fixpoint capture_store_root_env (captured : store) : root_env :=
  match captured with
  | [] => []
  | se :: rest =>
      (se_name se, capture_value_roots (se_val se)) ::
      capture_store_root_env rest
  end.

Lemma capture_store_root_sets_length :
  forall captured,
    List.length (capture_store_root_sets captured) = List.length captured.
Proof.
  induction captured as [| se rest IH]; simpl; auto.
Qed.

Lemma capture_store_root_env_names :
  forall captured,
    root_env_names (capture_store_root_env captured) = store_names captured.
Proof.
  induction captured as [| se rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma capture_store_root_env_no_shadow :
  forall captured,
    store_no_shadow captured ->
    root_env_no_shadow (capture_store_root_env captured).
Proof.
  intros captured Hshadow.
  unfold root_env_no_shadow.
  rewrite capture_store_root_env_names.
  exact Hshadow.
Qed.

Lemma capture_value_roots_sound :
  forall v,
    value_roots_within [] v \/
    (exists x path, v = VRef x path) ->
    value_roots_within (capture_value_roots v) v.
Proof.
  intros v Hcase.
  destruct Hcase as [Hrootless | [x [path Href]]].
  - destruct v; simpl in *; try exact Hrootless.
    inversion Hrootless; subst.
    contradiction.
  - subst v. simpl. constructor. simpl. left. reflexivity.
Qed.

Lemma ty_compatible_expected_ref_actual_ref :
  forall Ω T_actual u l rk T,
    ty_compatible Ω T_actual (MkTy u (TRef l rk T)) ->
    exists u_actual l_actual T_actual_inner,
      T_actual = MkTy u_actual (TRef l_actual rk T_actual_inner).
Proof.
  intros Ω T_actual u l rk T Hcompat.
  remember (MkTy u (TRef l rk T)) as T_expected eqn:Hexpected.
  induction Hcompat; inversion Hexpected; subst; try discriminate.
  - subst. eauto.
  - eauto.
  - eauto.
Qed.

Lemma ty_lifetime_equiv_expected_ref_actual_ref :
  forall T_actual u l rk T,
    ty_lifetime_equiv T_actual (MkTy u (TRef l rk T)) ->
    exists l_actual T_actual_inner,
      T_actual = MkTy u (TRef l_actual rk T_actual_inner).
Proof.
  intros T_actual u l rk T Hequiv.
  remember (MkTy u (TRef l rk T)) as T_expected eqn:Hexpected.
  induction Hequiv; inversion Hexpected; subst; try discriminate.
  eauto.
Qed.

Lemma value_has_type_ref_ty_value_aux :
  forall env s v T_final,
    value_has_type env s v T_final ->
    forall u l rk T,
      T_final = MkTy u (TRef l rk T) ->
      exists x path, v = VRef x path.
Proof.
  intros env s v T_final Htype.
  induction Htype; intros u_ref l_ref rk_ref T_ref Href;
    inversion Href; subst; try discriminate.
  - eauto.
  - unfold fn_value_ty, fn_signature_ty_with_usage in Href.
    destruct (fn_lifetimes fdef) eqn:Hlifetimes.
    + unfold close_fn_ty in Href.
      rewrite map_lifetimes_ty_close_fn_lifetime_0 in Href.
      discriminate.
    + discriminate.
  - unfold fn_value_ty, fn_signature_ty_with_usage in Href.
    destruct (fn_lifetimes fdef) eqn:Hlifetimes.
    + unfold close_fn_ty in Href.
      rewrite map_lifetimes_ty_close_fn_lifetime_0 in Href.
      discriminate.
    + discriminate.
  - destruct (ty_compatible_expected_ref_actual_ref
      Ω T_actual u_ref l_ref rk_ref T_ref H)
      as [u_actual [l_actual [T_inner Hactual]]].
    eapply IHHtype. exact Hactual.
  - destruct (ty_lifetime_equiv_expected_ref_actual_ref
      T_actual u_ref l_ref rk_ref T_ref H)
      as [l_actual [T_inner Hactual]].
    eapply IHHtype. exact Hactual.
Qed.

Lemma value_has_type_ref_ty_value :
  forall env s v u l rk T,
    value_has_type env s v (MkTy u (TRef l rk T)) ->
    exists x path, v = VRef x path.
Proof.
  intros env s v u l rk T Htype.
  eapply value_has_type_ref_ty_value_aux.
  - exact Htype.
  - reflexivity.
Qed.

Lemma capture_store_root_env_store_keys_named :
  forall captured,
    root_env_store_keys_named
      (capture_store_root_env captured) captured.
Proof.
  intros captured.
  unfold root_env_store_keys_named, root_env_keys_named.
  rewrite capture_store_root_env_names.
  intros x Hin. exact Hin.
Qed.

Lemma copy_capture_roots_as_length :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    List.length captures = List.length caps.
Proof.
  intros captures.
  induction captures as [| x captures IH]; intros caps R Rcap Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate;
    simpl.
  - reflexivity.
  - destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    f_equal. eapply IH. exact Htail.
Qed.

Lemma copy_capture_roots_as_names :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    root_env_names Rcap = ctx_names (params_ctx caps).
Proof.
  intros captures.
  induction captures as [| x captures IH]; intros caps R Rcap Hcopy;
    destruct caps as [| cap caps]; simpl in Hcopy; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (root_env_lookup x R) as [roots |] eqn:Hlookup;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    simpl. rewrite (IH caps R Rtail Htail). reflexivity.
Qed.

Lemma copy_capture_roots_as_no_shadow :
  forall captures caps R Rcap,
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    root_env_no_shadow Rcap.
Proof.
  intros captures caps R Rcap Hcopy Hnodup.
  unfold root_env_no_shadow.
  rewrite (copy_capture_roots_as_names captures caps R Rcap Hcopy).
  exact Hnodup.
Qed.

Lemma param_name_nth_error_in_params_ctx :
  forall caps n cap,
    nth_error caps n = Some cap ->
    In (param_name cap) (ctx_names (params_ctx caps)).
Proof.
  induction caps as [| cap0 caps IH]; intros n cap Hnth;
    destruct n as [| n]; simpl in Hnth; try discriminate.
  - injection Hnth as <-. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hnth.
Qed.

Lemma copy_capture_roots_as_lookup_nth :
  forall captures caps R Rcap n src cap roots,
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    nth_error captures n = Some src ->
    nth_error caps n = Some cap ->
    root_env_lookup src R = Some roots ->
    root_env_lookup (param_name cap) Rcap = Some roots.
Proof.
  intros captures.
  induction captures as [| x captures IH];
    intros caps R Rcap n src cap roots Hcopy Hnodup Hsrc Hcap Hlookup_src;
    destruct caps as [| cap0 caps]; simpl in Hcopy; try discriminate.
  - destruct n; simpl in Hsrc; discriminate.
  - destruct (root_env_lookup x R) as [roots0 |] eqn:Hlookup_x;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Htail; try discriminate.
    injection Hcopy as <-.
    destruct n as [| n].
    + simpl in Hsrc, Hcap.
      injection Hsrc as <-. injection Hcap as <-.
      rewrite Hlookup_src in Hlookup_x. injection Hlookup_x as <-.
      simpl. rewrite ident_eqb_refl. reflexivity.
    + simpl in Hsrc, Hcap.
      simpl.
      inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
      destruct (ident_eqb (param_name cap) (param_name cap0)) eqn:Heq.
      * apply ident_eqb_eq in Heq.
        exfalso.
        apply Hnotin.
        rewrite <- Heq.
        eapply param_name_nth_error_in_params_ctx. exact Hcap.
      * eapply IH; eassumption.
Qed.

Lemma copy_capture_roots_as_lookup_head :
  forall x captures cap caps R Rcap roots,
    copy_capture_roots_as (x :: captures) (cap :: caps) R = Some Rcap ->
    NoDup (ctx_names (params_ctx (cap :: caps))) ->
    root_env_lookup x R = Some roots ->
    root_env_lookup (param_name cap) Rcap = Some roots.
Proof.
  intros x captures cap caps R Rcap roots Hcopy Hnodup Hlookup.
  eapply copy_capture_roots_as_lookup_nth with
    (captures := x :: captures) (caps := cap :: caps)
    (n := 0) (src := x) (cap := cap); eauto.
Qed.

Lemma check_make_closure_captures_exact_sctx_sound :
  forall env Ω Σ captures caps captured_tys,
    check_make_closure_captures_exact_sctx env Ω Σ captures caps =
      infer_ok captured_tys ->
    typed_captures Ω Σ LStatic captures caps captured_tys /\
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
      * apply CCap_RefFree.
        apply (capture_ref_free_ty_b_ty_ref_free env (param_ty cap)).
        exact Href_free.
      * apply ty_compatible_refl.
      * exact Htyped_tail.
    + simpl. rewrite Htys_tail. reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_base_sound :
  forall env Ω Σ captures caps captured_tys env_lt,
    check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps = infer_ok captured_tys ->
    closure_captures_allowed_b env Ω env_lt captured_tys = true ->
    typed_captures Ω Σ env_lt captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures.
  induction captures as [| x captures IH]; intros caps captured_tys env_lt
    Hcheck Hallowed;
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
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq Hcompat].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest | err] eqn:Hrest;
      try discriminate.
    injection Hcheck as <-.
    simpl in Hallowed.
    apply andb_true_iff in Hallowed as [Hallowed_head Hallowed_tail].
    destruct (IH caps captured_rest env_lt Hrest Hallowed_tail)
      as [Htyped_tail Htys_tail].
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
      * eapply closure_capture_allowed_b_sound. exact Hallowed_head.
      * apply ty_compatible_b_sound. exact Hcompat.
      * exact Htyped_tail.
    + simpl. rewrite Htys_tail. reflexivity.
Qed.

Lemma check_make_closure_captures_exact_sctx_with_env_sound :
  forall env Ω Σ captures caps env_lt captured_tys,
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    typed_captures Ω Σ env_lt captures caps captured_tys /\
    captured_tys = map param_ty caps.
Proof.
  intros env Ω Σ captures caps env_lt captured_tys Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  eapply check_make_closure_captures_exact_sctx_with_env_base_sound;
    eassumption.
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

Lemma copy_capture_store_exact_with_env_sctx_of_store :
  forall Ω env s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    sctx_of_store captured = sctx_of_ctx (params_ctx caps).
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys
    Hstore Hcopy Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  clear Henv Hallowed.
  revert caps captured captured_tys0 Hcopy Hbase.
  induction captures as [| x captures IH]; intros caps captured captured_tys0
    Hcopy Hbase;
    destruct caps as [| cap caps]; simpl in Hcopy, Hbase; try discriminate.
  - injection Hcopy as <-. reflexivity.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hbase;
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
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest_tys | err]
      eqn:Hrest_check; try discriminate.
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

Lemma store_names_app_hfb :
  forall s1 s2,
    store_names (s1 ++ s2) = store_names s1 ++ store_names s2.
Proof.
  intros s1.
  induction s1 as [| se rest IH]; intros s2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma store_roots_within_lookup_value_hfb :
  forall R s x se roots,
    store_roots_within R s ->
    store_lookup x s = Some se ->
    root_env_lookup x R = Some roots ->
    value_roots_within roots (se_val se).
Proof.
  intros R s x se roots Hwithin.
  revert x se roots.
  induction Hwithin as [R | R se_head rest Hentry Hrest IH];
    intros x se roots Hlookup_store Hlookup_roots;
    simpl in Hlookup_store; try discriminate.
  destruct se_head as [sx sT sv sst].
  inversion Hentry as [R0 sx0 sT0 sv0 sst0 roots0 Hlookup_head Hvalue];
    subst.
  simpl in Hlookup_store.
  destruct (ident_eqb x sx) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    inversion Hlookup_store; subst se.
    rewrite Hlookup_roots in Hlookup_head.
    inversion Hlookup_head; subst roots0.
    exact Hvalue.
  - eapply IH; eassumption.
Qed.

Lemma store_roots_within_weaken_lookup_hfb :
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

Lemma copy_capture_store_as_roots_within_copied_roots :
  forall captures caps s captured R Rcap,
    copy_capture_store_as captures caps s = Some captured ->
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    store_roots_within R s ->
    store_roots_within Rcap captured.
Proof.
  induction captures as [| x captures IH]; intros caps s captured R Rcap
    Hcopy_store Hcopy_roots Hnodup Hwithin;
    destruct caps as [| cap caps]; simpl in Hcopy_store, Hcopy_roots;
    try discriminate.
  - injection Hcopy_store as <-. constructor.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup_store;
      try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_store_tail; try discriminate.
    destruct (root_env_lookup x R) as [roots |] eqn:Hlookup_roots;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Hcopy_roots_tail; try discriminate.
    injection Hcopy_store as <-.
    injection Hcopy_roots as <-.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    constructor.
    + econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * eapply store_roots_within_lookup_value_hfb; eassumption.
    + eapply store_roots_within_weaken_lookup_hfb.
      * eapply IH; eassumption.
      * intros y roots_y Hin Hlookup_y.
        simpl.
        destruct (ident_eqb y (param_name cap)) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst y.
           exfalso. apply Hnotin.
           rewrite <- (copy_capture_store_as_store_names
             captures caps s captured_rest Hcopy_store_tail).
           exact Hin.
        -- exact Hlookup_y.
Qed.

Lemma copy_capture_roots_store_as_keys_named :
  forall captures caps R Rcap s captured,
    copy_capture_roots_as captures caps R = Some Rcap ->
    copy_capture_store_as captures caps s = Some captured ->
    root_env_store_keys_named Rcap captured.
Proof.
  intros captures caps R Rcap s captured Hcopy_roots Hcopy_store.
  unfold root_env_store_keys_named, root_env_keys_named.
  rewrite (copy_capture_roots_as_names captures caps R Rcap Hcopy_roots).
  rewrite (copy_capture_store_as_store_names captures caps s captured
    Hcopy_store).
  intros x Hin. exact Hin.
Qed.

Lemma copy_capture_roots_as_store_roots_named_in_frame :
  forall captures caps R Rcap s captured frame,
    copy_capture_store_as captures caps s = Some captured ->
    copy_capture_roots_as captures caps R = Some Rcap ->
    NoDup (ctx_names (params_ctx caps)) ->
    root_env_store_roots_named R frame ->
    root_env_store_roots_named Rcap (captured ++ frame).
Proof.
  induction captures as [| x captures IH]; intros caps R Rcap s captured
    frame Hcopy_store Hcopy_roots Hnodup Hnamed;
    destruct caps as [| cap caps]; simpl in Hcopy_store, Hcopy_roots;
    try discriminate.
  - injection Hcopy_store as <-. injection Hcopy_roots as <-.
    unfold root_env_store_roots_named.
    intros y roots z Hlookup _. simpl in Hlookup. discriminate.
  - destruct (store_lookup x s) as [se |] eqn:Hlookup_store;
      try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_store_tail; try discriminate.
    destruct (root_env_lookup x R) as [roots_x |] eqn:Hlookup_roots;
      try discriminate.
    destruct (copy_capture_roots_as captures caps R) as [Rtail |]
      eqn:Hcopy_roots_tail; try discriminate.
    injection Hcopy_store as <-.
    injection Hcopy_roots as <-.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    unfold root_env_store_roots_named in *.
    intros y roots z Hlookup Hin.
    simpl in Hlookup.
    destruct (ident_eqb y (param_name cap)) eqn:Heq.
    + injection Hlookup as <-.
      simpl. right. rewrite store_names_app_hfb. apply in_or_app. right.
      eapply Hnamed; eassumption.
    + simpl. right.
      eapply IH.
      * exact Hcopy_store_tail.
      * exact Hcopy_roots_tail.
      * exact Hnodup_tail.
      * exact Hnamed.
      * exact Hlookup.
      * exact Hin.
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

Lemma copy_capture_store_as_captured_entries_typed_with_env_base_preserved :
  forall Ω env s_target s Σ captures caps captured captured_tys,
    store_typed env s Σ ->
    store_ref_targets_preserved env s s_target ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env_base env Ω Σ captures caps =
      infer_ok captured_tys ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured).
Proof.
  intros Ω env s_target s Σ captures.
  induction captures as [| x captures IH]; intros caps captured captured_tys
    Hstore Hpres Hcopy Hcheck;
    destruct caps as [| cap caps]; simpl in Hcopy, Hcheck; try discriminate.
  - injection Hcopy as <-. constructor.
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
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest_tys | err]
      eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    injection Hcheck as <-.
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    simpl. constructor.
    + exact (conj eq_refl
        (conj eq_refl
          (conj (binding_state_refines_refl (se_state se))
            (value_has_type_store_preserved env s (se_val se) (se_ty se)
              Hvalue s_target Hpres)))).
    + eapply IH; eassumption.
Qed.

Lemma copy_capture_store_as_captured_entries_typed_with_env_preserved :
  forall Ω env s_target s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    store_ref_targets_preserved env s s_target ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    Forall2 (store_entry_typed env s_target) captured (sctx_of_store captured).
Proof.
  intros Ω env s_target s Σ captures caps captured env_lt captured_tys
    Hstore Hpres Hcopy Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  eapply copy_capture_store_as_captured_entries_typed_with_env_base_preserved;
    eassumption.
Qed.

Lemma copy_capture_store_as_captured_values_canonical_roots_with_env :
  forall Ω env s Σ captures caps captured env_lt captured_tys,
    store_typed env s Σ ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    Forall (fun se =>
      value_roots_within (capture_value_roots (se_val se)) (se_val se))
      captured.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys
    Hstore Hcopy Hcheck.
  unfold check_make_closure_captures_exact_sctx_with_env in Hcheck.
  destruct (check_make_closure_captures_exact_sctx_with_env_base
    env Ω Σ captures caps) as [captured_tys0 | err] eqn:Hbase;
    try discriminate.
  destruct (infer_closure_env_lifetime Ω captured_tys0) as [env_lt0 | err]
    eqn:Henv; try discriminate.
  destruct (closure_captures_allowed_b env Ω env_lt0 captured_tys0)
    eqn:Hallowed; try discriminate.
  injection Hcheck as <- <-.
  clear Henv.
  revert caps captured captured_tys0 Hcopy Hbase Hallowed.
  induction captures as [| x captures IH]; intros caps captured captured_tys0
    Hcopy Hbase Hallowed;
    destruct caps as [| cap caps]; simpl in Hcopy, Hbase; try discriminate.
  - injection Hcopy as <-. constructor.
  - destruct (param_mutability cap) eqn:Hcap_mut; simpl in Hbase;
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
    destruct (ty_eqb T (param_ty cap) &&
      ty_compatible_b Ω T (param_ty cap)) eqn:Hty; try discriminate.
    apply andb_true_iff in Hty as [Hty_eq _].
    destruct (check_make_closure_captures_exact_sctx_with_env_base
      env Ω Σ captures caps) as [captured_rest_tys | err]
      eqn:Hrest_check; try discriminate.
    destruct (store_lookup x s) as [se |] eqn:Hlookup_store; try discriminate.
    destruct (binding_available_b (se_state se) [] &&
      match ty_usage (se_ty se) with
      | UUnrestricted => true
      | _ => false
      end) eqn:Hcopy_ok; try discriminate.
    destruct (copy_capture_store_as captures caps s) as [captured_rest |]
      eqn:Hcopy_rest; try discriminate.
    injection Hcopy as <-.
    injection Hbase as <-.
    simpl in Hallowed.
    apply andb_true_iff in Hallowed as [Hallowed_head Hallowed_tail].
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup_store)
      as [T_lookup [st_lookup [m_lookup
        [Hlookup_static [Hse_name [Hse_ty [Hrefines Hvalue]]]]]]].
    rewrite Hlookup in Hlookup_static.
    inversion Hlookup_static; subst T_lookup st_lookup.
    apply ty_eqb_true in Hty_eq.
    simpl. constructor.
    + apply capture_value_roots_sound.
      unfold closure_capture_allowed_b in Hallowed_head.
      apply orb_true_iff in Hallowed_head as [Hfree | Href].
      * left.
        assert (Hrootless_T : runtime_rootless_ty env T).
        { apply capture_ref_free_ty_b_runtime_rootless. exact Hfree. }
        assert (Hrootless : runtime_rootless_ty env (se_ty se)).
        { rewrite <- H0. exact Hrootless_T. }
        eapply value_has_type_runtime_rootless_empty_roots.
        -- exact Hvalue.
        -- exact Hrootless.
      * right.
        destruct T as [u core]. simpl in Href.
        destruct core; try discriminate.
        destruct r; try discriminate.
        eapply value_has_type_ref_ty_value.
        rewrite H0. exact Hvalue.
    + eapply IH; eassumption.
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
  - unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    destruct (root_env_lookup x Rcap) as [roots_cap |] eqn:Hlookup_cap.
    + rewrite (root_env_lookup_app_left x Rcap R_args roots_cap
        Hlookup_cap) in Hlookup.
      inversion Hlookup; subst roots_cap.
      rewrite store_names_app.
      apply in_or_app. left.
      eapply Hnamed_cap; eassumption.
    + rewrite (root_env_lookup_app_right x Rcap R_args Hlookup_cap)
        in Hlookup.
      rewrite store_names_app.
      apply in_or_app. right.
      eapply Hnamed_args; eassumption.
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

Lemma capture_store_root_env_roots_within :
  forall captured,
    Forall
      (fun se =>
        value_roots_within (capture_value_roots (se_val se)) (se_val se))
      captured ->
    store_no_shadow captured ->
    store_roots_within (capture_store_root_env captured) captured.
Proof.
  intros captured Hvalues Hshadow.
  induction Hvalues as [| se rest Hvalue _ IH]; simpl in *.
  - constructor.
  - inversion Hshadow as [| ? ? Hnotin Hnodup_tail]; subst.
    constructor.
    + destruct se as [sx sT sv sst]. simpl in *.
      econstructor.
      * simpl. rewrite ident_eqb_refl. reflexivity.
      * exact Hvalue.
    + eapply store_roots_within_weaken_lookup_hfb.
      * apply IH. exact Hnodup_tail.
      * intros x roots Hin Hlookup. simpl.
        destruct (ident_eqb x (se_name se)) eqn:Heq.
        -- apply ident_eqb_eq in Heq. subst x.
           exfalso. apply Hnotin. exact Hin.
        -- exact Hlookup.
Qed.

Lemma value_has_type_ref_root_named :
  forall env s x path T,
    value_has_type env s (VRef x path) T ->
    In x (store_names s).
Proof.
  intros env s x path T Htype.
  remember (VRef x path) as v eqn:Hv.
  induction Htype; inversion Hv; subst; eauto.
  eapply store_lookup_some_in_store_names. exact H.
Qed.

Lemma capture_value_roots_store_roots_named :
  forall env s v T,
    value_has_type env s v T ->
    root_set_store_roots_named (capture_value_roots v) s.
Proof.
  intros env s v T Htype.
  destruct v; simpl; unfold root_set_store_roots_named;
    intros root_name Hin; simpl in Hin; try contradiction.
  destruct Hin as [Hin | Hin]; try contradiction.
  inversion Hin; subst.
  eapply value_has_type_ref_root_named. exact Htype.
Qed.

Lemma capture_store_root_env_store_roots_named_in_store :
  forall env target captured,
    Forall2 (store_entry_typed env target)
      captured (sctx_of_store captured) ->
    root_env_store_roots_named
      (capture_store_root_env captured) target.
Proof.
  intros env target captured Htyped.
  induction Htyped as [| se ce captured_tail Σ_tail Hentry _ IH].
  - unfold root_env_store_roots_named.
    intros x roots z Hlookup _. simpl in Hlookup. discriminate.
  - simpl in *.
    destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [_ Hvalue]]].
    subst cx cT.
    unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    simpl in Hlookup.
    destruct (ident_eqb x sx) eqn:Heq.
    + inversion Hlookup; subst roots.
      eapply capture_value_roots_store_roots_named in Hvalue.
      unfold root_set_store_roots_named in Hvalue.
      exact (Hvalue z Hin).
    + eapply IH; eassumption.
Qed.

Lemma capture_store_root_env_store_roots_named :
  forall env captured frame,
    Forall2 (store_entry_typed env (captured ++ frame))
      captured (sctx_of_store captured) ->
    root_env_store_roots_named
      (capture_store_root_env captured) (captured ++ frame).
Proof.
  intros env captured frame Htyped.
  eapply capture_store_root_env_store_roots_named_in_store.
  exact Htyped.
Qed.

Lemma copy_capture_store_as_captured_store_runtime_ready_in_frame_with_env :
  forall Ω env s Σ captures caps captured env_lt captured_tys frame,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (captured ++ frame) ->
    NoDup (ctx_names (params_ctx caps)) ->
    copy_capture_store_as captures caps s = Some captured ->
    check_make_closure_captures_exact_sctx_with_env env Ω Σ captures caps =
      infer_ok (env_lt, captured_tys) ->
    captured_store_runtime_ready_in_frame env captured
      (capture_store_root_env captured) frame.
Proof.
  intros Ω env s Σ captures caps captured env_lt captured_tys frame
    Hstore Hpres Hnodup Hcopy Hcheck.
  pose proof
    (copy_capture_store_as_captured_entries_typed_with_env_preserved
      Ω env (captured ++ frame) s Σ captures caps captured env_lt
      captured_tys Hstore Hpres Hcopy Hcheck) as Htyped.
  pose proof
    (copy_capture_store_as_captured_values_canonical_roots_with_env
      Ω env s Σ captures caps captured env_lt captured_tys
      Hstore Hcopy Hcheck) as Hvalues.
  assert (Hshadow : store_no_shadow captured).
  { unfold store_no_shadow.
    rewrite (copy_capture_store_as_store_names captures caps s captured Hcopy).
    exact Hnodup. }
  unfold captured_store_runtime_ready_in_frame.
  repeat split.
  - exact Htyped.
  - eapply capture_store_root_env_roots_within; eassumption.
  - exact Hshadow.
  - apply capture_store_root_env_no_shadow. exact Hshadow.
  - eapply capture_store_root_env_store_roots_named. exact Htyped.
  - apply capture_store_root_env_store_keys_named.
Qed.

Lemma captured_call_frame_ready_in_frame_compose :
  forall env captured Rcap s_args R_args,
    captured_store_runtime_ready_in_frame env captured Rcap s_args ->
    store_roots_within R_args s_args ->
    store_no_shadow s_args ->
    root_env_no_shadow R_args ->
    root_env_store_roots_named R_args s_args ->
    root_env_store_keys_named R_args s_args ->
    (forall x, In x (store_names captured) -> ~ In x (store_names s_args)) ->
    (forall x, root_env_lookup x Rcap = None \/
      root_env_lookup x R_args = None) ->
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hcap_ready Hroots_args
    Hshadow_args Hrn_args Hnamed_args Hkeys_args Hstore_disj Hroot_disj.
  unfold captured_store_runtime_ready_in_frame in Hcap_ready.
  destruct Hcap_ready as
    [Hcap_typed
      [Hroots_cap
        [Hshadow_cap
          [Hrn_cap [Hnamed_cap Hkeys_cap]]]]].
  unfold captured_call_frame_ready_in_frame,
    captured_store_runtime_ready_in_frame.
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
  - unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    destruct (root_env_lookup x Rcap) as [roots_cap |] eqn:Hlookup_cap.
    + rewrite (root_env_lookup_app_left x Rcap R_args roots_cap
        Hlookup_cap) in Hlookup.
      inversion Hlookup; subst roots_cap.
      eapply Hnamed_cap; eassumption.
    + rewrite (root_env_lookup_app_right x Rcap R_args Hlookup_cap)
        in Hlookup.
      rewrite store_names_app.
      apply in_or_app. right.
      eapply Hnamed_args; eassumption.
  - apply root_env_store_keys_named_app; assumption.
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

Lemma captured_store_runtime_ready_in_frame_from_self :
  forall env captured Rcap frame,
    captured_store_runtime_ready env captured Rcap ->
    captured_store_runtime_ready_in_frame env captured Rcap frame.
Proof.
  intros env captured Rcap frame Hready.
  unfold captured_store_runtime_ready, captured_store_runtime_ready_in_frame
    in *.
  destruct Hready as
    [Htyped [Hroots [Hshadow [Hrn [Hnamed Hkeys]]]]].
  repeat split.
  - unfold captured_store_typed, store_typed in Htyped.
    eapply store_typed_entries_store_preserved.
    + exact Htyped.
    + apply store_ref_targets_preserved_app_left.
  - exact Hroots.
  - exact Hshadow.
  - exact Hrn.
  - unfold root_env_store_roots_named in *.
    intros x roots z Hlookup Hin.
    rewrite store_names_app.
    apply in_or_app. left.
    eapply Hnamed; eassumption.
  - exact Hkeys.
Qed.

Lemma captured_call_frame_ready_in_frame_from_self :
  forall env captured Rcap s_args R_args,
    captured_call_frame_ready env captured Rcap s_args R_args ->
    captured_call_frame_ready_in_frame env captured Rcap s_args R_args.
Proof.
  intros env captured Rcap s_args R_args Hready.
  unfold captured_call_frame_ready, captured_call_frame_ready_in_frame in *.
  destruct Hready as [Hcap_ready Hrest].
  split.
  - eapply captured_store_runtime_ready_in_frame_from_self.
    exact Hcap_ready.
  - exact Hrest.
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
