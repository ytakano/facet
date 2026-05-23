From Facet.TypeSystem Require Export Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyRootFacts TypeSafetyReadiness.
From Stdlib Require Export List Bool ZArith String Program.Equality.
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
