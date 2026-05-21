From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyCallFrame.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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

