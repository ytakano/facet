From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyFrameScopeReady.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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

Lemma store_remove_params_cleanup_value_typed_excludes :
  forall ps env s_body frame R roots v T,
    store_param_scope ps s_body frame ->
    store_roots_within R s_body ->
    value_roots_within roots v ->
    store_no_shadow s_body ->
    NoDup (ctx_names (params_ctx ps)) ->
    roots_exclude_params ps roots ->
    root_env_excludes_params ps R ->
    value_has_type env s_body v T ->
    exists locals,
      store_remove_params ps s_body = locals ++ frame /\
      value_has_type env (store_remove_params ps s_body) v T /\
      store_refs_exclude_params ps (store_remove_params ps s_body).
Proof.
  intros ps env s_body frame R roots v T Hscope Hstore Hvalue_roots
    Hshadow Hnodup Hexclude_roots Hexclude_env Hvalue.
  destruct (store_remove_params_cleanup_excludes ps s_body frame R roots v
              Hscope Hstore Hvalue_roots Hshadow Hnodup Hexclude_roots
              Hexclude_env)
    as [locals [Hremoved [Hvalue_exclude Hstore_exclude]]].
  exists locals. repeat split; try assumption.
  eapply value_has_type_store_remove_params_excluding; eassumption.
Qed.

Lemma root_env_covers_params_add_params_roots_same_names :
  forall ps_cover ps_add roots R,
    ctx_names (params_ctx ps_cover) = ctx_names (params_ctx ps_add) ->
    params_names_nodup_b ps_add = true ->
    root_env_covers_params ps_cover
      (root_env_add_params_roots_same ps_add roots R).
Proof.
  intros ps_cover ps_add roots R Hnames Hnodup x Hin.
  induction ps_add as [| p ps_add IH] in ps_cover, Hnames, Hnodup, Hin |- *.
  - simpl in Hnames. rewrite Hnames in Hin. contradiction.
  - destruct ps_cover as [| p_cover ps_cover]; simpl in Hnames; try discriminate.
    inversion Hnames as [[Hhead Htail]].
    simpl in Hnodup.
    apply andb_true_iff in Hnodup as [_ Hnodup_tail].
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + subst x. rewrite Hhead.
      exists roots. apply root_env_lookup_add_eq.
    + destruct (IH ps_cover Htail Hnodup_tail Hin) as [roots_old Hlookup].
      destruct (ident_eqb x (param_name p)) eqn:Heq.
      * apply ident_eqb_eq in Heq. subst x.
        exists roots. apply root_env_lookup_add_eq.
      * exists roots_old.
        unfold root_env_add. simpl. rewrite Heq. exact Hlookup.
Qed.

Lemma root_env_excludes_params_names :
  forall ps1 ps2 R,
    ctx_names (params_ctx ps1) = ctx_names (params_ctx ps2) ->
    EnvStructuralRules.root_env_excludes_params ps2 R ->
    root_env_excludes_params ps1 R.
Proof.
  unfold root_env_excludes_params.
  intros ps1 ps2 R Hnames Hexclude x Hin.
  eapply Forall_forall in Hexclude.
  - exact Hexclude.
  - rewrite <- Hnames. exact Hin.
Qed.

Lemma store_refs_exclude_params_removed_names :
  forall ps_store ps_env R s,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_env) ->
    store_roots_within R (store_remove_params ps_store s) ->
    params_names_nodup_b ps_env = true ->
    store_no_shadow s ->
    EnvStructuralRules.root_env_excludes_params ps_env R ->
    store_refs_exclude_params ps_store (store_remove_params ps_store s).
Proof.
  intros ps_store ps_env R s Hnames Hroots Hnodup Hshadow Hexclude.
  eapply store_roots_exclude_params.
  - exact Hroots.
  - eapply root_env_excludes_params_names; eassumption.
  - intros x Hin se Hse.
    eapply store_remove_params_no_param_names.
    + eapply params_names_nodup_b_sound.
      eapply (params_names_nodup_b_names ps_env ps_store).
      * symmetry. exact Hnames.
      * exact Hnodup.
    + exact Hshadow.
    + exact Hin.
    + exact Hse.
Qed.

Lemma store_remove_match_payload_cleanup_value_typed_roots_names :
  forall ps_runtime ps_typed env s_body frame roots v T,
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    store_param_scope ps_runtime s_body frame ->
    value_roots_within roots v ->
    params_names_nodup_b ps_typed = true ->
    EnvStructuralRules.roots_exclude_params ps_typed roots ->
    value_has_type env s_body v T ->
    exists locals,
      store_remove_params ps_runtime s_body = locals ++ frame /\
      value_has_type env (store_remove_params ps_runtime s_body) v T /\
      value_refs_exclude_params ps_runtime v.
Proof.
  intros ps_runtime ps_typed env s_body frame roots v T Hnames Hscope
    Hvalue_roots Hnodup Hroots_excl Hvalue.
  destruct (store_remove_params_store_param_scope ps_runtime s_body frame
              Hscope) as [locals Hremoved].
  assert (Hvalue_exclude : value_refs_exclude_params ps_runtime v).
  { eapply value_roots_exclude_params.
    - exact Hvalue_roots.
    - unfold roots_exclude_params.
      intros x Hin.
      eapply Forall_forall in Hroots_excl.
      + exact Hroots_excl.
      + rewrite <- Hnames. exact Hin. }
  exists locals. repeat split; try assumption.
  eapply value_has_type_store_remove_params_excluding; eassumption.
Qed.

Lemma ctx_remove_params_cons_non_param :
  forall ps x T st m Γ,
    ~ In x (ctx_names (params_ctx ps)) ->
    sctx_remove_params ps ((x, T, st, m) :: Γ) =
      (x, T, st, m) :: sctx_remove_params ps Γ.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros x T st m Γ Hnotin.
  - reflexivity.
  - simpl in *.
    destruct (ident_eqb (param_name p) x) eqn:Heq.
    + apply ident_eqb_eq in Heq. contradiction Hnotin.
      left. exact Heq.
    + rewrite IH.
      * reflexivity.
      * intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma store_remove_params_nil :
  forall ps,
    store_remove_params ps [] = [].
Proof.
  induction ps as [| p ps IH]; simpl; auto.
Qed.

Lemma ctx_remove_params_nil :
  forall ps,
    sctx_remove_params ps [] = [].
Proof.
  induction ps as [| p ps IH]; simpl; auto.
Qed.

Lemma ctx_remove_b_not_in_names :
  forall x Γ,
    ~ In x (ctx_names Γ) ->
    ctx_remove_b x Γ = Γ.
Proof.
  intros x Γ Hnotin.
  induction Γ as [| [[[y T] st] m] Γ IH]; simpl; try reflexivity.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. contradiction Hnotin.
    left. symmetry. exact Heq.
  - rewrite IH; [reflexivity |].
    intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma ctx_remove_b_names_in :
  forall x y Γ,
    In y (ctx_names (ctx_remove_b x Γ)) ->
    In y (ctx_names Γ).
Proof.
  intros x y Γ.
  induction Γ as [| [[[z T] st] m] Γ IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct (ident_eqb x z).
    + right. exact Hin.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. apply IH. exact Hin.
Qed.

Lemma store_remove_names_in :
  forall x y s,
    In y (store_names (store_remove x s)) ->
    In y (store_names s).
Proof.
  intros x y s.
  induction s as [| se s IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct (ident_eqb x (se_name se)).
    + right. exact Hin.
    + simpl in Hin. destruct Hin as [Hin | Hin].
      * left. exact Hin.
      * right. apply IH. exact Hin.
Qed.

Lemma store_entry_refs_exclude_params_head :
  forall ps se s,
    store_refs_exclude_params ps (se :: s) ->
    value_refs_exclude_params ps (se_val se).
Proof.
  intros ps se s Hexclude x Hin.
  specialize (Hexclude x Hin).
  inversion Hexclude; subst.
  match goal with
  | Hentry : store_entry_refs_exclude_root _ se |- _ =>
      destruct se; inversion Hentry; subst; assumption
  end.
Qed.

Lemma store_entry_typed_remove_params_excluding :
  forall env ps s se ce,
    store_entry_typed env s se ce ->
    value_refs_exclude_params ps (se_val se) ->
    store_entry_typed env (store_remove_params ps s) se ce.
Proof.
  intros env ps s [sx sT sv sst] [[[cx cT] cst] cm] Htyped Hexclude.
  simpl in *.
  destruct Htyped as [Hname [HT [Hst Hv]]].
  repeat split; try assumption.
  eapply value_has_type_store_remove_params_excluding; eassumption.
Qed.

Lemma store_entries_typed_names :
  forall env s_source entries Σ,
    Forall2 (store_entry_typed env s_source) entries Σ ->
    store_names entries = ctx_names Σ.
Proof.
  intros env s_source entries Σ Htyped.
  induction Htyped as [| se ce entries_tail Σ_tail Hentry _ IH].
  - reflexivity.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname _].
    simpl. rewrite Hname, IH. reflexivity.
Qed.

Lemma store_refs_exclude_params_in :
  forall ps s se,
    store_refs_exclude_params ps s ->
    In se s ->
    value_refs_exclude_params ps (se_val se).
Proof.
  intros ps s se Hexclude Hin x Hx.
  specialize (Hexclude x Hx).
  induction Hexclude as [| se0 rest Hentry Hrest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst se0. destruct se; inversion Hentry; subst. assumption.
    + apply IH. exact Hin.
Qed.

Lemma store_remove_params_cons_param :
  forall ps se s,
    In (se_name se) (ctx_names (params_ctx ps)) ->
    ~ In (se_name se) (store_names s) ->
    store_remove_params ps (se :: s) = store_remove_params ps s.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros se s Hin Hnotin.
  - simpl in Hin. contradiction.
  - simpl in Hin |- *.
    destruct Hin as [Hin | Hin].
    + rewrite Hin. rewrite ident_eqb_refl.
      rewrite store_remove_not_in_names; [reflexivity | exact Hnotin].
    + destruct (ident_eqb (param_name p) (se_name se)) eqn:Heq.
      * apply ident_eqb_eq in Heq.
        rewrite Heq.
        rewrite store_remove_not_in_names; [reflexivity | exact Hnotin].
      * rewrite IH; [reflexivity | exact Hin |].
        intros Hbad. apply Hnotin.
        eapply store_remove_names_in. exact Hbad.
Qed.

Lemma ctx_remove_params_cons_param :
  forall ps x T st m Γ,
    In x (ctx_names (params_ctx ps)) ->
    ~ In x (ctx_names Γ) ->
    sctx_remove_params ps ((x, T, st, m) :: Γ) =
      sctx_remove_params ps Γ.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros x T st m Γ Hin Hnotin.
  - simpl in Hin. contradiction.
  - simpl in Hin |- *.
    destruct Hin as [Hin | Hin].
    + rewrite Hin. rewrite ident_eqb_refl.
      rewrite ctx_remove_b_not_in_names; [reflexivity | exact Hnotin].
    + destruct (ident_eqb (param_name p) x) eqn:Heq.
      * apply ident_eqb_eq in Heq.
        rewrite Heq.
        rewrite ctx_remove_b_not_in_names; [reflexivity | exact Hnotin].
      * rewrite IH; [reflexivity | exact Hin |].
        intros Hbad. apply Hnotin.
        eapply ctx_remove_b_names_in. exact Hbad.
Qed.

Lemma store_typed_entries_remove_params_excluding_final :
  forall env ps_all ps_store ps_ctx s_source s_target entries Σ,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    s_target = store_remove_params ps_all s_source ->
    Forall2 (store_entry_typed env s_source) entries Σ ->
    NoDup (store_names entries) ->
    store_refs_exclude_params ps_all s_target ->
    (forall se,
      In se (store_remove_params ps_store entries) ->
      In se s_target) ->
    Forall2 (store_entry_typed env s_target)
      (store_remove_params ps_store entries)
      (sctx_remove_params ps_ctx Σ).
Proof.
  intros env ps_all ps_store ps_ctx s_source s_target entries Σ
    Hnames Htarget Htyped.
  subst s_target.
  revert ps_store ps_ctx Hnames.
  induction Htyped as [| se ce entries_tail Σ_tail Hentry Htail IH];
    intros ps_store ps_ctx Hnames Hnodup Hexclude Hin_target.
  - rewrite store_remove_params_nil, ctx_remove_params_nil. constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hnodup.
    inversion Hnodup as [| ? ? Hnotin_tail Hnodup_tail].
    destruct (in_dec
      (fun a b : ident => ltac:(decide equality; [apply Nat.eq_dec | apply string_dec]))
      sx (ctx_names (params_ctx ps_store)))
      as [Hin_ps | Hnotin_ps].
    + rewrite store_remove_params_cons_param.
      * rewrite ctx_remove_params_cons_param.
        -- eapply IH.
           ++ exact Hnames.
           ++ exact Hnodup_tail.
           ++ exact Hexclude.
           ++ intros se Hin.
              apply Hin_target.
              rewrite store_remove_params_cons_param.
              ** exact Hin.
              ** exact Hin_ps.
              ** exact Hnotin_tail.
        -- rewrite <- Hname. rewrite <- Hnames. exact Hin_ps.
        -- rewrite <- Hname.
           rewrite <- (store_entries_typed_names env s_source entries_tail Σ_tail).
           ++ exact Hnotin_tail.
           ++ exact Htail.
      * exact Hin_ps.
      * exact Hnotin_tail.
    + rewrite store_remove_params_cons_non_param.
      * rewrite ctx_remove_params_cons_non_param.
        -- constructor.
           ++ eapply store_entry_typed_remove_params_excluding.
              ** simpl. repeat split; try eassumption.
              ** eapply store_refs_exclude_params_in.
                 --- exact Hexclude.
                 --- apply Hin_target.
                     rewrite store_remove_params_cons_non_param by exact Hnotin_ps.
                     simpl. left. reflexivity.
           ++ eapply IH.
              ** exact Hnames.
              ** exact Hnodup_tail.
              ** exact Hexclude.
              ** intros se Hin.
                 apply Hin_target.
                 rewrite store_remove_params_cons_non_param by exact Hnotin_ps.
                 simpl. right. exact Hin.
        -- rewrite <- Hname. rewrite <- Hnames. exact Hnotin_ps.
      * exact Hnotin_ps.
Qed.

Lemma store_typed_remove_params_excluding_final :
  forall env ps_store ps_ctx s Σ,
    ctx_names (params_ctx ps_store) = ctx_names (params_ctx ps_ctx) ->
    store_typed env s Σ ->
    store_no_shadow s ->
    store_refs_exclude_params ps_store (store_remove_params ps_store s) ->
    store_typed env (store_remove_params ps_store s)
      (sctx_remove_params ps_ctx Σ).
Proof.
  intros env ps_store ps_ctx s Σ Hnames Htyped Hshadow Hexclude.
  eapply store_typed_entries_remove_params_excluding_final
    with (ps_all := ps_store) (s_source := s).
  - exact Hnames.
  - reflexivity.
  - exact Htyped.
  - exact Hshadow.
  - exact Hexclude.
  - intros se Hin. exact Hin.
Qed.

Lemma store_remove_match_payload_cleanup_store_typed_names :
  forall ps_runtime ps_typed env s_body frame R roots v T Σ,
    ctx_names (params_ctx ps_runtime) = ctx_names (params_ctx ps_typed) ->
    store_param_scope ps_runtime s_body frame ->
    store_roots_within R (store_remove_params ps_runtime s_body) ->
    value_roots_within roots v ->
    store_no_shadow s_body ->
    params_names_nodup_b ps_typed = true ->
    EnvStructuralRules.roots_exclude_params ps_typed roots ->
    EnvStructuralRules.root_env_excludes_params ps_typed R ->
    value_has_type env s_body v T ->
    store_typed env s_body Σ ->
    exists locals,
      store_remove_params ps_runtime s_body = locals ++ frame /\
      value_has_type env (store_remove_params ps_runtime s_body) v T /\
      store_refs_exclude_params ps_runtime
        (store_remove_params ps_runtime s_body) /\
      store_typed env (store_remove_params ps_runtime s_body)
        (sctx_remove_params ps_typed Σ).
Proof.
  intros ps_runtime ps_typed env s_body frame R roots v T Σ Hnames Hscope
    Hroots_removed Hvalue_roots Hshadow Hnodup Hroots_excl Henv_excl
    Hvalue Hstore.
  destruct (store_remove_match_payload_cleanup_value_typed_roots_names
              ps_runtime ps_typed env s_body frame roots v T Hnames Hscope
              Hvalue_roots Hnodup Hroots_excl Hvalue)
    as [locals [Hremoved [Hvalue_removed _]]].
  assert (Hstore_refs_excl :
    store_refs_exclude_params ps_runtime
      (store_remove_params ps_runtime s_body)).
  { eapply store_refs_exclude_params_removed_names; eassumption. }
  assert (Hstore_removed :
    store_typed env (store_remove_params ps_runtime s_body)
      (sctx_remove_params ps_typed Σ)).
  { eapply store_typed_remove_params_excluding_final; eassumption. }
  exists locals. repeat split; eassumption.
Qed.

Lemma store_param_prefix_bind_params_length :
  forall ps vs s,
    Datatypes.length vs = Datatypes.length ps ->
    store_param_prefix ps (bind_params ps vs s) s.
Proof.
  induction ps as [| p ps IH]; intros vs s Hlen.
  - constructor.
  - destruct vs as [| v vs]; simpl in Hlen; try discriminate.
    simpl. constructor.
    apply IH. inversion Hlen. reflexivity.
Qed.

Lemma store_param_scope_bind_params_length :
  forall ps vs s,
    Datatypes.length vs = Datatypes.length ps ->
    store_param_scope ps (bind_params ps vs s) s.
Proof.
  intros ps vs s Hlen.
  constructor.
  apply store_param_prefix_bind_params_length. exact Hlen.
Qed.

Lemma store_frame_scope_bind_params_length :
  forall ps vs s Σ,
    Datatypes.length vs = Datatypes.length ps ->
    store_frame_scope ps Σ (bind_params ps vs s) s.
Proof.
  intros ps vs s Σ Hlen.
  constructor.
  apply store_param_prefix_bind_params_length. exact Hlen.
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
