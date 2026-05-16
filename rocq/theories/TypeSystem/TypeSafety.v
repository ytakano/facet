From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Function environment lookup facts                                   *)
(* ------------------------------------------------------------------ *)

Definition fn_env_unique_by_name (env : global_env) : Prop :=
  forall f1 f2,
    In f1 (env_fns env) ->
    In f2 (env_fns env) ->
    fn_name f1 = fn_name f2 ->
    f1 = f2.

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

Lemma lookup_fn_unique_by_name :
  forall env fname f_lookup f_typed,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    In f_typed (env_fns env) ->
    fn_name f_typed = fname ->
    fn_env_unique_by_name env ->
    f_lookup = f_typed.
Proof.
  intros env fname f_lookup f_typed Hlookup Hin_typed Hname_typed Hunique.
  destruct (lookup_fn_in_name fname (env_fns env) f_lookup Hlookup)
    as [Hin_lookup Hname_lookup].
  apply Hunique; try assumption.
  rewrite Hname_lookup. symmetry. exact Hname_typed.
Qed.

Lemma lookup_fn_typed_structural :
  forall env fname f_lookup,
    lookup_fn fname (env_fns env) = Some f_lookup ->
    env_fns_typed_structural env ->
    typed_fn_env_structural env f_lookup.
Proof.
  intros env fname f_lookup Hlookup Henv_typed.
  destruct (lookup_fn_in_name fname (env_fns env) f_lookup Hlookup)
    as [Hin_lookup _].
  apply Henv_typed. exact Hin_lookup.
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

(* ------------------------------------------------------------------ *)
(* Direct place helper facts                                            *)
(* ------------------------------------------------------------------ *)

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

Lemma typed_env_structural_preserves_direct_path_target :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 e_new T_new p T_old x path,
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ e_new T_new Σ1 ->
    exists T_root st,
      sctx_lookup x Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path = Some T_old.
Proof.
  intros env Ω n Σ Σ1 e_new T_new p T_old x path Hplace Hpath Htyped.
  destruct (typed_place_direct_lookup env Σ p T_old x path Hplace Hpath)
    as [T_root [st [Hlookup [_ Htype_path]]]].
  destruct (sctx_same_bindings_lookup Σ Σ1 x T_root st
              (typed_env_structural_same_bindings env Ω n Σ e_new T_new Σ1 Htyped)
              Hlookup)
    as [st1 Hlookup1].
  exists T_root, st1. split; assumption.
Qed.

Lemma typed_env_structural_preserves_var_target :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 e_new T_new x T_old,
    typed_place_env_structural env Σ (PVar x) T_old ->
    typed_env_structural env Ω n Σ e_new T_new Σ1 ->
    exists st,
      sctx_lookup x Σ1 = Some (T_old, st).
Proof.
  intros env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped.
  destruct (typed_env_structural_preserves_direct_path_target
              env Ω n Σ Σ1 e_new T_new (PVar x) T_old x []
              Hplace eq_refl Htyped)
    as [T_root [st [Hlookup Htype_path]]].
  simpl in Htype_path.
  inversion Htype_path; subst T_root.
  exists st. exact Hlookup.
Qed.

Lemma eval_place_direct_runtime_target_exists :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_root [st [HΣ [_ Htype_path]]]].
  destruct (store_typed_lookup_sctx env s Σ x_static T_root st Hstore HΣ)
    as [se [Hlookup [_ [Hse_ty [_ Hvroot]]]]].
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { rewrite Hse_ty. exact Hvroot. }
  assert (Htype_path_se : type_lookup_path env (se_ty se) path_static = Some T).
  { rewrite Hse_ty. exact Htype_path. }
  destruct (value_has_type_path_exists env s (se_val se) (se_ty se)
              path_static T Hvroot_se Htype_path_se)
    as [v_target [Hvalue_path _]].
  exists se, v_target.
  repeat split; assumption.
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

Lemma needs_consume_false_usage :
  forall T,
    needs_consume T = false ->
    ty_usage T = UUnrestricted.
Proof.
  intros [u c] Hconsume.
  destruct u; simpl in Hconsume; try discriminate; reflexivity.
Qed.

Lemma needs_consume_true_usage :
  forall T,
    needs_consume T = true ->
    ty_usage T <> UUnrestricted.
Proof.
  intros [u c] Hconsume Husage.
  destruct u; simpl in Hconsume; discriminate.
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
  | MkTy u (TForall n Ω_forall body) =>
      TC_Forall Ω u u n Ω_forall body body
        (US_refl u) (ty_compatible_refl Ω body)
  | MkTy u core =>
      TC_Core Ω u u core core (US_refl u) eq_refl
  end.

Lemma eval_var_consume_static_copy_contradiction :
  forall env Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  match goal with
  | Heq : T = se_ty se |- _ => rewrite Heq in Husage
  end.
  exact (needs_consume_true_usage (se_ty se) Hconsume Husage).
Qed.

Lemma eval_var_copy_static_move_contradiction :
  forall env Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  match goal with
  | Heq : T = se_ty se |- _ => rewrite Heq in Husage
  end.
  apply Husage.
  exact (needs_consume_false_usage (se_ty se) Hconsume).
Qed.

Lemma eval_place_consume_static_copy_direct_contradiction :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  apply (needs_consume_true_usage T Hconsume Husage).
Qed.

Lemma eval_place_copy_static_move_direct_contradiction :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  apply Husage.
  exact (needs_consume_false_usage T Hconsume).
Qed.

Lemma eval_var_consume_static_copy_contradiction_prefix :
  forall env Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HT [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HT in Hconsume.
  exact (needs_consume_true_usage T Hconsume Husage).
Qed.

Lemma eval_var_copy_static_move_contradiction_prefix :
  forall env Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    False.
Proof.
  intros env Σ s x T se Hstore Hplace Husage Hlookup Hconsume.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HT [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  apply Husage.
  rewrite HT in Hconsume.
  exact (needs_consume_false_usage T Hconsume).
Qed.

Lemma eval_place_consume_static_copy_direct_contradiction_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  apply (needs_consume_true_usage T Hconsume Husage).
Qed.

Lemma eval_place_copy_static_move_direct_contradiction_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval se T_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    False.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval se T_eval
    Hstore Hplace Husage Hpath_static Heval Hlookup Htype_eval Hconsume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ _]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  apply Husage.
  exact (needs_consume_false_usage T Hconsume).
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

Lemma runtime_path_lookup_typing :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall path v_path T_path,
      value_lookup_path v path = Some v_path ->
      type_lookup_path env T path = Some T_path ->
      value_has_type env s v_path T_path) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall name field_value fdef rest v_path T_path,
      lookup_value_field name fields = Some field_value ->
      lookup_field name defs = Some fdef ->
      value_lookup_path field_value rest = Some v_path ->
      type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
        Some T_path ->
      value_has_type env s v_path T_path).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; subst; simpl in *; try discriminate.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path; simpl in *; inversion H; inversion H0; subst; constructor.
  - destruct path as [|seg rest].
    + simpl in *.
      match goal with
      | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
          inversion Hvalue; inversion Htype; subst
      end.
      econstructor; eassumption.
    + simpl in *.
      rewrite lookup_value_field_local in *.
      match goal with
      | Hlookup : lookup_struct name env = Some sdef |- _ =>
          destruct (lookup_struct_success env name sdef Hlookup) as [_ Hstruct_name]
      end.
      match goal with
      | Hlookup : lookup_struct name env = Some sdef,
        Htype : context[lookup_struct (struct_name sdef) env] |- _ =>
          rewrite Hstruct_name in Htype;
          rewrite Hlookup in Htype
      end.
      destruct (lookup_value_field seg fields) as [field_value |] eqn:Hvalue_field;
        try discriminate.
      destruct (lookup_field seg (struct_fields sdef)) as [fdef |] eqn:Hfield;
        try discriminate.
      match goal with
      | IHfields : forall name field_value fdef rest v_path T_path,
          lookup_value_field name fields = Some field_value ->
          lookup_field name (struct_fields sdef) = Some fdef ->
          value_lookup_path field_value rest = Some v_path ->
          type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
            Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHfields; eassumption
      end.
  - match goal with
    | Hvalue : value_lookup_path (VRef _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst; econstructor; eassumption
    end.
  - match goal with
    | Hvalue : value_lookup_path (VClosure _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst
    end.
    eapply VHT_ClosureEmpty. eassumption.
  - match goal with
    | Hvalue : value_lookup_path (VClosure _ _) ?lookup_path = Some _ |- _ =>
        destruct lookup_path
    end; simpl in *; try discriminate.
    match goal with
    | Hvalue : Some _ = Some _, Htype : Some _ = Some _ |- _ =>
        inversion Hvalue; inversion Htype; subst
    end.
    match goal with
    | Hin : In ?fdef (env_fns env) |- _ =>
        eapply VHT_ClosureIn; [exact Hin | reflexivity]
    end.
  - match goal with
    | Hcompat : ty_compatible ?Omega ?T_actual ?T_expected,
      Htype : type_lookup_path env ?T_expected ?lookup_path = Some ?T_path |- _ =>
        destruct (type_lookup_path_compatible env Omega T_actual T_expected
                    lookup_path T_path Hcompat Htype)
          as [T_actual_path [Hactual_path Hcompat_path]]
    end.
    eapply (VHT_Compatible env s Ω v_path T_actual_path T_path).
    + match goal with
      | IHvalue : forall path v_path T_path,
          value_lookup_path _ path = Some v_path ->
          type_lookup_path env _ path = Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHvalue; eassumption
      end.
    + exact Hcompat_path.
  - match goal with
    | Heq : ty_lifetime_equiv ?T_actual ?T_expected,
      Htype : type_lookup_path env ?T_expected ?lookup_path = Some ?T_path |- _ =>
        destruct (type_lookup_path_lifetime_equiv env T_actual T_expected
                    lookup_path T_path Heq Htype)
          as [T_actual_path [Hactual_path Heq_path]]
    end.
    eapply (VHT_LifetimeEquiv env s v_path T_actual_path T_path).
    + match goal with
      | IHvalue : forall path v_path T_path,
          value_lookup_path _ path = Some v_path ->
          type_lookup_path env _ path = Some T_path ->
          value_has_type env s v_path T_path |- _ =>
          eapply IHvalue; eassumption
      end.
    + exact Heq_path.
  - destruct (String.eqb name0 (field_name f)) eqn:Hfield_name.
    + inversion H1; subst field_value.
      inversion H2; subst fdef.
      eapply H; eassumption.
    + eapply H0; eassumption.
Qed.

Lemma value_lookup_path_has_type :
  forall env s path v T v_path T_path,
    value_has_type env s v T ->
    value_lookup_path v path = Some v_path ->
    type_lookup_path env T path = Some T_path ->
    value_has_type env s v_path T_path.
Proof.
  intros env s path v T v_path T_path Htyped Hvalue Htype.
  exact (proj1 (runtime_path_lookup_typing env s) v T Htyped path v_path T_path Hvalue Htype).
Qed.

Inductive value_roots_within : root_set -> value -> Prop :=
  | VRW_Unit :
      forall roots,
      value_roots_within roots VUnit
  | VRW_Int : forall roots i,
      value_roots_within roots (VInt i)
  | VRW_Float : forall roots f,
      value_roots_within roots (VFloat f)
  | VRW_Bool : forall roots b,
      value_roots_within roots (VBool b)
  | VRW_Struct : forall roots name fields,
      value_fields_roots_within roots fields ->
      value_roots_within roots (VStruct name fields)
  | VRW_Ref : forall roots x path,
      In x roots ->
      value_roots_within roots (VRef x path)
  | VRW_ClosureEmpty : forall roots fname,
      value_roots_within roots (VClosure fname [])
with store_entry_roots_within : root_env -> store_entry -> Prop :=
  | SERW_Entry : forall R sx sT sv sst roots,
      root_env_lookup sx R = Some roots ->
      value_roots_within roots sv ->
      store_entry_roots_within R (MkStoreEntry sx sT sv sst)
with store_roots_within : root_env -> store -> Prop :=
  | SRW_Nil :
      forall R,
      store_roots_within R []
  | SRW_Cons : forall R se rest,
      store_entry_roots_within R se ->
      store_roots_within R rest ->
      store_roots_within R (se :: rest)
with value_fields_roots_within
    : root_set -> list (string * value) -> Prop :=
  | VFRW_Nil :
      forall roots,
      value_fields_roots_within roots []
  | VFRW_Cons : forall roots name v rest,
      value_roots_within roots v ->
      value_fields_roots_within roots rest ->
      value_fields_roots_within roots ((name, v) :: rest).

Scheme value_roots_within_ind' := Induction for value_roots_within Sort Prop
with store_entry_roots_within_ind' := Induction for store_entry_roots_within Sort Prop
with store_roots_within_ind' := Induction for store_roots_within Sort Prop
with value_fields_roots_within_ind' := Induction for value_fields_roots_within Sort Prop.
Combined Scheme value_roots_within_mutind
  from value_roots_within_ind', store_entry_roots_within_ind',
       store_roots_within_ind', value_fields_roots_within_ind'.

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

Lemma root_set_union_in_right :
  forall x roots_left roots_right,
    In x roots_right ->
    In x (root_set_union roots_left roots_right).
Proof.
  intros x roots_left roots_right Hin.
  induction roots_left as [| y ys IH]; simpl; try assumption.
  destruct (existsb (ident_eqb y) roots_right).
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
    destruct (existsb (ident_eqb x) roots_right) eqn:Hexists.
    + apply root_set_union_in_right.
      apply existsb_exists in Hexists.
      destruct Hexists as [z [Hz_in Hz_eq]].
      apply ident_eqb_eq in Hz_eq. subst z. exact Hz_in.
    + simpl. left. reflexivity.
  - destruct (existsb (ident_eqb y) roots_right).
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
  - destruct (H0 sx roots e) as [roots' [Hlookup Hincl]].
    eapply SERW_Entry.
    + exact Hlookup.
    + eapply H. exact Hincl.
Qed.

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

Fixpoint root_env_remove_params (ps : list param) (R : root_env)
    : root_env :=
  match ps with
  | [] => R
  | p :: ps' => root_env_remove_params ps' (root_env_remove (param_name p) R)
  end.

Fixpoint root_env_add_params_roots
    (ps : list param) (roots : list root_set) (R : root_env) : root_env :=
  match ps, roots with
  | p :: ps', roots_p :: roots' =>
      root_env_add (param_name p) roots_p
        (root_env_add_params_roots ps' roots' R)
  | _, _ => R
  end.

Definition call_param_root_env
    (ps : list param) (arg_roots : list root_set) (R_tail : root_env)
    : root_env :=
  root_env_add_params_roots ps arg_roots
    (root_env_remove_params ps R_tail).

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

Definition store_no_shadow (s : store) : Prop :=
  NoDup (store_names s).

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

Inductive preservation_ready_expr : expr -> Prop :=
  | PRE_Unit :
      preservation_ready_expr EUnit
  | PRE_Lit : forall lit,
      preservation_ready_expr (ELit lit)
  | PRE_Var : forall x,
      preservation_ready_expr (EVar x)
  | PRE_Fn : forall fname,
      preservation_ready_expr (EFn fname)
  | PRE_Place_Direct : forall p x path,
      place_path p = Some (x, path) ->
      preservation_ready_expr (EPlace p)
  | PRE_Borrow : forall rk p x path,
      place_path p = Some (x, path) ->
      preservation_ready_expr (EBorrow rk p)
  | PRE_Struct : forall sname lts args fields,
      preservation_ready_fields fields ->
      preservation_ready_expr (EStruct sname lts args fields)
  | PRE_Drop : forall e,
      preservation_ready_expr e ->
      preservation_ready_expr (EDrop e)
  | PRE_Assign : forall p e_new x path,
      place_path p = Some (x, path) ->
      preservation_ready_expr e_new ->
      preservation_ready_expr (EAssign p e_new)
  | PRE_Replace : forall p e_new x path,
      place_path p = Some (x, path) ->
      preservation_ready_expr e_new ->
      preservation_ready_expr (EReplace p e_new)
  | PRE_If : forall e1 e2 e3,
      preservation_ready_expr e1 ->
      preservation_ready_expr e2 ->
      preservation_ready_expr e3 ->
      preservation_ready_expr (EIf e1 e2 e3)
with preservation_ready_args : list expr -> Prop :=
  | PRA_Nil :
      preservation_ready_args []
  | PRA_Cons : forall e rest,
      preservation_ready_expr e ->
      preservation_ready_args rest ->
      preservation_ready_args (e :: rest)
with preservation_ready_fields : list (string * expr) -> Prop :=
  | PRF_Nil :
      preservation_ready_fields []
  | PRF_Cons : forall name e rest,
      preservation_ready_expr e ->
      preservation_ready_fields rest ->
      preservation_ready_fields ((name, e) :: rest).

Definition env_fns_preservation_ready (env : global_env) : Prop :=
  forall f, In f (env_fns env) -> preservation_ready_expr (fn_body f).

Inductive preservation_direct_call_ready_expr : expr -> Prop :=
  | PDCR_Ready : forall e,
      preservation_ready_expr e ->
      preservation_direct_call_ready_expr e
  | PDCR_Call : forall fname args,
      preservation_ready_args args ->
      preservation_direct_call_ready_expr (ECall fname args).

Lemma preservation_ready_direct_call_ready :
  forall e,
    preservation_ready_expr e ->
    preservation_direct_call_ready_expr e.
Proof.
  intros e Hready.
  apply PDCR_Ready. exact Hready.
Qed.

Lemma preservation_direct_call_ready_not_call_inv :
  forall e,
    preservation_direct_call_ready_expr e ->
    (forall fname args, e <> ECall fname args) ->
    preservation_ready_expr e.
Proof.
  intros e Hready Hnot_call.
  inversion Hready; subst.
  - exact H.
  - exfalso. apply (Hnot_call fname args). reflexivity.
Qed.

Lemma place_path_rename_place_some :
  forall ρ p x path,
    place_path p = Some (x, path) ->
    exists xr, place_path (rename_place ρ p) = Some (xr, path).
Proof.
  intros ρ p.
  induction p as [root | p IHp | p IHp f]; intros x path Hpath; simpl in Hpath.
  - inversion Hpath; subst. eexists. reflexivity.
  - discriminate.
  - destruct (place_path p) as [[root subpath] |] eqn:Hsub; try discriminate.
    inversion Hpath; subst x path.
    destruct (IHp root subpath eq_refl) as [xr Hrenamed].
    simpl. rewrite Hrenamed. exists xr. reflexivity.
Qed.

Lemma alpha_rename_preservation_ready_expr :
  forall ρ used e er used',
    alpha_rename_expr ρ used e = (er, used') ->
    preservation_ready_expr e ->
    preservation_ready_expr er
with alpha_rename_preservation_ready_args :
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
    preservation_ready_args args ->
    preservation_ready_args argsr
with alpha_rename_preservation_ready_fields :
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
    preservation_ready_fields fields ->
    preservation_ready_fields fieldsr.
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
      eapply PRE_Place_Direct. exact Hpath.
    + inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply PRE_Borrow. exact Hpath.
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
      apply PRE_Struct.
      eapply alpha_rename_preservation_ready_fields; eauto.
    + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
      inversion Hrename; subst.
      apply PRE_Drop.
      eapply alpha_rename_preservation_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply PRE_Assign.
      * exact Hpath.
      * eapply alpha_rename_preservation_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply PRE_Replace.
      * exact Hpath.
      * eapply alpha_rename_preservation_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
      inversion Hrename; subst.
      apply PRE_If.
      * eapply alpha_rename_preservation_ready_expr; eauto.
      * eapply alpha_rename_preservation_ready_expr; eauto.
      * eapply alpha_rename_preservation_ready_expr; eauto.
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
      * eapply alpha_rename_preservation_ready_expr; eauto.
      * eapply alpha_rename_preservation_ready_args; eauto.
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
      * eapply alpha_rename_preservation_ready_expr; eauto.
      * eapply alpha_rename_preservation_ready_fields; eauto.
Qed.

Lemma alpha_rename_fn_def_preservation_ready_body :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    preservation_ready_expr (fn_body f) ->
    preservation_ready_expr (fn_body fr).
Proof.
  intros used f fr used' Hrename Hready.
  unfold alpha_rename_fn_def in Hrename.
  destruct (alpha_rename_params [] (param_names (fn_params f) ++
             free_vars_expr (fn_body f) ++ used) (fn_params f))
    as [[paramsr ρ] used1] eqn:Hparams.
  destruct (alpha_rename_expr ρ used1 (fn_body f)) as [bodyr used2]
    eqn:Hbody.
  inversion Hrename; subst. simpl.
  eapply alpha_rename_preservation_ready_expr; eauto.
Qed.

Lemma alpha_rename_direct_call_ready_expr :
  forall ρ used e er used',
    alpha_rename_expr ρ used e = (er, used') ->
    preservation_direct_call_ready_expr e ->
    preservation_direct_call_ready_expr er.
Proof.
  intros ρ used e er used' Hrename Hready.
  inversion Hready; subst.
  - apply PDCR_Ready.
    eapply alpha_rename_preservation_ready_expr; eassumption.
  - simpl in Hrename.
    destruct
      ((fix go (used0 : list ident) (args0 : list expr)
          {struct args0} : list expr * list ident :=
         match args0 with
         | [] => ([], used0)
         | arg :: rest =>
             let (arg', used1) := alpha_rename_expr ρ used0 arg in
             let (rest', used2) := go used1 rest in
             (arg' :: rest', used2)
         end) used args)
      as [argsr used_args] eqn:Hargs.
    inversion Hrename; subst.
    apply PDCR_Call.
    eapply alpha_rename_preservation_ready_args; eassumption.
Qed.

Lemma lookup_alpha_rename_fn_def_preservation_ready_body :
  forall env fname fdef fcall used used',
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def used fdef = (fcall, used') ->
    preservation_ready_expr (fn_body fcall).
Proof.
  intros env fname fdef fcall used used' Hlookup Henv_ready Hrename.
  destruct (lookup_fn_in_name fname (env_fns env) fdef Hlookup)
    as [Hin _].
  eapply alpha_rename_fn_def_preservation_ready_body.
  - exact Hrename.
  - apply Henv_ready. exact Hin.
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
        (sctx_of_ctx (params_ctx (fn_params f)))
        (fn_body f) T_body (sctx_of_ctx Γ_out) /\
      ty_compatible_b (fn_outlives f) T_body (fn_ret f) = true /\
      params_ok_env_b env (fn_params f) Γ_out = true.
Proof.
  intros env f Htyped.
  unfold typed_fn_env_structural in Htyped.
  exact Htyped.
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

Lemma preservation_ready_fields_lookup :
  forall fields name e,
    preservation_ready_fields fields ->
    lookup_expr_field name fields = Some e ->
    preservation_ready_expr e.
Proof.
  intros fields name e Hready.
  induction Hready as [| fname field_expr rest Hexpr _ IH];
    simpl; intros Hlookup.
  - discriminate.
  - destruct (String.eqb name fname) eqn:Hname.
    + inversion Hlookup; subst. exact Hexpr.
    + apply IH. exact Hlookup.
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
    inversion Htyped; subst.
    all: repeat split; try assumption;
      eapply store_roots_within_lookup_value; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst.
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
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _.
    inversion Hready.
  - intros s fname Ω n R Σ T Σ' R' roots _ Hroots Hnodup Hrn Htyped.
    inversion Htyped; subst. repeat split; try assumption; constructor.
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
    repeat split; try assumption.
    apply value_roots_within_union_r. exact Hv3.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R' roots
      Hready _ _ _ _.
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

Definition root_env_covers_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    exists roots, root_env_lookup x R = Some roots.

Definition roots_exclude_params (ps : list param) (roots : root_set) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    roots_exclude x roots.

Definition root_env_excludes_params (ps : list param) (R : root_env) : Prop :=
  forall x,
    In x (ctx_names (params_ctx ps)) ->
    root_env_excludes x R.

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
  assert (existsb (ident_eqb x) roots = true) as Hexists.
  { apply existsb_exists.
    exists x. split.
    - exact Hin.
    - apply ident_eqb_refl. }
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
    inversion Htyped; subst.
    match goal with
    | Hready1 : provenance_ready_expr e1,
      Hready2 : provenance_ready_expr e2,
      Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
        ?R1_body ?roots1_body,
      Hfresh : root_env_lookup x ?R1_body = None,
      Htyped2 : typed_env_roots env Ω n
        (root_env_add x ?roots1_body ?R1_body)
        (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
        ?R2_body ?roots2_body |- _ =>
        destruct (IH1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
                    ps frame Hready1 Htyped1 Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        pose proof (root_env_covers_params_lookup_none_not_in
                      ps R1_body x Hcover1 Hfresh) as Hnotin;
        pose proof (root_env_covers_params_add
                      ps R1_body x roots1_body Hcover1) as Hcover_add;
        pose proof (store_param_scope_add
                      ps s1 frame1 x T_ann v1 Hnotin Hscope1) as Hscope_add;
        destruct (IH2 Ω n (root_env_add x roots1_body R1_body)
                    (sctx_add x T_ann m Σ1_body) T2_body Σ2_body
                    R2_body roots2_body ps frame1 Hready2 Htyped2
                    Hcover_add Hscope_add)
          as [Hcover2 [frame2 Hscope2]];
        split;
        [ eapply root_env_covers_params_remove_non_param; eassumption
        | eapply store_param_scope_remove_non_param; eassumption ]
    end.
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
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready _ _ _.
    inversion Hready.
  - intros s fname Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover Hscope.
    inversion Htyped; subst. split; [exact Hcover | exists frame; exact Hscope].
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Hready_then : provenance_ready_expr e2,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1
        ?R1 ?roots_cond,
      Htyped_then : typed_env_roots env Ω n ?R1 ?Σ1 e2 ?T2 ?Σ2
        ?R2 ?roots2 |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                    Hready_cond Htyped_cond Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        exact (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2 ps frame1
                 Hready_then Htyped_then Hcover1 Hscope1)
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots ps frame Hready Htyped Hcover Hscope.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Hready_else : provenance_ready_expr e3,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1
        ?R1 ?roots_cond,
      Htyped_else : typed_env_roots env Ω n ?R1 ?Σ1 e3 ?T3 ?Σ3
        ?R3 ?roots3 |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond ps frame
                    Hready_cond Htyped_cond Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        exact (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3 ps frame1
                 Hready_else Htyped_else Hcover1 Hscope1)
    end.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R' roots
      ps frame Hready _ _ _.
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
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Htyped_rest : typed_fields_roots env Ω n lts ?args_inst ?R1 ?Σ1
        ?fields0 rest ?Σ2 ?R2 ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                    Hready_field Htyped_field Hcover Hscope)
          as [Hcover1 [frame1 Hscope1]];
        exact (IHrest Ω n lts args0 R1 Σ1 Σ' R' roots_rest ps frame1
                 Hready Htyped_rest Hcover1 Hscope1)
    end.
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
      dependent destruction Htyped.
      match goal with
      | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
        Htyped_field : typed_env_roots env Ω n R Σ _ ?T_field ?Σ1
          ?R1 ?roots_field,
        Htyped_rest : typed_fields_roots env Ω n lts args ?R1 ?Σ1
          ?fields0 rest ?Σ2 ?R2 ?roots_rest |- _ =>
          rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
          rewrite Hlookup_typed in Hlookup_expr;
          inversion Hlookup_expr; subst e_field;
          destruct (Hexpr env s e s1 v Heval_field Ω n R Σ T_field Σ1
                      R1 roots_field ps frame Hready_field Htyped_field
                      Hcover Hroots Hshadow Hrn Hscope Hfresh)
            as [Hcover1 [Hroots1 [Hshadow1 [Hrn1 [Hscope1 Hfresh1]]]]];
          exact (IHrest Ω n lts args R1 Σ1 Σ2 R2 roots_rest ps frame
                   Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                   Hscope1 Hfresh1)
      end.
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
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 (PVar x) ?T0 |- _ =>
          destruct (typed_place_direct_lookup env Σ0 (PVar x) T0 x []
                    Hplace eq_refl) as [T_root [st [Hlookup_ctx _]]];
          assert (Hscope_used :
            store_frame_scope ps Σ0 (store_mark_used x s) frame)
          by (eapply store_frame_scope_mark_used;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh | exact Hscope ])
      end.
      repeat split; assumption.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 (PVar x) ?T0 |- _ =>
          destruct (typed_place_direct_lookup env Σ0 (PVar x) T0 x []
                    Hplace eq_refl) as [T_root [st [Hlookup_ctx _]]];
          assert (Hscope_used :
            store_frame_scope ps Σ0 (store_mark_used x s) frame)
          by (eapply store_frame_scope_mark_used;
              [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
              | exact Hfresh | exact Hscope ])
      end.
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
                  ps R1 x Hcover1 H8) as Hnotin.
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
    destruct (proj1 eval_preserves_roots_ready_mutual env
                (store_add x T_ann v1 s1) e2 s2 v2 Heval2
                Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots Hready2
                Hadd_roots Hadd_shadow Hadd_rn H13)
      as [Hroots2 [_ [Hshadow2 Hrn2]]].
    destruct (IH2 Ω n (root_env_add x roots1 R1)
                (sctx_add x T_ann m Σ1) T Σ2 R2 roots ps frame
                Hready2 H13
                (root_env_covers_params_add ps R1 x roots1 Hcover1)
                Hadd_roots Hadd_shadow Hadd_rn Hscope_add Hfresh_add)
      as [Hcover2 [Hscope2 Hfresh2]].
    assert (Hin_x_Σ2 : In x (ctx_names Σ2)).
    { pose proof (typed_env_structural_same_bindings env Ω n
                    (sctx_add x T_ann m Σ1) e2 T Σ2
                    (typed_env_roots_structural env Ω n
                      (root_env_add x roots1 R1)
                      (sctx_add x T_ann m Σ1) e2 T Σ2 R2 roots H13))
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
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1
        ?R1 ?roots_new,
      Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
      Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ1 x [] Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        assert (Hscope2 : store_frame_scope ps Σ1 s2 frame)
          by (eapply store_frame_scope_update_val;
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
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots ps frame Hready Htyped
      Hcover Hroots Hshadow Hrn Hscope Hfresh.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    match goal with
    | Hpath_var : place_path (PVar _) = Some _ |- _ =>
        simpl in Hpath_var; inversion Hpath_var; subst; clear Hpath_var
    end.
    match goal with
    | Hready_new : provenance_ready_expr e_new,
      Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1
        ?roots_new,
      Havailable : sctx_path_available Σ' x [] = infer_ok tt |- _ =>
        destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new ps frame
                    Hready_new Htyped_new Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        destruct (sctx_path_available_success Σ' x [] Havailable)
          as [T_root [st [Hlookup_ctx _]]];
        repeat split;
        [ apply root_env_covers_params_update; exact Hcover1
        | eapply store_frame_scope_update_val;
          [ eapply sctx_lookup_in_ctx_names; exact Hlookup_ctx
          | exact Hfresh1 | exact Hscope1 | exact Hupdate ]
        | exact Hfresh1 ]
    end.
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
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots ps frame
      Hready _ _ _ _ _ _ _.
    inversion Hready.
  - intros s fname Ω n R Σ T Σ' R' roots ps frame _ Htyped Hcover
      _ _ _ Hscope Hfresh.
    inversion Htyped; subst. repeat split; assumption.
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
    + exact Hcover3.
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
      Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R' roots
      ps frame Hready _ _ _ _ _ _ _.
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
    dependent destruction Htyped.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Htyped_rest : typed_fields_roots env Ω n lts ?args_inst ?R1 ?Σ1
        ?fields0 rest ?Σ2 ?R2 ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hroots Hshadow Hrn Htyped_field)
          as [Hroots1 [_ [Hshadow1 Hrn1]]];
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field ps frame
                    Hready_field Htyped_field Hcover Hroots Hshadow Hrn
                    Hscope Hfresh)
          as [Hcover1 [Hscope1 Hfresh1]];
        exact (IHrest Ω n lts args_inst R1 Σ1 Σ2 R2 roots_rest ps frame
                 Hready Htyped_rest Hcover1 Hroots1 Hshadow1 Hrn1
                 Hscope1 Hfresh1)
    end.
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

Lemma bind_params_head_fresh_in_tail :
  forall env Ω s p ps vs,
    NoDup (ctx_names (params_ctx (p :: ps))) ->
    params_fresh_in_store (p :: ps) s ->
    eval_args_values_have_types env Ω s vs ps ->
    ~ In (param_name p) (store_names (bind_params ps vs s)).
Proof.
  intros env Ω s p ps vs Hnodup Hfresh Hargs.
  rewrite (store_names_bind_params env Ω s vs ps Hargs).
  rewrite in_app_iff.
  intros [Hin_params | Hin_store].
  - exact (params_ctx_names_nodup_head_not_tail p ps Hnodup Hin_params).
  - exact (params_fresh_in_store_head p ps s Hfresh Hin_store).
Qed.

Lemma bind_params_store_no_shadow :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_no_shadow s ->
    store_no_shadow (bind_params ps vs s).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs Hshadow.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - exact Hshadow.
  - simpl.
    apply store_no_shadow_add.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma bind_params_store_roots_within_call_param_root_env :
  forall env Ω s vs ps R_tail arg_roots,
    eval_args_values_have_types env Ω s vs ps ->
    Forall2 value_roots_within arg_roots vs ->
    store_roots_within R_tail s ->
    store_no_shadow s ->
    root_env_no_shadow R_tail ->
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    store_roots_within (call_param_root_env ps arg_roots R_tail)
      (bind_params ps vs s).
Proof.
  intros env Ω s vs ps R_tail arg_roots Hargs Hvalues Hroots Hshadow
    Hrn Hnodup Hfresh.
  revert R_tail arg_roots Hroots Hrn Hnodup Hfresh Hvalues.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH];
    intros R_tail arg_roots Hroots Hrn Hnodup Hfresh Hvalues; simpl in *.
  - inversion Hvalues; subst. exact Hroots.
  - inversion Hvalues as [| ? ? ? ? Hvalue Hvalues_tail]; subst.
    rename l into arg_roots_tail.
    inversion Hnodup as [| ? ? Hnotin_tail Hnodup_tail]; subst.
    assert (Htail_roots_base :
      store_roots_within (root_env_remove (param_name p) R_tail) s).
    { apply store_roots_within_remove_env.
      - exact Hroots.
      - intros se Hin Heq.
        pose proof (store_entry_name_in_store_names se s Hin) as Hse_name.
        rewrite Heq in Hse_name.
        exact (params_fresh_in_store_head p ps s Hfresh Hse_name). }
    assert (Htail_roots :
      store_roots_within
        (call_param_root_env ps arg_roots_tail
          (root_env_remove (param_name p) R_tail))
        (bind_params ps vs s)).
    { apply IH.
      - exact Htail_roots_base.
      - apply root_env_no_shadow_remove. exact Hrn.
      - exact Hnodup_tail.
      - eapply params_fresh_in_store_tail. exact Hfresh.
      - exact Hvalues_tail. }
    assert (Hparam_fresh_root :
      root_env_lookup (param_name p)
        (call_param_root_env ps arg_roots_tail
          (root_env_remove (param_name p) R_tail)) = None).
    { unfold call_param_root_env.
      rewrite root_env_add_params_roots_lookup_not_in.
      - rewrite root_env_lookup_remove_params_not_in.
        + apply root_env_lookup_remove_eq_no_shadow. exact Hrn.
        + exact Hnotin_tail.
      - exact Hnotin_tail. }
    apply store_add_roots_within.
    + exact Htail_roots.
    + exact Hparam_fresh_root.
    + exact Hvalue.
Qed.

Lemma eval_args_bind_params_call_param_root_env_ready :
  forall env s args s_args vs Ω n R Σ ps_typed Σ_args R_args arg_roots
      ps_bind,
    eval_args env s args s_args vs ->
    provenance_ready_args args ->
    typed_args_roots env Ω n R Σ args ps_typed Σ_args R_args arg_roots ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    NoDup (ctx_names (params_ctx ps_bind)) ->
    params_fresh_in_store ps_bind s_args ->
    eval_args_values_have_types env Ω s_args vs ps_bind ->
    store_roots_within (call_param_root_env ps_bind arg_roots R_args)
      (bind_params ps_bind vs s_args) /\
    store_no_shadow (bind_params ps_bind vs s_args) /\
    root_env_no_shadow (call_param_root_env ps_bind arg_roots R_args) /\
    root_env_covers_params ps_bind
      (call_param_root_env ps_bind arg_roots R_args).
Proof.
  intros env s args s_args vs Ω n R Σ ps_typed Σ_args R_args arg_roots
    ps_bind
    Heval_args Hready Htyped_args Hroots Hshadow Hrn Hnodup Hfresh
    Hargs_values.
  destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ ps_typed Σ_args
              R_args arg_roots Hready Hroots Hshadow Hrn Htyped_args)
    as [Hroots_args [Hvalues [Hshadow_args Hrn_args]]].
  repeat split.
  - eapply bind_params_store_roots_within_call_param_root_env; eassumption.
  - eapply bind_params_store_no_shadow; eassumption.
  - apply call_param_root_env_no_shadow; assumption.
  - apply call_param_root_env_covers_params.
    + exact Hnodup.
    + rewrite (Forall2_length Hvalues).
      eapply eval_args_values_have_types_length. exact Hargs_values.
Qed.

Lemma bind_params_ref_targets_preserved :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_ref_targets_preserved env s (bind_params ps vs s).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - apply store_ref_targets_preserved_refl.
  - simpl.
    eapply store_ref_targets_preserved_trans.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma bind_params_store_typed_prefix :
  forall env Ω s vs ps,
    NoDup (ctx_names (params_ctx ps)) ->
    params_fresh_in_store ps s ->
    eval_args_values_have_types env Ω s vs ps ->
    store_typed_prefix env (bind_params ps vs s) (sctx_of_ctx (params_ctx ps)).
Proof.
  intros env Ω s vs ps Hnodup Hfresh Hargs.
  induction Hargs as [| v vs p ps T_actual Hv Hcompat Hargs IH].
  - simpl. unfold store_typed_prefix. exists [], s. split.
    + reflexivity.
    + constructor.
  - simpl.
    eapply store_typed_prefix_add_compatible.
    + apply IH.
      * eapply params_ctx_names_nodup_tail. exact Hnodup.
      * eapply params_fresh_in_store_tail. exact Hfresh.
    + eapply value_has_type_store_preserved.
      * exact Hv.
      * eapply bind_params_ref_targets_preserved.
        -- eapply params_ctx_names_nodup_tail. exact Hnodup.
        -- eapply params_fresh_in_store_tail. exact Hfresh.
        -- exact Hargs.
    + exact Hcompat.
    + apply store_add_fresh_ref_targets_preserved.
      apply store_lookup_not_in_names.
      eapply bind_params_head_fresh_in_tail; eassumption.
Qed.

Lemma eval_args_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s args params
      s' values,
    store_typed env s Σ ->
    typed_args_env_structural env Ω n Σ args params Σ' ->
    eval_args env s args s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    eval_args_values_have_types env Ω s' values params /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s args params s' values
    Hstore Htyped Heval Hpres.
  revert s s' values Hstore Heval.
  induction Htyped as
      [Σ
      |Σ Σ1 Σ2 e es p ps T_e Htyped_e Hcompat Htyped_rest IH];
    intros s s' values Hstore Heval.
  - inversion Heval; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - inversion Heval; subst.
    match goal with
    | Heval_e : eval env s e ?s1 ?v,
      Heval_rest : eval_args env ?s1 es s' ?vs |- _ =>
        destruct (Hpres Σ s e T_e Σ1 s1 v Hstore Htyped_e Heval_e)
          as [Hstore1 [Hv Hpres1]];
        destruct (IH s1 s' vs Hstore1 Heval_rest)
          as [Hstore2 [Hargs_values Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs_values ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
Qed.

Lemma eval_struct_fields_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) lts args Σ Σ' s fields defs
      s' values,
    store_typed env s Σ ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
    eval_struct_fields env s fields defs s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    struct_fields_have_type env s' lts args values defs /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n lts args Σ Σ' s fields defs s' values
    Hstore Htyped Heval Hpres.
  revert s s' values Hstore Heval.
  induction Htyped as
      [lts args Σ fields
      | lts args Σ Σ1 Σ2 fields f rest e_field T_field
          Hlookup Htyped_field Hcompat Htyped_rest IH];
    intros s s' values Hstore Heval.
  - inversion Heval; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - inversion Heval; subst.
    rewrite lookup_field_b_lookup_expr_field in Hlookup.
    match goal with
    | Hexpr : lookup_expr_field (field_name f) fields = Some _ |- _ =>
        rewrite Hlookup in Hexpr; inversion Hexpr; subst
    end.
    match goal with
    | Htyped_e : typed_env_structural env Ω n Σ ?e T_field Σ1,
      Heval_field : eval env s ?e ?s1 ?v,
      Heval_rest : eval_struct_fields env ?s1 fields rest s' ?values_tail |- _ =>
        destruct (Hpres Σ s e T_field Σ1 s1 v
                    Hstore Htyped_e Heval_field)
          as [Hstore1 [Hvalue Hpres1]];
        destruct (IH s1 s' values_tail Hstore1 Heval_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
Qed.

Lemma eval_struct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s'
      name lts args fields values sdef,
    store_typed env s Σ ->
    lookup_struct name env = Some sdef ->
    typed_fields_env_structural env Ω n lts args Σ fields (struct_fields sdef) Σ' ->
    eval_struct_fields env s fields (struct_fields sdef) s' values ->
    (forall Σ0 s0 e T Σ1 s1 v,
      store_typed env s0 Σ0 ->
      typed_env_structural env Ω n Σ0 e T Σ1 ->
      eval env s0 e s1 v ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v T /\
      store_ref_targets_preserved env s0 s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' (VStruct name values)
      (instantiate_struct_instance_ty sdef lts args) /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' name lts args fields values sdef
    Hstore Hlookup Htyped_fields Heval_fields Hpres.
  destruct (eval_struct_fields_preserves_typing env Ω n lts args
              Σ Σ' s fields (struct_fields sdef) s' values
              Hstore Htyped_fields Heval_fields Hpres)
    as [Hstore' [Hfields Hpres_store]].
  split.
  - exact Hstore'.
  - split.
    + econstructor; eassumption.
    + exact Hpres_store.
Qed.

(* ------------------------------------------------------------------ *)
(* Basic big-step preservation cases                                    *)
(* ------------------------------------------------------------------ *)

Lemma eval_unit_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ s Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_int_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s i,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VInt i) (MkTy UUnrestricted TIntegers).
Proof.
  intros env Ω n Σ s i Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_float_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s f,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VFloat f) (MkTy UUnrestricted TFloats).
Proof.
  intros env Ω n Σ s f Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_lit_bool_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s b,
    store_typed env s Σ ->
    store_typed env s Σ /\
    value_has_type env s (VBool b) (MkTy UUnrestricted TBooleans).
Proof.
  intros env Ω n Σ s b Hstore.
  split; [exact Hstore | constructor].
Qed.

Lemma eval_fn_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s fname fdef,
    store_typed env s Σ ->
    In fdef (env_fns env) ->
    fn_name fdef = fname ->
    store_typed env s Σ /\
    value_has_type env s (VClosure fname []) (fn_value_ty fdef).
Proof.
  intros env Ω n Σ s fname fdef Hstore Hin Hname.
  split; [exact Hstore |].
  eapply VHT_ClosureIn; eassumption.
Qed.

Lemma eval_var_copy_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    store_typed env s Σ /\
    value_has_type env s (se_val se) T.
Proof.
  intros env Ω n Σ s x T se Hstore Hplace _ Hlookup _.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst.
  split; [exact Hstore | exact Hv].
Qed.

Lemma eval_var_move_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s x T se,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    sctx_consume_path Σ x [] = infer_ok Σ' ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    se_used se = false ->
    store_typed env (store_mark_used x s) Σ' /\
    value_has_type env (store_mark_used x s) (se_val se) T.
Proof.
  intros env Ω n Σ Σ' s x T se Hstore Hplace _ Hconsume Hlookup _ _.
  inversion Hplace; subst; clear Hplace.
  destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
    as [Tse [stse [m [HΣ [Hname [HT [Hst Hv]]]]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HΣ
  end.
  inversion HΣ; subst Tse stse.
  destruct (sctx_consume_path_success Σ x [] Σ' Hconsume)
    as [T0 [st0 [HlookupΣ [_ Hupdate]]]].
  match goal with
  | Hsctx : sctx_lookup x Σ = Some (T, ?st) |- _ =>
      rewrite Hsctx in HlookupΣ
  end.
  inversion HlookupΣ; subst T0 st0.
  split.
  - eapply store_typed_mark_used; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hv.
    + apply store_mark_used_ref_targets_preserved.
Qed.

Lemma eval_place_copy_direct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_typed env s Σ /\ value_has_type env s v T.
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval se T_eval v
    Hstore Hplace _ Hpath_static Heval Hlookup _ Htype_eval _ Hvalue.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  split; [exact Hstore |].
  eapply value_lookup_path_has_type; eassumption.
Qed.

Lemma eval_place_move_direct_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    sctx_consume_path Σ x_static path_static = infer_ok Σ' ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_consume_path x_eval path_eval s = Some s' ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' p T x_static path_static x_eval path_eval se
    T_eval v Hstore Hplace _ Hpath_static Hconsume Heval Hlookup _
    Htype_eval _ Hvalue Hstore_consume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hlookup)
    as [T_root [st [m [HΣ [Hname [HTy [Hst Hvroot]]]]]]].
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  rewrite HΣstatic in HΣ.
  inversion HΣ; subst T_static st_static.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  assert (Hvpath : value_has_type env s v T).
  { eapply value_lookup_path_has_type; eassumption. }
  split.
  - eapply store_typed_consume_path; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hvpath.
    + unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_static s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_static);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
Qed.

Lemma eval_var_copy_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T = UUnrestricted ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = false ->
    store_typed_prefix env s Σ /\
    value_has_type env s (se_val se) T.
Proof.
  intros env Ω n Σ s x T se Hstore Hplace _ Hlookup _.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HTy [_ Hv]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  split; assumption.
Qed.

Lemma eval_var_move_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s x T se,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T ->
    ty_usage T <> UUnrestricted ->
    sctx_consume_path Σ x [] = infer_ok Σ' ->
    store_lookup x s = Some se ->
    needs_consume (se_ty se) = true ->
    se_used se = false ->
    store_typed_prefix env (store_mark_used x s) Σ' /\
    value_has_type env (store_mark_used x s) (se_val se) T.
Proof.
  intros env Ω n Σ Σ' s x T se Hstore Hplace _ Hconsume Hlookup _ _.
  destruct (typed_place_direct_lookup env Σ (PVar x) T x [] Hplace eq_refl)
    as [T_root [st [HΣ [_ Htype]]]].
  simpl in Htype. inversion Htype; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T st Hstore HΣ)
    as [se' [Hlookup' [_ [HTy [_ Hv]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  destruct (sctx_consume_path_success Σ x [] Σ' Hconsume)
    as [T0 [st0 [HlookupΣ [_ Hupdate]]]].
  rewrite HΣ in HlookupΣ.
  inversion HlookupΣ; subst T0 st0.
  split.
  - eapply store_typed_prefix_mark_used; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hv.
    + apply store_mark_used_ref_targets_preserved.
Qed.

Lemma eval_place_copy_direct_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T = UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = false ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_typed_prefix env s Σ /\ value_has_type env s v T.
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval se T_eval v
    Hstore Hplace _ Hpath_static Heval Hlookup _ Htype_eval _ Hvalue.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ Hvroot]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  split; [exact Hstore |].
  eapply value_lookup_path_has_type; eassumption.
Qed.

Lemma eval_place_move_direct_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p T
      x_static path_static x_eval path_eval se T_eval v,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    ty_usage T <> UUnrestricted ->
    place_path p = Some (x_static, path_static) ->
    sctx_consume_path Σ x_static path_static = infer_ok Σ' ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    binding_available_b (se_state se) path_eval = true ->
    type_lookup_path env (se_ty se) path_eval = Some T_eval ->
    needs_consume T_eval = true ->
    value_lookup_path (se_val se) path_eval = Some v ->
    store_consume_path x_eval path_eval s = Some s' ->
    store_typed_prefix env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' p T x_static path_static x_eval path_eval se
    T_eval v Hstore Hplace _ Hpath_static Hconsume Heval Hlookup _
    Htype_eval _ Hvalue Hstore_consume.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_static [st_static [HΣstatic [_ Htype_static]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_static st_static Hstore HΣstatic)
    as [se' [Hlookup' [_ [HTy [_ Hvroot]]]]].
  rewrite Hlookup in Hlookup'.
  inversion Hlookup'; subst se'.
  rewrite HTy in Htype_eval.
  rewrite Htype_static in Htype_eval.
  inversion Htype_eval; subst T_eval.
  assert (Hvpath : value_has_type env s v T).
  { eapply value_lookup_path_has_type; eassumption. }
  split.
  - eapply store_typed_prefix_consume_path; eassumption.
  - eapply value_has_type_store_preserved.
    + exact Hvpath.
    + unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_static s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_static);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
Qed.

Lemma eval_place_direct_runtime_target_exists_prefix :
  forall env Σ s p T x_static path_static x_eval path_eval,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    eval_place s p x_eval path_eval ->
    exists se v_target,
      store_lookup x_eval s = Some se /\
      value_lookup_path (se_val se) path_eval = Some v_target /\
      type_lookup_path env (se_ty se) path_eval = Some T.
Proof.
  intros env Σ s p T x_static path_static x_eval path_eval
    Hstore Hplace Hpath_static Heval_place.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static)
    as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T x_static path_static
              Hplace Hpath_static)
    as [T_root [st [HΣ [_ Htype_path]]]].
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_root st Hstore HΣ)
    as [se [Hlookup [_ [Hse_ty [_ Hvroot]]]]].
  assert (Hvroot_se : value_has_type env s (se_val se) (se_ty se)).
  { rewrite Hse_ty. exact Hvroot. }
  assert (Htype_path_se : type_lookup_path env (se_ty se) path_static = Some T).
  { rewrite Hse_ty. exact Htype_path. }
  destruct (value_has_type_path_exists env s (se_val se) (se_ty se)
              path_static T Hvroot_se Htype_path_se)
    as [v_target [Hvalue_path _]].
  exists se, v_target.
  repeat split; assumption.
Qed.

Lemma eval_drop_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' e T v,
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e T Σ' ->
     eval env s e s' v ->
     store_typed env s' Σ' /\ value_has_type env s' v T) ->
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    eval env s e s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ' s s' e T v Hpres Hstore Htyped Heval.
  destruct (Hpres Hstore Htyped Heval) as [Hstore' _].
  split; [exact Hstore' | constructor].
Qed.

Lemma eval_let_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2
      m x T T1 e1 e2 T2 v1 v2,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T1 Σ1 ->
    eval env s e1 s1 v1 ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T1 Σ1 ->
     eval env s e1 s1 v1 ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 v1 T1 /\
     store_ref_targets_preserved env s s1) ->
    ty_compatible_b Ω T1 T = true ->
    store_ref_targets_preserved env s1 (store_add x T v1 s1) ->
    typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
    eval env (store_add x T v1 s1) e2 s2 v2 ->
    (store_typed env (store_add x T v1 s1) (sctx_add x T m Σ1) ->
     typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
     eval env (store_add x T v1 s1) e2 s2 v2 ->
     store_typed env s2 Σ2 /\
     value_has_type env s2 v2 T2 /\
     store_ref_targets_preserved env (store_add x T v1 s1) s2) ->
    store_lookup x s1 = None ->
    value_refs_exclude_root x v2 ->
    store_refs_exclude_root x (store_remove x s2) ->
    store_typed env (store_remove x s2) (sctx_remove x Σ2) /\
    value_has_type env (store_remove x s2) v2 T2 /\
    store_ref_targets_preserved env s (store_remove x s2).
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 m x T T1 e1 e2 T2 v1 v2
    Hstore Htyped1 Heval1 Hpres1 Hcompat Hadd_pres Htyped2 Heval2
    Hpres2 Hfresh Hexclude_v Hexclude_store.
  destruct (Hpres1 Hstore Htyped1 Heval1) as [Hstore1 [Hv1 Hpres_s_s1]].
  pose proof (ty_compatible_b_sound Ω T1 T Hcompat) as Hcompat_prop.
  pose proof (store_typed_add_compatible env Ω s1 Σ1 x T1 T m v1
                Hstore1 Hv1 Hcompat_prop) as Hstore_add.
  specialize (Hstore_add Hadd_pres).
  destruct (Hpres2 Hstore_add Htyped2 Heval2)
    as [Hstore2 [Hv2 Hpres_add_s2]].
  split.
  - eapply store_typed_remove_excluding_root; eassumption.
  - split.
    + eapply value_has_type_store_remove_excluding_root; eassumption.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_s_s1.
      * eapply store_ref_targets_preserved_remove_after_absent_root.
        -- eapply store_ref_targets_preserved_trans.
           ++ exact Hadd_pres.
           ++ exact Hpres_add_s2.
        -- exact Hfresh.
Qed.

Lemma eval_let_roots_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R R1 R2 Σ Σ1 Σ2 s s1 s2
      m x T T1 e1 e2 T2 roots1 roots2 v1 v2,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ e1 T1 Σ1 R1 roots1 ->
    ty_compatible_b Ω T1 T = true ->
    root_env_lookup x R1 = None ->
    typed_env_roots env Ω n (root_env_add x roots1 R1)
      (sctx_add x T m Σ1) e2 T2 Σ2 R2 roots2 ->
    sctx_check_ok env x T Σ2 = true ->
    roots_exclude x roots2 ->
    root_env_excludes x (root_env_remove x R2) ->
    provenance_ready_expr e1 ->
    provenance_ready_expr e2 ->
    eval env s e1 s1 v1 ->
    eval env (store_add x T v1 s1) e2 s2 v2 ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T1 Σ1 ->
     eval env s e1 s1 v1 ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 v1 T1 /\
     store_ref_targets_preserved env s s1) ->
    (store_typed env (store_add x T v1 s1) (sctx_add x T m Σ1) ->
     typed_env_structural env Ω n (sctx_add x T m Σ1) e2 T2 Σ2 ->
     eval env (store_add x T v1 s1) e2 s2 v2 ->
     store_typed env s2 Σ2 /\
     value_has_type env s2 v2 T2 /\
     store_ref_targets_preserved env (store_add x T v1 s1) s2) ->
    store_typed env (store_remove x s2) (sctx_remove x Σ2) /\
    value_has_type env (store_remove x s2) v2 T2 /\
    store_ref_targets_preserved env s (store_remove x s2).
Proof.
  intros env Ω n R R1 R2 Σ Σ1 Σ2 s s1 s2 m x T T1 e1 e2 T2
    roots1 roots2 v1 v2 Hstore Hroots Hnodup Hrn Htyped1 Hcompat
    Hfresh_root Htyped2 _ Hexclude_roots Hexclude_env Hready1 Hready2
    Heval1 Heval2 Hpres1 Hpres2.
  destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1 v1 Heval1
              Ω n R Σ T1 Σ1 R1 roots1 Hready1 Hroots Hnodup Hrn Htyped1)
    as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]].
  assert (Hfresh_store : store_lookup x s1 = None)
    by (eapply store_roots_within_lookup_none; eassumption).
  assert (Hadd_pres :
    store_ref_targets_preserved env s1 (store_add x T v1 s1))
    by (apply store_add_fresh_ref_targets_preserved; exact Hfresh_store).
  assert (Hadd_roots :
    store_roots_within (root_env_add x roots1 R1)
      (store_add x T v1 s1))
    by (eapply store_add_roots_within; eassumption).
  assert (Hadd_nodup : store_no_shadow (store_add x T v1 s1))
    by (apply store_no_shadow_add; assumption).
  assert (Hadd_rn : root_env_no_shadow (root_env_add x roots1 R1))
    by (apply root_env_no_shadow_add; assumption).
  destruct (proj1 eval_preserves_roots_ready_mutual env
              (store_add x T v1 s1) e2 s2 v2 Heval2
              Ω n (root_env_add x roots1 R1) (sctx_add x T m Σ1)
              T2 Σ2 R2 roots2 Hready2 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
    as [Hroots2_runtime [Hv2_roots [Hnodup2 _]]].
  assert (Hremove_names :
    forall se, In se (store_remove x s2) -> se_name se <> x)
    by (apply store_no_shadow_remove_no_name; exact Hnodup2).
  assert (Hroots_removed :
    store_roots_within (root_env_remove x R2) (store_remove x s2))
    by (eapply store_remove_roots_within; eassumption).
  assert (Hexclude_v : value_refs_exclude_root x v2)
    by (eapply value_roots_exclude_root; eassumption).
  assert (Hexclude_store : store_refs_exclude_root x (store_remove x s2))
    by (eapply store_roots_exclude_root; eassumption).
  eapply eval_let_preserves_typing.
  - exact Hstore.
  - eapply typed_env_roots_structural. exact Htyped1.
  - exact Heval1.
  - exact Hpres1.
  - exact Hcompat.
  - exact Hadd_pres.
  - eapply typed_env_roots_structural. exact Htyped2.
  - exact Heval2.
  - exact Hpres2.
  - exact Hfresh_store.
  - exact Hexclude_v.
  - exact Hexclude_store.
Qed.

Lemma usage_sub_left_max :
  forall u1 u2,
    usage_sub u1 (usage_max u1 u2).
Proof.
  destruct u1, u2; simpl; constructor.
Qed.

Lemma usage_sub_right_max :
  forall u1 u2,
    usage_sub u2 (usage_max u1 u2).
Proof.
  destruct u1, u2; simpl; constructor.
Qed.

Lemma value_has_type_if_left_result :
  forall env s v T2 T3,
    value_has_type env s v T2 ->
    value_has_type env s v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env s v [u2 c2] [u3 c3] Hv.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + apply usage_sub_left_max.
    + reflexivity.
Qed.

Lemma value_has_type_if_right_result :
  forall env s v T2 T3,
    value_has_type env s v T3 ->
    ty_core T2 = ty_core T3 ->
    value_has_type env s v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env s v [u2 c2] [u3 c3] Hv Hcore.
  simpl in Hcore. subst c3.
  eapply value_has_type_compatible with (Ω := []).
  - exact Hv.
  - apply TC_Core.
    + apply usage_sub_right_max.
    + reflexivity.
Qed.

Lemma eval_if_true_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat)
      Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 (e1 e2 e3 : expr) T_cond T2 T3 v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
    eval env s e1 s1 (VBool true) ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
     eval env s e1 s1 (VBool true) ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 (VBool true) T_cond) ->
    typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
    eval env s1 e2 s2 v ->
    (store_typed env s1 Σ1 ->
     typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
     eval env s1 e2 s2 v ->
     store_typed env s2 Σ2 /\ value_has_type env s2 v T2) ->
    ty_core T2 = ty_core T3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s2 Σ4 /\
    value_has_type env s2 v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env Ω n Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 e1 e2 e3 T_cond T2 T3 v
    Hstore Htyped_cond Heval_cond Hpres_cond Htyped_then Heval_then
    Hpres_then _ Hmerge.
  destruct (Hpres_cond Hstore Htyped_cond Heval_cond) as [Hstore1 _].
  destruct (Hpres_then Hstore1 Htyped_then Heval_then) as [Hstore2 Hv].
  split.
  - eapply store_typed_ctx_merge_left; eassumption.
  - eapply value_has_type_if_left_result. exact Hv.
Qed.

Lemma eval_if_false_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat)
      Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 (e1 e2 e3 : expr) T_cond T2 T3 v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
    eval env s e1 s1 (VBool false) ->
    (store_typed env s Σ ->
     typed_env_structural env Ω n Σ e1 T_cond Σ1 ->
     eval env s e1 s1 (VBool false) ->
     store_typed env s1 Σ1 /\
     value_has_type env s1 (VBool false) T_cond) ->
    typed_env_structural env Ω n Σ1 e2 T2 Σ2 ->
    typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
    eval env s1 e3 s2 v ->
    (store_typed env s1 Σ1 ->
     typed_env_structural env Ω n Σ1 e3 T3 Σ3 ->
     eval env s1 e3 s2 v ->
     store_typed env s2 Σ3 /\ value_has_type env s2 v T3) ->
    ty_core T2 = ty_core T3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s2 Σ4 /\
    value_has_type env s2 v
      (MkTy (usage_max (ty_usage T2) (ty_usage T3)) (ty_core T2)).
Proof.
  intros env Ω n Σ Σ1 Σ2 Σ3 Σ4 s s1 s2 e1 e2 e3 T_cond T2 T3 v
    Hstore Htyped_cond Heval_cond Hpres_cond Htyped_then Htyped_else Heval_else
    Hpres_else Hcore Hmerge.
  destruct (Hpres_cond Hstore Htyped_cond Heval_cond) as [Hstore1 _].
  destruct (Hpres_else Hstore1 Htyped_else Heval_else) as [Hstore3 Hv].
  assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3).
  { eapply typed_env_structural_branch_type_eq.
    - exact Htyped_then.
    - exact Htyped_else. }
  split.
  - eapply store_typed_ctx_merge_right; eassumption.
  - eapply value_has_type_if_right_result; eassumption.
Qed.

Lemma eval_borrow_shared_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_unique_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target Hstore _ _ _ _ Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_unique_indirect_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = None ->
    place_under_unique_ref_structural env Σ p ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _ _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_shared_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x path se v_target,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    eval_place s p x path ->
    store_lookup x s = Some se ->
    type_lookup_path env (se_ty se) path = Some T ->
    value_lookup_path (se_val se) path = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x path)
      (MkTy UUnrestricted (TRef (LVar n) RShared T)).
Proof.
  intros env Ω n Σ s p T x path se v_target Hstore _ _
    Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma eval_borrow_unique_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ s p T x_static path_static
      x_eval path_eval se v_target,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T ->
    place_path p = Some (x_static, path_static) ->
    sctx_lookup_mut x_static Σ = Some MMutable ->
    eval_place s p x_eval path_eval ->
    store_lookup x_eval s = Some se ->
    type_lookup_path env (se_ty se) path_eval = Some T ->
    value_lookup_path (se_val se) path_eval = Some v_target ->
    store_typed_prefix env s Σ /\
    value_has_type env s (VRef x_eval path_eval)
      (MkTy UAffine (TRef (LVar n) RUnique T)).
Proof.
  intros env Ω n Σ s p T x_static path_static x_eval path_eval
    se v_target Hstore _ _ _ _ Hlookup Htype Hvalue.
  split; [exact Hstore | econstructor; eassumption].
Qed.

Lemma store_typed_prefix_update_path_typed :
  forall env s Σ x path v_new T_path s',
    store_typed_prefix env s Σ ->
    store_ref_targets_preserved env s s' ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path = Some T_path) ->
    value_has_type env s v_new T_path ->
    store_update_path x path v_new s = Some s' ->
    store_typed_prefix env s' Σ.
Proof.
  intros env s Σ x path v_new T_path s' Hstore Hpres Htarget Hvnew Hupdate.
  destruct Htarget as [T_root [st [HΣ Htype_path]]].
  eapply store_typed_prefix_update_path.
  - exact Hstore.
  - exact Hpres.
  - intros se T st0 Hlookup HΣ0 v_root Hvalue_update.
    rewrite HΣ in HΣ0.
    inversion HΣ0; subst T st0.
    destruct (store_typed_prefix_lookup_sctx env s Σ x T_root st Hstore HΣ)
      as [se' [Hlookup' [_ [HTse [_ Hvroot]]]]].
    rewrite Hlookup in Hlookup'.
    inversion Hlookup'; subst se'.
    eapply (value_update_path_has_type env s (se_val se) T_root
              path v_new T_path v_root).
    + exact Hvroot.
    + exact Htype_path.
    + exact Hvnew.
    + exact Hvalue_update.
  - exact Hupdate.
Qed.

Lemma eval_assign_path_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 p
      T_old T_new x_static path_static x_eval path_eval v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    eval_place s p x_eval path_eval ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_typed env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 p T_old T_new
    x_static path_static x_eval path_eval v_new Hstore Hplace Hpath_static
    Hstore1 Hvnew _ Hcompat Htarget Heval_place Hpres_update Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  split.
  - eapply store_typed_update_path_typed.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Htarget.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_assign_var_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 x
      old_e T_old T_new v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_typed env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 x old_e T_old T_new v_new
    Hstore _ Hstore1 Hvnew _ Hcompat Htarget _
    Hpres_update Hupdate.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st Hlookup1].
  split.
  - eapply store_typed_update_val.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Hlookup1.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_var_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 x
      old_e T_old T_new v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    sctx_path_available Σ1 x [] = infer_ok tt ->
    sctx_restore_path Σ1 x [] = infer_ok Σ2 ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_restore_path x [] s2 = Some s3 ->
    store_typed env s3 Σ2 /\
    value_has_type env s3 (se_val old_e) T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 x old_e T_old T_new v_new
    Hstore Hplace Hstore1 Hvnew Hpres_new_store Hcompat Htarget Havailable Hrestore
    Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (typed_place_direct_lookup env Σ (PVar x) T_old x [] Hplace eq_refl)
    as [T_root [st [Hlookup0 [_ Htype_old]]]].
  simpl in Htype_old. inversion Htype_old; subst T_root.
  destruct (store_typed_lookup env s Σ x old_e Hstore Hlookup_old)
    as [Tse [stse [m [HΣ [Hname [HT [Href Hold]]]]]]].
  rewrite Hlookup0 in HΣ.
  inversion HΣ; subst Tse stse.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st_target HΣ_target].
  destruct (sctx_path_available_success Σ1 x [] Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  rewrite HΣ_target in HΣ_av.
  inversion HΣ_av; subst T_av st_av.
  assert (Hstore2 : store_typed env s2 Σ1).
  { eapply store_typed_update_val.
    - exact Hstore1.
    - exact Hpres_update.
    - exact HΣ_target.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  split.
  - eapply store_typed_restore_available_path.
    + exact Hstore2.
    + exact HΣ_target.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_replace_path_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 p
      T_old T_new x_static path_static x_eval path_eval old_v v_new,
    store_typed env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    sctx_path_available Σ1 x_static path_static = infer_ok tt ->
    sctx_restore_path Σ1 x_static path_static = infer_ok Σ2 ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_restore_path x_eval path_eval s2 = Some s3 ->
    store_typed env s3 Σ2 /\
    value_has_type env s3 old_v T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 p T_old T_new
    x_static path_static x_eval path_eval old_v v_new Hstore Hplace
    Hpath_static Hstore1 Hvnew Hpres_new_store Hcompat Htarget
    Havailable Hrestore Heval_place Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T_old x_static path_static
              Hplace Hpath_static)
    as [T_root0 [st0 [HΣ0 [_ Htype_old]]]].
  destruct (store_typed_lookup_path env s Σ x_static path_static old_v
              Hstore Hlookup_old)
    as [se [T_root [st [m [HΣ [Hname [HTy [Hstore_lookup Hvalue_lookup]]]]]]]].
  rewrite HΣ0 in HΣ.
  inversion HΣ; subst T_root st.
  destruct (store_typed_lookup env s Σ x_static se Hstore Hstore_lookup)
    as [Tse [stse [mse [HΣlookup [_ [HTse [_ Hvroot]]]]]]].
  rewrite HΣ0 in HΣlookup.
  inversion HΣlookup; subst Tse stse.
  assert (Hold : value_has_type env s old_v T_old).
  { eapply value_lookup_path_has_type.
    - exact Hvroot.
    - exact Hvalue_lookup.
    - match goal with
      | Hty : se_ty se = T_root0 |- _ =>
          rewrite Hty; exact Htype_old
      | Hty : T_root0 = se_ty se |- _ =>
          rewrite <- Hty; exact Htype_old
      end.
  }
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  assert (Hstore2 : store_typed env s2 Σ1).
  { eapply store_typed_update_path_typed.
    - exact Hstore1.
    - exact Hpres_update.
    - exact Htarget.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  destruct (sctx_path_available_success Σ1 x_static path_static Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  split.
  - eapply store_typed_restore_available_path.
    + exact Hstore2.
    + exact HΣ_av.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_var_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 x
      old_e T_old T_new v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_typed_prefix env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 x old_e T_old T_new v_new
    _ _ Hstore1 Hvnew _ Hcompat Htarget _ Hpres_update Hupdate.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st Hlookup1].
  split.
  - eapply store_typed_prefix_update_val.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Hlookup1.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_var_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 x
      old_e T_old T_new v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ (PVar x) T_old ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists st, sctx_lookup x Σ1 = Some (T_old, st)) ->
    sctx_path_available Σ1 x [] = infer_ok tt ->
    sctx_restore_path Σ1 x [] = infer_ok Σ2 ->
    store_lookup x s = Some old_e ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_val x v_new s1 = Some s2 ->
    store_restore_path x [] s2 = Some s3 ->
    store_typed_prefix env s3 Σ2 /\
    value_has_type env s3 (se_val old_e) T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 x old_e T_old T_new v_new
    Hstore Hplace Hstore1 Hvnew Hpres_new_store Hcompat Htarget Havailable Hrestore
    Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (typed_place_direct_lookup env Σ (PVar x) T_old x [] Hplace eq_refl)
    as [T_root [st [Hlookup0 [_ Htype_old]]]].
  simpl in Htype_old. inversion Htype_old; subst T_root.
  destruct (store_typed_prefix_lookup_sctx env s Σ x T_old st Hstore Hlookup0)
    as [se [Hlookup_se [_ [HT [_ Hold]]]]].
  rewrite Hlookup_old in Hlookup_se.
  inversion Hlookup_se; subst se.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  destruct Htarget as [st_target HΣ_target].
  destruct (sctx_path_available_success Σ1 x [] Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  rewrite HΣ_target in HΣ_av.
  inversion HΣ_av; subst T_av st_av.
  assert (Hstore2 : store_typed_prefix env s2 Σ1).
  { eapply store_typed_prefix_update_val.
    - exact Hstore1.
    - exact Hpres_update.
    - exact HΣ_target.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  split.
  - eapply store_typed_prefix_restore_available_path.
    + exact Hstore2.
    + exact HΣ_target.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_path_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 s s1 s2 p
      T_old T_new x_static path_static x_eval path_eval v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    eval_place s p x_eval path_eval ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_typed_prefix env s2 Σ1 /\
    value_has_type env s2 VUnit (MkTy UUnrestricted TUnits).
Proof.
  intros env Ω n Σ Σ1 s s1 s2 p T_old T_new
    x_static path_static x_eval path_eval v_new _ _ Hpath_static
    Hstore1 Hvnew _ Hcompat Htarget Heval_place Hpres_update Hupdate.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  split.
  - eapply store_typed_prefix_update_path_typed.
    + exact Hstore1.
    + exact Hpres_update.
    + exact Htarget.
    + eapply value_has_type_compatible; eassumption.
    + exact Hupdate.
  - constructor.
Qed.

Lemma eval_replace_path_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ1 Σ2 s s1 s2 s3 p
      T_old T_new x_static path_static x_eval path_eval old_v v_new,
    store_typed_prefix env s Σ ->
    typed_place_env_structural env Σ p T_old ->
    place_path p = Some (x_static, path_static) ->
    store_typed_prefix env s1 Σ1 ->
    value_has_type env s1 v_new T_new ->
    store_ref_targets_preserved env s s1 ->
    ty_compatible_b Ω T_new T_old = true ->
    (exists T_root st,
      sctx_lookup x_static Σ1 = Some (T_root, st) /\
      type_lookup_path env T_root path_static = Some T_old) ->
    sctx_path_available Σ1 x_static path_static = infer_ok tt ->
    sctx_restore_path Σ1 x_static path_static = infer_ok Σ2 ->
    eval_place s p x_eval path_eval ->
    store_lookup_path x_eval path_eval s = Some old_v ->
    store_ref_targets_preserved env s1 s2 ->
    store_update_path x_eval path_eval v_new s1 = Some s2 ->
    store_restore_path x_eval path_eval s2 = Some s3 ->
    store_typed_prefix env s3 Σ2 /\
    value_has_type env s3 old_v T_old.
Proof.
  intros env Ω n Σ Σ1 Σ2 s s1 s2 s3 p T_old T_new
    x_static path_static x_eval path_eval old_v v_new Hstore Hplace
    Hpath_static Hstore1 Hvnew Hpres_new_store Hcompat Htarget
    Havailable Hrestore Heval_place Hlookup_old Hpres_update Hupdate Hstore_restore.
  destruct (eval_place_matches_place_path s p x_eval path_eval
              x_static path_static Heval_place Hpath_static) as [Hx Hpath].
  subst x_eval path_eval.
  destruct (typed_place_direct_lookup env Σ p T_old x_static path_static
              Hplace Hpath_static)
    as [T_root0 [st0 [HΣ0 [_ Htype_old]]]].
  unfold store_lookup_path in Hlookup_old.
  destruct (store_lookup x_static s) as [se |] eqn:Hstore_lookup; try discriminate.
  destruct (store_typed_prefix_lookup_sctx
              env s Σ x_static T_root0 st0 Hstore HΣ0)
    as [se' [Hstore_lookup' [_ [HTse [_ Hvroot]]]]].
  rewrite Hstore_lookup in Hstore_lookup'.
  inversion Hstore_lookup'; subst se'.
  assert (Hold : value_has_type env s old_v T_old).
  { eapply value_lookup_path_has_type.
    - exact Hvroot.
    - exact Hlookup_old.
    - exact Htype_old.
  }
  pose proof (ty_compatible_b_sound Ω T_new T_old Hcompat) as Hcompat_prop.
  assert (Hstore2 : store_typed_prefix env s2 Σ1).
  { eapply store_typed_prefix_update_path_typed.
    - exact Hstore1.
    - exact Hpres_update.
    - exact Htarget.
    - eapply value_has_type_compatible; eassumption.
    - exact Hupdate.
  }
  destruct (sctx_path_available_success Σ1 x_static path_static Havailable)
    as [T_av [st_av [HΣ_av Hst_av]]].
  split.
  - eapply store_typed_prefix_restore_available_path.
    + exact Hstore2.
    + exact HΣ_av.
    + exact Hst_av.
    + exact Hstore_restore.
    + exact Hrestore.
  - eapply value_has_type_store_preserved.
    + exact Hold.
    + eapply store_ref_targets_preserved_trans.
      * exact Hpres_new_store.
      * eapply store_ref_targets_preserved_trans.
        -- exact Hpres_update.
        -- unfold store_restore_path in Hstore_restore.
           eapply store_update_state_ref_targets_preserved.
           exact Hstore_restore.
Qed.

Lemma eval_assign_direct_case_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p e_new x path,
    store_typed env s Σ ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ (EAssign p e_new)
      (MkTy UUnrestricted TUnits) Σ' ->
    eval env s (EAssign p e_new) s' VUnit ->
    (forall T_new Σ1 s1 v_new,
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      eval env s e_new s1 v_new ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v_new T_new /\
      store_ref_targets_preserved env s s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' VUnit (MkTy UUnrestricted TUnits) /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' p e_new x path
    Hstore Hpath Htyped Heval Hpres.
  inversion Htyped; subst; try discriminate.
  - inversion Heval; subst; try discriminate.
    + simpl in Hpath. inversion Hpath; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      destruct (typed_env_structural_preserves_var_target
                  env Ω n Σ Σ' e_new T_new x0 T_old H1 H5)
        as [st Htarget].
      destruct (Hpres T_new Σ' s1 v_new H5 H10)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s').
      { eapply store_update_val_ref_targets_preserved.
        - exact Hstore1.
        - exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H7.
        - exact H12. }
      destruct (eval_assign_var_preserves_typing env Ω n Σ Σ' s s1 s'
                  x0 old_e T_old T_new v_new Hstore H1
                  Hstore1 Hvnew Hpres_new
                  H7 (ex_intro _ st Htarget) H6 Hpres_update H12)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans; eassumption.
    + destruct (typed_env_structural_preserves_direct_path_target
                  env Ω n Σ Σ' e_new T_new p T_old x0 path0
                  H1 H3 H5) as [T_root [st Htarget]].
      destruct (eval_place_matches_place_path s p x1 path1 x0 path0 H6 H3)
        as [Hx_eval Hpath_eval].
      subst x1 path1.
      destruct (Hpres T_new Σ' s1 v_new H5 H10)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s').
      { eapply store_update_path_ref_targets_preserved.
        - exact Hstore1.
        - exists T_root, st. exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H7.
        - exact H12. }
      destruct (eval_assign_path_preserves_typing env Ω n Σ Σ' s s1 s'
                  p T_old T_new x0 path0 x0 path0 v_new
                  Hstore H1 H3 Hstore1 Hvnew Hpres_new
                  H7 (ex_intro _ T_root (ex_intro _ st Htarget))
                  H6 Hpres_update H12)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans; eassumption.
  - match goal with
    | Hnone : place_path p = None |- _ =>
        rewrite Hpath in Hnone; discriminate
    end.
Qed.

Lemma eval_replace_direct_case_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s' p e_new T_old x path v,
    store_typed env s Σ ->
    place_path p = Some (x, path) ->
    typed_env_structural env Ω n Σ (EReplace p e_new) T_old Σ' ->
    eval env s (EReplace p e_new) s' v ->
    (forall T_new Σ1 s1 v_new,
      typed_env_structural env Ω n Σ e_new T_new Σ1 ->
      eval env s e_new s1 v_new ->
      store_typed env s1 Σ1 /\
      value_has_type env s1 v_new T_new /\
      store_ref_targets_preserved env s s1) ->
    store_typed env s' Σ' /\
    value_has_type env s' v T_old /\
    store_ref_targets_preserved env s s'.
Proof.
  intros env Ω n Σ Σ' s s' p e_new T_old x path v
    Hstore Hpath Htyped Heval Hpres.
  inversion Htyped; subst; try discriminate.
  - inversion Heval; subst; try discriminate.
    + simpl in Hpath. inversion Hpath; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      destruct (typed_env_structural_preserves_var_target
                  env Ω n Σ Σ1 e_new T_new x0 T_old H1 H4)
        as [st Htarget].
      destruct (Hpres T_new Σ1 s1 v_new H4 H8)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s2).
      { eapply store_update_val_ref_targets_preserved.
        - exact Hstore1.
        - exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H5.
        - exact H11. }
      assert (Hpres_restore : store_ref_targets_preserved env s2 s').
      { unfold store_restore_path in H14.
        eapply store_update_state_ref_targets_preserved.
        exact H14. }
      destruct (eval_replace_var_preserves_typing env Ω n Σ Σ1 Σ' s s1 s2 s'
                  x0 old_e T_old T_new v_new Hstore H1
                  Hstore1 Hvnew Hpres_new
                  H5 (ex_intro _ st Htarget) H7 H10 H6 Hpres_update H11 H14)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_new.
      * eapply store_ref_targets_preserved_trans; eassumption.
    + destruct (typed_env_structural_preserves_direct_path_target
                  env Ω n Σ Σ1 e_new T_new p T_old x0 path0
                  H1 H2 H4) as [T_root [st Htarget]].
      destruct (eval_place_matches_place_path s p x1 path1 x0 path0 H6 H2)
        as [Hx_eval Hpath_eval].
      subst x1 path1.
      destruct (Hpres T_new Σ1 s1 v_new H4 H9)
        as [Hstore1 [Hvnew Hpres_new]].
      assert (Hpres_update : store_ref_targets_preserved env s1 s2).
      { eapply store_update_path_ref_targets_preserved.
        - exact Hstore1.
        - exists T_root, st. exact Htarget.
        - eapply value_has_type_compatible.
          + exact Hvnew.
          + apply ty_compatible_b_sound with (Ω := Ω). exact H5.
        - exact H12. }
      assert (Hpres_restore : store_ref_targets_preserved env s2 s').
      { unfold store_restore_path in H15.
        eapply store_update_state_ref_targets_preserved.
        exact H15. }
      destruct (eval_replace_path_preserves_typing env Ω n Σ Σ1 Σ' s s1 s2 s'
                  p T_old T_new x0 path0 x0 path0 v v_new
                  Hstore H1 H2 Hstore1 Hvnew Hpres_new
                  H5 (ex_intro _ T_root (ex_intro _ st Htarget))
                  H7 H10 H6 H8 Hpres_update H12 H15)
        as [Hstore_final Hv_final].
      repeat split; try assumption.
      eapply store_ref_targets_preserved_trans.
      * exact Hpres_new.
      * eapply store_ref_targets_preserved_trans; eassumption.
  - match goal with
    | Hnone : place_path p = None |- _ =>
        rewrite Hpath in Hnone; discriminate
    end.
Qed.

Lemma eval_letinfer_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ' s s'
      m x e1 e2 T v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ (ELetInfer m x e1 e2) T Σ' ->
    eval env s (ELetInfer m x e1 e2) s' v ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
Proof.
  intros env Ω n Σ Σ' s s' m x e1 e2 T v _ _ Heval.
  inversion Heval.
Qed.

Theorem eval_preserves_typing_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction; eassumption.
    + assert (Hmove_pair :
        store_typed env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
    IHfields Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : preservation_ready_fields ?fields0,
      Htyped_fields : typed_fields_env_structural env Ω n lts args
        Σ ?fields0 (struct_fields sdef) Σ' |- _ =>
        destruct (IHfields Ω n lts args Σ Σ'
                    Hready_fields Hstore Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready.
  - intros s s' e v Heval IH Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e Σ' |- _ =>
        destruct (IH Ω n Σ T_e Σ' Hready_e Hstore Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s p x path rk Heval_place Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore0 Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore0 Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s fname Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_then : preservation_ready_expr e2,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHthen Ω n Σ1 T2 Σ2
                    Hready_then Hstore1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_else : preservation_ready_expr e3,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Htyped_else : typed_env_structural env Ω n ?Σ1 e3 ?T3 ?Σ3,
      Hcore : ty_core ?T2 = ty_core ?T3,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHelse Ω n Σ1 T3 Σ3
                    Hready_else Hstore1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq; eassumption);
        split;
        [ eapply store_typed_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
      Heval_args IHargs Hrename Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s Ω n Σ ps Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n Σ ps Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Hready_rest : preservation_ready_args es,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_env_structural env Ω n ?Σ1 es ?ps_rest Σ' |- _ =>
        destruct (IHe Ω n Σ T_e Σ1 Hready_e Hstore Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (IHrest Ω n Σ1 ps_rest Σ' Hready_rest Hstore1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args Σ Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args Σ Σ' Hready Hstore Htyped.
    pose proof (preservation_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Hready; subst.
    simpl in Hlookup_expr; try discriminate.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_structural env Ω n Σ ?e_field ?T_field ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_env_structural env Ω n lts args
        ?Σ1 ?fields0 rest Σ' |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst;
        destruct (IHfield Ω n Σ T_field Σ1 Hready_field Hstore Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (IHrest Ω n lts args Σ1 Σ' Hready Hstore1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 Σ0 T0 Σ0'
      Hready Hstore Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 Σ0 ps0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 Σ0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

Theorem eval_preserves_typing_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed_prefix env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed_prefix env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed_prefix env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
        preservation_ready_expr e ->
        store_typed_prefix env s Σ ->
        typed_env_structural env Ω n Σ e T Σ' ->
        store_typed_prefix env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
        preservation_ready_args args ->
        store_typed_prefix env s Σ ->
        typed_args_env_structural env Ω n Σ args ps Σ' ->
        store_typed_prefix env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
        preservation_ready_fields fields ->
        store_typed_prefix env s Σ ->
        typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
        store_typed_prefix env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing_prefix env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction_prefix; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction_prefix; eassumption.
    + destruct (eval_var_move_preserves_typing_prefix env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing_prefix
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction_prefix; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction_prefix; eassumption.
    + assert (Hmove_pair :
        store_typed_prefix env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing_prefix; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
    IHfields Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : preservation_ready_fields ?fields0,
      Htyped_fields : typed_fields_env_structural env Ω n lts args
        Σ ?fields0 (struct_fields sdef) Σ' |- _ =>
        destruct (IHfields Ω n lts args Σ Σ'
                    Hready_fields Hstore Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready.
  - intros s s' e v Heval IH Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e Σ' |- _ =>
        destruct (IH Ω n Σ T_e Σ' Hready_e Hstore Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace Htyped_new)
            as [st Htarget];
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new ?Σ1,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ1 Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing_prefix
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : preservation_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_structural env Ω n Σ e_new ?T_new Σ',
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static Htyped_new) as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n Σ T_new Σ' Hready_new Hstore Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved_prefix;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing_prefix
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s p x path rk Heval_place Ω n Σ T Σ' Hready Hstore Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore0 Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hstore0 : store_typed_prefix env s ?Σ0,
        Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore0 Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore0 Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hsome : place_path p = Some _, Hnone : place_path p = None |- _ =>
          rewrite Hsome in Hnone; discriminate
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s fname Ω n Σ T Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_then : preservation_ready_expr e2,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHthen Ω n Σ1 T2 Σ2
                    Hready_then Hstore1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_prefix_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n Σ T Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : preservation_ready_expr e1,
      Hready_else : preservation_ready_expr e3,
      Htyped_cond : typed_env_structural env Ω n Σ e1 ?T_cond ?Σ1,
      Htyped_then : typed_env_structural env Ω n ?Σ1 e2 ?T2 ?Σ2,
      Htyped_else : typed_env_structural env Ω n ?Σ1 e3 ?T3 ?Σ3,
      Hcore : ty_core ?T2 = ty_core ?T3,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n Σ T_cond Σ1
                    Hready_cond Hstore Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (IHelse Ω n Σ1 T3 Σ3
                    Hready_else Hstore1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq; eassumption);
        split;
        [ eapply store_typed_prefix_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
      Heval_args IHargs Hrename Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n Σ T Σ' Hready _ _.
    inversion Hready.
  - intros s Ω n Σ ps Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n Σ ps Σ' Hready Hstore Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : preservation_ready_expr e,
      Hready_rest : preservation_ready_args es,
      Htyped_e : typed_env_structural env Ω n Σ e ?T_e ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_env_structural env Ω n ?Σ1 es ?ps_rest Σ' |- _ =>
        destruct (IHe Ω n Σ T_e Σ1 Hready_e Hstore Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (IHrest Ω n Σ1 ps_rest Σ' Hready_rest Hstore1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args Σ Σ' _ Hstore Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args Σ Σ' Hready Hstore Htyped.
    pose proof (preservation_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Hready; subst.
    simpl in Hlookup_expr; try discriminate.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_structural env Ω n Σ ?e_field ?T_field ?Σ1,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_env_structural env Ω n lts args
        ?Σ1 ?fields0 rest Σ' |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst;
        destruct (IHfield Ω n Σ T_field Σ1 Hready_field Hstore Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (IHrest Ω n lts args Σ1 Σ' Hready Hstore1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 Σ0 T0 Σ0'
      Hready Hstore Htyped.
    destruct (Hmut env0) as [Hexpr [_ _]].
    eapply Hexpr; eassumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 Σ0 ps0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [Hargs _]].
      eapply Hargs; eassumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 Σ0 Σ0'
        Hready Hstore Htyped.
      destruct (Hmut env0) as [_ [_ Hfields]].
      eapply Hfields; eassumption.
Qed.

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

Theorem eval_preserves_roots_ready_prefix_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      preservation_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      preservation_ready_args args ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      preservation_ready_fields fields ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R' /\
      store_ref_targets_preserved env s s').
Proof.
  split.
  - intros env s e s' v Heval Ω n R Σ T Σ' R' roots
      Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 eval_preserves_typing_ready_prefix_mutual
                env s e s' v Heval Ω n Σ T Σ' Hpres_ready Hstore
                (typed_env_roots_structural env Ω n R Σ e T Σ' R' roots
                  Htyped))
      as [Hstore' [_ Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env s args s' vs Heval Ω n R Σ ps Σ' R' roots
        Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 eval_preserves_typing_ready_prefix_mutual)
                  env s args s' vs Heval Ω n Σ ps Σ' Hpres_ready Hstore
                  (typed_args_roots_structural env Ω n R Σ args ps Σ' R'
                    roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
                  env s args s' vs Heval Ω n R Σ ps Σ' R' roots
                  Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
        roots Hprov Hpres_ready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj2 (proj2 eval_preserves_typing_ready_prefix_mutual)
                  env s fields defs s' values Heval Ω n lts args Σ Σ'
                  Hpres_ready Hstore
                  (typed_fields_roots_structural env Ω n lts args R Σ
                    fields defs Σ' R' roots Htyped))
        as [Hstore' [_ Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual)
                  env s fields defs s' values Heval Ω n lts args R Σ Σ' R'
                  roots Hprov Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used' T_body Γ_out,
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    typed_env_structural env (fn_outlives fcall) (fn_lifetimes fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env
      (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  intros env Ω n Σ Σ_args fname args fdef fcall σ s s_args s_body
    vs ret used' T_body Γ_out Hstore Hready_args Htyped_args Heval_args
    Hlookup Henv_checked Henv_ready Hrename Htyped_body Hcompat_body
    Heval_body.
  destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore Htyped_args)
    as [Hstore_args [Hargs_subst _]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hready_body : preservation_ready_expr (fn_body fcall)).
  { eapply lookup_alpha_rename_fn_def_preservation_ready_body; eassumption. }
  destruct (proj1 eval_preserves_typing_ready_prefix_mutual
              env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out)
              Hready_body Hstore_bind Htyped_body)
    as [Hstore_body [Hv_body Hpres_body]].
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  repeat split; try assumption.
  eapply value_has_type_apply_lt_ty. exact Hv_ret_fdef.
Qed.

Lemma eval_direct_call_body_preserves_typing_prefix_from_lookup :
  forall env (Ω : outlives_ctx) (n : nat) Σ Σ_args fname args
      fdef fcall σ s s_args s_body vs ret used',
    store_typed env s Σ ->
    preservation_ready_args args ->
    typed_args_env_structural env Ω n Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args ->
    eval_args env s args s_args vs ->
    lookup_fn fname (env_fns env) = Some fdef ->
    env_fns_checked_structural env ->
    env_fns_preservation_ready env ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    exists Γ_out,
      store_typed env s_args Σ_args /\
      store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
      value_has_type env s_body ret (apply_lt_ty σ (fn_ret fdef)) /\
      store_ref_targets_preserved env
        (bind_params (fn_params fcall) vs s_args) s_body.
Proof.
  intros env Ω n Σ Σ_args fname args fdef fcall σ s s_args s_body
    vs ret used' Hstore Hready_args Htyped_args Heval_args Hlookup
    Henv_checked Henv_ready Hrename Heval_body.
  pose proof (lookup_alpha_rename_fn_def_typed_structural
                env fname fdef fcall (store_names s_args) used'
                Hlookup Henv_checked Hrename) as Htyped_fn.
  destruct (typed_fn_env_structural_body env fcall Htyped_fn)
    as [T_body [Γ_out [Htyped_body [Hcompat_body _]]]].
  exists Γ_out.
  eapply eval_direct_call_body_preserves_typing_prefix; eassumption.
Qed.

Lemma eval_direct_call_body_cleanup_preserves_value_and_refs :
  forall env (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall σ s s_args s_body vs ret used'
      T_body Γ_out R_params R_body roots_body,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    provenance_ready_args args ->
    preservation_ready_args args ->
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    store_roots_within R_params
      (bind_params (fn_params fcall) vs s_args) ->
    store_no_shadow (bind_params (fn_params fcall) vs s_args) ->
    root_env_no_shadow R_params ->
    root_env_covers_params (fn_params fcall) R_params ->
    provenance_ready_expr (fn_body fcall) ->
    preservation_ready_expr (fn_body fcall) ->
    typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
      R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
      (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body ->
    ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true ->
    roots_exclude_params (fn_params fcall) roots_body ->
    root_env_excludes_params (fn_params fcall) R_body ->
    eval env (bind_params (fn_params fcall) vs s_args)
      (fn_body fcall) s_body ret ->
    store_typed env s_args Σ_args /\
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args /\
    store_typed_prefix env s_body (sctx_of_ctx Γ_out) /\
    store_roots_within R_body s_body /\
    store_no_shadow s_body /\
    root_env_no_shadow R_body /\
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef)) /\
    store_ref_targets_preserved env s
      (store_remove_params (fn_params fcall) s_body) /\
    exists frame_final locals,
      store_param_scope (fn_params fcall) s_body frame_final /\
      store_remove_params (fn_params fcall) s_body = locals ++ frame_final /\
      value_refs_exclude_params (fn_params fcall) ret /\
      store_refs_exclude_params (fn_params fcall)
        (store_remove_params (fn_params fcall) s_body).
Proof.
  intros env Ω n R Σ Σ_args R_args arg_roots fname args fdef fcall σ
    s s_args s_body vs ret used' T_body Γ_out R_params R_body roots_body
    Hstore Hroots Hshadow Hrn Hprov_args Hready_args Htyped_args Heval_args
    Hrename Hroots_bind Hshadow_bind Hrn_params Hcover_params Hprov_body
    Hready_body Htyped_body Hcompat_body Hexclude_ret Hexclude_env
    Heval_body.
  destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
              env s args s_args vs Heval_args Ω n Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args
              Hready_args Hstore
              (typed_args_roots_structural env Ω n R Σ args
                (apply_lt_params σ (fn_params fdef)) Σ_args R_args
                arg_roots Htyped_args))
    as [Hstore_args [Hargs_subst Hpres_args]].
  destruct (proj1 (proj2 eval_preserves_roots_ready_mutual)
              env s args s_args vs Heval_args Ω n R Σ
              (apply_lt_params σ (fn_params fdef)) Σ_args R_args
              arg_roots Hprov_args Hroots Hshadow Hrn Htyped_args)
    as [_ [_ [Hshadow_args _]]].
  pose proof (alpha_rename_fn_def_shape (store_names s_args)
                fdef fcall used' Hrename) as Hshape.
  destruct Hshape as [_ [Hret Hparams_alpha]].
  assert (Hargs_unsubst_fdef :
    eval_args_values_have_types env Ω s_args vs (fn_params fdef)).
  { eapply eval_args_values_have_types_apply_lt_params_inv.
    exact Hargs_subst. }
  assert (Hargs_fcall :
    eval_args_values_have_types env Ω s_args vs (fn_params fcall)).
  { eapply eval_args_values_have_types_params_alpha.
    - exact Hparams_alpha.
    - exact Hargs_unsubst_fdef. }
  assert (Hnodup :
    NoDup (ctx_names (params_ctx (fn_params fcall)))).
  { eapply alpha_rename_fn_def_params_nodup_ctx_names. exact Hrename. }
  assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args).
  { eapply alpha_rename_fn_def_params_fresh_in_store. exact Hrename. }
  assert (Hstore_bind :
    store_typed_prefix env (bind_params (fn_params fcall) vs s_args)
      (sctx_of_ctx (params_ctx (fn_params fcall)))).
  { eapply bind_params_store_typed_prefix; eassumption. }
  assert (Hframe_start :
    store_frame_scope (fn_params fcall)
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_frame_scope_bind_params. exact Hargs_fcall. }
  assert (Hframe_fresh_start :
    store_frame_static_fresh
      (sctx_of_ctx (params_ctx (fn_params fcall))) s_args).
  { eapply params_fresh_in_store_frame_static_fresh. exact Hfresh. }
  destruct (proj1 eval_preserves_frame_scope_roots_ready_mutual
              env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body
              Hcover_params Hroots_bind Hshadow_bind Hrn_params
              Hframe_start Hframe_fresh_start)
    as [_ [_ [_ [_ [Hframe_scope _]]]]].
  destruct (proj1 eval_preserves_roots_ready_prefix_mutual
              env (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              Hprov_body Hready_body Hstore_bind Hroots_bind Hshadow_bind
              Hrn_params Htyped_body)
    as [Hstore_body [Hroots_body [Hret_roots
        [Hshadow_body [Hrn_body Hpres_body]]]]].
  assert (Hv_body : value_has_type env s_body ret T_body).
  { destruct (proj1 eval_preserves_typing_ready_prefix_mutual
                env (bind_params (fn_params fcall) vs s_args)
                (fn_body fcall) s_body ret Heval_body
                (fn_outlives fcall) (fn_lifetimes fcall)
                (sctx_of_ctx (params_ctx (fn_params fcall)))
                T_body (sctx_of_ctx Γ_out)
                Hready_body Hstore_bind
                (typed_env_roots_structural env (fn_outlives fcall)
                  (fn_lifetimes fcall) R_params
                  (sctx_of_ctx (params_ctx (fn_params fcall)))
                  (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body
                  roots_body Htyped_body)) as [_ [Hv _]].
    exact Hv. }
  assert (Hv_ret_fcall : value_has_type env s_body ret (fn_ret fcall)).
  { eapply value_has_type_compatible.
    - exact Hv_body.
    - apply ty_compatible_b_sound with (Ω := fn_outlives fcall).
      exact Hcompat_body. }
  assert (Hv_ret_fdef : value_has_type env s_body ret (fn_ret fdef)).
  { rewrite Hret. exact Hv_ret_fcall. }
  destruct (eval_preserves_param_scope_roots_ready_mutual)
    as [Hscope_expr _].
  assert (Hscope_start :
    store_param_scope (fn_params fcall)
      (bind_params (fn_params fcall) vs s_args) s_args).
  { eapply store_param_scope_bind_params. exact Hargs_fcall. }
  destruct (Hscope_expr env
              (bind_params (fn_params fcall) vs s_args)
              (fn_body fcall) s_body ret Heval_body
              (fn_outlives fcall) (fn_lifetimes fcall)
              R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
              T_body (sctx_of_ctx Γ_out) R_body roots_body
              (fn_params fcall) s_args Hprov_body Htyped_body)
              as [frame_final Hscope_body].
  { exact Hcover_params. }
  { exact Hscope_start. }
  destruct (store_remove_params_cleanup_excludes
              (fn_params fcall) s_body frame_final R_body roots_body ret
              Hscope_body Hroots_body Hret_roots Hshadow_body Hnodup
              Hexclude_ret Hexclude_env)
    as [locals [Hremoved [Hret_exclude Hstore_exclude]]].
  assert (Hv_final :
    value_has_type env (store_remove_params (fn_params fcall) s_body)
      ret (apply_lt_ty σ (fn_ret fdef))).
  { apply value_has_type_apply_lt_ty.
    eapply value_has_type_store_remove_params_excluding.
    - exact Hv_ret_fdef.
    - exact Hret_exclude. }
  assert (Hpres_bind :
    store_ref_targets_preserved env s_args
      (bind_params (fn_params fcall) vs s_args)).
  { eapply bind_params_ref_targets_preserved; eassumption. }
  assert (Hpres_args_body :
    store_ref_targets_preserved env s_args s_body).
  { eapply store_ref_targets_preserved_trans; eassumption. }
  assert (Hpres_args_final :
    store_ref_targets_preserved env s_args
      (store_remove_params (fn_params fcall) s_body)).
  { eapply store_ref_targets_preserved_remove_params_after_absent;
      eassumption. }
  assert (Hsame_body :
    sctx_same_bindings
      (sctx_of_ctx (params_ctx (fn_params fcall)))
      (sctx_of_ctx Γ_out)).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural. exact Htyped_body. }
  assert (Hremoved_exact :
    store_remove_params (fn_params fcall) s_body = s_args).
  { eapply store_remove_params_store_frame_scope_exact.
    - exact Hsame_body.
    - eapply store_frame_scope_param_scope. exact Hframe_scope.
    - exact Hframe_scope. }
  assert (Hstore_final :
    store_typed env (store_remove_params (fn_params fcall) s_body) Σ_args).
  { rewrite Hremoved_exact. exact Hstore_args. }
  repeat split; try assumption.
  - eapply store_ref_targets_preserved_trans; eassumption.
  - exists frame_final, locals. repeat split; assumption.
Qed.

Definition direct_call_callee_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    exists T_body Γ_out R_params R_body roots_body,
      store_roots_within R_params
        (bind_params (fn_params fcall) vs s_args) /\
      store_no_shadow (bind_params (fn_params fcall) vs s_args) /\
      root_env_no_shadow R_params /\
      root_env_covers_params (fn_params fcall) R_params /\
      provenance_ready_expr (fn_body fcall) /\
      preservation_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        R_params (sctx_of_ctx (params_ctx (fn_params fcall)))
        (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body.

Definition direct_call_callee_body_root_evidence (env : global_env) : Prop :=
  forall (Ω : outlives_ctx) (n : nat) R Σ Σ_args R_args arg_roots
      (fname : ident) args fdef fcall (σ : list lifetime) s s_args vs
      used',
    typed_args_roots env Ω n R Σ args
      (apply_lt_params σ (fn_params fdef)) Σ_args R_args arg_roots ->
    eval_args env s args s_args vs ->
    alpha_rename_fn_def (store_names s_args) fdef = (fcall, used') ->
    exists T_body Γ_out R_body roots_body,
      provenance_ready_expr (fn_body fcall) /\
      preservation_ready_expr (fn_body fcall) /\
      typed_env_roots env (fn_outlives fcall) (fn_lifetimes fcall)
        (call_param_root_env (fn_params fcall) arg_roots R_args)
        (sctx_of_ctx (params_ctx (fn_params fcall)))
        (fn_body fcall) T_body (sctx_of_ctx Γ_out) R_body roots_body /\
      ty_compatible_b (fn_outlives fcall) T_body (fn_ret fcall) = true /\
      roots_exclude_params (fn_params fcall) roots_body /\
      root_env_excludes_params (fn_params fcall) R_body.

Theorem eval_preserves_typing_ready_with_call_invariants_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ T Σ',
      preservation_ready_expr e ->
      store_typed env s Σ ->
      typed_env_structural env Ω n Σ e T Σ' ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) Σ ps Σ',
      preservation_ready_args args ->
      store_typed env s Σ ->
      typed_args_env_structural env Ω n Σ args ps Σ' ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    env_fns_typed_structural env ->
    fn_env_unique_by_name env ->
    forall (Ω : outlives_ctx) (n : nat) lts args Σ Σ',
      preservation_ready_fields fields ->
      store_typed env s Σ ->
      typed_fields_env_structural env Ω n lts args Σ fields defs Σ' ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s').
Proof.
  split.
  - intros env s e s' v Heval _ _ Ω n Σ T Σ' Hready Hstore Htyped.
    exact (proj1 eval_preserves_typing_ready_mutual env s e s' v Heval
      Ω n Σ T Σ' Hready Hstore Htyped).
  - split.
    + intros env s args s' vs Heval _ _ Ω n Σ ps Σ' Hready Hstore Htyped.
      exact (proj1 (proj2 eval_preserves_typing_ready_mutual)
        env s args s' vs Heval Ω n Σ ps Σ' Hready Hstore Htyped).
    + intros env s fields defs s' values Heval _ _ Ω n lts args Σ Σ'
        Hready Hstore Htyped.
      exact (proj2 (proj2 eval_preserves_typing_ready_mutual)
        env s fields defs s' values Heval Ω n lts args Σ Σ'
        Hready Hstore Htyped).
Qed.

Lemma eval_let_roots_ready_preserves_typing :
  forall env (Ω : outlives_ctx) (n : nat) R R' Σ Σ' s s'
      m x T_ann e1 e2 T roots v,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ (ELet m x T_ann e1 e2) T Σ' R' roots ->
    provenance_ready_expr (ELet m x T_ann e1 e2) ->
    preservation_ready_expr e1 ->
    preservation_ready_expr e2 ->
    eval env s (ELet m x T_ann e1 e2) s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' v T /\
    store_ref_targets_preserved env s s' /\
    store_roots_within R' s' /\
    value_roots_within roots v /\
    store_no_shadow s' /\
    root_env_no_shadow R'.
Proof.
  intros env Ω n R R' Σ Σ' s s' m x T_ann e1 e2 T roots v
    Hstore Hroots Hnodup Hrn Htyped Hready Hready1_struct
    Hready2_struct Heval.
  destruct (proj1 eval_preserves_roots_ready_mutual env s
              (ELet m x T_ann e1 e2) s' v Heval
              Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped)
    as [Hroots_final [Hv_roots [Hnodup_final Hrn_final]]].
  dependent destruction Hready.
  inversion Heval; subst.
  inversion Htyped; subst.
  match goal with
  | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
      ?R1_body ?roots1_body,
    Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
    Hfresh : root_env_lookup x ?R1_body = None,
    Htyped2 : typed_env_roots env Ω n
      (root_env_add x ?roots1_body ?R1_body)
      (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
      ?R2_body ?roots2_body,
    Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
    Hexcl_roots : roots_exclude x ?roots2_body,
    Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
    Heval1 : eval env s e1 ?s1_body ?v1_body,
    Heval2 : eval env (store_add x T_ann ?v1_body ?s1_body) e2
      ?s2_body ?v2_body |- _ =>
      let Hpres1 := fresh "Hpres1" in
      let Hpres2 := fresh "Hpres2" in
      assert (Hpres1 :
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
        eval env s e1 s1_body v1_body ->
        store_typed env s1_body Σ1_body /\
        value_has_type env s1_body v1_body T1_body /\
        store_ref_targets_preserved env s s1_body);
      [ intros Hstore0 Htyped0 Heval0;
        exact (proj1 eval_preserves_typing_ready_mutual env s e1
          s1_body v1_body Heval0 Ω n Σ T1_body Σ1_body
          Hready1_struct Hstore0 Htyped0)
      | assert (Hpres2 :
          store_typed env (store_add x T_ann v1_body s1_body)
            (sctx_add x T_ann m Σ1_body) ->
          typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
            e2 T2_body Σ2_body ->
          eval env (store_add x T_ann v1_body s1_body) e2 s2_body v2_body ->
          store_typed env s2_body Σ2_body /\
          value_has_type env s2_body v2_body T2_body /\
          store_ref_targets_preserved env
            (store_add x T_ann v1_body s1_body) s2_body);
        [ intros Hstore0 Htyped0 Heval0;
          exact (proj1 eval_preserves_typing_ready_mutual env
            (store_add x T_ann v1_body s1_body) e2 s2_body v2_body
            Heval0 Ω n (sctx_add x T_ann m Σ1_body) T2_body
            Σ2_body Hready2_struct Hstore0 Htyped0)
        | destruct (eval_let_roots_preserves_typing env Ω n R R1_body
            R2_body Σ Σ1_body Σ2_body s s1_body s2_body m x T_ann
            T1_body e1 e2 T2_body roots1_body roots2_body v1_body
            v2_body Hstore Hroots Hnodup Hrn Htyped1 Hcompat Hfresh
            Htyped2 Hcheck Hexcl_roots Hexcl_env Hready1 Hready2 Heval1
            Heval2 Hpres1 Hpres2)
          as [Hstore_final [Hv_final Hpres_final]];
          repeat split; assumption ]
      ]
  end.
Qed.

Theorem eval_preserves_typing_roots_ready_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_roots_within roots v /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
      provenance_ready_args args ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed env s' Σ' /\
      eval_args_values_have_types env Ω s' vs ps /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      Forall2 value_roots_within roots vs /\
      store_no_shadow s' /\
      root_env_no_shadow R') /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
      provenance_ready_fields fields ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed env s' Σ' /\
      struct_fields_have_type env s' lts args values defs /\
      store_ref_targets_preserved env s s' /\
      store_roots_within R' s' /\
      value_fields_roots_within roots values /\
      store_no_shadow s' /\
      root_env_no_shadow R').
Proof.
  assert (Htyping : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
        provenance_ready_expr e ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_typed env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_typed env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_typed env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_typed env s' Σ' /\
        struct_fields_have_type env s' lts args values defs /\
        store_ref_targets_preserved env s s')).
  { intro env.
    apply eval_eval_args_eval_struct_fields_ind.
  - intros s Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s i Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s f Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s b Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split; try exact Hstore; try constructor.
    apply store_ref_targets_preserved_refl.
  - intros s x se Hlookup Hconsume Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + destruct (eval_var_copy_preserves_typing env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction; eassumption.
    + destruct (eval_var_move_preserves_typing env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hstore _ _ _ Htyped.
    inversion Hready; subst; try discriminate.
    inversion Htyped; subst.
    + destruct (eval_place_copy_direct_preserves_typing
                  env Ω n _ s p T x path x_eval path_eval se T_eval v
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_place_copy_static_move_direct_contradiction; eassumption.
  - intros s s' p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Hstore_consume
      Ω n R Σ T Σ' R' roots Hready Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_place_consume_static_copy_direct_contradiction; eassumption.
    + assert (Hmove_pair :
        store_typed env s' Σ' /\ value_has_type env s' v T).
      { eapply eval_place_move_direct_preserves_typing; eassumption. }
      destruct Hmove_pair as [Hstore' Hv].
      repeat split; try assumption.
      unfold store_consume_path in Hstore_consume.
      destruct (store_lookup x_eval s) as [se0 |] eqn:Hlookup0;
        try discriminate.
      destruct (binding_available_b (se_state se0) path_eval);
        try discriminate.
      eapply store_update_state_ref_targets_preserved.
      exact Hstore_consume.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IHfields Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    rewrite Hlookup in H4. inversion H4; subst sdef0.
    match goal with
    | Hready_fields : provenance_ready_fields ?fields0,
      Htyped_fields : typed_fields_roots env Ω n lts args R Σ ?fields0
        (struct_fields sdef) Σ' R' roots |- _ =>
        destruct (IHfields Ω n lts args R Σ Σ' R' roots
                    Hready_fields Hstore Hroots Hnodup Hrn Htyped_fields)
          as [Hstore' [Hfields Hpres_fields]]
    end.
    split.
    + exact Hstore'.
    + split.
      * econstructor; eassumption.
      * exact Hpres_fields.
  - intros s s1 s2 m x T_ann e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
        ?R1_body ?roots1_body,
      Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
      Hfresh : root_env_lookup x ?R1_body = None,
      Htyped2 : typed_env_roots env Ω n
        (root_env_add x ?roots1_body ?R1_body)
        (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
        ?R2_body ?roots2_body,
      Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
      Hexcl_roots : roots_exclude x ?roots2_body,
      Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
      Hready1 : provenance_ready_expr e1,
      Hready2 : provenance_ready_expr e2 |- _ =>
        let Hpres1 := fresh "Hpres1" in
        let Hpres2 := fresh "Hpres2" in
        assert (Hpres1 :
          store_typed env s Σ ->
          typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
          eval env s e1 s1 v1 ->
          store_typed env s1 Σ1_body /\
          value_has_type env s1 v1 T1_body /\
          store_ref_targets_preserved env s s1);
        [ intros Hstore0 _ Heval0;
          exact (IH1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hstore0 Hroots Hnodup Hrn Htyped1)
        | destruct (proj1 eval_preserves_roots_ready_mutual env s e1
            s1 v1 Heval1 Ω n R Σ T1_body Σ1_body R1_body roots1_body
            Hready1 Hroots Hnodup Hrn Htyped1)
          as [Hroots1_runtime [Hv1_roots [Hnodup1 Hrn1]]];
          assert (Hfresh_store : store_lookup x s1 = None)
            by (eapply store_roots_within_lookup_none; eassumption);
          assert (Hadd_roots :
            store_roots_within (root_env_add x roots1_body R1_body)
              (store_add x T_ann v1 s1))
            by (eapply store_add_roots_within; eassumption);
          assert (Hadd_nodup :
            store_no_shadow (store_add x T_ann v1 s1))
            by (apply store_no_shadow_add; assumption);
          assert (Hadd_rn :
            root_env_no_shadow (root_env_add x roots1_body R1_body))
            by (apply root_env_no_shadow_add; assumption);
          assert (Hpres2 :
            store_typed env (store_add x T_ann v1 s1)
              (sctx_add x T_ann m Σ1_body) ->
            typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
              e2 T2_body Σ2_body ->
            eval env (store_add x T_ann v1 s1) e2 s2 v2 ->
            store_typed env s2 Σ2_body /\
            value_has_type env s2 v2 T2_body /\
            store_ref_targets_preserved env
              (store_add x T_ann v1 s1) s2);
          [ intros Hstore0 _ Heval0;
            exact (IH2 Ω n (root_env_add x roots1_body R1_body)
              (sctx_add x T_ann m Σ1_body) T2_body Σ2_body R2_body
              roots2_body Hready2 Hstore0 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
          | eapply eval_let_roots_preserves_typing;
            eassumption ] ]
    end.
  - intros s s' e v Heval IH Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e Σ' R' ?roots_e |- _ =>
        destruct (IH Ω n R Σ T_e Σ' R' roots_e Hready_e
                    Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore' [_ Hpres]]
    end.
    repeat split.
    + exact Hstore'.
    + constructor.
    + exact Hpres.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Hrestore Ω n R Σ T Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 x [] = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 x [] = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ1 e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_var_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Havailable Hrestore_ctx Hlookup
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new
      IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup
      Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + simpl in x0. inversion x0; subst.
      simpl in *.
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; subst; clear H
      end.
      match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ (PVar x) ?T_old,
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_var_target
                      env Ω n Σ Σ' e_new T_new x T_old Hplace
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [st Htarget];
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_val_ref_targets_preserved;
              [ exact Hstore1
              | exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_var_preserves_typing
                      env Ω n Σ Σ' s s1 s2 x old_e T_old T_new v_new
                      Hstore Hplace Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ st Htarget) Hlookup Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s s1 s2 s3 p x_eval path_eval old_v e_new v_new
      Heval_place Hlookup_old Heval_new IHnew Hupdate Hrestore
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new ?Σ1 ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true,
        Havailable : sctx_path_available ?Σ1 ?x_static ?path_static = infer_ok tt,
        Hrestore_ctx : sctx_restore_path ?Σ1 ?x_static ?path_static = infer_ok Σ' |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ1 e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ1 R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ1 R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          assert (Hpres_restore : store_ref_targets_preserved env s2 s3)
          by (unfold store_restore_path in Hrestore;
              eapply store_update_state_ref_targets_preserved; exact Hrestore);
          destruct (eval_replace_path_preserves_typing
                      env Ω n Σ Σ1 Σ' s s1 s2 s3 p T_old T_new
                      x_static path_static x_static path_static old_v v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Havailable Hrestore_ctx Heval_place Hlookup_old
                      Hpres_update Hupdate Hrestore)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans;
          [ exact Hpres_new
          | eapply store_ref_targets_preserved_trans; eassumption ]
      end.
  - intros s s1 s2 p x_eval path_eval e_new v_new Heval_place
      Heval_new IHnew Hupdate Ω n R Σ T Σ' R' roots Hready Hstore
      Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst; try discriminate.
    + match goal with
      | Hready_new : provenance_ready_expr e_new,
        Hplace : typed_place_env_structural env Σ p ?T_old,
        Hpath_static : place_path p = Some (?x_static, ?path_static),
        Htyped_new : typed_env_roots env Ω n R Σ e_new ?T_new Σ' ?R1 ?roots_new,
        Hcompat : ty_compatible_b Ω ?T_new ?T_old = true |- _ =>
          destruct (typed_env_structural_preserves_direct_path_target
                      env Ω n Σ Σ' e_new T_new p T_old x_static path_static
                      Hplace Hpath_static
                      (typed_env_roots_structural env Ω n R Σ e_new
                        T_new Σ' R1 roots_new Htyped_new))
            as [T_root [st Htarget]];
          destruct (eval_place_matches_place_path s p x_eval path_eval
                      x_static path_static Heval_place Hpath_static)
            as [Hx_eval Hpath_eval];
          subst x_eval path_eval;
          destruct (IHnew Ω n R Σ T_new Σ' R1 roots_new Hready_new
                      Hstore Hroots Hnodup Hrn Htyped_new)
            as [Hstore1 [Hvnew Hpres_new]];
          assert (Hpres_update : store_ref_targets_preserved env s1 s2)
          by (eapply store_update_path_ref_targets_preserved;
              [ exact Hstore1
              | exists T_root, st; exact Htarget
              | eapply value_has_type_compatible;
                [ exact Hvnew
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hupdate ]);
          destruct (eval_assign_path_preserves_typing
                      env Ω n Σ Σ' s s1 s2 p T_old T_new
                      x_static path_static x_static path_static v_new
                      Hstore Hplace Hpath_static Hstore1 Hvnew Hpres_new Hcompat
                      (ex_intro _ T_root (ex_intro _ st Htarget))
                      Heval_place Hpres_update Hupdate)
            as [Hstore_final Hv_final];
          repeat split; try assumption;
          eapply store_ref_targets_preserved_trans; eassumption
      end.
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing
                      env Ω n Σ0 s p T_place x path se v_target
                      Hstore Hplace Heval_place Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static),
        Hmut : sctx_lookup_mut ?x_static ?Σ0 = Some MMutable |- _ =>
          destruct (eval_place_direct_runtime_target_exists
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s fname Ω n R Σ T Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
    | Hready_cond : provenance_ready_expr e1,
      Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
      Hready_then : provenance_ready_expr e2,
      Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
      Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool true) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHthen Ω n R1 Σ1 T2 Σ2 R2 roots2
                    Hready_then Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_then)
          as [Hstore2 [Hv Hpres_then]];
        split;
        [ eapply store_typed_ctx_merge_left; eassumption
        | split;
          [ eapply value_has_type_if_left_result; exact Hv
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Ω n R Σ T Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    match goal with
      | Hready_cond : provenance_ready_expr e1,
        Htyped_cond : typed_env_roots env Ω n R Σ e1 ?T_cond ?Σ1 ?R1 ?roots_cond,
        Htyped_then : typed_env_roots env Ω n ?R1 Σ1 e2 ?T2 ?Σ2 ?R2 ?roots2,
        Hready_else : provenance_ready_expr e3,
        Htyped_else : typed_env_roots env Ω n ?R1 Σ1 e3 ?T3 ?Σ3 ?R3 ?roots3,
        Hmerge : ctx_merge (ctx_of_sctx ?Σ2) (ctx_of_sctx ?Σ3) = Some Σ' |- _ =>
        destruct (IHcond Ω n R Σ T_cond Σ1 R1 roots_cond
                    Hready_cond Hstore Hroots Hnodup Hrn Htyped_cond)
          as [Hstore1 [_ Hpres_cond]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e1 s1
                    (VBool false) Heval_cond Ω n R Σ T_cond Σ1 R1
                    roots_cond Hready_cond Hroots Hnodup Hrn Htyped_cond)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHelse Ω n R1 Σ1 T3 Σ3 R3 roots3
                    Hready_else Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_else)
          as [Hstore3 [Hv Hpres_else]];
        assert (Htypes : Forall2 sctx_entry_type_eq Σ2 Σ3)
        by (eapply typed_env_structural_branch_type_eq;
            [ eapply typed_env_roots_structural; exact Htyped_then
            | eapply typed_env_roots_structural; exact Htyped_else ]);
        split;
        [ eapply store_typed_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R' roots
      Hready _ _ _ _ _.
    inversion Hready.
  - intros s s_fn s_args s_body callee args0 fname captured fdef fcall vs ret
      used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
      Heval_body IHbody Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    inversion Hready.
  - intros s Ω n R Σ ps Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_rest IHrest
      Ω n R Σ ps Σ' R' roots Hready Hstore Hroots Hnodup Hrn Htyped.
    inversion Hready; subst.
    inversion Htyped; subst.
    match goal with
    | Hready_e : provenance_ready_expr e,
      Hready_rest : provenance_ready_args es,
      Htyped_e : typed_env_roots env Ω n R Σ e ?T_e ?Σ1 ?R1 ?roots_e,
      Hcompat : ty_compatible_b Ω ?T_e (param_ty ?p) = true,
      Htyped_rest : typed_args_roots env Ω n ?R1 ?Σ1 es ?ps_rest
        Σ' R' ?roots_rest |- _ =>
        destruct (IHe Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hstore Hroots Hnodup Hrn Htyped_e)
          as [Hstore1 [Hv Hpres_e]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_e Ω n R Σ T_e Σ1 R1 roots_e
                    Hready_e Hroots Hnodup Hrn Htyped_e)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n R1 Σ1 ps_rest Σ' R' roots_rest
                    Hready_rest Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hargs Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ econstructor;
            [ eapply value_has_type_store_preserved;
              [ exact Hv | exact Hpres_rest ]
            | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat
            | exact Hargs ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s Ω n lts args R Σ Σ' R' roots _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    repeat split.
    + exact Hstore.
    + constructor.
    + apply store_ref_targets_preserved_refl.
  - intros s s1 s2 fields f rest e v values Hlookup_expr Heval_field
      IHfield Heval_rest IHrest Ω n lts args R Σ Σ' R' roots Hready
      Hstore Hroots Hnodup Hrn Htyped.
    pose proof (provenance_ready_fields_lookup fields (field_name f) e
                  Hready Hlookup_expr) as Hready_field.
    inversion Htyped; subst.
    match goal with
    | Hlookup_typed : lookup_field_b (field_name f) ?fields0 = Some ?e_field,
      Htyped_field : typed_env_roots env Ω n R Σ ?e_field ?T_field ?Σ1
        ?R1 ?roots_field,
      Hcompat : ty_compatible_b Ω ?T_field
        (instantiate_struct_field_ty lts args f) = true,
      Htyped_rest : typed_fields_roots env Ω n lts args ?R1 ?Σ1
        ?fields0 rest Σ' R' ?roots_rest |- _ =>
        rewrite lookup_field_b_lookup_expr_field in Hlookup_typed;
        rewrite Hlookup_typed in Hlookup_expr;
        inversion Hlookup_expr; subst e_field;
        destruct (IHfield Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hstore Hroots Hnodup Hrn Htyped_field)
          as [Hstore1 [Hvalue Hpres_field]];
        destruct (proj1 eval_preserves_roots_ready_mutual env s e s1 v
                    Heval_field Ω n R Σ T_field Σ1 R1 roots_field
                    Hready_field Hroots Hnodup Hrn Htyped_field)
          as [Hroots1 [_ [Hnodup1 Hrn1]]];
        destruct (IHrest Ω n lts args R1 Σ1 Σ' R' roots_rest
                    Hready Hstore1 Hroots1 Hnodup1 Hrn1 Htyped_rest)
          as [Hstore2 [Hfields Hpres_rest]];
        split;
        [ exact Hstore2
        | split;
          [ constructor;
            [ reflexivity
            | eapply value_has_type_store_preserved;
              [ eapply value_has_type_compatible;
                [ exact Hvalue
                | apply ty_compatible_b_sound with (Ω := Ω); exact Hcompat ]
              | exact Hpres_rest ]
            | exact Hfields ]
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  }
  split.
  - intros env0 s0 e0 s0' v0 Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
      Hready Hstore Hroots Hnodup Hrn Htyped.
    destruct (proj1 (Htyping env0) s0 e0 s0' v0 Heval
                Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hstore Hroots Hnodup Hrn Htyped)
      as [Hstore' [Hv Hpres]].
    destruct (proj1 eval_preserves_roots_ready_mutual env0 s0 e0 s0' v0
                Heval Ω0 n0 R0 Σ0 T0 Σ0' R0' roots0
                Hready Hroots Hnodup Hrn Htyped)
      as [Hroots' [Hv_roots [Hnodup' Hrn']]].
    repeat split; assumption.
  - split.
    + intros env0 s0 args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0'
        R0' roots0 Hready Hstore Hroots Hnodup Hrn Htyped.
      destruct (proj1 (proj2 (Htyping env0)) s0 args0 s0' vs0 Heval
                  Ω0 n0 R0 Σ0 ps0 Σ0' R0' roots0
                  Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj1 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  args0 s0' vs0 Heval Ω0 n0 R0 Σ0 ps0 Σ0' R0'
                  roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
    + intros env0 s0 fields0 defs0 s0' values0 Heval Ω0 n0 lts0
        args0 R0 Σ0 Σ0' R0' roots0 Hready Hstore Hroots Hnodup Hrn
        Htyped.
      destruct (proj2 (proj2 (Htyping env0)) s0 fields0 defs0 s0'
                  values0 Heval Ω0 n0 lts0 args0 R0 Σ0 Σ0' R0'
                  roots0 Hready Hstore Hroots Hnodup Hrn Htyped)
        as [Hstore' [Hvals Hpres]].
      destruct (proj2 (proj2 eval_preserves_roots_ready_mutual) env0 s0
                  fields0 defs0 s0' values0 Heval Ω0 n0 lts0 args0 R0
                  Σ0 Σ0' R0' roots0 Hready Hroots Hnodup Hrn Htyped)
        as [Hroots' [Hvals_roots [Hnodup' Hrn']]].
      repeat split; assumption.
Qed.

Theorem eval_preserves_typing_direct_call_roots_ready :
  forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      preservation_direct_call_ready_expr e ->
      store_typed env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      fn_env_unique_by_name env ->
      env_fns_preservation_ready env ->
      direct_call_callee_body_root_evidence env ->
      store_typed env s' Σ' /\
      value_has_type env s' v T /\
      store_ref_targets_preserved env s s'.
Proof.
  intros env s e s' v Heval Ω n R Σ T Σ' R' roots Hready Hstore
    Hroots Hshadow Hrn Htyped Hunique _ Hcallee_roots.
  inversion Hready as [e_ready Hpres_ready | fname args Hready_args]; subst.
  - pose proof (preservation_ready_implies_provenance_ready e Hpres_ready)
      as Hprov.
    destruct (proj1 eval_preserves_typing_roots_ready_mutual
                env s e s' v Heval Ω n R Σ T Σ' R' roots
                Hprov Hstore Hroots Hshadow Hrn Htyped)
      as [Hstore' [Hv [Hpres _]]].
    repeat split; assumption.
  - dependent destruction Heval.
    dependent destruction Htyped.
    repeat match goal with
    | Hlookup : lookup_fn (fn_name ?f_typed) (env_fns env) =
        Some ?f_runtime,
      Hin : In ?f_typed (env_fns env) |- _ =>
        pose proof (lookup_fn_unique_by_name env (fn_name f_typed)
          f_runtime f_typed Hlookup Hin eq_refl Hunique) as Hsame;
        subst f_runtime
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : fn_name ?f_typed = ?fname_call |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin Hname Hunique) as Hsame;
        subst f_typed
    | Hlookup : lookup_fn ?fname_call (env_fns env) = Some ?f_runtime,
      Hin : In ?f_typed (env_fns env),
      Hname : ?fname_call = fn_name ?f_typed |- _ =>
        pose proof (lookup_fn_unique_by_name env fname_call f_runtime f_typed
          Hlookup Hin (eq_sym Hname) Hunique) as Hsame;
        subst f_typed
    end.
    match goal with
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used') |- _ =>
        destruct (Hcallee_roots Ω n R Σ Σ' R' arg_roots (fn_name fdef)
                    args_call fdef fcall σ s s_args vs used' Htyped_args
                    Heval_args Hrename)
          as (T_body & Γ_out & R_body & roots_body &
              Hprov_body & Hready_body & Htyped_body & Hcompat_body &
              Hexclude_ret & Hexclude_env)
    end.
    match goal with
    | Htyped_args : typed_args_roots env Ω n R Σ ?args_call
        (apply_lt_params ?σ (fn_params ?fdef)) Σ' R' ?arg_roots,
      Heval_args : eval_args env s ?args_call ?s_args ?vs,
      Hready_args0 : preservation_ready_args ?args_call,
      Hrename : alpha_rename_fn_def (store_names ?s_args) ?fdef =
        (?fcall, ?used'),
      Heval_body : eval env
        (bind_params (fn_params ?fcall) ?vs ?s_args)
        (fn_body ?fcall) ?s_body ?ret |- _ =>
        pose proof (preservation_ready_args_implies_provenance_ready
                      args_call Hready_args0) as Hprov_args;
        destruct (proj1 (proj2 eval_preserves_typing_ready_mutual)
                    env s args_call s_args vs Heval_args Ω n Σ
                    (apply_lt_params σ (fn_params fdef)) Σ'
                    Hready_args0 Hstore
                    (typed_args_roots_structural env Ω n R Σ args_call
                      (apply_lt_params σ (fn_params fdef)) Σ' R'
                      arg_roots Htyped_args))
          as [_ [Hargs_subst _]];
        pose proof (alpha_rename_fn_def_shape (store_names s_args)
                      fdef fcall used' Hrename) as Hshape;
        destruct Hshape as [_ [_ Hparams_alpha]];
        assert (Hargs_unsubst_fdef :
          eval_args_values_have_types env Ω s_args vs (fn_params fdef))
        by (eapply eval_args_values_have_types_apply_lt_params_inv;
            exact Hargs_subst);
        assert (Hargs_fcall :
          eval_args_values_have_types env Ω s_args vs (fn_params fcall))
        by (eapply eval_args_values_have_types_params_alpha;
            [ exact Hparams_alpha | exact Hargs_unsubst_fdef ]);
        assert (Hnodup :
          NoDup (ctx_names (params_ctx (fn_params fcall))))
        by (eapply alpha_rename_fn_def_params_nodup_ctx_names;
            exact Hrename);
        assert (Hfresh : params_fresh_in_store (fn_params fcall) s_args)
        by (eapply alpha_rename_fn_def_params_fresh_in_store;
            exact Hrename);
        destruct (eval_args_bind_params_call_param_root_env_ready
                    env s args_call s_args vs Ω n R Σ
                    (apply_lt_params σ (fn_params fdef)) Σ' R' arg_roots
                    (fn_params fcall) Heval_args Hprov_args Htyped_args
                    Hroots Hshadow Hrn Hnodup Hfresh Hargs_fcall)
          as [Hroots_bind [Hshadow_bind [Hrn_params Hcover_params]]];
        destruct (eval_direct_call_body_cleanup_preserves_value_and_refs
                    env Ω n R Σ Σ' R' arg_roots (fn_name fdef) args_call fdef fcall σ
                    s s_args s_body vs ret used' T_body Γ_out
                    (call_param_root_env (fn_params fcall) arg_roots R')
                    R_body roots_body Hstore Hroots Hshadow Hrn Hprov_args
                    Hready_args0 Htyped_args Heval_args Hrename Hroots_bind
                    Hshadow_bind Hrn_params Hcover_params Hprov_body
                    Hready_body Htyped_body Hcompat_body Hexclude_ret
                    Hexclude_env Heval_body)
          as [_ [Hstore_final [_ [_ [_ [_ [Hv_final [Hpres_final _]]]]]]]]
    end.
    repeat split; assumption.
Qed.
