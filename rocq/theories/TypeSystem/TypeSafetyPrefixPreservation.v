From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyPrefixPreservationCallInvariants.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_let_roots_ready_preserves_typing_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
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
  intros Hpreservation Hroots_preservation env Ω n R R' Σ Σ' s s'
    m x T_ann e1 e2 T roots v Hstore Hroots Hnodup Hrn Htyped
    Hready Hready1_struct Hready2_struct Heval.
  destruct (proj1 Hroots_preservation env s
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
        exact (proj1 Hpreservation env s e1 s1_body v1_body Heval0
          Ω n Σ T1_body Σ1_body Hready1_struct Hstore0 Htyped0)
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
          exact (proj1 Hpreservation env
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

Theorem eval_preserves_typing_roots_ready_prefix_mutual_core :
  (forall env s e s' v,
    eval env s e s' v ->
    forall (Ω : outlives_ctx) (n : nat) R Σ T Σ' R' roots,
      provenance_ready_expr e ->
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_env_roots env Ω n R Σ e T Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
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
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
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
      store_typed_prefix env s Σ ->
      store_roots_within R s ->
      store_no_shadow s ->
      root_env_no_shadow R ->
      typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
      store_typed_prefix env s' Σ' /\
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
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_env_roots env Ω n R Σ e T Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
        value_has_type env s' v T /\
        store_ref_targets_preserved env s s') /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      forall (Ω : outlives_ctx) (n : nat) R Σ ps Σ' R' roots,
        provenance_ready_args args ->
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_args_roots env Ω n R Σ args ps Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
        eval_args_values_have_types env Ω s' vs ps /\
        store_ref_targets_preserved env s s') /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      forall (Ω : outlives_ctx) (n : nat) lts args R Σ Σ' R' roots,
        provenance_ready_fields fields ->
        store_typed_prefix env s Σ ->
        store_roots_within R s ->
        store_no_shadow s ->
        root_env_no_shadow R ->
        typed_fields_roots env Ω n lts args R Σ fields defs Σ' R' roots ->
        store_typed_prefix env s' Σ' /\
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
    + destruct (eval_var_copy_preserves_typing_prefix env Ω n _ s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_ref_targets_preserved_refl.
    + exfalso.
      eapply eval_var_copy_static_move_contradiction_prefix; eassumption.
  - intros s x se Hlookup Hconsume Hused Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    + exfalso.
      eapply eval_var_consume_static_copy_contradiction_prefix; eassumption.
    + destruct (eval_var_move_preserves_typing_prefix env Ω n Σ Σ' s x T se
                  Hstore) as [Hstore' Hv]; try eassumption.
      repeat split; try assumption.
      apply store_mark_used_ref_targets_preserved.
  - intros s p x_eval path_eval se T_eval v Heval_place Hlookup
      Havailable Htype_eval Hconsume Hvalue Ω n R Σ T Σ' R' roots
      Hready Hstore _ _ _ Htyped.
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
      Ω n R Σ T Σ' R' roots Hready Hstore _ _ _ Htyped.
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
          store_typed_prefix env s Σ ->
          typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
          eval env s e1 s1 v1 ->
          store_typed_prefix env s1 Σ1_body /\
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
            store_typed_prefix env (store_add x T_ann v1 s1)
              (sctx_add x T_ann m Σ1_body) ->
            typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
              e2 T2_body Σ2_body ->
            eval env (store_add x T_ann v1 s1) e2 s2 v2 ->
            store_typed_prefix env s2 Σ2_body /\
            value_has_type env s2 v2 T2_body /\
            store_ref_targets_preserved env
              (store_add x T_ann v1 s1) s2);
          [ intros Hstore0 _ Heval0;
            exact (IH2 Ω n (root_env_add x roots1_body R1_body)
              (sctx_add x T_ann m Σ1_body) T2_body Σ2_body R2_body
              roots2_body Hready2 Hstore0 Hadd_roots Hadd_nodup Hadd_rn
              Htyped2)
          | eapply eval_let_roots_preserves_typing_prefix;
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
  - intros s p x path rk Heval_place Ω n R Σ T Σ' R' roots Hready
      Hstore _ _ _ Htyped.
    dependent destruction Hready.
    inversion Htyped; subst.
    + match goal with
      | Hplace : typed_place_env_structural env ?Σ0 p ?T_place,
        Hpath : place_path p = Some (?x_static, ?path_static) |- _ =>
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_shared_preserves_typing_prefix
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
          destruct (eval_place_direct_runtime_target_exists_prefix
                      env Σ0 s p T_place x_static path_static x path
                      Hstore Hplace Hpath Heval_place)
            as [se [v_target [Hlookup [Hvalue Htype_eval]]]];
          destruct (eval_borrow_unique_preserves_typing_prefix
                      env Ω n Σ0 s p T_place x_static path_static x path
                      se v_target Hstore Hplace Hpath Hmut Heval_place
                      Hlookup Htype_eval Hvalue)
            as [Hstore' Hv];
          repeat split; try assumption;
          apply store_ref_targets_preserved_refl
      end.
  - intros s r p x path se v T_eval Hplace Heval_place Hlookup Hvalue
      Htype_eval Husage Ω n R Σ T Σ' R' roots Hready _ _ _ _ _.
    dependent destruction Hready.
  - intros s s_r r x path se v T_eval Hnot_place Heval_r IHr Hlookup
      Hvalue Htype_eval Husage Ω n R Σ T Σ' R' roots Hready Hstore Hroots
      Hnodup Hrn Htyped.
    dependent destruction Hready.
    inversion Heval_r; subst.
    dependent destruction Htyped.
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H4 H2)
        as [Hx Hpath].
      subst x path.
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_root [st [HΣ [_ Htype_path]]]].
      destruct (store_typed_prefix_lookup_sctx
                  env s_r Σ x1 T_root st Hstore HΣ)
        as [se' [Hlookup' [_ [HT [_ Hvroot]]]]].
      rewrite Hlookup in Hlookup'.
      inversion Hlookup'; subst se'.
      rewrite HT in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
    + destruct (eval_place_matches_place_path s_r p x path x1 path1 H5 H2)
        as [Hx Hpath].
      subst x path.
      destruct (typed_place_direct_lookup env Σ p T x1 path1 H0 H2)
        as [T_root [st [HΣ [_ Htype_path]]]].
      destruct (store_typed_prefix_lookup_sctx
                  env s_r Σ x1 T_root st Hstore HΣ)
        as [se' [Hlookup' [_ [HT [_ Hvroot]]]]].
      rewrite Hlookup in Hlookup'.
      inversion Hlookup'; subst se'.
      rewrite HT in Htype_eval.
      rewrite Htype_path in Htype_eval.
      inversion Htype_eval; subst T_eval.
      repeat split; try assumption;
        try apply store_ref_targets_preserved_refl;
        try (eapply value_lookup_path_has_type; eassumption);
        try (eapply eval_place_lookup_path_roots_within; eassumption).
  - intros s fname fdef Hlookup Hcaps Ω n R Σ T Σ' R' roots
      _ Hstore _ _ _ Htyped.
    inversion Htyped; subst.
    split.
    + exact Hstore.
    + split.
      * eapply VHT_ClosureIn; [eassumption | reflexivity].
      * apply store_ref_targets_preserved_refl.
  - intros s fname captures captured fdef Hlookup Hcheck Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
    inversion Hready.
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
        [ eapply store_typed_prefix_ctx_merge_left; eassumption
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
        [ eapply store_typed_prefix_ctx_merge_right; eassumption
        | split;
          [ eapply value_has_type_if_right_result; eassumption
          | eapply store_ref_targets_preserved_trans; eassumption ] ]
    end.
  - intros s s_args s_body fname fdef fcall args0 vs ret used' Hlookup
      Hcaps Heval_args IHargs Hrename Heval_body IHbody Ω n R Σ T Σ' R'
      roots Hready _ _ _ _ _.
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
