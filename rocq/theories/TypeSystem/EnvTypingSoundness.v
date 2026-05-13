From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  TypingRules TypeChecker EnvStructuralRules EnvSoundnessFacts CheckerSoundness.
From Stdlib Require Import List String Bool Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Basic env/stateful checker soundness                                 *)
(* ------------------------------------------------------------------ *)

Fixpoint basic_expr (e : expr) : bool :=
  match e with
  | EUnit => true
  | ELit _ => true
  | EVar _ => true
  | EFn _ => true
  | EPlace _ => true
  | ELet _ _ _ e1 e2 => basic_expr e1 && basic_expr e2
  | ELetInfer _ _ e1 e2 => basic_expr e1 && basic_expr e2
  | EDeref e1 => basic_expr e1
  | EDrop e1 => basic_expr e1
  | EIf e1 e2 e3 => basic_expr e1 && basic_expr e2 && basic_expr e3
  | ECall _ _ => false
  | ECallExpr _ _ => false
  | EStruct _ _ _ _ => false
  | EReplace _ _ => false
  | EAssign _ _ => false
  | EBorrow _ _ => false
  end.

Lemma ctx_lookup_b_state_success :
  forall x Γ T b,
    ctx_lookup_b x Γ = Some (T, b) ->
    exists st, ctx_lookup_state x Γ = Some (T, st) /\ st_consumed st = b.
Proof.
  intros x Γ.
  induction Γ as [| [[[n Tn] st] m] rest IH]; intros T b Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (ident_eqb x n) eqn:Hname.
    + inversion Hlookup; subst.
      exists st. simpl. rewrite Hname. split; reflexivity.
    + destruct (IH T b Hlookup) as [st0 [Hstate Hconsumed]].
      exists st0. simpl. rewrite Hname. split; assumption.
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
  destruct (binding_available_b st path) eqn:Hpath; try discriminate.
  exists T, st. split; [reflexivity | exact Hpath].
Qed.

Lemma infer_place_env_type_sctx_structural_sound :
  forall env Σ p T,
    infer_place_env env (ctx_of_sctx Σ) p = infer_ok T ->
    typed_place_type_env_structural env Σ p T.
Proof.
  intros env Σ p.
  induction p as [x | p IH | p IH field]; intros T Hinfer; simpl in Hinfer.
  - destruct (ctx_lookup_b x (ctx_of_sctx Σ)) as [[Tx b] |] eqn:Hlookup;
      try discriminate.
    destruct b; try discriminate.
    inversion Hinfer; subst.
    destruct (ctx_lookup_b_state_success x (ctx_of_sctx Σ) T false Hlookup)
      as [st [Hstate _]].
    apply TPTES_Var with (st := st). exact Hstate.
  - destruct (infer_place_env env (ctx_of_sctx Σ) p) as [Tp | err] eqn:Hp;
      try discriminate.
    destruct Tp as [u c]; simpl in *.
    destruct c; try discriminate.
    inversion Hinfer; subst.
    eapply TPTES_Deref. apply IH. reflexivity.
  - destruct (infer_place_env env (ctx_of_sctx Σ) p) as [Tp | err] eqn:Hp;
      try discriminate.
    destruct (ty_core Tp) eqn:Hcore; try discriminate.
    destruct (lookup_struct s env) as [sdef |] eqn:Hstruct; try discriminate.
    destruct (lookup_field field (struct_fields sdef)) as [fdef |] eqn:Hfield;
      try discriminate.
    inversion Hinfer; subst.
    destruct (lookup_field_success field (struct_fields sdef) fdef Hfield)
      as [_ Hfname].
    subst field.
    eapply TPTES_Field.
    + replace (MkTy (ty_usage Tp) (TStruct s l l0)) with Tp
        by (destruct Tp as [u c]; simpl in Hcore; rewrite Hcore; reflexivity).
      apply IH. reflexivity.
    + simpl. exact Hcore.
    + exact Hstruct.
    + exact Hfield.
Qed.

Lemma infer_place_type_sctx_structural_sound :
  forall env Σ p T,
    infer_place_type_sctx env Σ p = infer_ok T ->
    typed_place_type_env_structural env Σ p T.
Proof.
  intros env Σ p.
  induction p as [x | p IH | p IH field]; intros T Hinfer; simpl in Hinfer.
  - destruct (sctx_lookup x Σ) as [[Tx st] |] eqn:Hlookup; try discriminate.
    inversion Hinfer; subst. apply TPTES_Var with (st := st). exact Hlookup.
  - destruct (infer_place_type_sctx env Σ p) as [Tp | err] eqn:Hp; try discriminate.
    destruct Tp as [u c]; simpl in *.
    destruct c; try discriminate.
    inversion Hinfer; subst.
    eapply TPTES_Deref. apply IH. reflexivity.
  - destruct (infer_place_type_sctx env Σ p) as [Tp | err] eqn:Hp; try discriminate.
    destruct (ty_core Tp) eqn:Hcore; try discriminate.
    destruct (lookup_struct s env) as [sdef |] eqn:Hstruct; try discriminate.
    destruct (lookup_field field (struct_fields sdef)) as [fdef |] eqn:Hfield;
      try discriminate.
    inversion Hinfer; subst.
    destruct (lookup_field_success field (struct_fields sdef) fdef Hfield)
      as [_ Hfname].
    subst field.
    eapply TPTES_Field.
    + replace (MkTy (ty_usage Tp) (TStruct s l l0)) with Tp
        by (destruct Tp as [u c]; simpl in Hcore; rewrite Hcore; reflexivity).
      apply IH. reflexivity.
    + simpl. exact Hcore.
    + exact Hstruct.
    + exact Hfield.
Qed.

Lemma infer_place_sctx_structural_sound :
  forall env Σ p T,
    infer_place_sctx env Σ p = infer_ok T ->
    typed_place_env_structural env Σ p T.
Proof.
  intros env Σ p.
  induction p as [x | p IH | p IH field]; intros T Hinfer; simpl in Hinfer.
  - destruct (sctx_lookup x Σ) as [[Tx st] |] eqn:Hlookup; try discriminate.
    destruct (binding_available_b st []) eqn:Havailable; try discriminate.
    inversion Hinfer; subst. apply TPES_Var with (st := st); assumption.
  - destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hp; try discriminate.
    destruct Tp as [u c]; simpl in *.
    destruct c; try discriminate.
    inversion Hinfer; subst.
    eapply TPES_Deref. apply IH. reflexivity.
  - destruct (infer_place_env env (ctx_of_sctx Σ) p) as [Tp | err] eqn:Hp;
      try discriminate.
    destruct (ty_core Tp) eqn:Hcore; try discriminate.
    destruct (lookup_struct s env) as [sdef |] eqn:Hstruct; try discriminate.
    destruct (lookup_field field (struct_fields sdef)) as [fdef |] eqn:Hfield;
      try discriminate.
    destruct (place_path p) as [[x base_path] |] eqn:Hbase_path.
    + destruct (sctx_path_available Σ x (base_path ++ [field])) as [[] | err] eqn:Havailable;
        try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_field_success field (struct_fields sdef) fdef Hfield)
        as [_ Hfname].
      subst field.
      destruct (sctx_path_available_success Σ x (base_path ++ [field_name fdef]) Havailable)
        as [Troot [st [Hlookup Hpath_available]]].
      eapply TPES_Field.
      * replace (MkTy (ty_usage Tp) (TStruct s l l0)) with Tp
          by (destruct Tp as [u c]; simpl in Hcore; rewrite Hcore; reflexivity).
        eapply infer_place_env_type_sctx_structural_sound. exact Hp.
      * simpl. exact Hcore.
      * exact Hstruct.
      * exact Hfield.
      * simpl. rewrite Hbase_path. reflexivity.
      * exact Hlookup.
      * exact Hpath_available.
    + inversion Hinfer; subst.
      destruct (lookup_field_success field (struct_fields sdef) fdef Hfield)
        as [_ Hfname].
      subst field.
      eapply TPES_Field_Indirect.
      * replace (MkTy (ty_usage Tp) (TStruct s l l0)) with Tp
          by (destruct Tp as [u c]; simpl in Hcore; rewrite Hcore; reflexivity).
        eapply infer_place_env_type_sctx_structural_sound. exact Hp.
      * simpl. exact Hcore.
      * exact Hstruct.
      * exact Hfield.
      * simpl. rewrite Hbase_path. reflexivity.
Qed.

Theorem infer_core_env_state_fuel_basic_structural_sound :
  forall fuel env Ω n Σ e T Σ',
    basic_expr e = true ->
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  induction fuel as [| fuel' IH]; intros env Ω n Σ e T Σ' Hbasic Hinfer.
  - simpl in Hinfer. discriminate.
  - destruct e; simpl in Hbasic; simpl in Hinfer; try discriminate.
    + inversion Hinfer; subst. constructor.
    + destruct l; inversion Hinfer; subst; constructor.
    + destruct (sctx_lookup i Σ) as [[Tvar st] |] eqn:Hlookup; try discriminate.
      destruct (binding_available_b st []) eqn:Havailable; try discriminate.
      destruct (consume_place_value env Σ (PVar i) Tvar) as [Σ0 | err] eqn:Hconsume;
        try discriminate.
      unfold consume_place_value in Hconsume.
      destruct (usage_eqb (ty_usage Tvar) UUnrestricted) eqn:Husage.
      * inversion Hconsume; subst.
        inversion Hinfer; subst.
        apply TES_Var_Copy.
        -- apply TPES_Var with (st := st); assumption.
        -- apply usage_eqb_true. exact Husage.
      * simpl in Hconsume.
        destruct (sctx_consume_path Σ i []) as [Σc | err] eqn:Hconsume_path;
          try discriminate.
        inversion Hconsume; subst.
        inversion Hinfer; subst.
        eapply TES_Var_Move.
        -- apply TPES_Var with (st := st); assumption.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hconsume_path.
    + apply andb_true_iff in Hbasic as [Hbasic1 Hbasic2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i t m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i t Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Let.
      * eapply IH; [exact Hbasic1 | exact He1].
      * exact Hcompat.
      * eapply IH; [exact Hbasic2 | exact He2].
      * exact Hcheck.
    + apply andb_true_iff in Hbasic as [Hbasic1 Hbasic2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i T1 m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i T1 Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_LetInfer.
      * eapply IH; [exact Hbasic1 | exact He1].
      * eapply IH; [exact Hbasic2 | exact He2].
      * exact Hcheck.
    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TES_Fn; eassumption.
    + destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct (consume_place_value env Σ p Tp) as [Σ0 | err] eqn:Hconsume;
        try discriminate.
      unfold consume_place_value in Hconsume.
      destruct (usage_eqb (ty_usage Tp) UUnrestricted) eqn:Husage.
      * inversion Hconsume; subst.
        inversion Hinfer; subst.
        apply TES_Place_Copy.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
      * destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        destruct (sctx_consume_path Σ x path) as [Σc | err] eqn:Hconsume_path;
          try discriminate.
        inversion Hconsume; subst.
        inversion Hinfer; subst.
        eapply TES_Place_Move.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hpath.
        -- exact Hconsume_path.
    + destruct (expr_as_place e) as [p |] eqn:Hplace_expr.
      * destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
        destruct Tp as [u c]; simpl in *.
        destruct c; try discriminate.
        destruct (usage_eqb (ty_usage t) UUnrestricted) eqn:Husage; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Deref_Place.
        -- exact Hplace_expr.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
      * destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tr Σr] | err]
          eqn:Hr; try discriminate.
        destruct Tr as [u c]; simpl in *.
        destruct c; try discriminate.
        destruct (usage_eqb (ty_usage t) UUnrestricted) eqn:Husage; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Deref_Expr.
        -- exact Hplace_expr.
        -- eapply IH; [exact Hbasic | exact Hr].
        -- apply usage_eqb_true. exact Husage.
    + destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Te Σe] | err]
        eqn:He; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Drop. eapply IH; [exact Hbasic | exact He].
    + repeat rewrite andb_true_iff in Hbasic.
      destruct Hbasic as [[Hbasic1 Hbasic2] Hbasic3].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[Tcond Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (ty_core_eqb (ty_core Tcond) TBooleans) eqn:Hbool; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ1 e2) as [[T2 Σ2] | err2]
        eqn:He2; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ1 e3) as [[T3 Σ3] | err3]
        eqn:He3; try discriminate.
      destruct (ty_core_eqb (ty_core T2) (ty_core T3)) eqn:Hcore; try discriminate.
      destruct (ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3)) as [Γ4 |] eqn:Hmerge;
        try discriminate.
      inversion Hinfer; subst.
      eapply TES_If.
      * eapply IH; [exact Hbasic1 | exact He1].
      * apply ty_core_eqb_true. exact Hbool.
      * eapply IH; [exact Hbasic2 | exact He2].
      * eapply IH; [exact Hbasic3 | exact He3].
      * apply ty_core_eqb_true. exact Hcore.
      * exact Hmerge.
Qed.
