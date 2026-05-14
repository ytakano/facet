From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  TypingRules TypeChecker EnvStructuralRules EnvSoundnessFacts CheckerSoundness.
From Stdlib Require Import List String Bool Lia PeanoNat.
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
Fixpoint call_expr (e : expr) : bool :=
  match e with
  | EUnit => true
  | ELit _ => true
  | EVar _ => true
  | EFn _ => true
  | EPlace _ => true
  | ELet _ _ _ e1 e2 => call_expr e1 && call_expr e2
  | ELetInfer _ _ e1 e2 => call_expr e1 && call_expr e2
  | ECall _ args => forallb call_expr args
  | ECallExpr callee args => call_expr callee && forallb call_expr args
  | EDeref e1 => call_expr e1
  | EDrop e1 => call_expr e1
  | EIf e1 e2 e3 => call_expr e1 && call_expr e2 && call_expr e3
  | EStruct _ _ _ _ => false
  | EReplace _ _ => false
  | EAssign _ _ => false
  | EBorrow _ _ => false
  end.

Definition call_exprs (args : list expr) : bool := forallb call_expr args.

Lemma call_exprs_in_true :
  forall args e,
    call_exprs args = true ->
    In e args ->
    call_expr e = true.
Proof.
  unfold call_exprs.
  intros args e Hargs Hin.
  rewrite forallb_forall in Hargs.
  apply Hargs. exact Hin.
Qed.

Fixpoint infer_env_args_collect fuel env Ω n (Σ : sctx) (args : list expr)
    : infer_result (list Ty * sctx) :=
  match args with
  | [] => infer_ok ([], Σ)
  | e :: rest =>
      match infer_core_env_state_fuel fuel env Ω n Σ e with
      | infer_err err => infer_err err
      | infer_ok (T_e, Σ1) =>
          match infer_env_args_collect fuel env Ω n Σ1 rest with
          | infer_err err => infer_err err
          | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
          end
      end
  end.

Lemma infer_env_args_collect_eq :
  forall fuel env Ω n args Σ,
    (fix collect (Σ0 : sctx) (as_ : list expr) : infer_result (list Ty * sctx) :=
       match as_ with
       | [] => infer_ok ([], Σ0)
       | e' :: es =>
           match infer_core_env_state_fuel fuel env Ω n Σ0 e' with
           | infer_err err => infer_err err
           | infer_ok (T_e, Σ1) =>
               match collect Σ1 es with
               | infer_err err => infer_err err
               | infer_ok (tys, Σ2) => infer_ok (T_e :: tys, Σ2)
               end
           end
       end) Σ args =
    infer_env_args_collect fuel env Ω n Σ args.
Proof.
  intros fuel env Ω n args.
  induction args as [|e rest IH]; intros Σ; simpl.
  - reflexivity.
  - destruct (infer_core_env_state_fuel fuel env Ω n Σ e) as [[T_e Σ1] | err] eqn:He;
      [rewrite IH |]; reflexivity.
Qed.

Lemma infer_env_args_collect_sound :
  forall fuel env Ω n Σ args arg_tys params Σ',
    infer_env_args_collect fuel env Ω n Σ args = infer_ok (arg_tys, Σ') ->
    (forall Σ0 e T Σ1,
        In e args ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T, Σ1) ->
        typed_env_structural env Ω n Σ0 e T Σ1) ->
    check_args Ω arg_tys params = None ->
    typed_args_env_structural env Ω n Σ args params Σ'.
Proof.
  intros fuel env Ω n Σ args.
  revert Σ.
  induction args as [|e rest IH]; intros Σ arg_tys params Σ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. inversion Hcollect; subst.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e) as [[T_e Σ1] | err] eqn:He;
      try discriminate.
    destruct (infer_env_args_collect fuel env Ω n Σ1 rest) as [[tys Σ2] | err'] eqn:Htail;
      try discriminate.
    inversion Hcollect; subst.
    destruct params as [|p ps]; simpl in Hcheck; try discriminate.
    destruct (ty_compatible_b Ω T_e (param_ty p)) eqn:Hcompat; try discriminate.
    eapply TESArgs_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + exact Hcompat.
    + eapply IH.
      * exact Htail.
      * intros Σ0 e0 T0 Σ0' Hin Hinfer0.
        eapply Hexpr.
        -- right. exact Hin.
        -- exact Hinfer0.
      * exact Hcheck.
Qed.

Fixpoint struct_expr (e : expr) : bool :=
  match e with
  | EUnit => true
  | ELit _ => true
  | EVar _ => true
  | EFn _ => true
  | EPlace _ => true
  | ELet _ _ _ e1 e2 => struct_expr e1 && struct_expr e2
  | ELetInfer _ _ e1 e2 => struct_expr e1 && struct_expr e2
  | ECall _ args => forallb struct_expr args
  | ECallExpr callee args => struct_expr callee && forallb struct_expr args
  | EStruct _ _ _ fields => forallb (fun '(_, e_field) => struct_expr e_field) fields
  | EReplace _ e_new => struct_expr e_new
  | EAssign _ e_new => struct_expr e_new
  | EBorrow _ _ => true
  | EDeref e1 => struct_expr e1
  | EDrop e1 => struct_expr e1
  | EIf e1 e2 e3 => struct_expr e1 && struct_expr e2 && struct_expr e3
  end.

Definition struct_exprs (args : list expr) : bool := forallb struct_expr args.

Lemma struct_exprs_in_true :
  forall args e,
    struct_exprs args = true ->
    In e args ->
    struct_expr e = true.
Proof.
  unfold struct_exprs.
  intros args e Hargs Hin.
  rewrite forallb_forall in Hargs.
  apply Hargs. exact Hin.
Qed.

Lemma lookup_field_b_struct_expr_true :
  forall fields name e,
    forallb (fun '(_, e_field) => struct_expr e_field) fields = true ->
    lookup_field_b name fields = Some e ->
    struct_expr e = true.
Proof.
  induction fields as [|[fname efield] rest IH]; intros name e Hfields Hlookup; simpl in *.
  - discriminate.
  - apply andb_true_iff in Hfields as [Hhead Htail].
    destruct (String.eqb name fname) eqn:Hname.
    + inversion Hlookup; subst. exact Hhead.
    + eapply IH; eassumption.
Qed.

Fixpoint infer_env_fields_collect fuel env Ω n lts args
    (Σ : sctx) (fields : list (string * expr)) (defs : list field_def)
    : infer_result sctx :=
  match defs with
  | [] => infer_ok Σ
  | f :: rest =>
      match lookup_field_b (field_name f) fields with
      | None => infer_err (ErrMissingField (field_name f))
      | Some e_field =>
          match infer_core_env_state_fuel fuel env Ω n Σ e_field with
          | infer_err err => infer_err err
          | infer_ok (T_field, Σ1) =>
              let T_expected := instantiate_struct_field_ty lts args f in
              if ty_compatible_b Ω T_field T_expected
              then infer_env_fields_collect fuel env Ω n lts args Σ1 fields rest
              else infer_err (compatible_error T_field T_expected)
          end
      end
  end.

Lemma infer_env_fields_collect_eq :
  forall fuel env Ω n lts args fields defs Σ,
    (fix go (Σ0 : sctx) (defs0 : list field_def) : infer_result sctx :=
       match defs0 with
       | [] => infer_ok Σ0
       | f :: rest =>
           match lookup_field_b (field_name f) fields with
           | None => infer_err (ErrMissingField (field_name f))
           | Some e_field =>
               match infer_core_env_state_fuel fuel env Ω n Σ0 e_field with
               | infer_err err => infer_err err
               | infer_ok (T_field, Σ1) =>
                   let T_expected := instantiate_struct_field_ty lts args f in
                   if ty_compatible_b Ω T_field T_expected
                   then go Σ1 rest
                   else infer_err (compatible_error T_field T_expected)
               end
           end
       end) Σ defs =
    infer_env_fields_collect fuel env Ω n lts args Σ fields defs.
Proof.
  intros fuel env Ω n lts args fields defs.
  induction defs as [|f rest IH]; intros Σ; simpl.
  - reflexivity.
  - destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try reflexivity.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e_field) as [[T_field Σ1] | err]
      eqn:Hfield; try reflexivity.
    destruct (ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f));
      [rewrite IH |]; reflexivity.
Qed.

Lemma infer_env_fields_collect_sound :
  forall fuel env Ω n lts args Σ fields defs Σ',
    forallb (fun '(_, e_field) => struct_expr e_field) fields = true ->
    infer_env_fields_collect fuel env Ω n lts args Σ fields defs = infer_ok Σ' ->
    (forall Σ0 e T Σ1,
        struct_expr e = true ->
        infer_core_env_state_fuel fuel env Ω n Σ0 e = infer_ok (T, Σ1) ->
        typed_env_structural env Ω n Σ0 e T Σ1) ->
    typed_fields_env_structural env Ω n lts args Σ fields defs Σ'.
Proof.
  intros fuel env Ω n lts args Σ fields defs.
  revert Σ.
  induction defs as [|f rest IH]; intros Σ Σ' Hfields Hcollect Hexpr; simpl in Hcollect.
  - inversion Hcollect; subst. constructor.
  - destruct (lookup_field_b (field_name f) fields) as [e_field |] eqn:Hlookup;
      try discriminate.
    destruct (infer_core_env_state_fuel fuel env Ω n Σ e_field) as [[T_field Σ1] | err]
      eqn:Hfield; try discriminate.
    destruct (ty_compatible_b Ω T_field (instantiate_struct_field_ty lts args f))
      eqn:Hcompat; try discriminate.
    eapply TESFields_Cons.
    + exact Hlookup.
    + eapply Hexpr.
      * eapply lookup_field_b_struct_expr_true; eassumption.
      * exact Hfield.
    + exact Hcompat.
    + eapply IH.
      * exact Hfields.
      * exact Hcollect.
      * exact Hexpr.
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

Lemma place_under_unique_ref_b_sound :
  forall env Σ p,
    place_under_unique_ref_b env Σ p = true ->
    place_under_unique_ref_structural env Σ p.
Proof.
  intros env Σ p.
  induction p as [x | p IH | p IH field]; intros Hunique; simpl in Hunique.
  - discriminate.
  - destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
    destruct Tp as [u c]; simpl in Hunique.
    destruct c; try discriminate.
    destruct r; try discriminate.
    eapply PUURS_Deref.
    eapply infer_place_sctx_structural_sound. exact Hplace.
  - apply PUURS_Field. apply IH. exact Hunique.
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

Theorem infer_core_env_state_fuel_call_structural_sound :
  forall fuel env Ω n Σ e T Σ',
    call_expr e = true ->
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  induction fuel as [| fuel' IH]; intros env Ω n Σ e T Σ' Hcall Hinfer.
  - simpl in Hinfer. discriminate.
  - destruct e; simpl in Hcall; simpl in Hinfer; try discriminate.
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
    + apply andb_true_iff in Hcall as [Hcall1 Hcall2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i t m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i t Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Let.
      * eapply IH; [exact Hcall1 | exact He1].
      * exact Hcompat.
      * eapply IH; [exact Hcall2 | exact He2].
      * exact Hcheck.
    + apply andb_true_iff in Hcall as [Hcall1 Hcall2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i T1 m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i T1 Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_LetInfer.
      * eapply IH; [exact Hcall1 | exact He1].
      * eapply IH; [exact Hcall2 | exact He2].
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
    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
      rewrite infer_env_args_collect_eq in Hinfer.
      destruct (infer_env_args_collect fuel' env Ω n Σ l) as [[arg_tys Σargs] | err]
        eqn:Hcollect; try discriminate.
      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
          arg_tys (fn_params fdef)) as [σ_acc |] eqn:Hbuild; try discriminate.
      remember (apply_lt_params (finalize_subst σ_acc) (fn_params fdef)) as ps_subst.
      destruct (check_args Ω arg_tys ps_subst) as [err |] eqn:Hcheck; try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
        try discriminate.
      remember (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)) as Ω_subst.
      destruct (outlives_constraints_hold_b Ω Ω_subst) eqn:Hout; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TES_Call with (fdef := fdef) (σ := finalize_subst σ_acc).
      * exact Hin.
      * exact Hname.
      * eapply infer_env_args_collect_sound.
        -- exact Hcollect.
        -- intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
           eapply IH.
           ++ eapply call_exprs_in_true; eassumption.
           ++ exact Hinfer_arg.
        -- exact Hcheck.
      * apply env_outlives_constraints_hold_b_sound. exact Hout.
    + apply andb_true_iff in Hcall as [Hcallee Hargs].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tcallee Σc] | err]
        eqn:Hcallee_infer; try discriminate.
      rewrite infer_env_args_collect_eq in Hinfer.
      destruct (infer_env_args_collect fuel' env Ω n Σc l) as [[arg_tys Σargs] | err]
        eqn:Hcollect; try discriminate.
      destruct Tcallee as [u c]; simpl in *.
      destruct c; try discriminate.
      * destruct (check_arg_tys Ω arg_tys l0) as [err |] eqn:Hcheck; try discriminate.
        inversion Hinfer; subst.
        eapply TES_CallExpr_Fn.
        -- eapply IH; [exact Hcallee | exact Hcallee_infer].
        -- eapply infer_env_args_collect_sound.
           ++ exact Hcollect.
           ++ intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
              eapply IH.
              ** eapply call_exprs_in_true; eassumption.
              ** exact Hinfer_arg.
           ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
      * destruct (ty_core t) eqn:Hbody; try discriminate.
        destruct (build_bound_sigma (repeat None n0) arg_tys l0) as [σ |] eqn:Hbuild;
          try discriminate.
        destruct (check_arg_tys Ω arg_tys (map (open_bound_ty σ) l0)) as [err |] eqn:Hcheck;
          try discriminate.
        destruct (contains_lbound_ty (open_bound_ty σ t0) ||
            contains_lbound_outlives (open_bound_outlives σ o)) eqn:Hleak;
          try discriminate.
        destruct (outlives_constraints_hold_b Ω (open_bound_outlives σ o)) eqn:Hout;
          try discriminate.
        inversion Hinfer; subst.
        apply opened_call_no_lbound_sound in Hleak as [Hret Hbounds].
        eapply TES_CallExpr_Forall with (σ := σ) (param_tys := l0).
        -- eapply IH; [exact Hcallee | exact Hcallee_infer].
        -- exact Hbody.
        -- eapply infer_env_args_collect_sound.
           ++ exact Hcollect.
           ++ intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
              eapply IH.
              ** eapply call_exprs_in_true; eassumption.
              ** exact Hinfer_arg.
           ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
        -- exact Hret.
        -- exact Hbounds.
        -- apply env_outlives_constraints_hold_b_sound. exact Hout.
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
        -- eapply IH; [exact Hcall | exact Hr].
        -- apply usage_eqb_true. exact Husage.
    + destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Te Σe] | err]
        eqn:He; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Drop. eapply IH; [exact Hcall | exact He].
    + repeat rewrite andb_true_iff in Hcall.
      destruct Hcall as [[Hcall1 Hcall2] Hcall3].
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
      * eapply IH; [exact Hcall1 | exact He1].
      * apply ty_core_eqb_true. exact Hbool.
      * eapply IH; [exact Hcall2 | exact He2].
      * eapply IH; [exact Hcall3 | exact He3].
      * apply ty_core_eqb_true. exact Hcore.
      * exact Hmerge.
Qed.

Theorem infer_core_env_state_fuel_struct_structural_sound :
  forall fuel env Ω n Σ e T Σ',
    struct_expr e = true ->
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env_structural env Ω n Σ e T Σ'.
Proof.
  induction fuel as [| fuel' IH]; intros env Ω n Σ e T Σ' Hstruct Hinfer.
  - simpl in Hinfer. discriminate.
  - destruct e; simpl in Hstruct; simpl in Hinfer; try discriminate.
    + inversion Hinfer; subst. constructor.
    + destruct l; inversion Hinfer; subst; constructor.
    + destruct (sctx_lookup i Σ) as [[Tvar st] |] eqn:Hlookup; try discriminate.
      destruct (binding_available_b st []) eqn:Havailable; try discriminate.
      destruct (consume_place_value env Σ (PVar i) Tvar) as [Σ0 | err] eqn:Hconsume;
        try discriminate.
      unfold consume_place_value in Hconsume.
      destruct (usage_eqb (ty_usage Tvar) UUnrestricted) eqn:Husage.
      * inversion Hconsume; subst. inversion Hinfer; subst.
        apply TES_Var_Copy.
        -- apply TPES_Var with (st := st); assumption.
        -- apply usage_eqb_true. exact Husage.
      * simpl in Hconsume.
        destruct (sctx_consume_path Σ i []) as [Σc | err] eqn:Hconsume_path;
          try discriminate.
        inversion Hconsume; subst. inversion Hinfer; subst.
        eapply TES_Var_Move.
        -- apply TPES_Var with (st := st); assumption.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hconsume_path.
    + apply andb_true_iff in Hstruct as [Hstruct1 Hstruct2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i t m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i t Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Let.
      * eapply IH; [exact Hstruct1 | exact He1].
      * exact Hcompat.
      * eapply IH; [exact Hstruct2 | exact He2].
      * exact Hcheck.
    + apply andb_true_iff in Hstruct as [Hstruct1 Hstruct2].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e1) as [[T1 Σ1] | err1]
        eqn:He1; try discriminate.
      destruct (infer_core_env_state_fuel fuel' env Ω n (sctx_add i T1 m Σ1) e2)
        as [[T2 Σ2] | err2] eqn:He2; try discriminate.
      destruct (sctx_check_ok i T1 Σ2) eqn:Hcheck; try discriminate.
      inversion Hinfer; subst.
      eapply TES_LetInfer.
      * eapply IH; [exact Hstruct1 | exact He1].
      * eapply IH; [exact Hstruct2 | exact He2].
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
      * inversion Hconsume; subst. inversion Hinfer; subst.
        apply TES_Place_Copy.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- apply usage_eqb_true. exact Husage.
      * destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        destruct (sctx_consume_path Σ x path) as [Σc | err] eqn:Hconsume_path;
          try discriminate.
        inversion Hconsume; subst. inversion Hinfer; subst.
        eapply TES_Place_Move.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
        -- exact Hpath.
        -- exact Hconsume_path.
    + destruct (lookup_fn_b i (env_fns env)) as [fdef |] eqn:Hlookup; try discriminate.
      rewrite infer_env_args_collect_eq in Hinfer.
      destruct (infer_env_args_collect fuel' env Ω n Σ l) as [[arg_tys Σargs] | err]
        eqn:Hcollect; try discriminate.
      destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef))
          arg_tys (fn_params fdef)) as [σ_acc |] eqn:Hbuild; try discriminate.
      remember (apply_lt_params (finalize_subst σ_acc) (fn_params fdef)) as ps_subst.
      destruct (check_args Ω arg_tys ps_subst) as [err |] eqn:Hcheck; try discriminate.
      destruct (forallb (wf_lifetime_b (mk_region_ctx n)) (finalize_subst σ_acc)) eqn:Hwf;
        try discriminate.
      remember (apply_lt_outlives (finalize_subst σ_acc) (fn_outlives fdef)) as Ω_subst.
      destruct (outlives_constraints_hold_b Ω Ω_subst) eqn:Hout; try discriminate.
      inversion Hinfer; subst.
      destruct (lookup_fn_b_sound i (env_fns env) fdef Hlookup) as [Hin Hname].
      eapply TES_Call with (fdef := fdef) (σ := finalize_subst σ_acc).
      * exact Hin.
      * exact Hname.
      * eapply infer_env_args_collect_sound.
        -- exact Hcollect.
        -- intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
           eapply IH.
           ++ eapply struct_exprs_in_true; eassumption.
           ++ exact Hinfer_arg.
        -- exact Hcheck.
      * apply env_outlives_constraints_hold_b_sound. exact Hout.
    + apply andb_true_iff in Hstruct as [Hcallee Hargs].
      destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tcallee Σc] | err]
        eqn:Hcallee_infer; try discriminate.
      rewrite infer_env_args_collect_eq in Hinfer.
      destruct (infer_env_args_collect fuel' env Ω n Σc l) as [[arg_tys Σargs] | err]
        eqn:Hcollect; try discriminate.
      destruct Tcallee as [u c]; simpl in *.
      destruct c; try discriminate.
      * destruct (check_arg_tys Ω arg_tys l0) as [err |] eqn:Hcheck; try discriminate.
        inversion Hinfer; subst.
        eapply TES_CallExpr_Fn.
        -- eapply IH; [exact Hcallee | exact Hcallee_infer].
        -- eapply infer_env_args_collect_sound.
           ++ exact Hcollect.
           ++ intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
              eapply IH.
              ** eapply struct_exprs_in_true; eassumption.
              ** exact Hinfer_arg.
           ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
      * destruct (ty_core t) eqn:Hbody; try discriminate.
        destruct (build_bound_sigma (repeat None n0) arg_tys l0) as [σ |] eqn:Hbuild;
          try discriminate.
        destruct (check_arg_tys Ω arg_tys (map (open_bound_ty σ) l0)) as [err |] eqn:Hcheck;
          try discriminate.
        destruct (contains_lbound_ty (open_bound_ty σ t0) ||
            contains_lbound_outlives (open_bound_outlives σ o)) eqn:Hleak;
          try discriminate.
        destruct (outlives_constraints_hold_b Ω (open_bound_outlives σ o)) eqn:Hout;
          try discriminate.
        inversion Hinfer; subst.
        apply opened_call_no_lbound_sound in Hleak as [Hret Hbounds].
        eapply TES_CallExpr_Forall with (σ := σ) (param_tys := l0).
        -- eapply IH; [exact Hcallee | exact Hcallee_infer].
        -- exact Hbody.
        -- eapply infer_env_args_collect_sound.
           ++ exact Hcollect.
           ++ intros Σ0 e0 T0 Σ1 Hin_arg Hinfer_arg.
              eapply IH.
              ** eapply struct_exprs_in_true; eassumption.
              ** exact Hinfer_arg.
           ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
        -- exact Hret.
        -- exact Hbounds.
        -- apply env_outlives_constraints_hold_b_sound. exact Hout.
    + destruct (lookup_struct s env) as [sdef |] eqn:Hlookup; try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l) (struct_lifetimes sdef))) eqn:Hlts;
        try discriminate.
      destruct (negb (Nat.eqb (Datatypes.length l0) (struct_type_params sdef))) eqn:Hargslen;
        try discriminate.
      destruct (check_struct_bounds env (struct_bounds sdef) l0) as [err |] eqn:Hbounds;
        try discriminate.
      destruct (first_duplicate_field l1) as [dup |] eqn:Hdup; try discriminate.
      destruct (first_unknown_field l1 (struct_fields sdef)) as [unknown |] eqn:Hunknown;
        try discriminate.
      destruct (first_missing_field (struct_fields sdef) l1) as [missing |] eqn:Hmissing;
        try discriminate.
      rewrite infer_env_fields_collect_eq in Hinfer.
      destruct (infer_env_fields_collect fuel' env Ω n l l0 Σ l1 (struct_fields sdef))
        as [Σfields | err] eqn:Hfields; try discriminate.
      inversion Hinfer; subst.
      apply negb_false_iff in Hlts. apply Nat.eqb_eq in Hlts.
      apply negb_false_iff in Hargslen. apply Nat.eqb_eq in Hargslen.
      eapply TES_Struct.
      * exact Hlookup.
      * exact Hlts.
      * exact Hargslen.
      * exact Hbounds.
      * eapply infer_env_fields_collect_sound.
        -- exact Hstruct.
        -- exact Hfields.
        -- intros Σ0 e0 T0 Σ1 Hexpr Hinfer0.
           eapply IH; [exact Hexpr | exact Hinfer0].
    + destruct (infer_place_sctx env Σ p) as [Told | err] eqn:Hplace; try discriminate.
      destruct (place_path p) as [[x path] |] eqn:Hpath.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tnew Σ1] | err]
          eqn:Hnew; try discriminate.
        destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
        destruct (sctx_path_available Σ1 x path) as [[] | err] eqn:Havailable; try discriminate.
        destruct (sctx_restore_path Σ1 x path) as [Σ2 | err] eqn:Hrestore; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Replace_Path.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- exact Hpath.
        -- exact Hmut.
        -- eapply IH; [exact Hstruct | exact Hnew].
        -- exact Hcompat.
        -- exact Havailable.
        -- exact Hrestore.
      * destruct (place_under_unique_ref_b env Σ p) eqn:Hunique; try discriminate.
        destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tnew Σ1] | err]
          eqn:Hnew; try discriminate.
        destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Replace_Indirect.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- exact Hpath.
        -- apply place_under_unique_ref_b_sound. exact Hunique.
        -- eapply IH; [exact Hstruct | exact Hnew].
        -- exact Hcompat.
    + destruct (infer_place_sctx env Σ p) as [Told | err] eqn:Hplace; try discriminate.
      destruct (usage_eqb (ty_usage Told) ULinear) eqn:Hlinear; try discriminate.
      destruct (place_path p) as [[x path] |] eqn:Hpath.
      * destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
        destruct mut; try discriminate.
        destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tnew Σ1] | err]
          eqn:Hnew; try discriminate.
        destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Assign_Path.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Hlinear. simpl in Hlinear. discriminate.
        -- exact Hpath.
        -- exact Hmut.
        -- eapply IH; [exact Hstruct | exact Hnew].
        -- exact Hcompat.
      * destruct (place_under_unique_ref_b env Σ p) eqn:Hunique; try discriminate.
        destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Tnew Σ1] | err]
          eqn:Hnew; try discriminate.
        destruct (ty_compatible_b Ω Tnew Told) eqn:Hcompat; try discriminate.
        inversion Hinfer; subst.
        eapply TES_Assign_Indirect.
        -- eapply infer_place_sctx_structural_sound. exact Hplace.
        -- intro Hu. rewrite Hu in Hlinear. simpl in Hlinear. discriminate.
        -- exact Hpath.
        -- apply place_under_unique_ref_b_sound. exact Hunique.
        -- eapply IH; [exact Hstruct | exact Hnew].
        -- exact Hcompat.
    + destruct (infer_place_sctx env Σ p) as [Tp | err] eqn:Hplace; try discriminate.
      destruct r.
      * inversion Hinfer; subst.
        eapply TES_BorrowShared.
        eapply infer_place_sctx_structural_sound. exact Hplace.
      * destruct (place_path p) as [[x path] |] eqn:Hpath.
        -- destruct (sctx_lookup_mut x Σ) as [mut |] eqn:Hmut; try discriminate.
           destruct mut; try discriminate.
           inversion Hinfer; subst.
           eapply TES_BorrowUnique.
           ++ eapply infer_place_sctx_structural_sound. exact Hplace.
           ++ exact Hpath.
           ++ exact Hmut.
        -- destruct (place_under_unique_ref_b env Σ p) eqn:Hunique; try discriminate.
           inversion Hinfer; subst.
           eapply TES_BorrowUnique_Indirect.
           ++ eapply infer_place_sctx_structural_sound. exact Hplace.
           ++ exact Hpath.
           ++ apply place_under_unique_ref_b_sound. exact Hunique.
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
        -- eapply IH; [exact Hstruct | exact Hr].
        -- apply usage_eqb_true. exact Husage.
    + destruct (infer_core_env_state_fuel fuel' env Ω n Σ e) as [[Te Σe] | err]
        eqn:He; try discriminate.
      inversion Hinfer; subst.
      eapply TES_Drop. eapply IH; [exact Hstruct | exact He].
    + repeat rewrite andb_true_iff in Hstruct.
      destruct Hstruct as [[Hstruct1 Hstruct2] Hstruct3].
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
      * eapply IH; [exact Hstruct1 | exact He1].
      * apply ty_core_eqb_true. exact Hbool.
      * eapply IH; [exact Hstruct2 | exact He2].
      * eapply IH; [exact Hstruct3 | exact He3].
      * apply ty_core_eqb_true. exact Hcore.
      * exact Hmerge.
Qed.
