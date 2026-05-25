From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma lookup_fn_in_name_readiness :
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

Lemma store_update_state_names_readiness :
  forall s x f s',
    store_update_state x f s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x f s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_state x f rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x f rest' Htail). reflexivity.
Qed.

Lemma store_update_val_names_readiness :
  forall s x v s',
    store_update_val x v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - inversion Hupdate. reflexivity.
  - destruct (store_update_val x v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x v rest' Htail). reflexivity.
Qed.

Lemma store_update_path_names_readiness :
  forall s x path v s',
    store_update_path x path v s = Some s' ->
    store_names s' = store_names s.
Proof.
  induction s as [| se rest IH]; intros x path v s' Hupdate;
    simpl in Hupdate; try discriminate.
  destruct (ident_eqb x (se_name se)) eqn:Heq.
  - destruct (value_update_path (se_val se) path v) as [v' |] eqn:Hvalue;
      try discriminate.
    inversion Hupdate. reflexivity.
  - destruct (store_update_path x path v rest) as [rest' |] eqn:Htail;
      try discriminate.
    inversion Hupdate. simpl. rewrite (IH x path v rest' Htail). reflexivity.
Qed.

Lemma store_restore_path_names_readiness :
  forall s x path s',
    store_restore_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_restore_path.
  intros s x path s' Hrestore.
  eapply store_update_state_names_readiness. exact Hrestore.
Qed.

Lemma store_consume_path_names_readiness :
  forall s x path s',
    store_consume_path x path s = Some s' ->
    store_names s' = store_names s.
Proof.
  unfold store_consume_path.
  intros s x path s' Hconsume.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (binding_available_b (se_state se) path) eqn:Havailable;
    try discriminate.
  eapply store_update_state_names_readiness. exact Hconsume.
Qed.

Lemma store_names_mark_used_readiness :
  forall x s,
    store_names (store_mark_used x s) = store_names s.
Proof.
  intros x s.
  induction s as [| se rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x (se_name se)); simpl; try reflexivity.
  rewrite IH. reflexivity.
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
  | PRE_Enum : forall enum_name variant_name lts args payloads,
      preservation_ready_args payloads ->
      preservation_ready_expr (EEnum enum_name variant_name lts args payloads)
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
    + destruct
        ((fix go (used0 : list ident) (args0 : list expr)
             {struct args0} : list expr * list ident :=
            match args0 with
            | [] => ([], used0)
            | arg :: rest =>
                let (arg', used1) := alpha_rename_expr ρ used0 arg in
                let (rest', used2) := go used1 rest in
                (arg' :: rest', used2)
            end) used payloads)
        as [payloadsr used_payloads] eqn:Hpayloads.
      inversion Hrename; subst.
      apply PRE_Enum.
      eapply alpha_rename_preservation_ready_args; eauto.
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
             param_names (fn_captures f) ++
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
  destruct (lookup_fn_in_name_readiness fname (env_fns env) fdef Hlookup)
    as [Hin _].
  eapply alpha_rename_fn_def_preservation_ready_body.
  - exact Hrename.
  - apply Henv_ready. exact Hin.
Qed.

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

Scheme preservation_ready_eval_ind' := Induction for eval Sort Prop
with preservation_ready_eval_args_ind' := Induction for eval_args Sort Prop
with preservation_ready_eval_struct_fields_ind' :=
  Induction for eval_struct_fields Sort Prop.

Combined Scheme preservation_ready_eval_eval_args_eval_struct_fields_ind
  from preservation_ready_eval_ind',
       preservation_ready_eval_args_ind',
       preservation_ready_eval_struct_fields_ind'.

Theorem preservation_ready_eval_store_names_mutual :
  (forall env s e s' v,
    eval env s e s' v ->
    preservation_ready_expr e ->
    store_names s' = store_names s) /\
  (forall env s args s' vs,
    eval_args env s args s' vs ->
    preservation_ready_args args ->
    store_names s' = store_names s) /\
  (forall env s fields defs s' values,
    eval_struct_fields env s fields defs s' values ->
    preservation_ready_fields fields ->
    store_names s' = store_names s).
Proof.
  assert (Hmut : forall env,
    (forall s e s' v,
      eval env s e s' v ->
      preservation_ready_expr e ->
      store_names s' = store_names s) /\
    (forall s args s' vs,
      eval_args env s args s' vs ->
      preservation_ready_args args ->
      store_names s' = store_names s) /\
    (forall s fields defs s' values,
      eval_struct_fields env s fields defs s' values ->
      preservation_ready_fields fields ->
      store_names s' = store_names s)).
  { intro env.
  apply (preservation_ready_eval_eval_args_eval_struct_fields_ind env
    (fun s e s' v _ =>
      preservation_ready_expr e -> store_names s' = store_names s)
    (fun s args s' vs _ =>
      preservation_ready_args args -> store_names s' = store_names s)
    (fun s fields defs s' values _ =>
      preservation_ready_fields fields -> store_names s' = store_names s)).
  - intros s Hready. reflexivity.
  - intros s lit Hready. reflexivity.
  - intros s lit Hready. reflexivity.
  - intros s lit Hready. reflexivity.
  - intros s x e Hlookup Hconsume Hready. reflexivity.
  - intros s x e Hlookup Hconsume Hused Hready.
    apply store_names_mark_used_readiness.
  - intros s p x path e T v Hplace Hlookup Havailable Hty Hconsume
      Hvalue Hready. reflexivity.
  - intros s s' p x path e T v Hplace Hlookup Havailable Hty Hconsume
      Hvalue Hupdate Hready.
    eapply store_consume_path_names_readiness. exact Hupdate.
  - intros s s' name lts args fields values sdef Hlookup Heval_fields
      IH Hready.
    inversion Hready; subst. apply IH.
    match goal with
    | H : preservation_ready_fields fields |- _ => exact H
    end.
  - intros s s' enum_name variant_name lts args payloads values edef vdef
      Hlookup Hvariant Heval_args IH Hready.
    inversion Hready; subst. apply IH.
    match goal with
    | H : preservation_ready_args payloads |- _ => exact H
    end.
  - intros s s1 s2 m x T e1 e2 v1 v2 Heval1 IH1 Heval2 IH2
      Hready.
    inversion Hready.
  - intros s s' e v Heval IH Hready.
    inversion Hready; subst. apply IH.
    match goal with
    | H : preservation_ready_expr e |- _ => exact H
    end.
  - intros s s1 s2 s3 x old_e e_new v_new Hlookup Heval_new IH
      Hupdate Hrestore Hready.
    inversion Hready; subst.
    rewrite (store_restore_path_names_readiness s2 x [] s3 Hrestore).
    rewrite (store_update_val_names_readiness s1 x v_new s2 Hupdate).
    apply IH.
    match goal with
    | H : preservation_ready_expr e_new |- _ => exact H
    end.
  - intros s s1 s2 x old_e e_new v_new Hlookup Heval_new IH
      Hupdate Hready.
    inversion Hready; subst.
    rewrite (store_update_val_names_readiness s1 x v_new s2 Hupdate).
    apply IH.
    match goal with
    | H : preservation_ready_expr e_new |- _ => exact H
    end.
  - intros s s1 s2 s3 p x path old_v e_new v_new Hplace Hlookup
      Heval_new IH Hupdate Hrestore Hready.
    inversion Hready; subst.
    rewrite (store_restore_path_names_readiness s2 x path s3 Hrestore).
    rewrite (store_update_path_names_readiness s1 x path v_new s2 Hupdate).
    apply IH.
    match goal with
    | H : preservation_ready_expr e_new |- _ => exact H
    end.
  - intros s s1 s2 p x path e_new v_new Hplace Heval_new IH Hupdate
      Hready.
    inversion Hready; subst.
    rewrite (store_update_path_names_readiness s1 x path v_new s2 Hupdate).
    apply IH.
    match goal with
    | H : preservation_ready_expr e_new |- _ => exact H
    end.
  - intros s p x path rk Hplace Hready. reflexivity.
  - intros s r p x path e v T Has_place Hplace Hlookup Hvalue Hty
      Husage Hready. reflexivity.
  - intros s s_r r x path e v T Hnot_place Heval_r IH Hlookup Hvalue
      Hty Husage Hready.
    inversion Hready.
  - intros s fname fdef Hlookup Hcaps Hready. reflexivity.
  - intros s fname captures captured fdef Hlookup Hcopy Hready.
    inversion Hready.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_then IHthen
      Hready.
    inversion Hready; subst.
    rewrite (IHthen ltac:(match goal with
      | H : preservation_ready_expr e2 |- _ => exact H
      end)).
    apply IHcond.
    match goal with
    | H : preservation_ready_expr e1 |- _ => exact H
    end.
  - intros s s1 s2 e1 e2 e3 v Heval_cond IHcond Heval_else IHelse
      Hready.
    inversion Hready; subst.
    rewrite (IHelse ltac:(match goal with
      | H : preservation_ready_expr e3 |- _ => exact H
      end)).
    apply IHcond.
    match goal with
    | H : preservation_ready_expr e1 |- _ => exact H
    end.
	  - intros s s_args s_body fname fdef fcall args vs ret used' Hlookup
	      Hcaps Heval_args IHargs Hrename Heval_body IHbody Hready.
	    inversion Hready.
	  - intros s s_args s_body fname type_args fdef fcall args vs ret used'
	      Hlookup Hcaps Heval_args IHargs Hrename Heval_body IHbody Hready.
	    inversion Hready.
	  - intros s s_fn s_args s_body callee args fname captured fdef fcall
	      vs ret used' Heval_callee IHcallee Hlookup Heval_args IHargs Hrename
	      Heval_body IHbody Hready.
    inversion Hready.
  - intros s Hready. reflexivity.
  - intros s s1 s2 e es v vs Heval_e IHe Heval_args IHargs Hready.
    inversion Hready; subst.
    rewrite (IHargs ltac:(match goal with
      | H : preservation_ready_args es |- _ => exact H
      end)).
    apply IHe.
    match goal with
    | H : preservation_ready_expr e |- _ => exact H
    end.
  - intros s Hready. reflexivity.
  - intros s s1 s2 fields f rest e v values Hlookup Heval_e IHe
      Heval_fields IHfields Hready.
    rewrite (IHfields Hready).
    apply IHe.
    eapply preservation_ready_fields_lookup; eassumption. }
  repeat split; intros env; destruct (Hmut env) as [He [Hargs Hfields]];
    eauto.
Qed.
