From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyFrameScope.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

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
  | ProvReady_Enum : forall enum_name variant_name lts args payloads,
      provenance_ready_args payloads ->
      provenance_ready_expr (EEnum enum_name variant_name lts args payloads)
  | ProvReady_Match : forall scrut branches,
      provenance_ready_expr scrut ->
      provenance_ready_match_branches branches ->
      provenance_ready_expr (EMatch scrut branches)
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
  | ProvReady_Assign : forall p e_new,
      provenance_ready_expr e_new ->
      provenance_ready_expr (EAssign p e_new)
  | ProvReady_Replace : forall p e_new,
      provenance_ready_expr e_new ->
      provenance_ready_expr (EReplace p e_new)
  | ProvReady_If : forall e1 e2 e3,
      provenance_ready_expr e1 ->
      provenance_ready_expr e2 ->
      provenance_ready_expr e3 ->
      provenance_ready_expr (EIf e1 e2 e3)
  | ProvReady_DerefBorrow : forall rk p x path,
      place_path p = Some (x, path) ->
      provenance_ready_expr (EDeref (EBorrow rk p))
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
      provenance_ready_fields ((name, e) :: rest)
with provenance_ready_match_branches : list (string * list ident * expr) -> Prop :=
  | ProvReadyMatchBranches_Nil :
      provenance_ready_match_branches []
  | ProvReadyMatchBranches_Cons : forall name binders e rest,
      provenance_ready_expr e ->
      provenance_ready_match_branches rest ->
      provenance_ready_match_branches ((name, binders, e) :: rest).

Lemma subst_type_params_expr_list_go_map :
  forall type_args args,
    ((fix go (es : list expr) : list expr :=
        match es with
        | [] => []
        | e' :: es' => subst_type_params_expr type_args e' :: go es'
        end) args) = map (subst_type_params_expr type_args) args.
Proof.
  intros type_args args. induction args as [| e args IH]; simpl;
    congruence.
Qed.

Lemma subst_type_params_fields_go_map :
  forall type_args fields,
    ((fix go (fs : list (string * expr)) : list (string * expr) :=
        match fs with
        | [] => []
        | (field, e') :: fs' =>
            (field, subst_type_params_expr type_args e') :: go fs'
        end) fields) =
    map (fun '(name, e) =>
      (name, subst_type_params_expr type_args e)) fields.
Proof.
  intros type_args fields.
  induction fields as [| [name e] fields IH]; simpl; congruence.
Qed.

Lemma subst_type_params_match_branches_go_map :
  forall type_args branches,
    ((fix go (bs : list (string * list ident * expr))
        : list (string * list ident * expr) :=
        match bs with
        | [] => []
        | (name, binders, e') :: bs' =>
            (name, binders, subst_type_params_expr type_args e') :: go bs'
        end) branches) =
    map (fun '(name, binders, e) =>
      (name, binders, subst_type_params_expr type_args e)) branches.
Proof.
  intros type_args branches.
  induction branches as [| [[name binders] e] branches IH]; simpl;
    congruence.
Qed.

Scheme provenance_ready_expr_ind' :=
  Induction for provenance_ready_expr Sort Prop
with provenance_ready_args_ind' :=
  Induction for provenance_ready_args Sort Prop
with provenance_ready_fields_ind' :=
  Induction for provenance_ready_fields Sort Prop
with provenance_ready_match_branches_ind' :=
  Induction for provenance_ready_match_branches Sort Prop.
Combined Scheme provenance_ready_mutind
  from provenance_ready_expr_ind', provenance_ready_args_ind',
       provenance_ready_fields_ind', provenance_ready_match_branches_ind'.

Lemma provenance_ready_subst_type_params_expr_mutual :
  (forall e,
    provenance_ready_expr e ->
    forall type_args,
      provenance_ready_expr (subst_type_params_expr type_args e)) /\
  (forall args,
    provenance_ready_args args ->
    forall type_args,
      provenance_ready_args (map (subst_type_params_expr type_args) args)) /\
  (forall fields,
    provenance_ready_fields fields ->
    forall type_args,
      provenance_ready_fields
        (map (fun '(name, e) =>
          (name, subst_type_params_expr type_args e)) fields)) /\
  (forall branches,
    provenance_ready_match_branches branches ->
    forall type_args,
      provenance_ready_match_branches
        (map (fun '(name, binders, e) =>
          (name, binders, subst_type_params_expr type_args e)) branches)).
Proof.
  apply provenance_ready_mutind; simpl; intros;
    repeat rewrite subst_type_params_expr_list_go_map;
    repeat rewrite subst_type_params_fields_go_map;
    repeat rewrite subst_type_params_match_branches_go_map;
    try constructor; eauto using provenance_ready_expr, provenance_ready_args,
      provenance_ready_fields, provenance_ready_match_branches.
Qed.

Lemma provenance_ready_expr_subst_type_params_expr :
  forall e type_args,
    provenance_ready_expr e ->
    provenance_ready_expr (subst_type_params_expr type_args e).
Proof.
  intros e type_args Hready.
  exact (proj1 provenance_ready_subst_type_params_expr_mutual e Hready type_args).
Qed.

Scheme preservation_ready_expr_ind' :=
  Induction for preservation_ready_expr Sort Prop
with preservation_ready_args_ind' :=
  Induction for preservation_ready_args Sort Prop
with preservation_ready_fields_ind' :=
  Induction for preservation_ready_fields Sort Prop
with preservation_ready_match_branches_ind' :=
  Induction for preservation_ready_match_branches Sort Prop.
Combined Scheme preservation_ready_mutind
  from preservation_ready_expr_ind', preservation_ready_args_ind',
       preservation_ready_fields_ind', preservation_ready_match_branches_ind'.

Lemma preservation_ready_implies_provenance_ready_mutual :
  (forall e,
    preservation_ready_expr e ->
    provenance_ready_expr e) /\
  (forall args,
    preservation_ready_args args ->
    provenance_ready_args args) /\
  (forall fields,
    preservation_ready_fields fields ->
    provenance_ready_fields fields) /\
  (forall branches,
    preservation_ready_match_branches branches ->
    provenance_ready_match_branches branches).
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
  exact (proj1 (proj2 (proj2 preservation_ready_implies_provenance_ready_mutual))).
Qed.

Lemma alpha_rename_provenance_ready_expr :
  forall ρ used e er used',
    alpha_rename_expr ρ used e = (er, used') ->
    provenance_ready_expr e ->
    provenance_ready_expr er
with alpha_rename_provenance_ready_args :
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
    provenance_ready_args args ->
    provenance_ready_args argsr
with alpha_rename_provenance_ready_fields :
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
    provenance_ready_fields fields ->
    provenance_ready_fields fieldsr
with alpha_rename_provenance_ready_match_branches :
  forall ρ used branches branchesr used',
    (fix go (used0 : list ident)
        (branches0 : list (string * list ident * expr))
        {struct branches0} : list (string * list ident * expr) * list ident :=
       match branches0 with
       | [] => ([], used0)
       | (name, binders, e) :: rest =>
           let binder_seed := binders ++ free_vars_expr e ++ used0 in
           let '(binders', ρ_branch, used1) :=
             alpha_rename_idents ρ binder_seed binders in
           let (e', used2) := alpha_rename_expr ρ_branch used1 e in
           let (rest', used3) := go used2 rest in
           ((name, binders', e') :: rest', used3)
       end) used branches = (branchesr, used') ->
    provenance_ready_match_branches branches ->
    provenance_ready_match_branches branchesr.
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
      eapply ProvReady_Place_Direct. exact Hpath.
    + inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_Borrow. exact Hpath.
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
      apply ProvReady_Struct.
      eapply alpha_rename_provenance_ready_fields; eauto.
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
	      apply ProvReady_Enum.
	      eapply alpha_rename_provenance_ready_args; eauto.
    + destruct (alpha_rename_expr ρ used scrut) as [scrutr used_scrut] eqn:Hscrut.
      destruct
        ((fix go (used0 : list ident)
             (branches0 : list (string * list ident * expr))
             {struct branches0} : list (string * list ident * expr) * list ident :=
            match branches0 with
            | [] => ([], used0)
            | (variant_name, binders, e) :: rest =>
                let binder_seed := binders ++ free_vars_expr e ++ used0 in
                let '(binders', ρ_branch, used1') :=
                  alpha_rename_idents ρ binder_seed binders in
                let (e', used2') := alpha_rename_expr ρ_branch used1' e in
                let (rest', used3) := go used2' rest in
                ((variant_name, binders', e') :: rest', used3)
            end) used_scrut branches)
        as [branchesr used_branches] eqn:Hbranches.
      inversion Hrename; subst.
      apply ProvReady_Match.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_match_branches; eauto.
	    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: ρ)
        (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
          x :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      inversion Hrename; subst.
      apply ProvReady_Let.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr
        ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: ρ)
        (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
          x :: free_vars_expr e2 ++ used1) e2)
        as [e2r used2] eqn:He2.
      inversion Hrename; subst.
      apply ProvReady_LetInfer.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e) as [er0 used0] eqn:He.
      inversion Hrename; subst.
      apply ProvReady_Drop.
      eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      apply ProvReady_Assign.
      eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e_new) as [er_new used_new]
        eqn:Hnew.
      inversion Hrename; subst.
      apply ProvReady_Replace.
      eapply alpha_rename_provenance_ready_expr; eauto.
    + destruct (alpha_rename_expr ρ used e1) as [e1r used1] eqn:He1.
      destruct (alpha_rename_expr ρ used1 e2) as [e2r used2] eqn:He2.
      destruct (alpha_rename_expr ρ used2 e3) as [e3r used3] eqn:He3.
      inversion Hrename; subst.
      apply ProvReady_If.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_expr; eauto.
    + simpl in Hrename.
      inversion Hrename; subst.
      destruct (place_path_rename_place_some ρ p x path H)
        as [xr Hpath].
      eapply ProvReady_DerefBorrow. exact Hpath.
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
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_args; eauto.
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
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_fields; eauto.
  - intros ρ used branches branchesr used' Hrename Hready.
    destruct Hready as [| name binders e rest He Hrest]; simpl in Hrename.
    + inversion Hrename; subst. constructor.
    + destruct (alpha_rename_idents ρ (binders ++ free_vars_expr e ++ used)
          binders) as [[bindersr ρ_branch] used1] eqn:Hbinders_ren.
      destruct (alpha_rename_expr ρ_branch used1 e)
        as [er used2] eqn:He_ren.
      destruct
        ((fix go (used0 : list ident)
             (branches0 : list (string * list ident * expr))
             {struct branches0} : list (string * list ident * expr) * list ident :=
            match branches0 with
            | [] => ([], used0)
            | (name0, binders0, e0) :: rest0 =>
                let binder_seed := binders0 ++ free_vars_expr e0 ++ used0 in
                let '(binders0', ρ_branch0, used3) :=
                  alpha_rename_idents ρ binder_seed binders0 in
                let (e', used4) := alpha_rename_expr ρ_branch0 used3 e0 in
                let (rest', used5) := go used4 rest0 in
                ((name0, binders0', e') :: rest', used5)
            end) used2 rest)
        as [restr used3] eqn:Hrest_ren.
      inversion Hrename; subst.
      constructor.
      * eapply alpha_rename_provenance_ready_expr; eauto.
      * eapply alpha_rename_provenance_ready_match_branches; eauto.
Qed.

Lemma alpha_rename_fn_def_provenance_ready_body :
  forall used f fr used',
    alpha_rename_fn_def used f = (fr, used') ->
    provenance_ready_expr (fn_body f) ->
    provenance_ready_expr (fn_body fr).
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
  eapply alpha_rename_provenance_ready_expr; eauto.
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

Lemma provenance_ready_match_branches_lookup :
  forall branches name e,
    provenance_ready_match_branches branches ->
    lookup_expr_branch name branches = Some e ->
    provenance_ready_expr e.
Proof.
  intros branches name e Hready.
  induction Hready as [| bname binders branch rest Hexpr _ IH];
    simpl; intros Hlookup.
  - discriminate.
  - destruct (String.eqb name bname) eqn:Hname.
    + inversion Hlookup; subst. exact Hexpr.
    + apply IH. exact Hlookup.
Qed.

Lemma roots_exclude_root_sets_union :
  forall x roots_list,
    Forall (roots_exclude x) roots_list ->
    roots_exclude x (root_sets_union roots_list).
Proof.
  intros x roots_list Hexclude.
  induction Hexclude as [| roots roots_list Hroot Hrest IH]; simpl.
  - unfold roots_exclude. intros Hin. contradiction.
  - apply roots_exclude_union; assumption.
Qed.

Lemma roots_exclude_root_sets_union_app_repeat_nil :
  forall x roots_list n,
    roots_exclude x (root_sets_union roots_list) ->
    roots_exclude x (root_sets_union (roots_list ++ repeat [] n)).
Proof.
  intros x roots_list n Hexclude.
  unfold roots_exclude in *.
  intros Hin.
  induction roots_list as [| roots rest IH] in n, Hexclude, Hin |- *.
  - simpl in Hin.
    induction n as [| n IHn]; simpl in Hin.
    + exact Hin.
    + apply IHn. exact Hin.
  - simpl in *.
    apply root_set_union_in_inv in Hin.
    destruct Hin as [Hin | Hin].
    + apply Hexclude. apply root_set_union_in_l. exact Hin.
    + apply IH with (n := n).
      * intros Hrest.
        apply Hexclude. apply root_set_union_in_r. exact Hrest.
      * exact Hin.
Qed.

Lemma value_roots_exclude_root_forall2 :
  forall roots_list values x,
    Forall2 value_roots_within roots_list values ->
    Forall (roots_exclude x) roots_list ->
    Forall (value_refs_exclude_root x) values.
Proof.
  intros roots_list values x Hroots Hexclude.
  induction Hroots as [| roots v roots_list values Hroot Hroots IH];
    inversion Hexclude; subst.
  - constructor.
  - constructor.
    + eapply value_roots_exclude_root; eassumption.
    + apply IH. assumption.
Qed.

Lemma store_names_in_store_entry :
  forall s se,
    In se s ->
    In (se_name se) (store_names s).
Proof.
  induction s as [| se_head rest IH]; intros se Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst se_head. left. reflexivity.
    + right. apply IH. exact Hin.
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
