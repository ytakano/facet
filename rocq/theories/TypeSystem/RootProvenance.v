From Facet.TypeSystem Require Import Syntax PathState Renaming TypingRules.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Root provenance summaries                                            *)
(* ------------------------------------------------------------------ *)

Inductive root_atom : Type :=
  | RStore : ident -> root_atom
  | RParam : ident -> root_atom.

Definition root_set := list root_atom.
Definition root_env := list (ident * root_set).

Definition initial_root_env_for_params (ps : list param) : root_env :=
  map (fun p => (param_name p, [RParam (param_name p)])) ps.

Definition initial_root_env_for_fn (f : fn_def) : root_env :=
  initial_root_env_for_params (fn_params f).

Definition root_atom_rename (rho : rename_env) (atom : root_atom)
    : root_atom :=
  match atom with
  | RStore x => RStore (lookup_rename x rho)
  | RParam x => RParam (lookup_rename x rho)
  end.

Fixpoint root_set_rename (rho : rename_env) (roots : root_set)
    : root_set :=
  match roots with
  | [] => []
  | atom :: rest => root_atom_rename rho atom :: root_set_rename rho rest
  end.

Fixpoint root_env_rename (rho : rename_env) (R : root_env)
    : root_env :=
  match R with
  | [] => []
  | (x, roots) :: rest =>
      (lookup_rename x rho, root_set_rename rho roots)
        :: root_env_rename rho rest
  end.

Definition root_atom_eqb (a b : root_atom) : bool :=
  match a, b with
  | RStore x, RStore y => ident_eqb x y
  | RParam x, RParam y => ident_eqb x y
  | _, _ => false
  end.

Lemma root_atom_eqb_eq :
  forall a b,
    root_atom_eqb a b = true ->
    a = b.
Proof.
  intros [x | x] [y | y] Heq; simpl in Heq; try discriminate;
    apply ident_eqb_eq in Heq; subst; reflexivity.
Qed.

Lemma root_atom_eqb_refl :
  forall a,
    root_atom_eqb a a = true.
Proof.
  intros [x | x]; simpl; apply ident_eqb_refl.
Qed.

Fixpoint root_env_names (R : root_env) : list ident :=
  match R with
  | [] => []
  | (x, _) :: rest => x :: root_env_names rest
  end.

Definition root_env_no_shadow (R : root_env) : Prop :=
  NoDup (root_env_names R).

Lemma root_env_rename_cons_initial_root_env_for_params_notin :
  forall x x' rho ps,
    ~ In x (ctx_names (params_ctx ps)) ->
    root_env_rename ((x, x') :: rho) (initial_root_env_for_params ps) =
    root_env_rename rho (initial_root_env_for_params ps).
Proof.
  intros x x' rho ps.
  induction ps as [| p ps IH]; intros Hnotin; simpl.
  - reflexivity.
  - destruct p as [m y T]. simpl in Hnotin.
    assert (Hy : y <> x).
    { intros Heq. apply Hnotin. subst. left. reflexivity. }
    assert (Htail : ~ In x (ctx_names (params_ctx ps))).
    { intros Hin. apply Hnotin. right. exact Hin. }
    simpl. unfold root_atom_rename. simpl.
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. exfalso. apply Hy. exact Hyx.
    + rewrite IH; [reflexivity | exact Htail].
Qed.

Lemma alpha_rename_params_initial_root_env_rename :
  forall rho used ps psr rho' used',
    NoDup (ctx_names (params_ctx ps)) ->
    alpha_rename_params rho used ps = (psr, rho', used') ->
    root_env_rename rho' (initial_root_env_for_params ps) =
    initial_root_env_for_params psr.
Proof.
  intros rho used ps. revert rho used.
  induction ps as [| p ps IH]; intros rho used psr rho' used' Hnodup Hrename.
  - simpl in Hrename. inversion Hrename. reflexivity.
  - destruct p as [m x T]. simpl in Hrename.
    destruct (alpha_rename_params rho (fresh_ident x used :: used) ps)
      as [[ps'' rho''] used''] eqn:Hps.
    inversion Hrename; subst. simpl.
    inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    repeat rewrite ident_eqb_refl.
    rewrite root_env_rename_cons_initial_root_env_for_params_notin.
    + rewrite (IH rho (fresh_ident x used :: used)
        ps'' rho'' used' Hnodup_tail Hps).
      reflexivity.
    + exact Hnotin.
Qed.

Lemma initial_root_env_for_params_names :
  forall ps,
    root_env_names (initial_root_env_for_params ps) =
    ctx_names (params_ctx ps).
Proof.
  induction ps as [| p ps IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma initial_root_env_for_params_no_shadow :
  forall ps,
    NoDup (ctx_names (params_ctx ps)) ->
    root_env_no_shadow (initial_root_env_for_params ps).
Proof.
  intros ps Hnodup.
  unfold root_env_no_shadow.
  rewrite initial_root_env_for_params_names.
  exact Hnodup.
Qed.

Lemma initial_root_env_for_fn_names :
  forall f,
    root_env_names (initial_root_env_for_fn f) =
    ctx_names (params_ctx (fn_params f)).
Proof.
  intros f.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_names.
Qed.

Lemma initial_root_env_for_fn_no_shadow :
  forall f,
    NoDup (ctx_names (params_ctx (fn_params f))) ->
    root_env_no_shadow (initial_root_env_for_fn f).
Proof.
  intros f Hnodup.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_no_shadow.
  exact Hnodup.
Qed.

Lemma root_env_rename_names :
  forall rho R,
    root_env_names (root_env_rename rho R) =
    map (fun x => lookup_rename x rho) (root_env_names R).
Proof.
  intros rho R.
  induction R as [| [x roots] rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition root_set_equiv (a b : root_set) : Prop :=
  forall atom, In atom a <-> In atom b.

Lemma root_set_equiv_refl :
  forall roots,
    root_set_equiv roots roots.
Proof.
  intros roots atom. split; intro H; exact H.
Qed.

Lemma root_set_equiv_sym :
  forall a b,
    root_set_equiv a b ->
    root_set_equiv b a.
Proof.
  intros a b Heq atom.
  destruct (Heq atom) as [Hab Hba].
  split; assumption.
Qed.

Lemma root_set_equiv_trans :
  forall a b c,
    root_set_equiv a b ->
    root_set_equiv b c ->
    root_set_equiv a c.
Proof.
  intros a b c Hab Hbc atom.
  destruct (Hab atom) as [Hab1 Hab2].
  destruct (Hbc atom) as [Hbc1 Hbc2].
  split; intro H.
  - apply Hbc1. apply Hab1. exact H.
  - apply Hab2. apply Hbc2. exact H.
Qed.

Lemma root_set_equiv_cons :
  forall atom a b,
    root_set_equiv a b ->
    root_set_equiv (atom :: a) (atom :: b).
Proof.
  intros atom a b Heq atom0.
  simpl.
  destruct (Heq atom0) as [Hab Hba].
  split; intros Hin.
  - destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + right. apply Hab. exact Hin.
  - destruct Hin as [Hin | Hin].
    + left. exact Hin.
    + right. apply Hba. exact Hin.
Qed.

Lemma root_set_equiv_app :
  forall a a' b b',
    root_set_equiv a a' ->
    root_set_equiv b b' ->
    root_set_equiv (a ++ b) (a' ++ b').
Proof.
  intros a a' b b' Ha Hb atom.
  split; intros Hin.
  - apply in_app_or in Hin.
    apply in_or_app.
    destruct Hin as [Hin | Hin].
    + left. apply Ha. exact Hin.
    + right. apply Hb. exact Hin.
  - apply in_app_or in Hin.
    apply in_or_app.
    destruct Hin as [Hin | Hin].
    + left. apply Ha. exact Hin.
    + right. apply Hb. exact Hin.
Qed.

Lemma root_set_rename_in :
  forall rho atom roots,
    In atom roots ->
    In (root_atom_rename rho atom) (root_set_rename rho roots).
Proof.
  intros rho atom roots.
  induction roots as [| atom0 rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst atom0. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma root_set_rename_in_inv :
  forall rho atom roots,
    In atom (root_set_rename rho roots) ->
    exists atom0,
      In atom0 roots /\
      atom = root_atom_rename rho atom0.
Proof.
  intros rho atom roots.
  induction roots as [| atom0 rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + exists atom0. split.
      * left. reflexivity.
      * symmetry. exact Hin.
    + destruct (IH Hin) as [atom1 [Hin1 Heq]].
      exists atom1. split.
      * right. exact Hin1.
      * exact Heq.
Qed.

Lemma root_set_rename_equiv :
  forall rho roots roots',
    root_set_equiv roots roots' ->
    root_set_equiv
      (root_set_rename rho roots)
      (root_set_rename rho roots').
Proof.
  intros rho roots roots' Heq atom.
  split; intros Hin;
    apply root_set_rename_in_inv in Hin;
    destruct Hin as [atom0 [Hin0 Hatom]]; subst atom.
  - apply root_set_rename_in. apply Heq. exact Hin0.
  - apply root_set_rename_in. apply Heq. exact Hin0.
Qed.

Lemma root_set_rename_app :
  forall rho a b,
    root_set_rename rho (a ++ b) =
    root_set_rename rho a ++ root_set_rename rho b.
Proof.
  intros rho a.
  induction a as [| atom rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition rename_no_collision_for
    (rho : rename_env) (x : ident) (names : list ident) : Prop :=
  forall y,
    In y names ->
    y <> x ->
    lookup_rename y rho <> lookup_rename x rho.

Fixpoint root_set_union (a b : root_set) : root_set :=
  match a with
  | [] => b
  | x :: xs =>
      if existsb (root_atom_eqb x) b
      then root_set_union xs b
      else x :: root_set_union xs b
  end.

Fixpoint root_sets_union (sets : list root_set) : root_set :=
  match sets with
  | [] => []
  | roots :: rest => root_set_union roots (root_sets_union rest)
  end.

Fixpoint root_env_lookup (x : ident) (R : root_env) : option root_set :=
  match R with
  | [] => None
  | (y, roots) :: rest =>
      if ident_eqb x y then Some roots else root_env_lookup x rest
  end.

Definition root_env_add (x : ident) (roots : root_set) (R : root_env)
    : root_env :=
  (x, roots) :: R.

Fixpoint root_env_update (x : ident) (roots : root_set) (R : root_env)
    : root_env :=
  match R with
  | [] => []
  | (y, roots_y) :: rest =>
      if ident_eqb x y
      then (y, roots) :: rest
      else (y, roots_y) :: root_env_update x roots rest
  end.

Fixpoint root_env_remove (x : ident) (R : root_env) : root_env :=
  match R with
  | [] => []
  | (y, roots) :: rest =>
      if ident_eqb x y then rest else (y, roots) :: root_env_remove x rest
  end.

Definition root_subst := list (ident * root_set).

Fixpoint root_subst_lookup (x : ident) (rho : root_subst) : root_set :=
  match rho with
  | [] => [RParam x]
  | (y, roots) :: rest =>
      if ident_eqb x y then roots else root_subst_lookup x rest
  end.

Fixpoint root_set_instantiate (rho : root_subst) (roots : root_set)
    : root_set :=
  match roots with
  | [] => []
  | RStore x :: rest =>
      root_set_union [RStore x] (root_set_instantiate rho rest)
  | RParam x :: rest =>
      root_set_union (root_subst_lookup x rho)
        (root_set_instantiate rho rest)
  end.

Fixpoint root_env_instantiate (rho : root_subst) (R : root_env)
    : root_env :=
  match R with
  | [] => []
  | (x, roots) :: rest =>
      (x, root_set_instantiate rho roots) :: root_env_instantiate rho rest
  end.

Fixpoint root_subst_of_params (ps : list param) (arg_roots : list root_set)
    : root_subst :=
  match ps, arg_roots with
  | p :: ps', roots :: arg_roots' =>
      (param_name p, roots) :: root_subst_of_params ps' arg_roots'
  | _, _ => []
  end.

Definition roots_exclude (x : ident) (roots : root_set) : Prop :=
  ~ In (RStore x) roots.

Definition root_env_excludes (x : ident) (R : root_env) : Prop :=
  forall y roots,
    root_env_lookup y R = Some roots ->
    y <> x ->
    roots_exclude x roots.

Lemma roots_exclude_equiv :
  forall x roots roots',
    root_set_equiv roots roots' ->
    roots_exclude x roots ->
    roots_exclude x roots'.
Proof.
  unfold roots_exclude.
  intros x roots roots' Heq Hexcl Hin.
  apply Hexcl.
  apply Heq. exact Hin.
Qed.

Lemma roots_exclude_rename :
  forall rho x roots,
    (forall y,
      In (RStore y) roots ->
      y <> x ->
      lookup_rename y rho <> lookup_rename x rho) ->
    roots_exclude x roots ->
    roots_exclude (lookup_rename x rho) (root_set_rename rho roots).
Proof.
  unfold roots_exclude.
  intros rho x roots Hnocoll Hexcl Hin.
  apply root_set_rename_in_inv in Hin.
  destruct Hin as [atom [Hin Hatom]].
  destruct atom as [y | y]; simpl in Hatom.
  - inversion Hatom as [Hren].
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      apply Hexcl. exact Hin.
    + apply ident_eqb_neq in Hyx.
      apply (Hnocoll y Hin Hyx). symmetry. exact Hren.
  - discriminate.
Qed.

Fixpoint root_provenance_place_name (p : place) : ident :=
  match p with
  | PVar x => x
  | PDeref q => root_provenance_place_name q
  | PField q _ => root_provenance_place_name q
  end.

Definition root_of_place (p : place) : root_set :=
  match place_path p with
  | Some (x, _) => [RStore x]
  | None => [RStore (root_provenance_place_name p)]
  end.

Lemma root_provenance_place_name_rename_place :
  forall rho p,
    root_provenance_place_name (rename_place rho p) =
    lookup_rename (root_provenance_place_name p) rho.
Proof.
  intros rho p.
  induction p as [x | p IH | p IH f]; simpl.
  - reflexivity.
  - exact IH.
  - exact IH.
Qed.

Lemma place_path_rename_place_some :
  forall rho p x path,
    place_path p = Some (x, path) ->
    place_path (rename_place rho p) = Some (lookup_rename x rho, path).
Proof.
  intros rho p.
  induction p as [y | p IH | p IH f]; intros x path Hpath; simpl in *.
  - inversion Hpath. reflexivity.
  - discriminate.
  - destruct (place_path p) as [[y parent_path] |] eqn:Hparent;
      try discriminate.
    inversion Hpath. subst x path.
    rewrite (IH y parent_path eq_refl).
    reflexivity.
Qed.

Lemma place_path_rename_place_none :
  forall rho p,
    place_path p = None ->
    place_path (rename_place rho p) = None.
Proof.
  intros rho p.
  induction p as [y | p IH | p IH f]; intros Hpath; simpl in *.
  - discriminate.
  - reflexivity.
  - destruct (place_path p) as [[y parent_path] |] eqn:Hparent;
      try discriminate.
    rewrite (IH eq_refl). reflexivity.
Qed.

Lemma root_of_place_rename_place :
  forall rho p,
    root_of_place (rename_place rho p) =
    root_set_rename rho (root_of_place p).
Proof.
  intros rho p.
  unfold root_of_place.
  destruct (place_path p) as [[x path] |] eqn:Hpath.
  - rewrite (place_path_rename_place_some rho p x path Hpath).
    reflexivity.
  - rewrite (place_path_rename_place_none rho p Hpath).
    simpl. rewrite root_provenance_place_name_rename_place.
    reflexivity.
Qed.

Lemma root_set_union_in_r :
  forall x a b,
    In x b ->
    In x (root_set_union a b).
Proof.
  intros x a.
  induction a as [| y ys IH]; intros b Hin; simpl.
  - exact Hin.
  - destruct (existsb (root_atom_eqb y) b).
    + apply IH. exact Hin.
    + simpl. right. apply IH. exact Hin.
Qed.

Lemma root_set_union_in_l :
  forall x a b,
    In x a ->
    In x (root_set_union a b).
Proof.
  intros x a.
  induction a as [| y ys IH]; intros b Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y.
      destruct (existsb (root_atom_eqb x) b) eqn:Hexists.
      * apply root_set_union_in_r.
        apply existsb_exists in Hexists.
        destruct Hexists as [z [Hin_z Heq_z]].
        apply root_atom_eqb_eq in Heq_z. subst z.
        exact Hin_z.
      * simpl. left. reflexivity.
    + destruct (existsb (root_atom_eqb y) b).
      * apply IH. exact Hin.
      * simpl. right. apply IH. exact Hin.
Qed.

Lemma roots_exclude_union :
  forall x a b,
    roots_exclude x a ->
    roots_exclude x b ->
    roots_exclude x (root_set_union a b).
Proof.
  unfold roots_exclude.
  intros x a.
  induction a as [| y ys IH]; intros b Ha Hb Hin; simpl in *.
  - apply Hb. exact Hin.
  - destruct (existsb (root_atom_eqb y) b) eqn:Hexists.
    + eapply IH.
      * intros Hin_y. apply Ha. right. exact Hin_y.
      * exact Hb.
      * exact Hin.
    + simpl in Hin.
      destruct Hin as [Heq | Hin].
      * apply Ha. left. exact Heq.
      * eapply IH.
        -- intros Hin_y. apply Ha. right. exact Hin_y.
        -- exact Hb.
        -- exact Hin.
Qed.

Lemma root_set_union_in_inv :
  forall x a b,
    In x (root_set_union a b) ->
    In x a \/ In x b.
Proof.
  intros x a.
  induction a as [| y ys IH]; intros b Hin; simpl in *.
  - right. exact Hin.
  - destruct (existsb (root_atom_eqb y) b) eqn:Hexists.
    + destruct (IH b Hin) as [Hin_y | Hin_b].
      * left. right. exact Hin_y.
      * right. exact Hin_b.
    + simpl in Hin.
      destruct Hin as [Heq | Hin].
      * left. left. exact Heq.
      * destruct (IH b Hin) as [Hin_y | Hin_b].
        -- left. right. exact Hin_y.
        -- right. exact Hin_b.
Qed.

Lemma root_set_union_equiv_app :
  forall a b,
    root_set_equiv (root_set_union a b) (a ++ b).
Proof.
  intros a b atom. split; intro Hin.
  - apply in_or_app.
    apply root_set_union_in_inv. exact Hin.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply root_set_union_in_l. exact Hin.
    + apply root_set_union_in_r. exact Hin.
Qed.

Lemma root_set_union_equiv :
  forall a a' b b',
    root_set_equiv a a' ->
    root_set_equiv b b' ->
    root_set_equiv (root_set_union a b) (root_set_union a' b').
Proof.
  intros a a' b b' Ha Hb.
  eapply root_set_equiv_trans.
  - apply root_set_union_equiv_app.
  - eapply root_set_equiv_trans.
    + apply root_set_equiv_app; eassumption.
    + apply root_set_equiv_sym. apply root_set_union_equiv_app.
Qed.

Lemma root_set_union_rename_equiv :
  forall rho roots_left roots_right,
    root_set_equiv
      (root_set_rename rho (root_set_union roots_left roots_right))
      (root_set_union (root_set_rename rho roots_left)
        (root_set_rename rho roots_right)).
Proof.
  intros rho roots_left roots_right.
  eapply root_set_equiv_trans.
  - apply root_set_rename_equiv.
    apply root_set_union_equiv_app.
  - rewrite root_set_rename_app.
    apply root_set_equiv_sym. apply root_set_union_equiv_app.
Qed.

Lemma root_sets_union_equiv :
  forall sets sets',
    Forall2 root_set_equiv sets sets' ->
    root_set_equiv (root_sets_union sets) (root_sets_union sets').
Proof.
  intros sets sets' Hsets.
  induction Hsets as [| roots roots' rest rest' Hroots Hrest IH];
    simpl.
  - apply root_set_equiv_refl.
  - apply root_set_union_equiv; assumption.
Qed.

Lemma root_set_instantiate_in :
  forall rho atom root roots,
    In atom roots ->
    In root
      (match atom with
       | RStore x => [RStore x]
       | RParam x => root_subst_lookup x rho
       end) ->
    In root (root_set_instantiate rho roots).
Proof.
  intros rho atom root roots.
  induction roots as [| atom0 rest IH]; intros Hin Hroot; simpl in *.
  - contradiction.
  - destruct Hin as [Hin | Hin].
    + subst atom0.
      destruct atom as [x | x]; simpl.
      * change (In root
          (root_set_union [RStore x] (root_set_instantiate rho rest))).
        apply root_set_union_in_l. exact Hroot.
      * change (In root
          (root_set_union (root_subst_lookup x rho)
            (root_set_instantiate rho rest))).
        apply root_set_union_in_l. exact Hroot.
    + destruct atom0 as [x | x]; simpl.
      * change (In root
          (root_set_union [RStore x] (root_set_instantiate rho rest))).
        apply root_set_union_in_r. apply IH; assumption.
      * change (In root
          (root_set_union (root_subst_lookup x rho)
            (root_set_instantiate rho rest))).
        apply root_set_union_in_r. apply IH; assumption.
Qed.

Lemma root_set_instantiate_in_inv :
  forall rho root roots,
    In root (root_set_instantiate rho roots) ->
    exists atom,
      In atom roots /\
      In root
        (match atom with
         | RStore x => [RStore x]
         | RParam x => root_subst_lookup x rho
         end).
Proof.
  intros rho root roots.
  induction roots as [| atom rest IH]; intros Hin; simpl in *.
  - contradiction.
  - destruct atom as [x | x].
    + change (In root
        (root_set_union [RStore x] (root_set_instantiate rho rest))) in Hin.
      apply root_set_union_in_inv in Hin.
      destruct Hin as [Hin | Hin].
      * exists (RStore x). split.
        -- left. reflexivity.
        -- exact Hin.
      * destruct (IH Hin) as [atom [Hatom Hroot]].
        exists atom. split.
        -- right. exact Hatom.
        -- exact Hroot.
    + change (In root
        (root_set_union (root_subst_lookup x rho)
          (root_set_instantiate rho rest))) in Hin.
      apply root_set_union_in_inv in Hin.
      destruct Hin as [Hin | Hin].
      * exists (RParam x). split.
        -- left. reflexivity.
        -- exact Hin.
      * destruct (IH Hin) as [atom [Hatom Hroot]].
        exists atom. split.
        -- right. exact Hatom.
        -- exact Hroot.
Qed.

Lemma root_set_instantiate_equiv :
  forall rho roots roots',
    root_set_equiv roots roots' ->
    root_set_equiv
      (root_set_instantiate rho roots)
      (root_set_instantiate rho roots').
Proof.
  intros rho roots roots' Heq root.
  split; intros Hin;
    apply root_set_instantiate_in_inv in Hin;
    destruct Hin as [atom [Hatom Hroot]].
  - eapply root_set_instantiate_in.
    + apply Heq. exact Hatom.
    + exact Hroot.
  - eapply root_set_instantiate_in.
    + apply Heq. exact Hatom.
    + exact Hroot.
Qed.

Lemma root_set_instantiate_union_equiv :
  forall rho roots_left roots_right,
    root_set_equiv
      (root_set_instantiate rho (root_set_union roots_left roots_right))
      (root_set_union (root_set_instantiate rho roots_left)
        (root_set_instantiate rho roots_right)).
Proof.
  intros rho roots_left roots_right root.
  split; intros Hin.
  - apply root_set_instantiate_in_inv in Hin.
    destruct Hin as [atom [Hatom Hroot]].
    apply root_set_union_in_inv in Hatom.
    destruct Hatom as [Hatom | Hatom].
    + apply root_set_union_in_l.
      eapply root_set_instantiate_in; eassumption.
    + apply root_set_union_in_r.
      eapply root_set_instantiate_in; eassumption.
  - apply root_set_union_in_inv in Hin.
    destruct Hin as [Hin | Hin];
      apply root_set_instantiate_in_inv in Hin;
      destruct Hin as [atom [Hatom Hroot]];
      eapply root_set_instantiate_in.
    + apply root_set_union_in_l. exact Hatom.
    + exact Hroot.
    + apply root_set_union_in_r. exact Hatom.
    + exact Hroot.
Qed.

Lemma root_sets_instantiate_union_equiv :
  forall rho sets,
    root_set_equiv
      (root_set_instantiate rho (root_sets_union sets))
      (root_sets_union (map (root_set_instantiate rho) sets)).
Proof.
  intros rho sets.
  induction sets as [| roots rest IH]; simpl.
  - apply root_set_equiv_refl.
  - eapply root_set_equiv_trans.
    + apply root_set_instantiate_union_equiv.
    + apply root_set_union_equiv.
      * apply root_set_equiv_refl.
      * exact IH.
Qed.

Lemma root_env_lookup_some_in_names :
  forall x R roots,
    root_env_lookup x R = Some roots ->
    In x (root_env_names R).
Proof.
  intros x R.
  induction R as [| [y roots_y] rest IH]; intros roots Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    left. reflexivity.
  - right. eapply IH. exact Hlookup.
Qed.

Lemma root_env_lookup_rename :
  forall rho R x roots,
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_lookup x R = Some roots ->
    root_env_lookup (lookup_rename x rho) (root_env_rename rho R) =
      Some (root_set_rename rho roots).
Proof.
  intros rho R.
  induction R as [| [y roots_y] rest IH]; intros x roots Hnocoll Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. subst y.
    simpl. rewrite ident_eqb_refl.
    inversion Hlookup. reflexivity.
  - simpl.
    destruct (ident_eqb (lookup_rename x rho) (lookup_rename y rho))
      eqn:Hren.
    + apply ident_eqb_eq in Hren.
      exfalso.
      apply (Hnocoll y).
      * left. reflexivity.
      * intros Heq. subst y. rewrite ident_eqb_refl in Hxy. discriminate.
      * symmetry. exact Hren.
    + apply IH.
      * intros z Hin Hzx.
        apply (Hnocoll z).
        -- right. exact Hin.
        -- exact Hzx.
      * exact Hlookup.
Qed.

Lemma root_env_lookup_rename_none :
  forall rho R x,
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_lookup x R = None ->
    root_env_lookup (lookup_rename x rho) (root_env_rename rho R) = None.
Proof.
  intros rho R.
  induction R as [| [y roots_y] rest IH]; intros x Hnocoll Hlookup;
    simpl in *; try reflexivity.
  destruct (ident_eqb x y) eqn:Hxy; try discriminate.
  simpl.
  destruct (ident_eqb (lookup_rename x rho) (lookup_rename y rho))
    eqn:Hren.
  - apply ident_eqb_eq in Hren.
    exfalso.
    apply (Hnocoll y).
    + left. reflexivity.
    + intros Heq. subst y. rewrite ident_eqb_refl in Hxy. discriminate.
    + symmetry. exact Hren.
  - apply IH.
    + intros z Hin Hzx.
      apply (Hnocoll z).
      * right. exact Hin.
      * exact Hzx.
    + exact Hlookup.
Qed.

Lemma root_env_rename_add :
  forall rho x roots R,
    root_env_rename rho (root_env_add x roots R) =
    root_env_add (lookup_rename x rho) (root_set_rename rho roots)
      (root_env_rename rho R).
Proof.
  reflexivity.
Qed.

Lemma root_env_rename_remove :
  forall rho R x,
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_rename rho (root_env_remove x R) =
    root_env_remove (lookup_rename x rho) (root_env_rename rho R).
Proof.
  intros rho R.
  induction R as [| [y roots_y] rest IH]; intros x Hnocoll;
    simpl; try reflexivity.
  destruct (ident_eqb x y) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. subst y.
    simpl. rewrite ident_eqb_refl. reflexivity.
  - simpl.
    destruct (ident_eqb (lookup_rename x rho) (lookup_rename y rho))
      eqn:Hren.
    + apply ident_eqb_eq in Hren.
      exfalso.
      apply (Hnocoll y).
      * left. reflexivity.
      * intros Heq. subst y. rewrite ident_eqb_refl in Hxy. discriminate.
      * symmetry. exact Hren.
    + rewrite IH.
      * reflexivity.
      * intros z Hin Hzx.
        apply (Hnocoll z).
        -- right. exact Hin.
        -- exact Hzx.
Qed.

Lemma root_env_rename_update :
  forall rho R x roots,
    rename_no_collision_for rho x (root_env_names R) ->
    root_env_rename rho (root_env_update x roots R) =
    root_env_update (lookup_rename x rho) (root_set_rename rho roots)
      (root_env_rename rho R).
Proof.
  intros rho R.
  induction R as [| [y roots_y] rest IH]; intros x roots Hnocoll;
    simpl; try reflexivity.
  destruct (ident_eqb x y) eqn:Hxy.
  - apply ident_eqb_eq in Hxy. subst y.
    simpl. rewrite ident_eqb_refl. reflexivity.
  - simpl.
    destruct (ident_eqb (lookup_rename x rho) (lookup_rename y rho))
      eqn:Hren.
    + apply ident_eqb_eq in Hren.
      exfalso.
      apply (Hnocoll y).
      * left. reflexivity.
      * intros Heq. subst y. rewrite ident_eqb_refl in Hxy. discriminate.
      * symmetry. exact Hren.
    + rewrite IH.
      * reflexivity.
      * intros z Hin Hzx.
        apply (Hnocoll z).
        -- right. exact Hin.
        -- exact Hzx.
Qed.

Lemma root_env_excludes_rename :
  forall rho x R,
    root_env_no_shadow R ->
    rename_no_collision_for rho x (root_env_names R) ->
    (forall y roots z,
      root_env_lookup y R = Some roots ->
      y <> x ->
      In (RStore z) roots ->
      z <> x ->
      lookup_rename z rho <> lookup_rename x rho) ->
    root_env_excludes x R ->
    root_env_excludes (lookup_rename x rho) (root_env_rename rho R).
Proof.
  unfold root_env_excludes.
  intros rho x R Hnodup Henv_nocoll Hroot_nocoll Hexcl.
  induction R as [| [y roots_y] rest IH];
    intros yr roots_r Hlookup Hyrx; simpl in *; try discriminate.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hy_notin Hnodup_tail]; subst.
  destruct (ident_eqb yr (lookup_rename y rho)) eqn:Hyr.
  - apply ident_eqb_eq in Hyr. subst yr.
    inversion Hlookup. subst roots_r.
    destruct (ident_eqb y x) eqn:Hyx.
    + apply ident_eqb_eq in Hyx. subst y.
      exfalso. apply Hyrx. reflexivity.
    + apply ident_eqb_neq in Hyx.
      apply roots_exclude_rename.
      * intros z Hin_z Hzx.
        eapply Hroot_nocoll.
        -- simpl. rewrite ident_eqb_refl. reflexivity.
        -- exact Hyx.
        -- exact Hin_z.
        -- exact Hzx.
      * eapply Hexcl.
        -- simpl. rewrite ident_eqb_refl. reflexivity.
        -- exact Hyx.
  - eapply IH.
    + unfold root_env_no_shadow. exact Hnodup_tail.
    + intros z Hin Hzx.
      apply (Henv_nocoll z).
      * right. exact Hin.
      * exact Hzx.
    + intros y0 roots0 z Hlookup0 Hy0x Hin_z Hzx.
      assert (Hy0_ne_y : y0 <> y).
      { intros Heq. subst y0.
        apply Hy_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup0. }
      eapply Hroot_nocoll.
      * simpl.
        destruct (ident_eqb y0 y) eqn:Hy0y.
        -- apply ident_eqb_eq in Hy0y. contradiction.
        -- rewrite Hy0y. exact Hlookup0.
      * exact Hy0x.
      * exact Hin_z.
      * exact Hzx.
    + intros y0 roots0 Hlookup0 Hy0x.
      assert (Hy0_ne_y : y0 <> y).
      { intros Heq. subst y0.
        apply Hy_notin.
        eapply root_env_lookup_some_in_names. exact Hlookup0. }
      eapply Hexcl.
      * simpl.
        destruct (ident_eqb y0 y) eqn:Hy0y.
        -- apply ident_eqb_eq in Hy0y. contradiction.
        -- rewrite Hy0y. exact Hlookup0.
      * exact Hy0x.
    + exact Hlookup.
    + exact Hyrx.
Qed.

Lemma root_env_lookup_add_eq :
  forall x roots R,
    root_env_lookup x (root_env_add x roots R) = Some roots.
Proof.
  intros x roots R.
  unfold root_env_add. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma root_env_lookup_add_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup x (root_env_add y roots R) = root_env_lookup x R.
Proof.
  intros x y roots R Hneq.
  unfold root_env_add. simpl.
  destruct (ident_eqb x y) eqn:Heq; try reflexivity.
  apply ident_eqb_eq in Heq. contradiction.
Qed.

Lemma root_env_lookup_update_eq :
  forall x roots R old_roots,
    root_env_lookup x R = Some old_roots ->
    root_env_lookup x (root_env_update x roots R) = Some roots.
Proof.
  intros x roots R.
  induction R as [| [y roots_y] rest IH]; intros old_roots Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - simpl. rewrite Heq. reflexivity.
  - simpl. rewrite Heq. eapply IH. exact Hlookup.
Qed.

Lemma root_env_lookup_update_neq :
  forall x y roots R,
    x <> y ->
    root_env_lookup x (root_env_update y roots R) = root_env_lookup x R.
Proof.
  intros x y roots R Hneq.
  induction R as [| [z roots_z] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb y z) eqn:Hy.
  - simpl.
    destruct (ident_eqb x z) eqn:Hx.
    + apply ident_eqb_eq in Hy. apply ident_eqb_eq in Hx. subst.
      contradiction.
    + reflexivity.
  - simpl.
    destruct (ident_eqb x z); try reflexivity.
    exact IH.
Qed.

Lemma root_env_lookup_remove_neq :
  forall x y R,
    x <> y ->
    root_env_lookup x (root_env_remove y R) = root_env_lookup x R.
Proof.
  intros x y R Hneq.
  induction R as [| [z roots] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb y z) eqn:Hy.
  - apply ident_eqb_eq in Hy. subst z.
    simpl.
    destruct (ident_eqb x y) eqn:Hx.
    + apply ident_eqb_eq in Hx. contradiction.
    + reflexivity.
  - simpl.
    destruct (ident_eqb x z); try reflexivity.
    exact IH.
Qed.

Lemma root_subst_lookup_eq :
  forall x roots rho,
    root_subst_lookup x ((x, roots) :: rho) = roots.
Proof.
  intros x roots rho. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma root_subst_lookup_neq :
  forall x y roots rho,
    x <> y ->
    root_subst_lookup x ((y, roots) :: rho) = root_subst_lookup x rho.
Proof.
  intros x y roots rho Hneq. simpl.
  destruct (ident_eqb x y) eqn:Heq; try reflexivity.
  apply ident_eqb_eq in Heq. contradiction.
Qed.

Lemma root_env_lookup_not_in_names :
  forall x R,
    ~ In x (root_env_names R) ->
    root_env_lookup x R = None.
Proof.
  intros x R.
  induction R as [| [y roots] rest IH]; intros Hnotin; simpl in *.
  - reflexivity.
  - destruct (ident_eqb x y) eqn:Heq.
    + apply ident_eqb_eq in Heq. subst y.
      exfalso. apply Hnotin. left. reflexivity.
    + apply IH. intros Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma root_env_lookup_none_not_in_names :
  forall x R,
    root_env_lookup x R = None ->
    ~ In x (root_env_names R).
Proof.
  intros x R.
  induction R as [| [y roots] rest IH]; intros Hlookup Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst y. rewrite ident_eqb_refl in Hlookup. discriminate.
    + destruct (ident_eqb x y); try discriminate.
      eapply IH; eassumption.
Qed.

Lemma root_env_names_update :
  forall x roots R,
    root_env_names (root_env_update x roots R) = root_env_names R.
Proof.
  intros x roots R.
  induction R as [| [y roots_y] rest IH]; simpl; try reflexivity.
  destruct (ident_eqb x y); simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma root_env_no_shadow_update :
  forall x roots R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_update x roots R).
Proof.
  unfold root_env_no_shadow.
  intros x roots R Hnodup.
  rewrite root_env_names_update. exact Hnodup.
Qed.

Lemma root_env_instantiate_names :
  forall rho R,
    root_env_names (root_env_instantiate rho R) = root_env_names R.
Proof.
  intros rho R.
  induction R as [| [x roots] rest IH]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Definition root_env_keys_named (R : root_env) (names : list ident) : Prop :=
  forall x, In x (root_env_names R) -> In x names.

Lemma root_env_keys_named_weaken :
  forall R names names',
    root_env_keys_named R names ->
    (forall x, In x names -> In x names') ->
    root_env_keys_named R names'.
Proof.
  unfold root_env_keys_named.
  intros R names names' Hnamed Hsubset x Hin.
  apply Hsubset. apply Hnamed. exact Hin.
Qed.

Lemma root_env_keys_named_lookup :
  forall x R roots names,
    root_env_lookup x R = Some roots ->
    root_env_keys_named R names ->
    In x names.
Proof.
  intros x R roots names Hlookup Hnamed.
  apply Hnamed.
  eapply root_env_lookup_some_in_names. exact Hlookup.
Qed.

Lemma root_env_keys_named_add :
  forall x roots R names,
    In x names ->
    root_env_keys_named R names ->
    root_env_keys_named (root_env_add x roots R) names.
Proof.
  unfold root_env_keys_named, root_env_add.
  intros x roots R names Hx Hnamed y Hin.
  simpl in Hin.
  destruct Hin as [Hy | Hin].
  - subst y. exact Hx.
  - apply Hnamed. exact Hin.
Qed.

Lemma root_env_keys_named_remove :
  forall x R names,
    root_env_keys_named R names ->
    root_env_keys_named (root_env_remove x R) names.
Proof.
  unfold root_env_keys_named.
  intros x R.
  induction R as [| [y roots] rest IH]; intros names Hnamed z Hin;
    simpl in *; try contradiction.
  destruct (ident_eqb x y) eqn:Hxy.
  - apply Hnamed. right. exact Hin.
  - simpl in Hin.
    destruct Hin as [Hz | Hin].
    + subst z. apply Hnamed. left. reflexivity.
    + apply IH.
      * intros w Hw. apply Hnamed. right. exact Hw.
      * exact Hin.
Qed.

Lemma root_env_keys_named_update :
  forall x roots R names,
    root_env_keys_named R names ->
    root_env_keys_named (root_env_update x roots R) names.
Proof.
  unfold root_env_keys_named.
  intros x roots R names Hnamed y Hin.
  rewrite root_env_names_update in Hin.
  apply Hnamed. exact Hin.
Qed.

Lemma root_env_keys_named_rename :
  forall rho R names names',
    root_env_keys_named R names ->
    (forall x, In x names -> In (lookup_rename x rho) names') ->
    root_env_keys_named (root_env_rename rho R) names'.
Proof.
  unfold root_env_keys_named.
  intros rho R names names' Hnamed Hrename x Hin.
  rewrite root_env_rename_names in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [y [Heq Hy]].
  subst x.
  apply Hrename. apply Hnamed. exact Hy.
Qed.

Lemma root_env_keys_named_instantiate :
  forall rho R names,
    root_env_keys_named R names ->
    root_env_keys_named (root_env_instantiate rho R) names.
Proof.
  unfold root_env_keys_named.
  intros rho R names Hnamed x Hin.
  rewrite root_env_instantiate_names in Hin.
  apply Hnamed. exact Hin.
Qed.

Lemma initial_root_env_for_params_keys_named :
  forall ps,
    root_env_keys_named
      (initial_root_env_for_params ps)
      (ctx_names (params_ctx ps)).
Proof.
  unfold root_env_keys_named.
  intros ps x Hin.
  rewrite initial_root_env_for_params_names in Hin.
  exact Hin.
Qed.

Lemma initial_root_env_for_fn_keys_named :
  forall f,
    root_env_keys_named
      (initial_root_env_for_fn f)
      (ctx_names (params_ctx (fn_params f))).
Proof.
  intros f.
  unfold initial_root_env_for_fn.
  apply initial_root_env_for_params_keys_named.
Qed.

Lemma root_env_instantiate_no_shadow :
  forall rho R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_instantiate rho R).
Proof.
  unfold root_env_no_shadow.
  intros rho R Hnodup.
  rewrite root_env_instantiate_names. exact Hnodup.
Qed.

Lemma root_env_lookup_instantiate :
  forall x rho R roots,
    root_env_lookup x R = Some roots ->
    root_env_lookup x (root_env_instantiate rho R) =
      Some (root_set_instantiate rho roots).
Proof.
  intros x rho R.
  induction R as [| [y roots_y] rest IH]; intros roots Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Heq.
  - inversion Hlookup. reflexivity.
  - eapply IH. exact Hlookup.
Qed.

Lemma root_env_lookup_instantiate_none :
  forall x rho R,
    root_env_lookup x R = None ->
    root_env_lookup x (root_env_instantiate rho R) = None.
Proof.
  intros x rho R.
  induction R as [| [y roots_y] rest IH]; intros Hlookup;
    simpl in *; try reflexivity.
  destruct (ident_eqb x y) eqn:Heq; try discriminate.
  apply IH. exact Hlookup.
Qed.

Lemma root_env_lookup_instantiate_inv :
  forall x rho R roots_inst,
    root_env_lookup x (root_env_instantiate rho R) = Some roots_inst ->
    exists roots,
      root_env_lookup x R = Some roots /\
      roots_inst = root_set_instantiate rho roots.
Proof.
  intros x rho R.
  induction R as [| [y roots_y] rest IH]; intros roots_inst Hlookup;
    simpl in *; try discriminate.
  destruct (ident_eqb x y) eqn:Hxy.
  - inversion Hlookup. subst roots_inst.
    exists roots_y. split.
    + reflexivity.
    + reflexivity.
  - destruct (IH roots_inst Hlookup) as [roots [Horig Heq]].
    exists roots. split.
    + exact Horig.
    + exact Heq.
Qed.

Lemma root_subst_lookup_excludes :
  forall x y rho,
    (forall param roots,
      In (param, roots) rho ->
      roots_exclude x roots) ->
    roots_exclude x (root_subst_lookup y rho).
Proof.
  unfold roots_exclude.
  intros x y rho Himages.
  induction rho as [| [param roots] rest IH]; simpl.
  - intros Hin. destruct Hin as [Hin | Hin]; try discriminate.
    contradiction.
  - destruct (ident_eqb y param) eqn:Hy.
    + exact (Himages param roots (or_introl eq_refl)).
    + apply IH. intros param' roots' Hin.
      exact (Himages param' roots' (or_intror Hin)).
Qed.

Lemma root_set_instantiate_excludes :
  forall x rho roots,
    roots_exclude x roots ->
    (forall param roots_image,
      In (param, roots_image) rho ->
      roots_exclude x roots_image) ->
    roots_exclude x (root_set_instantiate rho roots).
Proof.
  intros x rho roots.
  induction roots as [| atom rest IH]; intros Hroots Himages; simpl in *.
  - unfold roots_exclude. intros Hin. contradiction.
  - destruct atom as [store_x | param_x].
    + change (roots_exclude x
        (root_set_union [RStore store_x]
          (root_set_instantiate rho rest))).
      apply roots_exclude_union.
      * unfold roots_exclude. intros Hstore.
        destruct Hstore as [Hstore | Hstore]; try contradiction.
        apply Hroots. left. exact Hstore.
      * apply IH.
        -- intros Hbad. apply Hroots. right. exact Hbad.
        -- exact Himages.
    + change (roots_exclude x
        (root_set_union (root_subst_lookup param_x rho)
          (root_set_instantiate rho rest))).
      apply roots_exclude_union.
      * apply root_subst_lookup_excludes. exact Himages.
      * apply IH.
        -- intros Hbad. apply Hroots. right. exact Hbad.
        -- exact Himages.
Qed.

Lemma root_env_instantiate_excludes :
  forall x rho R,
    root_env_excludes x R ->
    (forall param roots_image,
      In (param, roots_image) rho ->
      roots_exclude x roots_image) ->
    root_env_excludes x (root_env_instantiate rho R).
Proof.
  unfold root_env_excludes.
  intros x rho R Hexcl Himages y roots_inst Hlookup Hyx.
  destruct (root_env_lookup_instantiate_inv y rho R roots_inst Hlookup)
    as [roots [Hlookup_orig Heq]].
  subst roots_inst.
  apply root_set_instantiate_excludes.
  - eapply Hexcl; eassumption.
  - exact Himages.
Qed.

Lemma root_env_no_shadow_add :
  forall x roots R,
    root_env_no_shadow R ->
    root_env_lookup x R = None ->
    root_env_no_shadow (root_env_add x roots R).
Proof.
  unfold root_env_no_shadow, root_env_add.
  intros x roots R Hnodup Hlookup.
  simpl. constructor.
  - eapply root_env_lookup_none_not_in_names. exact Hlookup.
  - exact Hnodup.
Qed.

Lemma root_env_no_shadow_remove :
  forall x R,
    root_env_no_shadow R ->
    root_env_no_shadow (root_env_remove x R).
Proof.
  unfold root_env_no_shadow.
  intros x R.
  induction R as [| [y roots] rest IH]; intros Hnodup; simpl in *.
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    destruct (ident_eqb x y).
    + exact Hnodup_tail.
    + simpl. constructor.
      * intros Hin. apply Hnotin.
        clear -Hin.
        induction rest as [| [z roots_z] rest IHrest]; simpl in *.
        -- contradiction.
        -- destruct (ident_eqb x z) eqn:Heq.
           ++ apply ident_eqb_eq in Heq. subst z.
              right. exact Hin.
           ++ destruct Hin as [Hin | Hin].
              ** left. exact Hin.
              ** right. apply IHrest. exact Hin.
      * apply IH. exact Hnodup_tail.
Qed.

Lemma root_env_lookup_remove_eq_no_shadow :
  forall x R,
    root_env_no_shadow R ->
    root_env_lookup x (root_env_remove x R) = None.
Proof.
  intros x R Hnodup.
  induction R as [| [y roots] rest IH]; simpl; try reflexivity.
  unfold root_env_no_shadow in Hnodup.
  simpl in Hnodup.
  inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
  destruct (ident_eqb x y) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst y.
    apply root_env_lookup_not_in_names. exact Hnotin.
  - simpl. rewrite Heq.
    apply IH.
    unfold root_env_no_shadow. exact Hnodup_tail.
Qed.

Lemma root_subst_of_params_lookup_head :
  forall p ps roots arg_roots,
    root_subst_lookup (param_name p)
      (root_subst_of_params (p :: ps) (roots :: arg_roots)) = roots.
Proof.
  intros p ps roots arg_roots. simpl.
  rewrite ident_eqb_refl. reflexivity.
Qed.

Lemma root_subst_of_params_lookup_not_in :
  forall ps arg_roots x,
    (forall p, In p ps -> param_name p <> x) ->
    root_subst_lookup x (root_subst_of_params ps arg_roots) = [RParam x].
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros arg_roots x Hnotin;
    destruct arg_roots as [| roots arg_roots]; simpl; try reflexivity.
  destruct (ident_eqb x (param_name p)) eqn:Heq.
  - apply ident_eqb_eq in Heq. subst x.
    exfalso. apply (Hnotin p); simpl; auto.
  - apply IH. intros q Hinq.
    apply Hnotin. simpl. right. exact Hinq.
Qed.

Lemma root_subst_of_params_lookup_tail_neq :
  forall p ps roots arg_roots x,
    x <> param_name p ->
    root_subst_lookup x
      (root_subst_of_params (p :: ps) (roots :: arg_roots)) =
    root_subst_lookup x (root_subst_of_params ps arg_roots).
Proof.
  intros p ps roots arg_roots x Hneq. simpl.
  destruct (ident_eqb x (param_name p)) eqn:Heq; try reflexivity.
  apply ident_eqb_eq in Heq. contradiction.
Qed.

Lemma root_subst_of_params_image_excludes :
  forall ps arg_roots x param roots,
    Forall (roots_exclude x) arg_roots ->
    In (param, roots) (root_subst_of_params ps arg_roots) ->
    roots_exclude x roots.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros arg_roots x param roots Hforall Hin;
    destruct arg_roots as [| roots_head arg_roots]; simpl in *;
    try contradiction.
  inversion Hforall as [| ? ? Hhead Htail]; subst.
  destruct Hin as [Hin | Hin].
  - inversion Hin. subst. exact Hhead.
  - eapply IH; eassumption.
Qed.

Lemma root_subst_of_params_lookup_excludes :
  forall ps arg_roots x y,
    Forall (roots_exclude x) arg_roots ->
    roots_exclude x
      (root_subst_lookup y (root_subst_of_params ps arg_roots)).
Proof.
  intros ps arg_roots x y Hforall.
  apply root_subst_lookup_excludes.
  intros param roots Hin.
  eapply root_subst_of_params_image_excludes; eassumption.
Qed.
