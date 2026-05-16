From Facet.TypeSystem Require Import Syntax PathState.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Root provenance summaries                                            *)
(* ------------------------------------------------------------------ *)

Definition root_set := list ident.
Definition root_env := list (ident * root_set).

Fixpoint root_env_names (R : root_env) : list ident :=
  match R with
  | [] => []
  | (x, _) :: rest => x :: root_env_names rest
  end.

Definition root_env_no_shadow (R : root_env) : Prop :=
  NoDup (root_env_names R).

Fixpoint root_set_union (a b : root_set) : root_set :=
  match a with
  | [] => b
  | x :: xs =>
      if existsb (ident_eqb x) b
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
  | [] => [x]
  | (y, roots) :: rest =>
      if ident_eqb x y then roots else root_subst_lookup x rest
  end.

Fixpoint root_set_instantiate (rho : root_subst) (roots : root_set)
    : root_set :=
  match roots with
  | [] => []
  | x :: rest =>
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
  ~ In x roots.

Definition root_env_excludes (x : ident) (R : root_env) : Prop :=
  forall y roots,
    root_env_lookup y R = Some roots ->
    y <> x ->
    roots_exclude x roots.

Fixpoint root_provenance_place_name (p : place) : ident :=
  match p with
  | PVar x => x
  | PDeref q => root_provenance_place_name q
  | PField q _ => root_provenance_place_name q
  end.

Definition root_of_place (p : place) : root_set :=
  match place_path p with
  | Some (x, _) => [x]
  | None => [root_provenance_place_name p]
  end.

Lemma root_set_union_in_r :
  forall x a b,
    In x b ->
    In x (root_set_union a b).
Proof.
  intros x a.
  induction a as [| y ys IH]; intros b Hin; simpl.
  - exact Hin.
  - destruct (existsb (ident_eqb y) b).
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
      destruct (existsb (ident_eqb x) b) eqn:Hexists.
      * apply root_set_union_in_r.
        apply existsb_exists in Hexists.
        destruct Hexists as [z [Hin_z Heq_z]].
        apply ident_eqb_eq in Heq_z. subst z.
        exact Hin_z.
      * simpl. left. reflexivity.
    + destruct (existsb (ident_eqb y) b).
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
  - destruct (existsb (ident_eqb y) b) eqn:Hexists.
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
    root_subst_lookup x (root_subst_of_params ps arg_roots) = [x].
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
