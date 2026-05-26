From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeRootCheckFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Definition initial_root_runtime_ready_for_fn (f : fn_def) (s : store) : Prop :=
  store_roots_within (initial_root_env_for_fn f) s /\
  store_no_shadow s /\
  root_env_store_roots_named (initial_root_env_for_fn f) s /\
  root_env_store_keys_named (initial_root_env_for_fn f) s.

Fixpoint ident_in_b (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => ident_eqb x y || ident_in_b x ys
  end.

Lemma ident_in_b_true_in :
  forall x xs,
    ident_in_b x xs = true ->
    In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros Hin.
  - discriminate.
  - apply orb_true_iff in Hin as [Heq | Hin].
    + apply ident_eqb_eq in Heq. subst y. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma ident_in_b_false_not_in :
  forall x xs,
    ident_in_b x xs = false ->
    ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros Hnot Hin.
  - contradiction.
  - apply orb_false_iff in Hnot as [Hneq Hnot].
    destruct Hin as [Heq | Hin].
    + subst y. rewrite ident_eqb_refl in Hneq. discriminate.
    + apply (IH Hnot). exact Hin.
Qed.

Fixpoint ident_names_unique_b (xs : list ident) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (ident_in_b x xs') && ident_names_unique_b xs'
  end.

Lemma ident_names_unique_b_nodup :
  forall xs,
    ident_names_unique_b xs = true ->
    NoDup xs.
Proof.
  induction xs as [| x xs IH]; simpl; intros Hunique.
  - constructor.
  - apply andb_true_iff in Hunique as [Hfresh Hrest].
    apply negb_true_iff in Hfresh.
    constructor.
    + apply ident_in_b_false_not_in. exact Hfresh.
    + apply IH. exact Hrest.
Qed.

Definition root_atom_in_b (a : root_atom) (roots : root_set) : bool :=
  existsb (root_atom_eqb a) roots.

Lemma root_atom_in_b_true_in :
  forall a roots,
    root_atom_in_b a roots = true ->
    In a roots.
Proof.
  unfold root_atom_in_b.
  intros a roots H.
  apply existsb_exists in H as [atom [Hin Heq]].
  apply root_atom_eqb_eq in Heq. subst atom.
  exact Hin.
Qed.

Fixpoint root_set_store_roots_named_b
    (roots : root_set) (s : store) : bool :=
  match roots with
  | [] => true
  | RStore z :: rest =>
      ident_in_b z (store_names s) &&
      root_set_store_roots_named_b rest s
  | RParam _ :: rest => root_set_store_roots_named_b rest s
  end.

Lemma root_set_store_roots_named_b_sound :
  forall roots s,
    root_set_store_roots_named_b roots s = true ->
    root_set_store_roots_named roots s.
Proof.
  induction roots as [| atom rest IH]; intros s Hnamed z Hin.
  - inversion Hin.
  - destruct atom as [y | y]; simpl in Hnamed, Hin.
    + apply andb_true_iff in Hnamed as [Hy Hrest].
      destruct Hin as [Hz | Hin].
      * inversion Hz; subst y. apply ident_in_b_true_in. exact Hy.
      * eapply IH; eassumption.
    + destruct Hin as [Hz | Hin].
      * discriminate.
      * eapply IH; eassumption.
Qed.

Fixpoint root_env_store_roots_named_b
    (R : root_env) (s : store) : bool :=
  match R with
  | [] => true
  | (_, roots) :: rest =>
      root_set_store_roots_named_b roots s &&
      root_env_store_roots_named_b rest s
  end.

Lemma root_env_store_roots_named_b_sound :
  forall R s,
    root_env_store_roots_named_b R s = true ->
    root_env_store_roots_named R s.
Proof.
  unfold root_env_store_roots_named.
  induction R as [| [y roots] rest IH]; intros s Hnamed x roots0 z Hlookup Hin.
  - simpl in Hlookup. discriminate.
  - simpl in Hnamed, Hlookup.
    apply andb_true_iff in Hnamed as [Hhead Htail].
    destruct (ident_eqb x y) eqn:Heq.
    + inversion Hlookup; subst roots0.
      eapply root_set_store_roots_named_b_sound; eassumption.
    + eapply IH; eassumption.
Qed.

Fixpoint root_env_store_keys_named_b (R : root_env) (s : store) : bool :=
  match R with
  | [] => true
  | (x, _) :: rest =>
      ident_in_b x (store_names s) &&
      root_env_store_keys_named_b rest s
  end.

Lemma root_env_store_keys_named_b_sound :
  forall R s,
    root_env_store_keys_named_b R s = true ->
    root_env_store_keys_named R s.
Proof.
  unfold root_env_store_keys_named, root_env_keys_named.
  induction R as [| [x roots] rest IH]; intros s Hkeys y Hin.
  - inversion Hin.
  - simpl in Hkeys, Hin.
    apply andb_true_iff in Hkeys as [Hx Hrest].
    destruct Hin as [Hy | Hin].
    + subst y. apply ident_in_b_true_in. exact Hx.
    + eapply IH; eassumption.
Qed.

Definition value_roots_within_leaf_b (roots : root_set) (v : value) : bool :=
  match v with
  | VUnit => true
  | VInt _ => true
  | VFloat _ => true
  | VBool _ => true
  | VStruct _ [] => true
  | VStruct _ (_ :: _) => false
  | VEnum _ _ _ _ [] => true
  | VEnum _ _ _ _ (_ :: _) => false
  | VRef x _ => root_atom_in_b (RStore x) roots
  | VClosure _ captured =>
      match captured with
      | [] => true
      | _ :: _ => false
      end
  end.

Fixpoint value_fields_roots_within_b
    (roots : root_set) (fields : list (string * value)) : bool :=
  match fields with
  | [] => true
  | (_, v) :: rest =>
      value_roots_within_leaf_b roots v &&
      value_fields_roots_within_b roots rest
  end.

Definition value_roots_within_b (roots : root_set) (v : value) : bool :=
  match v with
  | VStruct _ fields => value_fields_roots_within_b roots fields
  | _ => value_roots_within_leaf_b roots v
  end.

Lemma value_roots_within_leaf_b_sound :
  forall roots v,
    value_roots_within_leaf_b roots v = true ->
    value_roots_within roots v.
Proof.
  intros roots v Hwithin.
  destruct v as [| i | f | b | name fields | enum_name variant_name lts args values | x path | fname captured];
    simpl in Hwithin.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct fields as [| field rest]; try discriminate.
    apply VRW_Struct. constructor.
  - destruct values as [| value values]; try discriminate.
    apply VRW_Enum.
    + constructor.
    + intros root Hexclude. constructor.
  - apply VRW_Ref.
    apply root_atom_in_b_true_in. exact Hwithin.
  - destruct captured as [| se captured]; try discriminate.
    apply VRW_ClosureEmpty.
Qed.

Lemma value_fields_roots_within_b_sound :
  forall roots fields,
    value_fields_roots_within_b roots fields = true ->
    value_fields_roots_within roots fields.
Proof.
  induction fields as [| [name v] rest IH]; simpl; intros Hwithin.
  - constructor.
  - apply andb_true_iff in Hwithin as [Hvalue Hrest].
    constructor.
    + apply value_roots_within_leaf_b_sound. exact Hvalue.
    + apply IH. exact Hrest.
Qed.

Lemma value_roots_within_b_sound :
  forall roots v,
    value_roots_within_b roots v = true ->
    value_roots_within roots v.
Proof.
  intros roots v Hwithin.
  destruct v as [| i | f | b | name fields | enum_name variant_name lts args values | x path | fname captured];
    simpl in Hwithin; try (apply value_roots_within_leaf_b_sound; exact Hwithin).
  apply VRW_Struct.
  apply value_fields_roots_within_b_sound. exact Hwithin.
Qed.

Definition store_entry_roots_within_b (R : root_env) (se : store_entry)
    : bool :=
  match root_env_lookup (se_name se) R with
  | Some roots => value_roots_within_b roots (se_val se)
  | None => false
  end.

Lemma store_entry_roots_within_b_sound :
  forall R se,
    store_entry_roots_within_b R se = true ->
    store_entry_roots_within R se.
Proof.
  intros R [sx sT sv sst] Hwithin.
  unfold store_entry_roots_within_b in Hwithin. simpl in Hwithin.
  destruct (root_env_lookup sx R) as [roots |] eqn:Hlookup;
    try discriminate.
  apply SERW_Entry with (roots := roots).
  - exact Hlookup.
  - apply value_roots_within_b_sound. exact Hwithin.
Qed.

Fixpoint store_roots_within_b (R : root_env) (s : store) : bool :=
  match s with
  | [] => true
  | se :: rest =>
      store_entry_roots_within_b R se &&
      store_roots_within_b R rest
  end.

Lemma store_roots_within_b_sound :
  forall R s,
    store_roots_within_b R s = true ->
    store_roots_within R s.
Proof.
  induction s as [| se rest IH]; simpl; intros Hwithin.
  - constructor.
  - apply andb_true_iff in Hwithin as [Hentry Hrest].
    constructor.
    + apply store_entry_roots_within_b_sound. exact Hentry.
    + apply IH. exact Hrest.
Qed.

Definition store_no_shadow_b (s : store) : bool :=
  ident_names_unique_b (store_names s).

Lemma store_no_shadow_b_sound :
  forall s,
    store_no_shadow_b s = true ->
    store_no_shadow s.
Proof.
  intros s Hshadow.
  unfold store_no_shadow_b in Hshadow.
  unfold store_no_shadow.
  apply ident_names_unique_b_nodup. exact Hshadow.
Qed.

Definition check_initial_root_runtime_ready (f : fn_def) (s : store) : bool :=
  let R := initial_root_env_for_fn f in
  store_roots_within_b R s &&
  store_no_shadow_b s &&
  root_env_store_roots_named_b R s &&
  root_env_store_keys_named_b R s.

Lemma check_initial_root_runtime_ready_sound :
  forall f s,
    check_initial_root_runtime_ready f s = true ->
    initial_root_runtime_ready_for_fn f s.
Proof.
  intros f s Hready.
  unfold check_initial_root_runtime_ready in Hready.
  apply andb_true_iff in Hready as [Hready Hkeys].
  apply andb_true_iff in Hready as [Hready Hnamed].
  apply andb_true_iff in Hready as [Hroots Hshadow].
  unfold initial_root_runtime_ready_for_fn.
  repeat split.
  - apply store_roots_within_b_sound. exact Hroots.
  - apply store_no_shadow_b_sound. exact Hshadow.
  - apply root_env_store_roots_named_b_sound. exact Hnamed.
  - apply root_env_store_keys_named_b_sound. exact Hkeys.
Qed.
