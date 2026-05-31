From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness.
From Facet.TypeSystem Require Export EnvRuntimeInitialRootFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Lemma preservation_ready_expr_b_sound :
  forall e,
    preservation_ready_expr_b e = true ->
    preservation_ready_expr e.
Proof.
  assert (Hsize : forall n e,
    expr_size e < n ->
    preservation_ready_expr_b e = true ->
    preservation_ready_expr e).
  {
    induction n as [| n IH]; intros e Hlt Hready.
    - lia.
    - destruct e; simpl in Hready; try discriminate.
      + constructor.
      + constructor.
      + constructor.
      + constructor.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Place_Direct. exact Hpath.
      + apply PRE_Struct.
        induction l1 as [| [name field] rest IHfields].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hfield Hrest].
          constructor.
          -- apply IH with (e := field).
             ++ pose proof (expr_size_struct_field_lt s l l0
                  ((name, field) :: rest) name field (or_introl eq_refl)).
                lia.
             ++ exact Hfield.
          -- apply IHfields.
             ++ simpl. simpl in Hlt. lia.
             ++ exact Hrest.
      + apply PRE_Enum.
        induction l1 as [| payload rest IHpayloads].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hpayload Hrest].
          constructor.
          -- apply IH with (e := payload).
             ++ pose proof (expr_size_enum_payload_lt s s0 l l0
                  (payload :: rest) payload (or_introl eq_refl)).
                lia.
	             ++ exact Hpayload.
	          -- apply IHpayloads.
	             ++ simpl. simpl in Hlt. lia.
	             ++ exact Hrest.
      + apply andb_true_iff in Hready as [Hscrut Hbranches].
        apply PRE_Match.
        * apply IH with (e := e).
          -- pose proof (expr_size_match_scrutinee_lt e l).
             lia.
          -- exact Hscrut.
        * induction l as [| [[name binders] branch] rest IHbranches].
	          -- constructor.
	          -- simpl in Hbranches.
	             destruct binders as [| binder binders']; try discriminate.
	             apply andb_true_iff in Hbranches as [Hbranch Hrest].
	             constructor.
	             ++ reflexivity.
	             ++ apply IH with (e := branch).
	                ** pose proof (expr_size_match_branch_lt e
	                     ((name, [], branch) :: rest) name [] branch
	                     (or_introl eq_refl)).
	                   lia.
	                ** exact Hbranch.
             ++ apply IHbranches.
                ** simpl. simpl in Hlt. lia.
                ** exact Hrest.
	      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
	        eapply PRE_Replace.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Assign.
        * exact Hpath.
        * apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply PRE_Borrow. exact Hpath.
      + apply PRE_Drop.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + apply andb_true_iff in Hready as [H12 H3].
        apply andb_true_iff in H12 as [H1 H2].
        eapply PRE_If.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
        * apply IH with (e := e3); [simpl in Hlt; lia | exact H3].
  }
  intros e Hready.
  eapply Hsize with (n := S (expr_size e)); [lia | exact Hready].
Qed.

Lemma preservation_ready_args_b_sound :
  forall args,
    preservation_ready_args_b args = true ->
    preservation_ready_args args.
Proof.
  unfold preservation_ready_args_b.
  induction args as [| e rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply preservation_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma preservation_ready_fields_b_sound :
  forall fields,
    preservation_ready_fields_b fields = true ->
    preservation_ready_fields fields.
Proof.
  induction fields as [| [name e] rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply preservation_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma direct_call_ready_expr_b_sound :
  forall e,
    direct_call_ready_expr_b e = true ->
    exists fname args synthetic,
      direct_call_target_expr e = Some (fname, args, synthetic) /\
      preservation_ready_args args /\
      synthetic = ECall fname args.
Proof.
  intros e Hready.
  unfold direct_call_ready_expr_b in Hready.
  destruct (direct_call_target_expr e) as [[[fname args] synthetic] |]
    eqn:Htarget; try discriminate.
  exists fname, args, synthetic.
  split; [reflexivity|].
  split; [apply preservation_ready_args_b_sound; exact Hready|].
  unfold direct_call_target_expr in Htarget.
    destruct e; try discriminate.
  - inversion Htarget. reflexivity.
  - destruct e; try discriminate.
    inversion Htarget. reflexivity.
Qed.

Lemma provenance_ready_expr_b_sound :
  forall e,
    provenance_ready_expr_b e = true ->
    provenance_ready_expr e.
Proof.
  assert (Hsize : forall n e,
    expr_size e < n ->
    provenance_ready_expr_b e = true ->
    provenance_ready_expr e).
  {
    induction n as [| n IH]; intros e Hlt Hready.
    - lia.
    - destruct e; simpl in Hready; try discriminate.
      + constructor.
      + constructor.
      + constructor.
      + apply andb_true_iff in Hready as [H1 H2].
        eapply ProvReady_Let.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
      + apply andb_true_iff in Hready as [H1 H2].
        eapply ProvReady_LetInfer.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
      + constructor.
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Place_Direct. exact Hpath.
      + apply ProvReady_Struct.
        induction l1 as [| [name field] rest IHfields].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hfield Hrest].
          constructor.
          -- apply IH with (e := field).
             ++ pose proof (expr_size_struct_field_lt s l l0
                  ((name, field) :: rest) name field (or_introl eq_refl)).
                lia.
             ++ exact Hfield.
          -- apply IHfields.
             ++ simpl. simpl in Hlt. lia.
             ++ exact Hrest.
      + apply ProvReady_Enum.
        induction l1 as [| payload rest IHpayloads].
        * constructor.
        * simpl in Hready.
          apply andb_true_iff in Hready as [Hpayload Hrest].
          constructor.
          -- apply IH with (e := payload).
             ++ pose proof (expr_size_enum_payload_lt s s0 l l0
                  (payload :: rest) payload (or_introl eq_refl)).
                lia.
	             ++ exact Hpayload.
	          -- apply IHpayloads.
	             ++ simpl. simpl in Hlt. lia.
	             ++ exact Hrest.
      + apply andb_true_iff in Hready as [Hscrut Hbranches].
        apply ProvReady_Match.
        * apply IH with (e := e).
          -- pose proof (expr_size_match_scrutinee_lt e l).
             lia.
          -- exact Hscrut.
        * induction l as [| [[name binders] branch] rest IHbranches].
          -- constructor.
          -- simpl in Hbranches.
             apply andb_true_iff in Hbranches as [Hbranch Hrest].
             constructor.
             ++ apply IH with (e := branch).
                ** pose proof (expr_size_match_branch_lt e
                     ((name, binders, branch) :: rest) name binders branch
                     (or_introl eq_refl)).
                   lia.
                ** exact Hbranch.
             ++ apply IHbranches.
                ** simpl. simpl in Hlt. lia.
                ** exact Hrest.
	      + apply ProvReady_Replace.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + apply ProvReady_Assign.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_Borrow. exact Hpath.
      + destruct e; simpl in Hready; try discriminate.
        destruct (place_path p) as [[x path] |] eqn:Hpath; try discriminate.
        eapply ProvReady_DerefBorrow. exact Hpath.
      + apply ProvReady_Drop.
        apply IH with (e := e); [simpl in Hlt; lia | exact Hready].
      + apply andb_true_iff in Hready as [H12 H3].
        apply andb_true_iff in H12 as [H1 H2].
        eapply ProvReady_If.
        * apply IH with (e := e1); [simpl in Hlt; lia | exact H1].
        * apply IH with (e := e2); [simpl in Hlt; lia | exact H2].
        * apply IH with (e := e3); [simpl in Hlt; lia | exact H3].
  }
  intros e Hready.
  eapply Hsize with (n := S (expr_size e)); [lia | exact Hready].
Qed.

Lemma provenance_ready_args_b_sound :
  forall args,
    provenance_ready_args_b args = true ->
    provenance_ready_args args.
Proof.
  unfold provenance_ready_args_b.
  induction args as [| e rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply provenance_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.

Lemma provenance_ready_fields_b_sound :
  forall fields,
    provenance_ready_fields_b fields = true ->
    provenance_ready_fields fields.
Proof.
  induction fields as [| [name e] rest IH]; simpl; intros Hready.
  - constructor.
  - apply andb_true_iff in Hready as [He Hrest].
    constructor.
    + apply provenance_ready_expr_b_sound. exact He.
    + apply IH. exact Hrest.
Qed.
