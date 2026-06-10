From Facet.TypeSystem Require Import Lifetime Types Syntax Program TypingRules CheckerBase.
From Stdlib Require Import List String Bool Lia PeanoNat.
Import ListNotations.

Module CompatBoolSoundness.

Lemma usage_sub_bool_sound : forall u1 u2,
  usage_sub_bool u1 u2 = true -> usage_sub u1 u2.
Proof.
  intros u1 u2 H.
  destruct u1, u2; simpl in H; try discriminate; constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: ref_kind_eqb, ty_eqb, ty_core_eqb correctness             *)
(* ------------------------------------------------------------------ *)

Lemma ref_kind_eqb_true : forall k1 k2,
  ref_kind_eqb k1 k2 = true -> k1 = k2.
Proof.
  destruct k1, k2; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma lifetime_pair_eqb_true : forall p1 p2,
  lifetime_pair_eqb p1 p2 = true -> p1 = p2.
Proof.
  intros [a1 b1] [a2 b2] H. unfold lifetime_pair_eqb in H. simpl in H.
  apply andb_true_iff in H as [Ha Hb].
  apply lifetime_eqb_eq in Ha. apply lifetime_eqb_eq in Hb. subst.
  reflexivity.
Qed.

Lemma outlives_ctx_eqb_true : forall Ω1 Ω2,
  outlives_ctx_eqb Ω1 Ω2 = true -> Ω1 = Ω2.
Proof.
  induction Ω1 as [|p1 Ω1 IH]; intros Ω2 H.
  - destruct Ω2; simpl in H; try discriminate; reflexivity.
  - destruct Ω2 as [|p2 Ω2]; simpl in H; try discriminate.
    apply andb_true_iff in H as [Hp HΩ].
    apply lifetime_pair_eqb_true in Hp. subst p2.
    f_equal. apply IH. exact HΩ.
Qed.

Lemma lifetime_list_eqb_true : forall l1 l2,
  lifetime_list_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|lt1 l1 IH]; intros l2 H.
  - destruct l2; simpl in H; try discriminate; reflexivity.
  - destruct l2 as [|lt2 l2]; simpl in H; try discriminate.
    apply andb_true_iff in H as [Hlt Hrest].
    apply lifetime_eqb_eq in Hlt. subst lt2.
    f_equal. apply IH. exact Hrest.
Qed.

Lemma ty_depth_fn_arg_lt : forall u ts r t,
  In t ts -> ty_depth t < ty_depth (MkTy u (TFn ts r)).
Proof.
  intros u ts. induction ts as [| t1 ts' IH]; intros r t Hin.
  - contradiction.
  - simpl. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH r t Hin). simpl in IH. lia.
Qed.

Lemma ty_depth_fn_ret_lt : forall u ts r,
  ty_depth r < ty_depth (MkTy u (TFn ts r)).
Proof.
  intros u ts. induction ts as [| t1 ts' IH]; intros r.
  - simpl. lia.
  - simpl. specialize (IH r). simpl in IH. lia.
Qed.

Lemma ty_depth_fn_cons_lt : forall u t ts r,
  ty_depth (MkTy u (TFn ts r)) < ty_depth (MkTy u (TFn (t :: ts) r)).
Proof.
  intros u t ts. induction ts as [| t1 ts' IH]; intros r; simpl; lia.
Qed.

Lemma ty_depth_closure_arg_lt : forall u l ts r t,
  In t ts -> ty_depth t < ty_depth (MkTy u (TClosure l ts r)).
Proof.
  intros u l ts. induction ts as [| t1 ts' IH]; intros r t Hin.
  - contradiction.
  - simpl. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH r t Hin). simpl in IH. lia.
Qed.

Lemma ty_depth_closure_ret_lt : forall u l ts r,
  ty_depth r < ty_depth (MkTy u (TClosure l ts r)).
Proof.
  intros u l ts. induction ts as [| t1 ts' IH]; intros r.
  - simpl. lia.
  - simpl. specialize (IH r). simpl in IH. lia.
Qed.

Lemma ty_depth_closure_cons_lt : forall u l t ts r,
  ty_depth (MkTy u (TClosure l ts r)) <
  ty_depth (MkTy u (TClosure l (t :: ts) r)).
Proof.
  intros u l t ts. induction ts as [| t1 ts' IH]; intros r; simpl; lia.
Qed.

Lemma ty_depth_forall_body_lt : forall u n Ω body,
  ty_depth body < ty_depth (MkTy u (TForall n Ω body)).
Proof.
  intros. simpl. lia.
Qed.

Lemma ty_depth_type_forall_body_lt : forall u n bounds body,
  ty_depth body < ty_depth (MkTy u (TTypeForall n bounds body)).
Proof.
  intros. simpl. lia.
Qed.

Lemma ty_eqb_true : forall T1 T2,
  ty_eqb T1 T2 = true -> T1 = T2.
Proof.
  assert (Hsize : forall n T1 T2,
      ty_depth T1 < n ->
      ty_eqb T1 T2 = true -> T1 = T2).
  {
    induction n as [| n IH]; intros T1 T2 Hlt H.
    - destruct T1 as [? c]; destruct c; simpl in Hlt; lia.
    - destruct T1 as [u1 c1], T2 as [u2 c2].
      simpl in H. apply andb_true_iff in H as [Hu Hc].
      assert (Hequ : u1 = u2) by
        (destruct u1, u2; simpl in Hu; try discriminate; reflexivity).
      subst u2.
      f_equal.
	      destruct c1 as [| | | | s1 | i1 | name1 lts1 args1 | name1 lts1 args1
                     | ts1 r1 | lc1 cts1 cr1 | n1 Ω1 b1 | tn1 bs1 tb1
                     | for1 trait1 assoc_args1 assoc1 | l1 k1 t1],
               c2 as [| | | | s2 | i2 | name2 lts2 args2 | name2 lts2 args2
                     | ts2 r2 | lc2 cts2 cr2 | n2 Ω2 b2 | tn2 bs2 tb2
                     | for2 trait2 assoc_args2 assoc2 | l2 k2 t2];
        simpl in Hc; try discriminate.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + apply String.eqb_eq in Hc. subst. reflexivity.
      + apply Nat.eqb_eq in Hc. subst. reflexivity.
      + apply andb_true_iff in Hc as [Hname_lts Hargs].
        apply andb_true_iff in Hname_lts as [Hname Hlts].
        apply String.eqb_eq in Hname. subst name2.
        apply lifetime_list_eqb_true in Hlts. subst lts2.
        f_equal.
        revert args2 Hlt Hargs.
        induction args1 as [| t1 args1' IHargs]; intros args2 Hlt Hargs.
        * destruct args2; [reflexivity | discriminate].
        * destruct args2 as [| t2 args2']; [discriminate |].
          simpl in Hargs. apply andb_true_iff in Hargs as [Ht Htail].
          f_equal.
	          { apply IH; [simpl in Hlt; lia | exact Ht]. }
	          { apply IHargs; [simpl in *; lia | exact Htail]. }
	      + apply andb_true_iff in Hc as [Hname_lts Hargs].
	        apply andb_true_iff in Hname_lts as [Hname Hlts].
	        apply String.eqb_eq in Hname. subst name2.
	        apply lifetime_list_eqb_true in Hlts. subst lts2.
	        f_equal.
	        revert args2 Hlt Hargs.
	        induction args1 as [| t1 args1' IHargs]; intros args2 Hlt Hargs.
	        * destruct args2; [reflexivity | discriminate].
	        * destruct args2 as [| t2 args2']; [discriminate |].
	          simpl in Hargs. apply andb_true_iff in Hargs as [Ht Htail].
	          f_equal.
	          { apply IH; [simpl in Hlt; lia | exact Ht]. }
	          { apply IHargs; [simpl in *; lia | exact Htail]. }
	      + apply andb_true_iff in Hc as [Hlist Hr].
        assert (Heqr : r1 = r2) by
          (apply IH; [pose proof (ty_depth_fn_ret_lt u1 ts1 r1); lia | exact Hr]).
        subst r2. f_equal.
        revert ts2 Hlt Hlist.
        induction ts1 as [| t1 ts1' IHts]; intros ts2 Hlt Hlist.
        * destruct ts2; [reflexivity | discriminate].
        * destruct ts2 as [| t2 ts2']; [discriminate |].
          simpl in Hlist. apply andb_true_iff in Hlist as [Ht Hts].
          f_equal.
          { apply IH;
            [pose proof (ty_depth_fn_arg_lt u1 (t1::ts1') r1 t1 (or_introl eq_refl)); lia
            | exact Ht]. }
          { apply IHts;
            [ exact (Nat.lt_trans _ _ _ (ty_depth_fn_cons_lt u1 t1 ts1' r1) Hlt)
            | exact Hts]. }
      + apply andb_true_iff in Hc as [Henv_list Hr].
        apply andb_true_iff in Henv_list as [Henv Hlist].
        apply lifetime_eqb_eq in Henv. subst lc2.
        assert (Heqr : cr1 = cr2) by
          (apply IH; [pose proof (ty_depth_closure_ret_lt u1 lc1 cts1 cr1); lia | exact Hr]).
        subst cr2. f_equal.
        revert cts2 Hlt Hlist.
        induction cts1 as [| t1 cts1' IHts]; intros cts2 Hlt Hlist.
        * destruct cts2; [reflexivity | discriminate].
        * destruct cts2 as [| t2 cts2']; [discriminate |].
          simpl in Hlist. apply andb_true_iff in Hlist as [Ht Hts].
          f_equal.
          { apply IH;
            [pose proof (ty_depth_closure_arg_lt u1 lc1 (t1::cts1') cr1 t1 (or_introl eq_refl)); lia
            | exact Ht]. }
          { apply IHts;
            [ exact (Nat.lt_trans _ _ _ (ty_depth_closure_cons_lt u1 lc1 t1 cts1' cr1) Hlt)
            | exact Hts]. }
      + apply andb_true_iff in Hc as [Hlk Ht].
        apply andb_true_iff in Hlk as [Hn HΩ].
        apply Nat.eqb_eq in Hn. subst n2.
        apply outlives_ctx_eqb_true in HΩ. subst Ω2.
        f_equal. apply IH;
          [pose proof (ty_depth_forall_body_lt u1 n1 Ω1 b1); lia | exact Ht].
      + apply andb_true_iff in Hc as [Hlk Ht].
        apply andb_true_iff in Hlk as [Hn _Hbounds].
        apply Nat.eqb_eq in Hn. subst tn2.
        assert (Hbs : bs1 = bs2).
        { revert bs2 _Hbounds Hlt.
          induction bs1 as [| [idx1 refs1] bs1' IHbs];
            intros bs2 Hbounds Hdepth;
            destruct bs2 as [| [idx2 refs2] bs2']; simpl in Hbounds;
            try discriminate; try reflexivity.
          apply andb_true_iff in Hbounds as [Hhead Htail].
          apply andb_true_iff in Hhead as [Hidx Hrefs].
          apply Nat.eqb_eq in Hidx. subst idx2.
          assert (Hrefs_eq : refs1 = refs2).
          { revert refs2 Hrefs Hdepth.
            induction refs1 as [| [name1 args1] refs1' IHrefs];
              intros refs2 Hrefs Hdepth;
              destruct refs2 as [| [name2 args2] refs2']; simpl in Hrefs;
              try discriminate; try reflexivity.
            apply andb_true_iff in Hrefs as [Hhead Htail_refs].
            apply andb_true_iff in Hhead as [Hname Hargs].
            apply String.eqb_eq in Hname. subst name2.
            assert (Hargs_eq : args1 = args2).
            { revert args2 Hargs Hdepth.
              induction args1 as [| a1 args1' IHargs];
                intros args2 Hargs Hdepth.
              * destruct args2; simpl in Hargs; [reflexivity | discriminate].
              * destruct args2 as [| a2 args2']; simpl in Hargs; [discriminate |].
                apply andb_true_iff in Hargs as [Ha Htail_args].
                f_equal.
                -- apply IH; [simpl in Hdepth; lia | exact Ha].
                -- apply IHargs; [exact Htail_args | simpl in Hdepth; simpl; lia]. }
            assert (Hrefs_tail : refs1' = refs2').
            { apply IHrefs; [exact Htail_refs | simpl in Hdepth; simpl; lia]. }
            subst. reflexivity. }
          assert (Hbs_tail : bs1' = bs2').
          { apply IHbs; [exact Htail | simpl in Hdepth; simpl; lia]. }
          subst. reflexivity. }
        subst bs2.
        f_equal.
        apply IH;
          [pose proof (ty_depth_type_forall_body_lt u1 tn1 bs1 tb1); lia | exact Ht].
      + apply andb_true_iff in Hc as [Hleft Hassoc].
        apply andb_true_iff in Hleft as [Hleft Hargs].
        apply andb_true_iff in Hleft as [Hfor Htrait].
        assert (Hfor_eq : for1 = for2) by (apply IH; [simpl in Hlt; lia | exact Hfor]).
        subst for2.
        apply String.eqb_eq in Htrait. subst trait2.
        apply String.eqb_eq in Hassoc. subst assoc2.
        assert (Hargs_eq : assoc_args1 = assoc_args2).
        { revert assoc_args2 Hargs.
          induction assoc_args1 as [| a1 args1' IHargs]; intros assoc_args2 Hargs.
          - destruct assoc_args2; simpl in Hargs; [reflexivity | discriminate].
          - destruct assoc_args2 as [| a2 args2']; simpl in Hargs; [discriminate |].
            apply andb_true_iff in Hargs as [Ha Htail].
            f_equal.
            + apply IH; [simpl in Hlt; lia | exact Ha].
            + apply IHargs; [simpl; simpl in Hlt; lia | exact Htail]. }
        subst assoc_args2. reflexivity.
      + apply andb_true_iff in Hc as [Hlk Ht].
        apply andb_true_iff in Hlk as [Hl Hk].
        apply lifetime_eqb_eq in Hl. subst l2.
        apply ref_kind_eqb_true in Hk. subst k2.
        f_equal. apply IH; [simpl in Hlt; lia | exact Ht].
  }
  intros T1 T2 H.
  exact (Hsize (S (ty_depth T1)) T1 T2 (Nat.lt_succ_diag_r _) H).
Qed.

Lemma ty_core_eqb_true : forall c1 c2,
  ty_core_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2 H.
  destruct c1 as [| | | | s1 | i1 | name1 lts1 args1 | name1 lts1 args1
                  | ts1 r1 | lc1 cts1 cr1 | n1 Ω1 b1 | tn1 bs1 tb1
                  | for1 trait1 assoc_args1 assoc1 | l1 k1 t1],
           c2 as [| | | | s2 | i2 | name2 lts2 args2 | name2 lts2 args2
                  | ts2 r2 | lc2 cts2 cr2 | n2 Ω2 b2 | tn2 bs2 tb2
                  | for2 trait2 assoc_args2 assoc2 | l2 k2 t2];
    simpl in H; try discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H as [Hname_lts Hargs].
    apply andb_true_iff in Hname_lts as [Hname Hlts].
    apply String.eqb_eq in Hname. subst name2.
    apply lifetime_list_eqb_true in Hlts. subst lts2.
    f_equal.
    revert args2 Hargs.
    induction args1 as [| t1 args1' IHargs]; intros args2 Hargs.
    + destruct args2; [reflexivity | discriminate].
    + destruct args2 as [| t2 args2']; [discriminate |].
      simpl in Hargs. apply andb_true_iff in Hargs as [Ht Htail].
      f_equal.
      * apply ty_eqb_true. exact Ht.
      * apply IHargs. exact Htail.
  - apply andb_true_iff in H as [Hname_lts Hargs].
    apply andb_true_iff in Hname_lts as [Hname Hlts].
    apply String.eqb_eq in Hname. subst name2.
    apply lifetime_list_eqb_true in Hlts. subst lts2.
    f_equal.
    revert args2 Hargs.
    induction args1 as [| t1 args1' IHargs]; intros args2 Hargs.
    + destruct args2; [reflexivity | discriminate].
    + destruct args2 as [| t2 args2']; [discriminate |].
      simpl in Hargs. apply andb_true_iff in Hargs as [Ht Htail].
      f_equal.
      * apply ty_eqb_true. exact Ht.
      * apply IHargs. exact Htail.
  - apply andb_true_iff in H as [Hlist Hr].
    assert (Heqr : r1 = r2) by (apply ty_eqb_true; exact Hr). subst r2.
    f_equal.
    revert ts2 Hlist.
    induction ts1 as [| t1 ts1' IHts]; intros ts2 Hlist.
    + destruct ts2; [reflexivity | discriminate].
    + destruct ts2 as [| t2 ts2']; [discriminate |].
      simpl in Hlist. apply andb_true_iff in Hlist as [Ht Hts].
      f_equal.
      * apply ty_eqb_true. exact Ht.
      * apply IHts. exact Hts.
  - apply andb_true_iff in H as [Henv_list Hr].
    apply andb_true_iff in Henv_list as [Henv Hlist].
    apply lifetime_eqb_eq in Henv. subst lc2.
    assert (Heqr : cr1 = cr2) by (apply ty_eqb_true; exact Hr). subst cr2.
    f_equal.
    revert cts2 Hlist.
    induction cts1 as [| t1 cts1' IHts]; intros cts2 Hlist.
    + destruct cts2; [reflexivity | discriminate].
    + destruct cts2 as [| t2 cts2']; [discriminate |].
      simpl in Hlist. apply andb_true_iff in Hlist as [Ht Hts].
      f_equal.
      * apply ty_eqb_true. exact Ht.
      * apply IHts. exact Hts.
  - apply andb_true_iff in H as [Hlk Ht].
    apply andb_true_iff in Hlk as [Hn HΩ].
    apply Nat.eqb_eq in Hn. subst n2.
    apply outlives_ctx_eqb_true in HΩ. subst Ω2.
    f_equal. apply ty_eqb_true. exact Ht.
  - assert (Hty :
      ty_eqb
        (MkTy UUnrestricted (TTypeForall tn1 bs1 tb1))
        (MkTy UUnrestricted (TTypeForall tn2 bs2 tb2)) = true).
    { simpl. exact H. }
    apply ty_eqb_true in Hty. inversion Hty. reflexivity.
  - apply andb_true_iff in H as [Hleft Hassoc].
    apply andb_true_iff in Hleft as [Hleft Hargs].
    apply andb_true_iff in Hleft as [Hfor Htrait].
    apply ty_eqb_true in Hfor. subst for2.
    apply String.eqb_eq in Htrait. subst trait2.
    apply String.eqb_eq in Hassoc. subst assoc2.
    assert (Hargs_eq : assoc_args1 = assoc_args2).
    { revert assoc_args2 Hargs.
      induction assoc_args1 as [| a1 args1' IHargs]; intros assoc_args2 Hargs.
      - destruct assoc_args2; simpl in Hargs; [reflexivity | discriminate].
      - destruct assoc_args2 as [| a2 args2']; simpl in Hargs; [discriminate |].
        apply andb_true_iff in Hargs as [Ha Htail].
        f_equal.
        + apply ty_eqb_true. exact Ha.
        + apply IHargs. exact Htail. }
    subst assoc_args2. reflexivity.
  - apply andb_true_iff in H as [Hlk Ht].
    apply andb_true_iff in Hlk as [Hl Hk].
    apply lifetime_eqb_eq in Hl. subst l2.
    apply ref_kind_eqb_true in Hk. subst k2.
    f_equal. apply ty_eqb_true. exact Ht.
Qed.

Lemma usage_eqb_true : forall u1 u2,
  usage_eqb u1 u2 = true -> u1 = u2.
Proof. destruct u1, u2; simpl; intros H; try discriminate; reflexivity. Qed.

Lemma ty_compatible_args_contra_b_sound : forall compat Ω actual expected,
  (forall Ω T_actual T_expected,
      compat Ω T_actual T_expected = true ->
      ty_compatible Ω T_actual T_expected) ->
  ty_compatible_args_contra_b_fuel compat Ω actual expected = true ->
  Forall2 (fun expected actual => ty_compatible Ω expected actual) expected actual.
Proof.
  intros compat Ω actual.
  induction actual as [| a actual IH]; intros expected Hcompat Hargs.
  - destruct expected; simpl in Hargs; try discriminate. constructor.
  - destruct expected as [| e expected]; simpl in Hargs; try discriminate.
    apply andb_true_iff in Hargs as [Hhead Htail].
    constructor.
    + apply Hcompat. exact Hhead.
    + eapply IH.
      * exact Hcompat.
      * exact Htail.
Qed.

Lemma ty_compatible_forall_generalize_unused_sound :
  forall Ω ua ue n ca body,
    usage_sub_bool ua ue = true ->
    contains_lbound_ty body = false ->
    ty_compatible Ω (MkTy ua ca) body ->
    ty_compatible Ω (MkTy ua ca) (MkTy ue (TForall n [] body)).
Proof.
  intros Ω ua ue n ca body Hu Hnob Hcompat.
  eapply TC_Forall_GeneralizeUnused.
  - apply usage_sub_bool_sound. exact Hu.
  - exact Hnob.
  - exact Hcompat.
Qed.

Lemma ty_compatible_b_sound : forall Ω T_actual T_expected,
  ty_compatible_b Ω T_actual T_expected = true ->
  ty_compatible Ω T_actual T_expected.
Proof.
  intros Ω T_actual T_expected H.
  unfold ty_compatible_b in H.
  set (fuel := ty_depth T_actual + ty_depth T_expected) in H.
  clearbody fuel.
  revert Ω T_actual T_expected H.
  induction fuel as [| fuel IH]; intros Ω T_actual T_expected H.
  - simpl in H. discriminate.
  - destruct T_actual as [ua ca], T_expected as [ue ce].
    simpl in H. apply andb_true_iff in H as [Hu Hc].
	    destruct ca as [| | | | sa | ia | struct_a ltsa argsa | enum_a ltsa argsa
                     | tsa ra | lca ctsa cra | na Ωa body_a | tna boundsa tbody_a
                     | for_a trait_a assoc_args_a assoc_a | la rka Ta],
             ce as [| | | | se | ie | struct_e ltse argse | enum_e ltse argse
                     | tse re | lce ctse cre | nb Ωb body_b | tnb boundsb tbody_b
                     | for_b trait_b assoc_args_b assoc_b | lb rkb Tb];
      simpl in Hc; try discriminate;
	      try (apply TC_Core;
	           [apply usage_sub_bool_sound; exact Hu
	           | apply ty_core_eqb_true; exact Hc]).
	    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
	    + destruct Ωb as [|p Ωb]; [|discriminate].
	      apply andb_true_iff in Hc as [Hnob Hrec].
	      apply negb_true_iff in Hnob.
	      eapply ty_compatible_forall_generalize_unused_sound.
	      * exact Hu.
	      * exact Hnob.
	      * eapply IH. exact Hrec.
	    + destruct Ωb as [|p Ωb]; [|discriminate].
	      apply andb_true_iff in Hc as [Hnob Hrec].
	      apply negb_true_iff in Hnob.
	      eapply ty_compatible_forall_generalize_unused_sound.
	      * exact Hu.
	      * exact Hnob.
	      * eapply IH. exact Hrec.
		    + destruct Ωb as [|p Ωb]; [|discriminate].
		      apply andb_true_iff in Hc as [Hnob Hrec].
		      apply negb_true_iff in Hnob.
		      eapply ty_compatible_forall_generalize_unused_sound.
		      * exact Hu.
		      * exact Hnob.
		      * eapply IH. exact Hrec.
		    + destruct Ωb as [|p Ωb]; [|discriminate].
		      apply andb_true_iff in Hc as [Hnob Hrec].
		      apply negb_true_iff in Hnob.
		      eapply ty_compatible_forall_generalize_unused_sound.
		      * exact Hu.
		      * exact Hnob.
		      * eapply IH. exact Hrec.
		    + apply andb_true_iff in Hc as [Hargs Hret].
      apply TC_Fn.
      * apply usage_sub_bool_sound. exact Hu.
      * eapply ty_compatible_args_contra_b_sound.
        -- intros Ω0 T_actual0 T_expected0 Hcompat.
           eapply IH. exact Hcompat.
        -- exact Hargs.
      * eapply IH. exact Hret.
    + apply andb_true_iff in Hc as [Hargs Hret].
      apply TC_Fn_Closure.
      * apply usage_sub_bool_sound. exact Hu.
      * eapply ty_compatible_args_contra_b_sound.
        -- intros Ω0 T_actual0 T_expected0 Hcompat.
           eapply IH. exact Hcompat.
        -- exact Hargs.
      * eapply IH. exact Hret.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + apply andb_true_iff in Hc as [Henv_args Hret].
      apply andb_true_iff in Henv_args as [Henv Hargs].
      apply TC_Closure.
      * apply usage_sub_bool_sound. exact Hu.
      * apply outlives_b_sound. exact Henv.
      * eapply ty_compatible_args_contra_b_sound.
        -- intros Ω0 T_actual0 T_expected0 Hcompat.
           eapply IH. exact Hcompat.
        -- exact Hargs.
      * eapply IH. exact Hret.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + apply andb_true_iff in Hc as [HnΩ HT].
      apply andb_true_iff in HnΩ as [Hn HΩ].
      apply Nat.eqb_eq in Hn. subst nb.
      apply outlives_ctx_eqb_true in HΩ. subst Ωb.
      apply TC_Forall.
      * apply usage_sub_bool_sound. exact Hu.
      * eapply IH. exact HT.
	    + destruct Ωb as [|p Ωb]; [|discriminate].
	      apply andb_true_iff in Hc as [Hnob Hrec].
	      apply negb_true_iff in Hnob.
	      eapply ty_compatible_forall_generalize_unused_sound.
	      * exact Hu.
	      * exact Hnob.
	      * eapply IH. exact Hrec.
	    + apply andb_true_iff in Hc as [Hnb Hrec].
	      apply andb_true_iff in Hnb as [Hn Hbounds].
	      apply Nat.eqb_eq in Hn. subst tnb.
	      assert (Hbounds_eq : boundsa = boundsb).
	      { revert boundsb Hbounds.
	        induction boundsa as [| [idx1 refs1] bs1 IHbs];
	          intros boundsb Hbounds;
	          destruct boundsb as [| [idx2 refs2] bs2]; simpl in Hbounds;
	          try discriminate; try reflexivity.
	        apply andb_true_iff in Hbounds as [Hhead Htail].
	        apply andb_true_iff in Hhead as [Hidx Hrefs].
	        apply Nat.eqb_eq in Hidx. subst idx2.
	        assert (Hrefs_eq : refs1 = refs2).
	        { revert refs2 Hrefs.
	          induction refs1 as [| [name1 args1] refs1' IHrefs];
	            intros refs2 Hrefs;
	            destruct refs2 as [| [name2 args2] refs2']; simpl in Hrefs;
	            try discriminate; try reflexivity.
	          apply andb_true_iff in Hrefs as [Hhead Htail_refs].
	          apply andb_true_iff in Hhead as [Hname Hargs].
	          apply String.eqb_eq in Hname. subst name2.
	          assert (Hargs_eq : args1 = args2).
	          { revert args2 Hargs.
	            induction args1 as [| a1 args1' IHargs]; intros args2 Hargs;
	              destruct args2 as [| a2 args2']; simpl in Hargs;
	              try discriminate; try reflexivity.
	            apply andb_true_iff in Hargs as [Ha Htail_args].
	            f_equal; [apply ty_eqb_true; exact Ha | apply IHargs; exact Htail_args]. }
	          assert (Hrefs_tail : refs1' = refs2') by (apply IHrefs; exact Htail_refs).
	          subst. reflexivity. }
	        assert (Hbounds_tail : bs1 = bs2) by (apply IHbs; exact Htail).
	        subst. reflexivity. }
	      subst boundsb.
	      eapply TC_TypeForall.
	      * apply usage_sub_bool_sound. exact Hu.
	      * eapply IH. exact Hrec.
	    + destruct Ωb as [|p Ωb]; [|discriminate].
	      apply andb_true_iff in Hc as [Hnob Hrec].
	      apply negb_true_iff in Hnob.
	      eapply ty_compatible_forall_generalize_unused_sound.
	      * exact Hu.
	      * exact Hnob.
	      * eapply IH. exact Hrec.
    + destruct Ωb as [|p Ωb]; [|discriminate].
      apply andb_true_iff in Hc as [Hnob Hrec].
      apply negb_true_iff in Hnob.
      eapply ty_compatible_forall_generalize_unused_sound.
      * exact Hu.
      * exact Hnob.
      * eapply IH. exact Hrec.
    + apply andb_true_iff in Hc as [Hlr HT].
      apply andb_true_iff in Hlr as [Hl Hr].
      apply ref_kind_eqb_true in Hr. subst rkb.
      destruct rka.
      * apply TC_Ref_Shared.
        -- apply usage_sub_bool_sound. exact Hu.
        -- apply outlives_b_sound. exact Hl.
        -- eapply IH. exact HT.
      * apply ty_eqb_true in HT. subst Tb.
        apply TC_Ref_Unique.
        -- apply usage_sub_bool_sound. exact Hu.
        -- apply outlives_b_sound. exact Hl.
Qed.

End CompatBoolSoundness.

Lemma ty_compatible_b_sound_light : forall Ω T_actual T_expected,
  ty_compatible_b Ω T_actual T_expected = true ->
  ty_compatible Ω T_actual T_expected.
Proof.
  exact CompatBoolSoundness.ty_compatible_b_sound.
Qed.

Lemma ty_compatible_normalize_assoc_b_sound :
  forall env Ω T_actual T_expected,
    ty_compatible_b Ω
      (normalize_assoc_ty env T_actual)
      (normalize_assoc_ty env T_expected) = true ->
    ty_compatible Ω
      (normalize_assoc_ty env T_actual)
      (normalize_assoc_ty env T_expected).
Proof.
  intros env Ω T_actual T_expected Hcompat.
  exact (ty_compatible_b_sound_light Ω
    (normalize_assoc_ty env T_actual)
    (normalize_assoc_ty env T_expected) Hcompat).
Qed.
