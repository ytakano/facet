From Facet.TypeSystem Require Import Lifetime Types Syntax TypingRules TypeChecker AlphaRenaming.
From Stdlib Require Import List String Bool Lia PeanoNat Program.Equality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Auxiliary: usage_sub_bool correctness                                 *)
(* ------------------------------------------------------------------ *)

Lemma usage_sub_bool_sound : forall u1 u2,
  usage_sub_bool u1 u2 = true -> usage_sub u1 u2.
Proof.
  intros u1 u2 H.
  destruct u1, u2; simpl in H; try discriminate; constructor.
Qed.

Lemma usage_sub_bool_complete : forall u1 u2,
  usage_sub u1 u2 -> usage_sub_bool u1 u2 = true.
Proof.
  intros u1 u2 H. destruct H.
  - destruct u; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lookup_fn_b_sound : forall fname fenv fdef,
  lookup_fn_b fname fenv = Some fdef ->
  In fdef fenv /\ fn_name fdef = fname.
Proof.
  intros fname fenv.
  induction fenv as [| f fs IH]; intros fdef Hlookup.
  - discriminate.
  - simpl in Hlookup.
    destruct (ident_eqb fname (fn_name f)) eqn:Hname.
    + injection Hlookup as <-.
      apply ident_eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH fdef Hlookup) as [Hin Hfn].
      split; [right; exact Hin | exact Hfn].
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: _b helpers agree with TypingRules definitions              *)
(* ------------------------------------------------------------------ *)

Lemma ctx_lookup_b_eq : forall x Γ,
  ctx_lookup_b x Γ = ctx_lookup x Γ.
Proof.
  intros x Γ. induction Γ as [| [[[n T] b] m] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | apply IH].
Qed.

Lemma ctx_consume_b_eq : forall x Γ,
  ctx_consume_b x Γ = ctx_consume x Γ.
Proof.
  intros x Γ. induction Γ as [| [[[n T] b] m] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma ctx_remove_b_eq : forall x Γ,
  ctx_remove_b x Γ = ctx_remove x Γ.
Proof.
  intros x Γ. induction Γ as [| [[[n T] b] m] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | rewrite IH; reflexivity].
Qed.

(* ctx_add_b and ctx_add are definitionally equal. *)
Lemma ctx_add_b_eq : forall x T m Γ,
  ctx_add_b x T m Γ = ctx_add x T m Γ.
Proof. reflexivity. Qed.

Lemma ctx_lookup_mut_b_eq : forall x Γ,
  ctx_lookup_mut_b x Γ = ctx_lookup_mut x Γ.
Proof.
  intros x Γ. induction Γ as [| [[[n T] b] m] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | apply IH].
Qed.

Lemma infer_place_sound : forall fenv n Γ p T,
  infer_place Γ p = infer_ok T ->
  typed_place fenv n Γ p T.
Proof.
  intros fenv n Γ p. revert Γ.
  induction p as [x | p IH]; intros Γ T Hinfer.
  - simpl in Hinfer.
    destruct (ctx_lookup_b x Γ) as [[Tx b] |] eqn:Hlookup; [|discriminate].
    destruct b; [discriminate |].
    injection Hinfer as <-.
    apply TP_Var. rewrite <- ctx_lookup_b_eq. exact Hlookup.
  - simpl in Hinfer.
    destruct (infer_place Γ p) as [Tp | err] eqn:Hp; [|discriminate].
    destruct (ty_core Tp) eqn:Hcore; try discriminate.
    injection Hinfer as <-.
    lazymatch type of Hcore with
    | ty_core Tp = TRef ?la ?rk ?Tinner =>
        assert (HTeq : Tp = MkTy (ty_usage Tp) (TRef la rk Tinner))
          by (destruct Tp as [u c]; simpl in Hcore; rewrite Hcore; reflexivity);
        eapply TP_Deref;
        rewrite <- HTeq;
        apply IH;
        exact Hp
    end.
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

Lemma ty_depth_forall_body_lt : forall u n Ω body,
  ty_depth body < ty_depth (MkTy u (TForall n Ω body)).
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
      destruct c1 as [| | | | s1 | ts1 r1 | n1 Ω1 b1 | l1 k1 t1],
               c2 as [| | | | s2 | ts2 r2 | n2 Ω2 b2 | l2 k2 t2];
        simpl in Hc; try discriminate.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + apply String.eqb_eq in Hc. subst. reflexivity.
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
      + apply andb_true_iff in Hc as [Hlk Ht].
        apply andb_true_iff in Hlk as [Hn HΩ].
        apply Nat.eqb_eq in Hn. subst n2.
        apply outlives_ctx_eqb_true in HΩ. subst Ω2.
        f_equal. apply IH;
          [pose proof (ty_depth_forall_body_lt u1 n1 Ω1 b1); lia | exact Ht].
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
  destruct c1 as [| | | | s1 | ts1 r1 | n1 Ω1 b1 | l1 k1 t1],
           c2 as [| | | | s2 | ts2 r2 | n2 Ω2 b2 | l2 k2 t2];
    simpl in H; try discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
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
  - apply andb_true_iff in H as [Hlk Ht].
    apply andb_true_iff in Hlk as [Hn HΩ].
    apply Nat.eqb_eq in Hn. subst n2.
    apply outlives_ctx_eqb_true in HΩ. subst Ω2.
    f_equal. apply ty_eqb_true. exact Ht.
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

Lemma opened_call_no_lbound_sound : forall ret_open bounds_open,
  contains_lbound_ty ret_open ||
  contains_lbound_outlives bounds_open = false ->
  contains_lbound_ty ret_open = false /\
  contains_lbound_outlives bounds_open = false.
Proof.
  intros ret_open bounds_open H.
  apply orb_false_iff in H. exact H.
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
    destruct ca as [| | | | sa | tsa ra | na Ωa body_a | la rka Ta],
             ce as [| | | | se | tse re | nb Ωb body_b | lb rkb Tb];
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
    + apply andb_true_iff in Hc as [Hargs Hret].
      apply TC_Fn.
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
    + apply andb_true_iff in Hc as [Hlr HT].
      apply andb_true_iff in Hlr as [Hl Hr].
      apply ref_kind_eqb_true in Hr. subst rkb.
      apply TC_Ref.
      * apply usage_sub_bool_sound. exact Hu.
      * apply outlives_b_sound. exact Hl.
      * eapply IH. exact HT.
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: ctx_check_ok implies ctx_is_ok                             *)
(* ------------------------------------------------------------------ *)

Lemma ctx_check_ok_sound : forall x T Γ,
  ctx_check_ok x T Γ = true -> ctx_is_ok x T Γ.
Proof.
  intros x T Γ H.
  unfold ctx_check_ok, ctx_is_ok in *.
  destruct (ty_usage T) eqn:Hu; try exact I.
  rewrite ctx_lookup_b_eq in H.
  destruct (ctx_lookup x Γ) as [[T' b] |] eqn:Hl.
  - destruct b; [exact I | discriminate].
  - discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary for v6 ECall                                                *)
(* ------------------------------------------------------------------ *)

Lemma ecall_collect_eq : forall fenv Ω n args Γ,
  (fix collect (Γ0 : ctx) (as_ : list expr) : infer_result (list Ty * ctx) :=
     match as_ with
     | [] => infer_ok ([], Γ0)
     | e' :: es =>
         match infer_core fenv Ω n Γ0 e' with
         | infer_err err => infer_err err
         | infer_ok (T_e, Γ1) =>
             match collect Γ1 es with
             | infer_err err => infer_err err
             | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
             end
         end
     end) Γ args = infer_args_collect fenv Ω n Γ args.
Proof.
  intros fenv Ω n args. induction args as [| e es IH]; intros Γ; simpl.
  - reflexivity.
  - destruct (infer_core fenv Ω n Γ e) as [[T_e Γ1] | err] eqn:He; [rewrite IH |]; reflexivity.
Qed.

Lemma infer_call_args_sound_v2 : forall fenv Ω n Γ args arg_tys params Γ',
  infer_args_collect fenv Ω n Γ args = infer_ok (arg_tys, Γ') ->
  (forall Γ0 e T Γ1,
      In e args ->
      infer_core fenv Ω n Γ0 e = infer_ok (T, Γ1) ->
      typed fenv Ω n Γ0 e T Γ1) ->
  check_args Ω arg_tys params = None ->
  typed_args fenv Ω n Γ args params Γ'.
Proof.
  intros fenv Ω n Γ args.
  revert Γ.
  induction args as [| e es IH]; intros Γ arg_tys params Γ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. injection Hcollect as <- <-.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core fenv Ω n Γ e) as [[T_e Γ1] | err] eqn:He; [|discriminate].
    destruct (infer_args_collect fenv Ω n Γ1 es) as [[tys Γ2] | err'] eqn:Htail; [|discriminate].
    injection Hcollect as <- <-.
    destruct params as [| p ps]; [discriminate |].
    simpl in Hcheck.
    destruct (ty_compatible_b Ω T_e (param_ty p)) eqn:Hcompat;
      [| discriminate].
    eapply TArgs_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + apply ty_compatible_b_sound. exact Hcompat.
    + eapply IH.
      * exact Htail.
      * intros Γ0 e0 T0 Γ0' Hin Hinfer0.
        eapply Hexpr. right; exact Hin. exact Hinfer0.
      * exact Hcheck.
Qed.

Lemma check_arg_tys_params_of_tys : forall Ω arg_tys param_tys,
  check_arg_tys Ω arg_tys param_tys =
  check_args Ω arg_tys (params_of_tys param_tys).
Proof.
  intros Ω arg_tys. induction arg_tys as [| a arg_tys IH]; intros param_tys.
  - destruct param_tys; reflexivity.
  - destruct param_tys as [| p ps]; [reflexivity |].
    simpl. destruct (ty_compatible_b Ω a p); [apply IH | reflexivity].
Qed.

Lemma outlives_constraints_hold_b_sound : forall Ω constraints,
  outlives_constraints_hold_b Ω constraints = true ->
  Forall (fun '(a, b) => outlives Ω a b) constraints.
Proof.
  intros Ω constraints.
  unfold outlives_constraints_hold_b.
  induction constraints as [| [a b] rest IH]; simpl; intros H.
  - constructor.
  - apply andb_true_iff in H as [Hhead Htail].
    constructor.
    + apply outlives_b_sound. exact Hhead.
    + apply IH. exact Htail.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv Ω n Γ e T Γ',
  infer_core fenv Ω n Γ e = infer_ok (T, Γ') ->
  typed fenv Ω n Γ e T Γ'.
Proof.
  assert (Hsize : forall sz fenv Ω n Γ e T Γ',
    expr_size e < sz ->
    infer_core fenv Ω n Γ e = infer_ok (T, Γ') ->
    typed fenv Ω n Γ e T Γ').
  {
    induction sz as [| sz IH]; intros fenv Ω n Γ e T Γ' Hlt Hinfer.
    - lia.
    - destruct e; simpl in Hinfer.
      + injection Hinfer as <- <-. constructor.
      + destruct l; injection Hinfer as <- <-; constructor.
      + destruct (ctx_lookup_b i Γ) as [[Tx b] |] eqn:Hlookup; [|discriminate].
        destruct (usage_eqb (ty_usage Tx) UUnrestricted) eqn:Husage.
        * injection Hinfer as <- <-. eapply T_Var_Copy.
          -- rewrite <- ctx_lookup_b_eq. exact Hlookup.
          -- apply usage_eqb_true. exact Husage.
        * destruct b; [discriminate |].
          destruct (ctx_consume_b i Γ) as [Γc |] eqn:Hconsume; [|discriminate].
          injection Hinfer as <- <-. apply T_Var_Consume.
          -- rewrite <- ctx_lookup_b_eq. exact Hlookup.
          -- intro Hu. rewrite Hu in Husage. simpl in Husage. discriminate.
          -- rewrite <- ctx_consume_b_eq. exact Hconsume.
      + destruct (infer_core fenv Ω n Γ e1) as [[T1 Γ1] | err1] eqn:He1; [|discriminate].
        destruct (ty_compatible_b Ω T1 t) eqn:Hcompat; [|discriminate].
        destruct (infer_core fenv Ω n (ctx_add_b i t m Γ1) e2) as [[T2 Γ2] | err2] eqn:He2; [|discriminate].
        destruct (ctx_check_ok i t Γ2) eqn:Hok; [|discriminate].
        injection Hinfer as <- <-.
        eapply T_Let.
        * eapply IH; [simpl in Hlt; lia | exact He1].
        * apply ty_compatible_b_sound. exact Hcompat.
        * eapply IH; [simpl in Hlt; lia | exact He2].
        * apply ctx_check_ok_sound. exact Hok.
      + destruct (infer_core fenv Ω n Γ e1) as [[T1 Γ1] | err1] eqn:He1; [|discriminate].
        destruct (infer_core fenv Ω n (ctx_add_b i T1 m Γ1) e2) as [[T2 Γ2] | err2] eqn:He2; [|discriminate].
        destruct (ctx_check_ok i T1 Γ2) eqn:Hok; [|discriminate].
        injection Hinfer as <- <-.
        eapply T_LetInfer.
        * eapply IH; [simpl in Hlt; lia | exact He1].
        * eapply IH; [simpl in Hlt; lia | exact He2].
        * apply ctx_check_ok_sound. exact Hok.
      + destruct (lookup_fn_b i fenv) as [fdef |] eqn:Hlookup; [|discriminate].
        injection Hinfer as <- <-.
        destruct (lookup_fn_b_sound i fenv fdef Hlookup) as [Hin Hname].
        eapply T_FnValue.
        * exact Hin.
        * exact Hname.
      + destruct (lookup_fn_b i fenv) as [fdef |] eqn:Hlookup; [|discriminate].
        destruct (infer_args_collect fenv Ω n Γ l) as [[arg_tys Γcall] | err] eqn:Hcollect.
        2:{
          rewrite (ecall_collect_eq fenv Ω n l Γ) in Hinfer.
          rewrite Hcollect in Hinfer. discriminate.
        }
        rewrite (ecall_collect_eq fenv Ω n l Γ) in Hinfer.
        rewrite Hcollect in Hinfer.
        destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef))
          as [σ_acc |] eqn:Hbuild; [|discriminate].
        remember (finalize_subst σ_acc) as σ.
        remember (apply_lt_params σ (fn_params fdef)) as ps_subst.
        destruct (check_args Ω arg_tys ps_subst) as [err |] eqn:Hcheck; [discriminate |].
        destruct (forallb (wf_lifetime_b (mk_region_ctx n)) σ) eqn:Hwf; [|discriminate].
        remember (apply_lt_outlives σ (fn_outlives fdef)) as Ω_subst.
        destruct (outlives_constraints_hold_b Ω Ω_subst) eqn:Hout; [|discriminate].
        injection Hinfer as <- <-.
        destruct (lookup_fn_b_sound i fenv fdef Hlookup) as [Hin Hname].
        eapply T_Call_Lt with (fdef := fdef) (σ := σ).
        * exact Hin.
        * exact Hname.
        * subst ps_subst. eapply infer_call_args_sound_v2.
          -- exact Hcollect.
          -- intros Γ0 e0 T0 Γ1 Hin_arg Hinfer_arg.
             eapply IH.
             ++ pose proof (expr_size_call_arg_lt i l e0 Hin_arg). lia.
             ++ exact Hinfer_arg.
          -- exact Hcheck.
        * subst Ω_subst. apply outlives_constraints_hold_b_sound. exact Hout.
      + destruct (infer_core fenv Ω n Γ e) as [[Tcallee Γcallee] | err] eqn:Hcallee; [|discriminate].
        destruct (infer_args_collect fenv Ω n Γcallee l) as [[arg_tys Γcall] | err] eqn:Hcollect.
        2:{
          rewrite (ecall_collect_eq fenv Ω n l Γcallee) in Hinfer.
          rewrite Hcollect in Hinfer. discriminate.
        }
        rewrite (ecall_collect_eq fenv Ω n l Γcallee) in Hinfer.
        rewrite Hcollect in Hinfer.
        destruct (ty_core Tcallee) eqn:Hcore.
        * discriminate.
        * discriminate.
        * discriminate.
        * discriminate.
        * discriminate.
        * destruct (check_arg_tys Ω arg_tys l0) as [err |] eqn:Hcheck; [discriminate |].
          injection Hinfer as <- <-.
          eapply T_CallExpr_Fn.
          -- replace (MkTy (ty_usage Tcallee) (TFn l0 t)) with Tcallee.
             2:{ destruct Tcallee as [u c]. simpl in Hcore. rewrite Hcore. reflexivity. }
             eapply IH.
             ++ pose proof (expr_size_callexpr_callee_lt e l). lia.
             ++ exact Hcallee.
          -- eapply infer_call_args_sound_v2.
             ++ exact Hcollect.
             ++ intros Γ0 e0 T0 Γ1 Hin_arg Hinfer_arg.
                eapply IH.
                ** pose proof (expr_size_callexpr_arg_lt e l e0 Hin_arg). lia.
                ** exact Hinfer_arg.
             ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
        * destruct (ty_core t) eqn:Hbody; try discriminate.
          destruct (build_bound_sigma (repeat None n0) arg_tys l0) as [σ |] eqn:Hbuild; [|discriminate].
          remember (map (open_bound_ty σ) l0) as params_open.
          destruct (check_arg_tys Ω arg_tys params_open) as [err |] eqn:Hcheck; [discriminate |].
          remember (open_bound_ty σ t0) as ret_open.
          remember (open_bound_outlives σ o) as bounds_open.
          destruct (contains_lbound_ty ret_open || contains_lbound_outlives bounds_open) eqn:Hleak; [discriminate |].
          destruct (outlives_constraints_hold_b Ω bounds_open) eqn:Hout; [|discriminate].
          injection Hinfer as <- <-.
          apply opened_call_no_lbound_sound in Hleak as [Hret Hbounds].
          subst params_open ret_open bounds_open.
          eapply T_CallExpr_Forall with (σ := σ) (param_tys := l0).
          -- replace (MkTy (ty_usage Tcallee) (TForall n0 o t)) with Tcallee.
             2:{ destruct Tcallee as [u c]. simpl in Hcore. rewrite Hcore. reflexivity. }
             eapply IH.
             ++ pose proof (expr_size_callexpr_callee_lt e l). lia.
             ++ exact Hcallee.
          -- exact Hbody.
          -- eapply infer_call_args_sound_v2.
             ++ exact Hcollect.
             ++ intros Γ0 e0 T0 Γ1 Hin_arg Hinfer_arg.
                eapply IH.
                ** pose proof (expr_size_callexpr_arg_lt e l e0 Hin_arg). lia.
                ** exact Hinfer_arg.
             ++ rewrite <- check_arg_tys_params_of_tys. exact Hcheck.
          -- exact Hret.
          -- exact Hbounds.
          -- apply outlives_constraints_hold_b_sound. exact Hout.
        * discriminate.
      + destruct p as [x | p].
        * destruct (ctx_lookup_b x Γ) as [[Tx bx] |] eqn:Hlookup; [|discriminate].
          destruct bx; [discriminate |].
          destruct (ctx_lookup_mut_b x Γ) as [mx |] eqn:Hmut; [|discriminate].
          destruct mx; [discriminate |].
          destruct (infer_core fenv Ω n Γ e) as [[Tnew Γnew] | err] eqn:Hnew; [|discriminate].
          destruct (ty_compatible_b Ω Tnew Tx) eqn:Hcompat; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Replace.
          -- rewrite <- ctx_lookup_b_eq. exact Hlookup.
          -- rewrite <- ctx_lookup_mut_b_eq. exact Hmut.
          -- eapply IH; [simpl in Hlt; lia | exact Hnew].
          -- apply ty_compatible_b_sound. exact Hcompat.
        * destruct (infer_place Γ p) as [Tp | err] eqn:Hp; [|discriminate].
          destruct (ty_core Tp) eqn:Hcore; try discriminate.
          destruct r; [discriminate |].
          destruct (infer_core fenv Ω n Γ e) as [[Tnew Γnew] | err] eqn:Hnew; [|discriminate].
          destruct (ty_compatible_b Ω Tnew t) eqn:Hcompat; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Replace_Deref.
          -- replace (MkTy (ty_usage Tp) (TRef l RUnique t)) with Tp.
             ++ apply infer_place_sound. exact Hp.
             ++ destruct Tp as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
          -- eapply IH; [simpl in Hlt; lia | exact Hnew].
          -- apply ty_compatible_b_sound. exact Hcompat.
      + destruct p as [x | p].
        * destruct (ctx_lookup_b x Γ) as [[Tx bx] |] eqn:Hlookup; [|discriminate].
          destruct bx; [discriminate |].
          destruct (ctx_lookup_mut_b x Γ) as [mx |] eqn:Hmut; [|discriminate].
          destruct mx; [discriminate |].
          destruct (usage_eqb (ty_usage Tx) ULinear) eqn:Hlin; [discriminate |].
          destruct (infer_core fenv Ω n Γ e) as [[Tnew Γnew] | err] eqn:Hnew; [|discriminate].
          destruct (ty_compatible_b Ω Tnew Tx) eqn:Hcompat; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Assign.
          -- rewrite <- ctx_lookup_b_eq. exact Hlookup.
          -- rewrite <- ctx_lookup_mut_b_eq. exact Hmut.
          -- intro Hu. rewrite Hu in Hlin. simpl in Hlin. discriminate.
          -- eapply IH; [simpl in Hlt; lia | exact Hnew].
          -- apply ty_compatible_b_sound. exact Hcompat.
        * destruct (infer_place Γ p) as [Tp | err] eqn:Hp; [|discriminate].
          destruct (ty_core Tp) eqn:Hcore; try discriminate.
          destruct r; [discriminate |].
          destruct (usage_eqb (ty_usage t) ULinear) eqn:Hlin; [discriminate |].
          destruct (infer_core fenv Ω n Γ e) as [[Tnew Γnew] | err] eqn:Hnew; [|discriminate].
          destruct (ty_compatible_b Ω Tnew t) eqn:Hcompat; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Assign_Deref.
          -- replace (MkTy (ty_usage Tp) (TRef l RUnique t)) with Tp.
             ++ apply infer_place_sound. exact Hp.
             ++ destruct Tp as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
          -- intro Hu. rewrite Hu in Hlin. simpl in Hlin. discriminate.
          -- eapply IH; [simpl in Hlt; lia | exact Hnew].
          -- apply ty_compatible_b_sound. exact Hcompat.
      + destruct p as [x | p].
        * destruct (ctx_lookup_b x Γ) as [[Tx bx] |] eqn:Hlookup.
          2:{ destruct r; discriminate. }
          destruct bx.
          { destruct r; discriminate. }
          destruct r.
          -- injection Hinfer as <- <-. apply T_BorrowShared.
             rewrite <- ctx_lookup_b_eq. exact Hlookup.
          -- destruct (ctx_lookup_mut_b x Γ) as [mx |] eqn:Hmut; [|discriminate].
             destruct mx; [discriminate |].
             injection Hinfer as <- <-. apply T_BorrowMut.
             ++ rewrite <- ctx_lookup_b_eq. exact Hlookup.
             ++ rewrite <- ctx_lookup_mut_b_eq. exact Hmut.
        * destruct r.
          -- destruct (infer_place Γ p) as [Tp | err] eqn:Hp; [|discriminate].
             destruct (ty_core Tp) eqn:Hcore; try discriminate.
             injection Hinfer as <- <-.
             eapply T_ReBorrowShared.
             replace (MkTy (ty_usage Tp) (TRef l r t)) with Tp.
             ++ apply infer_place_sound. exact Hp.
             ++ destruct Tp as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
          -- destruct (infer_place Γ p) as [Tp | err] eqn:Hp; [|discriminate].
             destruct (ty_core Tp) eqn:Hcore; try discriminate.
             destruct r; [discriminate |].
             injection Hinfer as <- <-.
             eapply T_ReBorrowMut.
             replace (MkTy (ty_usage Tp) (TRef l RUnique t)) with Tp.
             ++ apply infer_place_sound. exact Hp.
             ++ destruct Tp as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
      + destruct (expr_as_place e) as [p |] eqn:Hplace.
        * destruct (infer_place Γ p) as [Tr | err] eqn:Hp; [|discriminate].
          destruct (ty_core Tr) eqn:Hcore; try discriminate.
          destruct (usage_eqb (ty_usage t) UUnrestricted) eqn:Hunr; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Deref_Place.
          -- exact Hplace.
          -- apply usage_eqb_true. exact Hunr.
          -- replace (MkTy (ty_usage Tr) (TRef l r t)) with Tr.
             ++ apply infer_place_sound. exact Hp.
             ++ destruct Tr as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
        * destruct (infer_core fenv Ω n Γ e) as [[Tr Γr] | err] eqn:Hr; [|discriminate].
          destruct (ty_core Tr) eqn:Hcore; try discriminate.
          destruct (usage_eqb (ty_usage t) UUnrestricted) eqn:Hunr; [|discriminate].
          injection Hinfer as <- <-.
          eapply T_Deref.
          -- exact Hplace.
          -- apply usage_eqb_true. exact Hunr.
          -- replace (MkTy (ty_usage Tr) (TRef l r t)) with Tr.
             ++ eapply IH; [simpl in Hlt; lia | exact Hr].
             ++ destruct Tr as [u c]. simpl in Hcore. rewrite Hcore. reflexivity.
      + destruct (infer_core fenv Ω n Γ e) as [[Te Γe] | err] eqn:He; [|discriminate].
        injection Hinfer as <- <-.
        eapply T_Drop. eapply IH; [simpl in Hlt; lia | exact He].
      + destruct (infer_core fenv Ω n Γ e1) as [[Tcond Γ1] | err1] eqn:He1; [|discriminate].
        destruct (ty_core_eqb (ty_core Tcond) TBooleans) eqn:Hbool; [|discriminate].
        destruct (infer_core fenv Ω n Γ1 e2) as [[T2 Γ2] | err2] eqn:He2; [|discriminate].
        destruct (infer_core fenv Ω n Γ1 e3) as [[T3 Γ3] | err3] eqn:He3; [|discriminate].
        destruct (ty_core_eqb (ty_core T2) (ty_core T3)) eqn:Hcore; [|discriminate].
        destruct (ctx_merge Γ2 Γ3) as [Γ4 |] eqn:Hmerge; [|discriminate].
        injection Hinfer as <- <-.
        eapply T_If.
        * eapply IH; [simpl in Hlt; lia | exact He1].
        * apply ty_core_eqb_true. exact Hbool.
        * eapply IH; [simpl in Hlt; lia | exact He2].
        * eapply IH; [simpl in Hlt; lia | exact He3].
        * apply ty_core_eqb_true. exact Hcore.
        * exact Hmerge.
  }
  intros fenv Ω n Γ e T Γ' Hinfer.
  eapply Hsize.
  - apply Nat.lt_succ_diag_r.
  - exact Hinfer.
Qed.

(* infer_body runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Theorem infer_body_sound : forall fenv Ω n Γ e T Γ',
  infer_body fenv Ω n Γ e = infer_ok (T, Γ') ->
  typed fenv Ω n Γ e T Γ'.
Proof.
  intros fenv Ω n Γ e T Γ' Hinfer.
  unfold infer_body in Hinfer.
  apply infer_sound. exact Hinfer.
Qed.

(* ------------------------------------------------------------------ *)
(* Function-definition-level soundness                                   *)
(* ------------------------------------------------------------------ *)

Lemma params_ok_b_sound : forall ps Γ,
  params_ok_b ps Γ = true -> params_ok ps Γ.
Proof.
  induction ps as [|p ps' IH]; simpl; intros Γ H.
  - exact I.
  - apply andb_true_iff in H as [Hok H'].
    split.
    + apply ctx_check_ok_sound. exact Hok.
    + apply IH. exact H'.
Qed.

Theorem infer_fn_def_sound : forall fenv f T Γ',
  infer fenv f = infer_ok (T, Γ') -> typed_fn_def fenv f.
Proof.
  intros fenv f T Γ' Hcheck.
  unfold infer in Hcheck.
  remember (fn_outlives f) as Ω.
  remember (mk_region_ctx (fn_lifetimes f)) as Δ.
  destruct (negb (wf_outlives_b Δ Ω)) eqn:Hwf_out; [discriminate |].
  destruct (negb (wf_type_b Δ (fn_ret f))) eqn:Hwf_ret; [discriminate |].
  destruct (negb (wf_params_b Δ (fn_params f))) eqn:Hwf_params; [discriminate |].
  destruct (infer_body fenv Ω (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hinfer; [|discriminate].
  destruct (negb (wf_type_b Δ T_body)) eqn:Hwf_body; [discriminate |].
  destruct (ty_compatible_b Ω T_body (fn_ret f)) eqn:Hcompat; [|discriminate].
  destruct (params_ok_b (fn_params f) Γ_out) eqn:Hparams; [|discriminate].
  injection Hcheck as <- <-.
  exists T_body, Γ_out.
  repeat split.
  - subst Ω. apply infer_body_sound. exact Hinfer.
  - subst Ω. apply ty_compatible_b_sound. exact Hcompat.
  - apply params_ok_b_sound. exact Hparams.
Qed.

Theorem check_program_sound : forall fenv,
  check_program fenv = true -> Forall (typed_fn_def fenv) fenv.
Proof.
  intros fenv H.
  apply Forall_forall. intros f Hf.
  unfold check_program in H.
  apply forallb_forall with (x := f) in H; [|exact Hf].
  destruct (infer fenv f) as [[T Γ'] | err] eqn:Hinfer.
  - eapply infer_fn_def_sound. exact Hinfer.
  - simpl in H. discriminate.
Qed.

(* infer_direct skips alpha renaming, so its soundness proof goes through
   infer_sound (infer_core soundness) directly, without AlphaRenaming lemmas. *)
Theorem infer_direct_sound : forall fenv f T Γ',
  infer_direct fenv f = infer_ok (T, Γ') -> typed_fn_def fenv f.
Proof.
  intros fenv f T Γ' Hcheck.
  unfold infer_direct in Hcheck.
  remember (fn_outlives f) as Ω.
  remember (mk_region_ctx (fn_lifetimes f)) as Δ.
  destruct (negb (wf_outlives_b Δ Ω)) eqn:Hwf_out; [discriminate |].
  destruct (negb (wf_type_b Δ (fn_ret f))) eqn:Hwf_ret; [discriminate |].
  destruct (negb (wf_params_b Δ (fn_params f))) eqn:Hwf_params; [discriminate |].
  destruct (infer_core fenv Ω (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hinfer; [|discriminate].
  destruct (negb (wf_type_b Δ T_body)) eqn:Hwf_body; [discriminate |].
  destruct (ty_compatible_b Ω T_body (fn_ret f)) eqn:Hcompat; [|discriminate].
  destruct (params_ok_b (fn_params f) Γ_out) eqn:Hparams; [|discriminate].
  injection Hcheck as <- <-.
  exists T_body, Γ_out.
  repeat split.
  - subst Ω. apply infer_sound. exact Hinfer.
  - subst Ω. apply ty_compatible_b_sound. exact Hcompat.
  - apply params_ok_b_sound. exact Hparams.
Qed.
