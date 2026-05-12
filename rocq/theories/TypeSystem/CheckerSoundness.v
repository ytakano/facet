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

(* ------------------------------------------------------------------ *)
(* Auxiliary: ref_kind_eqb, ty_eqb, ty_core_eqb correctness             *)
(* ------------------------------------------------------------------ *)

Lemma ref_kind_eqb_true : forall k1 k2,
  ref_kind_eqb k1 k2 = true -> k1 = k2.
Proof.
  destruct k1, k2; simpl; intros H; try discriminate; reflexivity.
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
      destruct c1 as [| | | | s1 | ts1 r1 | l1 k1 t1],
               c2 as [| | | | s2 | ts2 r2 | l2 k2 t2];
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
  destruct c1 as [| | | | s1 | ts1 r1 | l1 k1 t1],
           c2 as [| | | | s2 | ts2 r2 | l2 k2 t2];
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
    apply andb_true_iff in Hlk as [Hl Hk].
    apply lifetime_eqb_eq in Hl. subst l2.
    apply ref_kind_eqb_true in Hk. subst k2.
    f_equal. apply ty_eqb_true. exact Ht.
Qed.

Lemma usage_eqb_true : forall u1 u2,
  usage_eqb u1 u2 = true -> u1 = u2.
Proof. destruct u1, u2; simpl; intros H; try discriminate; reflexivity. Qed.

Lemma ty_compatible_b_sound : forall T_actual T_expected,
  ty_compatible_b T_actual T_expected = true ->
  ty_compatible T_actual T_expected.
Proof.
  assert (Hsize : forall n T_actual T_expected,
      ty_depth T_actual < n ->
      ty_compatible_b T_actual T_expected = true ->
      ty_compatible T_actual T_expected).
  {
    induction n as [| n IH]; intros T_actual T_expected Hlt H.
    - destruct T_actual as [? c]; destruct c; simpl in Hlt; lia.
    - destruct T_actual as [ua ca], T_expected as [ue ce].
      simpl in H. apply andb_true_iff in H as [Hu Hc].
      destruct ca as [| | | | sa | tsa ra | la rka Ta],
               ce as [| | | | se | tse re | lb rkb Tb];
        simpl in Hc; try discriminate;
        try (apply TC_Core;
             [apply usage_sub_bool_sound; exact Hu | reflexivity]).
      + apply String.eqb_eq in Hc. subst.
        apply TC_Core; [apply usage_sub_bool_sound; exact Hu | reflexivity].
      + apply TC_Core.
        * apply usage_sub_bool_sound. exact Hu.
        * apply ty_core_eqb_true. exact Hc.
      + apply andb_true_iff in Hc as [Hlr HT].
        apply andb_true_iff in Hlr as [Hl Hr].
        apply ref_kind_eqb_true in Hr. subst rkb.
        apply TC_Ref.
        * apply usage_sub_bool_sound. exact Hu.
        * apply outlives_b_sound. exact Hl.
        * apply IH.
          -- simpl in Hlt. lia.
          -- exact HT.
  }
  intros T_actual T_expected H.
  exact (Hsize (S (ty_depth T_actual)) T_actual T_expected
    (Nat.lt_succ_diag_r _) H).
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

Lemma ecall_collect_eq : forall fenv n args Γ,
  (fix collect (Γ0 : ctx) (as_ : list expr) : infer_result (list Ty * ctx) :=
     match as_ with
     | [] => infer_ok ([], Γ0)
     | e' :: es =>
         match infer_core fenv n Γ0 e' with
         | infer_err err => infer_err err
         | infer_ok (T_e, Γ1) =>
             match collect Γ1 es with
             | infer_err err => infer_err err
             | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
             end
         end
     end) Γ args = infer_args_collect fenv n Γ args.
Proof.
  intros fenv n args. induction args as [| e es IH]; intros Γ; simpl.
  - reflexivity.
  - destruct (infer_core fenv n Γ e) as [[T_e Γ1] | err] eqn:He; [rewrite IH |]; reflexivity.
Qed.

Lemma infer_call_args_sound_v2 : forall fenv n Γ args arg_tys params Γ',
  infer_args_collect fenv n Γ args = infer_ok (arg_tys, Γ') ->
  (forall Γ0 e T Γ1,
      In e args ->
      infer_core fenv n Γ0 e = infer_ok (T, Γ1) ->
      typed fenv n Γ0 e T Γ1) ->
  check_args arg_tys params = None ->
  typed_args fenv n Γ args params Γ'.
Proof.
  intros fenv n Γ args.
  revert Γ.
  induction args as [| e es IH]; intros Γ arg_tys params Γ' Hcollect Hexpr Hcheck.
  - simpl in Hcollect. injection Hcollect as <- <-.
    destruct params; simpl in Hcheck; [constructor | discriminate].
  - simpl in Hcollect.
    destruct (infer_core fenv n Γ e) as [[T_e Γ1] | err] eqn:He; [|discriminate].
    destruct (infer_args_collect fenv n Γ1 es) as [[tys Γ2] | err'] eqn:Htail; [|discriminate].
    injection Hcollect as <- <-.
    destruct params as [| p ps]; [discriminate |].
    simpl in Hcheck.
    destruct (ty_compatible_b T_e (param_ty p)) eqn:Hcompat;
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

(* ------------------------------------------------------------------ *)
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv n Γ e T Γ',
  infer_core fenv n Γ e = infer_ok (T, Γ') ->
  typed fenv n Γ e T Γ'.
Proof.
  assert (Hsize : forall sz fenv n Γ e T Γ',
    expr_size e < sz ->
    infer_core fenv n Γ e = infer_ok (T, Γ') ->
    typed fenv n Γ e T Γ').
  {
  induction sz as [| sz IH]; intros fenv n Γ e T Γ' Hlt Hinfer.
  - lia.
  - destruct e; simpl in Hinfer.

  (* EUnit *)
  + injection Hinfer as <- <-. constructor.

  (* ELit *)
  + destruct l.
    * injection Hinfer as <- <-. constructor.
    * injection Hinfer as <- <-. constructor.
    * injection Hinfer as <- <-. constructor.

  (* EVar i *)
  + rename i into x.
    destruct (ctx_lookup_b x Γ) as [[Tv b] |] eqn:Hlookup_b.
    2: discriminate.
    destruct (usage_eqb (ty_usage Tv) UUnrestricted) eqn:Hunr.
    * (* unrestricted: copy, no consumption *)
      injection Hinfer as <- <-.
      apply T_Var_Copy with (b := b).
      -- rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      -- destruct (ty_usage Tv); simpl in Hunr; try discriminate; reflexivity.
    * (* linear/affine: consume on read *)
      destruct b; [discriminate |].
      destruct (ctx_consume_b x Γ) as [Γ'' |] eqn:Hcons_b.
      2: discriminate.
      injection Hinfer as <- <-.
      apply T_Var_Consume.
      -- rewrite <- ctx_lookup_b_eq. exact Hlookup_b.
      -- intro Heq. rewrite Heq in Hunr. simpl in Hunr. discriminate.
      -- rewrite <- ctx_consume_b_eq. exact Hcons_b.

  (* ELet m i t e1 e2 *)
  + rename i into x.
    destruct (infer_core fenv n Γ e1) as [[T1 Γ1] | err1] eqn:He1.
    2: discriminate.
    destruct (ty_compatible_b T1 t) eqn:Hcompat.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    destruct (infer_core fenv n (ctx_add_b x t m Γ1) e2) as [[T2 Γ2] | err2] eqn:He2.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    destruct (ctx_check_ok x t Γ2) eqn:Hok.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    simpl in Hinfer.
    injection Hinfer as <- <-.
    rewrite ctx_remove_b_eq.
    eapply T_Let.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He1.
    * apply ty_compatible_b_sound. exact Hcompat.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He2.
    * apply ctx_check_ok_sound. exact Hok.
  (* ELetInfer m x e1 e2 *)
  + rename i into x.
    destruct (infer_core fenv n Γ e1) as [[T1 Γ1] | err1] eqn:He1.
    2: discriminate.
    destruct (infer_core fenv n (ctx_add_b x T1 m Γ1) e2) as [[T2 Γ2] | err2] eqn:He2.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    destruct (ctx_check_ok x T1 Γ2) eqn:Hok.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    simpl in Hinfer.
    injection Hinfer as <- <-.
    rewrite ctx_remove_b_eq.
    eapply T_LetInfer.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He1.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He2.
    * apply ctx_check_ok_sound. exact Hok.

  (* ECall *)
  + destruct (lookup_fn_b i fenv) as [fdef |] eqn:Hlookup.
    2: discriminate.
    rewrite ecall_collect_eq in Hinfer.
    destruct (infer_args_collect fenv n Γ l) as [[arg_tys Γcall] | err] eqn:Hcoll.
    2: discriminate.
    destruct (build_sigma (fn_lifetimes fdef) (repeat None (fn_lifetimes fdef)) arg_tys (fn_params fdef)) as [σ_acc |] eqn:Hbuild.
    2: discriminate.
    remember (finalize_subst σ_acc) as σ eqn:Hsigma.
    remember (apply_lt_params σ (fn_params fdef)) as ps_subst eqn:Hps.
    destruct (check_args arg_tys ps_subst) as [err' |] eqn:Hcheck.
    2: destruct (forallb (wf_lifetime_b (mk_region_ctx n)) σ) eqn:Hwf; simpl in Hinfer.
    all: try discriminate.
    injection Hinfer as <- <-.
    destruct (lookup_fn_b_sound i fenv fdef Hlookup) as [Hin Hname].
    eapply T_Call_Lt with (σ := σ).
    * exact Hin.
    * exact Hname.
    * rewrite <- Hps.
      eapply infer_call_args_sound_v2.
      -- exact Hcoll.
      -- intros Γ0 e0 T0 Γ0' Hin_arg Hinfer0.
         eapply IH.
         ++ pose proof (expr_size_call_arg_lt i l e0 Hin_arg) as Harg_lt.
            assert (expr_size e0 < sz) as Hlt_arg by lia.
            exact Hlt_arg.
         ++ exact Hinfer0.
      -- exact Hcheck.

  (* EReplace p e: PVar or PDeref (PVar) *)
  + destruct p as [px | q].
    * (* PVar px → T_Replace *)
      destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
      2: discriminate.
      destruct b; [discriminate |].
      destruct (ctx_lookup_mut_b px Γ) as [mut |] eqn:Hmut_b.
      2: discriminate.
      destruct mut; [discriminate |].
      destruct (infer_core fenv n Γ e) as [Htyped3 | err3] eqn:He.
      2: discriminate.
      destruct Htyped3 as [T_new Γ1].
      destruct (ty_compatible_b T_new T_x) eqn:Hcompat; [|discriminate].
      injection Hinfer as <- <-.
      apply T_Replace with (T_new := T_new).
      -- rewrite <- ctx_lookup_b_eq. exact Hlx_b.
      -- rewrite <- ctx_lookup_mut_b_eq. exact Hmut_b.
      -- eapply IH. simpl in Hlt; lia. exact He.
      -- apply ty_compatible_b_sound. exact Hcompat.
    * (* PDeref q *)
      destruct q as [rv | q2].
      -- (* PDeref (PVar rv) → T_Replace_Deref *)
         simpl in Hinfer.
         destruct (ctx_lookup_b rv Γ) as [[T_r b] |] eqn:Hlr_b;
           [| discriminate].
         destruct b; [discriminate |].
         destruct (ty_core T_r) eqn:HcoreR; try discriminate.
         lazymatch type of HcoreR with
         | ty_core T_r = TRef ?la ?rk ?T_inner =>
             destruct rk; [discriminate |];
             assert (HTeq : T_r = MkTy (ty_usage T_r) (TRef la RUnique T_inner))
               by (destruct T_r as [u c]; simpl in HcoreR; rewrite HcoreR; reflexivity)
         end.
         destruct (ctx_lookup_mut_b rv Γ) as [mut |] eqn:Hmut_b; [| discriminate].
         destruct mut; [discriminate |].
         destruct (infer_core fenv n Γ e) as [[T_new Γ1] |] eqn:He; [| discriminate].
         lazymatch type of HcoreR with
         | ty_core T_r = TRef ?la ?rk ?T_inner =>
             destruct (ty_compatible_b T_new T_inner) eqn:Hcompat;
               [| discriminate];
             injection Hinfer as <- <-;
             eapply T_Replace_Deref with (u_r := ty_usage T_r);
             [ rewrite <- ctx_lookup_b_eq; rewrite <- HTeq; exact Hlr_b
             | rewrite <- ctx_lookup_mut_b_eq; exact Hmut_b
             | eapply IH; [simpl in Hlt; lia | exact He]
             | apply ty_compatible_b_sound; exact Hcompat ]
         end.
      -- (* PDeref (PDeref _) → ErrNotImplemented *)
         discriminate.

  (* EAssign p e: PVar or PDeref (PVar) *)
  + destruct p as [px | q].
    * (* PVar px → T_Assign *)
      destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
      2: discriminate.
      destruct b; [discriminate |].
      destruct (ctx_lookup_mut_b px Γ) as [mut |] eqn:Hmut_b.
      2: discriminate.
      destruct mut; [discriminate |].
      destruct (usage_eqb (ty_usage T_x) ULinear) eqn:Hlin; [discriminate |].
      destruct (infer_core fenv n Γ e) as [[T_new Γ1] |] eqn:He.
      2: discriminate.
      destruct (ty_compatible_b T_new T_x) eqn:Hcompat; [|discriminate].
      injection Hinfer as <- <-.
      eapply T_Assign with (T := T_x) (T_new := T_new).
      -- rewrite <- ctx_lookup_b_eq. exact Hlx_b.
      -- rewrite <- ctx_lookup_mut_b_eq. exact Hmut_b.
      -- intro Heq. rewrite Heq in Hlin. simpl in Hlin. discriminate.
      -- eapply IH. simpl in Hlt; lia. exact He.
      -- apply ty_compatible_b_sound. exact Hcompat.
    * (* PDeref q *)
      destruct q as [rv | q2].
      -- (* PDeref (PVar rv) → T_Assign_Deref *)
         simpl in Hinfer.
         destruct (ctx_lookup_b rv Γ) as [[T_r b] |] eqn:Hlr_b; [| discriminate].
         destruct b; [discriminate |].
         destruct (ty_core T_r) eqn:HcoreR; try discriminate.
         lazymatch type of HcoreR with
         | ty_core T_r = TRef ?la ?rk ?T_inner =>
             destruct rk; [discriminate |];
             assert (HTeq : T_r = MkTy (ty_usage T_r) (TRef la RUnique T_inner))
               by (destruct T_r as [u c]; simpl in HcoreR; rewrite HcoreR; reflexivity)
         end.
         destruct (ctx_lookup_mut_b rv Γ) as [mut |] eqn:Hmut_b; [| discriminate].
         destruct mut; [discriminate |].
         lazymatch type of HcoreR with
         | ty_core T_r = TRef ?la ?rk ?T_inner =>
             destruct (usage_eqb (ty_usage T_inner) ULinear) eqn:Hlin; [discriminate |];
             destruct (infer_core fenv n Γ e) as [[T_new Γ1] |] eqn:He; [| discriminate];
             destruct (ty_compatible_b T_new T_inner) eqn:Hcompat;
               [| discriminate];
             injection Hinfer as <- <-;
             eapply T_Assign_Deref with (u_r := ty_usage T_r);
             [ rewrite <- ctx_lookup_b_eq; rewrite <- HTeq; exact Hlr_b
             | rewrite <- ctx_lookup_mut_b_eq; exact Hmut_b
             | intro Heq; rewrite Heq in Hlin; simpl in Hlin; discriminate
             | eapply IH; [simpl in Hlt; lia | exact He]
             | apply ty_compatible_b_sound; exact Hcompat ]
         end.
      -- discriminate.

  (* EBorrow rk p *)
  + destruct p as [px | q].
    * (* PVar px → T_BorrowShared or T_BorrowMut *)
      (* destruct r first so infer_core reduces to the ctx_lookup match *)
      destruct r; simpl in Hinfer.
      -- (* RShared *)
         destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
         2: discriminate.
         destruct b; [discriminate |].
         destruct (usage_eqb (ty_usage T_x) ULinear) eqn:Hlin; [discriminate |].
         injection Hinfer as <- <-.
         eapply T_BorrowShared.
         ++ rewrite <- ctx_lookup_b_eq. exact Hlx_b.
         ++ intro Heq. rewrite Heq in Hlin. simpl in Hlin. discriminate.
      -- (* RUnique *)
         destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
         2: discriminate.
         destruct b; [discriminate |].
         destruct (usage_eqb (ty_usage T_x) ULinear) eqn:Hlin; [discriminate |].
         destruct (ctx_lookup_mut_b px Γ) as [mut |] eqn:Hmut_b.
         2: discriminate.
         destruct mut; [discriminate |].
         injection Hinfer as <- <-.
         eapply T_BorrowMut.
         ++ rewrite <- ctx_lookup_b_eq. exact Hlx_b.
         ++ intro Heq. rewrite Heq in Hlin. simpl in Hlin. discriminate.
         ++ rewrite <- ctx_lookup_mut_b_eq. exact Hmut_b.
    * (* PDeref q → T_ReBorrowShared or T_ReBorrowMut *)
      destruct q as [rv | q2].
      -- (* PDeref (PVar rv): destruct r first so infer_core reduces *)
         destruct r; simpl in Hinfer.
         ++ (* EBorrow RShared (PDeref (PVar rv)) → T_ReBorrowShared *)
            destruct (ctx_lookup_b rv Γ) as [[T_r b] |] eqn:Hlr_b.
            2: discriminate.
            destruct b; [discriminate |].
            destruct (ty_core T_r) eqn:HcoreR; try discriminate.
            destruct (usage_eqb (ty_usage T_r) ULinear) eqn:Hlin; [discriminate |].
            injection Hinfer as <- <-.
            lazymatch type of HcoreR with
            | ty_core T_r = TRef ?la ?rk ?T_inner =>
                assert (HTeq : T_r = MkTy (ty_usage T_r) (TRef la rk T_inner))
                  by (destruct T_r as [u c]; simpl in HcoreR; rewrite HcoreR; reflexivity);
                eapply T_ReBorrowShared with (u_r := ty_usage T_r);
                [ rewrite <- ctx_lookup_b_eq; rewrite <- HTeq; exact Hlr_b
                | rewrite HTeq; simpl; intro Heq;
                  rewrite Heq in Hlin; simpl in Hlin; discriminate ]
            end.
         ++ (* EBorrow RUnique (PDeref (PVar rv)) → T_ReBorrowMut *)
            destruct (ctx_lookup_b rv Γ) as [[T_r b] |] eqn:Hlr_b.
            2: discriminate.
            destruct b; [discriminate |].
            destruct (ty_core T_r) eqn:HcoreR; try discriminate.
            (* infer_core for RUnique requires TRef _ RUnique T_inner;
               destruct rk before usage check so Hinfer can reduce *)
            lazymatch type of HcoreR with
            | ty_core T_r = TRef ?la ?rk ?T_inner =>
                destruct rk; [discriminate |]
            end.
            destruct (usage_eqb (ty_usage T_r) ULinear) eqn:Hlin; [discriminate |].
            destruct (ctx_lookup_mut_b rv Γ) as [mut |] eqn:Hmut_b; [| discriminate].
            destruct mut; [discriminate |].
            injection Hinfer as <- <-.
            lazymatch type of HcoreR with
            | ty_core T_r = TRef ?la RUnique ?T_inner =>
                assert (HTeq : T_r = MkTy (ty_usage T_r) (TRef la RUnique T_inner))
                  by (destruct T_r as [u c]; simpl in HcoreR; rewrite HcoreR; reflexivity);
                eapply T_ReBorrowMut with (u_r := ty_usage T_r);
                [ rewrite <- ctx_lookup_b_eq; rewrite <- HTeq; exact Hlr_b
                | rewrite HTeq; simpl; intro Heq;
                  rewrite Heq in Hlin; simpl in Hlin; discriminate
                | rewrite <- ctx_lookup_mut_b_eq; exact Hmut_b ]
            end.
      -- destruct r; cbn in Hinfer; discriminate.

  (* EDeref e *)
  + destruct (infer_core fenv n Γ e) as [[T_r Γ1] | err] eqn:He.
    2: discriminate.
    destruct (ty_core T_r) eqn:HcoreR; try discriminate.
    lazymatch type of HcoreR with
    | ty_core T_r = TRef ?la ?rk ?T_inner =>
        destruct (usage_eqb (ty_usage T_inner) UUnrestricted) eqn:Hunr;
        [| discriminate];
        injection Hinfer as <- <-;
        assert (Hte : typed fenv n Γ e T_r Γ1)
          by (eapply IH; [simpl in Hlt; lia | exact He]);
        assert (HTeq : T_r = MkTy (ty_usage T_r) (TRef la rk T_inner))
          by (destruct T_r as [u c]; simpl in HcoreR; rewrite HcoreR; reflexivity);
        rewrite HTeq in Hte;
        eapply T_Deref;
        [apply usage_eqb_true; exact Hunr | exact Hte]
    end.

  (* EDrop e *)
  + destruct (infer_core fenv n Γ e) as [Htyped4 | err4] eqn:He.
    2: discriminate.
    destruct Htyped4 as [Te Γ1].
      injection Hinfer as <- <-.
      eapply T_Drop.
      eapply IH.
      * simpl in Hlt. lia.
      * exact He.

  (* EIf e1 e2 e3 *)
  + destruct (infer_core fenv n Γ e1) as [[Tcond Γ1] | ] eqn:He1.
    2: discriminate.
    destruct (ty_core_eqb (ty_core Tcond) TBooleans) eqn:Hbool.
    2: discriminate.
    destruct (infer_core fenv n Γ1 e2) as [[T2 Γ2] | ] eqn:He2.
    2: { simpl in Hinfer. inversion Hinfer. }
    destruct (infer_core fenv n Γ1 e3) as [[T3 Γ3] | ] eqn:He3.
    2: { simpl in Hinfer. inversion Hinfer. }
    destruct (ty_core_eqb (ty_core T2) (ty_core T3)) eqn:Hcore.
    2: discriminate.
    destruct (ctx_merge Γ2 Γ3) as [Γ4 |] eqn:Hmerge.
    2: discriminate.
    simpl in Hinfer. injection Hinfer as <- <-.
    eapply T_If.
    * eapply IH. simpl in Hlt; lia. exact He1.
    * apply ty_core_eqb_true. exact Hbool.
    * eapply IH. simpl in Hlt; lia. exact He2.
    * eapply IH. simpl in Hlt; lia. exact He3.
    * apply ty_core_eqb_true. exact Hcore.
    * exact Hmerge.
  }
  intros fenv n Γ e T Γ' Hinfer.
  eapply (Hsize (S (expr_size e))).
  - lia.
  - exact Hinfer.
Qed.

(* infer_body runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Theorem infer_body_sound : forall fenv n Γ e T Γ',
  infer_body fenv n Γ e = infer_ok (T, Γ') ->
  typed fenv n Γ e T Γ'.
Proof.
  intros fenv n Γ e T Γ' Hinfer.
  unfold infer_body in Hinfer.
  destruct (alpha_rename_for_infer Γ fenv e) as [fenv' e'] eqn:Hrename.
  apply (alpha_rename_for_infer_typed_backward fenv n
    Γ e fenv' e' T Γ' Hrename).
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
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f))) eqn:Hwf_ret.
  { discriminate. }
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f))) eqn:Hwf_params.
  { discriminate. }
  destruct (infer_body fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hinfer.
  - destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body)) eqn:Hwf_body.
    { discriminate. }
    destruct (ty_compatible_b T_body (fn_ret f)) eqn:Hcompat; [|discriminate].
    destruct (params_ok_b _ _) eqn:Hparams; [|discriminate].
    apply infer_body_sound in Hinfer as Htyped.
    apply ty_compatible_b_sound in Hcompat.
    apply params_ok_b_sound in Hparams.
    exists T_body, Γ_out. repeat split; assumption.
  - discriminate.
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
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f))) eqn:Hwf_ret.
  { discriminate. }
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f))) eqn:Hwf_params.
  { discriminate. }
  destruct (infer_core fenv (fn_lifetimes f) (params_ctx (fn_params f)) (fn_body f))
    as [[T_body Γ_out] | err] eqn:Hinfer.
  - destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) T_body)) eqn:Hwf_body.
    { discriminate. }
    destruct (ty_compatible_b T_body (fn_ret f)) eqn:Hcompat; [|discriminate].
    destruct (params_ok_b _ _) eqn:Hparams; [|discriminate].
    apply infer_sound in Hinfer as Htyped.
    apply ty_compatible_b_sound in Hcompat.
    apply params_ok_b_sound in Hparams.
    exists T_body, Γ_out. repeat split; assumption.
  - discriminate.
Qed.
