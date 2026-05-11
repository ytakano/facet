From Facet.TypeSystem Require Import Types Syntax TypingRules TypeChecker AlphaRenaming.
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
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | apply IH].
Qed.

Lemma ctx_consume_b_eq : forall x Γ,
  ctx_consume_b x Γ = ctx_consume x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n).
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma ctx_remove_b_eq : forall x Γ,
  ctx_remove_b x Γ = ctx_remove x Γ.
Proof.
  intros x Γ. induction Γ as [| [[n T] b] t IH].
  - reflexivity.
  - simpl. destruct (ident_eqb x n); [reflexivity | rewrite IH; reflexivity].
Qed.

(* ctx_add_b and ctx_add are definitionally equal. *)
Lemma ctx_add_b_eq : forall x T Γ,
  ctx_add_b x T Γ = ctx_add x T Γ.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary: ty_core_eqb correctness                                    *)
(* ------------------------------------------------------------------ *)

Lemma ty_core_eqb_true : forall c1 c2,
  ty_core_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2 H.
  destruct c1, c2; simpl in H; try discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply String.eqb_eq in H. subst. reflexivity.
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
Lemma infer_call_args_sound : forall fenv Γ args params Γ',
  (forall Γ0 e T Γ1,
      In e args ->
      infer_core fenv Γ0 e = infer_ok (T, Γ1) ->
      typed fenv Γ0 e T Γ1) ->
  ((fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
      : infer_result ctx :=
      match as_, ps with
      | [],       []       => infer_ok Γ0
      | [],       _ :: _   => infer_err ErrArityMismatch
      | _ :: _,   []       => infer_err ErrArityMismatch
      | e' :: es, p :: ps' =>
          match infer_core fenv Γ0 e' with
          | infer_err err            => infer_err err
          | infer_ok (T_e, Γ1) =>
              if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) then
                if usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
                then go Γ1 es ps'
                else infer_err (ErrUsageMismatch (ty_usage T_e) (ty_usage (param_ty p)))
              else infer_err (ErrTypeMismatch (ty_core T_e) (ty_core (param_ty p)))
          end
      end) Γ args params) = infer_ok Γ' ->
  typed_args fenv Γ args params Γ'.
Proof.
  intros fenv Γ args.
  revert Γ.
  induction args as [| e es IH]; intros Γ params Γ' Hexpr Hgo;
    destruct params as [| p ps]; simpl in Hgo; try discriminate.
  - injection Hgo as <-. constructor.
  - destruct (infer_core fenv Γ e) as [[T_e Γ1] |] eqn:He;
      try discriminate.
    destruct (ty_core_eqb (ty_core T_e) (ty_core (param_ty p))) eqn:Hcore; [|discriminate].
    destruct (usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))) eqn:Hsub; [|discriminate].
    eapply TArgs_Cons.
    + eapply Hexpr.
      * left. reflexivity.
      * exact He.
    + exact (ty_core_eqb_true _ _ Hcore).
    + apply usage_sub_bool_sound. exact Hsub.
    + eapply IH.
      * intros Γ0 e0 T0 Γ0' Hin Hinfer0.
        eapply Hexpr.
        -- right; exact Hin.
        -- exact Hinfer0.
      * exact Hgo.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem: infer_core is sound w.r.t. typed                             *)
(* ------------------------------------------------------------------ *)

Theorem infer_sound : forall fenv Γ e T Γ',
  infer_core fenv Γ e = infer_ok (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  assert (Hsize : forall n fenv Γ e T Γ',
    expr_size e < n ->
    infer_core fenv Γ e = infer_ok (T, Γ') ->
    typed fenv Γ e T Γ').
  {
  induction n as [| n IH]; intros fenv Γ e T Γ' Hlt Hinfer.
  - lia.
  - destruct e; simpl in Hinfer.

  (* EUnit *)
  + injection Hinfer as <- <-. constructor.

  (* ELit *)
  + destruct l.
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
    destruct (infer_core fenv Γ e1) as [[T1 Γ1] | err1] eqn:He1.
    2: discriminate.
    destruct (ty_core_eqb (ty_core T1) (ty_core t)) eqn:Hcore.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    destruct (usage_sub_bool (ty_usage T1) (ty_usage t)) eqn:Hsub.
    2: {
      simpl in Hinfer.
      inversion Hinfer.
    }
    destruct (infer_core fenv (ctx_add_b x t Γ1) e2) as [[T2 Γ2] | err2] eqn:He2.
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
    * apply ty_core_eqb_true. exact Hcore.
    * apply usage_sub_bool_sound. exact Hsub.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He2.
    * apply ctx_check_ok_sound. exact Hok.
  (* ELetInfer: out of scope *)
  + discriminate.

  (* ECall *)
  + destruct (lookup_fn_b i fenv) as [fdef |] eqn:Hlookup.
    2: discriminate.
    remember
      ((fix go (Γ0 : ctx) (as_ : list expr) (ps : list param)
          : infer_result ctx :=
          match as_, ps with
          | [], [] => infer_ok Γ0
          | [], _ :: _ => infer_err ErrArityMismatch
          | _ :: _, [] => infer_err ErrArityMismatch
          | e' :: es, p :: ps' =>
              match infer_core fenv Γ0 e' with
              | infer_err err => infer_err err
              | infer_ok (T_e, Γ1) =>
                  if ty_core_eqb (ty_core T_e) (ty_core (param_ty p)) then
                    if usage_sub_bool (ty_usage T_e) (ty_usage (param_ty p))
                    then go Γ1 es ps'
                    else infer_err (ErrUsageMismatch (ty_usage T_e) (ty_usage (param_ty p)))
                  else infer_err (ErrTypeMismatch (ty_core T_e) (ty_core (param_ty p)))
              end
          end) Γ l (fn_params fdef)) as r eqn:Hgo.
    destruct r as [Γcall | err]; [|discriminate].
    injection Hinfer as <- <-.
    destruct (lookup_fn_b_sound i fenv fdef Hlookup) as [Hin Hname].
    eapply T_Call.
    * exact Hin.
    * exact Hname.
    * eapply infer_call_args_sound.
      -- intros Γ0 e0 T0 Γ0' Hin_arg Hinfer0.
         eapply IH.
         ++ pose proof (expr_size_call_arg_lt i l e0 Hin_arg) as Harg_lt.
            assert (expr_size e0 < n) as Hlt_arg by lia.
            exact Hlt_arg.
         ++ exact Hinfer0.
      -- symmetry. exact Hgo.

  (* EReplace (PVar px) e *)
  + destruct p as [px].
    destruct (ctx_lookup_b px Γ) as [[T_x b] |] eqn:Hlx_b.
    2: discriminate.
    destruct b; [discriminate |].
    destruct (infer_core fenv Γ e) as [Htyped3 | err3] eqn:He.
    2: discriminate.
    destruct Htyped3 as [T_new Γ1].
    destruct (ty_core_eqb (ty_core T_new) (ty_core T_x)) eqn:Hcore.
    2: discriminate.
    destruct (usage_sub_bool (ty_usage T_new) (ty_usage T_x)) eqn:Hsub.
    2: discriminate.
    injection Hinfer as <- <-.
    apply T_Replace with (T_new := T_new).
    * rewrite <- ctx_lookup_b_eq. exact Hlx_b.
    * eapply IH.
      -- simpl in Hlt. lia.
      -- exact He.
    * apply ty_core_eqb_true. exact Hcore.
    * apply usage_sub_bool_sound. exact Hsub.

  (* EDrop e *)
  + destruct (infer_core fenv Γ e) as [Htyped4 | err4] eqn:He.
    2: discriminate.
    destruct Htyped4 as [Te Γ1].
      injection Hinfer as <- <-.
      eapply T_Drop.
      eapply IH.
      * simpl in Hlt. lia.
      * exact He.
  }
  intros fenv Γ e T Γ' Hinfer.
  eapply (Hsize (S (expr_size e))).
  - lia.
  - exact Hinfer.
Qed.

(* Public infer runs alpha-renaming before infer_core. The proof requires
   alpha-renaming preservation for typing; keep it isolated from the
   infer_core soundness argument above. *)
Theorem infer_public_sound : forall fenv Γ e T Γ',
  infer fenv Γ e = infer_ok (T, Γ') ->
  typed fenv Γ e T Γ'.
Proof.
  intros fenv Γ e T Γ' Hinfer.
  unfold infer in Hinfer.
  destruct (alpha_rename_for_infer Γ fenv e) as [fenv' e'] eqn:Hrename.
  apply (alpha_rename_for_infer_typed_backward
    fenv Γ e fenv' e' T Γ' Hrename).
  apply infer_sound. exact Hinfer.
Qed.
