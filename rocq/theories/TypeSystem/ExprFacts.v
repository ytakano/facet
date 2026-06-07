From Facet.TypeSystem Require Import Types Syntax.
From Stdlib Require Import List String Bool Lia PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* General expression facts                                             *)
(* ------------------------------------------------------------------ *)

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EUnit => 1
  | ELit _ => 1
  | EVar _ => 1
  | EFn _ => 1
  | EMakeClosure _ _ => 1
  | EPlace _ => 1
  | ELet _ _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ELetInfer _ _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ECall _ args =>
      S ((fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | ECallGeneric _ _ args =>
      S ((fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | ECallExpr callee args =>
      S (expr_size callee +
         (fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | ECallExprGeneric callee _ args =>
      S (expr_size callee +
         (fix go (args0 : list expr) : nat :=
            match args0 with
            | [] => 0
            | arg :: rest => expr_size arg + go rest
            end) args)
  | EStruct _ _ _ fields =>
      S ((fix go (fields0 : list (string * expr)) : nat :=
            match fields0 with
            | [] => 0
            | (_, e) :: rest => expr_size e + go rest
            end) fields)
  | EEnum _ _ _ _ _ payloads =>
      S ((fix go (payloads0 : list expr) : nat :=
            match payloads0 with
            | [] => 0
            | e :: rest => expr_size e + go rest
            end) payloads)
  | EMatch scrut branches =>
      S (expr_size scrut +
         (fix go (branches0 : list (string * list ident * expr)) : nat :=
            match branches0 with
            | [] => 0
            | (_, _, e) :: rest => expr_size e + go rest
            end) branches)
  | EReplace _ e => S (expr_size e)
  | EAssign _ e => S (expr_size e)
  | EBorrow _ _ => 1
  | EDeref e => S (expr_size e)
  | EDrop e => S (expr_size e)
  | EIf e1 e2 e3 => S (expr_size e1 + expr_size e2 + expr_size e3)
  end.

Lemma expr_size_call_arg_lt : forall fname args arg,
  In arg args ->
  expr_size arg < expr_size (ECall fname args).
Proof.
  intros fname args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma expr_size_call_generic_arg_lt : forall fname type_args args arg,
  In arg args ->
  expr_size arg < expr_size (ECallGeneric fname type_args args).
Proof.
  intros fname type_args args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma expr_size_callexpr_callee_lt : forall callee args,
  expr_size callee < expr_size (ECallExpr callee args).
Proof.
  intros. simpl. lia.
Qed.

Lemma expr_size_callexpr_arg_lt : forall callee args arg,
  In arg args ->
  expr_size arg < expr_size (ECallExpr callee args).
Proof.
  intros callee args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma expr_size_callexpr_generic_callee_lt : forall callee type_args args,
  expr_size callee < expr_size (ECallExprGeneric callee type_args args).
Proof.
  intros. simpl. lia.
Qed.

Lemma expr_size_callexpr_generic_arg_lt :
  forall callee type_args args arg,
    In arg args ->
    expr_size arg < expr_size (ECallExprGeneric callee type_args args).
Proof.
  intros callee type_args args.
  induction args as [| a rest IH]; intros arg Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH arg Hin). simpl in IH. lia.
Qed.

Lemma expr_size_struct_field_lt : forall name lts args fields fname field_expr,
  In (fname, field_expr) fields ->
  expr_size field_expr < expr_size (EStruct name lts args fields).
Proof.
  intros name lts args fields.
  induction fields as [| [fname0 e0] rest IH]; intros fname field_expr Hin.
  - contradiction.
  - simpl in *. destruct Hin as [Heq | Hin].
    + injection Heq as _ <-. lia.
    + specialize (IH fname field_expr Hin). simpl in IH. lia.
Qed.

Lemma expr_size_struct_field_snd_lt : forall name lts args fields field_expr,
  In field_expr (map snd fields) ->
  expr_size field_expr < expr_size (EStruct name lts args fields).
Proof.
  intros name lts args fields.
  induction fields as [| [fname e] rest IH]; intros field_expr Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst field_expr. simpl. lia.
    + specialize (IH field_expr Hin).
      eapply Nat.lt_le_trans.
      * exact IH.
      * simpl. lia.
Qed.

Lemma expr_size_enum_payload_lt :
  forall enum_name variant_name lts variant_lts args payloads payload,
    In payload payloads ->
    expr_size payload <
      expr_size (EEnum enum_name variant_name lts variant_lts args payloads).
Proof.
  intros enum_name variant_name lts variant_lts args payloads.
  induction payloads as [| p rest IH]; intros payload Hin.
  - contradiction.
  - simpl in *. destruct Hin as [<- | Hin].
    + lia.
    + specialize (IH payload Hin). simpl in IH. lia.
Qed.

Lemma expr_size_match_scrutinee_lt :
  forall scrut branches,
    expr_size scrut < expr_size (EMatch scrut branches).
Proof.
  intros. simpl. lia.
Qed.

Lemma expr_size_match_branch_lt :
  forall scrut branches variant binders branch,
    In (variant, binders, branch) branches ->
    expr_size branch < expr_size (EMatch scrut branches).
Proof.
  intros scrut branches.
  induction branches as [| [[name binders0] e] rest IH];
    intros variant binders branch Hin.
  - contradiction.
  - simpl in *. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. lia.
    + specialize (IH variant binders branch Hin). simpl in IH. lia.
Qed.
