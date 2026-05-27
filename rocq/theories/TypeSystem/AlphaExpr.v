From Facet.TypeSystem Require Import Types Syntax Renaming.
From Facet.TypeSystem Require Import AlphaCore AlphaPlace.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Expression alpha-renaming relations                                 *)
(* ------------------------------------------------------------------ *)

Inductive expr_alpha : rename_env -> expr -> expr -> Prop :=
  | EA_Unit : forall ρ,
      expr_alpha ρ EUnit EUnit
  | EA_Lit : forall ρ l,
      expr_alpha ρ (ELit l) (ELit l)
  | EA_Var : forall ρ x,
      ~ In x (rename_range ρ) ->
      expr_alpha ρ (EVar x) (EVar (lookup_rename x ρ))
  | EA_Fn : forall ρ fname,
      expr_alpha ρ (EFn fname) (EFn fname)
  | EA_MakeClosure : forall ρ fname captures,
      expr_alpha ρ
        (EMakeClosure fname captures)
        (EMakeClosure fname (map (fun x => lookup_rename x ρ) captures))
  | EA_Place : forall ρ p pr,
      place_alpha ρ p pr ->
      expr_alpha ρ (EPlace p) (EPlace pr)
  | EA_Let : forall ρ m x xr T e1 e1r e2 e2r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ((x, xr) :: ρ) e2 e2r ->
      expr_alpha ρ (ELet m x T e1 e2) (ELet m xr T e1r e2r)
  | EA_LetInfer : forall ρ m x xr e1 e1r e2 e2r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ((x, xr) :: ρ) e2 e2r ->
      expr_alpha ρ (ELetInfer m x e1 e2) (ELetInfer m xr e1r e2r)
  | EA_Call : forall ρ fname args argsr,
      exprs_alpha ρ args argsr ->
      expr_alpha ρ (ECall fname args) (ECall fname argsr)
  | EA_CallGeneric : forall ρ fname type_args args argsr,
      exprs_alpha ρ args argsr ->
      expr_alpha ρ
        (ECallGeneric fname type_args args)
        (ECallGeneric fname type_args argsr)
  | EA_CallExpr : forall ρ callee calleer args argsr,
      expr_alpha ρ callee calleer ->
      exprs_alpha ρ args argsr ->
      expr_alpha ρ (ECallExpr callee args) (ECallExpr calleer argsr)
  | EA_Struct : forall ρ name lts args fields fieldsr,
      fields_alpha ρ fields fieldsr ->
      expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)
  | EA_Enum : forall ρ enum_name variant_name lts args payloads payloadsr,
      exprs_alpha ρ payloads payloadsr ->
      expr_alpha ρ
        (EEnum enum_name variant_name lts args payloads)
        (EEnum enum_name variant_name lts args payloadsr)
  | EA_Match : forall ρ scrut scrutr branches branchesr,
      expr_alpha ρ
        (EMatch scrut branches)
        (EMatch scrutr branchesr)
  | EA_Replace : forall ρ p pr e er,
      place_alpha ρ p pr ->
      expr_alpha ρ e er ->
      expr_alpha ρ (EReplace p e) (EReplace pr er)
  | EA_Assign : forall ρ p pr e er,
      place_alpha ρ p pr ->
      expr_alpha ρ e er ->
      expr_alpha ρ (EAssign p e) (EAssign pr er)
  | EA_Borrow : forall ρ rk p pr,
      place_alpha ρ p pr ->
      expr_alpha ρ (EBorrow rk p) (EBorrow rk pr)
  | EA_Deref : forall ρ e er,
      expr_alpha ρ e er ->
      expr_alpha ρ (EDeref e) (EDeref er)
  | EA_Drop : forall ρ e er,
      expr_alpha ρ e er ->
      expr_alpha ρ (EDrop e) (EDrop er)
  | EA_If : forall ρ e1 e1r e2 e2r e3 e3r,
      expr_alpha ρ e1 e1r ->
      expr_alpha ρ e2 e2r ->
      expr_alpha ρ e3 e3r ->
      expr_alpha ρ (EIf e1 e2 e3) (EIf e1r e2r e3r)
with exprs_alpha : rename_env -> list expr -> list expr -> Prop :=
  | EAs_Nil : forall ρ,
      exprs_alpha ρ [] []
  | EAs_Cons : forall ρ e er es esr,
      expr_alpha ρ e er ->
      exprs_alpha ρ es esr ->
      exprs_alpha ρ (e :: es) (er :: esr)
with fields_alpha : rename_env -> list (string * expr) -> list (string * expr) -> Prop :=
  | FAs_Nil : forall ρ,
      fields_alpha ρ [] []
  | FAs_Cons : forall ρ name e er fields fieldsr,
      expr_alpha ρ e er ->
      fields_alpha ρ fields fieldsr ->
      fields_alpha ρ ((name, e) :: fields) ((name, er) :: fieldsr).

Definition same_param_shape (p pr : param) : Prop :=
  param_mutability p = param_mutability pr /\
  param_ty p = param_ty pr.

Inductive params_alpha : list param -> list param -> Prop :=
  | ParamsAlpha_Nil :
      params_alpha [] []
  | ParamsAlpha_Cons : forall p pr ps psr,
      same_param_shape p pr ->
      params_alpha ps psr ->
      params_alpha (p :: ps) (pr :: psr).

Lemma params_alpha_length :
  forall ps psr,
    params_alpha ps psr ->
    List.length ps = List.length psr.
Proof.
  intros ps psr Halpha.
  induction Halpha; simpl; congruence.
Qed.

