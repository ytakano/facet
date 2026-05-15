From Facet.TypeSystem Require Import Types Syntax PathState TypingRules.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Alpha renaming                                                       *)
(* ------------------------------------------------------------------ *)

Definition rename_env : Type := list (ident * ident).

Fixpoint ident_in (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: ys => if ident_eqb x y then true else ident_in x ys
  end.

Fixpoint lookup_rename (x : ident) (ρ : rename_env) : ident :=
  match ρ with
  | [] => x
  | (old, fresh) :: ρ' =>
      if ident_eqb x old then fresh else lookup_rename x ρ'
  end.

Fixpoint max_ident_index (base : string) (used : list ident) : nat :=
  match used with
  | [] => O
  | (base0, n) :: used' =>
      if String.eqb base base0
      then Nat.max n (max_ident_index base used')
      else max_ident_index base used'
  end.

Definition fresh_ident (x : ident) (used : list ident) : ident :=
  (fst x, S (max_ident_index (fst x) used)).

Fixpoint ctx_names (Γ : ctx) : list ident :=
  match Γ with
  | [] => []
  | (x, _, _, _) :: Γ' => x :: ctx_names Γ'
  end.

Fixpoint place_name (p : place) : ident :=
  match p with
  | PVar x    => x
  | PDeref q  => place_name q
  | PField q _ => place_name q
  end.

Fixpoint free_vars_expr (e : expr) : list ident :=
  match e with
  | EUnit => []
  | ELit _ => []
  | EVar x => [x]
  | EFn _ => []
  | EPlace p => [place_name p]
  | ELet _ x _ e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ELetInfer _ x e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
  | ECall _ args =>
      let fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end
      in go args
  | ECallExpr callee args =>
      let fix go (args0 : list expr) : list ident :=
        match args0 with
        | [] => []
        | arg :: rest => free_vars_expr arg ++ go rest
        end
      in free_vars_expr callee ++ go args
  | EStruct _ _ _ fields =>
      let fix go (fields0 : list (string * expr)) : list ident :=
        match fields0 with
        | [] => []
        | (_, e) :: rest => free_vars_expr e ++ go rest
        end
      in go fields
  | EReplace p e_new => place_name p :: free_vars_expr e_new
  | EAssign p e_new => place_name p :: free_vars_expr e_new
  | EBorrow _ p => [place_name p]
  | EDeref e1 => free_vars_expr e1
  | EDrop e1 => free_vars_expr e1
  | EIf e1 e2 e3 => free_vars_expr e1 ++ free_vars_expr e2 ++ free_vars_expr e3
  end.

Fixpoint param_names (ps : list param) : list ident :=
  match ps with
  | [] => []
  | p :: ps' => param_name p :: param_names ps'
  end.

Fixpoint rename_place (ρ : rename_env) (p : place) : place :=
  match p with
  | PVar x   => PVar (lookup_rename x ρ)
  | PDeref q => PDeref (rename_place ρ q)
  | PField q f => PField (rename_place ρ q) f
  end.

Fixpoint alpha_rename_expr (ρ : rename_env) (used : list ident)
    (e : expr) : expr * list ident :=
  match e with
  | EUnit => (EUnit, used)
  | ELit l => (ELit l, used)
  | EVar x => (EVar (lookup_rename x ρ), used)
  | EFn fname => (EFn fname, used)
  | EPlace p => (EPlace (rename_place ρ p), used)
  | ECall fname args =>
      let fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1) := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1 rest in
            (arg' :: rest', used2)
        end
      in
      let (args', used') := go used args in
      (ECall fname args', used')
  | ECallExpr callee args =>
      let (callee', used1) := alpha_rename_expr ρ used callee in
      let fix go (used0 : list ident) (args0 : list expr)
          : list expr * list ident :=
        match args0 with
        | [] => ([], used0)
        | arg :: rest =>
            let (arg', used1') := alpha_rename_expr ρ used0 arg in
            let (rest', used2) := go used1' rest in
            (arg' :: rest', used2)
        end
      in
      let (args', used') := go used1 args in
      (ECallExpr callee' args', used')
  | EStruct name lts args fields =>
      let fix go (used0 : list ident) (fields0 : list (string * expr))
          : list (string * expr) * list ident :=
        match fields0 with
        | [] => ([], used0)
        | (fname, e) :: rest =>
            let (e', used1) := alpha_rename_expr ρ used0 e in
            let (rest', used2) := go used1 rest in
            ((fname, e') :: rest', used2)
        end
      in
      let (fields', used') := go used fields in
      (EStruct name lts args fields', used')
  | EReplace p e_new =>
      let (e_new', used') := alpha_rename_expr ρ used e_new in
      (EReplace (rename_place ρ p) e_new', used')
  | EAssign p e_new =>
      let (e_new', used') := alpha_rename_expr ρ used e_new in
      (EAssign (rename_place ρ p) e_new', used')
  | EBorrow rk p =>
      (EBorrow rk (rename_place ρ p), used)
  | EDeref e1 =>
      let (e1', used') := alpha_rename_expr ρ used e1 in
      (EDeref e1', used')
  | EDrop e1 =>
      let (e1', used') := alpha_rename_expr ρ used e1 in
      (EDrop e1', used')
  | ELet m x T e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELet m x' T e1' e2', used3)
  | ELetInfer m x e1 e2 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let used1' := x :: free_vars_expr e2 ++ used1 in
      let x' := fresh_ident x used1' in
      let used2 := x' :: used1' in
      let (e2', used3) := alpha_rename_expr ((x, x') :: ρ) used2 e2 in
      (ELetInfer m x' e1' e2', used3)
  | EIf e1 e2 e3 =>
      let (e1', used1) := alpha_rename_expr ρ used e1 in
      let (e2', used2) := alpha_rename_expr ρ used1 e2 in
      let (e3', used3) := alpha_rename_expr ρ used2 e3 in
      (EIf e1' e2' e3', used3)
  end.

Fixpoint alpha_rename_params (ρ : rename_env) (used : list ident)
    (ps : list param) : list param * rename_env * list ident :=
  match ps with
  | [] => ([], ρ, used)
  | p :: ps' =>
      let x := param_name p in
      let x' := fresh_ident x used in
      let p' := MkParam (param_mutability p) x' (param_ty p) in
      let '(ps'', ρ', used') :=
        alpha_rename_params ((x, x') :: ρ) (x' :: used) ps' in
      (p' :: ps'', ρ', used')
  end.

Definition alpha_rename_fn_def (used : list ident)
    (f : fn_def) : fn_def * list ident :=
  let used0 := param_names (fn_params f) ++ free_vars_expr (fn_body f) ++ used in
  let '(params', ρ, used1) := alpha_rename_params [] used0 (fn_params f) in
  let (body', used2) := alpha_rename_expr ρ used1 (fn_body f) in
  (MkFnDef (fn_name f) (fn_lifetimes f) (fn_outlives f) params' (fn_ret f) body', used2).

Fixpoint alpha_rename_syntax_go (used : list ident) (s : Syntax)
    : Syntax * list ident :=
  match s with
  | [] => ([], used)
  | f :: fs =>
      let (f', used1) := alpha_rename_fn_def used f in
      let (fs', used2) := alpha_rename_syntax_go used1 fs in
      (f' :: fs', used2)
  end.

Definition alpha_rename_syntax (s : Syntax) : Syntax :=
  fst (alpha_rename_syntax_go [] s).

Definition alpha_rename_for_infer (Γ : ctx) (fenv : list fn_def)
    (e : expr) : list fn_def * expr :=
  let (fenv', used) :=
    alpha_rename_syntax_go (free_vars_expr e ++ ctx_names Γ) fenv in
  let (e', _) := alpha_rename_expr [] used e in
  (fenv', e').
