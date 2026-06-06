From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Ordinary place, field, branch, and parameter helpers                *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_place (Γ : ctx) (p : place) : infer_result Ty :=
  match p with
  | PVar x =>
      match ctx_lookup_b x Γ with
      | None => infer_err (ErrUnknownVar x)
      | Some (_, true) => infer_err (ErrAlreadyConsumed x)
      | Some (T, false) => infer_ok T
      end
  | PDeref q =>
      match infer_place Γ q with
      | infer_err err => infer_err err
      | infer_ok Tq =>
          match ty_core Tq with
          | TRef _ _ T => infer_ok T
          | c => infer_err (ErrNotAReference c)
          end
      end
  | PField _ _ => infer_err ErrNotImplemented
  end.

Definition lookup_field_b (name : string) (fields : list (string * expr)) : option expr :=
  let fix go fields0 :=
    match fields0 with
    | [] => None
    | (fname, e) :: rest =>
        if String.eqb name fname then Some e else go rest
    end
  in go fields.

Definition has_field_b (name : string) (fields : list (string * expr)) : bool :=
  match lookup_field_b name fields with
  | Some _ => true
  | None => false
  end.

Definition first_duplicate_field (fields : list (string * expr)) : option string :=
  let fix go fields0 :=
    match fields0 with
    | [] => None
    | (name, _) :: rest =>
        if has_field_b name rest then Some name else go rest
    end
  in go fields.

Fixpoint first_unknown_field
    (fields : list (string * expr)) (defs : list field_def) : option string :=
  match fields with
  | [] => None
  | (name, _) :: rest =>
      match lookup_field name defs with
      | Some _ => first_unknown_field rest defs
      | None => Some name
      end
  end.

Fixpoint first_missing_field
    (defs : list field_def) (fields : list (string * expr)) : option string :=
  match defs with
  | [] => None
  | f :: rest =>
      if has_field_b (field_name f) fields
      then first_missing_field rest fields
      else Some (field_name f)
  end.

Definition lookup_branch_b (name : string)
    (branches : list (string * list ident * expr))
    : option expr :=
  lookup_expr_branch name branches.

Fixpoint has_branch_b (name : string)
    (branches : list (string * list ident * expr)) : bool :=
  match branches with
  | [] => false
  | (name', _, _) :: rest =>
      if String.eqb name name' then true else has_branch_b name rest
  end.

Fixpoint first_duplicate_branch
    (branches : list (string * list ident * expr)) : option string :=
  match branches with
  | [] => None
  | b :: rest =>
      let name := match_branch_name b in
      if has_branch_b name rest then Some name else first_duplicate_branch rest
  end.

Fixpoint first_unknown_variant_branch
    (branches : list (string * list ident * expr))
    (defs : list enum_variant_def)
    : option string :=
  match branches with
  | [] => None
  | (name, _, _) :: rest =>
      match lookup_enum_variant name defs with
      | Some _ => first_unknown_variant_branch rest defs
      | None => Some name
      end
  end.

Fixpoint first_missing_variant_branch
    (defs : list enum_variant_def)
    (branches : list (string * list ident * expr))
    : option string :=
  match defs with
  | [] => None
  | v :: rest =>
      if has_branch_b (enum_variant_name v) branches
      then first_missing_variant_branch rest branches
      else Some (enum_variant_name v)
  end.

Fixpoint first_payload_binder_branch
    (branches : list (string * list ident * expr)) : option string :=
  match branches with
  | [] => None
  | (name, [], _) :: rest => first_payload_binder_branch rest
  | (name, _ :: _, _) :: _ => Some name
  end.

Fixpoint first_payload_variant (defs : list enum_variant_def) : option string :=
  match defs with
  | [] => None
  | v :: rest =>
      match enum_variant_fields v with
      | [] => first_payload_variant rest
      | _ :: _ => Some (enum_variant_name v)
      end
  end.

Definition first_unsupported_match_payload
    (branches : list (string * list ident * expr))
    (defs : list enum_variant_def) : option string :=
  match first_payload_binder_branch branches with
  | Some name => Some name
  | None => first_payload_variant defs
  end.

Fixpoint usage_max_tys_nonempty (head : Ty) (tail : list Ty) : usage :=
  match tail with
  | [] => ty_usage head
  | t :: rest => usage_max (ty_usage head) (usage_max_tys_nonempty t rest)
  end.

Fixpoint ctx_merge_many (head : ctx) (tail : list ctx) : option ctx :=
  match tail with
  | [] => Some head
  | c :: rest =>
      match ctx_merge head c with
      | Some merged => ctx_merge_many merged rest
      | None => None
      end
  end.

Fixpoint match_binder_params (binders : list ident) (tys : list Ty)
    : infer_result (list param) :=
  match binders, tys with
  | [], [] => infer_ok []
  | x :: xs, T :: Ts =>
      match match_binder_params xs Ts with
      | infer_ok ps => infer_ok (MkParam MImmutable x T :: ps)
      | infer_err err => infer_err err
      end
  | _, _ => infer_err ErrArityMismatch
  end.

Definition instantiate_enum_variant_field_tys
    (lts : list lifetime) (args : list Ty) (v : enum_variant_def) : list Ty :=
  map (instantiate_enum_variant_field_ty lts args) (enum_variant_fields v).

Definition match_payload_params
    (binders : list ident) (lts : list lifetime) (args : list Ty)
    (v : enum_variant_def) : infer_result (list param) :=
  match_binder_params binders (instantiate_enum_variant_field_tys lts args v).

Lemma match_binder_params_names :
  forall binders tys ps,
    match_binder_params binders tys = infer_ok ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  induction binders as [| x xs IH]; intros tys ps Hmatch;
    destruct tys as [| T Ts]; simpl in Hmatch; try discriminate.
  - inversion Hmatch. reflexivity.
  - destruct (match_binder_params xs Ts) as [ps_tail | err] eqn:Htail;
      try discriminate.
    inversion Hmatch; subst ps; simpl.
    rewrite (IH Ts ps_tail Htail). reflexivity.
Qed.

Lemma match_payload_params_names :
  forall binders lts args v ps,
    match_payload_params binders lts args v = infer_ok ps ->
    ctx_names (params_ctx ps) = binders.
Proof.
  intros binders lts args v ps Hmatch.
  unfold match_payload_params in Hmatch.
  eapply match_binder_params_names. exact Hmatch.
Qed.

Definition ctx_add_params (ps : list param) (Γ : ctx) : ctx :=
  params_ctx ps ++ Γ.

Fixpoint ctx_remove_params (ps : list param) (Γ : ctx) : ctx :=
  match ps with
  | [] => Γ
  | p :: rest => ctx_remove_params rest (ctx_remove_b (param_name p) Γ)
  end.

Fixpoint ctx_check_ok_params (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      ctx_check_ok (param_name p) (param_ty p) Γ &&
      ctx_check_ok_params rest Γ
  end.

Fixpoint ident_in_b (x : ident) (xs : list ident) : bool :=
  match xs with
  | [] => false
  | y :: rest => ident_eqb x y || ident_in_b x rest
  end.

Fixpoint ident_nodup_b (xs : list ident) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (ident_in_b x rest) && ident_nodup_b rest
  end.

Definition params_names_nodup_b (ps : list param) : bool :=
  ident_nodup_b (ctx_names (params_ctx ps)).

Fixpoint ctx_lookup_params_none_b (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: rest =>
      match ctx_lookup_state (param_name p) Γ with
      | Some _ => false
      | None => ctx_lookup_params_none_b rest Γ
      end
  end.

Fixpoint unrestricted_unit_params_of_binders (binders : list ident) : list param :=
  match binders with
  | [] => []
  | x :: rest =>
      MkParam MImmutable x (MkTy UUnrestricted TUnits) ::
        unrestricted_unit_params_of_binders rest
  end.
