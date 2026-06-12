From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance CheckerBase CheckerTraits CheckerHrt CheckerClosure CheckerOrdinary CheckerEnvHelpers CheckerCore CheckerEnvCore CheckerState CheckerStateCore CheckerElabCore CheckerRootsCore CheckerRootsShadow CheckerAssocRootsShadow.
From Stdlib Require Import List String Bool ZArith.
Import ListNotations.

Definition infer_body (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx) (e : expr)
    : infer_result (Ty * ctx) :=
  infer_core fenv Ω n Γ e.

(* ------------------------------------------------------------------ *)
(* Argument collection helper for ECall soundness                        *)
(* ------------------------------------------------------------------ *)

Fixpoint infer_args_collect (fenv : list fn_def) (Ω : outlives_ctx) (n : nat) (Γ : ctx)
    (args : list expr) : infer_result (list Ty * ctx) :=
  match args with
  | [] => infer_ok ([], Γ)
  | e :: es =>
      match infer_core fenv Ω n Γ e with
      | infer_err err => infer_err err
      | infer_ok (T_e, Γ1) =>
          match infer_args_collect fenv Ω n Γ1 es with
          | infer_err err => infer_err err
          | infer_ok (tys, Γ2) => infer_ok (T_e :: tys, Γ2)
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(* Function-definition-level type checker                                *)
(* ------------------------------------------------------------------ *)

Fixpoint params_ok_b (ps : list param) (Γ : ctx) : bool :=
  match ps with
  | [] => true
  | p :: ps' =>
      ctx_check_ok (param_name p) (param_ty p) Γ &&
      params_ok_b ps' Γ
  end.

Fixpoint wf_params_b (Δ : region_ctx) (ps : list param) : bool :=
  match ps with
  | [] => true
  | p :: ps' => wf_type_b Δ (param_ty p) && wf_params_b Δ ps'
  end.

Fixpoint string_in (x : string) (xs : list string) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else string_in x ys
  end.

Fixpoint duplicate_param_name_aux (seen : list string) (ps : list param) : option ident :=
  match ps with
  | [] => None
  | p :: ps' =>
      if string_in (fst (param_name p)) seen
      then Some (param_name p)
      else duplicate_param_name_aux (fst (param_name p) :: seen) ps'
  end.

Definition duplicate_param_name (ps : list param) : option ident :=
  duplicate_param_name_aux [] ps.

Definition check_fn_binding_params (Δ : region_ctx) (f : fn_def)
    : option infer_error :=
  if negb (wf_params_b Δ (fn_captures f))
  then Some ErrLifetimeLeak
  else
  if negb (wf_params_b Δ (fn_params f))
  then Some ErrLifetimeLeak
  else
  match duplicate_param_name (fn_binding_params f) with
  | Some x => Some (ErrDuplicateParam x)
  | None => None
  end.

Lemma string_in_false_not_in : forall x xs,
  string_in x xs = false ->
  ~ In x xs.
Proof.
  intros x xs.
  induction xs as [| y ys IH]; simpl; intros H Hin.
  - contradiction.
  - destruct (String.eqb x y) eqn:Heq.
    + discriminate.
    + destruct Hin as [Heq_xy | Hin].
      * subst y. rewrite String.eqb_refl in Heq. discriminate.
      * apply (IH H). exact Hin.
Qed.

Fixpoint string_names_unique_b (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: xs' => negb (string_in x xs') && string_names_unique_b xs'
  end.

Definition fn_name_strings (fns : list fn_def) : list string :=
  map (fun f => fst (fn_name f)) fns.

Definition enum_variant_names (e : enum_def) : list string :=
  map enum_variant_name (enum_variants e).

Definition top_level_names (env : global_env) : list string :=
  map struct_name (env_structs env) ++
  map enum_name (env_enums env) ++
  map trait_name (env_traits env) ++
  fn_name_strings (env_fns env).

Definition top_level_names_unique_b (env : global_env) : bool :=
  string_names_unique_b (top_level_names env).

Definition enum_variants_unique_b (e : enum_def) : bool :=
  string_names_unique_b (enum_variant_names e).

Definition enum_variant_names_unique_b (env : global_env) : bool :=
  forallb enum_variants_unique_b (env_enums env).

Definition global_names_unique_b (env : global_env) : bool :=
  top_level_names_unique_b env && enum_variant_names_unique_b env.

Lemma string_names_unique_b_nodup : forall xs,
  string_names_unique_b xs = true ->
  NoDup xs.
Proof.
  induction xs as [| x xs IH]; simpl; intros Hunique.
  - constructor.
  - apply andb_true_iff in Hunique.
    destruct Hunique as [Hfresh Hrest].
    apply negb_true_iff in Hfresh.
    constructor.
    + apply string_in_false_not_in. exact Hfresh.
    + apply IH. exact Hrest.
Qed.

Lemma NoDup_app_right : forall (A : Type) (xs ys : list A),
  NoDup (xs ++ ys) ->
  NoDup ys.
Proof.
  intros A xs.
  induction xs as [| x xs IH]; intros ys Hnodup.
  - simpl in Hnodup. exact Hnodup.
  - simpl in Hnodup. inversion Hnodup as [| ? ? _ Hnodup_tail]; subst.
    apply IH. exact Hnodup_tail.
Qed.

Lemma NoDup_app_left : forall (A : Type) (xs ys : list A),
  NoDup (xs ++ ys) ->
  NoDup xs.
Proof.
  intros A xs.
  induction xs as [| x xs IH]; intros ys Hnodup.
  - constructor.
  - simpl in Hnodup. inversion Hnodup as [| ? ? Hfresh Hnodup_tail]; subst.
    constructor.
    + intros Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IH with (ys := ys). exact Hnodup_tail.
Qed.

Lemma top_level_names_unique_b_nodup : forall env,
  top_level_names_unique_b env = true ->
  NoDup (top_level_names env).
Proof.
  intros env Hunique.
  unfold top_level_names_unique_b in Hunique.
  apply string_names_unique_b_nodup. exact Hunique.
Qed.

Lemma top_level_names_unique_b_fn_names_nodup : forall env,
  top_level_names_unique_b env = true ->
  NoDup (fn_name_strings (env_fns env)).
Proof.
  intros env Hunique.
  pose proof (top_level_names_unique_b_nodup env Hunique) as Hnodup.
  unfold top_level_names in Hnodup.
  apply (NoDup_app_right string
    (map struct_name (env_structs env) ++
     map enum_name (env_enums env) ++
     map trait_name (env_traits env))).
  repeat rewrite <- app_assoc. exact Hnodup.
Qed.

Lemma ctx_names_params_ctx_param_names : forall ps,
  ctx_names (params_ctx ps) = param_names ps.
Proof.
  induction ps as [| p ps IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma param_names_app : forall ps1 ps2,
  param_names (ps1 ++ ps2) = param_names ps1 ++ param_names ps2.
Proof.
  induction ps1 as [| p ps1 IH]; intros ps2.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma duplicate_param_name_aux_none_no_seen : forall seen ps x,
  duplicate_param_name_aux seen ps = None ->
  In x (param_names ps) ->
  ~ In (fst x) seen.
Proof.
  intros seen ps.
  revert seen.
  induction ps as [| p ps IH]; simpl; intros seen x Hnone Hin.
  - contradiction.
  - destruct (string_in (fst (param_name p)) seen) eqn:Hseen;
      try discriminate.
    destruct Hin as [Hx | Hin].
    + subst x. apply string_in_false_not_in. exact Hseen.
    + specialize (IH (fst (param_name p) :: seen) x Hnone Hin).
      intros Hfst. apply IH. right. exact Hfst.
Qed.

Lemma duplicate_param_name_aux_none_nodup_param_names : forall seen ps,
  duplicate_param_name_aux seen ps = None ->
  NoDup (param_names ps).
Proof.
  intros seen ps.
  revert seen.
  induction ps as [| p ps IH]; simpl; intros seen Hnone.
  - constructor.
  - destruct (string_in (fst (param_name p)) seen) eqn:Hseen;
      try discriminate.
    constructor.
    + intros Hin.
      pose proof (duplicate_param_name_aux_none_no_seen
        (fst (param_name p) :: seen) ps (param_name p) Hnone Hin) as Hfresh.
      apply Hfresh. left. reflexivity.
    + apply (IH (fst (param_name p) :: seen)). exact Hnone.
Qed.

Lemma duplicate_param_name_none_nodup_params_ctx : forall ps,
  duplicate_param_name ps = None ->
  NoDup (ctx_names (params_ctx ps)).
Proof.
  intros ps Hnone.
  rewrite ctx_names_params_ctx_param_names.
  unfold duplicate_param_name in Hnone.
  eapply duplicate_param_name_aux_none_nodup_param_names.
  exact Hnone.
Qed.

Lemma duplicate_param_name_none_nodup_params_ctx_prefix : forall ps caps,
  duplicate_param_name (ps ++ caps) = None ->
  NoDup (ctx_names (params_ctx ps)).
Proof.
  intros ps caps Hnone.
  rewrite ctx_names_params_ctx_param_names.
  pose proof (duplicate_param_name_none_nodup_params_ctx (ps ++ caps) Hnone)
    as Hnodup_all.
  rewrite ctx_names_params_ctx_param_names in Hnodup_all.
  rewrite param_names_app in Hnodup_all.
  eapply NoDup_app_left. exact Hnodup_all.
Qed.


(* Check a single function definition:
   - infer the body type
   - verify it matches fn_ret (core type + exact usage)
   - verify all linear/affine parameters are consumed *)
Definition infer (fenv : list fn_def) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_body fenv Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_b (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

(* Check all functions in the program *)
Definition check_program (fenv : list fn_def) : bool :=
  forallb (fun f =>
    match infer fenv f with
    | infer_ok _ => true
    | infer_err _ => false
    end) fenv.

Definition infer_env (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env body_env Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition fn_with_body (f : fn_def) (body : expr) : fn_def :=
  MkFnDef (fn_name f) (fn_lifetimes f) (fn_outlives f)
    (fn_captures f) (fn_params f) (fn_ret f) body
    (fn_type_params f) (fn_bounds f).

Fixpoint lookup_param_ty (x : ident) (ps : list param) : option Ty :=
  match ps with
  | [] => None
  | p :: ps' =>
      if ident_eqb x (param_name p)
      then Some (param_ty p)
      else lookup_param_ty x ps'
  end.

Definition mixed_forall_type_generic_fn_ty_b (T : Ty) : bool :=
  match ty_core T with
  | TForall _ _ body =>
      match ty_core body with
      | TTypeForall _ _ inner =>
          match ty_core inner with
          | TFn _ _ => true
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

Definition cleanup_mixed_param_call_expr (ps : list param) (e : expr) : expr :=
  match e with
  | ECallExprGeneric (EVar x) _ args =>
      match lookup_param_ty x ps with
      | Some T =>
          if mixed_forall_type_generic_fn_ty_b T
          then ECallExpr (EVar x) args
          else e
      | None => e
      end
  | _ => e
  end.

Definition infer_env_elab (env : global_env) (f : fn_def)
    : infer_result (Ty * ctx * fn_def) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_elab body_env Ω n (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, body') =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out,
               fn_with_body f (cleanup_mixed_param_call_expr (fn_params f) body'))
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots_shadow_safe
    (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots_shadow_safe
          body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots_shadow_safe_checked
    (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots_shadow_safe_checked
          body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Definition infer_env_roots_shadow_safe_checked_assoc
    (env : global_env) (f : fn_def) (R0 : root_env)
    : infer_result (Ty * ctx * root_env * root_set) :=
  let n := fn_lifetimes f in
  let Ω := fn_outlives f in
  let Δ := mk_region_ctx n in
  let body_env := global_env_with_local_bounds env (fn_bounds f) in
  if negb (wf_outlives_b Δ Ω)
  then infer_err ErrLifetimeLeak
  else
  if negb (wf_type_b Δ (fn_ret f))
  then infer_err ErrLifetimeLeak
  else
  match check_fn_binding_params Δ f with
  | Some err => infer_err err
  | None =>
  match infer_core_env_roots_shadow_safe_checked_assoc
          body_env Ω n R0 (fn_body_ctx f) (fn_body f) with
  | infer_err err => infer_err err
  | infer_ok (T_body, Γ_out, R_out, roots) =>
      if negb (wf_type_b Δ T_body)
      then infer_err ErrLifetimeLeak
      else
      if ty_compatible_b Ω T_body (fn_ret f) then
        if params_ok_env_b env (fn_params f) Γ_out
        then infer_ok (fn_ret f, Γ_out, R_out, roots)
        else infer_err ErrContextCheckFailed
      else infer_err (compatible_error T_body (fn_ret f))
  end
  end.

Lemma infer_env_params_nodup : forall env f T Γ',
  infer_env env f = infer_ok (T, Γ') ->
  NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f T Γ' Hinfer.
  unfold infer_env in Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  unfold check_fn_binding_params in Hinfer.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_captures f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (duplicate_param_name (fn_binding_params f)) as [dup |] eqn:Hdup;
    try discriminate.
  unfold fn_binding_params in Hdup.
  eapply duplicate_param_name_none_nodup_params_ctx_prefix. exact Hdup.
Qed.

Lemma infer_env_roots_params_nodup : forall env f R0 T Γ' R' roots,
  infer_env_roots env f R0 = infer_ok (T, Γ', R', roots) ->
  NoDup (ctx_names (params_ctx (fn_params f))).
Proof.
  intros env f R0 T Γ' R' roots Hinfer.
  unfold infer_env_roots in Hinfer.
  destruct (negb (wf_outlives_b (mk_region_ctx (fn_lifetimes f)) (fn_outlives f)));
    try discriminate.
  destruct (negb (wf_type_b (mk_region_ctx (fn_lifetimes f)) (fn_ret f)));
    try discriminate.
  unfold check_fn_binding_params in Hinfer.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_captures f)));
    try discriminate.
  destruct (negb (wf_params_b (mk_region_ctx (fn_lifetimes f)) (fn_params f)));
    try discriminate.
  destruct (duplicate_param_name (fn_binding_params f)) as [dup |] eqn:Hdup;
    try discriminate.
  unfold fn_binding_params in Hdup.
  eapply duplicate_param_name_none_nodup_params_ctx_prefix. exact Hdup.
Qed.

