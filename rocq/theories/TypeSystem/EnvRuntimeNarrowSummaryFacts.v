From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules RootProvenance TypeChecker RuntimeTyping
  EnvStructuralRules CheckerSoundness AlphaRenaming EnvTypingSoundness
  TypeSafetyBasePreservationMutual TypeSafetyDirectCallWrappers
  TypeSafetyCheckedRoots.
From Facet.TypeSystem Require Export EnvRuntimeFunctionValueCallFacts.
From Stdlib Require Import List Bool Lia String Program.Equality.
Import ListNotations.

Inductive expr_root_shadow_store_safe_narrow_summary
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSSN_FunctionValueCall : forall R Σ x args T_callee Σ_callee
      R_callee roots_callee T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
        T_callee Σ_callee R_callee roots_callee ->
      supported_non_type_generic_function_value_call_callee_shape T_callee ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExpr (EVar x) args) T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ECallExpr (EVar x) args) T Σ' R' roots roots
  | ERSSN_TypeGenericFunctionValueCall : forall R Σ x type_args args inst_fuel
      T_callee Σ_callee R_callee roots_callee T Σ' R' roots,
      store_safe_function_value_call_args env args ->
      Forall (fun T => contains_lbound_ty T = false) type_args ->
      Forall (fun T => match ty_core T with TForall _ _ _ => False | _ => True end)
        type_args ->
      check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
        check_expr_root_shadow_store_safe_narrow_summary_fuel inst_fuel
        env type_args = true ->
      typed_env_roots_shadow_safe env Omega n R Σ (EVar x)
        T_callee Σ_callee R_callee roots_callee ->
      supported_type_generic_function_value_call_callee_shape T_callee ->
      (forall type_params bounds body,
          ty_core T_callee = TTypeForall type_params bounds body ->
          Datatypes.length type_args = type_params) ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (ECallExprGeneric (EVar x) type_args args) T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ECallExprGeneric (EVar x) type_args args) T Σ' R' roots roots
  | ERSSN_Let : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      non_function_value_ty_b T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSSN_LetInfer : forall R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      non_function_value_ty_b T1 = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      sctx_check_ok env x T1 Sigma2 = true ->
      roots_exclude x roots2 ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) roots2 ret_roots
  | ERSSN_BorrowDirect : forall R Σ rk p T Σ' R' roots x path,
      typed_env_roots_shadow_safe env Omega n R Σ (EBorrow rk p)
        T Σ' R' roots ->
      place_path p = Some (x, path) ->
      singleton_store_root roots = Some x ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EBorrow rk p) T Σ' R' roots roots
  | ERSSN_BorrowUniqueResolvedWritableChain : forall R Σ p T Σ' R' roots x,
      typed_env_roots_shadow_safe env Omega n R Σ (EBorrow RUnique p)
        T Σ' R' roots ->
      place_path p = None ->
      place_resolved_write_writable_chain env R Σ p ->
      place_resolved_write_target R p = Some x ->
      singleton_store_root roots = Some x ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EBorrow RUnique p) T Σ' R' roots roots
  | ERSSN_Unit : forall R Σ T Σ' R' roots,
      typed_env_roots_shadow_safe env Omega n R Σ EUnit T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ EUnit T Σ' R' roots roots
  | ERSSN_EmptyStructRootless : forall R Σ name lts args T Σ' R' roots sdef,
      lookup_struct name env = Some sdef ->
      struct_bounds sdef = [] ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (EStruct name lts args []) T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EStruct name lts args []) T Σ' R' roots []
  | ERSSN_AssignLit : forall R Σ p lit T Σ' R' roots,
      typed_env_roots_shadow_safe env Omega n R Σ (EAssign p (ELit lit))
        T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EAssign p (ELit lit)) T Σ' R' roots roots
  | ERSSN_AssignGenericDirect : forall R Σ x fname type_args T Σ' R'
      roots fcallee T_body Sigma_body R_body roots_body ret_roots_body
      sname lts tys,
      In fcallee (env_fns env) ->
      fn_name fcallee = fname ->
      Datatypes.length type_args = fn_type_params fcallee ->
      fn_bounds fcallee = [] ->
      fn_params fcallee = [] ->
      subst_type_params_ctx type_args (fn_body_ctx fcallee) = [] ->
      subst_type_params_expr type_args (fn_body fcallee) =
        EStruct sname lts tys [] ->
      NoDup (ctx_names (params_ctx
        (apply_type_params type_args (fn_params fcallee)))) ->
      expr_root_shadow_store_safe_narrow_summary env (fn_outlives fcallee)
        (fn_lifetimes fcallee) (initial_root_env_for_fn fcallee)
        (sctx_of_ctx (subst_type_params_ctx type_args (fn_body_ctx fcallee)))
        (subst_type_params_expr type_args (fn_body fcallee)) T_body
        Sigma_body R_body roots_body ret_roots_body ->
      ty_compatible_b (fn_outlives fcallee) T_body
        (subst_type_params_ty type_args (fn_ret fcallee)) = true ->
      roots_exclude_params (apply_type_params type_args (fn_params fcallee))
        roots_body ->
      root_env_excludes_params (apply_type_params type_args (fn_params fcallee))
        R_body ->
      typed_env_roots_shadow_safe env Omega n R Σ
        (EAssign (PVar x) (ECallGeneric fname type_args [])) T Σ' R' roots ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EAssign (PVar x) (ECallGeneric fname type_args []))
        T Σ' R' roots roots
  | ERSSN_VarNonFunction : forall R Σ x T Σ' R' roots,
      typed_env_roots_shadow_safe env Omega n R Σ (EVar x) T Σ' R' roots ->
      non_function_value_ty_b T = true ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EVar x) T Σ' R' roots roots
  | ERSSN_DropPlaceDirect : forall R Σ p T Σ' R' roots x path,
      typed_env_roots_shadow_safe env Omega n R Σ (EDrop (EPlace p))
        T Σ' R' roots ->
      place_path p = Some (x, path) ->
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ (EDrop (EPlace p)) T Σ' R' roots roots.

Inductive expr_root_shadow_store_safe_narrow_summary_checked
    (env : global_env) (Omega : outlives_ctx) (n : nat)
    : root_env -> sctx -> expr -> Ty -> sctx -> root_env -> root_set ->
      root_set -> Prop :=
  | ERSSNC_Conservative : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e T Σ' R' roots ret_roots
  | ERSSNC_CaptureRefFreeResult : forall R Σ e T Σ' R' roots ret_roots,
      expr_root_shadow_store_safe_narrow_summary
        env Omega n R Σ e T Σ' R' roots ret_roots ->
      capture_ref_free_ty_b env T = true ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e T Σ' R' [] ret_roots
  | ERSSNC_DerefBorrowShared_CaptureRefFreeResult : forall R Σ p T Σ' R' roots,
      typed_env_roots_shadow_safe env Omega n R Σ
        (EDeref (EBorrow RShared p)) T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (EDeref (EBorrow RShared p)) T Σ' R' [] []
  | ERSSNC_EmptyStruct_CaptureRefFreeResult : forall R Σ name lts args T Σ' R' roots,
      typed_env_roots_shadow_safe env Omega n R Σ
        (EStruct name lts args []) T Σ' R' roots ->
      capture_ref_free_ty_b env T = true ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (EStruct name lts args []) T Σ' R' [] []
  | ERSSNC_Let_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      ty_compatible_b Omega T1 T_hidden = true ->
      non_function_value_ty_b T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) [] ret_roots
  | ERSSNC_Let_BoundCheckedCaptureRefFreeResult : forall R R1 R2 Σ Σ1 Sigma2 m x T_hidden T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e1 T1 Σ1 R1 [] ret_roots1 ->
      capture_ref_free_ty_b env T1 = true ->
      ty_compatible_b Omega T1 T_hidden = true ->
      non_function_value_ty_b T_hidden = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T_hidden m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T_hidden Sigma2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (ELet m x T_hidden e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) [] ret_roots
  | ERSSNC_LetInfer_BoundCheckedCaptureRefFreeResult : forall R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      typed_env_roots_shadow_safe env Omega n R Σ e1 T1 Σ1 R1 roots1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e1 T1 Σ1 R1 [] ret_roots1 ->
      capture_ref_free_ty_b env T1 = true ->
      non_function_value_ty_b T1 = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T1 Sigma2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) [] ret_roots
  | ERSSNC_LetInfer_CaptureRefFreeResult : forall R R1 R2 Σ Σ1 Sigma2 m x T1 e1 e2
      T2 roots1 roots2 ret_roots1 ret_roots,
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ e1 T1 Σ1 R1 roots1 ret_roots1 ->
      non_function_value_ty_b T1 = true ->
      root_env_lookup x R1 = None ->
      roots_exclude x roots1 ->
      root_env_excludes x R1 ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n (root_env_add x roots1 R1)
        (sctx_add x T1 m Σ1) e2 T2 Sigma2 R2 roots2 ret_roots ->
      capture_ref_free_ty_b env T2 = true ->
      sctx_check_ok env x T1 Sigma2 = true ->
      root_env_excludes x (root_env_remove x R2) ->
      expr_root_shadow_store_safe_narrow_summary_checked
        env Omega n R Σ (ELetInfer m x e1 e2) T2
        (sctx_remove x Sigma2) (root_env_remove x R2) [] ret_roots.

Lemma disjoint_names_evar_of_call_expr :
  forall x args ys,
    disjoint_names (free_vars_expr (ECallExpr (EVar x) args)) ys ->
    disjoint_names (free_vars_expr (EVar x)) ys.
Proof.
  intros x args ys Hdisj y Hy.
  simpl in Hy. destruct Hy as [Hy | Hy]; [subst y | contradiction].
  apply Hdisj. simpl. left. reflexivity.
Qed.

Lemma disjoint_names_evar_of_call_expr_generic :
  forall x type_args args ys,
    disjoint_names (free_vars_expr (ECallExprGeneric (EVar x) type_args args)) ys ->
    disjoint_names (free_vars_expr (EVar x)) ys.
Proof.
  intros x type_args args ys Hdisj y Hy.
  simpl in Hy. destruct Hy as [Hy | Hy]; [subst y | contradiction].
  apply Hdisj. simpl. left. reflexivity.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_function_value_call_intro :
  forall env Omega n rho Rr Sigmar x args er used used' T Sigma' R' roots
      T_callee_r Sigma_callee_r R_callee_r roots_callee_r,
    store_safe_function_value_call_args env args ->
    alpha_rename_expr rho used (ECallExpr (EVar x) args) = (er, used') ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar
      (EVar (lookup_rename x rho)) T_callee_r Sigma_callee_r
      R_callee_r roots_callee_r ->
    supported_non_type_generic_function_value_call_callee_shape T_callee_r ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar er T Sigma' R' roots ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T Sigma' R' roots roots.
Proof.
  intros env Omega n rho Rr Sigmar x args er used used' T Sigma' R' roots
    T_callee_r Sigma_callee_r R_callee_r roots_callee_r Hargs Hrename
    Hcallee Hshape Hcall.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) as [argsr used_args] eqn:Hargsr.
  inversion Hrename; subst er used'.
  eapply ERSSN_FunctionValueCall.
  - eapply store_safe_function_value_call_args_alpha_rename_call_go;
      eassumption.
  - exact Hcallee.
  - exact Hshape.
  - exact Hcall.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_type_generic_function_value_call_intro :
  forall env Omega n rho Rr Sigmar x type_args args inst_fuel er used used' T Sigma' R' roots
      T_callee_r Sigma_callee_r R_callee_r roots_callee_r,
    store_safe_function_value_call_args env args ->
    Forall (fun T => contains_lbound_ty T = false) type_args ->
    Forall (fun T => match ty_core T with TForall _ _ _ => False | _ => True end)
      type_args ->
    check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
      check_expr_root_shadow_store_safe_narrow_summary_fuel inst_fuel
      env type_args = true ->
    alpha_rename_expr rho used (ECallExprGeneric (EVar x) type_args args) = (er, used') ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar
      (EVar (lookup_rename x rho)) T_callee_r Sigma_callee_r
      R_callee_r roots_callee_r ->
    supported_type_generic_function_value_call_callee_shape T_callee_r ->
    (forall type_params bounds body,
        ty_core T_callee_r = TTypeForall type_params bounds body ->
        Datatypes.length type_args = type_params) ->
    typed_env_roots_shadow_safe env Omega n Rr Sigmar er T Sigma' R' roots ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T Sigma' R' roots roots.
Proof.
  intros env Omega n rho Rr Sigmar x type_args args inst_fuel er used used' T Sigma' R' roots
    T_callee_r Sigma_callee_r R_callee_r roots_callee_r Hargs Hclosed Hno_top
    Hinstantiated Hrename Hcallee Hshape Harity Hcall.
  simpl in Hrename.
  destruct ((fix go (used0 : list ident) (args0 : list expr)
      : list expr * list ident :=
      match args0 with
      | [] => ([], used0)
      | arg :: rest =>
          let (arg', used1) := alpha_rename_expr rho used0 arg in
          let (rest', used2) := go used1 rest in
          (arg' :: rest', used2)
      end) used args) as [argsr used_args] eqn:Hargsr.
  inversion Hrename; subst er used'.
  eapply ERSSN_TypeGenericFunctionValueCall.
  - eapply store_safe_function_value_call_args_alpha_rename_call_go;
      eassumption.
  - exact Hclosed.
  - exact Hno_top.
  - exact Hinstantiated.
  - exact Hcallee.
  - exact Hshape.
  - exact Harity.
  - exact Hcall.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_intro :
  forall env Omega n rho Rr Sigmar m x xr T_hidden e1 e2 er used used'
      e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
      T2 Sigma2r R2r roots2r ret_roots,
    alpha_rename_expr rho used (ELet m x T_hidden e1 e2) = (er, used') ->
    alpha_rename_expr rho used e1 = (e1r, used1) ->
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
    alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar e1r T1 Sigma1r R1r roots1r ret_roots1r ->
    ty_compatible_b Omega T1 T_hidden = true ->
    non_function_value_ty_b T_hidden = true ->
    root_env_lookup xr R1r = None ->
    roots_exclude xr roots1r ->
    root_env_excludes xr R1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add xr roots1r R1r)
      (sctx_add xr T_hidden m Sigma1r) e2r T2 Sigma2r R2r
      roots2r ret_roots ->
    sctx_check_ok env xr T_hidden Sigma2r = true ->
    roots_exclude xr roots2r ->
    root_env_excludes xr (root_env_remove xr R2r) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T2
      (sctx_remove xr Sigma2r) (root_env_remove xr R2r) roots2r
      ret_roots.
Proof.
  intros env Omega n rho Rr Sigmar m x xr T_hidden e1 e2 er used used'
    e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
    T2 Sigma2r R2r roots2r ret_roots Hrename He1 Hxr Hused2 He2
    Hsummary1 Hcompat Hnonfun Hlookup Hexcl_roots1 Hexcl_env1
    Hsummary2 Hcheck Hexcl_roots2 Hexcl_env2.
  subst xr used2.
  simpl in Hrename.
  rewrite He1 in Hrename.
  rewrite He2 in Hrename.
  inversion Hrename; subst er used'.
  eapply ERSSN_Let; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_infer_intro :
  forall env Omega n rho Rr Sigmar m x xr e1 e2 er used used'
      e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
      T2 Sigma2r R2r roots2r ret_roots,
    alpha_rename_expr rho used (ELetInfer m x e1 e2) = (er, used') ->
    alpha_rename_expr rho used e1 = (e1r, used1) ->
    xr = fresh_ident x (x :: free_vars_expr e2 ++ used1) ->
    used2 = xr :: x :: free_vars_expr e2 ++ used1 ->
    alpha_rename_expr ((x, xr) :: rho) used2 e2 = (e2r, used3) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar e1r T1 Sigma1r R1r roots1r ret_roots1r ->
    non_function_value_ty_b T1 = true ->
    root_env_lookup xr R1r = None ->
    roots_exclude xr roots1r ->
    root_env_excludes xr R1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add xr roots1r R1r)
      (sctx_add xr T1 m Sigma1r) e2r T2 Sigma2r R2r roots2r
      ret_roots ->
    sctx_check_ok env xr T1 Sigma2r = true ->
    roots_exclude xr roots2r ->
    root_env_excludes xr (root_env_remove xr R2r) ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n Rr Sigmar er T2
      (sctx_remove xr Sigma2r) (root_env_remove xr R2r) roots2r
      ret_roots.
Proof.
  intros env Omega n rho Rr Sigmar m x xr e1 e2 er used used'
    e1r used1 used2 e2r used3 T1 Sigma1r R1r roots1r ret_roots1r
    T2 Sigma2r R2r roots2r ret_roots Hrename He1 Hxr Hused2 He2
    Hsummary1 Hnonfun Hlookup Hexcl_roots1 Hexcl_env1 Hsummary2
    Hcheck Hexcl_roots2 Hexcl_env2.
  subst xr used2.
  simpl in Hrename.
  rewrite He1 in Hrename.
  rewrite He2 in Hrename.
  inversion Hrename; subst er used'.
  eapply ERSSN_LetInfer; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_init_support :
  forall rho R Rr roots rootsr Sigma Sigmar xr,
    ctx_alpha rho Sigma Sigmar ->
    root_env_no_shadow R ->
    root_env_no_shadow Rr ->
    root_env_equiv Rr (root_env_rename rho R) ->
    root_set_equiv rootsr (root_set_rename rho roots) ->
    root_env_sctx_keys_named R Sigma ->
    root_env_sctx_roots_named R Sigma ->
    root_set_sctx_roots_named roots Sigma ->
    ~ In xr (ctx_names Sigmar) ->
    root_env_lookup xr Rr = None /\
    roots_exclude xr rootsr /\
    root_env_excludes xr Rr.
Proof.
  intros rho R Rr roots rootsr Sigma Sigmar xr Hctx Hrn Hrn_r HR
    Hroots Hkeys Hroot_names Hroot_set_names Hfresh.
  exact (root_env_sctx_support_fresh_renamed_let_init rho R Rr roots rootsr
    Sigma Sigmar xr Hctx Hrn Hrn_r HR Hroots Hkeys Hroot_names
    Hroot_set_names Hfresh).
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision :
  forall rho Sigma Sigma2 Sigmar R x xr T m,
    ctx_alpha rho Sigma Sigmar ->
    root_env_no_shadow R ->
    root_env_sctx_keys_named R Sigma2 ->
    sctx_same_bindings (sctx_add x T m Sigma) Sigma2 ->
    ~ In xr (ctx_names Sigmar) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R).
Proof.
  intros rho Sigma Sigma2 Sigmar R x xr T m Hctx Hrn Hkeys Hsame
    Hfresh Hnocoll.
  eapply root_env_remove_shadow_safe_rename_no_collision_on_same_bindings;
    eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    typed_env_roots_shadow_safe env Omega n R Σ e T Σ' R' roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - exact H2.
  - exact H6.
  - eapply TERS_Let; eauto.
  - eapply TERS_LetInfer; eauto.
  - exact H.
  - exact H.
  - exact H.
  - exact H1.
  - exact H.
  - exact H10.
  - exact H.
  - exact H.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision_from_summary :
  forall env Omega n rho Sigma1 Sigma2 Sigma1r R1 R2 roots1 roots2
      x xr T m e2 T2 ret_roots,
    ctx_alpha rho Sigma1 Sigma1r ->
    expr_root_shadow_store_safe_narrow_summary
      env Omega n (root_env_add x roots1 R1) (sctx_add x T m Sigma1)
      e2 T2 Sigma2 R2 roots2 ret_roots ->
    root_env_no_shadow (root_env_add x roots1 R1) ->
    root_env_sctx_keys_named (root_env_add x roots1 R1)
      (sctx_add x T m Sigma1) ->
    ~ In xr (ctx_names Sigma1r) ->
    rename_no_collision_on rho (root_env_names (root_env_remove x R2)) ->
    rename_no_collision_on ((x, xr) :: rho) (root_env_names R2).
Proof.
  intros env Omega n rho Sigma1 Sigma2 Sigma1r R1 R2 roots1 roots2
    x xr T m e2 T2 ret_roots Hctx Hsummary Hns_add Hkeys_add
    Hfresh Hnocoll.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n (root_env_add x roots1 R1) (sctx_add x T m Sigma1)
    e2 T2 Sigma2 R2 roots2 ret_roots Hsummary) as Htyped.
  assert (HnsR2 : root_env_no_shadow R2).
  { eapply typed_env_roots_no_shadow.
    - eapply typed_env_roots_shadow_safe_roots. exact Htyped.
    - exact Hns_add. }
  assert (HkeysR2 : root_env_sctx_keys_named R2 Sigma2).
  { destruct (typed_roots_shadow_safe_sctx_keys_named_mutual env Omega n)
      as [Hkeys_env _].
    eapply Hkeys_env; eassumption. }
  assert (Hsame : sctx_same_bindings (sctx_add x T m Sigma1) Sigma2).
  { eapply typed_env_structural_same_bindings.
    eapply typed_env_roots_structural.
    eapply typed_env_roots_shadow_safe_roots. exact Htyped. }
  eapply expr_root_shadow_store_safe_narrow_summary_alpha_rename_let_body_no_collision;
    eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed :
  forall env Omega n R Σ e T Σ' R' roots ret_roots s s',
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    store_typed env s Σ ->
    root_env_no_shadow R ->
    root_env_store_roots_named R s ->
    root_env_store_keys_named R s ->
    store_typed env s' Σ' ->
    root_env_no_shadow R' ->
    root_env_store_roots_named R' s' /\
    root_set_store_roots_named roots s' /\
    root_env_store_keys_named R' s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots s s'
    Hsummary Hstore Hrn Hnamed Hkeys Hstore' Hrn'.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n R Σ e T Σ' R' roots ret_roots Hsummary)
    as Htyped_shadow.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ e T Σ' R' roots Htyped_shadow)
    as Htyped_roots.
  assert (Hctx_roots : root_env_ctx_roots_named R Σ)
    by (eapply root_env_store_roots_named_to_ctx; eassumption).
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ e T Σ' R' roots Htyped_roots Hrn Hctx_roots)
    as [Hctx_roots' Hctx_set'].
  assert (Hctx_keys : root_env_sctx_keys_named R Σ)
    by (eapply root_env_store_keys_named_to_ctx; eassumption).
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ e T Σ' R' roots Htyped_shadow
    Hrn Hctx_keys) as Hctx_keys'.
  repeat split.
  - eapply root_env_ctx_roots_named_store_typed; eassumption.
  - eapply root_set_ctx_roots_named_store_typed; eassumption.
  - eapply root_env_ctx_keys_named_store_typed; eassumption.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_runtime_names_from_store_typed_prefix_ctx :
  forall env Omega n R Σ e T Σ' R' roots ret_roots s',
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_env_no_shadow R ->
    root_env_ctx_roots_named R Σ ->
    root_env_sctx_keys_named R Σ ->
    store_typed_prefix env s' Σ' ->
    root_env_no_shadow R' ->
    root_env_store_roots_named R' s' /\
    root_set_store_roots_named roots s' /\
    root_env_store_keys_named R' s'.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots s'
    Hsummary Hrn Hctx_roots Hctx_keys Hstore' Hrn'.
  pose proof (expr_root_shadow_store_safe_narrow_summary_typed
    env Omega n R Σ e T Σ' R' roots ret_roots Hsummary)
    as Htyped_shadow.
  pose proof (typed_env_roots_shadow_safe_roots
    env Omega n R Σ e T Σ' R' roots Htyped_shadow)
    as Htyped_roots.
  destruct (proj1 (typed_roots_ctx_roots_named_mutual env Omega n)
    R Σ e T Σ' R' roots Htyped_roots Hrn Hctx_roots)
    as [Hctx_roots' Hctx_set'].
  pose proof (proj1 (typed_roots_shadow_safe_sctx_keys_named_mutual
    env Omega n) R Σ e T Σ' R' roots Htyped_shadow
    Hrn Hctx_keys) as Hctx_keys'.
  repeat split.
  - eapply root_env_ctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_set_ctx_roots_named_store_typed_prefix; eassumption.
  - eapply root_env_ctx_keys_named_store_typed_prefix; eassumption.
Qed.

Lemma infer_core_env_roots_shadow_safe_evar_lookup_core_base :
  forall env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st,
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_out, R_out, roots) ->
    sctx_lookup x (sctx_of_ctx Γ) = Some (T_lookup, st) ->
    ty_core T_infer = ty_core T_lookup.
Proof.
  intros env Ω n R Γ x T_infer Γ_out R_out roots T_lookup st
    Hinfer Hlookup.
  unfold infer_core_env_roots_shadow_safe in Hinfer.
  cbn in Hinfer.
  unfold consume_direct_place_value_roots, infer_place_roots in Hinfer.
  cbn in Hinfer.
  rewrite Hlookup in Hinfer.
  destruct (binding_available_b st []) eqn:Havailable; try discriminate.
  destruct (root_env_lookup x R) as [roots0 |] eqn:Hroot; try discriminate.
  destruct (usage_eqb (ty_usage T_lookup) UUnrestricted) eqn:Husage.
  - inversion Hinfer; subst. reflexivity.
  - destruct (sctx_consume_path (sctx_of_ctx Γ) x []) as [Σc | err]
      eqn:Hconsume; try discriminate.
    inversion Hinfer; subst. reflexivity.
Qed.

Lemma typed_env_roots_shadow_safe_evar_infer_core_base :
  forall env Ω n R Γ x T_typed Σ_out R_out roots_typed
      T_infer Γ_infer R_infer roots_infer,
    typed_env_roots_shadow_safe env Ω n R (sctx_of_ctx Γ) (EVar x)
      T_typed Σ_out R_out roots_typed ->
    infer_core_env_roots_shadow_safe env Ω n R Γ (EVar x) =
      infer_ok (T_infer, Γ_infer, R_infer, roots_infer) ->
    ty_core T_infer = ty_core T_typed.
Proof.
  intros env Ω n R Γ x T_typed Σ_out R_out roots_typed
    T_infer Γ_infer R_infer roots_infer Htyped Hinfer.
  dependent destruction Htyped.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core_base; eassumption.
  - match goal with
    | Hplace : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace; subst
    end.
    eapply infer_core_env_roots_shadow_safe_evar_lookup_core_base; eassumption.
Qed.


Lemma typed_env_roots_shadow_safe_evar_core_eq_base :
  forall env Ω n R Σ x T1 Σ1 R1 roots1 T2 Σ2 R2 roots2,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x)
      T1 Σ1 R1 roots1 ->
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x)
      T2 Σ2 R2 roots2 ->
    ty_core T1 = ty_core T2.
Proof.
  intros env Ω n R Σ x T1 Σ1 R1 roots1 T2 Σ2 R2 roots2
    Htyped1 Htyped2.
  dependent destruction Htyped1; dependent destruction Htyped2;
    match goal with
    | Hplace1 : typed_place_env_structural _ _ (PVar _) _,
      Hplace2 : typed_place_env_structural _ _ (PVar _) _ |- _ =>
        inversion Hplace1; subst; inversion Hplace2; subst;
        match goal with
        | Hlookup1 : sctx_lookup ?x ?Σ = Some (?T1, _),
          Hlookup2 : sctx_lookup ?x ?Σ = Some (?T2, _) |- _ =>
            rewrite Hlookup1 in Hlookup2; inversion Hlookup2; subst;
            reflexivity
        end
    end.
Qed.

Lemma typed_env_roots_shadow_safe_evar_rename_no_collision_on_output_base :
  forall env Ω n rho R Σ x T Σ' R' roots,
    typed_env_roots_shadow_safe env Ω n R Σ (EVar x) T Σ' R' roots ->
    rename_no_collision_on rho (root_env_names R) ->
    rename_no_collision_on rho (root_env_names R').
Proof.
  intros env Ω n rho R Σ x T Σ' R' roots Htyped Hnocoll.
  dependent destruction Htyped; exact Hnocoll.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_roots_ret_equiv :
  forall env Omega n R Σ e T Σ' R' roots ret_roots,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    root_set_equiv roots ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots Hsummary.
  induction Hsummary.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
  - exact IHHsummary2.
  - exact IHHsummary2.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
  - inversion H1; subst.
    match goal with
    | Hfields : typed_fields_roots_shadow_safe _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        inversion Hfields; subst
    end.
    + apply root_set_equiv_refl.
    + match goal with
      | Hlookup : lookup_field_b _ [] = Some _ |- _ =>
          simpl in Hlookup; discriminate
      end.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
  - apply root_set_equiv_refl.
Qed.

Lemma expr_root_shadow_store_safe_narrow_summary_ret_roots_exclude :
  forall env Omega n R Σ e T Σ' R' roots ret_roots x,
    expr_root_shadow_store_safe_narrow_summary
      env Omega n R Σ e T Σ' R' roots ret_roots ->
    roots_exclude x roots ->
    roots_exclude x ret_roots.
Proof.
  intros env Omega n R Σ e T Σ' R' roots ret_roots x Hsummary Hexcl.
  eapply roots_exclude_equiv.
  - eapply expr_root_shadow_store_safe_narrow_summary_roots_ret_equiv.
    exact Hsummary.
  - exact Hexcl.
Qed.


Lemma expr_names_subst_type_params_expr :
  forall type_args e,
    expr_names (subst_type_params_expr type_args e) = expr_names e.
Proof.
  fix IH 2. intros type_args e.
  destruct e as
    [| lit | x | m x T e1 e2 | m x e1 e2 | fname | fname captures
     | p | fname args | fname type_args' args | ef args | ef type_args' args
     | name lts type_args' fields | enum_name variant lts variant_lts type_args' payloads
     | discr branches | p rhs | p rhs | rk p | e | e | e1 e2 e3];
    simpl; try reflexivity.
  - rewrite (IH type_args e1), (IH type_args e2). reflexivity.
  - rewrite (IH type_args e1), (IH type_args e2). reflexivity.
  - induction args as [| arg args IHargs]; simpl; auto.
    rewrite (IH type_args arg), IHargs. reflexivity.
  - induction args as [| arg args IHargs]; simpl; auto.
    rewrite (IH type_args arg), IHargs. reflexivity.
  - assert (Hargs :
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => expr_names arg ++ go rest
          end)
        ((fix go (es : list expr) : list expr :=
            match es with
            | [] => []
            | e' :: es' => subst_type_params_expr type_args e' :: go es'
            end) args)) =
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => expr_names arg ++ go rest
          end) args)).
    { induction args as [| arg args IHargs]; simpl; auto.
      rewrite (IH type_args arg), IHargs. reflexivity. }
    rewrite (IH type_args ef), Hargs. reflexivity.
  - assert (Hargs :
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => expr_names arg ++ go rest
          end)
        ((fix go (es : list expr) : list expr :=
            match es with
            | [] => []
            | e' :: es' => subst_type_params_expr type_args e' :: go es'
            end) args)) =
      ((fix go (args0 : list expr) : list ident :=
          match args0 with
          | [] => []
          | arg :: rest => expr_names arg ++ go rest
          end) args)).
    { induction args as [| arg args IHargs]; simpl; auto.
      rewrite (IH type_args arg), IHargs. reflexivity. }
    rewrite (IH type_args ef), Hargs. reflexivity.
  - induction fields as [| [field expr] fields IHfields]; simpl; auto.
    rewrite (IH type_args expr), IHfields. reflexivity.
  - induction payloads as [| payload payloads IHpayloads]; simpl; auto.
    rewrite (IH type_args payload), IHpayloads. reflexivity.
  - assert (Hbranches :
      ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
          match branches0 with
          | [] => []
          | (_, _, e) :: rest => expr_names e ++ go rest
          end)
        ((fix go (bs : list (string * list ident * expr))
            : list (string * list ident * expr) :=
            match bs with
            | [] => []
            | (name, binders, e') :: bs' =>
                (name, binders, subst_type_params_expr type_args e') :: go bs'
            end) branches)) =
      ((fix go (branches0 : list (string * list ident * expr)) : list ident :=
          match branches0 with
          | [] => []
          | (_, _, e) :: rest => expr_names e ++ go rest
          end) branches)).
    { induction branches as [| [[branch_name binders] branch] branches IHbranches];
        simpl; auto.
      rewrite (IH type_args branch), IHbranches. reflexivity. }
    rewrite (IH type_args discr), Hbranches. reflexivity.
  - rewrite (IH type_args rhs). reflexivity.
  - rewrite (IH type_args rhs). reflexivity.
  - rewrite (IH type_args e). reflexivity.
  - rewrite (IH type_args e). reflexivity.
  - rewrite (IH type_args e1), (IH type_args e2), (IH type_args e3).
    reflexivity.
Qed.

Lemma ctx_alpha_subst_type_params_ctx :
  forall type_args rho Gamma Gammar,
    ctx_alpha rho Gamma Gammar ->
    ctx_alpha rho
      (subst_type_params_ctx type_args Gamma)
      (subst_type_params_ctx type_args Gammar).
Proof.
  intros type_args rho Gamma Gammar Halpha.
  induction Halpha.
  - simpl. constructor.
  - simpl. constructor.
    + exact IHHalpha.
    + rewrite ctx_names_subst_type_params_ctx. exact H.
    + exact H0.
Qed.


Lemma alpha_rename_expr_subst_type_params_expr :
  forall type_args rho used e er used',
    alpha_rename_expr rho used e = (er, used') ->
    alpha_rename_expr rho used (subst_type_params_expr type_args e) =
      (subst_type_params_expr type_args er, used').
Proof.
  intros type_args.
  assert (Hsize : forall n rho used e er used',
    expr_size e < n ->
    alpha_rename_expr rho used e = (er, used') ->
    alpha_rename_expr rho used (subst_type_params_expr type_args e) =
      (subst_type_params_expr type_args er, used')).
  { induction n as [| n IH]; intros rho used e er used' Hlt Hrename.
    - lia.
    - destruct e as
        [| lit | x | m x T e1 e2 | m x e1 e2 | fname | fname captures
         | p | fname args | fname type_args0 args | callee args | callee type_args0 args
         | sname lts type_args0 fields | ename variant lts variant_lts type_args0 payloads
         | scrut branches | p rhs | p rhs | rk p | e | e | e1 e2 e3];
        simpl in Hrename |- *; try (inversion Hrename; subst; reflexivity).
      + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
        rewrite expr_names_subst_type_params_expr.
        destruct (alpha_rename_expr
          ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: rho)
          (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
            x :: free_vars_expr e2 ++ used1) e2)
          as [e2r used2] eqn:He2.
        injection Hrename as <- <-.
        rewrite (IH rho used e1 e1r used1); [| simpl in Hlt; lia | exact He1].
        simpl.
        rewrite (IH _ _ e2 e2r used2); [reflexivity | simpl in Hlt; lia | exact He2].
      + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
        rewrite expr_names_subst_type_params_expr.
        destruct (alpha_rename_expr
          ((x, fresh_ident x (x :: free_vars_expr e2 ++ used1)) :: rho)
          (fresh_ident x (x :: free_vars_expr e2 ++ used1) ::
            x :: free_vars_expr e2 ++ used1) e2)
          as [e2r used2] eqn:He2.
        injection Hrename as <- <-.
        rewrite (IH rho used e1 e1r used1); [| simpl in Hlt; lia | exact He1].
        simpl.
        rewrite (IH _ _ e2 e2r used2); [reflexivity | simpl in Hlt; lia | exact He2].
      + assert (Hargs : forall args0 used0 argsr usedr,
          (forall a, In a args0 -> In a args) ->
          ((fix go (used1 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used1)
              | arg :: rest =>
                  let (arg', used2) := alpha_rename_expr rho used1 arg in
                  let (rest', used3) := go used2 rest in
                  (arg' :: rest', used3)
              end) used0 args0) = (argsr, usedr) ->
          ((fix go (used1 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used1)
              | arg :: rest =>
                  let (arg', used2) := alpha_rename_expr rho used1 arg in
                  let (rest', used3) := go used2 rest in
                  (arg' :: rest', used3)
              end) used0
            ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) args0)) =
          ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) argsr, usedr)).
        { induction args0 as [| arg rest IHargs]; intros used0 argsr usedr Hincl Hgo; simpl in Hgo |- *.
          - inversion Hgo; subst. reflexivity.
          - destruct (alpha_rename_expr rho used0 arg) as [ar used1] eqn:Harg.
            destruct ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg0 :: rest0 =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg0 in
                  let (rest', used4) := go used3 rest0 in
                  (arg' :: rest', used4)
              end) used1 rest) as [restr used2] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used0 arg ar used1).
            + simpl.
              rewrite (IHargs used1 restr used2); auto.
              intros a Ha. apply Hincl. right. exact Ha.
            + pose proof (expr_size_call_arg_lt fname args arg (Hincl arg (or_introl eq_refl))). lia.
            + exact Harg. }
        destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used args) as [argsr used_args] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (Hargs args used argsr used_args (fun a H => H) Hgo). reflexivity.
      + assert (Hargs : forall args0 used0 argsr usedr,
          (forall a, In a args0 -> In a args) ->
          ((fix go (used1 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used1)
              | arg :: rest =>
                  let (arg', used2) := alpha_rename_expr rho used1 arg in
                  let (rest', used3) := go used2 rest in
                  (arg' :: rest', used3)
              end) used0 args0) = (argsr, usedr) ->
          ((fix go (used1 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used1)
              | arg :: rest =>
                  let (arg', used2) := alpha_rename_expr rho used1 arg in
                  let (rest', used3) := go used2 rest in
                  (arg' :: rest', used3)
              end) used0
            ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) args0)) =
          ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) argsr, usedr)).
        { induction args0 as [| arg rest IHargs]; intros used0 argsr usedr Hincl Hgo; simpl in Hgo |- *.
          - inversion Hgo; subst. reflexivity.
          - destruct (alpha_rename_expr rho used0 arg) as [ar used1] eqn:Harg.
            destruct ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg0 :: rest0 =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg0 in
                  let (rest', used4) := go used3 rest0 in
                  (arg' :: rest', used4)
              end) used1 rest) as [restr used2] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used0 arg ar used1).
            + simpl.
              rewrite (IHargs used1 restr used2); auto.
              intros a Ha. apply Hincl. right. exact Ha.
            + pose proof (expr_size_call_generic_arg_lt fname type_args0 args arg (Hincl arg (or_introl eq_refl))). lia.
            + exact Harg. }
        destruct ((fix go (used0 : list ident) (args0 : list expr) {struct args0}
          : list expr * list ident :=
          match args0 with
          | [] => ([], used0)
          | arg :: rest =>
              let (arg', used1) := alpha_rename_expr rho used0 arg in
              let (rest', used2) := go used1 rest in
              (arg' :: rest', used2)
          end) used args) as [argsr used_args] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (Hargs args used argsr used_args (fun a H => H) Hgo). reflexivity.
      + destruct (alpha_rename_expr rho used callee) as [calleer used0] eqn:Hcallee.
        assert (Hargs : forall args0 used1 argsr usedr,
          (forall a, In a args0 -> In a args) ->
          ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg :: rest =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg in
                  let (rest', used4) := go used3 rest in
                  (arg' :: rest', used4)
              end) used1 args0) = (argsr, usedr) ->
          ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg :: rest =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg in
                  let (rest', used4) := go used3 rest in
                  (arg' :: rest', used4)
              end) used1
            ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) args0)) =
          ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) argsr, usedr)).
        { induction args0 as [| arg rest IHargs]; intros used1 argsr usedr Hincl Hgo; simpl in Hgo |- *.
          - inversion Hgo; subst. reflexivity.
          - destruct (alpha_rename_expr rho used1 arg) as [ar used2] eqn:Harg.
            destruct ((fix go (used3 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used3)
              | arg0 :: rest0 =>
                  let (arg', used4) := alpha_rename_expr rho used3 arg0 in
                  let (rest', used5) := go used4 rest0 in
                  (arg' :: rest', used5)
              end) used2 rest) as [restr used3] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used1 arg ar used2).
            + simpl.
              rewrite (IHargs used2 restr used3); auto.
              intros a Ha. apply Hincl. right. exact Ha.
            + pose proof (expr_size_callexpr_arg_lt callee args arg (Hincl arg (or_introl eq_refl))). lia.
            + exact Harg. }
        destruct ((fix go (used1 : list ident) (args0 : list expr) {struct args0}
          : list expr * list ident :=
          match args0 with
          | [] => ([], used1)
          | arg :: rest =>
              let (arg', used2) := alpha_rename_expr rho used1 arg in
              let (rest', used3) := go used2 rest in
              (arg' :: rest', used3)
          end) used0 args) as [argsr used_args] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (IH rho used callee calleer used0); [| pose proof (expr_size_callexpr_callee_lt callee args); lia | exact Hcallee].
        simpl. rewrite (Hargs args used0 argsr used_args (fun a H => H) Hgo). reflexivity.
      + destruct (alpha_rename_expr rho used callee) as [calleer used0] eqn:Hcallee.
        assert (Hargs : forall args0 used1 argsr usedr,
          (forall a, In a args0 -> In a args) ->
          ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg :: rest =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg in
                  let (rest', used4) := go used3 rest in
                  (arg' :: rest', used4)
              end) used1 args0) = (argsr, usedr) ->
          ((fix go (used2 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used2)
              | arg :: rest =>
                  let (arg', used3) := alpha_rename_expr rho used2 arg in
                  let (rest', used4) := go used3 rest in
                  (arg' :: rest', used4)
              end) used1
            ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) args0)) =
          ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) argsr, usedr)).
        { induction args0 as [| arg rest IHargs]; intros used1 argsr usedr Hincl Hgo; simpl in Hgo |- *.
          - inversion Hgo; subst. reflexivity.
          - destruct (alpha_rename_expr rho used1 arg) as [ar used2] eqn:Harg.
            destruct ((fix go (used3 : list ident) (args1 : list expr) {struct args1}
              : list expr * list ident :=
              match args1 with
              | [] => ([], used3)
              | arg0 :: rest0 =>
                  let (arg', used4) := alpha_rename_expr rho used3 arg0 in
                  let (rest', used5) := go used4 rest0 in
                  (arg' :: rest', used5)
              end) used2 rest) as [restr used3] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used1 arg ar used2).
            + simpl.
              rewrite (IHargs used2 restr used3); auto.
              intros a Ha. apply Hincl. right. exact Ha.
            + pose proof (expr_size_callexpr_generic_arg_lt callee type_args0 args arg
                (Hincl arg (or_introl eq_refl))). lia.
            + exact Harg. }
        destruct ((fix go (used1 : list ident) (args0 : list expr) {struct args0}
          : list expr * list ident :=
          match args0 with
          | [] => ([], used1)
          | arg :: rest =>
              let (arg', used2) := alpha_rename_expr rho used1 arg in
              let (rest', used3) := go used2 rest in
              (arg' :: rest', used3)
          end) used0 args) as [argsr used_args] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (IH rho used callee calleer used0);
          [| pose proof (expr_size_callexpr_generic_callee_lt callee type_args0 args); lia
           | exact Hcallee].
        simpl. rewrite (Hargs args used0 argsr used_args (fun a H => H) Hgo). reflexivity.
      + assert (Hfields : forall fields0 used0 fieldsr usedr,
          (forall field e0, In (field, e0) fields0 -> In (field, e0) fields) ->
          ((fix go (used1 : list ident) (fields1 : list (string * expr)) {struct fields1}
              : list (string * expr) * list ident :=
              match fields1 with
              | [] => ([], used1)
              | (field, e0) :: rest =>
                  let (e0', used2) := alpha_rename_expr rho used1 e0 in
                  let (rest', used3) := go used2 rest in
                  ((field, e0') :: rest', used3)
              end) used0 fields0) = (fieldsr, usedr) ->
          ((fix go (used1 : list ident) (fields1 : list (string * expr)) {struct fields1}
              : list (string * expr) * list ident :=
              match fields1 with
              | [] => ([], used1)
              | (field, e0) :: rest =>
                  let (e0', used2) := alpha_rename_expr rho used1 e0 in
                  let (rest', used3) := go used2 rest in
                  ((field, e0') :: rest', used3)
              end) used0
            ((fix subst_go (fs : list (string * expr)) : list (string * expr) :=
              match fs with
              | [] => []
              | (field, e0) :: fs0 =>
                  (field, subst_type_params_expr type_args e0) :: subst_go fs0
              end) fields0)) =
          ((fix subst_go (fs : list (string * expr)) : list (string * expr) :=
              match fs with
              | [] => []
              | (field, e0) :: fs0 =>
                  (field, subst_type_params_expr type_args e0) :: subst_go fs0
              end) fieldsr, usedr)).
        { induction fields0 as [| [field e0] rest IHfields];
            intros used0 fieldsr usedr Hincl Hgo; simpl in Hgo |- *.
          - injection Hgo as <- <-. reflexivity.
          - destruct (alpha_rename_expr rho used0 e0) as [e0r used1] eqn:He0.
            destruct ((fix go (used2 : list ident) (fields1 : list (string * expr)) {struct fields1}
              : list (string * expr) * list ident :=
              match fields1 with
              | [] => ([], used2)
              | (field0, e1) :: rest0 =>
                  let (e1', used3) := alpha_rename_expr rho used2 e1 in
                  let (rest', used4) := go used3 rest0 in
                  ((field0, e1') :: rest', used4)
              end) used1 rest) as [restr used2] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used0 e0 e0r used1).
            + simpl.
              rewrite (IHfields used1 restr used2); auto.
              intros field0 e1 Hin. apply Hincl. right. exact Hin.
            + pose proof (expr_size_struct_field_lt sname lts type_args0 fields field e0
                (Hincl field e0 (or_introl eq_refl))). lia.
            + exact He0. }
        destruct ((fix go (used0 : list ident) (fields0 : list (string * expr)) {struct fields0}
          : list (string * expr) * list ident :=
          match fields0 with
          | [] => ([], used0)
          | (field, e0) :: rest =>
              let (e0', used1) := alpha_rename_expr rho used0 e0 in
              let (rest', used2) := go used1 rest in
              ((field, e0') :: rest', used2)
          end) used fields) as [fieldsr used_fields] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (Hfields fields used fieldsr used_fields
          (fun field e0 H => H) Hgo). reflexivity.
      + assert (Hpayloads : forall payloads0 used0 payloadsr usedr,
          (forall e0, In e0 payloads0 -> In e0 payloads) ->
          ((fix go (used1 : list ident) (payloads1 : list expr) {struct payloads1}
              : list expr * list ident :=
              match payloads1 with
              | [] => ([], used1)
              | e0 :: rest =>
                  let (e0', used2) := alpha_rename_expr rho used1 e0 in
                  let (rest', used3) := go used2 rest in
                  (e0' :: rest', used3)
              end) used0 payloads0) = (payloadsr, usedr) ->
          ((fix go (used1 : list ident) (payloads1 : list expr) {struct payloads1}
              : list expr * list ident :=
              match payloads1 with
              | [] => ([], used1)
              | e0 :: rest =>
                  let (e0', used2) := alpha_rename_expr rho used1 e0 in
                  let (rest', used3) := go used2 rest in
                  (e0' :: rest', used3)
              end) used0
            ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) payloads0)) =
          ((fix subst_go (es : list expr) : list expr :=
              match es with
              | [] => []
              | e0 :: es0 => subst_type_params_expr type_args e0 :: subst_go es0
              end) payloadsr, usedr)).
        { induction payloads0 as [| e0 rest IHpayloads];
            intros used0 payloadsr usedr Hincl Hgo; simpl in Hgo |- *.
          - injection Hgo as <- <-. reflexivity.
          - destruct (alpha_rename_expr rho used0 e0) as [e0r used1] eqn:He0.
            destruct ((fix go (used2 : list ident) (payloads1 : list expr) {struct payloads1}
              : list expr * list ident :=
              match payloads1 with
              | [] => ([], used2)
              | e1 :: rest0 =>
                  let (e1', used3) := alpha_rename_expr rho used2 e1 in
                  let (rest', used4) := go used3 rest0 in
                  (e1' :: rest', used4)
              end) used1 rest) as [restr used2] eqn:Hrest.
            injection Hgo as <- <-.
            rewrite (IH rho used0 e0 e0r used1).
            + simpl.
              rewrite (IHpayloads used1 restr used2); auto.
              intros e1 Hin. apply Hincl. right. exact Hin.
            + pose proof (expr_size_enum_payload_lt ename variant lts variant_lts type_args0 payloads e0
                (Hincl e0 (or_introl eq_refl))). lia.
            + exact He0. }
        destruct ((fix go (used0 : list ident) (payloads0 : list expr) {struct payloads0}
          : list expr * list ident :=
          match payloads0 with
          | [] => ([], used0)
          | e0 :: rest =>
              let (e0', used1) := alpha_rename_expr rho used0 e0 in
              let (rest', used2) := go used1 rest in
              (e0' :: rest', used2)
          end) used payloads) as [payloadsr used_payloads] eqn:Hgo.
        injection Hrename as <- <-.
        rewrite (Hpayloads payloads used payloadsr used_payloads
          (fun e0 H => H) Hgo). reflexivity.
      + (* EMatch *)
        destruct (alpha_rename_expr rho used scrut) as [scrutr used0] eqn:Hscrut.
        destruct ((fix go (used1 : list ident) (branches0 : list (string * list ident * expr)) {struct branches0}
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used1)
          | (variant_name, binders, e0) :: rest =>
              let binder_seed := binders ++ free_vars_expr e0 ++ used1 in
              let '(binders', rho_branch, used2) := alpha_rename_idents rho binder_seed binders in
              let (e0', used3) := alpha_rename_expr rho_branch used2 e0 in
              let (rest', used4) := go used3 rest in
              ((variant_name, binders', e0') :: rest', used4)
          end) used0 branches) as [branchesr used_branches] eqn:Hbranches.
        injection Hrename as <- <-.
        rewrite (IH rho used scrut scrutr used0); [| pose proof (expr_size_match_scrutinee_lt scrut branches); lia | exact Hscrut].
        simpl.
        assert (Hbranches_comm : forall branches0 used1 branchesr0 usedr,
          (forall name binders branch,
              In (name, binders, branch) branches0 ->
              In (name, binders, branch) branches) ->
          ((fix go (used2 : list ident) (branches1 : list (string * list ident * expr)) {struct branches1}
              : list (string * list ident * expr) * list ident :=
              match branches1 with
              | [] => ([], used2)
              | (variant_name, binders, e0) :: rest =>
                  let binder_seed := binders ++ free_vars_expr e0 ++ used2 in
                  let '(binders', rho_branch, used3) :=
                    alpha_rename_idents rho binder_seed binders in
                  let (e0', used4) := alpha_rename_expr rho_branch used3 e0 in
                  let (rest', used5) := go used4 rest in
                  ((variant_name, binders', e0') :: rest', used5)
              end) used1 branches0) = (branchesr0, usedr) ->
          ((fix go (used2 : list ident) (branches1 : list (string * list ident * expr)) {struct branches1}
              : list (string * list ident * expr) * list ident :=
              match branches1 with
              | [] => ([], used2)
              | (variant_name, binders, e0) :: rest =>
                  let binder_seed := binders ++ free_vars_expr e0 ++ used2 in
                  let '(binders', rho_branch, used3) :=
                    alpha_rename_idents rho binder_seed binders in
                  let (e0', used4) := alpha_rename_expr rho_branch used3 e0 in
                  let (rest', used5) := go used4 rest in
                  ((variant_name, binders', e0') :: rest', used5)
              end) used1
            ((fix subst_go (bs : list (string * list ident * expr))
                : list (string * list ident * expr) :=
                match bs with
                | [] => []
                | (name, binders, e0) :: bs0 =>
                    (name, binders, subst_type_params_expr type_args e0)
                      :: subst_go bs0
                end) branches0)) =
          ((fix subst_go (bs : list (string * list ident * expr))
              : list (string * list ident * expr) :=
              match bs with
              | [] => []
              | (name, binders, e0) :: bs0 =>
                  (name, binders, subst_type_params_expr type_args e0)
                    :: subst_go bs0
              end) branchesr0, usedr)).
        { induction branches0 as [| [[branch_name binders] branch] rest IHbranches];
            intros used1 branchesr0 usedr Hincl Hgo; simpl in Hgo |- *.
          - injection Hgo as <- <-. reflexivity.
          - rewrite expr_names_subst_type_params_expr.
            destruct (alpha_rename_idents rho
              (binders ++ free_vars_expr branch ++ used1) binders)
              as [[bindersr rho_branch] used2] eqn:Hbinders.
            destruct (alpha_rename_expr rho_branch used2 branch)
              as [branchr used3] eqn:Hbranch.
            destruct ((fix go (used4 : list ident) (branches1 : list (string * list ident * expr)) {struct branches1}
              : list (string * list ident * expr) * list ident :=
              match branches1 with
              | [] => ([], used4)
              | (variant_name, binders0, e0) :: rest0 =>
                  let binder_seed := binders0 ++ free_vars_expr e0 ++ used4 in
                  let '(binders0', rho_branch0, used5) :=
                    alpha_rename_idents rho binder_seed binders0 in
                  let (e0', used6) := alpha_rename_expr rho_branch0 used5 e0 in
                  let (rest', used7) := go used6 rest0 in
                  ((variant_name, binders0', e0') :: rest', used7)
              end) used3 rest) as [restr used4] eqn:Hrest.
            injection Hgo as <- <-.
            simpl.
            replace (binders ++
              free_vars_expr (subst_type_params_expr type_args branch) ++ used1)
              with (binders ++ free_vars_expr branch ++ used1)
              by (rewrite expr_names_subst_type_params_expr; reflexivity).
            change (expr_names branch) with (free_vars_expr branch).
            rewrite Hbinders.
            rewrite (IH rho_branch used2 branch branchr used3).
            + simpl.
              destruct (((fix go
                (used2 : list ident)
                (branches1 : list (string * list ident * expr)) {struct branches1}
                : list (string * list ident * expr) * list ident :=
                match branches1 with
                | [] => ([], used2)
                | (variant_name, binders0, e0) :: rest0 =>
                    let binder_seed := binders0 ++ free_vars_expr e0 ++ used2 in
                    let '(binders0', rho_branch0, used5) :=
                      alpha_rename_idents rho binder_seed binders0 in
                    let (e0', used6) := alpha_rename_expr rho_branch0 used5 e0 in
                    let (rest', used7) := go used6 rest0 in
                    ((variant_name, binders0', e0') :: rest', used7)
                end)
                used3
                ((fix subst_go (bs : list (string * list ident * expr))
                  : list (string * list ident * expr) :=
                  match bs with
                  | [] => []
                  | (name, binders0, e0) :: bs0 =>
                      (name, binders0, subst_type_params_expr type_args e0)
                      :: subst_go bs0
                  end) rest))) as [restr_sub used_sub] eqn:Hrest_sub.
              pose proof (IHbranches used3 restr used4) as Hrest_comm.
              assert (Hincl_rest : forall (name0 : string)
                  (binders0 : list ident) (branch0 : expr),
                  In (name0, binders0, branch0) rest ->
                  In (name0, binders0, branch0) branches).
              { intros name0 binders0 branch0 Hin.
                apply Hincl. right. exact Hin. }
              specialize (Hrest_comm Hincl_rest Hrest).
              rewrite Hrest_sub in Hrest_comm.
              injection Hrest_comm as <- <-.
              reflexivity.
            + pose proof (expr_size_match_branch_lt scrut branches branch_name binders branch
                (Hincl branch_name binders branch (or_introl eq_refl))). lia.
            + exact Hbranch. }
        destruct (((fix go (used1 : list ident)
          (branches0 : list (string * list ident * expr)) {struct branches0}
          : list (string * list ident * expr) * list ident :=
          match branches0 with
          | [] => ([], used1)
          | (variant_name, binders, e0) :: rest =>
              let binder_seed := binders ++ free_vars_expr e0 ++ used1 in
              let '(binders', rho_branch, used2) :=
                alpha_rename_idents rho binder_seed binders in
              let (e0', used3) := alpha_rename_expr rho_branch used2 e0 in
              let (rest', used4) := go used3 rest in
              ((variant_name, binders', e0') :: rest', used4)
          end) used0
          ((fix subst_go (bs : list (string * list ident * expr))
            : list (string * list ident * expr) :=
            match bs with
            | [] => []
            | (name, binders, e0) :: bs0 =>
                (name, binders, subst_type_params_expr type_args e0)
                :: subst_go bs0
            end) branches))) as [branches_sub used_sub] eqn:Hbranches_sub.
        pose proof (Hbranches_comm branches used0 branchesr used_branches
          (fun name binders branch H => H) Hbranches) as Hbranches_comm'.
        rewrite Hbranches_sub in Hbranches_comm'.
        injection Hbranches_comm' as <- <-.
        reflexivity.
      + destruct (alpha_rename_expr rho used rhs) as [rhsr used0] eqn:Hrhs.
        injection Hrename as <- <-.
        rewrite (IH rho used rhs rhsr used0); [reflexivity | simpl in Hlt; lia | exact Hrhs].
      + destruct (alpha_rename_expr rho used rhs) as [rhsr used0] eqn:Hrhs.
        injection Hrename as <- <-.
        rewrite (IH rho used rhs rhsr used0); [reflexivity | simpl in Hlt; lia | exact Hrhs].
      + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
        injection Hrename as <- <-.
        rewrite (IH rho used e er0 used0); [reflexivity | simpl in Hlt; lia | exact He].
      + destruct (alpha_rename_expr rho used e) as [er0 used0] eqn:He.
        injection Hrename as <- <-.
        rewrite (IH rho used e er0 used0); [reflexivity | simpl in Hlt; lia | exact He].
      + destruct (alpha_rename_expr rho used e1) as [e1r used1] eqn:He1.
        destruct (alpha_rename_expr rho used1 e2) as [e2r used2] eqn:He2.
        destruct (alpha_rename_expr rho used2 e3) as [e3r used3] eqn:He3.
        injection Hrename as <- <-.
        rewrite (IH rho used e1 e1r used1); [| simpl in Hlt; lia | exact He1].
        simpl.
        rewrite (IH rho used1 e2 e2r used2); [| simpl in Hlt; lia | exact He2].
        simpl.
        rewrite (IH rho used2 e3 e3r used3); [reflexivity | simpl in Hlt; lia | exact He3]. }
  intros rho used e er used' Hrename.
  eapply Hsize with (n := S (expr_size e)); [lia | exact Hrename].
Qed.

