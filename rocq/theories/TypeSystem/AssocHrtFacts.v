From Facet.TypeSystem Require Import
  Lifetime Types Syntax PathState Program Renaming TypingRules RootProvenance
  CheckerBase CheckerTraits CheckerHrt CheckerEnvHelpers AssocCompatibility AssocHrtHelpers
  AssocArgBoolFacts.
From Stdlib Require Import List Bool ZArith.
Import ListNotations.

Local Opaque ty_compatible_assoc_b.

(* ------------------------------------------------------------------ *)
(* Associated-projection HRT helper boolean facts                        *)
(* ------------------------------------------------------------------ *)

Definition assoc_checked_arg_tys
    (env : global_env) (Ω : outlives_ctx)
    (arg_tys param_tys : list Ty) : Prop :=
  Forall2
    (fun actual expected =>
       ty_compatible_assoc_checked env Ω actual expected)
    arg_tys param_tys /\
  length arg_tys = length param_tys.

Lemma check_arg_tys_assoc_checked_arg_tys :
  forall env Ω arg_tys param_tys,
    check_arg_tys_assoc env Ω arg_tys param_tys = None ->
    assoc_checked_arg_tys env Ω arg_tys param_tys.
Proof.
  intros env Ω arg_tys param_tys Hcheck.
  split.
  - apply (check_arg_tys_assoc_true env Ω). exact Hcheck.
  - apply (check_arg_tys_assoc_length env Ω). exact Hcheck.
Qed.

Lemma infer_hrt_call_env_assoc_checked_args :
  forall env Ω n m bounds body arg_tys T,
    infer_hrt_call_env_assoc env Ω n m bounds body arg_tys = infer_ok T ->
    (exists param_tys ret σ,
        ty_core body = TFn param_tys ret /\
        build_bound_sigma (repeat None m) arg_tys param_tys = Some σ /\
        check_arg_tys_assoc env Ω arg_tys
          (map (open_bound_ty σ) param_tys) = None /\
        assoc_checked_arg_tys env Ω arg_tys
          (map (open_bound_ty σ) param_tys)) \/
    (exists env_lt param_tys ret σ0,
        ty_core body = TClosure env_lt param_tys ret /\
        build_bound_sigma (repeat None m) arg_tys param_tys = Some σ0 /\
        check_arg_tys_assoc env Ω arg_tys
          (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
            param_tys) = None /\
        assoc_checked_arg_tys env Ω arg_tys
          (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
            param_tys)).
Proof.
  intros env Ω n m bounds body arg_tys T Hinfer.
  unfold infer_hrt_call_env_assoc in Hinfer.
  destruct (ty_core body) eqn:Hcore; try discriminate.
  - destruct (build_bound_sigma (repeat None m) arg_tys l) as [sigma|] eqn:Hsigma;
      try discriminate.
    destruct (check_arg_tys_assoc env Ω arg_tys
      (map (open_bound_ty sigma) l)) eqn:Hcheck; try discriminate.
    destruct (contains_lbound_ty (open_bound_ty sigma t) ||
      contains_lbound_outlives (open_bound_outlives sigma bounds)) eqn:?; try discriminate.
    destruct (outlives_constraints_hold_b Ω
      (open_bound_outlives sigma bounds)) eqn:?; try discriminate.
    left. exists l, t, sigma.
    split; [reflexivity |].
    split; [exact Hsigma |].
    split; [exact Hcheck |].
    apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
  - destruct (build_bound_sigma (repeat None m) arg_tys l0) as [sigma|] eqn:Hsigma;
      try discriminate.
    destruct (check_arg_tys_assoc env Ω arg_tys
      (map (open_bound_ty (complete_bound_sigma_with_vars n sigma)) l0))
      eqn:Hcheck; try discriminate.
    destruct (contains_lbound_lifetime
      (open_bound_lifetime (complete_bound_sigma_with_vars n sigma) l) ||
      contains_lbound_ty
        (open_bound_ty (complete_bound_sigma_with_vars n sigma) t) ||
      contains_lbound_outlives
        (open_bound_outlives (complete_bound_sigma_with_vars n sigma) bounds))
      eqn:?; try discriminate.
    destruct (outlives_constraints_hold_b Ω
      (open_bound_outlives (complete_bound_sigma_with_vars n sigma) bounds))
      eqn:?; try discriminate.
    right. exists l, l0, t, sigma.
    split; [reflexivity |].
    split; [exact Hsigma |].
    split; [exact Hcheck |].
    apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
Qed.

Lemma infer_type_forall_call_env_assoc_checked_args :
  forall env Ω type_params bounds body arg_tys T,
    infer_type_forall_call_env_assoc
      env Ω type_params bounds body arg_tys = infer_ok T ->
    exists type_args param_tys ret,
      ty_core body = TFn param_tys ret /\
      infer_type_forall_args type_params param_tys arg_tys = Some type_args /\
      check_type_forall_bounds env bounds type_args = None /\
      check_arg_tys_assoc env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys) = None /\
      assoc_checked_arg_tys env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys).
Proof.
  intros env Ω type_params bounds body arg_tys T Hinfer.
  unfold infer_type_forall_call_env_assoc in Hinfer.
  destruct (ty_core body) eqn:Hcore; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (check_type_forall_bounds env bounds type_args) eqn:Hbounds;
    try discriminate.
  destruct (check_arg_tys_assoc env Ω arg_tys
    (map (subst_type_params_ty type_args) l)) eqn:Hcheck; try discriminate.
  exists type_args, l, t.
  split; [reflexivity |].
  split; [exact Htype_args |].
  split; [exact Hbounds |].
  split; [exact Hcheck |].
  apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
Qed.

Lemma infer_type_forall_call_env_elab_assoc_checked_args :
  forall env Ω type_params bounds body arg_tys type_args_ret,
    infer_type_forall_call_env_elab_assoc
      env Ω type_params bounds body arg_tys = infer_ok type_args_ret ->
    exists type_args param_tys ret,
      ty_core body = TFn param_tys ret /\
      infer_type_forall_args type_params param_tys arg_tys = Some type_args /\
      check_type_forall_bounds env bounds type_args = None /\
      check_arg_tys_assoc env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys) = None /\
      assoc_checked_arg_tys env Ω arg_tys
        (map (subst_type_params_ty type_args) param_tys).
Proof.
  intros env Ω type_params bounds body arg_tys type_args_ret Hinfer.
  unfold infer_type_forall_call_env_elab_assoc in Hinfer.
  destruct (ty_core body) eqn:Hcore; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|]
    eqn:Htype_args; try discriminate.
  destruct (check_type_forall_bounds env bounds type_args) eqn:Hbounds;
    try discriminate.
  destruct (check_arg_tys_assoc env Ω arg_tys
    (map (subst_type_params_ty type_args) l)) eqn:Hcheck; try discriminate.
  exists type_args, l, t.
  split; [reflexivity |].
  split; [exact Htype_args |].
  split; [exact Hbounds |].
  split; [exact Hcheck |].
  apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
Qed.

Lemma infer_mixed_forall_call_env_assoc_checked_args :
  forall env Ω n m lt_bounds type_params type_bounds body arg_tys T,
    infer_mixed_forall_call_env_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys = infer_ok T ->
    exists type_args param_tys ret σ0,
      ty_core body = TFn param_tys ret /\
      infer_type_forall_args type_params param_tys arg_tys = Some type_args /\
      build_bound_sigma (repeat None m) arg_tys
        (map (subst_type_params_ty type_args) param_tys) = Some σ0 /\
      check_arg_tys_assoc env Ω arg_tys
        (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
          (map (subst_type_params_ty type_args) param_tys)) = None /\
      assoc_checked_arg_tys env Ω arg_tys
        (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
          (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros env Ω n m lt_bounds type_params type_bounds body arg_tys T Hinfer.
  unfold infer_mixed_forall_call_env_assoc in Hinfer.
  destruct (ty_core body) eqn:Hcore; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|] eqn:Htype_args;
    try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|] eqn:Hsigma; try discriminate.
  destruct (check_arg_tys_assoc env Ω arg_tys
    (map (open_bound_ty (complete_bound_sigma_with_vars n sigma0))
      (map (subst_type_params_ty type_args) l))) eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty (complete_bound_sigma_with_vars n sigma0)
      (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives
      (open_bound_outlives (complete_bound_sigma_with_vars n sigma0) lt_bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds (complete_bound_sigma_with_vars n sigma0)
        type_bounds)) eqn:?; try discriminate.
  destruct (outlives_constraints_hold_b Ω
    (open_bound_outlives (complete_bound_sigma_with_vars n sigma0) lt_bounds))
    eqn:?; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds (complete_bound_sigma_with_vars n sigma0) type_bounds)
    type_args) eqn:?; try discriminate.
  exists type_args, l, t, sigma0.
  split; [reflexivity |].
  split; [exact Htype_args |].
  split; [exact Hsigma |].
  split; [exact Hcheck |].
  apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
Qed.

Lemma infer_mixed_forall_call_env_elab_assoc_checked_args :
  forall env Ω n m lt_bounds type_params type_bounds body arg_tys type_args_ret,
    infer_mixed_forall_call_env_elab_assoc
      env Ω n m lt_bounds type_params type_bounds body arg_tys =
      infer_ok type_args_ret ->
    exists type_args param_tys ret σ0,
      ty_core body = TFn param_tys ret /\
      infer_type_forall_args type_params param_tys arg_tys = Some type_args /\
      build_bound_sigma (repeat None m) arg_tys
        (map (subst_type_params_ty type_args) param_tys) = Some σ0 /\
      check_arg_tys_assoc env Ω arg_tys
        (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
          (map (subst_type_params_ty type_args) param_tys)) = None /\
      assoc_checked_arg_tys env Ω arg_tys
        (map (open_bound_ty (complete_bound_sigma_with_vars n σ0))
          (map (subst_type_params_ty type_args) param_tys)).
Proof.
  intros env Ω n m lt_bounds type_params type_bounds body arg_tys type_args_ret
    Hinfer.
  unfold infer_mixed_forall_call_env_elab_assoc in Hinfer.
  destruct (ty_core body) eqn:Hcore; try discriminate.
  destruct (infer_type_forall_args type_params l arg_tys) as [type_args|] eqn:Htype_args;
    try discriminate.
  destruct (build_bound_sigma (repeat None m) arg_tys
    (map (subst_type_params_ty type_args) l)) as [sigma0|] eqn:Hsigma; try discriminate.
  destruct (check_arg_tys_assoc env Ω arg_tys
    (map (open_bound_ty (complete_bound_sigma_with_vars n sigma0))
      (map (subst_type_params_ty type_args) l))) eqn:Hcheck; try discriminate.
  destruct (contains_lbound_ty
    (open_bound_ty (complete_bound_sigma_with_vars n sigma0)
      (subst_type_params_ty type_args t)) ||
    contains_lbound_outlives
      (open_bound_outlives (complete_bound_sigma_with_vars n sigma0) lt_bounds) ||
    existsb
      (fun b : core_trait_bound Ty =>
         existsb
           (fun tr : core_trait_ref Ty =>
              existsb contains_lbound_ty (core_trait_ref_args Ty tr))
           (core_bound_traits Ty b))
      (open_core_trait_bounds (complete_bound_sigma_with_vars n sigma0)
        type_bounds)) eqn:?; try discriminate.
  destruct (outlives_constraints_hold_b Ω
    (open_bound_outlives (complete_bound_sigma_with_vars n sigma0) lt_bounds))
    eqn:?; try discriminate.
  destruct (check_type_forall_bounds env
    (open_core_trait_bounds (complete_bound_sigma_with_vars n sigma0) type_bounds)
    type_args) eqn:?; try discriminate.
  exists type_args, l, t, sigma0.
  split; [reflexivity |].
  split; [exact Htype_args |].
  split; [exact Hsigma |].
  split; [exact Hcheck |].
  apply check_arg_tys_assoc_checked_arg_tys. exact Hcheck.
Qed.
