From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  OperationalSemantics TypingRules TypeChecker.
From Stdlib Require Import List String Bool Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Runtime value typing                                                 *)
(* ------------------------------------------------------------------ *)

Inductive ty_lifetime_equiv : Ty -> Ty -> Prop :=
  | TLE_Units : forall u,
      ty_lifetime_equiv (MkTy u TUnits) (MkTy u TUnits)
  | TLE_Integers : forall u,
      ty_lifetime_equiv (MkTy u TIntegers) (MkTy u TIntegers)
  | TLE_Floats : forall u,
      ty_lifetime_equiv (MkTy u TFloats) (MkTy u TFloats)
  | TLE_Booleans : forall u,
      ty_lifetime_equiv (MkTy u TBooleans) (MkTy u TBooleans)
  | TLE_Named : forall u name,
      ty_lifetime_equiv (MkTy u (TNamed name)) (MkTy u (TNamed name))
  | TLE_Param : forall u i,
      ty_lifetime_equiv (MkTy u (TParam i)) (MkTy u (TParam i))
  | TLE_Struct : forall u name lts_actual lts_expected args_actual args_expected,
      Forall2 ty_lifetime_equiv args_actual args_expected ->
      ty_lifetime_equiv
        (MkTy u (TStruct name lts_actual args_actual))
        (MkTy u (TStruct name lts_expected args_expected))
  | TLE_Fn : forall u params_actual params_expected ret_actual ret_expected,
      Forall2 ty_lifetime_equiv params_actual params_expected ->
      ty_lifetime_equiv ret_actual ret_expected ->
      ty_lifetime_equiv
        (MkTy u (TFn params_actual ret_actual))
        (MkTy u (TFn params_expected ret_expected))
  | TLE_Forall : forall u n Ω_actual Ω_expected body_actual body_expected,
      ty_lifetime_equiv body_actual body_expected ->
      ty_lifetime_equiv
        (MkTy u (TForall n Ω_actual body_actual))
        (MkTy u (TForall n Ω_expected body_expected))
  | TLE_Ref : forall u l_actual l_expected rk T_actual T_expected,
      ty_lifetime_equiv T_actual T_expected ->
      ty_lifetime_equiv
        (MkTy u (TRef l_actual rk T_actual))
        (MkTy u (TRef l_expected rk T_expected)).

Fixpoint ty_lifetime_equiv_refl (T : Ty) : ty_lifetime_equiv T T :=
  match T with
  | MkTy u TUnits => TLE_Units u
  | MkTy u TIntegers => TLE_Integers u
  | MkTy u TFloats => TLE_Floats u
  | MkTy u TBooleans => TLE_Booleans u
  | MkTy u (TNamed name) => TLE_Named u name
  | MkTy u (TParam i) => TLE_Param u i
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty) : Forall2 ty_lifetime_equiv xs xs :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv x x xs' xs'
            (ty_lifetime_equiv_refl x) (go xs')
        end
      in
      TLE_Struct u name lts lts args args (go args)
  | MkTy u (TFn params ret) =>
      let fix go (xs : list Ty) : Forall2 ty_lifetime_equiv xs xs :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv x x xs' xs'
            (ty_lifetime_equiv_refl x) (go xs')
        end
      in
      TLE_Fn u params params ret ret (go params) (ty_lifetime_equiv_refl ret)
  | MkTy u (TForall n Ω body) =>
      TLE_Forall u n Ω Ω body body (ty_lifetime_equiv_refl body)
  | MkTy u (TRef l rk Tinner) =>
      TLE_Ref u l l rk Tinner Tinner (ty_lifetime_equiv_refl Tinner)
  end.

Fixpoint ty_lifetime_equiv_apply_lt_ty
    (σ : list lifetime) (T : Ty)
    : ty_lifetime_equiv T (apply_lt_ty σ T) :=
  match T with
  | MkTy u TUnits => TLE_Units u
  | MkTy u TIntegers => TLE_Integers u
  | MkTy u TFloats => TLE_Floats u
  | MkTy u TBooleans => TLE_Booleans u
  | MkTy u (TNamed name) => TLE_Named u name
  | MkTy u (TParam i) => TLE_Param u i
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty)
          : Forall2 ty_lifetime_equiv
              xs
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ y :: map_lt ys'
                  end) xs) :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv
            x (apply_lt_ty σ x) xs'
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ y :: map_lt ys'
                end) xs')
            (ty_lifetime_equiv_apply_lt_ty σ x) (go xs')
        end
      in
      TLE_Struct u name lts (map (apply_lt_lifetime σ) lts)
        args
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ x :: map_lt xs'
            end) args)
        (go args)
  | MkTy u (TFn params ret) =>
      let fix go (xs : list Ty)
          : Forall2 ty_lifetime_equiv
              xs
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ y :: map_lt ys'
                  end) xs) :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv
            x (apply_lt_ty σ x) xs'
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ y :: map_lt ys'
                end) xs')
            (ty_lifetime_equiv_apply_lt_ty σ x) (go xs')
        end
      in
      TLE_Fn u params
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ x :: map_lt xs'
            end) params)
        ret (apply_lt_ty σ ret)
        (go params) (ty_lifetime_equiv_apply_lt_ty σ ret)
  | MkTy u (TForall n Ω body) =>
      TLE_Forall u n Ω (apply_lt_outlives σ Ω)
        body (apply_lt_ty σ body)
        (ty_lifetime_equiv_apply_lt_ty σ body)
  | MkTy u (TRef l rk Tinner) =>
      TLE_Ref u l (apply_lt_lifetime σ l) rk
        Tinner (apply_lt_ty σ Tinner)
        (ty_lifetime_equiv_apply_lt_ty σ Tinner)
  end.

Lemma ty_lifetime_equiv_with_usage :
  forall u T_actual T_expected,
    ty_lifetime_equiv T_actual T_expected ->
    ty_lifetime_equiv
      (MkTy u (ty_core T_actual))
      (MkTy u (ty_core T_expected)).
Proof.
  intros u T_actual T_expected Heq.
  inversion Heq; subst; simpl; eauto using ty_lifetime_equiv.
Qed.

Lemma ty_lifetime_equiv_sym :
  forall T_actual T_expected,
    ty_lifetime_equiv T_actual T_expected ->
    ty_lifetime_equiv T_expected T_actual.
Proof.
  fix IH 3.
  intros T_actual T_expected Heq.
  destruct Heq.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor. induction H; constructor; eauto.
  - constructor.
    + induction H; constructor; eauto.
    + apply IH. exact Heq.
  - constructor. apply IH. exact Heq.
  - constructor. apply IH. exact Heq.
Qed.

Fixpoint ty_lifetime_equiv_apply_lt_ty_two
    (σ_actual σ_expected : list lifetime) (T : Ty)
    : ty_lifetime_equiv (apply_lt_ty σ_actual T) (apply_lt_ty σ_expected T) :=
  match T with
  | MkTy u TUnits => TLE_Units u
  | MkTy u TIntegers => TLE_Integers u
  | MkTy u TFloats => TLE_Floats u
  | MkTy u TBooleans => TLE_Booleans u
  | MkTy u (TNamed name) => TLE_Named u name
  | MkTy u (TParam i) => TLE_Param u i
  | MkTy u (TStruct name lts args) =>
      let fix go (xs : list Ty)
          : Forall2 ty_lifetime_equiv
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ_actual y :: map_lt ys'
                  end) xs)
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ_expected y :: map_lt ys'
                  end) xs) :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv
            (apply_lt_ty σ_actual x) (apply_lt_ty σ_expected x)
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ_actual y :: map_lt ys'
                end) xs')
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ_expected y :: map_lt ys'
                end) xs')
            (ty_lifetime_equiv_apply_lt_ty_two σ_actual σ_expected x)
            (go xs')
        end
      in
      TLE_Struct u name
        (map (apply_lt_lifetime σ_actual) lts)
        (map (apply_lt_lifetime σ_expected) lts)
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ_actual x :: map_lt xs'
            end) args)
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ_expected x :: map_lt xs'
            end) args)
        (go args)
  | MkTy u (TFn params ret) =>
      let fix go (xs : list Ty)
          : Forall2 ty_lifetime_equiv
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ_actual y :: map_lt ys'
                  end) xs)
              ((fix map_lt (ys : list Ty) : list Ty :=
                  match ys with
                  | [] => []
                  | y :: ys' => apply_lt_ty σ_expected y :: map_lt ys'
                  end) xs) :=
        match xs with
        | [] => @Forall2_nil Ty Ty ty_lifetime_equiv
        | x :: xs' => @Forall2_cons Ty Ty ty_lifetime_equiv
            (apply_lt_ty σ_actual x) (apply_lt_ty σ_expected x)
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ_actual y :: map_lt ys'
                end) xs')
            ((fix map_lt (ys : list Ty) : list Ty :=
                match ys with
                | [] => []
                | y :: ys' => apply_lt_ty σ_expected y :: map_lt ys'
                end) xs')
            (ty_lifetime_equiv_apply_lt_ty_two σ_actual σ_expected x)
            (go xs')
        end
      in
      TLE_Fn u
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ_actual x :: map_lt xs'
            end) params)
        ((fix map_lt (xs : list Ty) : list Ty :=
            match xs with
            | [] => []
            | x :: xs' => apply_lt_ty σ_expected x :: map_lt xs'
            end) params)
        (apply_lt_ty σ_actual ret) (apply_lt_ty σ_expected ret)
        (go params)
        (ty_lifetime_equiv_apply_lt_ty_two σ_actual σ_expected ret)
  | MkTy u (TForall n Ω body) =>
      TLE_Forall u n
        (apply_lt_outlives σ_actual Ω)
        (apply_lt_outlives σ_expected Ω)
        (apply_lt_ty σ_actual body)
        (apply_lt_ty σ_expected body)
        (ty_lifetime_equiv_apply_lt_ty_two σ_actual σ_expected body)
  | MkTy u (TRef l rk Tinner) =>
      TLE_Ref u (apply_lt_lifetime σ_actual l)
        (apply_lt_lifetime σ_expected l) rk
        (apply_lt_ty σ_actual Tinner)
        (apply_lt_ty σ_expected Tinner)
        (ty_lifetime_equiv_apply_lt_ty_two σ_actual σ_expected Tinner)
  end.

Lemma nth_error_forall2_ty_lifetime_equiv :
  forall args_actual args_expected i T_actual T_expected,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    nth_error args_actual i = Some T_actual ->
    nth_error args_expected i = Some T_expected ->
    ty_lifetime_equiv T_actual T_expected.
Proof.
  intros args_actual.
  induction args_actual as [|Ta args_actual IH];
    intros args_expected [|i] T_actual T_expected Hargs Ha He;
    inversion Hargs; subst; simpl in *; try discriminate.
  - inversion Ha; inversion He; subst. assumption.
  - eapply IH; eassumption.
Qed.

Lemma subst_type_params_param_lifetime_equiv :
  forall args_actual args_expected i u,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    ty_lifetime_equiv
      match nth_error args_actual i with
      | Some T' => MkTy u (ty_core T')
      | None => MkTy u (TParam i)
      end
      match nth_error args_expected i with
      | Some T' => MkTy u (ty_core T')
      | None => MkTy u (TParam i)
      end.
Proof.
  intros args_actual args_expected i u Hargs.
  assert (Hlen : List.length args_actual = List.length args_expected).
  { induction Hargs; simpl; congruence. }
  destruct (nth_error args_actual i) as [Ta |] eqn:Ha;
    destruct (nth_error args_expected i) as [Te |] eqn:He.
  - apply ty_lifetime_equiv_with_usage.
    eapply nth_error_forall2_ty_lifetime_equiv; eassumption.
  - assert (Ha_some : i < List.length args_actual).
    { apply nth_error_Some. rewrite Ha. discriminate. }
    apply nth_error_None in He.
    rewrite <- Hlen in He. lia.
  - apply nth_error_None in Ha.
    assert (He_some : i < List.length args_expected).
    { apply nth_error_Some. rewrite He. discriminate. }
    rewrite Hlen in Ha. lia.
  - constructor.
Qed.

Lemma subst_type_params_ty_lifetime_equiv :
  forall args_actual args_expected T_actual T_expected,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    ty_lifetime_equiv T_actual T_expected ->
    ty_lifetime_equiv
      (subst_type_params_ty args_actual T_actual)
      (subst_type_params_ty args_expected T_expected).
Proof.
  fix IH 6.
  intros args_actual args_expected T_actual T_expected Hargs Heq.
  destruct Heq; simpl; eauto using ty_lifetime_equiv,
    subst_type_params_param_lifetime_equiv.
  - apply TLE_Struct.
    induction H; simpl; constructor; eauto.
  - apply TLE_Fn.
    + induction H; simpl; constructor; eauto.
    + eapply IH; eassumption.
Qed.

Lemma instantiate_struct_field_ty_lifetime_equiv :
  forall lts_actual lts_expected args_actual args_expected fdef,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    ty_lifetime_equiv
      (instantiate_struct_field_ty lts_actual args_actual fdef)
      (instantiate_struct_field_ty lts_expected args_expected fdef).
Proof.
  intros lts_actual lts_expected args_actual args_expected fdef Hargs.
  unfold instantiate_struct_field_ty.
  apply subst_type_params_ty_lifetime_equiv.
  - exact Hargs.
  - apply ty_lifetime_equiv_apply_lt_ty_two.
Qed.

Inductive value_has_type (env : global_env) (s : store) : value -> Ty -> Prop :=
  | VHT_Unit : forall u,
      value_has_type env s VUnit (MkTy u TUnits)
  | VHT_Int : forall u i,
      value_has_type env s (VInt i) (MkTy u TIntegers)
  | VHT_Float : forall u f,
      value_has_type env s (VFloat f) (MkTy u TFloats)
  | VHT_Bool : forall u b,
      value_has_type env s (VBool b) (MkTy u TBooleans)
  | VHT_Struct : forall name lts args fields sdef,
      lookup_struct name env = Some sdef ->
      struct_fields_have_type env s lts args fields (struct_fields sdef) ->
      value_has_type env s (VStruct name fields)
        (instantiate_struct_instance_ty sdef lts args)
  | VHT_Ref : forall u la rk x path se v T,
      store_lookup x s = Some se ->
      value_lookup_path (se_val se) path = Some v ->
      type_lookup_path env (se_ty se) path = Some T ->
      value_has_type env s (VRef x path) (MkTy u (TRef la rk T))
  | VHT_ClosureEmpty : forall fname fdef,
      lookup_fn fname (env_fns env) = Some fdef ->
      value_has_type env s (VClosure fname []) (fn_value_ty fdef)
  | VHT_ClosureIn : forall fname fdef,
      In fdef (env_fns env) ->
      fn_name fdef = fname ->
      value_has_type env s (VClosure fname []) (fn_value_ty fdef)
  | VHT_Compatible : forall Ω v T_actual T_expected,
      value_has_type env s v T_actual ->
      ty_compatible Ω T_actual T_expected ->
      value_has_type env s v T_expected
  | VHT_LifetimeEquiv : forall v T_actual T_expected,
      value_has_type env s v T_actual ->
      ty_lifetime_equiv T_actual T_expected ->
      value_has_type env s v T_expected
with struct_fields_have_type
    (env : global_env) (s : store)
    : list lifetime -> list Ty -> list (string * value) -> list field_def -> Prop :=
  | SFHT_Nil :
      forall lts args,
      struct_fields_have_type env s lts args [] []
  | SFHT_Cons : forall lts args name v fields f defs,
      name = field_name f ->
      value_has_type env s v (instantiate_struct_field_ty lts args f) ->
      struct_fields_have_type env s lts args fields defs ->
      struct_fields_have_type env s lts args ((name, v) :: fields) (f :: defs).

Scheme value_has_type_ind' := Induction for value_has_type Sort Prop
with struct_fields_have_type_ind' := Induction for struct_fields_have_type Sort Prop.
Combined Scheme runtime_typing_ind
  from value_has_type_ind', struct_fields_have_type_ind'.

(* References in surviving runtime values must not point at a removed
   store root. *)
Inductive value_refs_exclude_root (root : ident) : value -> Prop :=
  | VRE_Unit :
      value_refs_exclude_root root VUnit
  | VRE_Int : forall i,
      value_refs_exclude_root root (VInt i)
  | VRE_Float : forall f,
      value_refs_exclude_root root (VFloat f)
  | VRE_Bool : forall b,
      value_refs_exclude_root root (VBool b)
  | VRE_Struct : forall name fields,
      value_fields_refs_exclude_root root fields ->
      value_refs_exclude_root root (VStruct name fields)
  | VRE_Ref : forall x path,
      ident_eqb root x = false ->
      value_refs_exclude_root root (VRef x path)
  | VRE_Closure : forall fname captures,
      store_refs_exclude_root root captures ->
      value_refs_exclude_root root (VClosure fname captures)
with store_entry_refs_exclude_root (root : ident) : store_entry -> Prop :=
  | SERE_Entry : forall sx sT sv sst,
      value_refs_exclude_root root sv ->
      store_entry_refs_exclude_root root (MkStoreEntry sx sT sv sst)
with store_refs_exclude_root (root : ident) : store -> Prop :=
  | SRE_Nil :
      store_refs_exclude_root root []
  | SRE_Cons : forall se rest,
      store_entry_refs_exclude_root root se ->
      store_refs_exclude_root root rest ->
      store_refs_exclude_root root (se :: rest)
with value_fields_refs_exclude_root
    (root : ident) : list (string * value) -> Prop :=
  | VFRE_Nil :
      value_fields_refs_exclude_root root []
  | VFRE_Cons : forall name v rest,
      value_refs_exclude_root root v ->
      value_fields_refs_exclude_root root rest ->
      value_fields_refs_exclude_root root ((name, v) :: rest).

Definition store_ref_targets_preserved
    (env : global_env) (s s' : store) : Prop :=
  forall x path se v T,
    store_lookup x s = Some se ->
    value_lookup_path (se_val se) path = Some v ->
    type_lookup_path env (se_ty se) path = Some T ->
    exists se' v',
      store_lookup x s' = Some se' /\
      value_lookup_path (se_val se') path = Some v' /\
      type_lookup_path env (se_ty se') path = Some T.

Lemma store_ref_targets_preserved_refl :
  forall env s,
    store_ref_targets_preserved env s s.
Proof.
  unfold store_ref_targets_preserved.
  intros env s x path se v T Hlookup Hvalue Htype.
  exists se, v. repeat split; assumption.
Qed.

Lemma store_ref_targets_preserved_trans :
  forall env s1 s2 s3,
    store_ref_targets_preserved env s1 s2 ->
    store_ref_targets_preserved env s2 s3 ->
    store_ref_targets_preserved env s1 s3.
Proof.
  unfold store_ref_targets_preserved.
  intros env s1 s2 s3 H12 H23 x path se v T Hlookup Hvalue Htype.
  destruct (H12 x path se v T Hlookup Hvalue Htype)
    as [se2 [v2 [Hlookup2 [Hvalue2 Htype2]]]].
  destruct (H23 x path se2 v2 T Hlookup2 Hvalue2 Htype2)
    as [se3 [v3 [Hlookup3 [Hvalue3 Htype3]]]].
  exists se3, v3. repeat split; assumption.
Qed.

Lemma runtime_typing_store_preserved :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall s',
      store_ref_targets_preserved env s s' ->
      value_has_type env s' v T) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall s',
      store_ref_targets_preserved env s s' ->
      struct_fields_have_type env s' lts args fields defs).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; eauto using value_has_type, struct_fields_have_type.
  - match goal with
    | Hpres : store_ref_targets_preserved env s ?s',
      Hlookup : store_lookup x s = Some se,
      Hvalue : value_lookup_path (se_val se) path = Some v,
      Htype : type_lookup_path env (se_ty se) path = Some T |- _ =>
        destruct (Hpres x path se v T Hlookup Hvalue Htype)
          as [se' [v' [Hlookup' [Hvalue' Htype']]]]
    end.
    eapply VHT_Ref; eassumption.
Qed.

Lemma value_has_type_store_preserved :
  forall env s v T,
    value_has_type env s v T ->
    forall s',
      store_ref_targets_preserved env s s' ->
      value_has_type env s' v T.
Proof.
  intros env s v T H s' Hpres.
  exact (proj1 (runtime_typing_store_preserved env s) v T H s' Hpres).
Qed.

Lemma store_lookup_remove_neq :
  forall s root x,
    ident_eqb root x = false ->
    store_lookup x (store_remove root s) = store_lookup x s.
Proof.
  induction s as [|se rest IH]; intros root x Hneq.
  - reflexivity.
  - simpl.
    destruct (ident_eqb root (se_name se)) eqn:Hroot.
    + destruct (ident_eqb x (se_name se)) eqn:Hx.
      * assert (root = x).
        { apply ident_eqb_eq in Hroot.
          apply ident_eqb_eq in Hx.
          congruence. }
        subst x.
        rewrite ident_eqb_refl in Hneq.
        discriminate.
      * reflexivity.
    + simpl.
      destruct (ident_eqb x (se_name se)); [reflexivity |].
      apply IH. exact Hneq.
Qed.

Lemma runtime_typing_store_remove_excluding_root :
  forall env s root,
  (forall v T,
    value_has_type env s v T ->
    value_refs_exclude_root root v ->
    value_has_type env (store_remove root s) v T) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    value_fields_refs_exclude_root root fields ->
    struct_fields_have_type env (store_remove root s) lts args fields defs).
Proof.
  intros env s root.
  apply runtime_typing_ind; intros;
    eauto using value_has_type, struct_fields_have_type.
  - apply VHT_Struct with (sdef := sdef); [assumption |].
    match goal with
    | Hexclude : value_refs_exclude_root root (VStruct _ _) |- _ =>
        inversion Hexclude; subst
    end.
    eauto.
  - match goal with
    | Hexclude : value_refs_exclude_root root (VRef _ _) |- _ =>
        inversion Hexclude; subst
    end.
    eapply VHT_Ref.
    + rewrite store_lookup_remove_neq; eassumption.
    + eassumption.
    + eassumption.
  - match goal with
    | Hexclude : value_fields_refs_exclude_root root ((_ , _) :: _) |- _ =>
        inversion Hexclude; subst
    end.
    econstructor; eauto.
Qed.

Lemma value_has_type_store_remove_excluding_root :
  forall env s root v T,
    value_has_type env s v T ->
    value_refs_exclude_root root v ->
    value_has_type env (store_remove root s) v T.
Proof.
  intros env s root v T Htyped Hexclude.
  exact (proj1 (runtime_typing_store_remove_excluding_root env s root)
    v T Htyped Hexclude).
Qed.

Lemma struct_fields_have_type_store_remove_excluding_root :
  forall env s root lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    value_fields_refs_exclude_root root fields ->
    struct_fields_have_type env (store_remove root s) lts args fields defs.
Proof.
  intros env s root lts args fields defs Htyped Hexclude.
  exact (proj2 (runtime_typing_store_remove_excluding_root env s root)
    lts args fields defs Htyped Hexclude).
Qed.

Lemma value_has_type_compatible :
  forall env s Ω v T_actual T_expected,
    value_has_type env s v T_actual ->
    ty_compatible Ω T_actual T_expected ->
    value_has_type env s v T_expected.
Proof.
  intros env s Ω v T_actual T_expected Htyped Hcompat.
  eapply VHT_Compatible; eassumption.
Qed.

Lemma value_has_type_apply_lt_ty :
  forall env s σ v T,
    value_has_type env s v T ->
    value_has_type env s v (apply_lt_ty σ T).
Proof.
  intros env s σ v T Htyped.
  eapply VHT_LifetimeEquiv.
  - exact Htyped.
  - apply ty_lifetime_equiv_apply_lt_ty.
Qed.

Lemma struct_fields_have_type_store_preserved :
  forall env s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall s',
      store_ref_targets_preserved env s s' ->
      struct_fields_have_type env s' lts args fields defs.
Proof.
  intros env s lts args fields defs H s' Hpres.
  exact (proj2 (runtime_typing_store_preserved env s)
    lts args fields defs H s' Hpres).
Qed.

(* ------------------------------------------------------------------ *)
(* Runtime struct field helpers                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint lookup_value_field (name : string) (fields : list (string * value))
    : option value :=
  match fields with
  | [] => None
  | (field_name, v) :: rest =>
      if String.eqb name field_name then Some v else lookup_value_field name rest
  end.

Fixpoint update_value_field
    (name : string) (v_new : value) (fields : list (string * value))
    : option (list (string * value)) :=
  match fields with
  | [] => None
  | (field_name, v) :: rest =>
      if String.eqb name field_name
      then Some ((field_name, v_new) :: rest)
      else match update_value_field name v_new rest with
           | Some rest' => Some ((field_name, v) :: rest')
           | None => None
           end
  end.

Fixpoint update_value_field_path
    (name : string) (path : field_path) (v_new : value)
    (fields : list (string * value)) : option (list (string * value)) :=
  match fields with
  | [] => None
  | (field_name, v) :: rest =>
      if String.eqb name field_name
      then match value_update_path v path v_new with
           | Some v' => Some ((field_name, v') :: rest)
           | None => None
           end
      else match update_value_field_path name path v_new rest with
           | Some rest' => Some ((field_name, v) :: rest')
           | None => None
           end
  end.

Lemma lookup_value_field_local :
  forall name fields,
    (let fix lookup (fields : list (string * value)) : option value :=
       match fields with
       | [] => None
       | (field_name, v) :: rest =>
           if String.eqb name field_name then Some v else lookup rest
       end
     in lookup fields) = lookup_value_field name fields.
Proof.
  intros name fields.
  induction fields as [|[field_name v] rest IH]; simpl.
  - reflexivity.
  - destruct (String.eqb name field_name); [reflexivity | exact IH].
Qed.

Lemma value_lookup_path_struct_cons :
  forall sname fields name rest,
    value_lookup_path (VStruct sname fields) (name :: rest) =
    match lookup_value_field name fields with
    | Some v => value_lookup_path v rest
    | None => None
    end.
Proof.
  intros sname fields name rest.
  simpl.
  rewrite lookup_value_field_local.
  reflexivity.
Qed.

Lemma update_value_field_path_local :
  forall name rest v_new fields,
    (let fix update (fields0 : list (string * value)) : option (list (string * value)) :=
       match fields0 with
       | [] => None
       | (name0, fv) :: tail =>
           if String.eqb name name0
           then match value_update_path fv rest v_new with
                | Some fv' => Some ((name0, fv') :: tail)
                | None => None
                end
           else match update tail with
                | Some tail' => Some ((name0, fv) :: tail')
                | None => None
                end
       end
     in update fields) = update_value_field_path name rest v_new fields.
Proof.
  intros name rest v_new fields.
  induction fields as [|[field_name v] tail IH]; simpl.
  - reflexivity.
  - destruct (String.eqb name field_name); [reflexivity |].
    replace ((fix update (fields0 : list (string * value)) :
                option (list (string * value)) :=
                match fields0 with
                | [] => None
                | (name0, fv) :: tail0 =>
                    if String.eqb name name0
                    then match value_update_path fv rest v_new with
                         | Some fv' => Some ((name0, fv') :: tail0)
                         | None => None
                         end
                    else match update tail0 with
                         | Some tail' => Some ((name0, fv) :: tail')
                         | None => None
                         end
                end) tail)
      with (update_value_field_path name rest v_new tail).
    reflexivity.
Qed.

Lemma value_update_path_struct_cons :
  forall sname fields name rest v_new,
    value_update_path (VStruct sname fields) (name :: rest) v_new =
    match update_value_field_path name rest v_new fields with
    | Some fields' => Some (VStruct sname fields')
    | None => None
    end.
Proof.
  intros sname fields name rest v_new.
  simpl.
  rewrite update_value_field_path_local.
  reflexivity.
Qed.

Lemma update_value_field_path_exists :
  forall name fields fv rest v_new fv',
    lookup_value_field name fields = Some fv ->
    value_update_path fv rest v_new = Some fv' ->
    exists fields',
      update_value_field_path name rest v_new fields = Some fields'.
Proof.
  intros name fields.
  induction fields as [|[field_name field_value] tail IH];
    intros fv rest v_new fv' Hlookup Hupdate.
  - discriminate.
  - simpl in Hlookup |- *.
    destruct (String.eqb name field_name) eqn:Hname.
    + inversion Hlookup; subst field_value.
      rewrite Hupdate.
      eexists. reflexivity.
    + destruct (IH fv rest v_new fv' Hlookup Hupdate)
        as [tail' Htail].
      rewrite Htail.
      eexists. reflexivity.
Qed.

Lemma value_lookup_path_update_exists :
  forall v path v_old v_new,
    value_lookup_path v path = Some v_old ->
    exists v',
      value_update_path v path v_new = Some v'.
Proof.
  intros v path.
  revert v.
  induction path as [|seg rest IH]; intros v v_old v_new Hlookup.
  - destruct v; simpl; eexists; reflexivity.
  - destruct v; simpl in Hlookup; try discriminate.
    rewrite lookup_value_field_local in Hlookup.
    rewrite value_update_path_struct_cons.
    destruct (lookup_value_field seg l) as [field_value |] eqn:Hfield;
      try discriminate.
    destruct (IH field_value v_old v_new Hlookup) as [field_value' Hupdate].
    destruct (update_value_field_path_exists seg l field_value rest v_new
                field_value' Hfield Hupdate)
      as [fields' Hfields].
    rewrite Hfields.
    eexists. reflexivity.
Qed.

Lemma struct_fields_have_type_lookup :
  forall env s lts args fields defs name v fdef,
    struct_fields_have_type env s lts args fields defs ->
    lookup_value_field name fields = Some v ->
    lookup_field name defs = Some fdef ->
    value_has_type env s v (instantiate_struct_field_ty lts args fdef).
Proof.
  intros env s lts args fields defs name v fdef Htyped.
  induction Htyped as [lts args|lts args runtime_name fv fields f defs Hname Hv Hfields IH];
    intros Hvalue Hfield.
  - discriminate.
  - simpl in Hvalue, Hfield.
    destruct (String.eqb name runtime_name) eqn:Hvalue_name;
      destruct (String.eqb name (field_name f)) eqn:Hfield_name.
    + inversion Hvalue; subst fv.
      inversion Hfield; subst fdef.
      exact Hv.
    + apply String.eqb_eq in Hvalue_name.
      assert (name = field_name f) by congruence.
      rewrite H in Hfield_name.
      rewrite String.eqb_refl in Hfield_name.
      discriminate.
    + apply String.eqb_eq in Hfield_name.
      assert (name = runtime_name) by congruence.
      rewrite H in Hvalue_name.
      rewrite String.eqb_refl in Hvalue_name.
      discriminate.
    + eapply IH; eassumption.
Qed.

Lemma struct_fields_have_type_update :
  forall env s lts args fields defs name v_new fields' fdef,
    struct_fields_have_type env s lts args fields defs ->
    lookup_field name defs = Some fdef ->
    value_has_type env s v_new (instantiate_struct_field_ty lts args fdef) ->
    update_value_field name v_new fields = Some fields' ->
    struct_fields_have_type env s lts args fields' defs.
Proof.
  intros env s lts args fields defs name v_new fields' fdef Htyped.
  revert name v_new fields' fdef.
  induction Htyped as [lts args|lts args runtime_name fv fields f defs Hname Hv Hfields IH];
    intros name v_new fields' fdef Hfield Hvnew Hupdate.
  - discriminate.
  - simpl in Hfield, Hupdate.
    destruct (String.eqb name runtime_name) eqn:Hvalue_name;
      destruct (String.eqb name (field_name f)) eqn:Hfield_name.
    + inversion Hfield; subst fdef.
      inversion Hupdate; subst fields'.
      constructor.
      * exact Hname.
      * exact Hvnew.
      * exact Hfields.
    + apply String.eqb_eq in Hvalue_name.
      assert (name = field_name f) by congruence.
      rewrite H in Hfield_name.
      rewrite String.eqb_refl in Hfield_name.
      discriminate.
    + apply String.eqb_eq in Hfield_name.
      assert (name = runtime_name) by congruence.
      rewrite H in Hvalue_name.
      rewrite String.eqb_refl in Hvalue_name.
      discriminate.
    + destruct (update_value_field name v_new fields) as [fields_tail' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst fields'.
      constructor.
      * exact Hname.
      * exact Hv.
      * eapply IH; eassumption.
Qed.

Lemma runtime_lookup_struct_in_success :
  forall name structs sdef,
    lookup_struct_in name structs = Some sdef ->
    struct_name sdef = name.
Proof.
  intros name structs.
  induction structs as [|h rest IH]; intros sdef Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name (struct_name h)) eqn:Hname.
    + inversion Hlookup; subst.
      apply String.eqb_eq in Hname. symmetry. exact Hname.
    + eapply IH. exact Hlookup.
Qed.

Lemma runtime_lookup_struct_success :
  forall env name sdef,
    lookup_struct name env = Some sdef ->
    struct_name sdef = name.
Proof.
  unfold lookup_struct.
  intros env name sdef Hlookup.
  eapply runtime_lookup_struct_in_success. exact Hlookup.
Qed.

(* ------------------------------------------------------------------ *)
(* Runtime store typing                                                 *)
(* ------------------------------------------------------------------ *)

Definition binding_state_refines (runtime static : binding_state) : Prop :=
  forall p,
    binding_available_b static p = true ->
    binding_available_b runtime p = true.

Lemma binding_state_refines_refl :
  forall st,
    binding_state_refines st st.
Proof.
  unfold binding_state_refines. auto.
Qed.

Lemma binding_state_refines_consume_path :
  forall runtime static p,
    binding_state_refines runtime static ->
    binding_state_refines
      (state_consume_path p runtime)
      (state_consume_path p static).
Proof.
  intros [rconsumed rmoved] [sconsumed smoved] p Href q Havailable.
  unfold binding_state_refines in Href.
  destruct p as [|seg rest]; simpl.
  - discriminate.
  - unfold binding_available_b in Havailable.
    simpl in Havailable.
    destruct sconsumed; simpl in Havailable; try discriminate.
    destruct (path_conflict_b q (seg :: rest)) eqn:Hconflict; simpl in Havailable; try discriminate.
    destruct (path_conflicts_any_b q smoved) eqn:Hstatic; simpl in Havailable; try discriminate.
    assert (Hstatic_available :
      binding_available_b {| st_consumed := false; st_moved_paths := smoved |} q = true).
    { unfold binding_available_b. simpl. rewrite Hstatic. reflexivity. }
    specialize (Href q Hstatic_available).
    destruct rconsumed; simpl in Href |- *; try discriminate.
    unfold binding_available_b in Href |- *.
    simpl in Href |- *.
    rewrite Hconflict.
    exact Href.
Qed.

Lemma binding_state_refines_trans :
  forall st1 st2 st3,
    binding_state_refines st1 st2 ->
    binding_state_refines st2 st3 ->
    binding_state_refines st1 st3.
Proof.
  unfold binding_state_refines.
  intros st1 st2 st3 H12 H23 p Havailable.
  apply H12. apply H23. exact Havailable.
Qed.

Lemma path_prefix_conflicts :
  forall p q,
    path_prefix_b p q = true ->
    path_conflict_b p q = true.
Proof.
  intros p q Hprefix.
  unfold path_conflict_b.
  rewrite Hprefix. reflexivity.
Qed.

Lemma remove_restored_paths_available_noop :
  forall p paths,
    path_conflicts_any_b p paths = false ->
    remove_restored_paths p paths = paths.
Proof.
  intros p paths.
  induction paths as [|q rest IH]; intros Hconflicts.
  - reflexivity.
  - simpl in Hconflicts.
    destruct (path_conflict_b p q) eqn:Hconflict; try discriminate.
    simpl.
    destruct (path_prefix_b p q) eqn:Hprefix.
    + rewrite (path_prefix_conflicts p q Hprefix) in Hconflict. discriminate.
    + f_equal. apply IH. exact Hconflicts.
Qed.

Lemma state_restore_path_available_noop :
  forall st p,
    binding_available_b st p = true ->
    state_restore_path p st = st.
Proof.
  intros [consumed moved] p Havailable.
  unfold binding_available_b in Havailable.
  simpl in Havailable.
  destruct consumed; simpl in Havailable; try discriminate.
  destruct (path_conflicts_any_b p moved) eqn:Hconflicts; simpl in Havailable;
    try discriminate.
  unfold state_restore_path. simpl.
  rewrite (remove_restored_paths_available_noop p moved Hconflicts).
  reflexivity.
Qed.

Lemma binding_state_refines_restore_path_available :
  forall runtime static p,
    binding_state_refines runtime static ->
    binding_available_b static p = true ->
    binding_state_refines
      (state_restore_path p runtime)
      (state_restore_path p static).
Proof.
  intros runtime static p Href Havailable_static.
  pose proof (Href p Havailable_static) as Havailable_runtime.
  rewrite (state_restore_path_available_noop static p Havailable_static).
  rewrite (state_restore_path_available_noop runtime p Havailable_runtime).
  exact Href.
Qed.

Lemma path_conflicts_any_app :
  forall p paths1 paths2,
    path_conflicts_any_b p (paths1 ++ paths2) =
    path_conflicts_any_b p paths1 || path_conflicts_any_b p paths2.
Proof.
  intros p paths1.
  induction paths1 as [|q rest IH]; intros paths2.
  - reflexivity.
  - simpl. rewrite IH.
    destruct (path_conflict_b p q); reflexivity.
Qed.

Lemma binding_state_refines_merge_left :
  forall st2 st3 st4,
    st4 =
      MkBindingState (st_consumed st2 || st_consumed st3)
        (st_moved_paths st2 ++ st_moved_paths st3) ->
    binding_state_refines st2 st4.
Proof.
  intros [consumed2 moved2] [consumed3 moved3] st4 Hst4 p Havailable.
  subst st4.
  unfold binding_state_refines, binding_available_b in *.
  simpl in *.
  rewrite path_conflicts_any_app in Havailable.
  destruct consumed2;
    destruct consumed3;
    destruct (path_conflicts_any_b p moved2);
    destruct (path_conflicts_any_b p moved3);
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma binding_state_refines_merge_right :
  forall st2 st3 st4,
    st4 =
      MkBindingState (st_consumed st2 || st_consumed st3)
        (st_moved_paths st2 ++ st_moved_paths st3) ->
    binding_state_refines st3 st4.
Proof.
  intros [consumed2 moved2] [consumed3 moved3] st4 Hst4 p Havailable.
  subst st4.
  unfold binding_state_refines, binding_available_b in *.
  simpl in *.
  rewrite path_conflicts_any_app in Havailable.
  destruct consumed2;
    destruct consumed3;
    destruct (path_conflicts_any_b p moved2);
    destruct (path_conflicts_any_b p moved3);
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma binding_state_refines_merge_linear_left :
  forall st2 st3 st4,
    st_consumed st2 = st_consumed st3 ->
    st4 =
      MkBindingState (st_consumed st2)
        (st_moved_paths st2 ++ st_moved_paths st3) ->
    binding_state_refines st2 st4.
Proof.
  intros [consumed2 moved2] [consumed3 moved3] st4 Hconsumed Hst4 p Havailable.
  simpl in Hconsumed. subst consumed3.
  subst st4.
  unfold binding_available_b in *.
  simpl in *.
  rewrite path_conflicts_any_app in Havailable.
  destruct consumed2;
    destruct (path_conflicts_any_b p moved2);
    destruct (path_conflicts_any_b p moved3);
    simpl in *; try discriminate; reflexivity.
Qed.

Lemma binding_state_refines_merge_linear_right :
  forall st2 st3 st4,
    st_consumed st2 = st_consumed st3 ->
    st4 =
      MkBindingState (st_consumed st2)
        (st_moved_paths st2 ++ st_moved_paths st3) ->
    binding_state_refines st3 st4.
Proof.
  intros [consumed2 moved2] [consumed3 moved3] st4 Hconsumed Hst4 p Havailable.
  simpl in Hconsumed. subst consumed3.
  subst st4.
  unfold binding_available_b in *.
  simpl in *.
  rewrite path_conflicts_any_app in Havailable.
  destruct consumed2;
    destruct (path_conflicts_any_b p moved2);
    destruct (path_conflicts_any_b p moved3);
    simpl in *; try discriminate; reflexivity.
Qed.

Definition store_entry_typed
    (env : global_env) (s : store) (se : store_entry) (ce : sctx_entry) : Prop :=
  match se, ce with
  | MkStoreEntry sx sT sv sst, (cx, cT, cst, _) =>
      sx = cx /\
      sT = cT /\
      binding_state_refines sst cst /\
      value_has_type env s sv sT
  end.

Definition store_typed (env : global_env) (s : store) (Σ : sctx) : Prop :=
  Forall2 (store_entry_typed env s) s Σ.

Definition store_typed_prefix (env : global_env) (s : store) (Σ : sctx) : Prop :=
  exists entries frame,
    s = entries ++ frame /\
    Forall2 (store_entry_typed env s) entries Σ.

Lemma store_entry_typed_store_preserved :
  forall env s se ce,
    store_entry_typed env s se ce ->
    forall s',
      store_ref_targets_preserved env s s' ->
      store_entry_typed env s' se ce.
Proof.
  intros env s [sx sT sv sst] [[[cx cT] cst] cm] H s' Hpres.
  simpl in *.
  destruct H as [Hname [HT [Hst Hv]]].
  repeat split; try assumption.
  eapply value_has_type_store_preserved; eassumption.
Qed.

Lemma store_typed_store_param_preserved :
  forall env s_param s_entries Σ,
    Forall2 (store_entry_typed env s_param) s_entries Σ ->
    forall s_param',
      store_ref_targets_preserved env s_param s_param' ->
      Forall2 (store_entry_typed env s_param') s_entries Σ.
Proof.
  intros env s_param s_entries Σ H.
  induction H; intros s' Hpres.
  - constructor.
  - constructor.
    + eapply store_entry_typed_store_preserved; eassumption.
    + apply IHForall2. exact Hpres.
Qed.

Lemma store_typed_prefix_empty :
  forall env s,
    store_typed_prefix env s [].
Proof.
  intros env s.
  unfold store_typed_prefix.
  exists [], s.
  split; constructor.
Qed.

Lemma store_typed_prefix_exact :
  forall env s Σ,
    store_typed env s Σ ->
    store_typed_prefix env s Σ.
Proof.
  intros env s Σ Htyped.
  unfold store_typed_prefix.
  exists s, [].
  split.
  - rewrite app_nil_r. reflexivity.
  - exact Htyped.
Qed.

Lemma store_lookup_app_some :
  forall x entries frame se,
    store_lookup x entries = Some se ->
    store_lookup x (entries ++ frame) = Some se.
Proof.
  intros x entries.
  induction entries as [|entry rest IH]; intros frame se Hlookup.
  - discriminate.
  - simpl in Hlookup |- *.
    destruct (ident_eqb x (se_name entry)); [exact Hlookup |].
    apply IH. exact Hlookup.
Qed.

Lemma store_lookup_app_none :
  forall x entries frame,
    store_lookup x entries = None ->
    store_lookup x (entries ++ frame) = store_lookup x frame.
Proof.
  intros x entries.
  induction entries as [|entry rest IH]; intros frame Hlookup.
  - reflexivity.
  - simpl in Hlookup |- *.
    destruct (ident_eqb x (se_name entry)); try discriminate.
    apply IH. exact Hlookup.
Qed.

Lemma store_typed_lookup_entries :
  forall env s_param entries Σ x se,
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_lookup x entries = Some se ->
    exists (T : Ty) (st : binding_state) (m : mutability),
      sctx_lookup x Σ = Some (T, st) /\
      se_name se = x /\
      se_ty se = T /\
      binding_state_refines (se_state se) st /\
      value_has_type env s_param (se_val se) T.
Proof.
  intros env s_param entries Σ x se Htyped.
  induction Htyped as [|se0 ce s_tail Σ_tail Hentry Htail IH]; intros Hlookup.
  - discriminate.
  - destruct se0 as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hlookup.
    destruct (ident_eqb x sx) eqn:Hsx.
    + inversion Hlookup; subst se.
      exists cT, cst, cm.
      apply ident_eqb_eq in Hsx.
      repeat split.
      * simpl. rewrite <- Hname. rewrite <- Hsx. rewrite ident_eqb_refl. reflexivity.
      * simpl. symmetry. exact Hsx.
      * simpl. exact HT.
      * simpl. exact Hst.
      * simpl. rewrite <- HT. exact Hv.
    + destruct (IH Hlookup) as [T [st [m [HΣ [Hn [HTy [Hst' Hv']]]]]]].
      exists T, st, m.
      repeat split.
      * simpl.
        destruct (ident_eqb x cx) eqn:Hcx.
        -- apply ident_eqb_eq in Hcx.
           apply ident_eqb_neq in Hsx. exfalso. apply Hsx.
           rewrite Hname. exact Hcx.
        -- exact HΣ.
      * exact Hn.
      * exact HTy.
      * exact Hst'.
      * exact Hv'.
Qed.

Lemma store_typed_lookup :
  forall env s Σ x se,
    store_typed env s Σ ->
    store_lookup x s = Some se ->
    exists (T : Ty) (st : binding_state) (m : mutability),
      sctx_lookup x Σ = Some (T, st) /\
      se_name se = x /\
      se_ty se = T /\
      binding_state_refines (se_state se) st /\
      value_has_type env s (se_val se) T.
Proof.
  intros env s Σ x se Htyped Hlookup.
  eapply store_typed_lookup_entries; eassumption.
Qed.

Lemma store_typed_lookup_sctx_entries :
  forall env s_param entries Σ x T st,
    Forall2 (store_entry_typed env s_param) entries Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    exists se,
      store_lookup x entries = Some se /\
      se_name se = x /\
      se_ty se = T /\
      binding_state_refines (se_state se) st /\
      value_has_type env s_param (se_val se) T.
Proof.
  intros env s_param entries Σ x T st Htyped.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros Hlookup.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hlookup.
    destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hlookup; subst T st.
      exists (MkStoreEntry sx sT sv sst).
      repeat split.
      * simpl. rewrite Hname. rewrite Hcx. reflexivity.
      * simpl. apply ident_eqb_eq in Hcx. rewrite Hname. symmetry. exact Hcx.
      * simpl. exact HT.
      * simpl. exact Hst.
      * simpl. rewrite <- HT. exact Hv.
    + destruct (IH Hlookup) as [se' [Hs [Hn [HTy [Hst' Hv']]]]].
      exists se'.
      repeat split.
      * simpl.
        destruct (ident_eqb x sx) eqn:Hsx.
        -- apply ident_eqb_eq in Hsx.
           apply ident_eqb_neq in Hcx. exfalso. apply Hcx.
           rewrite <- Hname. exact Hsx.
        -- exact Hs.
      * exact Hn.
      * exact HTy.
      * exact Hst'.
      * exact Hv'.
Qed.

Lemma store_typed_lookup_sctx :
  forall env s Σ x T st,
    store_typed env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    exists se,
      store_lookup x s = Some se /\
      se_name se = x /\
      se_ty se = T /\
      binding_state_refines (se_state se) st /\
      value_has_type env s (se_val se) T.
Proof.
  intros env s Σ x T st Htyped Hlookup.
  eapply store_typed_lookup_sctx_entries; eassumption.
Qed.

Lemma store_typed_prefix_lookup_sctx :
  forall env s Σ x T st,
    store_typed_prefix env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    exists se,
      store_lookup x s = Some se /\
      se_name se = x /\
      se_ty se = T /\
      binding_state_refines (se_state se) st /\
      value_has_type env s (se_val se) T.
Proof.
  intros env s Σ x T st Htyped Hlookup.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  destruct (store_typed_lookup_sctx_entries env s entries Σ x T st
    Hentries Hlookup) as [se [Hstore [Hname [HT [Hst Hv]]]]].
  exists se.
  repeat split; try assumption.
  subst s.
  apply store_lookup_app_some. exact Hstore.
Qed.

Lemma store_typed_add :
  forall env s Σ x T m v,
    store_typed env s Σ ->
    value_has_type env s v T ->
    store_ref_targets_preserved env s (store_add x T v s) ->
    store_typed env (store_add x T v s) (sctx_add x T m Σ).
Proof.
  intros env s Σ x T m v Htyped Hv Hpres.
  unfold store_add, sctx_add, store_typed.
  constructor.
  - simpl. repeat split; try reflexivity.
    eapply value_has_type_store_preserved; eassumption.
  - eapply store_typed_store_param_preserved; eassumption.
Qed.

Lemma store_typed_prefix_add :
  forall env s Σ x T m v,
    store_typed_prefix env s Σ ->
    value_has_type env s v T ->
    store_ref_targets_preserved env s (store_add x T v s) ->
    store_typed_prefix env (store_add x T v s) (sctx_add x T m Σ).
Proof.
  intros env s Σ x T m v Htyped Hv Hpres.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  unfold store_typed_prefix, store_add, sctx_add.
  exists (MkStoreEntry x T v (binding_state_of_bool false) :: entries), frame.
  split.
  - simpl. subst s. reflexivity.
  - constructor.
    + simpl. repeat split; try reflexivity.
      eapply value_has_type_store_preserved; eassumption.
    + eapply store_typed_store_param_preserved; eassumption.
Qed.

Lemma store_typed_add_compatible :
  forall env Ω s Σ x T_actual T_expected m v,
    store_typed env s Σ ->
    value_has_type env s v T_actual ->
    ty_compatible Ω T_actual T_expected ->
    store_ref_targets_preserved env s (store_add x T_expected v s) ->
    store_typed env (store_add x T_expected v s)
      (sctx_add x T_expected m Σ).
Proof.
  intros env Ω s Σ x T_actual T_expected m v Hstore Hv Hcompat Hpres.
  eapply store_typed_add.
  - exact Hstore.
  - eapply value_has_type_compatible; eassumption.
  - exact Hpres.
Qed.

Lemma store_typed_prefix_add_compatible :
  forall env Ω s Σ x T_actual T_expected m v,
    store_typed_prefix env s Σ ->
    value_has_type env s v T_actual ->
    ty_compatible Ω T_actual T_expected ->
    store_ref_targets_preserved env s (store_add x T_expected v s) ->
    store_typed_prefix env (store_add x T_expected v s)
      (sctx_add x T_expected m Σ).
Proof.
  intros env Ω s Σ x T_actual T_expected m v Hstore Hv Hcompat Hpres.
  eapply store_typed_prefix_add.
  - exact Hstore.
  - eapply value_has_type_compatible; eassumption.
  - exact Hpres.
Qed.

Lemma store_typed_remove_entries :
  forall env s_param s_target entries Σ x,
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    Forall2 (store_entry_typed env s_target)
      (store_remove x entries) (sctx_remove x Σ).
Proof.
  intros env s_param s_target entries Σ x Htyped Hpres.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH].
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + eapply store_typed_store_param_preserved; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * eapply store_typed_store_param_preserved.
        -- exact IH.
        -- apply store_ref_targets_preserved_refl.
Qed.

Lemma store_typed_remove :
  forall env s Σ x,
    store_typed env s Σ ->
    store_ref_targets_preserved env s (store_remove x s) ->
    store_typed env (store_remove x s) (sctx_remove x Σ).
Proof.
  intros env s Σ x Htyped Hpres.
  eapply store_typed_remove_entries; eassumption.
Qed.

Lemma store_entry_typed_store_remove_excluding_root :
  forall env s root se ce,
    store_entry_typed env s se ce ->
    store_entry_refs_exclude_root root se ->
    store_entry_typed env (store_remove root s) se ce.
Proof.
  intros env s root [sx sT sv sst] [[[cx cT] cst] cm] Htyped Hexclude.
  simpl in *.
  destruct Htyped as [Hname [HT [Hst Hv]]].
  inversion Hexclude; subst.
  repeat split; try assumption.
  eapply value_has_type_store_remove_excluding_root; eassumption.
Qed.

Lemma store_typed_store_param_remove_excluding_root :
  forall env s_param entries Σ root,
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_refs_exclude_root root entries ->
    Forall2 (store_entry_typed env (store_remove root s_param)) entries Σ.
Proof.
  intros env s_param entries Σ root Htyped.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros Hexclude.
  - constructor.
  - inversion Hexclude; subst.
    constructor.
    + eapply store_entry_typed_store_remove_excluding_root; eassumption.
    + apply IH. assumption.
Qed.

Lemma store_typed_remove_entries_excluding_root :
  forall env s_param entries Σ root,
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_refs_exclude_root root (store_remove root entries) ->
    Forall2 (store_entry_typed env (store_remove root s_param))
      (store_remove root entries) (sctx_remove root Σ).
Proof.
  intros env s_param entries Σ root Htyped.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros Hexclude.
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hexclude |- *.
    destruct (ident_eqb root sx) eqn:Hsx;
      destruct (ident_eqb root cx) eqn:Hcx.
    + eapply store_typed_store_param_remove_excluding_root; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + inversion Hexclude; subst.
      constructor.
      * eapply store_entry_typed_store_remove_excluding_root.
        -- simpl. repeat split; try assumption.
        -- assumption.
      * apply IH. assumption.
Qed.

Lemma store_typed_remove_excluding_root :
  forall env s Σ root,
    store_typed env s Σ ->
    store_refs_exclude_root root (store_remove root s) ->
    store_typed env (store_remove root s) (sctx_remove root Σ).
Proof.
  intros env s Σ root Htyped Hexclude.
  eapply store_typed_remove_entries_excluding_root; eassumption.
Qed.

Lemma store_ref_targets_preserved_remove_after_absent_root :
  forall env s s' root,
    store_ref_targets_preserved env s s' ->
    store_lookup root s = None ->
    store_ref_targets_preserved env s (store_remove root s').
Proof.
  unfold store_ref_targets_preserved.
  intros env s s' root Hpres Habsent x path se v T Hlookup Hvalue Htype.
  destruct (ident_eqb root x) eqn:Hroot.
  - apply ident_eqb_eq in Hroot. subst x.
    rewrite Hlookup in Habsent. discriminate.
  - destruct (Hpres x path se v T Hlookup Hvalue Htype)
      as [se' [v' [Hlookup' [Hvalue' Htype']]]].
    exists se', v'. repeat split; try assumption.
    rewrite store_lookup_remove_neq; assumption.
Qed.

Lemma store_update_state_ref_targets_preserved :
  forall env s x f s',
    store_update_state x f s = Some s' ->
    store_ref_targets_preserved env s s'.
Proof.
  unfold store_ref_targets_preserved.
  intros env s x f s' Hupdate y path se v T Hlookup Hvalue Htype.
  revert s' Hupdate Hlookup.
  induction s as [|e tail IH]; intros s' Hupdate Hlookup.
  - discriminate.
  - simpl in Hupdate, Hlookup.
    destruct e as [ex eT ev est].
    simpl in Hupdate, Hlookup.
    destruct (ident_eqb x ex) eqn:Hx.
    + inversion Hupdate; subst.
      destruct (ident_eqb y ex) eqn:Hy.
      * inversion Hlookup; subst.
        exists (MkStoreEntry ex eT ev (f est)), v.
        split; [simpl; rewrite Hy; reflexivity |].
        split; simpl; assumption.
      * exists se.
        exists v.
        split; [simpl; rewrite Hy; exact Hlookup |].
        split; assumption.
    + destruct (store_update_state x f tail) as [tail' |] eqn:Htail;
        try discriminate.
      inversion Hupdate; subst.
      destruct (ident_eqb y ex) eqn:Hy.
      * inversion Hlookup; subst.
        exists (MkStoreEntry ex eT ev est), v.
        split; [simpl; rewrite Hy; reflexivity |].
        split; simpl; assumption.
      * destruct (IH tail' eq_refl Hlookup)
          as [se' [v' [Hlookup' [Hvalue' Htype']]]].
        exists se', v'.
        split; [simpl; rewrite Hy; exact Hlookup' |].
        split; assumption.
Qed.

Lemma store_typed_update_state_entries :
  forall env s_param s_target entries Σ x f entries' Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    (forall runtime static,
      binding_state_refines runtime static ->
      binding_state_refines (f runtime) (f static)) ->
    store_update_state x f entries = Some entries' ->
    sctx_update_state x f Σ = Some Σ' ->
    Forall2 (store_entry_typed env s_target) entries' Σ'.
Proof.
  intros env s_param s_target entries Σ x f entries' Σ' Htyped Hpres Hrefines.
  revert entries' Σ'.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros entries' Σ' Hs HΣ.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hs, HΣ.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hs; subst entries'.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- apply Hrefines. exact Hst.
        -- eapply value_has_type_store_preserved; eassumption.
      * eapply store_typed_store_param_preserved; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_state x f s_tail) as [s_tail' |] eqn:Hs_tail;
        try discriminate.
      destruct (sctx_update_state x f Σ_tail) as [Σ_tail' |] eqn:HΣ_tail;
        try discriminate.
      inversion Hs; subst entries'.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * eapply IH.
        -- reflexivity.
        -- reflexivity.
Qed.

Lemma store_typed_update_state :
  forall env s Σ x f s' Σ',
    store_typed env s Σ ->
    (forall runtime static,
      binding_state_refines runtime static ->
      binding_state_refines (f runtime) (f static)) ->
    store_update_state x f s = Some s' ->
    sctx_update_state x f Σ = Some Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x f s' Σ' Htyped Hrefines Hs HΣ.
  eapply store_typed_update_state_entries.
  - exact Htyped.
  - eapply store_update_state_ref_targets_preserved. exact Hs.
  - exact Hrefines.
  - exact Hs.
  - exact HΣ.
Qed.

Lemma store_typed_restore_path :
  forall env s Σ x p s' Σ',
    store_typed env s Σ ->
    (forall runtime static,
      binding_state_refines runtime static ->
      binding_state_refines
        (state_restore_path p runtime)
        (state_restore_path p static)) ->
    store_restore_path x p s = Some s' ->
    sctx_restore_path Σ x p = infer_ok Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x p s' Σ' Htyped Hrestore_refines Hs HΣ.
  unfold store_restore_path in Hs.
  unfold sctx_restore_path in HΣ.
  destruct (sctx_update_state x (state_restore_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion HΣ; subst Σ0.
  eapply store_typed_update_state; eassumption.
Qed.

Lemma store_typed_update_restore_available_entries :
  forall env s_param s_target entries Σ x p T st entries' Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    sctx_lookup x Σ = Some (T, st) ->
    binding_available_b st p = true ->
    store_update_state x (state_restore_path p) entries = Some entries' ->
    sctx_update_state x (state_restore_path p) Σ = Some Σ' ->
    Forall2 (store_entry_typed env s_target) entries' Σ'.
Proof.
  intros env s_param s_target entries Σ x p T st entries' Σ'
    Htyped Hpres Hlookup Havailable.
  revert entries' Σ' Hlookup.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros entries' Σ' Hlookup Hs HΣ.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Href Hv]]].
    simpl in Hlookup, Hs, HΣ.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hlookup; subst T st.
      inversion Hs; subst entries'.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- apply binding_state_refines_restore_path_available; assumption.
        -- eapply value_has_type_store_preserved; eassumption.
      * eapply store_typed_store_param_preserved; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_state x (state_restore_path p) s_tail)
        as [s_tail' |] eqn:Hs_tail; try discriminate.
      destruct (sctx_update_state x (state_restore_path p) Σ_tail)
        as [Σ_tail' |] eqn:HΣ_tail; try discriminate.
      inversion Hs; subst entries'.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * eapply IH.
        -- exact Hlookup.
        -- reflexivity.
        -- reflexivity.
Qed.

Lemma store_typed_update_restore_available :
  forall env s Σ x p T st s' Σ',
    store_typed env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    binding_available_b st p = true ->
    store_update_state x (state_restore_path p) s = Some s' ->
    sctx_update_state x (state_restore_path p) Σ = Some Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x p T st s' Σ' Htyped Hlookup Havailable Hs HΣ.
  eapply store_typed_update_restore_available_entries.
  - exact Htyped.
  - eapply store_update_state_ref_targets_preserved. exact Hs.
  - exact Hlookup.
  - exact Havailable.
  - exact Hs.
  - exact HΣ.
Qed.

Lemma store_typed_restore_available_path :
  forall env s Σ x p T st s' Σ',
    store_typed env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    binding_available_b st p = true ->
    store_restore_path x p s = Some s' ->
    sctx_restore_path Σ x p = infer_ok Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x p T st s' Σ' Htyped Hlookup Havailable Hs HΣ.
  unfold store_restore_path in Hs.
  unfold sctx_restore_path in HΣ.
  destruct (sctx_update_state x (state_restore_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion HΣ; subst Σ0.
  eapply store_typed_update_restore_available; eassumption.
Qed.

Lemma store_typed_consume_path :
  forall env s Σ x p s' Σ',
    store_typed env s Σ ->
    store_consume_path x p s = Some s' ->
    sctx_consume_path Σ x p = infer_ok Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x p s' Σ' Htyped Hs HΣ.
  unfold store_consume_path in Hs.
  unfold sctx_consume_path, sctx_path_available in HΣ.
  destruct (store_lookup x s) as [se |] eqn:Hslookup; try discriminate.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:HΣlookup; try discriminate.
  destruct (binding_available_b (se_state se) p) eqn:Hsavailable; try discriminate.
  destruct (binding_available_b st p) eqn:HΣavailable; try discriminate.
  destruct (sctx_update_state x (state_consume_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion HΣ; subst Σ0.
  eapply store_typed_update_state.
  - exact Htyped.
  - intros runtime static Href.
    apply binding_state_refines_consume_path. exact Href.
  - exact Hs.
  - exact Hupdate.
Qed.

Lemma store_mark_used_ref_targets_preserved :
  forall env s x,
    store_ref_targets_preserved env s (store_mark_used x s).
Proof.
  unfold store_ref_targets_preserved.
  intros env s x y path se v T Hlookup Hvalue Htype.
  induction s as [|e tail IH].
  - discriminate.
  - simpl in Hlookup |- *.
    destruct e as [ex eT ev est].
    simpl in Hlookup |- *.
    destruct (ident_eqb x ex) eqn:Hx;
      destruct (ident_eqb y ex) eqn:Hy.
    + inversion Hlookup; subst.
      exists (MkStoreEntry ex eT ev (state_consume_path [] est)), v.
      split; [simpl; rewrite Hy; reflexivity |].
      split; simpl; assumption.
    + exists se.
      exists v.
      split; [simpl; rewrite Hy; exact Hlookup |].
      split; assumption.
    + inversion Hlookup; subst.
      exists (MkStoreEntry ex eT ev est), v.
      split; [simpl; rewrite Hy; reflexivity |].
      split; simpl; assumption.
    + destruct (IH Hlookup) as [se' [v' [Hlookup' [Hvalue' Htype']]]].
      exists se', v'.
      split; [simpl; rewrite Hy; exact Hlookup' |].
      split; assumption.
Qed.

Lemma store_typed_mark_used_entries :
  forall env s_param s_target entries Σ x Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    sctx_update_state x (state_consume_path []) Σ = Some Σ' ->
    Forall2 (store_entry_typed env s_target) (store_mark_used x entries) Σ'.
Proof.
  intros env s_param s_target entries Σ x Σ' Htyped Hpres HΣ.
  revert Σ' HΣ.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros Σ' HΣ.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in HΣ.
    simpl.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- unfold binding_state_refines. intros p Havailable.
           simpl in Havailable. discriminate.
        -- eapply value_has_type_store_preserved; eassumption.
      * eapply store_typed_store_param_preserved; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (sctx_update_state x (state_consume_path []) Σ_tail)
        as [Σ_tail' |] eqn:Htail_update; try discriminate.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * apply IH. reflexivity.
Qed.

Lemma store_typed_mark_used :
  forall env s Σ x Σ',
    store_typed env s Σ ->
    sctx_update_state x (state_consume_path []) Σ = Some Σ' ->
    store_typed env (store_mark_used x s) Σ'.
Proof.
  intros env s Σ x Σ' Htyped HΣ.
  eapply store_typed_mark_used_entries.
  - exact Htyped.
  - apply store_mark_used_ref_targets_preserved.
  - exact HΣ.
Qed.

Lemma store_typed_update_val_entries :
  forall env s_param s_target entries Σ x v T st entries',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s_param v T ->
    store_update_val x v entries = Some entries' ->
    Forall2 (store_entry_typed env s_target) entries' Σ.
Proof.
  intros env s_param s_target entries Σ x v T st entries'
    Htyped Hpres Hlookup Hv Hupdate.
  revert entries' Hupdate T st Hlookup Hv.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros entries' Hupdate T st Hlookup Hv.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hsv]]].
    simpl in Hupdate, Hlookup.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hupdate; subst entries'.
      inversion Hlookup; subst T st.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact Hst.
        -- rewrite HT. eapply value_has_type_store_preserved; eassumption.
      * eapply store_typed_store_param_preserved; eassumption.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_val x v s_tail) as [s_tail' |] eqn:Htail_update;
        try discriminate.
      inversion Hupdate; subst entries'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * eapply IH.
        -- reflexivity.
        -- exact Hlookup.
        -- exact Hv.
Qed.

Lemma store_typed_update_val :
  forall env s Σ x v T st s',
    store_typed env s Σ ->
    store_ref_targets_preserved env s s' ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s v T ->
    store_update_val x v s = Some s' ->
    store_typed env s' Σ.
Proof.
  intros env s Σ x v T st s' Htyped Hpres Hlookup Hv Hupdate.
  eapply store_typed_update_val_entries; eassumption.
Qed.

Lemma store_typed_lookup_path :
  forall env s Σ x path v,
    store_typed env s Σ ->
    store_lookup_path x path s = Some v ->
    exists (se : store_entry) (T_root : Ty) (st : binding_state) (m : mutability),
      sctx_lookup x Σ = Some (T_root, st) /\
      se_name se = x /\
      se_ty se = T_root /\
      store_lookup x s = Some se /\
      value_lookup_path (se_val se) path = Some v.
Proof.
  intros env s Σ x path v Htyped Hpath.
  unfold store_lookup_path in Hpath.
  destruct (store_lookup x s) as [se |] eqn:Hlookup; try discriminate.
  destruct (store_typed_lookup env s Σ x se Htyped Hlookup)
    as [T_root [st [m [HΣ [Hn [HTy [Hst Hv]]]]]]].
  exists se, T_root, st, m.
  repeat split; try assumption.
Qed.

Lemma value_lookup_path_nil :
  forall v,
    value_lookup_path v [] = Some v.
Proof.
  destruct v; reflexivity.
Qed.

Lemma value_update_path_nil :
  forall v v_new,
    value_update_path v [] v_new = Some v_new.
Proof.
  destruct v; reflexivity.
Qed.

Lemma store_typed_update_path_entries :
  forall env s_param s_target entries Σ x path v_new entries',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_ref_targets_preserved env s_param s_target ->
    (forall se T st,
      store_lookup x entries = Some se ->
      sctx_lookup x Σ = Some (T, st) ->
      forall v_root,
        value_update_path (se_val se) path v_new = Some v_root ->
        value_has_type env s_param v_root T) ->
    store_update_path x path v_new entries = Some entries' ->
    Forall2 (store_entry_typed env s_target) entries' Σ.
Proof.
  intros env s_param s_target entries Σ x path v_new entries'
    Htyped Hpres Hroot Hupdate.
  revert entries' Hupdate Hroot.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros entries' Hupdate Hroot.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hupdate.
    destruct (ident_eqb x sx) eqn:Hsx.
    + destruct (value_update_path sv path v_new) as [v_root |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst entries'.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact Hst.
        -- rewrite HT.
           eapply value_has_type_store_preserved.
           ++ eapply Hroot.
              ** simpl. rewrite Hsx. reflexivity.
              ** simpl. rewrite <- Hname.
                 apply ident_eqb_eq in Hsx.
                 rewrite <- Hsx. rewrite ident_eqb_refl. reflexivity.
              ** exact Hvalue.
           ++ exact Hpres.
      * eapply store_typed_store_param_preserved; eassumption.
    + destruct (store_update_path x path v_new s_tail) as [s_tail' |]
        eqn:Htail_update; try discriminate.
      inversion Hupdate; subst entries'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_preserved; eassumption.
      * eapply IH.
        -- reflexivity.
        -- intros se0 T st Hlookup HΣ v_root Hvalue.
           eapply Hroot.
           ++ simpl. rewrite Hsx. exact Hlookup.
           ++ simpl.
              destruct (ident_eqb x cx) eqn:Hcx.
              ** apply ident_eqb_eq in Hcx.
                 apply ident_eqb_neq in Hsx. exfalso. apply Hsx.
                 rewrite Hname. exact Hcx.
              ** exact HΣ.
           ++ exact Hvalue.
Qed.

Lemma store_typed_update_path :
  forall env s Σ x path v_new s',
    store_typed env s Σ ->
    store_ref_targets_preserved env s s' ->
    (forall se T st,
      store_lookup x s = Some se ->
      sctx_lookup x Σ = Some (T, st) ->
      forall v_root,
        value_update_path (se_val se) path v_new = Some v_root ->
        value_has_type env s v_root T) ->
    store_update_path x path v_new s = Some s' ->
    store_typed env s' Σ.
Proof.
  intros env s Σ x path v_new s' Htyped Hpres Hroot Hupdate.
  eapply store_typed_update_path_entries; eassumption.
Qed.

Lemma store_update_state_prefix_hit :
  forall env s_param entries Σ frame x f s' Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    store_update_state x f (entries ++ frame) = Some s' ->
    sctx_update_state x f Σ = Some Σ' ->
    exists entries',
      store_update_state x f entries = Some entries' /\
      s' = entries' ++ frame.
Proof.
  intros env s_param entries Σ frame x f s' Σ' Htyped.
  revert s' Σ'.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros s' Σ' Hs HΣ.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hs, HΣ.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hs; subst s'.
      inversion HΣ; subst Σ'.
      exists (MkStoreEntry sx sT sv (f sst) :: s_tail).
      split; [simpl; rewrite Hsx; reflexivity | reflexivity].
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_state x f (s_tail ++ frame)) as [s_tail' |]
        eqn:Hs_tail; try discriminate.
      destruct (sctx_update_state x f Σ_tail) as [Σ_tail' |]
        eqn:HΣ_tail; try discriminate.
      inversion Hs; subst s'.
      inversion HΣ; subst Σ'.
      destruct (IH s_tail' Σ_tail' eq_refl eq_refl)
        as [entries' [Hentries Hs']].
      subst s_tail'.
      exists (MkStoreEntry sx sT sv sst :: entries').
      split.
      * simpl. rewrite Hsx. rewrite Hentries. reflexivity.
      * reflexivity.
Qed.

Lemma store_update_restore_available_prefix_hit :
  forall env s_param entries Σ frame x p T st s' Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    store_update_state x (state_restore_path p) (entries ++ frame) = Some s' ->
    sctx_update_state x (state_restore_path p) Σ = Some Σ' ->
    exists entries',
      store_update_state x (state_restore_path p) entries = Some entries' /\
      s' = entries' ++ frame.
Proof.
  intros env s_param entries Σ frame x p T st s' Σ'
    Htyped Hlookup Hs HΣ.
  eapply store_update_state_prefix_hit; eassumption.
Qed.

Lemma store_mark_used_prefix_hit :
  forall env s_param entries Σ frame x Σ',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    sctx_update_state x (state_consume_path []) Σ = Some Σ' ->
    store_mark_used x (entries ++ frame) = store_mark_used x entries ++ frame.
Proof.
  intros env s_param entries Σ frame x Σ' Htyped.
  revert Σ'.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros Σ' HΣ.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in HΣ.
    simpl.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + reflexivity.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (sctx_update_state x (state_consume_path []) Σ_tail)
        as [Σ_tail' |] eqn:HΣ_tail; try discriminate.
      rewrite (IH Σ_tail' eq_refl).
      reflexivity.
Qed.

Lemma store_update_val_prefix_hit :
  forall env s_param entries Σ frame x v T st s',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    store_update_val x v (entries ++ frame) = Some s' ->
    exists entries',
      store_update_val x v entries = Some entries' /\
      s' = entries' ++ frame.
Proof.
  intros env s_param entries Σ frame x v T st s' Htyped.
  revert s' T st.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros s' T st Hlookup Hupdate.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hlookup, Hupdate.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hupdate; subst s'.
      exists (MkStoreEntry sx sT v sst :: s_tail).
      split; [simpl; rewrite Hsx; reflexivity | reflexivity].
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_val x v (s_tail ++ frame)) as [s_tail' |]
        eqn:Htail_update; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH s_tail' T st Hlookup eq_refl)
        as [entries' [Hentries Hs']].
      subst s_tail'.
      exists (MkStoreEntry sx sT sv sst :: entries').
      split.
      * simpl. rewrite Hsx. rewrite Hentries. reflexivity.
      * reflexivity.
Qed.

Lemma store_update_path_prefix_split :
  forall x path v_new entries frame s',
    store_update_path x path v_new (entries ++ frame) = Some s' ->
    (exists entries',
      store_update_path x path v_new entries = Some entries' /\
      s' = entries' ++ frame) \/
    (store_update_path x path v_new entries = None /\
     exists frame',
       store_update_path x path v_new frame = Some frame' /\
       s' = entries ++ frame').
Proof.
  intros x path v_new entries.
  induction entries as [|se s_tail IH]; intros frame s' Hupdate.
  - right.
    split; [reflexivity |].
    exists s'. split; [exact Hupdate | reflexivity].
  - simpl in Hupdate.
    destruct se as [sx sT sv sst].
    simpl in Hupdate.
    destruct (ident_eqb x sx) eqn:Hsx.
    + destruct (value_update_path sv path v_new) as [v_root |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst s'.
      left.
      exists (MkStoreEntry sx sT v_root sst :: s_tail).
      split; [simpl; rewrite Hsx; rewrite Hvalue; reflexivity | reflexivity].
    + destruct (store_update_path x path v_new (s_tail ++ frame))
        as [s_tail_frame' |] eqn:Htail; try discriminate.
      inversion Hupdate; subst s'.
      destruct (IH frame s_tail_frame' Htail)
        as [[entries' [Hentries Hs']]
           | [Hentries_none [frame' [Hframe Hs']]]].
      * subst s_tail_frame'.
        left.
        exists (MkStoreEntry sx sT sv sst :: entries').
        split.
        -- simpl. rewrite Hsx. rewrite Hentries. reflexivity.
        -- reflexivity.
      * subst s_tail_frame'.
        right.
        split.
        -- simpl. rewrite Hsx. rewrite Hentries_none. reflexivity.
        -- exists frame'. split; [exact Hframe | reflexivity].
Qed.

Lemma store_update_val_lookup_none :
  forall x v entries entries' y,
    store_update_val x v entries = Some entries' ->
    store_lookup y entries = None ->
    store_lookup y entries' = None.
Proof.
  intros x v entries.
  revert x v.
  induction entries as [|se rest IH]; intros x v entries' y Hupdate Hlookup.
  - discriminate.
  - destruct se as [sx sT sv sst].
    simpl in Hupdate, Hlookup |- *.
    destruct (ident_eqb x sx) eqn:Hsx.
    + inversion Hupdate; subst entries'.
      simpl.
      destruct (ident_eqb y sx); try discriminate.
      exact Hlookup.
    + remember (store_update_val x v rest) as updated eqn:Htail.
      symmetry in Htail.
      destruct updated as [rest' |]; try discriminate.
      inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy; try discriminate.
      simpl. rewrite Hy. exact (IH x v rest' y Htail Hlookup).
Qed.

Lemma store_update_path_lookup_none :
  forall x path v_new entries entries' y,
    store_update_path x path v_new entries = Some entries' ->
    store_lookup y entries = None ->
    store_lookup y entries' = None.
Proof.
  intros x path v_new entries.
  revert x path v_new.
  induction entries as [|se rest IH];
    intros x path v_new entries' y Hupdate Hlookup.
  - discriminate.
  - destruct se as [sx sT sv sst].
    simpl in Hupdate, Hlookup |- *.
    destruct (ident_eqb x sx) eqn:Hsx.
    + destruct (value_update_path sv path v_new) as [v_root |]
        eqn:Hvalue; try discriminate.
      inversion Hupdate; subst entries'.
      simpl.
      destruct (ident_eqb y sx); try discriminate.
      exact Hlookup.
    + remember (store_update_path x path v_new rest) as updated eqn:Htail.
      symmetry in Htail.
      destruct updated as [rest' |]; try discriminate.
      inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy; try discriminate.
      simpl. rewrite Hy. exact (IH x path v_new rest' y Htail Hlookup).
Qed.

Lemma store_update_path_exists_from_lookup :
  forall x path v_new entries se v_root,
    store_lookup x entries = Some se ->
    value_update_path (se_val se) path v_new = Some v_root ->
    exists entries',
      store_update_path x path v_new entries = Some entries'.
Proof.
  intros x path v_new entries.
  induction entries as [|entry rest IH]; intros se v_root Hlookup Hvalue.
  - discriminate.
  - destruct entry as [sx sT sv sst].
    simpl in Hlookup |- *.
    destruct (ident_eqb x sx) eqn:Hsx.
    + inversion Hlookup; subst se.
      simpl in Hvalue.
      rewrite Hvalue.
      eexists. reflexivity.
    + destruct (IH se v_root Hlookup Hvalue) as [rest' Hrest].
      rewrite Hrest.
      eexists. reflexivity.
Qed.

Lemma store_typed_prefix_update_state :
  forall env s Σ x f s' Σ',
    store_typed_prefix env s Σ ->
    (forall runtime static,
      binding_state_refines runtime static ->
      binding_state_refines (f runtime) (f static)) ->
    store_update_state x f s = Some s' ->
    sctx_update_state x f Σ = Some Σ' ->
    store_typed_prefix env s' Σ'.
Proof.
  intros env s Σ x f s' Σ' Htyped Hrefines Hs HΣ.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs_eq Hentries]]].
  subst s.
  destruct (store_update_state_prefix_hit env (entries ++ frame)
    entries Σ frame x f s' Σ' Hentries Hs HΣ)
    as [entries' [Hentries_update Hs']].
  subst s'.
  unfold store_typed_prefix.
  exists entries', frame.
  split; [reflexivity |].
  eapply store_typed_update_state_entries.
  - exact Hentries.
  - eapply store_update_state_ref_targets_preserved.
    exact Hs.
  - exact Hrefines.
  - exact Hentries_update.
  - exact HΣ.
Qed.

Lemma store_typed_prefix_restore_path :
  forall env s Σ x p s' Σ',
    store_typed_prefix env s Σ ->
    (forall runtime static,
      binding_state_refines runtime static ->
      binding_state_refines
        (state_restore_path p runtime)
        (state_restore_path p static)) ->
    store_restore_path x p s = Some s' ->
    sctx_restore_path Σ x p = infer_ok Σ' ->
    store_typed_prefix env s' Σ'.
Proof.
  intros env s Σ x p s' Σ' Htyped Hrestore_refines Hs HΣ.
  unfold store_restore_path in Hs.
  unfold sctx_restore_path in HΣ.
  destruct (sctx_update_state x (state_restore_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion HΣ; subst Σ0.
  eapply store_typed_prefix_update_state; eassumption.
Qed.

Lemma store_typed_prefix_restore_available_path :
  forall env s Σ x p T st s' Σ',
    store_typed_prefix env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    binding_available_b st p = true ->
    store_restore_path x p s = Some s' ->
    sctx_restore_path Σ x p = infer_ok Σ' ->
    store_typed_prefix env s' Σ'.
Proof.
  intros env s Σ x p T st s' Σ' Htyped Hlookup Havailable Hs HΣ.
  unfold store_restore_path in Hs.
  unfold sctx_restore_path in HΣ.
  destruct (sctx_update_state x (state_restore_path p) Σ) as [Σ0 |] eqn:Hupdate;
    try discriminate.
  inversion HΣ; subst Σ0.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs_eq Hentries]]].
  subst s.
  destruct (store_update_restore_available_prefix_hit env (entries ++ frame)
    entries Σ frame x p T st s' Σ' Hentries Hlookup Hs Hupdate)
    as [entries' [Hentries_update Hs']].
  subst s'.
  unfold store_typed_prefix.
  exists entries', frame.
  split; [reflexivity |].
  eapply store_typed_update_restore_available_entries.
  - exact Hentries.
  - eapply store_update_state_ref_targets_preserved.
    exact Hs.
  - exact Hlookup.
  - exact Havailable.
  - exact Hentries_update.
  - exact Hupdate.
Qed.

Lemma store_typed_prefix_consume_path :
  forall env s Σ x p s' Σ',
    store_typed_prefix env s Σ ->
    store_consume_path x p s = Some s' ->
    sctx_consume_path Σ x p = infer_ok Σ' ->
    store_typed_prefix env s' Σ'.
Proof.
  intros env s Σ x p s' Σ' Htyped Hs HΣ.
  unfold store_consume_path in Hs.
  unfold sctx_consume_path, sctx_path_available in HΣ.
  destruct (store_lookup x s) as [se |] eqn:Hslookup; try discriminate.
  destruct (sctx_lookup x Σ) as [[T st] |] eqn:HΣlookup; try discriminate.
  destruct (binding_available_b (se_state se) p) eqn:Hsavailable; try discriminate.
  destruct (binding_available_b st p) eqn:HΣavailable; try discriminate.
  destruct (sctx_update_state x (state_consume_path p) Σ) as [Σ0 |]
    eqn:Hupdate; try discriminate.
  inversion HΣ; subst Σ0.
  eapply store_typed_prefix_update_state.
  - exact Htyped.
  - intros runtime static Href.
    apply binding_state_refines_consume_path. exact Href.
  - exact Hs.
  - exact Hupdate.
Qed.

Lemma store_typed_prefix_mark_used :
  forall env s Σ x Σ',
    store_typed_prefix env s Σ ->
    sctx_update_state x (state_consume_path []) Σ = Some Σ' ->
    store_typed_prefix env (store_mark_used x s) Σ'.
Proof.
  intros env s Σ x Σ' Htyped HΣ.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  rewrite (store_mark_used_prefix_hit env (entries ++ frame)
    entries Σ frame x Σ' Hentries HΣ).
  unfold store_typed_prefix.
  exists (store_mark_used x entries), frame.
  split; [reflexivity |].
  eapply store_typed_mark_used_entries.
  - exact Hentries.
  - rewrite <- (store_mark_used_prefix_hit env (entries ++ frame)
      entries Σ frame x Σ' Hentries HΣ).
    apply store_mark_used_ref_targets_preserved.
  - exact HΣ.
Qed.

Lemma store_typed_prefix_update_val :
  forall env s Σ x v T st s',
    store_typed_prefix env s Σ ->
    store_ref_targets_preserved env s s' ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s v T ->
    store_update_val x v s = Some s' ->
    store_typed_prefix env s' Σ.
Proof.
  intros env s Σ x v T st s' Htyped Hpres Hlookup Hv Hupdate.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  destruct (store_update_val_prefix_hit env (entries ++ frame)
    entries Σ frame x v T st s' Hentries Hlookup Hupdate)
    as [entries' [Hentries_update Hs']].
  subst s'.
  unfold store_typed_prefix.
  exists entries', frame.
  split; [reflexivity |].
  eapply store_typed_update_val_entries; eassumption.
Qed.

Lemma store_typed_prefix_update_path :
  forall env s Σ x path v_new s',
    store_typed_prefix env s Σ ->
    store_ref_targets_preserved env s s' ->
    (forall se T st,
      store_lookup x s = Some se ->
      sctx_lookup x Σ = Some (T, st) ->
      forall v_root,
        value_update_path (se_val se) path v_new = Some v_root ->
        value_has_type env s v_root T) ->
    store_update_path x path v_new s = Some s' ->
    store_typed_prefix env s' Σ.
Proof.
  intros env s Σ x path v_new s' Htyped Hpres Hroot Hupdate.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  destruct (store_update_path_prefix_split x path v_new entries frame s' Hupdate)
    as [[entries' [Hentries_update Hs']]
       | [Hentries_none [frame' [Hframe_update Hs']]]].
  - subst s'.
    unfold store_typed_prefix.
    exists entries', frame.
    split; [reflexivity |].
    eapply store_typed_update_path_entries.
    + exact Hentries.
    + exact Hpres.
    + intros se T st Hlookup HΣ v_root Hvalue.
      eapply Hroot.
      * apply store_lookup_app_some. exact Hlookup.
      * exact HΣ.
      * exact Hvalue.
    + exact Hentries_update.
  - subst s'.
    unfold store_typed_prefix.
    exists entries, frame'.
    split; [reflexivity |].
    eapply store_typed_store_param_preserved.
    + exact Hentries.
    + exact Hpres.
Qed.

Lemma store_typed_ctx_merge_left_entries :
  forall env s_param entries Σ2 Σ3 Σ4,
    Forall2 (store_entry_typed env s_param) entries Σ2 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    Forall2 (store_entry_typed env s_param) entries Σ4.
Proof.
  intros env s_param entries Σ2 Σ3 Σ4 Htyped.
  revert Σ3 Σ4.
  induction Htyped as [|se ce2 s_tail Σ2_tail Hentry Htail IH];
    intros Σ3 Σ4 Hmerge.
  - destruct Σ3 as [|[[[cx3 cT3] cst3] cm3] Σ3_tail];
      simpl in Hmerge; try discriminate.
    inversion Hmerge; subst; constructor.
  - destruct se as [sx sT sv sst].
    destruct ce2 as [[[cx2 cT2] cst2] cm2].
    destruct Σ3 as [|[[[cx3 cT3] cst3] cm3] Σ3_tail];
      simpl in Hmerge; try discriminate.
    destruct (negb (ident_eqb cx2 cx3)) eqn:Hneq; try discriminate.
    destruct (ctx_merge Σ2_tail Σ3_tail) as [Σtail4 |] eqn:Htail_merge;
      try discriminate.
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Href Hv]]].
    destruct (ty_usage cT2) eqn:Husage.
    + destruct (Bool.eqb (st_consumed cst2) (st_consumed cst3)) eqn:Hconsumed;
        try discriminate.
      simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- assert (Hmerge_ref :
          binding_state_refines cst2
            (MkBindingState (st_consumed cst2)
              (st_moved_paths cst2 ++ st_moved_paths cst3))).
           { apply (binding_state_refines_merge_linear_left cst2 cst3
                (MkBindingState (st_consumed cst2)
                  (st_moved_paths cst2 ++ st_moved_paths cst3))).
             - apply Bool.eqb_true_iff. exact Hconsumed.
             - reflexivity. }
           exact (binding_state_refines_trans sst cst2
             (MkBindingState (st_consumed cst2)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href Hmerge_ref).
        -- exact Hv.
      * eapply IH. exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact (binding_state_refines_trans sst cst2
          (MkBindingState (st_consumed cst2 || st_consumed cst3)
            (st_moved_paths cst2 ++ st_moved_paths cst3))
          Href (binding_state_refines_merge_left cst2 cst3 _ eq_refl)).
        -- exact Hv.
      * eapply IH. exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact (binding_state_refines_trans sst cst2
          (MkBindingState (st_consumed cst2 || st_consumed cst3)
            (st_moved_paths cst2 ++ st_moved_paths cst3))
          Href (binding_state_refines_merge_left cst2 cst3 _ eq_refl)).
        -- exact Hv.
      * eapply IH. exact Htail_merge.
Qed.

Lemma store_typed_ctx_merge_left :
  forall env s Σ2 Σ3 Σ4,
    store_typed env s Σ2 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s Σ4.
Proof.
  intros env s Σ2 Σ3 Σ4 Htyped Hmerge.
  eapply store_typed_ctx_merge_left_entries; eassumption.
Qed.

Lemma store_typed_ctx_merge_right_entries :
  forall env s_param entries Σ2 Σ3 Σ4,
    Forall2 (store_entry_typed env s_param) entries Σ3 ->
    Forall2
      (fun ce2 ce3 =>
        match ce2, ce3 with
        | (_, T2, _, _), (_, T3, _, _) => T2 = T3
        end) Σ2 Σ3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    Forall2 (store_entry_typed env s_param) entries Σ4.
Proof.
  intros env s_param entries Σ2 Σ3 Σ4 Htyped.
  revert Σ2 Σ4.
  induction Htyped as [|se ce3 s_tail Σ3_tail Hentry Htail IH];
    intros Σ2 Σ4 Htypes Hmerge.
  - destruct Σ2 as [|[[[cx2 cT2] cst2] cm2] Σ2_tail];
      simpl in Hmerge; try discriminate.
    inversion Hmerge; subst; constructor.
  - destruct se as [sx sT sv sst].
    destruct ce3 as [[[cx3 cT3] cst3] cm3].
    inversion Htypes as [|ce2_head ce3_head Σ2_tail' Σ3_tail' Htype_head Htypes_tail];
      subst; clear Htypes.
    destruct ce2_head as [[[cx2 cT2] cst2] cm2].
    simpl in Htype_head.
    rename Σ2_tail' into Σ2_tail.
    simpl in Hmerge.
    destruct (negb (ident_eqb cx2 cx3)) eqn:Hneq; try discriminate.
    destruct (ctx_merge Σ2_tail Σ3_tail) as [Σtail4 |] eqn:Htail_merge;
      try discriminate.
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Href Hv]]].
    apply negb_false_iff in Hneq.
    apply ident_eqb_eq in Hneq.
    assert (HT_left : cT2 = sT) by (rewrite Htype_head; symmetry; exact HT).
    destruct (ty_usage cT2) eqn:Husage.
    + destruct (Bool.eqb (st_consumed cst2) (st_consumed cst3)) eqn:Hconsumed;
        try discriminate.
      simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- transitivity cx3; [exact Hname | symmetry; exact Hneq].
        -- symmetry. exact HT_left.
        -- assert (Hmerge_ref :
             binding_state_refines cst3
               (MkBindingState (st_consumed cst2)
                 (st_moved_paths cst2 ++ st_moved_paths cst3))).
           { apply (binding_state_refines_merge_linear_right cst2 cst3
                (MkBindingState (st_consumed cst2)
                  (st_moved_paths cst2 ++ st_moved_paths cst3))).
             - apply Bool.eqb_true_iff. exact Hconsumed.
             - reflexivity. }
           exact (binding_state_refines_trans sst cst3
             (MkBindingState (st_consumed cst2)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href Hmerge_ref).
        -- exact Hv.
      * eapply IH; eassumption.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- transitivity cx3; [exact Hname | symmetry; exact Hneq].
        -- symmetry. exact HT_left.
        -- exact (binding_state_refines_trans sst cst3
             (MkBindingState (st_consumed cst2 || st_consumed cst3)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href (binding_state_refines_merge_right cst2 cst3 _ eq_refl)).
        -- exact Hv.
      * eapply IH; eassumption.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- transitivity cx3; [exact Hname | symmetry; exact Hneq].
        -- symmetry. exact HT_left.
        -- exact (binding_state_refines_trans sst cst3
             (MkBindingState (st_consumed cst2 || st_consumed cst3)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href (binding_state_refines_merge_right cst2 cst3 _ eq_refl)).
        -- exact Hv.
      * eapply IH; eassumption.
Qed.

Lemma store_typed_ctx_merge_right :
  forall env s Σ2 Σ3 Σ4,
    store_typed env s Σ3 ->
    Forall2
      (fun ce2 ce3 =>
        match ce2, ce3 with
        | (_, T2, _, _), (_, T3, _, _) => T2 = T3
        end) Σ2 Σ3 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s Σ4.
Proof.
  intros env s Σ2 Σ3 Σ4 Htyped Htypes Hmerge.
  eapply store_typed_ctx_merge_right_entries; eassumption.
Qed.

Lemma type_lookup_path_compatible :
  forall env Ω T_actual T_expected path T_path,
    ty_compatible Ω T_actual T_expected ->
    type_lookup_path env T_expected path = Some T_path ->
    exists T_actual_path,
      type_lookup_path env T_actual path = Some T_actual_path /\
      ty_compatible Ω T_actual_path T_path.
Proof.
  intros env Ω T_actual T_expected path T_path Hcompat.
  revert path T_path.
  induction Hcompat; intros path T_path Hlookup.
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua ca). split.
      * reflexivity.
      * apply TC_Core; [exact H | exact H0].
    + subst ce.
      exists T_path. split.
      * exact Hlookup.
      * destruct T_path as [u c].
        apply TC_Core; [apply US_refl | reflexivity].
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua (TRef la RShared Ta)). split.
      * reflexivity.
      * eapply TC_Ref_Shared; eassumption.
    + simpl in Hlookup. discriminate.
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua (TRef la RUnique Ta)). split.
      * reflexivity.
      * eapply TC_Ref_Unique; eassumption.
    + simpl in Hlookup. discriminate.
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua (TFn params_a ret_a)). split.
      * reflexivity.
      * eapply TC_Fn; eassumption.
    + simpl in Hlookup. discriminate.
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua (TForall n Ω_forall body_a)). split.
      * reflexivity.
      * eapply TC_Forall; eassumption.
    + simpl in Hlookup. discriminate.
  - destruct path as [|seg rest].
    + simpl in Hlookup. inversion Hlookup; subst T_path.
      exists (MkTy ua ca). split.
      * reflexivity.
      * eapply TC_Forall_GeneralizeUnused; eassumption.
    + simpl in Hlookup. discriminate.
Qed.

Lemma type_lookup_path_lifetime_equiv :
  forall env T_actual T_expected path T_path,
    ty_lifetime_equiv T_actual T_expected ->
    type_lookup_path env T_expected path = Some T_path ->
    exists T_actual_path,
      type_lookup_path env T_actual path = Some T_actual_path /\
      ty_lifetime_equiv T_actual_path T_path.
Proof.
  intros env T_actual T_expected path.
  revert T_actual T_expected.
  induction path as [|seg rest IH];
    intros T_actual T_expected T_path Heq Hlookup.
  - simpl in Hlookup. inversion Hlookup; subst T_path.
    exists T_actual. split; [reflexivity | exact Heq].
  - inversion Heq; subst; simpl in Hlookup; try discriminate.
    simpl.
    destruct (lookup_struct name env) as [sdef |] eqn:Hstruct;
      try discriminate.
    destruct (lookup_field seg (struct_fields sdef)) as [fdef |] eqn:Hfield;
      try discriminate.
    apply IH with
      (T_expected := instantiate_struct_field_ty lts_expected args_expected fdef).
    + apply instantiate_struct_field_ty_lifetime_equiv.
      exact H.
    + exact Hlookup.
Qed.

Lemma type_lookup_path_app :
  forall env T p q,
    type_lookup_path env T (p ++ q) =
    match type_lookup_path env T p with
    | Some T' => type_lookup_path env T' q
    | None => None
    end.
Proof.
  intros env T p.
  revert T.
  induction p as [|seg rest IH]; intros T q.
  - reflexivity.
  - simpl.
    destruct (ty_core T); try reflexivity.
    destruct (lookup_struct s env) as [sdef |]; try reflexivity.
    destruct (lookup_field seg (struct_fields sdef)) as [fdef |]; try reflexivity.
    apply IH.
Qed.

Lemma runtime_path_exists_typing :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall lookup_path T_path,
      type_lookup_path env T lookup_path = Some T_path ->
      exists v_path,
        value_lookup_path v lookup_path = Some v_path /\
        value_has_type env s v_path T_path) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall name fdef rest T_path,
      lookup_field name defs = Some fdef ->
      type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
        Some T_path ->
      exists field_value v_path,
        lookup_value_field name fields = Some field_value /\
        value_lookup_path field_value rest = Some v_path /\
        value_has_type env s v_path T_path).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; subst; simpl in *; try discriminate.
  - destruct lookup_path; simpl in *; try discriminate.
    inversion H; subst. exists VUnit. split; [reflexivity | constructor].
  - destruct lookup_path; simpl in *; try discriminate.
    inversion H; subst. exists (VInt i). split; [reflexivity | constructor].
  - destruct lookup_path; simpl in *; try discriminate.
    inversion H; subst. exists (VFloat f). split; [reflexivity | constructor].
  - destruct lookup_path; simpl in *; try discriminate.
    inversion H; subst. exists (VBool b). split; [reflexivity | constructor].
  - destruct lookup_path as [|seg rest].
    + simpl in *.
      inversion H0; subst.
      exists (VStruct name fields). split; [reflexivity | econstructor; eassumption].
    + simpl in *.
      rewrite lookup_value_field_local.
      pose proof (runtime_lookup_struct_success env name sdef e)
        as Hstruct_name.
      rewrite Hstruct_name in H0.
      rewrite e in H0.
      destruct (lookup_field seg (struct_fields sdef)) as [fdef |] eqn:Hfield;
        try discriminate.
      destruct (H seg fdef rest T_path Hfield H0)
        as [field_value [v_path [Hlookup [Hvalue Hv]]]].
      exists v_path. split.
      * rewrite Hlookup. exact Hvalue.
      * exact Hv.
  - destruct lookup_path as [|seg rest].
    + match goal with
      | Hquery : type_lookup_path env (MkTy _ (TRef _ _ _)) [] = Some _ |- _ =>
          simpl in Hquery; inversion Hquery; clear Hquery; subst
      end.
      simpl.
      exists (VRef x path). split; [reflexivity | econstructor; eassumption].
    + match goal with
      | Hquery : type_lookup_path env (MkTy _ (TRef _ _ _)) (seg :: rest) = Some _ |- _ =>
          simpl in Hquery; discriminate Hquery
      end.
  - destruct lookup_path as [|seg rest].
    + simpl in *.
      match goal with
      | |- exists _, Some (VClosure ?closure_name []) = Some _ /\ _ =>
          exists (VClosure closure_name [])
      end.
      repeat match goal with
      | Hsome : Some _ = Some _ |- _ => inversion Hsome; clear Hsome; subst
      end.
      split; [reflexivity | eapply VHT_ClosureEmpty; eassumption].
    + unfold fn_value_ty in *.
      destruct (fn_lifetimes fdef); simpl in *; discriminate.
  - destruct lookup_path as [|seg rest].
    + simpl in *.
      match goal with
      | |- exists _, Some (VClosure ?closure_name []) = Some _ /\ _ =>
          exists (VClosure closure_name [])
      end.
      repeat match goal with
      | Hsome : Some _ = Some _ |- _ => inversion Hsome; clear Hsome; subst
      end.
      split; [reflexivity | eapply VHT_ClosureIn; [eassumption | reflexivity]].
    + unfold fn_value_ty in *.
      destruct (fn_lifetimes fdef); simpl in *; discriminate.
  - match goal with
    | Hcompat : ty_compatible Ω T_actual T_expected,
      Htype : type_lookup_path env T_expected lookup_path = Some T_path |- _ =>
        destruct (type_lookup_path_compatible env Ω T_actual T_expected
                  lookup_path T_path Hcompat Htype)
          as [T_actual_path [Hactual_path Hcompat_path]]
    end.
    destruct (H lookup_path T_actual_path Hactual_path)
      as [v_path [Hvalue Hv]].
    exists v_path. split.
    + exact Hvalue.
    + eapply VHT_Compatible; eassumption.
  - match goal with
    | Heq : ty_lifetime_equiv T_actual T_expected,
      Htype : type_lookup_path env T_expected lookup_path = Some T_path |- _ =>
        destruct (type_lookup_path_lifetime_equiv env T_actual T_expected
                  lookup_path T_path Heq Htype)
          as [T_actual_path [Hactual_path Heq_path]]
    end.
    destruct (H lookup_path T_actual_path Hactual_path)
      as [v_path [Hvalue Hv]].
    exists v_path. split.
    + exact Hvalue.
    + eapply VHT_LifetimeEquiv; eassumption.
  - destruct (String.eqb name0 (field_name f)) eqn:Hfield_name.
    + inversion H1; subst fdef.
      destruct (H rest T_path H2) as [v_path [Hvalue Hv]].
      exists v, v_path.
      split; [reflexivity |].
      split; assumption.
    + destruct (H0 name0 fdef rest T_path H1 H2)
        as [field_value [v_path [Hlookup [Hvalue Hv]]]].
      exists field_value, v_path.
      split; [exact Hlookup |].
      split; assumption.
Qed.

Lemma value_has_type_path_exists :
  forall env s v T path T_path,
    value_has_type env s v T ->
    type_lookup_path env T path = Some T_path ->
    exists v_path,
      value_lookup_path v path = Some v_path /\
      value_has_type env s v_path T_path.
Proof.
  intros env s v T path T_path Htyped Htype.
  exact (proj1 (runtime_path_exists_typing env s)
    v T Htyped path T_path Htype).
Qed.

Lemma struct_fields_have_type_path_exists :
  forall env s lts args fields defs name fdef rest T_path,
    struct_fields_have_type env s lts args fields defs ->
    lookup_field name defs = Some fdef ->
    type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
      Some T_path ->
    exists field_value v_path,
      lookup_value_field name fields = Some field_value /\
      value_lookup_path field_value rest = Some v_path /\
      value_has_type env s v_path T_path.
Proof.
  intros env s lts args fields defs name fdef rest T_path Htyped Hfield Htype.
  exact (proj2 (runtime_path_exists_typing env s)
    lts args fields defs Htyped name fdef rest T_path Hfield Htype).
Qed.

Lemma runtime_path_update_typing :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall upd_path v_new T_path v',
      type_lookup_path env T upd_path = Some T_path ->
      value_has_type env s v_new T_path ->
      value_update_path v upd_path v_new = Some v' ->
      value_has_type env s v' T) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall name rest v_new fields' fdef T_path,
      lookup_field name defs = Some fdef ->
      type_lookup_path env (instantiate_struct_field_ty lts args fdef) rest =
        Some T_path ->
      value_has_type env s v_new T_path ->
      update_value_field_path name rest v_new fields = Some fields' ->
      struct_fields_have_type env s lts args fields' defs).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; subst; simpl in *; try discriminate.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path as [|seg rest].
    + simpl in *.
      repeat match goal with
      | Hsome : Some _ = Some _ |- _ => inversion Hsome; clear Hsome; subst
      end.
      match goal with
      | Htyped : value_has_type env s v' (instantiate_struct_instance_ty sdef lts args) |- _ =>
          exact Htyped
      end.
    + simpl in *.
      rewrite update_value_field_path_local in *.
      pose proof (runtime_lookup_struct_success env name sdef e)
        as Hstruct_name.
      rewrite Hstruct_name in H0.
      simpl in H0.
      rewrite e in H0.
      destruct (lookup_field seg (struct_fields sdef)) as [fdef |] eqn:Hfield;
        try discriminate.
      destruct (update_value_field_path seg rest v_new fields)
        as [fields' |] eqn:Hupdate_fields; try discriminate.
      inversion H2; subst v'.
      econstructor.
      * exact e.
      * eapply H; eassumption.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path; simpl in *; try discriminate.
    inversion H; inversion H1; subst. exact H0.
  - destruct upd_path as [|seg rest].
    + simpl in *.
      destruct v; simpl in *;
      repeat match goal with
      | Hsome : Some _ = Some _ |- _ => inversion Hsome; clear Hsome; subst
      end; eassumption.
    + match goal with
      | Hcompat : ty_compatible _ _ _ |- _ => inversion Hcompat; subst; clear Hcompat
      end; simpl in *; try discriminate.
      apply (VHT_Compatible env s Ω v' (MkTy ua ce) (MkTy ue ce)).
      * apply (H (seg :: rest) v_new T_path v').
        -- simpl. eassumption.
        -- eassumption.
        -- eassumption.
      * apply TC_Core; [assumption | reflexivity].
  - match goal with
    | Heq : ty_lifetime_equiv T_actual T_expected,
      Htype : type_lookup_path env T_expected upd_path = Some T_path |- _ =>
        destruct (type_lookup_path_lifetime_equiv env T_actual T_expected
                  upd_path T_path Heq Htype)
          as [T_actual_path [Hactual_path Heq_path]]
    end.
    eapply VHT_LifetimeEquiv.
    + eapply H.
      * exact Hactual_path.
      * eapply VHT_LifetimeEquiv.
        -- eassumption.
        -- apply ty_lifetime_equiv_sym. exact Heq_path.
      * eassumption.
    + eassumption.
  - simpl in *.
    destruct (String.eqb name0 (field_name f)) eqn:Hname_field.
    + match goal with
      | Hfield : Some f = Some fdef |- _ => inversion Hfield; subst fdef
      end.
      destruct (value_update_path v rest v_new) as [v' |] eqn:Hupdate_value;
        try discriminate.
      match goal with
      | Hupdate : Some ((field_name f, v') :: fields) = Some fields' |- _ =>
          inversion Hupdate; subst fields'
      end.
      constructor.
      * reflexivity.
      * eapply H; eassumption.
      * exact s0.
    + destruct (update_value_field_path name0 rest v_new fields)
        as [fields_tail' |] eqn:Hupdate_tail; try discriminate.
      match goal with
      | Hupdate : Some ((field_name f, v) :: fields_tail') = Some fields' |- _ =>
          inversion Hupdate; subst fields'
      end.
      constructor.
      * reflexivity.
      * exact v0.
      * eapply H0.
        -- eassumption.
        -- eassumption.
        -- eassumption.
        -- exact Hupdate_tail.
Qed.

Lemma value_update_path_has_type :
  forall env s v T path v_new T_path v',
    value_has_type env s v T ->
    type_lookup_path env T path = Some T_path ->
    value_has_type env s v_new T_path ->
    value_update_path v path v_new = Some v' ->
    value_has_type env s v' T.
Proof.
  intros env s v T path v_new T_path v' Htyped Hpath Hvnew Hupdate.
  exact (proj1 (runtime_path_update_typing env s)
    v T Htyped path v_new T_path v' Hpath Hvnew Hupdate).
Qed.

Lemma store_update_val_ref_targets_preserved_entries :
  forall env s_param entries Σ x v T st entries',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s_param v T ->
    store_update_val x v entries = Some entries' ->
    store_ref_targets_preserved env entries entries'.
Proof.
  unfold store_ref_targets_preserved.
  intros env s_param entries Σ x v T st entries' Htyped.
  revert x v T st entries'.
  induction Htyped as [|se ce entries_tail Σ_tail Hentry Htail IH];
    intros x v T st entries' HΣ Hv Hupdate y path se_old v_old T_path
      Hlookup Hvalue Htype.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Href Hsv]]].
    simpl in HΣ, Hupdate, Hlookup.
    destruct (ident_eqb x sx) eqn:Hsx.
    + inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy.
      * inversion Hlookup; subst se_old.
        apply ident_eqb_eq in Hsx.
        subst x.
        rewrite <- Hname in HΣ.
        rewrite ident_eqb_refl in HΣ.
        inversion HΣ; subst T st.
        simpl in Htype.
        assert (Htype_cT : type_lookup_path env cT path = Some T_path).
        { rewrite <- HT. exact Htype. }
        destruct (value_has_type_path_exists env s_param v cT path T_path
                  Hv Htype_cT)
          as [v_path [Hvalue_path Hv_path]].
        exists (MkStoreEntry sx sT v sst), v_path.
        split; [simpl; rewrite Hy; reflexivity |].
        split; [simpl; exact Hvalue_path |].
        simpl. rewrite HT. exact Htype_cT.
      * exists se_old, v_old.
        repeat split; simpl; try (rewrite Hy; exact Hlookup); assumption.
    + destruct (store_update_val x v entries_tail) as [tail' |] eqn:Htail_update;
        try discriminate.
      inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy.
      * inversion Hlookup; subst se_old.
        exists (MkStoreEntry sx sT sv sst), v_old.
        repeat split; simpl; try (rewrite Hy; reflexivity); assumption.
      * assert (HΣ_tail : sctx_lookup x Σ_tail = Some (T, st)).
        { destruct (ident_eqb x cx) eqn:Hcx.
          - apply ident_eqb_eq in Hcx.
            apply ident_eqb_neq in Hsx.
            exfalso. apply Hsx.
            rewrite Hname. exact Hcx.
          - exact HΣ. }
        destruct (IH x v T st tail' HΣ_tail Hv Htail_update
                    y path se_old v_old T_path Hlookup Hvalue Htype)
          as [se' [v' [Hlookup' [Hvalue' Htype']]]].
        exists se', v'.
        repeat split; simpl; try (rewrite Hy; exact Hlookup'); assumption.
Qed.

Lemma store_update_val_ref_targets_preserved :
  forall env s Σ x v T st s',
    store_typed env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s v T ->
    store_update_val x v s = Some s' ->
    store_ref_targets_preserved env s s'.
Proof.
  intros env s Σ x v T st s' Htyped HΣ Hv Hupdate.
  eapply store_update_val_ref_targets_preserved_entries; eassumption.
Qed.

Lemma store_update_path_ref_targets_preserved_entries :
  forall env s_param entries Σ x path_update v_new T_update entries',
    Forall2 (store_entry_typed env s_param) entries Σ ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path_update = Some T_update) ->
    value_has_type env s_param v_new T_update ->
    store_update_path x path_update v_new entries = Some entries' ->
    store_ref_targets_preserved env entries entries'.
Proof.
  unfold store_ref_targets_preserved.
  intros env s_param entries Σ x path_update v_new T_update entries'
    Htyped.
  revert x path_update v_new T_update entries'.
  induction Htyped as [|se ce entries_tail Σ_tail Hentry Htail IH];
    intros x path_update v_new T_update entries' Htarget Hvnew Hupdate
      y path se_old v_old T_path Hlookup Hvalue Htype.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Href Hsv]]].
    simpl in Hupdate, Hlookup.
    destruct Htarget as [T_root [st [HΣ Htype_update]]].
    simpl in HΣ.
    destruct (ident_eqb x sx) eqn:Hsx.
    + destruct (value_update_path sv path_update v_new) as [v_root |]
        eqn:Hvalue_update; try discriminate.
      inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy.
      * inversion Hlookup; subst se_old.
        apply ident_eqb_eq in Hsx.
        subst x.
        rewrite Hname in HΣ.
        rewrite ident_eqb_refl in HΣ.
        inversion HΣ; subst T_root st.
        assert (Htype_cT : type_lookup_path env cT path = Some T_path).
        { rewrite <- HT. exact Htype. }
        assert (Hsv_cT : value_has_type env s_param sv cT).
        { rewrite <- HT. exact Hsv. }
        pose proof (value_update_path_has_type env s_param sv cT
          path_update v_new T_update v_root
          Hsv_cT Htype_update Hvnew Hvalue_update) as Hvroot.
        destruct (value_has_type_path_exists env s_param v_root cT
                  path T_path Hvroot Htype_cT)
          as [v_path [Hvalue_path Hv_path]].
        exists (MkStoreEntry sx sT v_root sst), v_path.
        split; [simpl; rewrite Hy; reflexivity |].
        split; [simpl; exact Hvalue_path |].
        simpl. rewrite HT. exact Htype_cT.
      * exists se_old, v_old.
        repeat split; simpl; try (rewrite Hy; exact Hlookup); assumption.
    + destruct (store_update_path x path_update v_new entries_tail)
        as [tail' |] eqn:Htail_update; try discriminate.
      inversion Hupdate; subst entries'.
      destruct (ident_eqb y sx) eqn:Hy.
      * inversion Hlookup; subst se_old.
        exists (MkStoreEntry sx sT sv sst), v_old.
        repeat split; simpl; try (rewrite Hy; reflexivity); assumption.
      * assert (Htarget_tail :
          exists T_root st,
            sctx_lookup x Σ_tail = Some (T_root, st) /\
            type_lookup_path env T_root path_update = Some T_update).
        { exists T_root, st.
          split; [|exact Htype_update].
          destruct (ident_eqb x cx) eqn:Hcx.
          - apply ident_eqb_eq in Hcx.
            apply ident_eqb_neq in Hsx.
            exfalso. apply Hsx.
            rewrite Hname. exact Hcx.
          - exact HΣ. }
        destruct (IH x path_update v_new T_update tail'
                    Htarget_tail Hvnew Htail_update
                    y path se_old v_old T_path Hlookup Hvalue Htype)
          as [se' [v' [Hlookup' [Hvalue' Htype']]]].
        exists se', v'.
        repeat split; simpl; try (rewrite Hy; exact Hlookup'); assumption.
Qed.

Lemma store_update_path_ref_targets_preserved :
  forall env s Σ x path_update v_new T_update s',
    store_typed env s Σ ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path_update = Some T_update) ->
    value_has_type env s v_new T_update ->
    store_update_path x path_update v_new s = Some s' ->
    store_ref_targets_preserved env s s'.
Proof.
  intros env s Σ x path_update v_new T_update s' Htyped Htarget Hvnew Hupdate.
  eapply store_update_path_ref_targets_preserved_entries; eassumption.
Qed.

Lemma store_update_val_ref_targets_preserved_prefix :
  forall env s Σ x v T st s',
    store_typed_prefix env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s v T ->
    store_update_val x v s = Some s' ->
    store_ref_targets_preserved env s s'.
Proof.
  intros env s Σ x v T st s' Htyped HΣ Hv Hupdate.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  destruct (store_update_val_prefix_hit env (entries ++ frame)
    entries Σ frame x v T st s' Hentries HΣ Hupdate)
    as [entries' [Hentries_update Hs']].
  subst s'.
  pose proof (store_update_val_ref_targets_preserved_entries
    env (entries ++ frame) entries Σ x v T st entries'
    Hentries HΣ Hv Hentries_update) as Hpres_entries.
  unfold store_ref_targets_preserved in *.
  intros y path se_old v_old T_path Hlookup Hvalue Htype.
  destruct (store_lookup y entries) as [se_entries |] eqn:Hentries_lookup.
  - assert (se_entries = se_old) as ->.
    { pose proof (store_lookup_app_some y entries frame se_entries
        Hentries_lookup) as Happ.
      rewrite Hlookup in Happ.
      inversion Happ. reflexivity. }
    destruct (Hpres_entries y path se_old v_old T_path
      Hentries_lookup Hvalue Htype)
      as [se' [v' [Hlookup' [Hvalue' Htype']]]].
    exists se', v'.
    repeat split; try assumption.
    apply store_lookup_app_some. exact Hlookup'.
  - pose proof (store_lookup_app_none y entries frame Hentries_lookup)
      as Hsource_app.
    rewrite Hsource_app in Hlookup.
    assert (Hentries'_lookup : store_lookup y entries' = None).
    { eapply store_update_val_lookup_none; eassumption. }
    exists se_old, v_old.
    repeat split; try assumption.
    rewrite (store_lookup_app_none y entries' frame Hentries'_lookup).
    exact Hlookup.
Qed.

Lemma store_update_path_ref_targets_preserved_prefix :
  forall env s Σ x path_update v_new T_update s',
    store_typed_prefix env s Σ ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path_update = Some T_update) ->
    value_has_type env s v_new T_update ->
    store_update_path x path_update v_new s = Some s' ->
    store_ref_targets_preserved env s s'.
Proof.
  intros env s Σ x path_update v_new T_update s'
    Htyped Htarget Hvnew Hupdate.
  unfold store_typed_prefix in Htyped.
  destruct Htyped as [entries [frame [Hs Hentries]]].
  subst s.
  destruct Htarget as [T_root [st [HΣ Htype_update]]].
  assert (Htarget_entries :
    exists T_root0 st0,
      sctx_lookup x Σ = Some (T_root0, st0) /\
      type_lookup_path env T_root0 path_update = Some T_update).
  { exists T_root, st. split; assumption. }
  destruct (store_update_path_prefix_split x path_update v_new entries frame
    s' Hupdate)
    as [[entries' [Hentries_update Hs']]
       | [Hentries_none [frame' [Hframe_update Hs']]]].
  - subst s'.
    pose proof (store_update_path_ref_targets_preserved_entries
      env (entries ++ frame) entries Σ x path_update v_new T_update entries'
      Hentries Htarget_entries Hvnew Hentries_update) as Hpres_entries.
    unfold store_ref_targets_preserved in *.
    intros y path se_old v_old T_path Hlookup Hvalue Htype.
    destruct (store_lookup y entries) as [se_entries |] eqn:Hentries_lookup.
    + assert (se_entries = se_old) as ->.
      { pose proof (store_lookup_app_some y entries frame se_entries
          Hentries_lookup) as Happ.
        rewrite Hlookup in Happ.
        inversion Happ. reflexivity. }
      destruct (Hpres_entries y path se_old v_old T_path
        Hentries_lookup Hvalue Htype)
        as [se' [v' [Hlookup' [Hvalue' Htype']]]].
      exists se', v'.
      repeat split; try assumption.
      apply store_lookup_app_some. exact Hlookup'.
    + pose proof (store_lookup_app_none y entries frame Hentries_lookup)
        as Hsource_app.
      rewrite Hsource_app in Hlookup.
      assert (Hentries'_lookup : store_lookup y entries' = None).
      { eapply store_update_path_lookup_none; eassumption. }
      exists se_old, v_old.
      repeat split; try assumption.
      rewrite (store_lookup_app_none y entries' frame Hentries'_lookup).
      exact Hlookup.
  - destruct (store_typed_lookup_sctx_entries
      env (entries ++ frame) entries Σ x T_root st Hentries HΣ)
      as [se [Hstore [Hname [HT [Href Hse]]]]].
    destruct (value_has_type_path_exists env (entries ++ frame)
      (se_val se) T_root path_update T_update Hse Htype_update)
      as [v_old [Hvalue_old Hv_old]].
    destruct (value_lookup_path_update_exists
      (se_val se) path_update v_old v_new Hvalue_old)
      as [v_root Hvalue_update].
    destruct (store_update_path_exists_from_lookup x path_update v_new
      entries se v_root Hstore Hvalue_update)
      as [entries' Hentries_update].
    rewrite Hentries_update in Hentries_none. discriminate.
Qed.

Lemma store_typed_update_path_typed :
  forall env s Σ x path v_new T_path s',
    store_typed env s Σ ->
    store_ref_targets_preserved env s s' ->
    (exists T_root st,
      sctx_lookup x Σ = Some (T_root, st) /\
      type_lookup_path env T_root path = Some T_path) ->
    value_has_type env s v_new T_path ->
    store_update_path x path v_new s = Some s' ->
    store_typed env s' Σ.
Proof.
  intros env s Σ x path v_new T_path s' Hstore Hpres Htarget Hvnew Hupdate.
  destruct Htarget as [T_root [st [HΣ Htype_path]]].
  eapply store_typed_update_path.
  - exact Hstore.
  - exact Hpres.
  - intros se T st0 Hlookup HΣ0 v_root Hvalue_update.
    rewrite HΣ in HΣ0.
    inversion HΣ0; subst T st0.
    destruct (store_typed_lookup env s Σ x se Hstore Hlookup)
      as [Tse [stse [m [HΣlookup [Hname [HT [Href Hvroot]]]]]]].
    rewrite HΣ in HΣlookup.
    inversion HΣlookup; subst Tse stse.
    eapply (value_update_path_has_type env s (se_val se) (se_ty se)
      path v_new T_path v_root).
    + exact Hvroot.
    + match goal with
      | Hty : T_root = se_ty se |- _ =>
          rewrite <- Hty; exact Htype_path
      | Hty : se_ty se = T_root |- _ =>
          rewrite Hty; exact Htype_path
      end.
    + exact Hvnew.
    + exact Hvalue_update.
  - exact Hupdate.
Qed.

(* ------------------------------------------------------------------ *)
(* Runtime reference well-formedness                                    *)
(* ------------------------------------------------------------------ *)

Inductive runtime_refs_wf (env : global_env) (s : store) : value -> Prop :=
  | RRW_Unit :
      runtime_refs_wf env s VUnit
  | RRW_Int : forall i,
      runtime_refs_wf env s (VInt i)
  | RRW_Float : forall f,
      runtime_refs_wf env s (VFloat f)
  | RRW_Bool : forall b,
      runtime_refs_wf env s (VBool b)
  | RRW_Struct : forall name fields,
      Forall (fun fv => runtime_refs_wf env s (snd fv)) fields ->
      runtime_refs_wf env s (VStruct name fields)
  | RRW_Ref : forall x path se T v,
      store_lookup x s = Some se ->
      type_lookup_path env (se_ty se) path = Some T ->
      value_lookup_path (se_val se) path = Some v ->
      runtime_refs_wf env s (VRef x path)
  | RRW_Closure : forall fname captured,
      Forall (store_entry_refs_wf env captured) captured ->
      runtime_refs_wf env s (VClosure fname captured)
with store_entry_refs_wf (env : global_env) (s : store) : store_entry -> Prop :=
  | SERW_Entry : forall x T v st,
      runtime_refs_wf env s v ->
      store_entry_refs_wf env s (MkStoreEntry x T v st).

Definition store_refs_wf (env : global_env) (s : store) : Prop :=
  Forall (store_entry_refs_wf env s) s.
