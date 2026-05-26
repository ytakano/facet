From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Stdlib Require Import List Bool ZArith String Program.Equality Lia.
Import ListNotations.

Inductive value_roots_within : root_set -> value -> Prop :=
  | VRW_Unit :
      forall roots,
      value_roots_within roots VUnit
  | VRW_Int : forall roots i,
      value_roots_within roots (VInt i)
  | VRW_Float : forall roots f,
      value_roots_within roots (VFloat f)
  | VRW_Bool : forall roots b,
      value_roots_within roots (VBool b)
  | VRW_Struct : forall roots name fields,
      value_fields_roots_within roots fields ->
      value_roots_within roots (VStruct name fields)
  | VRW_Enum : forall roots enum_name variant_name lts args values,
      Forall (value_roots_within roots) values ->
      (forall root,
        roots_exclude root roots ->
        Forall (value_refs_exclude_root root) values) ->
      value_roots_within roots (VEnum enum_name variant_name lts args values)
  | VRW_Ref : forall roots x path,
      In (RStore x) roots ->
      value_roots_within roots (VRef x path)
  | VRW_ClosureEmpty : forall roots fname,
      value_roots_within roots (VClosure fname [])
  | VRW_ClosureCaptured : forall roots fname captured,
      (forall root,
        roots_exclude root roots ->
        store_refs_exclude_root root captured) ->
      value_roots_within roots (VClosure fname captured)
with store_entry_roots_within : root_env -> store_entry -> Prop :=
  | SERW_Entry : forall R sx sT sv sst roots,
      root_env_lookup sx R = Some roots ->
      value_roots_within roots sv ->
      store_entry_roots_within R (MkStoreEntry sx sT sv sst)
with store_roots_within : root_env -> store -> Prop :=
  | SRW_Nil :
      forall R,
      store_roots_within R []
  | SRW_Cons : forall R se rest,
      store_entry_roots_within R se ->
      store_roots_within R rest ->
      store_roots_within R (se :: rest)
with value_fields_roots_within
    : root_set -> list (string * value) -> Prop :=
  | VFRW_Nil :
      forall roots,
      value_fields_roots_within roots []
  | VFRW_Cons : forall roots name v rest,
      value_roots_within roots v ->
      value_fields_roots_within roots rest ->
      value_fields_roots_within roots ((name, v) :: rest).

Scheme value_roots_within_ind' := Induction for value_roots_within Sort Prop
with store_entry_roots_within_ind' := Induction for store_entry_roots_within Sort Prop
with store_roots_within_ind' := Induction for store_roots_within Sort Prop
with value_fields_roots_within_ind' := Induction for value_fields_roots_within Sort Prop.
Combined Scheme value_roots_within_mutind
  from value_roots_within_ind', store_entry_roots_within_ind',
       store_roots_within_ind', value_fields_roots_within_ind'.

Definition root_env_store_roots_named (R : root_env) (s : store) : Prop :=
  forall x roots z,
    root_env_lookup x R = Some roots ->
    In (RStore z) roots ->
    In z (store_names s).

Definition root_set_store_roots_named (roots : root_set) (s : store) : Prop :=
  forall z,
    In (RStore z) roots ->
    In z (store_names s).

Definition root_env_ctx_roots_named (R : root_env) (Σ : sctx) : Prop :=
  forall x roots z,
    root_env_lookup x R = Some roots ->
    In (RStore z) roots ->
    In z (ctx_names Σ).

Definition root_set_ctx_roots_named (roots : root_set) (Σ : sctx) : Prop :=
  forall z,
    In (RStore z) roots ->
    In z (ctx_names Σ).

Definition root_set_stores_subset (roots roots_bound : root_set) : Prop :=
  forall z,
    In (RStore z) roots ->
    In (RStore z) roots_bound.

Definition root_set_no_store (roots : root_set) : Prop :=
  forall z,
    ~ In (RStore z) roots.

Definition root_env_ctx_keys_named (R : root_env) (Σ : sctx) : Prop :=
  root_env_keys_named R (ctx_names Σ).

Definition root_env_store_keys_named (R : root_env) (s : store) : Prop :=
  root_env_keys_named R (store_names s).

Inductive runtime_rootless_ty (env : global_env) : Ty -> Prop :=
  | RRT_Unit : forall u,
      runtime_rootless_ty env (MkTy u TUnits)
  | RRT_Int : forall u,
      runtime_rootless_ty env (MkTy u TIntegers)
  | RRT_Float : forall u,
      runtime_rootless_ty env (MkTy u TFloats)
  | RRT_Bool : forall u,
      runtime_rootless_ty env (MkTy u TBooleans)
  | RRT_Struct : forall u name lts args sdef,
      lookup_struct name env = Some sdef ->
      runtime_rootless_fields env lts args (struct_fields sdef) ->
      runtime_rootless_ty env (MkTy u (TStruct name lts args))
  | RRT_Enum : forall u name lts args edef,
      lookup_enum name env = Some edef ->
      runtime_rootless_enum_variants env lts args (enum_variants edef) ->
      runtime_rootless_ty env (MkTy u (TEnum name lts args))
  | RRT_Fn : forall u params ret,
      runtime_rootless_ty env (MkTy u (TFn params ret))
  | RRT_Forall : forall u n Ω body,
      runtime_rootless_ty env body ->
      runtime_rootless_ty env (MkTy u (TForall n Ω body))
  | RRT_TypeForall : forall u n bounds body,
      runtime_rootless_ty env body ->
      runtime_rootless_ty env (MkTy u (TTypeForall n bounds body))
with runtime_rootless_fields
    (env : global_env) : list lifetime -> list Ty -> list field_def -> Prop :=
  | RRF_Nil : forall lts args,
      runtime_rootless_fields env lts args []
  | RRF_Cons : forall lts args f fs,
      runtime_rootless_ty env (instantiate_struct_field_ty lts args f) ->
      runtime_rootless_fields env lts args fs ->
      runtime_rootless_fields env lts args (f :: fs)
with runtime_rootless_enum_variants
    (env : global_env) : list lifetime -> list Ty -> list enum_variant_def -> Prop :=
  | RREV_Nil : forall lts args,
      runtime_rootless_enum_variants env lts args []
  | RREV_Cons : forall lts args v vs,
      runtime_rootless_enum_fields env lts args (enum_variant_fields v) ->
      runtime_rootless_enum_variants env lts args vs ->
      runtime_rootless_enum_variants env lts args (v :: vs)
with runtime_rootless_enum_fields
    (env : global_env) : list lifetime -> list Ty -> list Ty -> Prop :=
  | RREF_Nil : forall lts args,
      runtime_rootless_enum_fields env lts args []
  | RREF_Cons : forall lts args T Ts,
      runtime_rootless_ty env (instantiate_enum_variant_field_ty lts args T) ->
      runtime_rootless_enum_fields env lts args Ts ->
      runtime_rootless_enum_fields env lts args (T :: Ts).

Scheme runtime_rootless_ty_ind' := Induction for runtime_rootless_ty Sort Prop
with runtime_rootless_fields_ind' := Induction for runtime_rootless_fields Sort Prop
with runtime_rootless_enum_variants_ind' :=
  Induction for runtime_rootless_enum_variants Sort Prop
with runtime_rootless_enum_fields_ind' :=
  Induction for runtime_rootless_enum_fields Sort Prop.
Combined Scheme runtime_rootless_ind
  from runtime_rootless_ty_ind', runtime_rootless_fields_ind',
       runtime_rootless_enum_variants_ind',
       runtime_rootless_enum_fields_ind'.

Lemma runtime_rootless_ty_change_usage :
  forall env T u,
    runtime_rootless_ty env T ->
    runtime_rootless_ty env (MkTy u (ty_core T)).
Proof.
  intros env T u Hrootless.
  destruct T as [u0 core].
  induction Hrootless; simpl; eauto using runtime_rootless_ty.
Qed.

Lemma ty_compatible_runtime_rootless_actual :
  forall env Ω T_actual T_expected,
    ty_compatible Ω T_actual T_expected ->
    runtime_rootless_ty env T_expected ->
    runtime_rootless_ty env T_actual.
Proof.
  intros env Ω T_actual T_expected Hcompat.
  induction Hcompat; intros Hrootless.
  - subst ce.
    change (runtime_rootless_ty env (MkTy ua (ty_core (MkTy ue ca)))).
    apply runtime_rootless_ty_change_usage. exact Hrootless.
  - inversion Hrootless.
  - inversion Hrootless.
  - constructor.
  - inversion Hrootless.
  - inversion Hrootless.
  - inversion Hrootless; subst.
    constructor. apply IHHcompat. assumption.
  - inversion Hrootless; subst.
    constructor. apply IHHcompat. assumption.
  - inversion Hrootless; subst.
    apply IHHcompat. assumption.
Qed.

Lemma ty_lifetime_equiv_runtime_rootless_actual :
  forall env T_actual T_expected,
    ty_lifetime_equiv T_actual T_expected ->
    runtime_rootless_ty env T_expected ->
    runtime_rootless_ty env T_actual
with ty_lifetime_equiv_runtime_rootless_fields_actual :
  forall env lts_actual lts_expected args_actual args_expected fdefs,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    runtime_rootless_fields env lts_expected args_expected fdefs ->
    runtime_rootless_fields env lts_actual args_actual fdefs
with ty_lifetime_equiv_runtime_rootless_enum_variants_actual :
  forall env lts_actual lts_expected args_actual args_expected variants,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    runtime_rootless_enum_variants env lts_expected args_expected variants ->
    runtime_rootless_enum_variants env lts_actual args_actual variants
with ty_lifetime_equiv_runtime_rootless_enum_fields_actual :
  forall env lts_actual lts_expected args_actual args_expected Ts,
    Forall2 ty_lifetime_equiv args_actual args_expected ->
    runtime_rootless_enum_fields env lts_expected args_expected Ts ->
    runtime_rootless_enum_fields env lts_actual args_actual Ts.
Proof.
  - intros env T_actual T_expected Heq Hrootless.
    destruct Heq; inversion Hrootless; subst; try solve [constructor].
    + eapply RRT_Struct.
      * exact H2.
      * eapply ty_lifetime_equiv_runtime_rootless_fields_actual; eassumption.
	    + eapply RRT_Enum.
	      * exact H2.
	      * eapply ty_lifetime_equiv_runtime_rootless_enum_variants_actual; eassumption.
	    + apply RRT_Forall.
	      eapply ty_lifetime_equiv_runtime_rootless_actual; eassumption.
	    + apply RRT_TypeForall.
	      eapply ty_lifetime_equiv_runtime_rootless_actual; eassumption.
	  - intros env lts_actual lts_expected args_actual args_expected fdefs
      Hargs Hfields.
    induction Hfields.
    + constructor.
    + constructor.
      * eapply ty_lifetime_equiv_runtime_rootless_actual.
        -- eapply instantiate_struct_field_ty_lifetime_equiv. exact Hargs.
        -- exact H.
	      * apply IHHfields. exact Hargs.
  - intros env lts_actual lts_expected args_actual args_expected variants
      Hargs Hvariants.
    induction Hvariants.
    + constructor.
    + constructor.
      * eapply ty_lifetime_equiv_runtime_rootless_enum_fields_actual; eassumption.
      * apply IHHvariants. exact Hargs.
  - intros env lts_actual lts_expected args_actual args_expected Ts
      Hargs Hfields.
    induction Hfields.
    + constructor.
    + constructor.
      * eapply ty_lifetime_equiv_runtime_rootless_actual.
        -- eapply instantiate_enum_variant_field_ty_lifetime_equiv. exact Hargs.
        -- exact H.
      * apply IHHfields. exact Hargs.
Qed.

Lemma capture_ref_free_ty_b_fuel_runtime_rootless :
  forall fuel env T,
    capture_ref_free_ty_b_fuel fuel env T = true ->
    runtime_rootless_ty env T.
Proof.
  induction fuel as [| fuel IH]; intros env T Hfree; simpl in Hfree;
    try discriminate.
  destruct T as [u core].
  destruct core as
    [| | | | named | tparam | name lts args | name lts args | params ret
     | env_lt params ret | n Ω body | tn tbounds tbody | la rk inner];
    simpl in *; try discriminate.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply andb_true_iff in Hfree as [Hargs Hfields_lookup].
    destruct (lookup_struct name env) as [sdef |] eqn:Hlookup;
      try discriminate.
	    eapply RRT_Struct.
	    + exact Hlookup.
	    + clear Hargs.
	      induction (struct_fields sdef) as [| f fs IHfs]; simpl in *.
      * constructor.
      * apply andb_true_iff in Hfields_lookup as [Hfield Hfields].
        constructor.
	        -- apply IH. exact Hfield.
	        -- apply IHfs. exact Hfields.
  - apply andb_true_iff in Hfree as [Hargs Hvariants_lookup].
    destruct (lookup_enum name env) as [edef |] eqn:Hlookup;
      try discriminate.
	    eapply RRT_Enum.
	    + exact Hlookup.
	    + induction (enum_variants edef) as [| v vs IHvs]; simpl in *.
	      * constructor.
	      * apply andb_true_iff in Hvariants_lookup as [Hv Hvs].
	        constructor.
	        -- induction (enum_variant_fields v) as [| T Ts IHTs]; simpl in *.
	           ++ constructor.
	           ++ apply andb_true_iff in Hv as [HT HTs].
	              constructor.
	              ** apply IH. exact HT.
	              ** apply IHTs. exact HTs.
	        -- apply IHvs. exact Hvs.
  - constructor.
  - apply RRT_Forall. apply IH. exact Hfree.
  - apply RRT_TypeForall. apply IH. exact Hfree.
Qed.

Lemma capture_ref_free_ty_b_runtime_rootless :
  forall env T,
    capture_ref_free_ty_b env T = true ->
    runtime_rootless_ty env T.
Proof.
  intros env T Hfree.
  unfold capture_ref_free_ty_b in Hfree.
  eapply capture_ref_free_ty_b_fuel_runtime_rootless. exact Hfree.
Qed.

Lemma lookup_struct_deterministic :
  forall env name sdef1 sdef2,
    lookup_struct name env = Some sdef1 ->
    lookup_struct name env = Some sdef2 ->
    sdef1 = sdef2.
Proof.
  intros env name sdef1 sdef2 Hlookup1 Hlookup2.
  rewrite Hlookup1 in Hlookup2.
  inversion Hlookup2. reflexivity.
Qed.

Lemma lookup_enum_deterministic :
  forall env name edef1 edef2,
    lookup_enum name env = Some edef1 ->
    lookup_enum name env = Some edef2 ->
    edef1 = edef2.
Proof.
  intros env name edef1 edef2 Hlookup1 Hlookup2.
  rewrite Hlookup1 in Hlookup2.
  inversion Hlookup2. reflexivity.
Qed.

Lemma lookup_enum_in_success_rootfacts :
  forall name enums e,
    lookup_enum_in name enums = Some e ->
    In e enums /\ enum_name e = name.
Proof.
  intros name enums.
  induction enums as [| h rest IH]; intros e Hlookup; simpl in Hlookup.
  - discriminate.
  - destruct (String.eqb name (enum_name h)) eqn:Hname.
    + inversion Hlookup; subst.
      apply String.eqb_eq in Hname.
      split; [left; reflexivity | symmetry; exact Hname].
    + destruct (IH e Hlookup) as [Hin Henum].
      split; [right; exact Hin | exact Henum].
Qed.

Lemma lookup_enum_success_rootfacts :
  forall env name e,
    lookup_enum name env = Some e ->
    In e (env_enums env) /\ enum_name e = name.
Proof.
  unfold lookup_enum. intros env name e H.
  apply lookup_enum_in_success_rootfacts. exact H.
Qed.

Lemma lookup_enum_variant_runtime_rootless :
  forall env lts args variants variant_name vdef,
    lookup_enum_variant variant_name variants = Some vdef ->
    runtime_rootless_enum_variants env lts args variants ->
    runtime_rootless_enum_fields env lts args (enum_variant_fields vdef).
Proof.
  intros env lts args variants.
  induction variants as [| v variants IH]; intros variant_name vdef Hlookup Hrootless;
    simpl in Hlookup.
  - discriminate.
  - inversion Hrootless; subst.
    destruct (String.eqb variant_name (enum_variant_name v)) eqn:Hname.
    + inversion Hlookup; subst. assumption.
    + eapply IH; eassumption.
Qed.

Lemma runtime_rootless_enum_fields_Forall :
  forall env lts args Ts,
    runtime_rootless_enum_fields env lts args Ts ->
    Forall (runtime_rootless_ty env)
      (map (instantiate_enum_variant_field_ty lts args) Ts).
Proof.
  intros env lts args Ts Hrootless.
  induction Hrootless.
  - constructor.
  - simpl. constructor; assumption.
Qed.

Lemma value_roots_within_excludes_rootfacts :
  (forall roots v,
    value_roots_within roots v ->
    forall root,
      roots_exclude root roots ->
      value_refs_exclude_root root v) /\
  (forall R se,
    store_entry_roots_within R se ->
    forall root,
      root_env_excludes root R ->
      se_name se <> root ->
      store_entry_refs_exclude_root root se) /\
  (forall R s,
    store_roots_within R s ->
    forall root,
      root_env_excludes root R ->
      (forall se, In se s -> se_name se <> root) ->
      store_refs_exclude_root root s) /\
  (forall roots fields,
    value_fields_roots_within roots fields ->
    forall root,
      roots_exclude root roots ->
      value_fields_refs_exclude_root root fields).
Proof.
  apply value_roots_within_mutind; intros;
    try solve [constructor; eauto].
  - econstructor.
    destruct (ident_eqb root x) eqn:Hroot; try reflexivity.
    apply ident_eqb_eq in Hroot. subst x. contradiction.
  - constructor. constructor.
  - constructor.
    + eapply H; eauto.
      eapply H2. simpl. left. reflexivity.
    + eapply H0; eauto.
      intros se0 Hin. eapply H2. simpl. right. exact Hin.
Qed.

Lemma value_roots_within_empty_refs_exclude :
  forall v root,
    value_roots_within [] v ->
    value_refs_exclude_root root v.
Proof.
  intros v root Hwithin.
  eapply (proj1 value_roots_within_excludes_rootfacts); eauto.
  unfold roots_exclude. intros Hin. contradiction.
Qed.

Definition root_atom_eq_dec : forall a b : root_atom, {a = b} + {a <> b}.
Proof.
  intros [x | x] [y | y].
  - destruct x as [xs xn], y as [ys yn].
    destruct (string_dec xs ys) as [Hs | Hs]; subst.
    + destruct (Nat.eq_dec xn yn) as [Hn | Hn]; subst.
      * left. reflexivity.
      * right. intros H. inversion H. contradiction.
    + right. intros H. inversion H. contradiction.
  - right. discriminate.
  - right. discriminate.
  - destruct x as [xs xn], y as [ys yn].
    destruct (string_dec xs ys) as [Hs | Hs]; subst.
    + destruct (Nat.eq_dec xn yn) as [Hn | Hn]; subst.
      * left. reflexivity.
      * right. intros H. inversion H. contradiction.
    + right. intros H. inversion H. contradiction.
Defined.

Fixpoint value_size (v : value) : nat :=
  match v with
  | VStruct _ fields =>
      S ((fix fields_size (fields : list (string * value)) : nat :=
            match fields with
            | [] => 0
            | (_, fv) :: rest => value_size fv + fields_size rest
            end) fields)
  | VEnum _ _ _ _ values =>
      S ((fix values_size (values : list value) : nat :=
            match values with
            | [] => 0
            | fv :: rest => value_size fv + values_size rest
            end) values)
  | VClosure _ _ => 1
  | _ => 1
  end.

Lemma value_roots_within_from_refs_exclude :
  forall roots v,
    (forall root, roots_exclude root roots -> value_refs_exclude_root root v) ->
    value_roots_within roots v.
Proof.
  intros roots v.
  remember (S (value_size v)) as n eqn:Hn.
  assert (Hlt : value_size v < n) by lia.
  clear Hn.
  revert v roots Hlt.
  induction n as [| n IH]; intros v roots Hlt Hrefs; [lia |].
  destruct v as [| i | f | b | name fields | enum_name variant_name lts args values
               | x path | fname captured]; try solve [constructor].
  - apply VRW_Struct.
    revert Hlt Hrefs.
    induction fields as [| [fname fv] rest IHfields]; intros Hlt Hrefs; simpl in *.
    + constructor.
    + constructor.
      * apply IH.
        -- lia.
        -- intros root Hexcl.
           pose proof (Hrefs root Hexcl) as Hstruct.
           inversion Hstruct; subst.
           match goal with
           | Hfields : value_fields_refs_exclude_root root _ |- _ =>
               inversion Hfields; subst; assumption
           end.
      * apply IHfields.
        -- lia.
        -- intros root Hexcl.
           constructor.
           pose proof (Hrefs root Hexcl) as Hstruct.
           inversion Hstruct; subst.
           match goal with
           | Hfields : value_fields_refs_exclude_root root _ |- _ =>
               inversion Hfields; subst; assumption
           end.
  - apply VRW_Enum.
    + revert Hlt Hrefs.
      induction values as [| v values IHvalues]; intros Hlt Hrefs; simpl in *.
      * constructor.
      * constructor.
        -- apply IH.
           ++ lia.
           ++ intros root Hexcl.
              pose proof (Hrefs root Hexcl) as Henum.
              inversion Henum; subst.
              repeat match goal with
              | Hvalues : Forall (value_refs_exclude_root root) (_ :: _) |- _ =>
                  inversion Hvalues; subst; clear Hvalues
              end; assumption.
        -- apply IHvalues.
           ++ lia.
           ++ intros root Hexcl.
              constructor.
              pose proof (Hrefs root Hexcl) as Henum.
              inversion Henum; subst.
              repeat match goal with
              | Hvalues : Forall (value_refs_exclude_root root) (_ :: _) |- _ =>
                  inversion Hvalues; subst; clear Hvalues
              end; assumption.
    + intros root Hexcl.
      pose proof (Hrefs root Hexcl) as Henum.
      inversion Henum; subst. assumption.
  - destruct (in_dec root_atom_eq_dec (RStore x) roots) as [Hin | Hnotin].
    + apply VRW_Ref. exact Hin.
    + exfalso.
      pose proof (Hrefs x Hnotin) as Href.
      inversion Href; subst.
      rewrite ident_eqb_refl in H0. discriminate.
  - destruct captured as [| se rest].
    + apply VRW_ClosureEmpty.
    + apply VRW_ClosureCaptured.
      intros root Hexcl.
      pose proof (Hrefs root Hexcl) as Hclosure.
      inversion Hclosure; subst. exact H0.
Qed.

Lemma value_has_type_runtime_rootless_empty_roots_mut :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    runtime_rootless_ty env T ->
    value_roots_within [] v) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    runtime_rootless_fields env lts args defs ->
    value_fields_roots_within [] fields) /\
  (forall values tys,
    enum_values_have_type env s values tys ->
    Forall (runtime_rootless_ty env) tys ->
    Forall (value_roots_within []) values /\
    forall root, Forall (value_refs_exclude_root root) values).
Proof.
  intros env s.
  apply (runtime_typing_ind env s
    (fun v T _ =>
      runtime_rootless_ty env T -> value_roots_within [] v)
    (fun lts args fields defs _ =>
      runtime_rootless_fields env lts args defs ->
      value_fields_roots_within [] fields)
    (fun values tys _ =>
      Forall (runtime_rootless_ty env) tys ->
      Forall (value_roots_within []) values /\
      forall root, Forall (value_refs_exclude_root root) values));
    try solve [intros; constructor].
  - intros name lts args fields sdef Hlookup Hfields IHfields Hrootless.
    unfold instantiate_struct_instance_ty in Hrootless.
    inversion Hrootless; subst.
    destruct (lookup_struct_success env name sdef Hlookup) as [_ Hstruct_name].
    subst name.
    assert (sdef0 = sdef) as ->.
    { eapply lookup_struct_deterministic; eassumption. }
    constructor.
    match goal with
    | Hroot_fields : runtime_rootless_fields env lts args (struct_fields sdef) |- _ =>
        eapply IHfields; exact Hroot_fields
    end.
  - intros enum_name variant_name lts args values edef vdef Hlookup Hvariant
      Hvalues IHvalues Hrootless.
    destruct (lookup_enum_success_rootfacts env enum_name edef Hlookup)
      as [_ Henum_name].
    subst enum_name.
    unfold instantiate_enum_ty in Hrootless.
    inversion Hrootless; subst.
    assert (edef0 = edef) as ->.
    { eapply lookup_enum_deterministic; eassumption. }
    constructor.
    + apply IHvalues.
      eapply runtime_rootless_enum_fields_Forall.
      eapply lookup_enum_variant_runtime_rootless; eassumption.
    + intros root _.
      apply IHvalues.
      eapply runtime_rootless_enum_fields_Forall.
      eapply lookup_enum_variant_runtime_rootless; eassumption.
  - intros u la rk x path se v T Hstore Hvalue Htype Hrootless.
    inversion Hrootless.
  - intros Ω v T_actual T_expected Htyped IHtyped Hcompat Hrootless.
    eapply IHtyped.
    eapply ty_compatible_runtime_rootless_actual; eassumption.
  - intros v T_actual T_expected Htyped IHtyped Heq Hrootless.
    eapply IHtyped.
    eapply ty_lifetime_equiv_runtime_rootless_actual; eassumption.
  - intros lts args name v fields f defs Hname Htyped IHtyped
      Hfields IHfields Hrootless.
    inversion Hrootless; subst.
    constructor.
    + match goal with
      | Hroot_field : runtime_rootless_ty env
          (instantiate_struct_field_ty lts args f) |- _ =>
          apply IHtyped; exact Hroot_field
      end.
    + match goal with
      | Hroot_fields : runtime_rootless_fields env lts args defs |- _ =>
          apply IHfields; exact Hroot_fields
      end.
  - intros _.
    split; [constructor | intros root; constructor].
  - intros v values T tys Htyped IHtyped Hvalues IHvalues Hrootless.
    inversion Hrootless; subst.
    split.
    + constructor.
      * apply IHtyped. assumption.
      * apply IHvalues. assumption.
    + intros root. constructor.
      * apply value_roots_within_empty_refs_exclude.
        apply IHtyped. assumption.
      * apply IHvalues. assumption.
Qed.

Lemma value_has_type_runtime_rootless_empty_roots :
  forall env s v T,
    value_has_type env s v T ->
    runtime_rootless_ty env T ->
    value_roots_within [] v.
Proof.
  intros env s v T Htyped Hrootless.
  exact (proj1 (value_has_type_runtime_rootless_empty_roots_mut env s)
    v T Htyped Hrootless).
Qed.

Lemma struct_fields_have_type_runtime_rootless_empty_roots :
  forall env s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    runtime_rootless_fields env lts args defs ->
    value_fields_roots_within [] fields.
Proof.
  intros env s lts args fields defs Htyped Hrootless.
  exact (proj1 (proj2 (value_has_type_runtime_rootless_empty_roots_mut env s))
    lts args fields defs Htyped Hrootless).
Qed.

Lemma enum_values_have_type_runtime_rootless_empty_roots :
  forall env s values tys,
    enum_values_have_type env s values tys ->
    Forall (runtime_rootless_ty env) tys ->
    forall root, Forall (value_refs_exclude_root root) values.
Proof.
  intros env s values tys Htyped Hrootless root.
  exact (proj2 (proj2 (proj2 (value_has_type_runtime_rootless_empty_roots_mut env s))
    values tys Htyped Hrootless) root).
Qed.

Lemma value_has_type_runtime_rootless_store_any_mut :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    runtime_rootless_ty env T ->
    forall s', value_has_type env s' v T) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    runtime_rootless_fields env lts args defs ->
    forall s', struct_fields_have_type env s' lts args fields defs) /\
  (forall values tys,
    enum_values_have_type env s values tys ->
    Forall (runtime_rootless_ty env) tys ->
    forall s', enum_values_have_type env s' values tys).
Proof.
  intros env s.
  apply (runtime_typing_ind env s
    (fun v T _ =>
      runtime_rootless_ty env T -> forall s', value_has_type env s' v T)
    (fun lts args fields defs _ =>
      runtime_rootless_fields env lts args defs ->
      forall s', struct_fields_have_type env s' lts args fields defs)
    (fun values tys _ =>
      Forall (runtime_rootless_ty env) tys ->
      forall s', enum_values_have_type env s' values tys)).
  - intros u Hrootless s'. constructor.
  - intros u i Hrootless s'. constructor.
  - intros u f Hrootless s'. constructor.
  - intros u b Hrootless s'. constructor.
  - intros name lts args fields sdef Hlookup Hfields IHfields Hrootless s'.
    unfold instantiate_struct_instance_ty in Hrootless.
    inversion Hrootless; subst.
    destruct (lookup_struct_success env name sdef Hlookup) as [_ Hstruct_name].
    subst name.
    assert (sdef0 = sdef) as ->.
    { eapply lookup_struct_deterministic; eassumption. }
    eapply VHT_Struct.
    + exact Hlookup.
    + match goal with
      | Hroot_fields : runtime_rootless_fields env lts args
          (struct_fields sdef) |- _ =>
          exact (IHfields Hroot_fields s')
      end.
  - intros enum_name variant_name lts args values edef vdef Hlookup Hvariant
      Hvalues IHvalues Hrootless s'.
    destruct (lookup_enum_success_rootfacts env enum_name edef Hlookup)
      as [_ Henum_name].
    subst enum_name.
    unfold instantiate_enum_ty in Hrootless.
    inversion Hrootless; subst.
    assert (edef0 = edef) as ->.
    { eapply lookup_enum_deterministic; eassumption. }
    eapply VHT_Enum.
    + exact Hlookup.
    + exact Hvariant.
    + eapply IHvalues.
      eapply runtime_rootless_enum_fields_Forall.
      eapply lookup_enum_variant_runtime_rootless; eassumption.
  - intros u la rk x path se v T Hstore Hvalue Htype Hrootless s'.
    inversion Hrootless.
  - intros fname fdef Hlookup Hrootless s'. constructor. exact Hlookup.
  - intros fname fdef Hin Hname Hrootless s'.
    econstructor; eassumption.
  - intros Ω v T_actual T_expected Htyped IHtyped Hcompat Hrootless s'.
    eapply VHT_Compatible.
    + eapply IHtyped.
      eapply ty_compatible_runtime_rootless_actual; eassumption.
    + exact Hcompat.
  - intros v T_actual T_expected Htyped IHtyped Heq Hrootless s'.
    eapply VHT_LifetimeEquiv.
    + eapply IHtyped.
      eapply ty_lifetime_equiv_runtime_rootless_actual; eassumption.
    + exact Heq.
  - intros lts args Hrootless s'. constructor.
  - intros lts args name v fields f defs Hname Htyped IHtyped
      Hfields IHfields Hrootless s'.
    inversion Hrootless; subst.
    econstructor.
    + match goal with
      | H : _ = _ |- _ => exact H
      | |- _ = _ => reflexivity
      end.
    + match goal with
      | Hroot_field : runtime_rootless_ty env
          (instantiate_struct_field_ty lts args f) |- _ =>
          exact (IHtyped Hroot_field s')
      end.
    + match goal with
      | Hroot_fields : runtime_rootless_fields env lts args defs |- _ =>
          exact (IHfields Hroot_fields s')
      end.
  - intros Hrootless s'. constructor.
  - intros v values T tys Htyped IHtyped Hvalues IHvalues Hrootless s'.
    inversion Hrootless; subst.
    constructor.
    + apply IHtyped. assumption.
    + apply IHvalues. assumption.
Qed.

Lemma value_has_type_runtime_rootless_store_any :
  forall env s s' v T,
    value_has_type env s v T ->
    runtime_rootless_ty env T ->
    value_has_type env s' v T.
Proof.
  intros env s s' v T Htyped Hrootless.
  exact (proj1 (value_has_type_runtime_rootless_store_any_mut env s)
    v T Htyped Hrootless s').
Qed.

Lemma struct_fields_have_type_runtime_rootless_store_any :
  forall env s s' lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    runtime_rootless_fields env lts args defs ->
    struct_fields_have_type env s' lts args fields defs.
Proof.
  intros env s s' lts args fields defs Htyped Hrootless.
  exact (proj1 (proj2 (value_has_type_runtime_rootless_store_any_mut env s))
    lts args fields defs Htyped Hrootless s').
Qed.

Lemma enum_values_have_type_runtime_rootless_store_any :
  forall env s s' values tys,
    enum_values_have_type env s values tys ->
    Forall (runtime_rootless_ty env) tys ->
    enum_values_have_type env s' values tys.
Proof.
  intros env s s' values tys Htyped Hrootless.
  exact (proj2 (proj2 (value_has_type_runtime_rootless_store_any_mut env s))
    values tys Htyped Hrootless s').
Qed.

Lemma root_set_stores_subset_equiv :
  forall roots roots' roots_bound,
    root_set_equiv roots roots' ->
    root_set_stores_subset roots' roots_bound ->
    root_set_stores_subset roots roots_bound.
Proof.
  unfold root_set_stores_subset, root_set_equiv.
  intros roots roots' roots_bound Heq Hsubset z Hin.
  apply Hsubset. apply Heq. exact Hin.
Qed.

Lemma roots_exclude_stores_subset :
  forall x roots roots_bound,
    root_set_stores_subset roots roots_bound ->
    roots_exclude x roots_bound ->
    roots_exclude x roots.
Proof.
  unfold root_set_stores_subset, roots_exclude.
  intros x roots roots_bound Hsubset Hexclude Hin.
  apply Hexclude. apply Hsubset. exact Hin.
Qed.

Lemma root_subst_lookup_stores_subset_root_sets_union :
  forall ps arg_roots y roots_bound,
    roots_bound = root_sets_union arg_roots ->
    root_set_stores_subset
      (root_subst_lookup y (root_subst_of_params ps arg_roots))
      roots_bound.
Proof.
  intros ps.
  induction ps as [| p ps IH]; intros arg_roots y roots_bound Hbound.
  - destruct arg_roots as [| roots arg_roots].
    + simpl in *. subst roots_bound.
      unfold root_set_stores_subset. intros z Hin.
      destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
    + simpl in *. subst roots_bound.
      unfold root_set_stores_subset. intros z Hin.
      destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
  - destruct arg_roots as [| roots arg_roots].
    + simpl in *. subst roots_bound.
      unfold root_set_stores_subset. intros z Hin.
      destruct Hin as [Hin | Hin]; [inversion Hin | contradiction].
    + simpl in *. subst roots_bound.
      unfold root_set_stores_subset. intros z Hin.
      destruct (ident_eqb y (param_name p)) eqn:Heq.
      * apply root_set_union_in_l. exact Hin.
      * apply root_set_union_in_r.
        eapply IH; [reflexivity | exact Hin].
Qed.

Lemma root_set_instantiate_no_store_stores_subset_root_sets_union :
  forall ps arg_roots roots,
    root_set_no_store roots ->
    root_set_stores_subset
      (root_set_instantiate (root_subst_of_params ps arg_roots) roots)
      (root_sets_union arg_roots).
Proof.
  intros ps arg_roots roots Hnostore.
  unfold root_set_stores_subset.
  intros z Hin.
  apply root_set_instantiate_in_inv in Hin.
  destruct Hin as [atom [Hatom Hinst]].
  destruct atom as [x | x].
  - exfalso. apply (Hnostore x). exact Hatom.
  - eapply root_subst_lookup_stores_subset_root_sets_union.
    + reflexivity.
    + exact Hinst.
Qed.
