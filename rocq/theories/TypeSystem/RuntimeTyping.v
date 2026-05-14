From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  OperationalSemantics TypingRules TypeChecker.
From Stdlib Require Import List String Bool.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Runtime value typing                                                 *)
(* ------------------------------------------------------------------ *)

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
  | VHT_Ref : forall u la rk x path T,
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

Lemma runtime_typing_store_irrelevant :
  forall env s,
  (forall v T,
    value_has_type env s v T ->
    forall s',
      value_has_type env s' v T) /\
  (forall lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall s',
      struct_fields_have_type env s' lts args fields defs).
Proof.
  intros env s.
  apply runtime_typing_ind; intros; eauto using value_has_type, struct_fields_have_type.
Qed.

Lemma value_has_type_store_irrelevant :
  forall env s v T,
    value_has_type env s v T ->
    forall s',
      value_has_type env s' v T.
Proof.
  intros env s v T H s'.
  exact (proj1 (runtime_typing_store_irrelevant env s) v T H s').
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

Lemma struct_fields_have_type_store_irrelevant :
  forall env s lts args fields defs,
    struct_fields_have_type env s lts args fields defs ->
    forall s',
      struct_fields_have_type env s' lts args fields defs.
Proof.
  intros env s lts args fields defs H s'.
  exact (proj2 (runtime_typing_store_irrelevant env s) lts args fields defs H s').
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

Lemma store_entry_typed_store_irrelevant :
  forall env s se ce,
    store_entry_typed env s se ce ->
    forall s',
      store_entry_typed env s' se ce.
Proof.
  intros env s [sx sT sv sst] [[[cx cT] cst] cm] H s'.
  simpl in *.
  destruct H as [Hname [HT [Hst Hv]]].
  repeat split; try assumption.
  eapply value_has_type_store_irrelevant. exact Hv.
Qed.

Lemma store_typed_store_param_irrelevant :
  forall env s_param s_entries Σ,
    Forall2 (store_entry_typed env s_param) s_entries Σ ->
    forall s_param',
      Forall2 (store_entry_typed env s_param') s_entries Σ.
Proof.
  intros env s_param s_entries Σ H.
  induction H; intros s'.
  - constructor.
  - constructor.
    + eapply store_entry_typed_store_irrelevant. exact H.
    + apply IHForall2.
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
  intros env s Σ x se Htyped.
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
      * simpl. rewrite <- HT.
        eapply value_has_type_store_irrelevant. exact Hv.
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
      * eapply value_has_type_store_irrelevant. exact Hv'.
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
  intros env s Σ x T st Htyped.
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
      * simpl. rewrite <- HT.
        eapply value_has_type_store_irrelevant. exact Hv.
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
      * eapply value_has_type_store_irrelevant. exact Hv'.
Qed.

Lemma store_typed_add :
  forall env s Σ x T m v,
    store_typed env s Σ ->
    value_has_type env s v T ->
    store_typed env (store_add x T v s) (sctx_add x T m Σ).
Proof.
  intros env s Σ x T m v Htyped Hv.
  unfold store_add, sctx_add, store_typed.
  constructor.
  - simpl. repeat split; try reflexivity.
    eapply value_has_type_store_irrelevant. exact Hv.
  - eapply store_typed_store_param_irrelevant. exact Htyped.
Qed.

Lemma store_typed_add_compatible :
  forall env Ω s Σ x T_actual T_expected m v,
    store_typed env s Σ ->
    value_has_type env s v T_actual ->
    ty_compatible Ω T_actual T_expected ->
    store_typed env (store_add x T_expected v s)
      (sctx_add x T_expected m Σ).
Proof.
  intros env Ω s Σ x T_actual T_expected m v Hstore Hv Hcompat.
  eapply store_typed_add.
  - exact Hstore.
  - eapply value_has_type_compatible; eassumption.
Qed.

Lemma store_typed_remove :
  forall env s Σ x,
    store_typed env s Σ ->
    store_typed env (store_remove x s) (sctx_remove x Σ).
Proof.
  intros env s Σ x Htyped.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH].
  - constructor.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + eapply store_typed_store_param_irrelevant. exact Htail.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant. exact IH.
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
  intros env s Σ x f s' Σ' Htyped Hrefines.
  revert s' Σ'.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH]; intros s' Σ' Hs HΣ.
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
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- apply Hrefines. exact Hst.
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant. exact Htail.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_state x f s_tail) as [s_tail' |] eqn:Hs_tail;
        try discriminate.
      destruct (sctx_update_state x f Σ_tail) as [Σ_tail' |] eqn:HΣ_tail;
        try discriminate.
      inversion Hs; subst s'.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        apply IH; reflexivity.
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

Lemma store_typed_mark_used :
  forall env s Σ x Σ',
    store_typed env s Σ ->
    sctx_update_state x (state_consume_path []) Σ = Some Σ' ->
    store_typed env (store_mark_used x s) Σ'.
Proof.
  intros env s Σ x Σ' Htyped HΣ.
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
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant. exact Htail.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (sctx_update_state x (state_consume_path []) Σ_tail)
        as [Σ_tail' |] eqn:Htail_update; try discriminate.
      inversion HΣ; subst Σ'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        apply IH. reflexivity.
Qed.

Lemma store_typed_update_val :
  forall env s Σ x v T st s',
    store_typed env s Σ ->
    sctx_lookup x Σ = Some (T, st) ->
    value_has_type env s v T ->
    store_update_val x v s = Some s' ->
    store_typed env s' Σ.
Proof.
  intros env s Σ x v T st s' Htyped Hlookup Hv Hupdate.
  revert s' Hupdate T st Hlookup Hv.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros s' Hupdate T st Hlookup Hv.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hsv]]].
    simpl in Hupdate, Hlookup.
    destruct (ident_eqb x sx) eqn:Hsx;
      destruct (ident_eqb x cx) eqn:Hcx.
    + inversion Hupdate; subst s'.
      inversion Hlookup; subst T st.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact Hst.
        -- rewrite HT. eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant. exact Htail.
    + apply ident_eqb_eq in Hsx. apply ident_eqb_neq in Hcx. subst sx.
      contradiction.
    + apply ident_eqb_neq in Hsx. apply ident_eqb_eq in Hcx.
      subst cx. exfalso. apply Hsx. exact Hcx.
    + destruct (store_update_val x v s_tail) as [s_tail' |] eqn:Htail_update;
        try discriminate.
      inversion Hupdate; subst s'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_irrelevant. exact Hsv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH.
        -- reflexivity.
        -- exact Hlookup.
        -- eapply value_has_type_store_irrelevant. exact Hv.
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

Lemma store_typed_update_path :
  forall env s Σ x path v_new s',
    store_typed env s Σ ->
    (forall se T st,
      store_lookup x s = Some se ->
      sctx_lookup x Σ = Some (T, st) ->
      forall v_root,
        value_update_path (se_val se) path v_new = Some v_root ->
        value_has_type env s v_root T) ->
    store_update_path x path v_new s = Some s' ->
    store_typed env s' Σ.
Proof.
  intros env s Σ x path v_new s' Htyped Hroot Hupdate.
  revert s' Hupdate Hroot.
  induction Htyped as [|se ce s_tail Σ_tail Hentry Htail IH];
    intros s' Hupdate Hroot.
  - discriminate.
  - destruct se as [sx sT sv sst].
    destruct ce as [[[cx cT] cst] cm].
    simpl in Hentry.
    destruct Hentry as [Hname [HT [Hst Hv]]].
    simpl in Hupdate.
    destruct (ident_eqb x sx) eqn:Hsx.
    + destruct (value_update_path sv path v_new) as [v_root |] eqn:Hvalue;
        try discriminate.
      inversion Hupdate; subst s'.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact Hst.
        -- rewrite HT.
           eapply value_has_type_store_irrelevant.
           eapply Hroot.
           ++ simpl. rewrite Hsx. reflexivity.
           ++ simpl. rewrite <- Hname.
              apply ident_eqb_eq in Hsx.
              rewrite <- Hsx. rewrite ident_eqb_refl. reflexivity.
           ++ exact Hvalue.
      * eapply store_typed_store_param_irrelevant. exact Htail.
    + destruct (store_update_path x path v_new s_tail) as [s_tail' |]
        eqn:Htail_update; try discriminate.
      inversion Hupdate; subst s'.
      constructor.
      * simpl. repeat split; try assumption.
        eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH.
        -- reflexivity.
        -- intros se0 T st Hlookup HΣ v_root Hvalue.
           eapply value_has_type_store_irrelevant.
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

Lemma store_typed_ctx_merge_left :
  forall env s Σ2 Σ3 Σ4,
    store_typed env s Σ2 ->
    ctx_merge (ctx_of_sctx Σ2) (ctx_of_sctx Σ3) = Some Σ4 ->
    store_typed env s Σ4.
Proof.
  intros env s Σ2 Σ3 Σ4 Htyped.
  revert Σ3 Σ4.
  induction Htyped as [|se ce2 s_tail Σ2_tail Hentry Htail IH];
    intros Σ3 Σ4 Hmerge.
  - destruct Σ3 as [|[[[cx3 cT3] cst3] cm3] Σ3_tail];
      simpl in Hmerge; try discriminate.
    inversion Hmerge; subst; unfold store_typed; apply Forall2_nil.
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
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH. exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact (binding_state_refines_trans sst cst2
          (MkBindingState (st_consumed cst2 || st_consumed cst3)
            (st_moved_paths cst2 ++ st_moved_paths cst3))
          Href (binding_state_refines_merge_left cst2 cst3 _ eq_refl)).
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH. exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- exact Hname.
        -- exact HT.
        -- exact (binding_state_refines_trans sst cst2
          (MkBindingState (st_consumed cst2 || st_consumed cst3)
            (st_moved_paths cst2 ++ st_moved_paths cst3))
          Href (binding_state_refines_merge_left cst2 cst3 _ eq_refl)).
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH. exact Htail_merge.
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
  intros env s Σ2 Σ3 Σ4 Htyped.
  revert Σ2 Σ4.
  induction Htyped as [|se ce3 s_tail Σ3_tail Hentry Htail IH];
    intros Σ2 Σ4 Htypes Hmerge.
  - destruct Σ2 as [|[[[cx2 cT2] cst2] cm2] Σ2_tail];
      simpl in Hmerge; try discriminate.
    inversion Hmerge; subst; unfold store_typed; apply Forall2_nil.
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
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH.
        -- exact Htypes_tail.
        -- exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- transitivity cx3; [exact Hname | symmetry; exact Hneq].
        -- symmetry. exact HT_left.
        -- exact (binding_state_refines_trans sst cst3
             (MkBindingState (st_consumed cst2 || st_consumed cst3)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href (binding_state_refines_merge_right cst2 cst3 _ eq_refl)).
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH.
        -- exact Htypes_tail.
        -- exact Htail_merge.
    + simpl in Hmerge. inversion Hmerge; subst Σ4.
      constructor.
      * simpl. repeat split.
        -- transitivity cx3; [exact Hname | symmetry; exact Hneq].
        -- symmetry. exact HT_left.
        -- exact (binding_state_refines_trans sst cst3
             (MkBindingState (st_consumed cst2 || st_consumed cst3)
               (st_moved_paths cst2 ++ st_moved_paths cst3))
             Href (binding_state_refines_merge_right cst2 cst3 _ eq_refl)).
        -- eapply value_has_type_store_irrelevant. exact Hv.
      * eapply store_typed_store_param_irrelevant.
        eapply IH.
        -- exact Htypes_tail.
        -- exact Htail_merge.
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
      exists (MkTy ua (TRef la rk Ta)). split.
      * reflexivity.
      * eapply TC_Ref; eassumption.
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
