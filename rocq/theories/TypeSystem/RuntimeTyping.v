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
(* Runtime store typing                                                 *)
(* ------------------------------------------------------------------ *)

Definition store_entry_typed
    (env : global_env) (s : store) (se : store_entry) (ce : sctx_entry) : Prop :=
  match se, ce with
  | MkStoreEntry sx sT sv sst, (cx, cT, cst, _) =>
      sx = cx /\
      sT = cT /\
      sst = cst /\
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
      se_state se = st /\
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
      se_state se = st /\
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
    store_update_state x f s = Some s' ->
    sctx_update_state x f Σ = Some Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x f s' Σ' Htyped.
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
        -- rewrite Hst. reflexivity.
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
    store_restore_path x p s = Some s' ->
    sctx_restore_path Σ x p = infer_ok Σ' ->
    store_typed env s' Σ'.
Proof.
  intros env s Σ x p s' Σ' Htyped Hs HΣ.
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
  eapply store_typed_update_state; eassumption.
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
        -- rewrite Hst. reflexivity.
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
