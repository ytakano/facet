From Facet.TypeSystem Require Import Lifetime Types Syntax PathState Program
  Renaming OperationalSemantics TypingRules TypeChecker RuntimeTyping RootProvenance
  EnvStructuralRules AlphaRenaming EnvSoundnessFacts CheckerSoundness.
From Facet.TypeSystem Require Export TypeSafetyPrefixPreservationCallInvariants.
From Stdlib Require Import List Bool ZArith String Program.Equality.
Import ListNotations.

Lemma eval_let_roots_ready_preserves_typing_with_preservation_core :
  eval_preserves_typing_ready_mutual_statement ->
  eval_preserves_roots_ready_mutual_statement ->
  forall env (Ω : outlives_ctx) (n : nat) R R' Σ Σ' s s'
      m x T_ann e1 e2 T roots v,
    store_typed env s Σ ->
    store_roots_within R s ->
    store_no_shadow s ->
    root_env_no_shadow R ->
    typed_env_roots env Ω n R Σ (ELet m x T_ann e1 e2) T Σ' R' roots ->
    provenance_ready_expr (ELet m x T_ann e1 e2) ->
    preservation_ready_expr e1 ->
    preservation_ready_expr e2 ->
    eval env s (ELet m x T_ann e1 e2) s' v ->
    store_typed env s' Σ' /\
    value_has_type env s' v T /\
    store_ref_targets_preserved env s s' /\
    store_roots_within R' s' /\
    value_roots_within roots v /\
    store_no_shadow s' /\
    root_env_no_shadow R'.
Proof.
  intros Hpreservation Hroots_preservation env Ω n R R' Σ Σ' s s'
    m x T_ann e1 e2 T roots v Hstore Hroots Hnodup Hrn Htyped
    Hready Hready1_struct Hready2_struct Heval.
  destruct (proj1 Hroots_preservation env s
              (ELet m x T_ann e1 e2) s' v Heval
              Ω n R Σ T Σ' R' roots Hready Hroots Hnodup Hrn Htyped)
    as [Hroots_final [Hv_roots [Hnodup_final Hrn_final]]].
  dependent destruction Hready.
  inversion Heval; subst.
  inversion Htyped; subst.
  match goal with
  | Htyped1 : typed_env_roots env Ω n R Σ e1 ?T1_body ?Σ1_body
      ?R1_body ?roots1_body,
    Hcompat : ty_compatible_b Ω ?T1_body T_ann = true,
    Hfresh : root_env_lookup x ?R1_body = None,
    Htyped2 : typed_env_roots env Ω n
      (root_env_add x ?roots1_body ?R1_body)
      (sctx_add x T_ann m ?Σ1_body) e2 ?T2_body ?Σ2_body
      ?R2_body ?roots2_body,
    Hcheck : sctx_check_ok env x T_ann ?Σ2_body = true,
    Hexcl_roots : roots_exclude x ?roots2_body,
    Hexcl_env : root_env_excludes x (root_env_remove x ?R2_body),
    Heval1 : eval env s e1 ?s1_body ?v1_body,
    Heval2 : eval env (store_add x T_ann ?v1_body ?s1_body) e2
      ?s2_body ?v2_body |- _ =>
      let Hpres1 := fresh "Hpres1" in
      let Hpres2 := fresh "Hpres2" in
      assert (Hpres1 :
        store_typed env s Σ ->
        typed_env_structural env Ω n Σ e1 T1_body Σ1_body ->
        eval env s e1 s1_body v1_body ->
        store_typed env s1_body Σ1_body /\
        value_has_type env s1_body v1_body T1_body /\
        store_ref_targets_preserved env s s1_body);
      [ intros Hstore0 Htyped0 Heval0;
        exact (proj1 Hpreservation env s e1 s1_body v1_body Heval0
          Ω n Σ T1_body Σ1_body Hready1_struct Hstore0 Htyped0)
      | assert (Hpres2 :
          store_typed env (store_add x T_ann v1_body s1_body)
            (sctx_add x T_ann m Σ1_body) ->
          typed_env_structural env Ω n (sctx_add x T_ann m Σ1_body)
            e2 T2_body Σ2_body ->
          eval env (store_add x T_ann v1_body s1_body) e2 s2_body v2_body ->
          store_typed env s2_body Σ2_body /\
          value_has_type env s2_body v2_body T2_body /\
          store_ref_targets_preserved env
            (store_add x T_ann v1_body s1_body) s2_body);
        [ intros Hstore0 Htyped0 Heval0;
          exact (proj1 Hpreservation env
            (store_add x T_ann v1_body s1_body) e2 s2_body v2_body
            Heval0 Ω n (sctx_add x T_ann m Σ1_body) T2_body
            Σ2_body Hready2_struct Hstore0 Htyped0)
        | destruct (eval_let_roots_preserves_typing env Ω n R R1_body
            R2_body Σ Σ1_body Σ2_body s s1_body s2_body m x T_ann
            T1_body e1 e2 T2_body roots1_body roots2_body v1_body
            v2_body Hstore Hroots Hnodup Hrn Htyped1 Hcompat Hfresh
            Htyped2 Hcheck Hexcl_roots Hexcl_env Hready1 Hready2 Heval1
            Heval2 Hpres1 Hpres2)
          as [Hstore_final [Hv_final Hpres_final]];
          repeat split; assumption ]
      ]
  end.
Qed.
