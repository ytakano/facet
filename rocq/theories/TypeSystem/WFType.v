From Facet.TypeSystem Require Import Lifetime Types.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Type well-formedness                                                 *)
(* ------------------------------------------------------------------ *)

(* wf_type Δ T holds when T is well-formed under region context Δ.    *)
(* Reference types require the lifetime to be valid in Δ.             *)
Inductive wf_type (Δ : region_ctx) : Ty -> Prop :=
| WF_Units    : forall u,   wf_type Δ (MkTy u TUnits)
| WF_Integers : forall u,   wf_type Δ (MkTy u TIntegers)
| WF_Floats   : forall u,   wf_type Δ (MkTy u TFloats)
| WF_Booleans : forall u,   wf_type Δ (MkTy u TBooleans)
| WF_Named    : forall u s, wf_type Δ (MkTy u (TNamed s))
| WF_Param    : forall u i, wf_type Δ (MkTy u (TParam i))
| WF_Struct   : forall u name lts args,
    Forall (wf_lifetime Δ) lts ->
    Forall (wf_type Δ) args ->
    wf_type Δ (MkTy u (TStruct name lts args))
| WF_Fn       : forall u params ret,
    Forall (wf_type Δ) params ->
    wf_type Δ ret ->
    wf_type Δ (MkTy u (TFn params ret))
| WF_Forall   : forall u n Ω body,
    wf_type ((map LBound (seq 0 n)) ++ Δ) body ->
    Forall (fun '(a, b) => wf_lifetime ((map LBound (seq 0 n)) ++ Δ) a /\
                            wf_lifetime ((map LBound (seq 0 n)) ++ Δ) b) Ω ->
    wf_type Δ (MkTy u (TForall n Ω body))
| WF_Ref      : forall u l rk T,
    ref_usage_ok_b u rk = true ->
    wf_lifetime Δ l ->
    wf_type Δ T ->
    wf_type Δ (MkTy u (TRef l rk T)).

(* ------------------------------------------------------------------ *)
(* Example: &unrestricted isize is well-formed in any context          *)
(* ------------------------------------------------------------------ *)

Example wf_shared_ref_isize :
  wf_type [] (MkTy UUnrestricted (TRef LStatic RShared (MkTy UUnrestricted TIntegers))).
Proof.
  apply WF_Ref.
  - reflexivity.
  - apply WF_LStatic.
  - apply WF_Integers.
Qed.
