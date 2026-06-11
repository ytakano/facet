From Facet.TypeSystem Require Import Lifetime Types Program TypingRules CheckerBase.

Definition ty_compatible_assoc
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : Prop :=
  ty_compatible Ω
    (normalize_assoc_ty env T_actual)
    (normalize_assoc_ty env T_expected).

Definition ty_compatible_assoc_b
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : bool :=
  ty_compatible_b Ω
    (normalize_assoc_ty env T_actual)
    (normalize_assoc_ty env T_expected).

Definition ty_compatible_assoc_checked
    (env : global_env) (Ω : outlives_ctx)
    (T_actual T_expected : Ty) : Prop :=
  ty_compatible_assoc_b env Ω T_actual T_expected = true.
