# Env Checker Soundness Roadmap

## 方針

現在の公開実行経路は `infer_full_env` / `infer_core_env_state_fuel` / `borrow_check_env` に統一されている。一方で、`EnvTypingRules.v` の soundness は `TE_Checker` / `BOE_Checker` という wrapper 規則に依存しており、Rocq の証明としては弱い。

このロードマップでは、旧 `CheckerSoundness.v` / `BorrowCheckSoundness.v` が持っていた構造的 soundness を env/stateful 経路へ移植し、最終的に「抽出される新 checker が、独立した Prop レベル仕様に対して sound である」と言える状態にする。

原則:

- `TE_Checker`, `TFE_Checker`, `BOE_Checker` は段階的な足場として残してよいが、最終 theorem では使わない。
- 旧 `TypingRules.v` / legacy checker は proof 参照用に読んでよいが、新しい主定理は `EnvTypingRules.v` 側に作る。
- `Admitted` / `Axiom` は使わない。
- 各 milestone は `cd rocq && make` と `rg -n "\bAxiom\b|Admitted\." rocq/theories` を通過条件にする。

## Target Theorems

最終的に欲しい theorem:

```coq
Theorem infer_core_env_state_fuel_structural_sound :
  forall fuel env Ω n Σ e T Σ',
    infer_core_env_state_fuel fuel env Ω n Σ e = infer_ok (T, Σ') ->
    typed_env_structural env Ω n Σ e T Σ'.

Theorem borrow_check_env_structural_sound :
  forall env PBS Γ e PBS',
    borrow_check_env env PBS Γ e = infer_ok PBS' ->
    borrow_ok_env_structural env PBS Γ e PBS'.

Theorem infer_full_env_structural_sound :
  forall env f T Γ',
    ValidEnv env ->
    infer_full_env env f = infer_ok (T, Γ') ->
    checked_fn_env_structural env f.
```

`typed_env_structural`, `borrow_ok_env_structural`, `checked_fn_env_structural` は checker wrapper を含まない Prop レベル仕様とする。

## Milestones

1. **P0: 仕様の分離** [done]
   - `EnvTypingRules.v` に wrapper-free な `typed_env_structural` を追加する。
   - 既存の `typed_env` は互換用に残すか、`typed_env_checker` に rename するかを決める。
   - `typed_place_env` / `typed_place_type_env` も wrapper-free 規則を追加し、field lookup、deref、path availability を Prop として表す。
   - `borrow_ok_env_structural` / `borrow_ok_fields_env_structural` を追加し、`BOE_Checker` を使わない borrow 仕様を定義する。

2. **P1: bool/option helper soundness** [done]
   - `ty_compatible_b_sound`, `check_arg_tys` soundness, `check_args` soundness を env proof から再利用できる位置へ整理する。
   - `sctx_lookup`, `sctx_consume_path`, `sctx_restore_path`, `sctx_check_ok`, `ctx_merge` の Prop 対応 lemma を追加する。
   - `lookup_struct`, `lookup_field`, `lookup_field_b`, `first_duplicate_field`, `first_unknown_field`, `first_missing_field` の成功時 soundness を追加する。
   - `check_struct_bounds_sound` と trait impl 解決 soundness を最終 theorem で使える形に強化する。

3. **P2: 基本式の typing soundness** [done]
   - `EUnit`, `ELit`, `EVar`, `EPlace`, `EFn` の checker 分岐から構造規則を導く。
   - `ELet`, `ELetInfer`, `EDrop`, `EDeref`, `EIf` の帰納ケースを証明する。
   - `ctx_merge` 後の branch context soundness を追加する。
   - fuel が減る再帰呼び出しを扱うため、旧 `CheckerSoundness.v` と同様に expression size か fuel induction を固定する。
   - `EnvTypingSoundness.v` に `basic_expr` fragment の `infer_core_env_state_fuel_basic_structural_sound` を追加し、call/HRT、struct literal、field mutation/borrow は P3-P5 に残す。

4. **P3: call と HRT soundness**
   - `ECall` の `build_sigma`, `finalize_subst`, `apply_lt_params`, `apply_lt_ty`, `apply_lt_outlives` の soundness を証明する。
   - `ECallExpr` の `TFn` case を構造規則へ接続する。
   - `ECallExpr` の `TForall` case を旧 `CheckerSoundness.v` の `T_CallExpr_Forall` 証明相当で env/stateful 版へ移植する。
   - `build_bound_sigma`, `open_bound_ty`, `open_bound_outlives`, `contains_lbound_ty`, `contains_lbound_outlives`, `outlives_constraints_hold_b` の補題を追加する。
   - HRT fixture に対応する theorem-level regression examples を `EnvTypingRules.v` または専用 proof file に追加する。

5. **P4: struct / field typing soundness**
   - struct literal の arity、duplicate/unknown/missing field 検査から `typed_fields_env_structural` へ接続する。
   - field access の copy/move、partial move、restore、parent availability を Prop 化する。
   - `EReplace`, `EAssign`, `EBorrow` の path-aware typing soundness を wrapper なしで証明する。
   - trait bound checked struct literal について、`check_struct_bounds` 成功から `struct_bounds_resolved_env` を導くことを main proof に組み込む。

6. **P5: borrow checker env soundness**
   - `borrow_check_env` の全ケースを `borrow_ok_env_structural` に対して証明する。
   - `EUnit`, `ELit`, `EVar`, `EFn`, `EPlace`, `EStruct`, `EDrop`, `EDeref`, `ELet`, `ELetInfer`, `EIf`, `ECall`, `ECallExpr` を網羅する。
   - `PBShared` / `PBMut` の path prefix conflict lemma を追加する。
   - `pbs_new_entries`, `pbs_remove_all`, `pbs_eqb` の soundness を追加し、scope exit と branch equality を Prop に落とす。

7. **P6: validator と full checker の統合**
   - `ValidatorSoundness.v` の `validate_env_sound` を、現状の component 分解から `ValidEnv env` と checker 前提に使える形へ強化する。
   - `infer_env` 成功から `typed_fn_env_structural` を証明する。
   - `infer_full_env` 成功から `checked_fn_env_structural` を証明する。
   - OCaml CLI が使う `validate -> infer_full_env` の経路に対応する end-to-end theorem を追加する。

8. **P7: wrapper 規則の退役**
   - `infer_core_env_state_fuel_structural_sound` と `borrow_check_env_structural_sound` が通った後、最終 theorem が `TE_Checker` / `BOE_Checker` に依存していないことを確認する。
   - `TE_Checker`, `TFE_Checker`, `BOE_Checker` を削除するか、名前に `Legacy` / `CheckerSpec` を付けて main theorem から切り離す。
   - `plan/struct_roadmap.md` の M7 を「proof surface」ではなく「structural soundness 完了」に更新する。

## Known Proof Gaps

- `infer_core_env_state_fuel_sound` は現在 `TE_Checker` に包むだけで、構造的 typing を証明していない。
- `borrow_check_env_sound` は現在 `BOE_Checker` に包むだけで、borrow 規則の全ケースを証明していない。
- `ECallExpr` の `TForall` は実装済みだが、新経路での HRT soundness theorem はない。
- `ECall` の lifetime substitution、outlives constraints、argument checking の env/stateful 版 theorem が不足している。
- struct/field の一部 Prop 規則はあるが、checker 分岐からその規則へ到達する主証明が不足している。
- `ValidatorSoundness.v` は validation 成功から checker soundness へつなぐには弱い。

## Acceptance Criteria

各 milestone 完了時:

```sh
cd rocq && make
rg -n "\bAxiom\b|Admitted\." rocq/theories
```

P6 以降は追加で:

```sh
dune build
sh tests/run.sh
sh tests/fir/run.sh
```

最終完了条件:

- `infer_full_env_structural_sound` が `TE_Checker` / `BOE_Checker` を使わずに証明されている。
- HRT valid fixtures に対応する theorem-level examples が通っている。
- struct field move/borrow/replace の theorem-level examples が通っている。
- `fixtures/TypeChecker.mli` の公開 API は env checker 系のみで、legacy checker は公開されていない。
