# Type Safety Roadmap

## 方針

現在の env/stateful 経路では、checker soundness は証明済みである。

- `infer_core_env_state_fuel_structural_sound`
- `borrow_check_env_structural_sound`
- `infer_full_env_structural_sound`

ただし、これらは「checker が Prop レベル仕様に対して sound」であることを示す theorem であり、operational semantics まで含む型安全性 theorem ではない。

この roadmap では、`OperationalSemantics.v` の big-step `eval` と `EnvStructuralRules.v` の `typed_env_structural` / `borrow_ok_env_structural` を接続し、段階的に preservation、runtime reference safety、aliasing safety、将来の small-step progress へ進む。

原則:

- checker soundness と type safety を分離する。
- 最初の target は big-step result typing / preservation とする。
- progress は現状の big-step semantics では直接表現しにくいため、small-step semantics 導入後に扱う。
- closure、variant、effect、function generics は、導入と同時に safety invariant を更新する。
- `Admitted` / `Axiom` は使わない。

## Target Theorems

最初に欲しい theorem:

```coq
Theorem eval_preserves_typing :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    eval env s e s' v ->
    store_typed env s' Σ' /\ value_has_type env s' v T.

Theorem infer_full_env_big_step_safe :
  forall env f T Γ' s s' v,
    ValidEnv env ->
    infer_full_env env f = infer_ok (T, Γ') ->
    initial_store_for_fn f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
```

その後に追加する theorem:

```coq
Theorem eval_no_dangling_refs :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    borrow_ok_env_structural env [] (ctx_of_sctx Σ) e [] ->
    eval env s e s' v ->
    refs_wf env s' v /\ store_refs_wf env s'.

Theorem step_progress :
  forall env Ω n Σ e T,
    store_typed env [] Σ ->
    typed_env_structural env Ω n Σ e T Σ ->
    terminal e \/ exists e' s', step env [] e s' e'.
```

`step_progress` は small-step semantics 導入後の目標とし、初期 milestone では実装しない。

## Milestones

1. **S0: safety statement 固定**
   - `RuntimeTyping.v` を追加し、runtime value/store の型付け仕様を定義する。
   - `value_has_type env s v T` を定義する。
   - `store_typed env s Σ` を定義し、store entry と `sctx` entry の name/type/state が一致することを表す。
   - `runtime_refs_wf env s v` / `store_refs_wf env s` を定義する。
   - `borrow_ok_env_structural` は ownership/aliasing invariant として後続 theorem で使い、typing preservation の最小 theorem には混ぜない。

2. **S1: value/path/store helper**
   - `value_lookup_path` と `type_lookup_path` の対応を証明する。
   - `value_update_path` が `value_has_type` を保存することを証明する。
   - `store_lookup`, `store_update_val`, `store_update_path`, `store_consume_path`, `store_restore_path`, `store_add`, `store_remove` が `store_typed` を保存することを証明する。
   - struct field value list と `struct_fields` の対応関係を定義し、field lookup/update の補題を追加する。
   - linear struct の partial move は、親 binding 全体の消費ではなく、型に基づく linear component ごとの消費義務として表す。
   - `sctx_check_ok` が `st_moved_paths` の prefix conflict だけで linear binding を OK にしないよう、残余 linear obligation を計算する helper と soundness 補題を追加する。

3. **S2: big-step preservation / result typing**
   - `eval`, `eval_args`, `eval_struct_fields` の相互 induction で preservation を証明する。
   - `EUnit`, literal, `EVar`, `EPlace`, `ELet`, `ELetInfer`, `EDrop`, `EIf` を先に通す。
   - struct literal と field access/move の store state 対応を証明する。
   - `EReplace`, `EAssign`, `EBorrow`, `EDeref` を path-aware store helper へ接続する。
   - `replace p e_new` は、target path が `e_new` 評価後も available であることを typing premise として preservation に使う。これは自己消費する `replace s.f s.f` を拒否する既存ガードの証明側の対応である。
   - `EReplace` / `EAssign` は root binding の mutability だけでなく、target path 上の struct field mutability を検査する。少なくとも最終 field は `MMutable` を必須にする。
   - `&mut T` の referent type は invariant にする。`&shared T` は inner type の covariant compatibility を維持してよいが、unique reference は usage/core/lifetime の厳密一致または invariant relation だけを許す。
   - theorem は `typed_env_structural` から始め、checker theorem は使わない。

4. **S3: function call / current closure value safety**
   - `VClosure fname captured` の runtime typing を定義する。
   - 現状の `EFn` は empty capture を返すため、まず `captured = []` の closure safety を証明する。
   - `bind_params` と `store_remove_params` が `store_typed` を保存する補題を追加する。
   - `ECall` / `ECallExpr` の preservation を証明する。
   - 将来の closure 導入前に、captured store の型付け invariant をこの milestone で固定する。

5. **S4: checker-to-runtime end-to-end safety**
   - `infer_full_env_structural_sound` を使って、checker 成功から big-step safety theorem へ接続する。
   - `initial_store_for_fn f s` を定義し、関数引数 store と `params_ctx` の対応を証明する。
   - `infer_full_env_big_step_safe` を追加する。
   - Validator 経由 theorem として `validate_env` / `validate_fns` 成功後の safety theorem を追加する。

6. **S5: borrow/runtime reference safety**
   - `VRef x path` が指す store path が存在し、型が `TRef` の inner type と対応することを証明する。
   - `refs_in_value` / `refs_in_store` を定義する。
   - `borrow_ok_env_structural` と runtime refs の対応 invariant を導入する。
   - borrow 中の元 place に対する通常の `EVar` / `EPlace` read/move を active borrow state と照合する。
   - conflicting unique borrow がある place は read/copy/move/update を禁止する。conflicting shared borrow がある place は affine/linear move と mutable update を禁止し、unrestricted copy の扱いは仕様として明示する。
   - `let` 境界で、削除される local binding に由来する reference が body result や store に escape しないことを検査・証明する。必要なら fresh let-region を導入するが、最初は escape check で進める。
   - local type annotation の lifetime elision が `LVar 0` 固定にならないよう、local annotation 内の elided lifetime は当面拒否する。fresh local region 導入は後続拡張に残す。
   - dangling reference が評価結果・store に残らないことを theorem 化する。
   - path prefix conflict に基づく aliasing safety は、shared/mut の runtime ref set を導入して段階的に証明する。

7. **S6: small-step semantics と progress**
   - `StepSemantics.v` を追加し、`step env s e s' e'` と `terminal` を定義する。
   - big-step preservation で得た helper を再利用し、small-step preservation を証明する。
   - closed expression または well-typed runtime configuration に対して `progress` / `not_stuck` を証明する。
   - divergence は progress theorem で扱い、big-step result theorem とは分離する。

8. **S7: future feature gates**
   - closure:
     - captured environment の store typing と borrow invariant を追加する。
     - closure escaping と lifetime/borrow の関係を safety theorem に反映する。
   - function generics:
     - runtime type erasure の補題を追加する。
     - type/lifetime substitution が `value_has_type` と `store_typed` を保存することを証明する。
   - generic trait:
     - trait impl の type argument 数が trait 定義と一致することを検証する。
     - bound 側で `Trait<Args...>` を表現できるようにし、impl/use 時に trait 自身の bounds を反映する。
     - generic trait の checker/runtime 接続は、arity・bounds・impl validation が揃うまで feature gate として扱う。
   - variant:
     - variant value typing、constructor typing、match exhaustiveness safety を追加する。
     - pattern match の preservation/progress を追加する。
   - effect:
     - `eval` / `step` の result を value から effectful outcome へ拡張するかを決める。
     - preservation statement を effect row/capability を含む形に更新する。

## Implementation Order

1. `RuntimeTyping.v` を追加して S0/S1 の定義と store helper を証明する。
2. `TypeSafety.v` を追加して S2 の big-step preservation を基本式から始める。
3. call/closure 関連の S3 を追加する。
4. `EnvFullSoundness.v` / `ValidatorSoundness.v` と接続して S4 を証明する。
5. borrow/runtime reference safety を S5 として別 theorem 群にする。
6. small-step semantics が必要になった時点で S6 を開始する。

## Acceptance Criteria

各 milestone 完了時:

```sh
cd rocq && make -B
rg -n "\bAxiom\b|Admitted\." rocq/theories
git diff --check
```

S4 以降:

```sh
dune build
bash tests/run.sh
sh tests/fir/run.sh
```

review 指摘に対応する regression:

- borrow 中の root/field を move/read する式は拒否される。
- inner `let` の local binding への reference が外側へ escape する式は拒否される。
- linear struct の一部 field だけを move/drop して残りの linear field を放置する式は拒否される。
- `replace x x` / `replace s.f s.f` のように target を new value 評価中に消費する式は拒否され続ける。
- immutable field への assign/replace は、root binding が mutable でも拒否される。
- `&mut unrestricted T` を `&mut affine T` など異なる referent type として使う式は拒否される。
- local annotation の elided lifetime は拒否される。
- generic trait は arity・type argument・bounds の validation が入るまで soundness 対象から外す。

型安全性 roadmap の初期完了条件:

- `eval_preserves_typing` が `typed_env_structural` から証明されている。
- `infer_full_env_big_step_safe` が checker 成功 theorem と接続されている。
- `VRef` の dangling reference safety が theorem として独立している。
- progress は small-step milestone へ明示的に分離されている。

## Known Risks

- 現在の `eval` は big-step なので、非停止や stuck state の一般的な progress は表現できない。
- `typed_env_structural` は static context、`eval` は runtime store を扱うため、`store_typed` の設計が後続 proof の難易度を決める。
- `VClosure fname captured` は将来の closure 実装で大きく変わる可能性があるため、captured store invariant を早めに固定する必要がある。
- borrow checker の static `path_borrow_state` と runtime refs の対応は未定義なので、aliasing safety は preservation とは別 milestone にする。
- `plan/review.md` の指摘は古い extracted artifact の行番号を参照しているため、roadmap では行番号ではなく semantic issue として追跡する。
