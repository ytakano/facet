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

## Current Status

Last updated implementation point: strengthened runtime `VHT_Ref` target invariant.

- S0: `[done]` runtime value/store typing と runtime reference well-formedness の仕様は導入済み。
- S1: `[done]` path/value/store helper の主要部分と linear partial-move obligation helper/checker fix は導入済み。
- S2: `[partial]` 個別 preservation helper、`eval_args` helper、direct assign/replace bridge、readiness helper、ready restricted mutual preservation theorem は導入済み。`VHT_Ref` は runtime store 内の参照先 path の存在・型対応を要求する形に強化済み。full unrestricted theorem は未完了。
- S3: `[todo]` call/closure preservation は未着手。ただし empty closure value typing helper は一部存在する。
- S4-S6: `[todo]` checker-to-runtime safety、runtime reference safety、small-step progress は未着手。

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

1. **S0: safety statement 固定** `[done]`
   - `RuntimeTyping.v` を追加し、runtime value/store の型付け仕様を定義済み。
   - `value_has_type env s v T` を定義済み。
   - `store_typed env s Σ` は state 完全一致ではなく `binding_state_refines runtime static` ベースで定義済み。
   - `runtime_refs_wf env s v` / `store_refs_wf env s` を定義済み。
   - `borrow_ok_env_structural` は ownership/aliasing invariant として後続 theorem で使い、typing preservation の最小 theorem には混ぜない。

2. **S1: value/path/store helper** `[done]`
   - `[done]` `value_lookup_path` と `type_lookup_path` の対応を証明済み。
   - `[done]` `value_update_path` が `value_has_type` を保存することを証明済み。
   - `[done]` `store_lookup`, `store_update_val`, `store_update_path`, `store_consume_path`, `store_add`, `store_remove` の `store_typed` 保存補題を追加済み。
   - `[done]` `store_restore_path` は availability 前提付きの `store_typed_restore_available_path` を追加済み。
   - `[done]` `ctx_merge` 後の store typing は then/else 両側補題を追加済み。
   - `[done]` struct field value list と `struct_fields` の lookup/update helper を追加済み。
   - `[done]` linear struct の partial move は、親 binding 全体の消費ではなく、型に基づく linear component ごとの消費義務として表す。
   - `[done]` `sctx_check_ok` が `st_moved_paths` の prefix conflict だけで linear binding を OK にしないよう、残余 linear obligation を計算する helper と soundness 補題を追加済み（`308496a`）。

3. **S2: big-step preservation / result typing** `[partial]`
   - `[done]` `EUnit`, literal, `EFn`, `EVar`, direct `EPlace`, `ELet`, `EDrop`, `EIf` の個別 preservation helper を追加済み。
   - `[done]` struct literal と `eval_struct_fields` の preservation helper を追加済み。
   - `[done]` `EBorrow` は shared/unique/direct/indirect の result typing helper を追加済み。
   - `[done]` direct path `EAssign` / `EReplace` を path-aware store helper へ接続済み。
   - `[done]` root `Eval_Assign` / `Eval_Replace` 用 preservation helper を追加済み。
   - `[done]` `eval_args_preserves_typing` と `eval_args_values_have_types` を追加済み（`68dfd35`）。
   - `[done]` direct assign/replace の full `eval` derivation を root/path helper へ接続する bridge lemma を追加済み（`f17beb2`）。
   - `[done]` runtime/static copy-vs-move mismatch contradiction helper を追加済み（`855577d`）。
   - `[done]` `preservation_ready_expr` / `preservation_ready_args` / `preservation_ready_fields` と field lookup helper を追加済み（`4675b39`）。
   - `[done]` `replace p e_new` は target path が `e_new` 評価後も available であることを typing premise として preservation に使う。これは自己消費する `replace s.f s.f` を拒否する既存ガードの証明側の対応である。
   - `[done]` direct `assign p e_new` も target path が `e_new` 評価後も available であることを typing premise として要求する。
   - `[done]` `eval`, `eval_args`, `eval_struct_fields` の相互 induction で ready subset 用の `eval_preserves_typing_ready_mutual` を証明済み（`4947081`）。
   - `[done]` `VHT_Ref` を強化し、`VRef x path` が `store_lookup x s`、`value_lookup_path`、`type_lookup_path` で実在する runtime target を指すことを要求するようにした。これに伴い、古い `value_has_type_store_irrelevant` は削除し、`store_ref_targets_preserved` 前提付きの `value_has_type_store_preserved` に置き換えた。
   - `[done]` `store_update_state` / `store_mark_used` / restore 系の state-only 更新が `store_ref_targets_preserved` を満たす補題を追加済み。
   - `[partial]` direct `assign` / `replace` / `let` / borrow / args / struct fields は、強化後の reference preservation obligation を露出する形に補題を弱めた。未証明 obligation は explicit premise にし、ready subset からは外している。
   - `[todo]` ready restriction のない full `eval_preserves_typing` を証明する。
   - `[done]` `typed_env_structural` が binding lookup/type を保存する same-bindings helper を追加し、現在 explicit premise にしている lookup 条件を theorem 本体で導出できるようにした。
   - `[done]` `EIf` false branch の `store_typed_ctx_merge_right` 用 type-equality premise は branch typing から導出できる helper を追加済み。
   - `[todo]` indirect `EReplace` / `EAssign`、`EDeref`、`ECall` / `ECallExpr` を preservation theorem へ接続する。
   - `[todo]` `ELetInfer` の現在の contradiction-only helper を実証明に置き換える。
   - `[todo]` `let` の local binding への reference escape を禁止する typing/borrow invariant を追加し、`store_remove` が `store_ref_targets_preserved` を満たすことを証明する。
   - `[todo]` `assign` / `replace` の value update が既存 reference target を壊さないことを示すため、`value_has_type` から `type_lookup_path` 対応 path の runtime value 存在を導く補題と、`store_update_val` / `store_update_path` の `store_ref_targets_preserved` 補題を追加する。
   - `[todo]` `borrow` preservation は、`eval_place` が返す `(x,path)` に対して store target が存在することを typing/store から導出する補題を追加して ready subset に戻す。
   - `[todo]` `eval_args` / `eval_struct_fields` の sequencing は、各 step が `store_ref_targets_preserved` を返す相互 preservation theorem に強めてから ready subset に戻す。
   - `[done]` `EReplace` / `EAssign` は root binding の mutability だけでなく、target path 上の struct field mutability を検査する。少なくとも最終 field は `MMutable` を必須にする。
   - `[done]` `&mut T` の referent type は invariant にする。`&shared T` は inner type の covariant compatibility を維持してよいが、unique reference は usage/core/lifetime の厳密一致または invariant relation だけを許す。
   - theorem は `typed_env_structural` から始め、checker theorem は使わない。

4. **S3: function call / current closure value safety** `[todo]`
   - `VClosure fname captured` の runtime typing を定義する。
   - `[partial]` 現状の `EFn` は empty capture を返すため、まず `captured = []` の closure safety を証明する。`VClosure fname []` の value typing helper は一部追加済み。
   - `bind_params` と `store_remove_params` が `store_typed` を保存する補題を追加する。
   - `ECall` / `ECallExpr` の preservation を証明する。
   - 将来の closure 導入前に、captured store の型付け invariant をこの milestone で固定する。

5. **S4: checker-to-runtime end-to-end safety** `[todo]`
   - `infer_full_env_structural_sound` を使って、checker 成功から big-step safety theorem へ接続する。
   - `initial_store_for_fn f s` を定義し、関数引数 store と `params_ctx` の対応を証明する。
   - `infer_full_env_big_step_safe` を追加する。
   - Validator 経由 theorem として `validate_env` / `validate_fns` 成功後の safety theorem を追加する。

6. **S5: borrow/runtime reference safety** `[todo]`
   - `VRef x path` が指す store path が存在し、型が `TRef` の inner type と対応することを証明する。
   - `refs_in_value` / `refs_in_store` を定義する。
   - `borrow_ok_env_structural` と runtime refs の対応 invariant を導入する。
   - borrow 中の元 place に対する通常の `EVar` / `EPlace` read/move を active borrow state と照合する。
   - conflicting unique borrow がある place は read/copy/move/update を禁止する。conflicting shared borrow がある place は affine/linear move と mutable update を禁止し、unrestricted copy の扱いは仕様として明示する。
   - `let` 境界で、削除される local binding に由来する reference が body result や store に escape しないことを検査・証明する。必要なら fresh let-region を導入するが、最初は escape check で進める。
   - local type annotation の lifetime elision が `LVar 0` 固定にならないよう、local annotation 内の elided lifetime は当面拒否する。fresh local region 導入は後続拡張に残す。
   - dangling reference が評価結果・store に残らないことを theorem 化する。
   - path prefix conflict に基づく aliasing safety は、shared/mut の runtime ref set を導入して段階的に証明する。

7. **S6: small-step semantics と progress** `[todo]`
   - `StepSemantics.v` を追加し、`step env s e s' e'` と `terminal` を定義する。
   - big-step preservation で得た helper を再利用し、small-step preservation を証明する。
   - closed expression または well-typed runtime configuration に対して `progress` / `not_stuck` を証明する。
   - divergence は progress theorem で扱い、big-step result theorem とは分離する。

8. **S7: future feature gates** `[todo]`
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

1. `[done]` `RuntimeTyping.v` を追加して S0/S1 の定義と主要 store helper を証明する。
2. `[partial]` `TypeSafety.v` を追加して S2 の個別 preservation helper を基本式から始める。
3. `[done]` `typed_env_structural` の same-bindings lookup helper を追加し、assign/replace helper の explicit lookup premise を theorem 本体で導出できるようにする。
4. `[done]` `eval`, `eval_args`, `eval_struct_fields` の ready restricted mutual preservation theorem を追加し、既存 helper を constructor ごとに接続する。
5. `[current]` full preservation に残る indirect update / deref / call blocker を S2/S3/S5 に分解する。
6. `[todo]` call/closure 関連の S3 を追加する。
7. `[todo]` `EnvFullSoundness.v` / `ValidatorSoundness.v` と接続して S4 を証明する。
8. `[todo]` borrow/runtime reference safety を S5 として別 theorem 群にする。
9. `[todo]` small-step semantics が必要になった時点で S6 を開始する。

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

- `[todo]` borrow 中の root/field を move/read する式は拒否される。
- `[todo]` inner `let` の local binding への reference が外側へ escape する式は拒否される。
- `[done]` linear struct の一部 field だけを move/drop して残りの linear field を放置する式は拒否される。
- `[done]` `replace x x` / `replace s.f s.f` のように target を new value 評価中に消費する式は拒否され続ける。
- `[done]` moved target への direct `assign` は拒否される。
- `[done]` immutable field への assign/replace は、root binding が mutable でも拒否される。
- `[done]` `&mut unrestricted T` を `&mut affine T` など異なる referent type として使う式は拒否される。
- `[todo]` local annotation の elided lifetime は拒否される。
- `[todo]` generic trait は arity・type argument・bounds の validation が入るまで soundness 対象から外す。

型安全性 roadmap の初期完了条件:

- `[done]` ready restricted `eval_preserves_typing_ready_mutual` が `typed_env_structural` から証明されている。
- `[todo]` unrestricted `eval_preserves_typing` が `typed_env_structural` から証明されている。
- `[todo]` `infer_full_env_big_step_safe` が checker 成功 theorem と接続されている。
- `[todo]` `VRef` の dangling reference safety が theorem として独立している。
- `[done]` progress は small-step milestone へ明示的に分離されている。

## Known Risks

- 現在の `eval` は big-step なので、非停止や stuck state の一般的な progress は表現できない。
- `typed_env_structural` は static context、`eval` は runtime store を扱うため、`store_typed` の設計が後続 proof の難易度を決める。
- `VClosure fname captured` は将来の closure 実装で大きく変わる可能性があるため、captured store invariant を早めに固定する必要がある。
- borrow checker の static `path_borrow_state` と runtime refs の対応は未定義なので、aliasing safety は preservation とは別 milestone にする。
- `plan/review.md` の指摘は古い extracted artifact の行番号を参照しているため、roadmap では行番号ではなく semantic issue として追跡する。
- 強化後の `VHT_Ref` により、従来の「value typing は store に依存しない」という仮定は使えない。今後の preservation は store typing だけでなく、評価が既存 reference target を保存することを明示的に運ぶ必要がある。
