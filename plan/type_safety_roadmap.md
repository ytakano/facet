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

Last updated implementation point: generic trait bounds now carry trait type arguments, `check_struct_bounds` resolves bounds with those arguments, and frontend validation rejects malformed bound refs while checking trait-own bounds on impls. `BorrowStateSafety.v` defines `pbs_no_conflicts` for active path borrows and pairwise conflict facts; `borrow_check_env` checks direct `EVar` / `EPlace` access against active path borrows; OCaml de Bruijn lowering rejects local annotated `let` types that contain `&T` / `&mut T` without explicit lifetime. Runtime aliasing correspondence is still future work.

- S0: `[done]` runtime value/store typing と runtime reference well-formedness の仕様は導入済み。
- S1: `[done]` path/value/store helper の主要部分と linear partial-move obligation helper/checker fix は導入済み。
- S2: `[partial]` 個別 preservation helper、`eval_args` helper、direct assign/replace bridge、readiness helper、ready restricted mutual preservation theorem は導入済み。`VHT_Ref` は runtime store 内の参照先 path の存在・型対応を要求する形に強化済み。direct assign/replace は concrete RHS preservation evidence 経由で ready subset に再接続済み。`store_remove` 用の root-exclusion runtime helper、static root provenance judgment、runtime root-within-to-exclusion bridge、ready fragment の root preservation theorem、roots-aware `ELet` bridge、top-level roots-ready `ELet` helper、roots-aware ready mutual preservation theorem、checker-facing root provenance sidecar API と soundness theorem は追加済み。full unrestricted theorem は未完了。
- S3: `[todo]` call/closure preservation は未着手。ただし empty closure value typing helper は一部存在する。
- S4: `[partial]` checker-to-runtime safety は root sidecar / ready fragment で接続済み。full unrestricted theorem と validator 経由 theorem は未着手。
- S5: `[partial]` ready/root-provenance fragment で runtime refs の no-dangling theorem、direct ref membership target theorem、static borrow-state no-conflict invariant、pairwise conflict corollary、direct access guard、local annotation lifetime elision rejection は追加済み。runtime aliasing correspondence と captured closure refs は未着手。
- S6: `[todo]` small-step progress は未着手。

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
   - `[done]` `eval`, `eval_args`, `eval_struct_fields` の相互 induction で ready subset 用の `eval_preserves_typing_ready_mutual` を証明済み（`4947081`）。強化後は各 branch が `store_ref_targets_preserved` も返す形に更新済み。
   - `[done]` `VHT_Ref` を強化し、`VRef x path` が `store_lookup x s`、`value_lookup_path`、`type_lookup_path` で実在する runtime target を指すことを要求するようにした。これに伴い、古い `value_has_type_store_irrelevant` は削除し、`store_ref_targets_preserved` 前提付きの `value_has_type_store_preserved` に置き換えた。
   - `[done]` `store_update_state` / `store_mark_used` / restore 系の state-only 更新が `store_ref_targets_preserved` を満たす補題を追加済み。
   - `[done]` direct `assign` / `replace` は、強化後の reference preservation obligation を露出する形に helper を弱め、concrete RHS preservation evidence を渡して root/path の update・restore obligation と ready subset への再接続を完了済み。
   - `[partial]` direct `let` は、強化後の reference preservation obligation に対する local binding removal / escape invariant が未解決。runtime 側には `value_refs_exclude_root` / `store_refs_exclude_root` と scoped `store_remove` helper を追加済みで、`eval_let_preserves_typing` は false な global remove-preservation premise ではなく root-exclusion premise を要求する形に弱めた。
   - `[done]` static root provenance として `root_set` / `root_env`、`typed_env_roots` / `typed_args_roots` / `typed_fields_roots`、および既存 `typed_env_structural` への projection lemma を追加済み。checker-facing API として別名 sidecar `infer_core_env_roots` / `infer_env_roots` / `infer_full_env_roots` を追加し、sidecar 成功から `typed_env_roots` を導く soundness theorem も追加済み。
   - `[done]` `typed_env_roots` の path assign/replace は、field-insensitive summary が untouched field 内の reference root を忘れないよう、既存 binding roots と RHS roots の union で更新する形に修正済み。
   - `[done]` `typed_env_roots` の `ELet` / `ELetInfer` は、body store に local binding を追加する前に `root_env_lookup x R1 = None` を要求するよう強化済み。
   - `[done]` `typed_env_roots` の root summaries を runtime 側の `value_refs_exclude_root` / `store_refs_exclude_root` premise へ変換するため、`TypeSafety.v` に `value_roots_within` / `store_roots_within` と exclusion bridge lemma を追加済み。
   - `[done]` `store_roots_within` の weakening、fresh lookup、`store_add` / `store_remove`、state-only update 用 helper を追加済み。
   - `[done]` `root_env` / `sctx` / runtime `store` の no-shadow/no-duplicate invariant と、add/remove/state-only/value/path update が名前集合を保存する helper を追加済み。
   - `[done]` no-shadow 前提付きで、`root_env_remove x` / `store_remove x` 後に `x` lookup が消えることを証明済み。
   - `[done]` roots-aware update preservation 用に、store 内に対象名が存在しない場合の `root_env_update` 保存 helper と、`value_roots_within` の union weakening helper は追加済み。
   - `[done]` `value_update_path` / `store_update_val` / `store_update_path` が `store_roots_within` を union summary に対して保存する helper を no-shadow 前提で証明済み。
   - `[done]` `replace p e_new` の result root summary は `[]` ではなく、置換前 target binding の root summary を返すよう修正済み。
   - `[done]` `typed_env_roots` / `typed_args_roots` / `typed_fields_roots` が `root_env_no_shadow` を保存する helper を追加済み。
   - `[done]` provenance-aware preservation theorem 用に、`provenance_ready_*` predicate、field lookup helper、`store_add` の fresh reference-target preservation、store/value path root lookup helper を追加済み。
   - `[done]` update alignment helper を追加し、runtime `eval_place` が返す `(x,path)` と static `typed_env_roots` summary を direct/path update case で接続済み。
   - `[done]` `typed_env_roots` を使う strengthened preservation theorem として `eval_preserves_roots_ready_mutual` を追加し、評価結果と出力 store が static root summaries に収まることを `eval` / `eval_args` / `eval_struct_fields` の相互 induction で証明済み。
   - `[done]` `eval_preserves_roots_ready_mutual` を使って `ELet` の root-exclusion premise を discharge する `eval_let_roots_preserves_typing` を追加済み。
   - `[done]` subexpression が既存 structural-ready subset に入る top-level `ELet` について、`eval_let_roots_ready_preserves_typing` を追加済み。
   - `[done]` `eval_let_roots_preserves_typing` を roots-aware ready mutual preservation theorem に組み込み、`ELet` を recursive preservation に戻す。
   - `[todo]` ready restriction のない full `eval_preserves_typing` を証明する。
   - `[done]` `typed_env_structural` が binding lookup/type を保存する same-bindings helper を追加し、現在 explicit premise にしている lookup 条件を theorem 本体で導出できるようにした。
   - `[done]` `EIf` false branch の `store_typed_ctx_merge_right` 用 type-equality premise は branch typing から導出できる helper を追加済み。
   - `[todo]` indirect `EReplace` / `EAssign`、`EDeref`、`ECall` / `ECallExpr` を preservation theorem へ接続する。
   - `[todo]` `ELetInfer` の現在の contradiction-only helper を実証明に置き換える。
   - `[todo]` `let` の local binding への reference escape を禁止する typing/borrow invariant を追加し、`store_remove` が `store_ref_targets_preserved` を満たすことを証明する。
   - `[done]` `assign` / `replace` の value update が既存 reference target を壊さないことを示すため、`value_has_type` から `type_lookup_path` 対応 path の runtime value 存在を導く補題と、typed `store_update_val` / `store_update_path` の `store_ref_targets_preserved` 補題を追加済み。
   - `[done]` `borrow` preservation は、direct place の `eval_place` が返す `(x,path)` に対して store target が存在することを typing/store から導出する補題を追加し、direct shared/unique borrow を ready subset に再接続済み。
   - `[done]` `eval_args` / `eval_struct_fields` の sequencing は、各 step が `store_ref_targets_preserved` を返す相互 preservation theorem に強め、非空 args/fields の ready constructor を復元済み。
   - `[done]` `EReplace` / `EAssign` は root binding の mutability だけでなく、target path 上の struct field mutability を検査する。少なくとも最終 field は `MMutable` を必須にする。
   - `[done]` `&mut T` の referent type は invariant にする。`&shared T` は inner type の covariant compatibility を維持してよいが、unique reference は usage/core/lifetime の厳密一致または invariant relation だけを許す。
   - theorem は `typed_env_structural` から始め、checker theorem は使わない。

4. **S3: function call / current closure value safety** `[todo]`
   - `VClosure fname captured` の runtime typing を定義する。
   - `[partial]` 現状の `EFn` は empty capture を返すため、まず `captured = []` の closure safety を証明する。`VClosure fname []` の value typing helper は一部追加済み。
   - `[partial]` `bind_params` は複数 parameter でも `params_ctx` と同じ順序で store entry を追加するよう修正済み。
   - `[partial]` call body の runtime store が caller store tail を保持するケースに備え、static context が visible prefix だけを記述する `store_typed_prefix` と基本 lookup/add 補題を追加済み。`bind_params` については parameter no-dup と caller store tail freshness 前提の下で typed-prefix preservation を追加済み。`store_remove_params (bind_params ps vs s) = s` の immediate cleanup roundtrip と、parameter prefix が残る store から caller frame を cleanup する `store_param_prefix` 補題も追加済み。state/value/path update・mark/consume/restore が parameter prefix を保存する構造補題と、`ELet` の local binding を parameter prefix の前に許す scoped prefix relation も追加済み。さらに state/value/path update・mark/consume/restore が scoped prefix を保存する構造補題も追加済み。roots-ready fragment では body evaluation 全体が scoped parameter prefix を保存する `eval_preserves_param_scope_roots_ready_mutual` も追加済み。`initial_root_env_for_params` の names/no-shadow/coverage 補題と、call body 開始 store が parameter scope と root coverage を持つ bridge も追加済み。加えて state/value/path update・mark/consume/restore が `store_typed_prefix` を保存する補題も追加済み。次は full `ECall` / `ECallExpr` preservation へ接続する invariant を固定する。
   - `[partial]` `ECall` preservation は、関数 body が typed 済みであることを表す環境前提（`env_fns_typed_structural`）と、runtime `lookup_fn` が typing witness と一致するための関数名一意性前提（`fn_env_unique_by_name`）を使う方針に固定済み。operational lookup helper と、この明示前提を受け取る preservation wrapper API も追加済み。`TES_Call` 単体は callee body typing を含まない。
   - `bind_params` の typed-prefix preservation は、parameter 名が caller store tail を shadow しない freshness/no-shadow 明示前提で接続済み。次はこの前提を call preservation theorem 側でどの invariant から供給するかを固定する。
   - `[partial]` lifetime substitution 済み引数を元の `fn_params` に bind する箇所は、runtime value typing が lifetime substitution と両立する補題を追加してから接続する。現状、`value_has_type_apply_lt_ty` は `apply_lt_ty σ T = T` の stable 前提つきでのみ証明済み。`VHT_Ref` は `type_lookup_path env (se_ty se) path = Some T` に依存し、`apply_lt_ty` が path type を変える場合は無条件 bridge が成立しないため、call preservation 前に params/ret の lifetime-erasure/stability invariant を固定する必要がある。
   - `ECall` / `ECallExpr` の preservation を証明する。
   - 将来の closure 導入前に、captured store の型付け invariant をこの milestone で固定する。

5. **S4: checker-to-runtime end-to-end safety** `[partial]`
   - `infer_full_env_structural_sound` を使って、checker 成功から big-step safety theorem へ接続する。
   - `[done]` `initial_store_for_fn env f s` を定義し、関数引数 store と `params_ctx` の対応を runtime store typing として固定する。
   - `[done]` `initial_root_env_for_params` / `initial_root_env_for_fn` を定義し、names/no-shadow/coverage helper を追加する。
   - `[done]` root sidecar checker 成功から ready fragment の big-step result typing を導く `infer_full_env_roots_big_step_safe_ready` を追加する。
   - `infer_full_env_big_step_safe` を追加する。
   - Validator 経由 theorem として `validate_env` / `validate_fns` 成功後の safety theorem を追加する。

6. **S5: borrow/runtime reference safety** `[partial]`
   - `[done]` `value_has_type` / `store_typed` から `runtime_refs_wf` / `store_refs_wf` を導く bridge lemma を追加する。
   - `[done]` ready/root-provenance fragment の `eval_no_dangling_refs_roots_ready` を追加する。
   - `[done]` root sidecar checker 成功から ready fragment の no-dangling refs を導く `infer_full_env_roots_no_dangling_refs_ready` を追加する。
   - `[done]` direct `VRef x path` が指す store path が存在し、型が対応することを `runtime_refs_wf_ref_target` と refs-in target theorem 群で証明する。
   - `[done]` non-captured closure fragment 用の `refs_in_value` / `refs_in_store` を定義する。captured closure refs は scoped closure-store invariant まで defer する。
   - `[done]` static active borrow state の no-conflict invariant `pbs_no_conflicts` を定義し、`borrow_ok_env_structural` / `borrow_check_env` が保存することを証明する。
   - `[done]` `pbs_no_conflicts` から shared/mut と distinct mut/mut の pairwise no-conflict corollary を導き、`borrow_check_env` 成功後にも接続する。
   - `borrow_ok_env_structural` と runtime refs の対応 invariant を導入する。
   - `[done]` borrow 中の元 place に対する通常の `EVar` / direct `EPlace` read/move を active borrow state と照合する。
   - `[done]` conflicting unique borrow がある direct place は read/copy/move/update を禁止する。conflicting shared borrow がある direct place は affine/linear move と mutable update を禁止し、unrestricted copy は許可する。indirect place は後続 slice に残す。
   - reference value の `drop` は borrow release として扱わない。`drop r; drop x` のように参照の最後の使用後に元 place を再利用するケースは、後続の non-lexical lifetime / last-use analysis で borrow end point を推論して解決する。
   - `let` 境界で、削除される local binding に由来する reference が body result や store に escape しないことを検査・証明する。必要なら fresh let-region を導入するが、最初は escape check で進める。
   - `[done]` local type annotation の lifetime elision が `LVar 0` 固定にならないよう、local annotation 内の elided lifetime は当面拒否する。fresh local region 導入は後続拡張に残す。
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
     - `[done]` trait impl の type argument 数が trait 定義と一致することを OCaml frontend validation で検証する。trait impl target の lifetime argument は、Rocq `trait_def` が type parameter だけを持つため拒否する。
     - `[done]` bound 側で `Trait<Args...>` を表現し、struct literal の bound check で trait args を使う。
     - `[done]` frontend / validator で impl の trait 自身の bounds を検査する。
     - generic trait の checker/runtime 接続は、trait-bound recursion や impl 側 `where` clause が必要になった時点で再評価する。
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
5. `[done]` direct update bridge の callback shape を concrete RHS evaluation 用に分け、direct assign/replace を ready subset に戻す。
6. `[partial]` `ELet` / `ELetInfer` の local binding removal 用 runtime root-exclusion helper を追加し、let preservation helper を scoped premise へ弱める。
7. `[partial]` root-sensitive provenance summary を Prop-level typing に追加し、既存 structural typing へ project できることを証明する。
8. `[partial]` root summaries から runtime exclusion への bridge を追加する。
9. `[done]` root provenance の path update rules を union ベースに直し、let freshness premise と runtime root helper を追加する。
10. `[done]` `root_env` / `store` / `sctx` の no-shadow/no-duplicate binding invariant を追加し、`root_env_remove` / name-preserving store/context update helper をその invariant 前提で証明する。
11. `[done]` `store_update_val` / `store_update_path` の roots-aware preservation helper を no-shadow 前提で証明する。
12. `[done]` update alignment helper を追加して provenance-aware preservation theorem を完成させ、評価結果と出力 store が static root summaries に収まることを証明する。
13. `[done]` `eval_preserves_roots_ready_mutual` を使って `ELet` の root-exclusion premise を discharge する bridge を追加する。
14. `[done]` roots-aware ready mutual preservation theorem を追加し、`ELet` bridge を recursive preservation に組み込む。
15. `[done]` checker が root provenance を返す executable interface を追加する。`infer_core_env_roots` / `infer_env_roots` / `infer_full_env_roots` は追加済み。
16. `[done]` sidecar checker 成功から `typed_env_roots` を導く soundness theorem を追加する。
17. `[done]` sidecar root soundness を使って S4 の checker-to-runtime 接続を ready fragment で開始する。
18. `[partial]` `EnvRuntimeSafety.v` に root sidecar / ready fragment の `infer_full_env_roots_big_step_safe_ready` を追加する。full `infer_full_env_big_step_safe` と `ValidatorSoundness.v` 経由 theorem は未完了。
19. `[partial]` `RuntimeRefSafety.v` に ready/root-provenance fragment の no-dangling runtime reference theorem 群と direct ref membership target theorem 群を追加し、`BorrowStateSafety.v` に static borrow-state no-conflict invariant と pairwise conflict corollary を追加する。`borrow_check_env` は direct `EVar` / `EPlace` access を active borrow state と照合済み。OCaml lowering は local annotation の elided reference lifetime を拒否済み。runtime aliasing correspondence、non-lexical lifetime / last-use based borrow end points、indirect place access、captured closure refs は未完了。
20. `[todo]` small-step semantics が必要になった時点で S6 を開始する。

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

- `[done]` borrow 中の direct root/field を move/read する式は拒否される。indirect place は後続 slice。
- `[todo]` reference の最後の使用後に元 root/field の direct move/read を再び許可する。これは `drop` を release primitive にせず、non-lexical lifetime / last-use analysis で解決する。
- `[todo]` inner `let` の local binding への reference が外側へ escape する式は拒否される。
- `[done]` linear struct の一部 field だけを move/drop して残りの linear field を放置する式は拒否される。
- `[done]` `replace x x` / `replace s.f s.f` のように target を new value 評価中に消費する式は拒否され続ける。
- `[done]` moved target への direct `assign` は拒否される。
- `[done]` immutable field への assign/replace は、root binding が mutable でも拒否される。
- `[done]` `&mut unrestricted T` を `&mut affine T` など異なる referent type として使う式は拒否される。
- `[done]` local annotation の elided lifetime は拒否される。
- `[done]` generic trait は impl arity/type argument validation、bound 側 `Trait<Args...>`、trait 自身の bounds 反映を追加済み。

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
- `store_remove x` は `VRef x _` を含む surviving value があると `value_has_type` を壊すため、global な `store_ref_targets_preserved env s (store_remove x s)` は false。`ELet` preservation は root-sensitive provenance summary を static typing/checker に追加するまで ready theorem へ再接続できない。
- root provenance は Prop-level API と別名 sidecar checker API の両方に存在し、sidecar 成功から `typed_env_roots` を導く soundness theorem は追加済み。checker-to-runtime theorem へ接続するには、初期 root environment と runtime store root invariant の対応を固定する必要がある。
