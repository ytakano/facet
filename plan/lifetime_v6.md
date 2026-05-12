# Lifetime v6: Lifetime Substitution at ECall

## 背景と問題

v5 で `fn_lifetimes : nat` と `LVar n` ベースの region context を導入した。
しかし ECall の引数型チェックが **ライフタイム添字を完全一致** で比較するため、
lifetime-polymorphic な関数を caller の LVar 添字が異なる引数で呼び出せない。

### 具体的な失敗例

```facet
// pass_through: fn_lifetimes = 1, param: TRef (LVar 0) T, ret: TRef (LVar 0) T
fn pass_through<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}

// caller: fn_lifetimes = 2, 'a = LVar 0, 'b = LVar 1
fn longer<'a, 'b>(
    x: unrestricted &'a unrestricted isize,
    y: unrestricted &'b unrestricted isize
) -> unrestricted &'b unrestricted isize {
    pass_through(y)
    // y: TRef (LVar 1) T  vs  param: TRef (LVar 0) T  → FAIL (LVar 1 ≠ LVar 0)
}
```

`y` は `'b = LVar 1` だが `pass_through` のパラメータは `'a = LVar 0` を期待する。
意味的には `'a := 'b` と単一化すれば有効だが、v5 の完全一致チェックでは拒否される。

### なぜ今まで動いていたか

`fn_lifetimes = 0` の caller 内のローカル borrow は全て `LVar 0` になる。
`fn_lifetimes = 1` の callee のパラメータも `LVar 0`。
偶然に一致するため呼び出しが通っていた。

---

## 解決策: ECall での Lifetime Substitution

### 概念

関数呼び出し `f<σ>(args)` における lifetime 代入 σ を以下のように定義する:

```
σ : list lifetime   (* 長さ = fn_lifetimes fdef *)
σ[i]  =  callee の LVar i を caller のどのライフタイムに対応させるか
```

**型チェック手順**:
1. 各引数 `args[j]` の型 `T_j` を推論
2. `T_j` と `param_ty p[j]` を再帰的に比較し、`p[j]` 中の `LVar i` → `T_j` 中のライフタイム という対応を収集 → σ を構築
3. `args[j]` の型を `apply_lt_ty σ (param_ty p[j])` と比較（コア型・usage の一致）
4. 返り値の型を `apply_lt_ty σ (fn_ret fdef)` として返す

**Soundness**: σ の各要素 `σ[i]` は caller の region context に属するライフタイムか
`LStatic` でなければならない（`wf_lifetime_b (mk_region_ctx n) σ[i] = true`）。

---

## 新規定義（TypeChecker.v）

### `apply_lt_lifetime` — lifetime の代入適用

```coq
Definition apply_lt_lifetime (σ : list lifetime) (l : lifetime) : lifetime :=
  match l with
  | LStatic => LStatic
  | LVar i  => match nth_error σ i with
               | Some l' => l'
               | None    => l   (* 範囲外: そのまま — callee の local borrow LVar m は変えない *)
               end
  end.
```

### `apply_lt_ty` — 型全体への代入適用

```coq
Fixpoint apply_lt_ty (σ : list lifetime) (T : Ty) : Ty :=
  MkTy (ty_usage T) (apply_lt_tycore σ (ty_core T))
with apply_lt_tycore (σ : list lifetime) (c : TypeCore Ty) : TypeCore Ty :=
  match c with
  | TUnits | TIntegers | TFloats | TBooleans => c
  | TNamed s => TNamed s
  | TFn ts r => TFn (map (apply_lt_ty σ) ts) (apply_lt_ty σ r)
  | TRef l rk t => TRef (apply_lt_lifetime σ l) rk (apply_lt_ty σ t)
  end.
```

### `apply_lt_param` / `apply_lt_params`

```coq
Definition apply_lt_param (σ : list lifetime) (p : param) : param :=
  {| param_mutability := param_mutability p;
     param_name       := param_name p;
     param_ty         := apply_lt_ty σ (param_ty p) |}.

Definition apply_lt_params (σ : list lifetime) (ps : list param) : list param :=
  map (apply_lt_param σ) ps.
```

### `lt_subst_unify_ty` — 引数型からσを推論

引数型 `T_arg` とパラメータ型 `T_param` を比較し、`T_param` 中の `LVar i` が
`T_arg` 中のどのライフタイムに対応するかを記録する。

```coq
(* σ_acc : nat → option lifetime の関数（部分代入）を list に近似 *)
(* 具体的には vector または association list を使う *)

(* σ_vec[i] : None = 未確定、Some l = LVar i が l に対応すると確定 *)
Definition lt_subst_vec := list (option lifetime).

Fixpoint unify_lt_ty
    (m : nat)            (* callee の fn_lifetimes *)
    (σ : lt_subst_vec)   (* 累積中の代入 *)
    (T_param : Ty)       (* callee のパラメータ型 *)
    (T_arg   : Ty)       (* 実引数の型 *)
  : option lt_subst_vec :=
  match ty_core T_param, ty_core T_arg with
  | TRef (LVar i) rk1 T_p, TRef l_arg rk2 T_a =>
      if Nat.ltb i m && ref_kind_eqb rk1 rk2 then
        match nth_error σ i with
        | None => None  (* shouldn't happen if σ has length m *)
        | Some None    =>   (* 未確定: 記録 *)
            let σ' := list_replace i (Some l_arg) σ in
            unify_lt_ty m σ' T_p T_a
        | Some (Some l') =>  (* 既確定: 一致チェック *)
            if lifetime_eqb l' l_arg
            then unify_lt_ty m σ T_p T_a
            else None  (* 競合: 失敗 *)
        end
      else None
  | TRef LStatic rk1 T_p, TRef LStatic rk2 T_a =>
      if ref_kind_eqb rk1 rk2
      then unify_lt_ty m σ T_p T_a
      else None
  | TIntegers, TIntegers | TFloats, TFloats
  | TBooleans, TBooleans | TUnits, TUnits => Some σ
  | _, _ => None  (* core 型不一致 *)
  end.
```

### `infer_lt_subst` — 全引数から σ を構築

```coq
(* 制限なし = None の位置はデフォルト LStatic で埋める *)
Definition finalize_subst (σ : lt_subst_vec) : list lifetime :=
  map (fun opt => match opt with Some l => l | None => LStatic end) σ.

Fixpoint infer_lt_subst
    (m : nat)
    (arg_tys : list Ty)
    (ps : list param)
  : option (list lifetime) :=
  match arg_tys, ps with
  | [], [] => Some (repeat (Some LStatic) m)  (* 引数なし: 全て LStatic *)
  | t :: ts, p :: ps' =>
      let σ0 := repeat (Some (** placeholder: None**)) m in
      (* ... 全引数ペアを畳み込んで unify_lt_ty を適用 *)
  | _, _ => None  (* arity mismatch *)
  end.
```

（詳細なアルゴリズムは実装フェーズで確定させる）

---

## TypingRules.v の変更

### `T_Call` を `T_Call_Lt` に置き換え

```coq
(* 旧 T_Call: 削除または Deprecated に *)
(* 新 T_Call_Lt: lifetime substitution σ を明示 *)
| T_Call_Lt : forall Γ Γ' fname fdef args (σ : list lifetime),
    In fdef fenv ->
    fn_name fdef = fname ->
    length σ = fn_lifetimes fdef ->
    (forall l, In l σ -> wf_lifetime_b (mk_region_ctx n) l = true) ->
    typed_args fenv n Γ args (apply_lt_params σ (fn_params fdef)) Γ' ->
    typed fenv n Γ (ECall fname args)
                   (apply_lt_ty σ (fn_ret fdef)) Γ'
```

**備考**:
- `σ` の各要素は caller の region context に属するライフタイム。
  `wf_lifetime_b (mk_region_ctx n) l` がその確認。
- `apply_lt_params` が LVar i → σ[i] の代入をパラメータ型全体に適用。
- 返り値の型も `apply_lt_ty σ (fn_ret fdef)`。

**旧 T_Call との互換性**:
`T_Call` は `σ = [LVar 0; LVar 1; ...; LVar (fn_lifetimes fdef - 1)]`
（恒等代入）とした `T_Call_Lt` の特殊ケースとして導出可能。

---

## TypeChecker.v の変更

### ECall case の更新

```coq
| ECall fname args =>
    match lookup_fn_b fname fenv with
    | None => infer_err (ErrFunctionNotFound fname)
    | Some fdef =>
        let m := fn_lifetimes fdef in
        (* 1. まず全引数の型を推論 *)
        let fix infer_all Γ0 es :=
          match es with
          | [] => infer_ok ([], Γ0)
          | e' :: es' =>
              match infer_core fenv n Γ0 e' with
              | infer_err err => infer_err err
              | infer_ok (Te, Γ1) =>
                  match infer_all Γ1 es' with
                  | infer_err err => infer_err err
                  | infer_ok (tys, Γ2) => infer_ok (Te :: tys, Γ2)
                  end
              end
          end
        in
        match infer_all Γ args with
        | infer_err err => infer_err err
        | infer_ok (arg_tys, Γ_out) =>
            (* 2. σ を推論 *)
            match infer_lt_subst m arg_tys (fn_params fdef) with
            | None => infer_err ErrLifetimeConflict  (* 新エラー *)
            | Some σ =>
                (* 3. 引数型を apply_lt_params σ した param 型と比較 *)
                let ps_subst := apply_lt_params σ (fn_params fdef) in
                (* usage check *)
                match check_args_usage arg_tys ps_subst with
                | false => infer_err ErrUsageMismatch
                | true  =>
                    (* 4. σ が caller の region context に収まるか確認 *)
                    let Δ := mk_region_ctx n in
                    if forallb (wf_lifetime_b Δ) σ
                    then infer_ok (apply_lt_ty σ (fn_ret fdef), Γ_out)
                    else infer_err ErrLifetimeLeak
                end
            end
        end
    end
```

**注意**: 現在の `infer_args` は引数の型推論と usage チェックを同時に行っている。
ECall を上記の 2 パス（推論 → unify → check）に変更する必要があるため、
`infer_args` の設計を変更するか、新しい helper を追加する。

---

## 新しいエラー種類

```coq
| ErrLifetimeConflict  (* 同じライフタイム変数に矛盾した割り当て *)
```

OCaml メッセージ: `"lifetime conflict: incompatible lifetime arguments"`

---

## CheckerSoundness.v の変更

### `infer_call_args_sound` の更新

`typed_args fenv n Γ args (fn_params fdef) Γ'` の代わりに
`typed_args fenv n Γ args (apply_lt_params σ (fn_params fdef)) Γ'` を使うように更新。

### `infer_sound` ECall case の更新

`T_Call_Lt` を使って証明を構築:
1. `infer_lt_subst` が `Some σ` を返すとき、対応する `T_Call_Lt` の前提を充足することを示す。
2. `forallb (wf_lifetime_b Δ) σ = true` から `forall l, In l σ → wf_lifetime_b Δ l = true` を導く。
3. `apply_lt_ty σ (fn_ret fdef)` が正しい型として返ることを示す。

---

## AlphaRenaming.v の変更

`apply_lt_ty` と alpha renaming が可換であることを証明する補題が必要な可能性がある:

```coq
Lemma apply_lt_ty_alpha_rename :
  forall σ old new T,
  apply_lt_ty σ (rename_ty old new T) =
  rename_ty old new (apply_lt_ty σ T).
```

（実装中に必要性を確認する）

---

## CheckerUsageSoundness.v の変更

`T_Call` の使用箇所を `T_Call_Lt` に更新する。
`apply_lt_ty` が usage を変えないことを証明する補題が必要:

```coq
Lemma apply_lt_ty_usage : forall σ T,
  ty_usage (apply_lt_ty σ T) = ty_usage T.
```

---

## BorrowCheckSoundness.v

`borrow_ok` は `typed` を直接使わないため変更不要。
ただし `T_Call_Lt` 変更後に `borrow_ok_typed_compatible` の依存関係を確認する。

---

## OCaml フロントエンドの変更

### `main.ml`
`ErrLifetimeConflict` のエラーメッセージを追加:

```ocaml
| ErrLifetimeConflict ->
    "lifetime conflict: incompatible lifetime arguments at call site"
```

### `fir.ml`
`infer_core` の呼び出しシグネチャは変わらない（`fenv n ctx e`）ため変更なし。

---

## テスト追加

### `tests/valid/lifetime/`

#### `call_second_lifetime.facet` — 2番目のライフタイムで多相関数を呼ぶ

```facet
fn pass_through<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}

fn call_with_b<'a, 'b>(
    x: unrestricted &'a unrestricted isize,
    y: unrestricted &'b unrestricted isize
) -> unrestricted &'b unrestricted isize {
    pass_through(y)
}
```

#### `call_static.facet` — LStatic lifetime で多相関数を呼ぶ

（static reference が実装された場合に追加）

#### `chain_lifetime_calls.facet` — 多相呼び出しの連鎖

```facet
fn id<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}

fn double_id<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    id(id(r))
}
```

### `tests/invalid/lifetime/`

#### `lifetime_conflict.facet` — 同一 LVar に異なるライフタイムを割り当て

（この状況が起きる具体的な文法が確定したら追加）

---

## 実装優先順位

1. `apply_lt_lifetime`, `apply_lt_ty`, `apply_lt_params` の定義（TypeChecker.v）
2. `lt_subst_vec`, `unify_lt_ty`, `infer_lt_subst` の定義
3. `T_Call_Lt` の追加（TypingRules.v）、旧 `T_Call` を削除
4. `infer_core` ECall case の更新（TypeChecker.v）
5. `CheckerSoundness.v` の更新（ECall proof, T_Call_Lt 対応）
6. `CheckerUsageSoundness.v` の更新
7. `AlphaRenaming.v` の更新（必要な場合）
8. OCaml: `ErrLifetimeConflict` 追加（main.ml）
9. テスト追加と全テスト通過確認
10. 全 Rocq ビルド + `dune build` 確認

---

## 既知の制限（v7 以降）

| 制限 | 内容 |
|------|------|
| Outlives 制約 | `'a : 'b` (a が b より長く生きる) を型システムに組み込む |
| Lifetime subtyping | `&'a T <: &'b T` when `'a : 'b` |
| Lifetime elision | `fn f(r: &isize) -> &isize` の lifetime を文脈から自動補完 |
| Higher-rank lifetimes | `for<'a> fn(&'a T) -> &'a T` 相当 |
| `EDeref (EDeref ...)` chain | 二重 deref 時のフリーズチェック |
| `PDeref (PDeref ...)` depth ≥ 2 | 引き続き `ErrNotImplemented` |
