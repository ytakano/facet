# Simple Lifetime — v0 実装要件

## 概要

`plan/simple_lifetime_and_borowwing/lifetime.md` の「最小 lifetime 基盤」（Step 1–3）を実装する。
Borrowing 規則（Step 6–8）はこの v0 の**スコープ外**。

---

## Goal

- `lifetime` 型と `outlives` 関係を Rocq で定義する
- `TRef` に lifetime パラメータを追加する（`&'a T` / `&'a mut T`）
- 型の well-formedness 判断 `Δ ⊢ T wellformed` を定義する
- 既存のビルドが通ることを確認する
- OCaml parser は静的 lifetime (`LStatic`) をデフォルトとして使用する

## Non-goals（スコープ外）

- Borrow 式の構文（`&x`, `&mut x`, `*x`）を Syntax.v に追加する
- TypingRules.v への借用型付け規則の追加
- BorrowState の定義・実装
- Re-borrow 規則
- safety theorem（preservation / progress / aliasing safety）
- OCaml パーサーへの明示的な lifetime 注釈構文（`'a` トークン）

---

## 実装コンポーネント

### 1. `Lifetime.v`（新規ファイル）

#### 1.1 lifetime 型

```coq
Inductive lifetime : Type :=
| LStatic         (* 静的 lifetime：全 lifetime を包含する *)
| LVar : nat -> lifetime.  (* 名前付き lifetime（番号で表現）*)
```

OCaml 抽出時に扱いやすいよう具体的な inductive 定義を使う（`Parameter` ではなく）。

#### 1.2 lifetime の等値判定

```coq
Definition lifetime_eqb (l1 l2 : lifetime) : bool :=
  match l1, l2 with
  | LStatic,  LStatic  => true
  | LVar n1, LVar n2   => Nat.eqb n1 n2
  | _, _               => false
  end.

Lemma lifetime_eqb_eq : forall l1 l2,
  lifetime_eqb l1 l2 = true <-> l1 = l2.
```

#### 1.3 region context

```coq
Definition region_ctx := list lifetime.
```

#### 1.4 outlives 関係

`outlives a b` は「lifetime `a` は `b` より長く生きる（`a` が `b` を包含する）」を意味する。

```coq
Inductive outlives : lifetime -> lifetime -> Prop :=
| Outlives_refl  : forall a,   outlives a a
| Outlives_trans : forall a b c,
    outlives a b -> outlives b c -> outlives a c
| Outlives_static : forall a,  outlives LStatic a.
```

記法：`'a : 'b` は `outlives a b` に対応。

#### 1.5 lifetime の well-formedness

```coq
Inductive wf_lifetime (Δ : region_ctx) : lifetime -> Prop :=
| WF_LStatic : wf_lifetime Δ LStatic
| WF_LVar    : forall n, In (LVar n) Δ -> wf_lifetime Δ (LVar n).
```

---

### 2. `Types.v` 修正

#### 2.1 TRef へ lifetime パラメータを追加

```coq
(* 変更前 *)
| TRef : ref_kind -> A -> TypeCore A.

(* 変更後 *)
| TRef : lifetime -> ref_kind -> A -> TypeCore A.
```

`From Facet.TypeSystem Require Import Lifetime.` を追加する。

---

### 3. `WFType.v`（新規ファイル）

型の well-formedness 判断を定義する。

```coq
From Facet.TypeSystem Require Import Lifetime Types.

Inductive wf_type (Δ : region_ctx) : Ty -> Prop :=
| WF_Units    : forall u,   wf_type Δ (MkTy u TUnits)
| WF_Integers : forall u,   wf_type Δ (MkTy u TIntegers)
| WF_Floats   : forall u,   wf_type Δ (MkTy u TFloats)
| WF_Booleans : forall u,   wf_type Δ (MkTy u TBooleans)
| WF_Named    : forall u s, wf_type Δ (MkTy u (TNamed s))
| WF_Fn       : forall u params ret,
    Forall (wf_type Δ) params ->
    wf_type Δ ret ->
    wf_type Δ (MkTy u (TFn params ret))
| WF_Ref      : forall u l rk T,
    wf_lifetime Δ l ->
    wf_type Δ T ->
    wf_type Δ (MkTy u (TRef l rk T)).
```

---

### 4. `TypeChecker.v` 修正

- `From Facet.TypeSystem Require Import Lifetime` を追加（または Types 経由で取得）
- `ty_eqb` と `ty_core_eqb` の TRef ケースを更新：

  ```coq
  (* 変更前 *)
  | TRef k1 t1, TRef k2 t2 => ref_kind_eqb k1 k2 && ty_eqb t1 t2

  (* 変更後 *)
  | TRef l1 k1 t1, TRef l2 k2 t2 =>
      lifetime_eqb l1 l2 && ref_kind_eqb k1 k2 && ty_eqb t1 t2
  ```

- `ty_depth` の TRef ケースを更新：

  ```coq
  (* 変更前 *)
  | TRef _ t => S (ty_depth t)

  (* 変更後 *)
  | TRef _ _ t => S (ty_depth t)
  ```

- `free_vars_expr` / `alpha_rename_expr` 内のパターンは `TRef` を直接触らないので原則不変。
  ただし `rename_ty` 等があれば確認要。

---

### 5. `CheckerSoundness.v` 修正

- `ref_kind_eqb_true` 証明はそのまま
- `ty_eqb_correct` と `ty_core_eqb_true` の TRef ケースを更新（lifetime_eqb_eq を使用）

---

### 6. `AlphaRenaming.v` 修正

- TRef のパターンマッチが `TRef _ t` → `TRef _ _ t` に変わる箇所を更新
- 内容は `TRef` を直接構築しないため影響は最小

---

### 7. `CheckerUsageSoundness.v` 修正

- TRef パターン（`TRef _ t`）を `TRef _ _ t` に更新

---

### 8. OCaml パーサー修正

`parser.mly` の型ルールで `TRef` に `LStatic` を補う：

```ocaml
(* 変更前 *)
| AMP; t = ty { TRef (RShared, t) }
| AMP; KW_MUT; t = ty { TRef (RUnique, t) }

(* 変更後 *)
| AMP; t = ty { TRef (LStatic, RShared, t) }
| AMP; KW_MUT; t = ty { TRef (LStatic, RUnique, t) }
```

明示的な lifetime 注釈（`& 'a T`）は v0 の対象外。

---

### 9. `_CoqProject` 更新

新ファイルを追加し、コンパイル順を正しく設定する：

```
-R theories Facet
theories/TypeSystem/Lifetime.v      ← 新規（Types.v より前）
theories/TypeSystem/Types.v
theories/TypeSystem/Syntax.v
theories/TypeSystem/OperationalSemantics.v
theories/TypeSystem/TypingRules.v
theories/TypeSystem/TypeChecker.v
theories/TypeSystem/WFType.v        ← 新規（TypeChecker.v の後）
theories/TypeSystem/AlphaRenaming.v
theories/TypeSystem/CheckerSoundness.v
theories/TypeSystem/CheckerUsageSoundness.v
```

---

## 影響範囲まとめ

| ファイル | 変更内容 | 重さ |
|---------|---------|------|
| `Lifetime.v` | 新規作成 | 中 |
| `WFType.v` | 新規作成 | 小 |
| `Types.v` | TRef に lifetime 追加、Lifetime import | 小 |
| `TypeChecker.v` | ty_eqb/ty_core_eqb/ty_depth の TRef ケース更新 | 小 |
| `CheckerSoundness.v` | ty_core_eqb_true TRef ケース更新 | 小 |
| `AlphaRenaming.v` | TRef パターン `_ _` → `_ _ _` 更新 | 小 |
| `CheckerUsageSoundness.v` | TRef パターン更新 | 小 |
| `ocaml/parser.mly` | TRef に LStatic 補完 | 小 |
| `rocq/_CoqProject` | Lifetime.v, WFType.v 追加 | 小 |
| `fixtures/TypeChecker.ml` | make による自動再生成 | 自動 |

---

## 検証基準

1. `cd rocq && make` が全ファイルエラーなしでコンパイルされる
2. `dune build` が成功する
3. 既存テスト（`tests/valid/**` と `tests/invalid/**`）が引き続き合格する
4. `WFType.v` が `&unrestricted isize` 型に対して `wf_type [] (MkTy UUnrestricted (TRef LStatic RShared (MkTy UUnrestricted TIntegers)))` を導けることを Example で確認

---

## 今後の拡張（v1 以降）

```
v1: Borrow 式（EBorrow, EDeref）を Syntax.v に追加 + TypingRules に T_Borrow
v2: BorrowState を TypingRules の判断に組み込む
v3: Re-borrow 規則
v4: Safety theorems（no dangling reference, aliasing safety）
```
