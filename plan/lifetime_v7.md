# Lifetime v7: Outlives Constraints と Lifetime Subtyping

## Summary

v6 で `ECall` の lifetime substitution は入ったが、`outlives` はまだ型システムに接続されていない。
v7 では `Lifetime.v` の `outlives` を checker と typing rules に組み込み、`&'a T <: &'b T` when `'a : 'b` を扱う。

主目的は、参照型の lifetime 完全一致を緩めつつ、短い lifetime を長い lifetime として扱う unsound な変換を拒否すること。

---

## Key Changes

### `Lifetime.v`

- `outlives_b : lifetime -> lifetime -> bool` を追加する。
- v7 では最小モデルとして `LStatic : l` と `l : l` のみを true にする。
- 明示的な user-defined outlives constraint list は v7 では導入しない。

### `TypingRules.v`

- `ty_compatible : Ty -> Ty -> Prop` を追加する。
- 非参照型は既存どおり core equality + usage subtyping。
- `TRef la rk Ta` を `TRef lb rk Tb` として使える条件は `outlives la lb` と inner type compatibility。
- `typed_args` は `ty_core = ty_core` の完全一致ではなく `ty_compatible T_e (param_ty p)` を使う。
- `T_Let`, `T_Replace`, `T_Assign`, `T_Replace_Deref`, `T_Assign_Deref`, `infer` の return matching に対応する Prop 側条件も `ty_compatible` に寄せる。

### `TypeChecker.v`

- `ty_compatible_b : Ty -> Ty -> bool` を追加する。
- `check_args` と `infer_core` の annotation/type matching を `ty_core_eqb` 直接比較から `ty_compatible_b` に変更する。
- `build_sigma` / `unify_lt` は lifetime substitution を作る役割に残し、substitution 後の最終チェックで `ty_compatible_b` を使う。
- `ErrLifetimeConflict` は substitution の矛盾、`ErrLifetimeLeak` は region 外 lifetime、既存の `ErrTypeMismatch` は structural mismatch に使い分ける。
- `fn_params` も `wf_type_b (mk_region_ctx (fn_lifetimes f))` で検査する。

### Proofs

- `CheckerSoundness.v` に `ty_compatible_b_sound` を追加し、既存の `ty_core_eqb_true` 使用箇所を置き換える。
- `CheckerUsageSoundness.v` は usage preservation 補題を `ty_compatible` 前提に合わせる。
- `BorrowCheckSoundness.v` は原則変更なし。borrow checker は lifetime subtyping を直接扱わない。

---

## Tests

既存の `tests/valid/lifetime/*.facet` と `tests/invalid/lifetime/*.facet` と同じ形式で、以下のファイルを追加する。

### valid: `tests/valid/lifetime/outlives_same_lifetime_arg.facet`

同じ lifetime の参照を、同じ lifetime を要求する関数に渡せることを確認する。

```facet
fn use_same<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}

fn caller<'a>(x: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    (use_same x)
}
```

### valid: `tests/valid/lifetime/outlives_polymorphic_return.facet`

v6 の lifetime substitution と v7 の compatibility が同時に働いても、同一 lifetime の返却が壊れないことを確認する。

```facet
fn id<'a>(r: unrestricted &'a unrestricted isize) -> unrestricted &'a unrestricted isize {
    r
}

fn caller<'a, 'b>(
    x: unrestricted &'a unrestricted isize,
    y: unrestricted &'b unrestricted isize
) -> unrestricted &'b unrestricted isize {
    (id y)
}
```

### invalid: `tests/invalid/lifetime/outlives_unrelated_return.facet`

v7 の最小 outlives では、`'a` と `'b` は同一でない限り互換ではない。`&'a T` を `&'b T` として返すケースを拒否する。

```facet
fn bad<'a, 'b>(r: unrestricted &'a unrestricted isize) -> unrestricted &'b unrestricted isize {
    r
}
```

### invalid: `tests/invalid/lifetime/outlives_unrelated_arg.facet`

`&'a T` を `&'b T` を要求する関数へ渡すケースを拒否する。

```facet
fn needs_b<'b>(r: unrestricted &'b unrestricted isize) -> unrestricted &'b unrestricted isize {
    r
}

fn bad<'a, 'b>(x: unrestricted &'a unrestricted isize) -> unrestricted &'b unrestricted isize {
    (needs_b x)
}
```

### invalid: `tests/invalid/lifetime/ref_kind_mismatch_arg.facet`

lifetime が一致していても、shared reference を mutable reference として渡せないことを確認する。

```facet
fn needs_mut<'a>(r: unrestricted &'a mut unrestricted isize) -> unrestricted &'a mut unrestricted isize {
    r
}

fn bad<'a>(x: unrestricted &'a unrestricted isize) -> unrestricted &'a mut unrestricted isize {
    (needs_mut x)
}
```

### 注意

現行 parser には `'static` の surface syntax がないため、`LStatic : 'a` の positive case は `.facet` テストでは直接表現できない。
`outlives_b LStatic (LVar n) = true` は Rocq 側の Example または checker helper の単体証明で確認する。

---

## Assumptions

- v7 は明示的な `'a : 'b` 構文や outlives constraint context を追加しない。
- Lifetime elision、higher-rank lifetimes、`PDeref (PDeref ...)`、`EDeref (EDeref ...)` chain は v8 以降に残す。
- Runtime representation は変更しない。`VRef ident` のまま、v7 は静的型検査のみを拡張する。
- OCaml parser は lifetime annotation の既存構文を維持し、v7 では新しい surface syntax を追加しない。
