結論から言うと、**先に lifetime の“最小基盤”を実装して、その上に borrowing 規則を実装すべき**。
ただし、**完全な lifetime 推論まで先に作る必要はない**。そこまでやると沼。Rocq、いや The Rocq Prover は証明支援系で、こういう依存構造を雑に作ると後で自分に刺さるのよ。なお Rocq は Coq から改名された現在の名称として扱っているわ。([Rocq][1])

## 推奨順序

```text
1. lifetime の基盤
2. 型の well-formedness
3. borrowing 規則
4. re-borrow 規則
5. safety theorem
```

## 理由

`borrowing` は `lifetime` に依存する。

たとえば Rust 風に書くと：

```rust
&'a T
&'a mut T
```

この `&'a T` の型付けには、少なくとも次が必要。

```text
'a が現在の環境で有効か
T が well-formed か
参照の lifetime が参照先より長すぎないか
'a : 'b のような outlives 関係をどう扱うか
```

つまり、borrowing 規則は lifetime 情報なしでは定義が不完全になる。

---

## 先に実装すべき lifetime はこれだけでいい

最初から Rust の lifetime inference 全体を実装しなくていい。まずはこれで十分。

```coq
Lifetime
Outlives : Lifetime -> Lifetime -> Prop
```

あるいは有限集合で：

```coq
RegionCtx := list Lifetime
```

型の well-formedness：

```text
Δ ⊢ 'a valid
Δ ⊢ T wellformed
```

参照型：

```text
Δ ⊢ 'a valid
Δ ⊢ T wellformed
-------------------------
Δ ⊢ Ref 'a imm T wellformed

Δ ⊢ 'a valid
Δ ⊢ T wellformed
-------------------------
Δ ⊢ Ref 'a mut T wellformed
```

ここまでが **lifetime の最小基盤**。

---

## borrowing 規則はその後

次に borrow state を入れる。

```text
B = 現在有効な borrow の集合
```

型付け判断は例えばこう。

```text
Γ ; Δ ; B ⊢ e : T ⊣ B'
```

意味：

```text
変数環境 Γ
lifetime 環境 Δ
borrow 状態 B
のもとで e は T 型を持ち、
borrow 状態は B' に変化する
```

不変借用：

```text
Γ(x) = T
Δ ⊢ 'a valid
B allows shared borrow of x
--------------------------------
Γ ; Δ ; B ⊢ & 'a x : Ref 'a imm T ⊣ B ∪ {shared(x, 'a)}
```

可変借用：

```text
Γ(x) = T
Δ ⊢ 'a valid
B allows unique borrow of x
--------------------------------
Γ ; Δ ; B ⊢ & 'a mut x : Ref 'a mut T ⊣ B ∪ {mutable(x, 'a)}
```

ここで `B allows ...` は例の規則：

```text
shared は複数可
mutable は1つだけ
shared と mutable は共存不可
```

---

## re-borrow は borrowing の後

`re-borrow` は通常の borrow より一段複雑。
親参照の権限を一時停止するから。

```rust
let r  = &mut x;
let rr = &mut *r;
```

形式的には：

```text
parent : Ref 'a mut T
'b <= 'a
--------------------------------
reborrow parent as Ref 'b mut T
```

つまり：

```text
lifetime(child) ⊆ lifetime(parent)
```

または outlives 記法なら：

```text
'a : 'b
```

親 `'a` が子 `'b` より長く生きる必要がある。

re-borrow の型付け規則は borrowing と lifetime の両方を使うので、後回しが正解。

---

## 実装順の具体案

おすすめはこれ。

```text
Step 1:
  Lifetime, Outlives, RegionCtx を定義

Step 2:
  Type を定義
    Int
    Bool
    Ref lifetime mutability type

Step 3:
  wellformed type を定義

Step 4:
  place / variable / ownership environment を定義

Step 5:
  BorrowState を定義
    shared loans
    mutable loans

Step 6:
  通常の borrowing 規則を実装

Step 7:
  re-borrow 規則を実装

Step 8:
  preservation / progress / no dangling reference / aliasing safety を証明
```

## 最小モデルならこう

最初の Rocq 実装では、lifetime を具体的な時区間として扱わなくてもいい。

```coq
Parameter lifetime : Type.
Parameter outlives : lifetime -> lifetime -> Prop.
```

そして公理または仮定として：

```coq
outlives_refl  : forall a, outlives a a
outlives_trans : forall a b c,
  outlives a b -> outlives b c -> outlives a c
```

これで `&'a T` と re-borrow の型付け規則を先に組める。

---

## 判断

だから答えは：

> **lifetime を先に実装する。ただし完全な lifetime checker ではなく、borrowing が参照できる最小の lifetime 基盤だけを先に作る。**

順序としては：

```text
minimal lifetime layer
→ borrow typing
→ re-borrow typing
→ lifetime constraints refinement
```

これが一番破綻しにくい。
いきなり borrowing から入るのは、型に `&'a T` と書いておきながら `'a` の意味を後で考える、という雑な設計になる。まあ、研究コードではよくある事故だけどね。

[1]: https://rocq-prover.org/doc/v9.0/refman/changes.html?utm_source=chatgpt.com "Recent changes — The Rocq Prover 9.0.1 documentation"
