結論から言うと、**Borrowing 規則**は、

> **不変参照は共有可、可変参照は排他。re-borrow は「親参照から一時的に子参照を作り、親の権限を一時停止する」規則。**

というもの。まあ、ここを雑に理解すると Rust にボコられる。

---

## 1. 要点

### 通常の borrowing

```rust
&T      // shared borrow / immutable borrow
&mut T  // mutable borrow / exclusive borrow
```

基本規則：

```text
1. &T は複数同時に存在できる
2. &mut T は同時に1つだけ
3. &mut T が有効な間、他の &T / &mut T は共存できない
4. 参照は参照先より長く生きてはいけない
```

要するに：

```text
shared read  : many
exclusive write : one
dangling reference : forbidden
```

---

## re-borrow の要点

**re-borrow** は、すでにある参照からさらに参照を作ること。

```rust
let r  = &mut x;
let rr = &mut *r;  // re-borrow
```

重要なのは、`rr` が有効な間、親の `r` は自由に使えないこと。

```text
親 &mut から 子 &mut を作る:
    子が有効な間、親 &mut は一時停止する

親 &mut から 子 &T を作る:
    子 &T が有効な間、親 &mut の書き込み権限は凍結される

親 &T から 子 &T は作れる:
    共有読み取りなので問題なし

親 &T から 子 &mut T は作れない:
    読み取り権限から書き込み権限は作れない
```

つまり、

> **re-borrow は親参照の権限を子参照に一時的に貸し出す操作。子が生きている間、親は衝突する使い方をできない。**

---

## 2. 形式的定義

値または場所 `x` について、時刻 `t` に有効な参照数を次のように定義する。

```text
S(x, t) = x への有効な shared borrow の数
M(x, t) = x への有効な mutable borrow の数
```

通常の borrowing が正しい条件：

```text
M(x, t) ∈ {0, 1}

M(x, t) = 1 => S(x, t) = 0

S(x, t) > 0 => M(x, t) = 0
```

つまり許される状態はこの2種類だけ。

```text
S(x, t) >= 0, M(x, t) = 0
```

または

```text
S(x, t) = 0, M(x, t) = 1
```

参照 `r` が `x` を指すなら、生存期間はこう。

```text
lifetime(r) ⊆ lifetime(x)
```

参照は、参照先より長く生きてはいけない。

---

## re-borrow の形式的定義

親参照 `p` から子参照 `c` を作るとする。

```text
c = reborrow(p)
```

このとき必要条件は：

```text
lifetime(c) ⊆ lifetime(p)
```

つまり、子参照は親参照より長く生きられない。

権限関係はこう。

```text
&T      から &T      は作れる
&T      から &mut T  は作れない
&mut T から &T      は作れる
&mut T から &mut T  は作れる
```

ただし、`&mut T` から re-borrow した場合：

```text
child が有効な間、
parent の conflicting access は禁止
```

具体的には：

```text
parent: &mut T
child : &mut T

=> child が有効な間、parent は読み書き不可
```

```text
parent: &mut T
child : &T

=> child が有効な間、parent は書き込み不可
```

---

## 3. Valid / Invalid な pseudo code

## Valid: shared borrow は複数可

```rust
let x = 10;

let a = &x;
let b = &x;

print(a);
print(b);
```

状態：

```text
S(x) = 2
M(x) = 0
```

読み取りだけなので有効。

---

## Valid: mutable borrow は1つだけなら可

```rust
let mut x = 10;

let a = &mut x;
*a = 20;

print(a);
```

状態：

```text
S(x) = 0
M(x) = 1
```

書き込み権限を `a` が独占している。

---

## Invalid: shared と mutable の同時存在

```rust
let mut x = 10;

let a = &x;
let b = &mut x;   // invalid

print(a);
```

状態：

```text
S(x) = 1
M(x) = 1
```

読んでいる最中に書くな、という話。そんなに難しくないでしょ。

---

## Invalid: mutable borrow が2つ

```rust
let mut x = 10;

let a = &mut x;
let b = &mut x;   // invalid

*a = 20;
*b = 30;
```

状態：

```text
M(x) = 2
```

排他的であるべき書き込み権限が2つあるため無効。

---

## Valid: `&mut` から `&mut` へ re-borrow

```rust
let mut x = 10;

let r = &mut x;

{
    let rr = &mut *r;  // re-borrow
    *rr = 20;
}   // rr ends here

*r = 30;              // valid
```

`rr` が有効な間、親の `r` は一時停止する。
`rr` が終わった後、`r` はまた使える。

---

## Invalid: mutable re-borrow 中に親を使う

```rust
let mut x = 10;

let r = &mut x;
let rr = &mut *r;

*r = 20;      // invalid
print(rr);
```

理由：

```text
rr が &mut として x を排他的に借用中
=> 親 r から x を変更できない
```

`rr` が子として独占しているのに、親が横から書くのはダメ。親子関係でも容赦ないわね。

---

## Valid: `&mut` から shared re-borrow

```rust
let mut x = 10;

let r = &mut x;

let s = &*r;      // shared re-borrow
print(s);         // s の最後の使用

*r = 20;          // valid
```

`s` が使い終わった後なら、親の `r` で再び書ける。

---

## Invalid: shared re-borrow 中に親 `&mut` で書く

```rust
let mut x = 10;

let r = &mut x;

let s = &*r;      // shared re-borrow

*r = 20;          // invalid
print(s);
```

理由：

```text
s: shared borrow が有効
r: mutable access しようとしている
```

読み取り参照 `s` がまだ生きているので、`r` から書き換えられない。

---

## Valid: `&T` から `&T` へ re-borrow

```rust
let x = 10;

let r = &x;
let s = &*r;

print(r);
print(s);
```

共有参照から共有参照を作るだけなので有効。

---

## Invalid: `&T` から `&mut T` を作る

```rust
let mut x = 10;

let r = &x;
let s = &mut *r;   // invalid
```

理由：

```text
parent: &T
child : &mut T
```

読み取り権限しかない親から、書き込み権限を持つ子は作れない。権限昇格は禁止。

---

## Invalid: 参照先が先に死ぬ

```rust
let r;

{
    let x = 10;
    r = &x;
}   // x is dropped

print(r);  // invalid
```

理由：

```text
lifetime(r) ⊄ lifetime(x)
```

`x` が消えた後に `r` が残るので dangling reference。

---

## まとめ

```text
&T:
    複数可
    読み取り専用

&mut T:
    1つだけ
    排他的
    読み書き可能

re-borrow:
    親参照から子参照を作る
    lifetime(child) ⊆ lifetime(parent)
    子が有効な間、親の衝突する操作は禁止

&mut -> &mut:
    親は一時停止

&mut -> &T:
    親の書き込み権限は一時凍結

&T -> &T:
    可

&T -> &mut:
    不可
```

一言でまとめるなら：

> **Borrowing は「共有読み取り」と「排他的書き込み」の静的制御。re-borrow は、その権限を親参照から子参照へ一時的に貸し出す仕組み。**
