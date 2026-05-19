# Closure の設計

## Surface Syntax

明示的な capture list を持つ。

```facet
let y: unrestricted isize = 1 in
let f = closure [y](x: unrestricted isize) -> unrestricted isize {
    y
} in
(f 1)
```

このyは、closure内でキャプチャされる変数である。
MoveかCopyかは、yの型とusageによって決まる。

- yがlinear/affineな場合はmoveされる
- yがunrestrictedな場合はコピーされる
- yがimmutableな参照の場合はコピーされる (immutableな参照は、unrestrictedなため)
- yがmutableな参照の場合はmoveされる (mutableな参照は、affineなため)

参照変数のキャプチャ用に、以下の記法も導入する。

```
closure [&n]() -> ...
closure [&mut n]() -> ...
```

ただし、parserは、capture syntax を AST に保持するだけで、
elaborator/checkerが borrow capture を reference-valued capture に変換する。

## Variable Capture

### Move/Copy Semantics

#### Linear Types

Linear Typesの値がclosure内でキャプチャされる場合、その値はclosureのenvにmoveされ、closureはその値を所有する。
Linear Typesの値をキャプチャする場合、そのclosure自体のusageは、linearでなければならない (usage polymorphic)。

これらの値への有効な参照が残っている場合はmove不可。

#### Affine Types

Affine Typesの値がclosure内でキャプチャされる場合、その値はclosureのenvにmoveされ、closureはその値を所有する。
Affine Typesの値をキャプチャする場合、そのclosure自体のusageは、affine or linearでなければならない (usage polymorphic)。

これらの値への有効な参照が残っている場合はmove不可。

#### Unrestricted Types

Unrestricted Typesの値がclosure内でキャプチャされる場合、その値はclosureのenvにコピーされる。
Unrestricted Typesの値をキャプチャする場合、そのclosure自体のusageは、何でもよい (usage polymorphic)。

### Reference Types

1. closure type に env lifetime を持たせる

closure<'env>(Args) -> Ret

制約:

all captured references outlive 'env
closure value may live only within 'env

2. surface syntaxでは lifetime を省略し、checker/elaborator が env lifetime を作る

let c = closure [r](x: T) -> U { ... }

内部的には:

c : closure<'env>(T) -> U
'a : 'env

のように扱う。

### Mutable and Immutable Captures

### Unrestricted Captures

#### Mutable Unrestricted Captures

MutableなUnrestrictedのキャプチャ変数は、closure内で、replace、assign可能。
何度もClosureを呼び出せるため、MutableなUnrestrictedのキャプチャ変数を持つClosureは、
そのClosure自体もmutableでなければならない。

キャプチャ変数が更新された場合、そのClosureのenvに保存されている値も更新される。

```facet
let mut n = 0 in
let mut f = closure [n]() -> unrestricted isize {
    (n = (+ n 1)); // nを更新, +はまだ未定義だが、存在すると仮定
    n
} in
(f); // return 1
(f)  // return 2
```

copy capture された unrestricted 変数を closure 内で更新しても、外側の元変数は更新されない。
更新されるのは closure env 内の captured slot である。

外側も更新したい場合は、&mut n を capture する

#### Immutable Unrestricted Captures

ImmutableなUnrestrictedのキャプチャ変数は、closure内で、replace、assign不可。
Closure自体は、Immutable/Mutableどちらでもよい。

### Reference-Valued Captures

#### Mutable Reference-Valued Captures

キャプチャしたMutable参照経由で値を更新する場合、そのClosureはmutableでなければならない。

#### Immutable Reference-Valued Captures

キャプチャしたImmutable参照経由で値を更新することはできない。

### Linear/Affine Captures

MutableなLinear/Affineのキャプチャ変数は、closure内で、replace、assign可能。
しかし、moveしているため、外側からはアクセスできない。

## Core Representation

```
surface:
  closure [x, y](args) -> ret { body }

core:
  EMakeClosure closure_id captures
```

lambda lifting

```
surface:
  closure [x, y](a: A) -> R { body }

elaborated synthetic fn:
  fn __closure_N captures (x: X, y: Y) params (a: A) -> R { body }
```

Capture parameters are represented separately from ordinary function
parameters:

```
fn_captures __closure_N = [x: X, y: Y]
fn_params   __closure_N = [a: A]
```

`fn_params` remains the public call interface. Direct `ECall` and `EFn` are
empty-capture only; captured functions are materialized by `EMakeClosure`.
`Eval_CallExpr` combines the captured frame and ordinary argument frame
internally, then hides/removes both internal frames from the caller-visible
result store for immutable Stage 7a calls.

## Closure Types

```
unrestricted closure<'env>(A) -> B
affine closure<'env>(A) -> B
linear closure<'env>(A) -> B
```

## call syntax

通常の関数呼び出しと同じ構文を使う。

```
(f 1)
```

## Rustとの比較

Facet では Fn / FnMut / FnOnce を Rust 風の独立 trait/kind として入れなくても、既存のmutability + usage で自然に表現できる。

```
Fn
  = closure value を immutable に呼べる
  = env を更新しない
  = closure usage は unrestricted/affine/linear の型規則に従う

FnMut
  = closure place が mutable のときだけ呼べる
  = env slot を assign/replace できる
  = 呼び出し後、更新後 env が closure value に書き戻される

FnOnce
  = closure value を move して呼ぶ
  = call が closure を消費する
  = linear/affine capture を消費できる
```

- immutable call:
  callee is read as an immutable value;
  captured env must not be mutated or consumed.
- mutable call:
  callee must be a mutable place;
  captured env may be updated;
  updated env is written back to the closure place.
- consuming call:
  callee is moved;
  captured env may be consumed;
  closure cannot be used after the call.

よって、Rust の Fn/FnMut/FnOnce に相当する区別は、新しい closure kind としては導入しない。
Facet では以下で表現する。

- call receiver の mutability
- closure value の usage
- captured env に対する read/update/move の可否
