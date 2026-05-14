# Review: Git commit 80056fa093357f04c447f108a6849f6449b0f68d

**型システムの健全性に刺さる穴**がいくつかある。

## 1. borrow 中の元の place を move できる

かなり危険。

`borrow_check_env` は `EReplace` / `EAssign` / `EBorrow` / 一部 `EDeref` だけを borrow state と照合していて、**`EVar` / `EPlace` による通常の move/read を見ていない**。最後は `_ -> Infer_ok pBS` で素通ししている。

該当箇所:

* `fixtures/TypeChecker.ml:3064-3152`
* 特に `EReplace` / `EAssign` / `EBorrow` だけが conflict を見る: `3109-3130`
* `EVar` / `EPlace` は `3152` の default に落ちる
* move 自体は `consume_place_value` で起きる: `2541-2546`

たとえば、規則上はこういうものを拒否する場所が見えない。

```facet
fn bad(mut x: linear isize, y: linear isize) -> unrestricted () {
    let r: affine &mut linear isize = (&mut x);
    let stolen: linear isize = x;
    let old: linear isize = (replace *r y);
    (drop stolen);
    (drop old)
}
```

`r` は `x` を指しているのに、その後 `x` を move できてしまう。さらに `replace *r y` で、すでに move 済みの場所から old を取り出す形になる。これは linearity 的にまずい。

修正方針は単純で、`EVar` / `EPlace` の消費時にも active borrow と照合するべき。少なくとも、

* conflicting shared borrow があるなら move 禁止
* conflicting unique borrow があるなら read/move 禁止
* unrestricted copy だけをどう扱うかは仕様で明確化

が必要。

## 2. inner `let` からローカル参照が脱出できる

これも大きい。

`EBorrow` はローカル borrow に一律 `LVar n` を付ける。だが `let` のスコープごとの lifetime を持っていないので、内側の変数への参照が外側に出られる。

該当箇所:

* `EBorrow` が `LVar n` を返す: `fixtures/TypeChecker.ml:2847-2864`
* `ELet` / `ELetInfer` は body の型 `T2` をそのまま返し、束縛変数を `ctx_remove` するだけ: `2587-2613`
* 関数末尾でしか `wf_type_b` を見ない: `2961-2981`
* borrow checker の `ELet` は initializer 側の borrow だけを後で remove しており、body から返る参照の escape を止めない: `3065-3079`

たとえばこれは dangling reference になるはず。

```facet
fn bad() -> unrestricted isize {
    let r = let x = 1 in (&x);
    (*r)
}
```

内側の `x` は死んでいるのに、`r` は外側で使える。
関数の最終戻り値は `isize` なので、`ErrLifetimeLeak` にも引っかからない。

修正するなら、`LVar n` みたいな関数単位の「雑な local lifetime」では足りない。`let` ごとに fresh region を切るか、少なくとも `let x = ... in e2` の境界で「`x` に由来する参照を返していない」ことを検査する必要がある。

## 3. linear struct の partial move が甘い

現在の `sctx_check_ok` は、linear binding について

```ocaml
st.st_consumed || path_conflicts_any_b [] st.st_moved_paths
```

を見ている。`[]` は全 path の prefix なので、**任意の field を 1 つ move しただけで親 linear 値が消費済み扱い**になる。

該当箇所:

* `path_prefix_b [] _ = true`: `fixtures/TypeChecker.ml:877-888`
* field move は `st_moved_paths` に path を追加: `920-925`
* linear の OK 判定: `2413-2420`

なので、こういうものが通る危険がある。

```facet
struct Pair {
    a: linear isize,
    b: linear isize
}

fn bad(p: linear Pair) -> unrestricted () {
    let a: linear isize = p.a;
    (drop a)
}
```

`p.b` が linear なのに消費されていない。
「field を 1 つ move したら親はもう使えない」という制約と、「残りの linear field も消費義務がある」という制約は別物。ここを混ぜると linearity が崩れる。

修正方針としては、型に基づいて residual obligation を計算する必要がある。つまり、親 `p` の linear 成分のうち、どの field path が消費済みかを追跡し、全 linear component が消費されたときだけ OK にする。

## 4. `replace p e_new` の `e_new` が `p` 自身を使える

`EReplace` は target の型を見たあと、**同じ context で `e_new` を評価し、その後 target path を restore** している。

該当箇所:

* `EReplace`: `fixtures/TypeChecker.ml:2775-2809`
* restore: `2446-2452`
* `state_restore_path`: `929-931`
* borrow checker 側も `e_new` 評価中に target を conflict として扱わない: `3109-3113`

これにより、field replace で自己参照的な move ができる危険がある。

```facet
struct One {
    a: linear isize
}

fn bad(mut s: linear One) -> unrestricted () {
    let old: linear isize = (replace s.a s.a);
    (drop old);
    (drop s)
}
```

`e_new` として `s.a` を move し、その後 `replace` が `s.a` を restored 扱いにする。実行意味論上は old と new が同じ linear resource を指す形になり得る。嫌な匂いどころか、線形型としては事故物件ね。

修正は、`replace p e_new` の `e_new` を検査する間、`p` と conflict する path を unavailable にすること。兄弟 field は許可してよいが、同一 path / prefix 関係は拒否すべき。

## 5. `&mut T` の中身が covariant になっている

`ty_compatible_b_fuel` の `TRef` ケースでは、shared / unique の区別なく inner type に `ty_compatible_b_fuel` を再帰適用している。

該当箇所:

* `fixtures/TypeChecker.ml:1885-1897`

つまり `&mut unrestricted isize` を `&mut affine isize` として渡せる方向がある。`&mut` は書き込みができるので、inner type は基本的に **invariant** にしないと危ない。

今のままだと、関数側が `&mut affine T` だと思って affine 値を書き込むが、呼び出し側は同じ場所を `unrestricted T` として扱う、という型の食い違いが起きる。

修正方針:

```text
&shared T:  T は covariant でもよい
&mut T:     T は invariant、少なくとも usage/core/lifetime を厳密一致
```

unique ref の lifetime 自体は共変でよい場合が多いが、referent type は雑に互換性で流してはいけない。

## 6. struct field の mutability が保存されているのに検査されていない

これは仕様とのズレがはっきりしている。

`field_def` には `field_mutability` があるし、`plan/struct.md` でも「field ごとの mut と binding 側の `let mut` の両方必要」と書かれている。なのに実装では、`EAssign` / `EReplace` が root binding の mutability だけを見ている。

該当箇所:

* field 定義には mutability がある: `fixtures/TypeChecker.ml:949-950`
* field lookup は型だけ返す: `2456-2521`
* assign / replace は root の `sctx_lookup_mut x` だけを見る: `2775-2845`

つまりこういうものが通る危険がある。

```facet
struct S {
    x: unrestricted isize
}

fn bad() -> unrestricted () {
    let mut s: unrestricted S = S { x = 1 };
    (s.x = 2)
}
```

`x` は field として immutable のはずなのに、親 binding が mutable なら更新できてしまう。

修正方針は、place から field path をたどるときに、最後の field だけでなく path 上の field mutability を確認すること。少なくとも assignment / replace target の final field は `MMutable` 必須。

## 7. local annotation の lifetime elision が `LVar 0` 固定

`lower_named_ty_core` の `NTRef None` は常に `LVar 0` に落ちる。

該当箇所:

* `ocaml/debruijn.ml:72-78`

これは signature 用の elision とは別物。関数引数・戻り値には `lower_input_ty` / `lower_output_ty` があるが、local let annotation や struct field などの通常 `ty` では、elided lifetime が雑に `LVar 0` になる。

問題は二つ。

まず、関数 lifetime がない場所では `LVar 0` は well-formed ではないのに、local annotation では検証されにくい。次に、`fn f<'a>(...)` の中では local の `&T` が暗黙に `'a` 扱いされるような挙動になる。

たとえばローカル borrow の注釈が、関数 lifetime の有無で挙動を変える可能性がある。

```facet
fn f<'a>(x: unrestricted isize) -> unrestricted isize {
    let r: unrestricted &unrestricted isize = (&x);
    (*r)
}
```

ここで local `&` を `'a` と見るのはかなり怪しい。local type annotation の elision は、明示的に禁止するか、fresh local region を導入するべき。

## 8. generic trait がかなり形だけ

`trait_def` には `trait_type_params` があるが、bound checking 側では trait args がほぼ使われていない。

該当箇所:

* `trait_def` は type params を持つ: `fixtures/TypeChecker.ml:961-963`
* `trait_impl_error` は常に `matching_impls trait_name [] for_ty`: `2052-2054`
* parser の trait bound は `T: Trait` だけで `Trait<...>` を受け取れない: `ocaml/parser.mly:133-135`
* `validate_impl` も trait arity をチェックしていない: `ocaml/debruijn.ml:367-375`

なので、generic trait は構文上存在しても、意味論としてはかなり未完成。少なくとも以下を入れるべき。

* impl の trait args 数が trait 定義と一致するか
* bound 側で `Trait<Args...>` を書けるか
* trait 自身の bounds を impl / use 時に反映するか

## 優先度

私ならこの順で直す。

1. **borrow 中の元 place の move/read 検査**
2. **local borrow の let-scope escape 防止**
3. **linear struct の field obligation**
4. **replace target と `e_new` の conflict 検査**
5. **`&mut` inner type の invariance**
6. **field mutability 検査**
7. local annotation の lifetime elision 整理
8. generic trait の arity/bounds 整備

現状はテストがかなり増えていて見た目は頼もしいけれど、テストが主に「borrow 作成同士の conflict」「assign/replace conflict」「戻り値 lifetime leak」に寄っている。**move/read と borrow state の相互作用**、**let 境界での参照 escape**、**linear aggregate の残余義務**がまだ薄い。そこを追加しないと、型システムとしては少し甘いわね。仕方ない、でもここまで来ているなら直せる範囲よ。
