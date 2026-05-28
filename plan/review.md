# Review: Git commit db57b9884fb19075954902e65d37f92572aad450
結論から言うと、**AlphaRenaming.v は拡張性がかなり低い**。ただし「未証明が混じっていて危険」というより、**証明責務・補助定理・サイズ測度・構文別の手書き処理が巨大単一ファイルに絡まりすぎて、AST や意味論の追加時に変更面が爆発する**、という種類の問題ね。

---

## 良い点

まず、`rocq/theories/TypeSystem` 配下では `Admitted` / `Axiom` / `Abort` は見当たらなかった。これは素直に良い。証明を穴で押し切っている実装ではなさそう。

また、過去に問題になりやすい箇所はいくつか対策が入っている。

`EVar` / `EPlace` に対して borrow 状態を見ているので、borrow 中の root / place を素通しで読む・動かす古い穴はだいぶ塞がっている。該当箇所は `TypeChecker.v:7301-7310`。

部分 move 済み線形 struct の扱いも、`linear_obligation_paths` と `linear_scope_ok_b` で義務 path を見る形になっている。`TypeChecker.v:3065-3094`。

immutable field assignment も、`writable_place_b` が parent の書き込み可能性と field mutability を見ている。`TypeChecker.v:3234-3274`。

テスト側にも、borrow conflict、lifetime escape、linear struct partial move、replace self-use、generic trait まわりの invalid ケースがかなり入っている。ここは「最新実装でかなり埋めてきた」印象。

---

## 主要な問題点

### 1. `AlphaRenaming.v` が責務を抱えすぎ

`AlphaRenaming.v` は 19,693 行ある。中身は単なる alpha-renaming の補題ではなく、少なくとも次を同居させている。

* `ctx_alpha`
* `place_alpha`
* `expr_alpha`
* executable renamer の soundness
* `expr_size` とサイズ減少補題
* typing preservation
* env structural typing preservation
* root / shadow / provenance 系の補題
* captured call / closure 関連の alpha 補題

さらに `AlphaRenaming.v` は先頭で `TypeChecker` と `EnvStructuralRules` まで import している。`AlphaRenaming.v:1`。つまり、alpha の基礎事実と checker / structural semantics が同じ階層にいる。これは拡張時に依存方向が読みづらい。

特に `expr_size` が `AlphaRenaming.v:1597` 以降に定義されているのに、後続の soundness 系ファイルで広く使われている。サイズ測度は alpha-renaming 固有ではないので、ここに置くべきではない。

**対処方針:**
`AlphaRenaming.v` は互換用の再 export ファイルにして、中身を分割するのがいい。

推奨構成はこう。

```coq
ExprFacts.v
  expr_size
  expr_size_*_lt
  list/fields/branches の基本補題

AlphaCore.v
  rename_env
  lookup_rename
  rename_range
  fresh_ident
  alpha_rename_idents 系の基本補題

AlphaCtx.v
  ctx_alpha
  ctx lookup / add / remove / consume / merge preservation

AlphaPlace.v
  place_alpha
  rename_place soundness

AlphaExpr.v
  expr_alpha
  exprs_alpha
  fields_alpha
  branches_alpha
  alpha_rename_expr_sound

AlphaFn.v
  alpha_rename_params
  alpha_rename_fn_def
  function body / captures / params まわりの補題

AlphaTyping.v
  typed preservation

AlphaEnvStructural.v
  typed_env_structural preservation

AlphaRoots.v
  root_env / root_set alpha 補題

AlphaShadowProvenance.v
  shadow / provenance / captured-call 関連

AlphaRenaming.v
  From Facet.TypeSystem Require Export
    ExprFacts AlphaCore AlphaCtx AlphaPlace AlphaExpr AlphaFn
    AlphaTyping AlphaEnvStructural AlphaRoots AlphaShadowProvenance.
```

既存ファイルは今のまま `Require Import AlphaRenaming` できる。つまり、**外部 API を壊さずに内部だけ分割できる**。コーディングエージェントにもこの形が一番扱いやすい。

---

### 2. `expr_alpha` の `EStruct` / `EMatch` が弱すぎる

ここはかなり重要。

`expr_alpha` は `AlphaRenaming.v:261-337` にあるが、`EStruct` と `EMatch` の定義が緩すぎる。

```coq
| EA_Struct : forall ρ name lts args fields fieldsr,
    expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)
```

`AlphaRenaming.v:298-300`

これだと、field の式が alpha 対応している必要がない。つまり理屈の上では、

```coq
EStruct "S" [] [] [("x", EVar a)]
```

と

```coq
EStruct "S" [] [] [("x", ELit 0)]
```

が alpha-related になり得る。これは alpha 同値としては明らかに強すぎる、というより弱すぎる関係ね。

`EMatch` も同じ。

```coq
| EA_Match : forall ρ scrut scrutr branches branchesr,
    expr_alpha ρ
      (EMatch scrut branches)
      (EMatch scrutr branchesr)
```

`AlphaRenaming.v:305-308`

scrutinee も branch も関係づけていない。

さらに `alpha_rename_expr_sound` 側では、struct / match の枝で実際に再帰処理をしているのに、最後は単に `apply EA_Struct` / `apply EA_Match` している。`AlphaRenaming.v:4705-4758`。つまり executable renamer の精密な挙動を、関係側が受け止めていない。

今のところ `expr_alpha` はほぼ `AlphaRenaming.v` 内部でしか使われていないようなので、即座に外部の theorem を壊すとは限らない。ただし、将来の証明やエージェントがこの relation を「alpha 同値」として使ったら危ない。まったく、将来の自分を撃つタイプの緩さね。

**修正案:**

```coq
Inductive fields_alpha : rename_env -> list (string * expr) -> list (string * expr) -> Prop :=
| FA_Nil : forall ρ,
    fields_alpha ρ [] []
| FA_Cons : forall ρ name e er rest restr,
    expr_alpha ρ e er ->
    fields_alpha ρ rest restr ->
    fields_alpha ρ ((name, e) :: rest) ((name, er) :: restr).

Inductive branches_alpha : rename_env ->
    list (string * list ident * expr) ->
    list (string * list ident * expr) -> Prop :=
| BA_Nil : forall ρ,
    branches_alpha ρ [] []
| BA_Cons : forall ρ variant binders bindersr e er rest restr ρ_branch,
    (* binders と bindersr が ρ_branch を作る、という補助関係を挟む *)
    branch_binders_alpha ρ binders bindersr ρ_branch ->
    expr_alpha ρ_branch e er ->
    branches_alpha ρ rest restr ->
    branches_alpha ρ
      ((variant, binders, e) :: rest)
      ((variant, bindersr, er) :: restr).
```

そして `EA_Struct` / `EA_Match` をこういう形にする。

```coq
| EA_Struct : forall ρ name lts args fields fieldsr,
    fields_alpha ρ fields fieldsr ->
    expr_alpha ρ (EStruct name lts args fields) (EStruct name lts args fieldsr)

| EA_Match : forall ρ scrut scrutr branches branchesr,
    expr_alpha ρ scrut scrutr ->
    branches_alpha ρ branches branchesr ->
    expr_alpha ρ (EMatch scrut branches) (EMatch scrutr branchesr)
```

これで relation が AST の構造を正しく反映する。

---

### 3. `Renaming.v` の traversal が手書きで重複している

`Syntax.v:49-69` の `expr` constructor はそこそこ多い。にもかかわらず、`Renaming.v` では `free_vars_expr` が全 constructor を手書きで見る。`Renaming.v:57-115`。`alpha_rename_expr` も同様に全 constructor を手書きで見る。`Renaming.v:141-268`。

この構造だと、新しい文法を 1 個足すだけで、最低でも次を全部触ることになる。

* `Syntax.v`
* `Renaming.v` の `free_vars_expr`
* `Renaming.v` の `alpha_rename_expr`
* `AlphaRenaming.v` の `expr_alpha`
* `AlphaRenaming.v` の `expr_size`
* `alpha_rename_expr_sound`
* typed preservation
* structural typing preservation
* checker / borrow checker / root checker
* runtime semantics
* readiness / provenance / shadow 系 predicate
* テスト

これはエージェントが壊しやすい。というか人間でも普通に壊す。

**対処方針:**
リスト系 traversal を共通化する。

例えば `Renaming.v` にこういう補助関数を導入する。

```coq
Fixpoint map_accum {A B : Type}
    (f : list ident -> A -> B * list ident)
    (used : list ident)
    (xs : list A)
    : list B * list ident :=
  match xs with
  | [] => ([], used)
  | x :: xs' =>
      let '(y, used1) := f used x in
      let '(ys, used2) := map_accum f used1 xs' in
      (y :: ys, used2)
  end.
```

その上で、

```coq
Definition alpha_rename_exprs ρ :=
  map_accum (fun used e => alpha_rename_expr ρ used e).

Definition alpha_rename_fields ρ :=
  map_accum
    (fun used '(name, e) =>
       let '(er, used') := alpha_rename_expr ρ used e in
       ((name, er), used')).

Definition alpha_rename_payloads ρ := alpha_rename_exprs ρ.
```

`EMatch` の branch は binder scope があるので少し特殊だけど、それでも `alpha_rename_branches` として外に出せる。

これをやると、`alpha_rename_expr_sound` の中にローカル `fix go` が何度も出てくる状態を減らせる。今は `Renaming.v:151-234` と `AlphaRenaming.v:4705-4758` に同型の再帰が散っている。証明の修正範囲が読みにくい。

---

### 4. `free_vars_expr` という名前が危険

`Renaming.v:57-115` の `free_vars_expr` は名前に反して、厳密な自由変数ではない。

たとえば let でこうなっている。

```coq
| ELet _ x _ e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
| ELetInfer _ x e1 e2 => x :: free_vars_expr e1 ++ free_vars_expr e2
```

`Renaming.v:65-66`

束縛変数 `x` を含めている。match branch の binder も body から取り除いていない。alpha-renaming の fresh seed としては、これは「保守的な name collection」として意味がある。だが、`free_vars_expr` という名前のままだと、将来の証明やエージェントが「本当の自由変数」と誤用する。

実際、`TypeSafetyHiddenFrameStrip.v` などでも `free_vars_expr` が使われている。過剰近似なら安全側に倒れることは多いが、`In x (free_vars_expr e)` を意味論的な自由変数として読む補題が増えると危険。

**修正案:**

* 現在の関数は `expr_names` または `expr_name_occurrences` に改名する。
* 本当に必要なら、束縛を除く `free_vars_expr_semantic` を別に作る。
* 既存証明はまず `Definition free_vars_expr := expr_names.` で互換性を残し、段階的に名前を移す。

これは地味だけど、エージェントの誤読防止にはかなり効く。

---

### 5. OCaml CLI が公開 checker endpoint とズレている

`TypeChecker.v` には、かなり強い program-level endpoint が用意されている。

```coq
check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary
```

これは `TypeChecker.v:7988-7995` にある。さらに extraction でも出している。`TypeChecker.v:9315-9340`。

しかし OCaml CLI はそれを acceptance gate として使っていない。`ocaml/main.ml` では、

```ocaml
let env_for_checker = alpha_normalize_global_env env
...
match infer_full_env_roots env_for_checker f r0 with
| Infer_ok ...
| Infer_err ErrNotImplemented ->
    infer_full_env env_for_checker f
```

という流れになっている。`ocaml/main.ml:306-328`。

つまり、CLI は function ごとに `infer_full_env_roots` を試し、`ErrNotImplemented` のときだけ ordinary env checker に fallback している。これは実装上便利なのは分かる。でも、Rocq 側に program-level gate があるなら、CLI の「OK」はその gate と一致しているべき。

特に `infer_full_env_roots_big_step_safe_ready` の theorem は、単に `infer_full_env_roots` が成功しただけではなく、

* `initial_store_for_fn`
* `provenance_ready_expr`
* `store_roots_within`
* `store_no_shadow`
* `root_env_no_shadow`
* `eval`

などの追加前提を持つ。`EnvRuntimeBaseSafety.v:131-140`。CLI コメントでは roots checker が “proven type-safe” と書いているが、そこは少し雑。は？それ本気で言ってるの、とまでは言わないけど、証明の前提を CLI の acceptance と混同すると危ない。

**修正案:**

CLI の acceptance はまず Rocq 側の単一 endpoint に寄せる。

```ocaml
let accepted =
  check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary env
in
if not accepted then exit 1;
```

その後で、診断用に `infer_full_env_roots` を各 function に回す。つまり、

1. program-level gate で受理 / 拒否を決める
2. 詳細エラー表示のために checker を回す
3. FIR emit は gate 成功後だけ許可する

という順番にする。

`ErrNotImplemented` fallback は、少なくとも通常テストでは使わない方がいい。残すなら `--unsafe-ordinary-fallback` のような明示 flag に隔離するべき。

---

### 6. `ELetInfer` の borrow checker が文脈を拡張していない

`ELet` は borrow check 時に body の context に binder を追加している。

```coq
borrow_check_env env PBS1 (ctx_add_b x T m Γ) e2
```

`TypeChecker.v:7388-7395`

一方 `ELetInfer` は、

```coq
borrow_check_env env PBS1 Γ e2
```

になっている。`TypeChecker.v:7398-7405`

つまり、`x` の型が分からないため body の borrow check context に追加していない。OCaml frontend が raw elaboration を必ず通して `ELetInfer` を `ELet` に変換してから checker に渡しているなら、実運用では回避される可能性が高い。`ocaml/debruijn.ml:762-769` で `elaborate_raw_global_env` は通っている。

でも `infer_full_env` / `check_program_env_alpha` は Rocq 側で公開されていて、`ELetInfer` を含む env に直接使える形に見える。ここは API と前提がズレている。

**対処方針:**

* 「borrow checker は elaborated AST のみ受け取る」と明記する。
* 可能なら public endpoint を `*_elab` 系に統一する。
* `infer_full_env` を内部用に寄せ、CLI / agent / docs では `check_program_env_alpha_elab_*` だけを使わせる。

---

### 7. ドキュメントが実装とズレている

`CLAUDE.md` と `.github/copilot-instructions.md` には `--debug-alpha` があると書かれている。

* `CLAUDE.md:48-49`
* `.github/copilot-instructions.md:45-46`

しかし `ocaml/main.ml:249-264` の option parser は `--emit-fir` 以外の未知 option を拒否する。`--debug-alpha` は実装されていない。

これはコーディングエージェントにはかなり悪い。エージェントは docs を信じてテストコマンドを組み立てるので、存在しない flag が書いてあるだけで無駄な修正に走る。

**修正案:**
どちらかに寄せる。

* 本当に必要なら `--debug-alpha` を実装する。
* すぐ実装しないなら docs から削る。

個人的には実装した方がいい。alpha-renaming の差分テストは、このプロジェクトにかなり向いている。

---

## AlphaRenaming.v の拡張性を上げる具体策

最初から全 rewrite すると壊れる。やる順番が大事。

### Phase 0: 振る舞いを変えずに足場を作る

まずは新ファイルだけ追加して、既存 theorem の名前は変えない。

追加候補:

```text
rocq/theories/TypeSystem/ExprFacts.v
rocq/theories/TypeSystem/AlphaCore.v
rocq/theories/TypeSystem/AlphaCtx.v
rocq/theories/TypeSystem/AlphaPlace.v
rocq/theories/TypeSystem/AlphaExpr.v
rocq/theories/TypeSystem/AlphaFn.v
rocq/theories/TypeSystem/AlphaTyping.v
rocq/theories/TypeSystem/AlphaEnvStructural.v
rocq/theories/TypeSystem/AlphaRoots.v
rocq/theories/TypeSystem/AlphaShadowProvenance.v
```

`rocq/_CoqProject` では `AlphaRenaming.v` の直前に並べる。既存 downstream はまだ `AlphaRenaming.v` を import すればよい。

この段階では theorem statement を変えない。単なる移動。退屈だけど、これを飛ばすと地獄を見る。

### Phase 1: `expr_size` を `ExprFacts.v` に移す

`expr_size` は alpha-renaming の概念ではない。`AlphaRenaming.v:1597` から始まる size と `expr_size_*_lt` 補題を `ExprFacts.v` に移す。

これだけでも後続 proof が `AlphaRenaming` 全体に依存しなくて済むケースが出てくる。

### Phase 2: list traversal helper を導入する

`Renaming.v` に `map_accum` 系を入れて、`alpha_rename_expr` の中の local `fix go` を外に出す。

対象はまずこのあたり。

* `ECall`
* `ECallGeneric`
* `ECallExpr`
* `EStruct`
* `EEnum`
* `EMatch`

該当箇所は `Renaming.v:151-234`。

この phase では出力が変わらないことを重視する。エージェントには「関数の意味を変えるな」と強く指示するべき。

### Phase 3: `fields_alpha` / `branches_alpha` を導入する

ここで初めて relation を強化する。

* `EA_Struct` に `fields_alpha` premise を追加
* `EA_Match` に scrutinee と `branches_alpha` premise を追加
* `alpha_rename_expr_sound` の struct / match branch を helper lemma で証明

この変更は theorem が壊れやすいので、Phase 0 / 1 / 2 のあとにやる。

### Phase 4: public checker endpoint を一本化する

OCaml CLI は `check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary` を受理判定に使う。`infer_full_env_roots` は診断用に回す。

この修正は alpha-renaming 本体とは別 PR にする方がいい。証明 refactor と CLI behavior change を混ぜると、失敗したとき原因が見えなくなる。

---

## コーディングエージェントに渡すなら、こう分割する

大きな依頼を一発で投げるのは悪手。エージェントは巨大 proof file を見ると、だいたい力技で壊す。仕方ないわね、依頼テンプレまで書いておく。

### Task 1: 互換分割だけ

```text
目的:
AlphaRenaming.v を意味変更なしで分割する。

制約:
- theorem / lemma / definition の名前と statement を変えない。
- 既存 downstream file の import は壊さない。
- AlphaRenaming.v は Require Export だけの互換 aggregator にする。
- 証明内容の変更は最小限。移動のみ。

対象:
- rocq/theories/TypeSystem/AlphaRenaming.v
- rocq/_CoqProject

新規候補:
- ExprFacts.v
- AlphaCore.v
- AlphaCtx.v
- AlphaPlace.v
- AlphaExpr.v
- AlphaFn.v
- AlphaTyping.v
- AlphaEnvStructural.v
- AlphaRoots.v
- AlphaShadowProvenance.v

確認:
cd rocq && make
rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories
```

### Task 2: `expr_alpha` の struct / match を強化

```text
目的:
expr_alpha の EStruct / EMatch constructor を構造的に正しくする。

制約:
- executable alpha_rename_expr の出力は変えない。
- fields_alpha と branches_alpha を追加する。
- EA_Struct は fields_alpha を要求する。
- EA_Match は scrutinee の expr_alpha と branches_alpha を要求する。
- まず alpha_rename_expr_sound が通ることを目標にする。
- typing preservation など大きな theorem の変更は必要最小限。

対象:
- AlphaExpr.v
- AlphaTyping.v
- AlphaEnvStructural.v
```

### Task 3: traversal helper 導入

```text
目的:
Renaming.v の list traversal 重複を減らす。

制約:
- alpha_rename_expr の意味を変えない。
- map_accum / alpha_rename_exprs / alpha_rename_fields / alpha_rename_payloads / alpha_rename_branches を追加する。
- 既存証明が必要とする unfold しやすさを保つ。
- 変更後も extraction 結果が大きく変わらないようにする。

対象:
- Renaming.v
- AlphaExpr.v
```

### Task 4: CLI acceptance gate 修正

```text
目的:
OCaml CLI の OK 判定を Rocq 側の public program-level checker に合わせる。

制約:
- check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary を受理判定に使う。
- infer_full_env_roots は診断用にのみ使う。
- ErrNotImplemented fallback でプログラムを受理しない。
- --emit-fir は program-level gate 成功後のみ許可する。

対象:
- ocaml/main.ml
- tests/valid
- tests/invalid
- CLAUDE.md
- .github/copilot-instructions.md
```

### Task 5: docs 修正

```text
目的:
エージェントが AST / checker / proof の追加点を見落とさないようにする。

追加:
docs/rocq-extension-guide.md

内容:
新しい expr constructor を追加するときのチェックリスト:
- Syntax.v
- Renaming.v: expr_names / alpha_rename_expr
- ExprFacts.v: expr_size
- AlphaExpr.v: expr_alpha + soundness
- TypingRules.v
- TypeChecker.v: infer_core_env / infer_core_env_roots / borrow_check_env
- OperationalSemantics.v
- readiness / provenance / shadow predicates
- CheckerSoundness.v
- BorrowCheckSoundness.v
- Env*Soundness.v
- tests/valid, tests/invalid, tests/fir
```

---

## 最優先で直すべき順番

私ならこの順でやる。

1. **docs drift 修正**
   `--debug-alpha` の嘘を消すか実装する。これは小さい割に効果が大きい。

2. **CLI acceptance gate を public checker endpoint に寄せる**
   OCaml 側が Rocq 側の安全 gate とズレている状態は避ける。

3. **`AlphaRenaming.v` を互換分割する**
   まず意味変更なし。ここで構造を作る。

4. **`expr_alpha` の `EStruct` / `EMatch` を強化する**
   これは relation の品質問題。将来の証明で事故る前に直す。

5. **`free_vars_expr` を `expr_names` に改名または分離する**
   名前が嘘をついている。エージェントにも人間にも悪い。

6. **traversal helper を導入する**
   文法追加時の変更面を減らす。

---

## まとめ

この実装は、証明穴だらけというより、**拡張に対して証明構造が硬すぎる**。特に `AlphaRenaming.v` は、今後文法や意味論を足すたびに作業者の認知負荷を跳ね上げる。

一番危ない設計臭はこの三つ。

* `AlphaRenaming.v` が 19,693 行の巨大依存ハブになっている。
* `expr_alpha` の `EStruct` / `EMatch` が構造を見ていない。
* OCaml CLI の受理経路が Rocq 側の program-level gate と一致していない。

解決策は、いきなり証明を美しく書き直すことではない。まず **互換分割**、次に **relation の強化**、その後に **traversal 共通化**。エージェントには巨大タスクではなく、上の Task 1〜5 のように狭い作業単位で渡すべき。そうすれば、文法・意味論の追加時に「どこを直せばいいか」が見えるようになる。
