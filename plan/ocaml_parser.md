# Facet Parser in OCamlの実装

# Goal

- Facet言語の構文解析器をOCamlで実装する
- RocqのExtraction時に、Peano NatからOCamlのbig integerに変換してExtractionするように設定
  - ExtrOcamlNatBigInt、ExtrOcamlZBigIntを利用
- ident の nat コンポーネントは、de Bruijnインデックスとすること
  - 通常パーサは名前ベースで変数を扱い、別パスでde Bruijnインデックスに変換すること
- 制約
  - 曖昧性のある表層構文は禁止
  - 中置記法禁止
  - rocq/theories/TypeSystem/Syntax.vのASTに変換可能
  - EBNFを機械的に生成可能であること
    - `--generate-grammar`オプションでEBNFを、マークダウン形式で出力可能であること
  - パースエラーを適切に報告すること
    - パース失敗した場合は、エラー型のバリアントを返す
    - パース失敗時の位置、rangeを報告すること
- ファイル読み込み
  - コマンドラインオプションから、ファイルを指定し、そのファイルを読み込みパースできること
  - パースしAST生成後、`fixtures/TypeChecker.ml`の`infer`関数に渡して型検査を行うこと
- 以下のファイルを作成すること
  - `ocaml/parser.ml`: OCamlで実装された構文解析器のコード
  - `ocaml/main.ml`: メイン実行ファイルのコード
- ELetInfer
  - 現段階では常に型検査でエラーとなってよい。後に、型推論を実装し解決予定。
  - パーサのみ実装すること
  - expr; (drop expr);のデシュガーが型検査エラーとなると想定
  - 現状では、linearな値のdrop xができないとを想定
- infer fenv ctx e を呼ぶ際のルール
  - ファイルで定義された全関数のbodyを検査すること
  - ctxには、その関数の fn_params を含めること
  - 関数定義のde Bruijnインデックスは常に0とする。同名の関数は、現段階では考慮しない。後の名前解決で、同名の関数があった場合は、エラーとする想定。
  - 関数呼び出しのde Bruijnインデックスも、常に0とする。
- 変数名 _ は、匿名変数とすること
  - 匿名変数は、同一ファイル内で複数回使用可能
  - de Bruijnインデックス付与の対象外, 常に0とする
  - 匿名変数は、let式の左辺にのみ使用可能とすること

# Tools

Menhir + Sedlex + Duneの利用を推奨

# Syntax

トップレベルの定義は、関数定義のみとすること。
トップレベルに式を置くことはできないものとする。

## 行コメント

// 以降の行はコメントとして扱う

## Function Call

```
(ID arg1 arg2 ...)
```

## Function Definition

```
fn ID (arg1: type1, arg2: type2, ...) -> type {
  expr
}
```

## Let

```
let ID: type = expr in expr
```

```
let ID = expr in expr
```

let の in が省略され、最後に;がある場合、syntax sugarとみなしてASTを生成。

```
let ID1 = expr1;
let ID2: type = expr2;
```

は、以下と解釈される。

```
let ID1 = expr1 in
  let ID2: type = expr2 in
    ()
```

```
fn double(x: affine isize) -> affine isize {
  let y: affine isize = x;
  y // 返り値
}
```

letの無い式は、let式の中の式とみなす。つまり、

```
{
  let ID1 = expr1;
  expr2;
  expr3;
  let ID2 = expr4;
  expr5
}
```

は、

```
let ID1 = expr1 in
let _ = expr2 in
let _ = expr3 in
let ID2 = expr4 in
expr5
```

と解釈できる。

;, inのないlet式の連続はパースエラーとする。

```
let ID1 = expr1
let ID2: type = expr2 // パースエラー
```

## Drop

```
(drop expr)
```

## Replace

```
(replace ID expr)
```

## Mutability

変数はデフォルトimmutable。変数の前に`mut`をつけると、mutableになる。

例

```
let mut x = 5;
```

```
fn add(mut x: linear isize) -> unrestricted unit
```

## Type

### Reference

```
& Type
&mut Type
```

& mut type を &mut として扱う

### Usage

```
linear TypeCore
affine TypeCore
unrestricted TypeCore
```

usage 無しの型はパースエラーとする

### Integer

```
isize
```

### Floating Point Number

```
f64
```

### Function Type

```
fn(Type1, Type2, ...) -> Type
```

### Unit

```
()
```

## Literal

- Integer Literal: 1, 42, -5
- Floating Point Literal: 3.14, -0.001,
  - 次の記法はパースエラーとする: 1., .5,  1e10, 1e-5

- lexer では最長一致にして、-> を - より優先して token 化
- -5 は 1トークンとする, スペース有りの- 5 はパースエラー

## 予約語

`fn`, `let`, `in`, `mut`,`drop`, `replace`, `affine`, `linear`, `unrestricted`, `isize`, `f64`は予約語とすること