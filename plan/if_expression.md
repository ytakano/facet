# If 式

# Goal

- Rocq
  - Primitive型とLiteralに、bool型を追加すること
  - EIf式の operational semantics を定義
  - EIf式の typing rules を定義
  - EIf式をサポートするように、TypeChecker.v を拡張すること
  - EIf式に対して、型検査が正しいことを証明すること
- OCaml
  - if式をサポートするように、構文、パーサを拡張
  - if式のFIR出力をサポートすること
- tests
  - linear/affinに対する、if式の型検査で、誤りが適切に発見できることを確認するテストケースをtests/linear_affine_error以下に追加すること
  - 上記以外の、if式に関する型検査エラーとなることを確認するテストケースをtests/if_expression以下に追加すること

# Rocq

## Bool型の追加

- Primitive型にbool型を追加
- Literalに、bool型のtrue, falseを追加

## EIf式のSyntax追加

```psuedocode
if expr1 {
  expr2
} else {
  expr3
}
```

## EIf式の operational semantics の定義

```psuedocode
if expr1 {
  expr2
} else {
  expr3
}
```

- expr1がtrueの場合、expr2を評価する
- expr1がfalseの場合、expr3を評価する

## Typing rule

```psuedocode
if expr1 {
  expr2
} else {
  expr3
}
```

- expr1の型は、boolでなければならない
- 条件式expr1の結果が, linear, affineのbool値の場合、その値は消費される
- expr2の型は、expr3の型と同じでなければならない
  - ただし、linear, affine, unrestricted などのusageは、異なってもよい
- if式全体の型は、expr2の型と同じである
  - ただし、usageは、expr2, expr3 のusageを比較し、条件の厳しいusageを採用する
  - 例: linear, affineのばあい、if式全体ではlinearとなる
- expr2または、expr3のどちらかで、linear, affineな値が消費された場合、if式全体も、そのlinear, affineな値を消費するとみなす
- expr2または、expr3のどちらかで、linear な値が消費された場合、もう一方でも、そのlinearな値を消費する必要がある。つまり、両方で、同じlinearな値が消費される必要があるか、全く消費しないのどちらかである

# Ocaml

## 表層構文

```facet
if expr1 {
  expr2
} else {
  expr3
}
```

## Syntax Sugar

else句は省略可能とする。つまり、以下のように書いてもよい。

```facet
if expr1 {
    expr2
}
```

これは、以下のSyntax Sugarとみなす。

```facet
if expr1 {
  expr2
} else {
  ()
}
```

## Facet Intermediate Representation (FIR)への変換

```facet
if expr1 {
  expr2
} else {
  expr3
}
```

FIRには、goto, if命令を追加。また、goto, if命令のためのラベルも追加する。
ラベルは、`ラベル名:`のように表現することとする。

```fir
if Value as linear bool -> IfThen, IfElse
IfThen:
    instructions for expr2
    goto LabelEnd
IfElse:
    instructions for expr3
LabelEnd:
```
