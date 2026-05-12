# Assignment

# Goal

- Rocq
  - Syntaxに、代入の構文を追加
  - TypingRulesに、代入の型検査ルールを追加
  - TypeCheckerに、代入の型検査の実装を追加
- OCaml
  - Parserに、代入の構文を追加
  - 代入のASTから、Facet IR (FIR) のassign命令を生成するコードを追加

# 制約

- 代入は、placeに対して行われる
  - place = expr
- 代入先のplaceは、mutableでなければならない
- 代入先のusageは、unrestrictedか、affineでなければならない
- 代入先と代入もとは、usageのpolymorphismのルールに従う必要がある
  - 例:
    - unrestrictedなplaceには、unrestrictedな値しか代入できない
    - affineなplaceには、unrestrictedな値も、affineな値も代入できる
    - linearな値は、どのplaceにも代入できない。なぜならば、代入先のusageはlinearであってはならないからである
- exprがaffineの場合、その値は消費される

# FIR

assign命令を追加すること。

```
assign x as affine isize = 100 as unrestricted isize
```
