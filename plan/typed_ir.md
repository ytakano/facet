# Typed IR

# Goal

- コマンドライン引数に--emit-fir <filename> を指定することで、Typed IRを出力する
- パース、型検査に失敗した場合は、エラーを出力し、Typed IRは出力しない

（firはFacet Intermediate Representationの略）

# 制約

- すべての値は、型注釈が必要
- 行指向
- SSA形式を採用
  - もとのASTに変数名がある場合、IR 上では x#0, x#1 のように de Bruijnインデックス付きで変数
  - 変数名を生成する場合、ユニークな名前を生成すること
- 命令セットは、let、return、call, drop, replaceの5種類
- 型は TypeChecker.infer_core を再帰的に呼び直して取得
- Rocqを用いた、FIRの検査は行わない
- ELetInferも、Letで出力すること
  - 型推論が失敗するが、出力はされない想定
- EDrop(ECall(...)) のようなネストした複合式は、FIR上では、一次変数を利用し、call命令とdrop命令に分割して出力すること

# Instructions

## Function Definition

```
fn ID (arg1: type1, arg2: type2, ...) -> type {
  instructions
}
```

## Value

値は、リテラル、変数のいずれかとする。
リテラル、変数には型注釈が必要

```
100 as linear isize
x as affine isize
```

## Let

- let式の変数には、全て型注釈が必要

```
let ID as type = Value
```

## Return

```
return Value as linear isize
```

## Function Call

```
call ID as unrestricted isize = ID (Value, Value, ...)
```

あるいは、返り値を無視する場合は以下も可能。

```
call _ as unrestricted unit = ID (Value, Value, ...)
```

## Drop

ID2をDropし、結果（unit）ID1に代入することを表す。

```
drop ID1 as unrestricted unit = ID2 as linear isize
```

## Replace

```
replace ID as affine isize = ID as affine isize with Value as affine isize
```

## Unit型の値

Unit型の値は、()と表す。
