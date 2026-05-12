# Underscore

## Summary

lexer では ident が _ を含み、しかも _ 専用トークンより先に ident がマッチする。
つまり _ は UNDERSCORE ではなく ID "_" になりやすい。parser 側では atom_expr が ID を変数として受け取るので、匿名変数 _ が式として参照できてしまう。
これは仕様とズレている。「_ は let 左辺のみ」なら、lexer を直して _ を専用トークンにし、atom_expr では受け取らない方がいい。
さらに、式文の desugar が、
ExprStmt e -> NLet (MImmutable, "_", None, e, cont)
なので、複数の _#0 が context に入り得る。匿名変数を本当に匿名にしたいなら、内部的にはユニークな不可視名を生成する方が安全。

## Goal

- lexer で _ を専用トークンにする
- _は、内部的にはユニークな不可視名を生成する
