# Lifetime v9: Nested Place FIR Lowering

## Summary

- v8で parser/typechecker/checker/Rocq semantics の recursive place 対応は進んだが、OCaml FIR は `PDeref _` に対して `failwith "nested places are not supported yet"` のまま残っていた。
- v9では `--emit-fir` が `*r`, `**rr` などの nested place を正しく出力できるようにする。
- Rocq の型規則や checker 仕様は変更せず、OCaml 側 FIR lowering/printing とテストを対象にする。

## Key Changes

- `ocaml/fir.ml` に FIR 用の place 表現を追加する。
- `FIReplace` と `FIBorrow` の対象を `ident` ではなく FIR place に変更する。
- `replace *r`, `replace **rr`, `&mut *r`, `&**rr` で root 変数ではなく実際の place を FIR に出力する。
- place の型推論ヘルパを追加し、`replace *r` の結果型を参照変数型ではなく deref 後の inner type にする。
- 既存の simple variable case は可能な限り出力互換を保つ。
- `FIDeref` の式 lowering は現状維持し、今回の対象は statement/place target の nested place 対応に限定する。

## Tests

- `tests/` 以下に FIR 用テストランナーを追加する。
- `--emit-fir` が nested place を含む valid `.facet` に対して panic/failwith しないことを確認する。
- 対象ケースは `replace *r`, `replace **rr`, `&mut *r`, `&**rr`, assignment through nested ref を含める。
- FIR 出力に `*r` や `**rr` 相当の nested place が現れることを最低限チェックする。
- 既存の typecheck 用 `tests/run.sh` は維持し、FIR テストは別 runner として追加する。

## Validation

- `dune build`
- `bash tests/run.sh`
- `bash tests/fir/run.sh`
- Rocq ファイルを変更した場合のみ `cd rocq && make`

## Assumptions

- v9では FIR の実行器や operational semantics は追加しない。
- lifetime elision、explicit outlives constraints、higher-rank lifetimes、`EVar r` copy aliasing は引き続き将来タスクとする。
- generated extraction artifact は Rocq 側を変更しない限り手動更新しない。
