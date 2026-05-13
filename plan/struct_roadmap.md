# Struct/Trait Implementation Roadmap

## 方針

`plan/struct.md` の仕様を、実装順に分解する。struct は Rocq のコア言語に追加し、trait はメソッドと関連型を持たない skeleton として導入する。top-level item は先に全収集し、Validator で環境の well-formedness を確認してから TypeChecker に渡す。

Validator は定義環境の正しさを担当し、TypeChecker は式・place・usage・borrow の動的な型検査を担当する。OCaml frontend と FIR は、Rocq 側の抽出物に追従して段階的に拡張する。

## Milestones

1. **M0: 未確定仕様の固定**
   - generic impl 解決を「型変数への単純な一階マッチング」として固定する。
   - impl 解決で複数候補が一致した場合はエラーにする。
   - lifetime 引数も impl マッチング対象に含める。
   - moved field に値を戻して全 field が available になった場合、親 struct への参照を再許可するかを決める。
   - FIR の struct 関連命令セットを決める。

2. **M1: Rocq core type/syntax/env 拡張**
   - `TypeCore` に `TStruct name lifetime_args type_args` 相当を追加する。
   - `place` に field path を表す `PField place field_name` 相当を追加する。
   - `expr` に struct literal を追加する。
   - struct / trait / impl / fn を保持する top-level item と環境型を追加する。
   - usage 最大値による struct instance usage 推論を定義する。

3. **M2: Validator 導入**
   - `theories/Validation/Validator.v` を追加し、実行可能な validation 関数を定義する。
   - Validator は top-level item を全収集し、`struct/trait/impl/fn` 環境を返す。
   - 重複名、未定義型、未定義 trait、重複 field、未知 field、recursive struct、相互 recursive struct を拒否する。
   - lifetime parameter と type parameter の重複、未定義参照、未使用を error として扱う。
   - `ValidEnv env` または `validated_env` を定義し、証明では TypeChecker の前提にする。

4. **M3: TypeChecker の struct/trait 環境対応**
   - `infer` / `infer_core` に validated environment を渡す。
   - struct literal の全 field 必須、順序任意、重複/未知 field error を検査する。
   - 型引数適用後の field usage 最大値から instance usage を推論する。
   - 明示型がある場合は `unrestricted <: affine <: linear` の usage subtyping で照合する。
   - trait bound は Validator で well-formedness を確認し、TypeChecker で型引数適用後の impl 解決を行う。

5. **M4: field place / partial move / partial reference**
   - `p.field` を式として使う場合、unrestricted field は copy、affine/linear field は move として扱う。
   - moved field は unavailable とし、moved でない sibling field は引き続き使用可能にする。
   - partial move された struct instance 全体への参照は禁止する。
   - borrow conflict は field path の同一または prefix 関係で衝突、兄弟 path は非衝突とする。
   - `&S` 越しの field move は禁止し、unrestricted field の copy のみ許可する。
   - `&mut S` 越しは affine/unrestricted field の assign/replace/borrow を許可し、linear field は replace/borrow のみ許可、assign は禁止する。
   - linear/affine field への参照は borrow のみ可能で、参照経由の消費は不可とする。

6. **M5: OCaml surface syntax 実装**
   - lexer に `struct`, `trait`, `impl`, `for`, `where` 関連 token と field access token を追加する。
   - parser に top-level item、generic parameter list、trait bound、impl、struct definition、struct literal、field access を追加する。
   - lifetime parameter と type parameter は `<...>` 内で混在可能にし、kind は `'a` 形式かどうかで判定する。
   - de Bruijn 変換を field path、struct literal、top-level item に対応させる。
   - CLI は Validator を TypeChecker 前に呼び、Validator error と TypeChecker error を区別して表示する。

7. **M6: FIR lowering**
   - struct literal、field access、field assign/replace/borrow は `ProjectField` 系の命令へ lower する。
   - `fir_place` に field path を保持するか、`ProjectField` 命令で一時変数へ射影するかは M0 の決定に従う。
   - `drop instance` は構造的 destructor として、unconsumed field を全て drop する FIR に展開する。
   - nested field は source の field path を保ったまま conflict/debug が追える形で出力する。

8. **M7: Soundness proofs 拡張**
   - `theories/Validation/ValidatorSoundness.v` を追加し、Validator が返す環境の well-formedness を証明する。
   - `TypingRules.v` と `OperationalSemantics.v` に struct literal、field place、field move/drop/borrow の規則を追加する。
   - `CheckerSoundness.v` で struct literal、field access、impl 解決、usage 推論の checker/rule 対応を証明する。
   - `CheckerUsageSoundness.v` と `BorrowCheckSoundness.v` で partial move/reference と field path conflict を扱う。

9. **M8: regression tests と docs**
   - valid/invalid fixture を struct literal、field access、partial move、partial reference、trait bound、impl 解決、recursive struct rejection に分けて追加する。
   - FIR fixture で field projection、field replace、field borrow、structural drop を確認する。
   - `AGENTS.md` と grammar 出力を必要に応じて更新する。

## Error 分担

- **Validator error**
  - top-level 名の重複。
  - struct / trait / impl / fn 環境の構築失敗。
  - 未定義型、未定義 trait、未定義 lifetime、未定義 type parameter。
  - lifetime/type parameter の重複または未使用。
  - struct field の重複、未知 field、recursive struct、相互 recursive struct。
  - trait bound の well-formedness 違反。

- **TypeChecker error**
  - struct literal の field 型不一致、usage mismatch、明示 usage との subtyping 不一致。
  - field access の move/copy/borrow 制約違反。
  - partial move 後の parent reference。
  - field path conflict。
  - impl 未解決または複数 impl 候補一致。
  - mutability 条件違反。

## Validation and Tests

実装各段階で以下を基準にする。

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
rg -n "\bAxiom\b|Admitted\." rocq/theories
```

追加する fixture の最低ライン:

- `tests/valid/struct/`: struct literal、field access、nested field、usage 推論、structural drop。
- `tests/valid/trait/`: trait skeleton、複数 trait bound、generic impl 解決。
- `tests/valid/borrow/`: sibling field borrow、`&S` field copy、`&mut S` field borrow/replace。
- `tests/invalid/struct/`: missing field、duplicate field、unknown field、recursive struct、usage mismatch。
- `tests/invalid/trait/`: unknown trait、duplicate impl、impl unresolved、ambiguous impl。
- `tests/invalid/borrow_conflict/`: prefix path conflict、partial move 後 parent reference。
- `tests/fir/`: `ProjectField` 系 lowering、field replace、field borrow、unconsumed field drop。

## Open Decisions

- moved field を replace して全 field が available になった場合、parent reference を再許可するか。
- FIR で field path を `fir_place` に保持するか、projection 命令へ完全に lower するか。
- generic impl matching の詳細なデータ構造と diagnostics。
