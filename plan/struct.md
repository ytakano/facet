# Struct素案

## Goals

- structはRocqのコア言語に追加し、型検査器で制約を満たすことを証明
- structのsurface syntaxを, OCamlで定義
- structのFIRを定義

## 制約

- struct instance usageは、メンバ変数usageに対してusage polymorphicを守る
  - structのinstanceがunrestricted
    - unrestrictedなメンバ変数のみ許可
  - structのinstanceがaffine
    - affine, unrestrictedなメンバ変数のみ許可
  - structのinstanceがlinear
    - linear, affine, unrestrictedなメンバ変数を許可
- 参照型のメンバ変数
  - 必ず、ライフタイムパラメータを持つ
  - struct引数に、ライフタイムパラメータを持たせる必要がある
- trait
  - 今回は、traitメソッド、関連型の実装は行わないが、traitの導入を想定する
  - traitのスケルトンのみ導入
  - generic boundのwell-formednessに導入して検証
  - impl をbound解決に使う
    - 完全一致のみ、重複impl禁止
- Generics
  - struct
    - structの定義にGenericsを導入
    - structは型引数を持つことができる
    - structの型引数に、trait boundを指定できる
  - trait
    - traitの定義にGenericsを導入
    - traitは型引数を持つことができる
    - traitの型引数に、trait boundを指定できる
    - impl<T> Trait for Struct<T>も許可
  - 型引数適用時に、型引数のusageを調べ、struct instanceのusageを決定する
    - struct instance usageは、メンバ変数usageに対してusage polymorphicを守るを参照
    - 「field usageの最大値をinstance usageにする」、つまり linearがあればlinear、linearがなくaffineがあればaffine、全てunrestrictedならunrestricted、
    - instanceの型を明示的に指定された場合は、usage subtypingを許す
      - unrestricted <: affine <: linear なら、推論が unrestricted の値を affine として扱うのはOK、逆はNG
  - struct/trait generic引数のkind
    - lifetimeは 'a で字句的に区別できるので混在可、ただし重複禁止
- partial move
  - structのメンバ変数の一部をmoveすることができる
  - moveされたメンバ変数は、使用できなくなる
  - moveされなかったメンバ変数は、引き続き使用できる
  - linear structのmove, dropについては後述
  - partial moveされたstruct instanceへの参照は禁止
  - p.field を式として使う場合、affine/linear fieldはmove扱い
- partially reference
  - structのメンバ変数の一部を参照することができる
  - 借用中は直接move/assign不可
  - 参照されなかったメンバ変数は、引き続き使用できる
    - &p.field1 中に replace p.field2 v や &mut p.field2などは許可
- struct / trait / impl を fn と同列のトップレベルitemとして扱う
  - 前方参照可能
  - 重複名不可
    - struct, trait, function名は同じ名前空間で重複不可
  - struct/trait/impl/fnを先に全収集してから検査する、struct依存グラフで再帰を検出
    - この検査は、TypeSystemとは別パスで行う
    - Rocqに、以下を追加
      - theories/Validation/Validator.v を追加して、実行可能な関数を定義し、OCamlにExtract
        - validatorは、成功した場合、struct/trait/impl、環境も返す
        - OCamlは、このValidatorをTypeCheck前に呼び出す
        - TypeCheckerに、struct/trait/impl、環境を渡す
        - TypeCheckerは、struct/trait/impl、環境が正しいことを前提にして、型検査を行う
          - validated_env レコードや ValidEnv env を返す
          - 実行時はデータ、証明では ValidEnv env 仮定を別引数にする
        - Validatorでgeneric boundのwell-formednessを検査し、TypeCheckerで型引数適用後のimpl解決
        - lifetime argumentsの検査も追加
          - struct S<'a, 'a>のような重複lifetime argumentは禁止
          - 未定義lifetime参照
          - 未使用lifetime (error)
        - type parameter argumentsの検査も追加
          - struct S<T, T>のような重複type parameter argumentは禁止
          - 未定義type参照
          - 未使用type parameter (error)
      - theories/Validation/ValidatorSoundness.v を追加して、Validatorの正しさを証明
- fieldのreplaceは可能
- fieldへの代入は、unrestricted, affineな値にのみ許可する
- 全てのfieldはpublicとする
  - privateは、後で導入予定
  - privateは、型検査器ではなく、visibility checkerを別に実装しチェック予定
- field毎にmutabilityを指定可能
  - Surface Syntaxで、mutabilityを指定しない場合、デフォルトでimmutableとする
  - mutと指定された場合、mutableとする
- Rocqで型引数・ライフタイム引数を保持するための、TStruct name lifetime_args, type_args や TApp name args 相当を導入
- fieldへの代入、replaceは、fieldごとの mut とbinding側の let mut instance の両方必要
- nested field、例 a.b.c や (*p).x.y も対応
  - 同一pathまたはprefix関係なら衝突、兄弟pathなら非衝突
  - 例: &p.a.b 中に replace p.a.c は許可、replace p.a と replace p.a.b.c は禁止
- recursive structは、現段階では許可しない
  - 無限サイズのstructは定義不可
  - 後に、Box、ポインタ相当を導入予定であり、その際に、recursive structを許可する予定
  - 相互recursive再帰も禁止
- &S 越しの .field はmove禁止
  - unrestrictedなfieldは、moveではなくcopyと想定するため、可能
- &mut S 越しのfield assign/replace/borrow
  - affine, unrestrictedなfieldは、assign/replace/borrow可能
  - linearなfieldは、replace/borrow可能, assign禁止
  - linear/affineへの参照は、borrowのみ可能で消費不可
- FIR
  - struct literal、field access、field assign/replace/borrowは、ProjectField のような命令にlower

## Surface Syntax

### Trait

```facet
trait TraitName<T> where T: TraitBound;
```

型引数と、where句は省略可能。

```facet
impl<T, U> TraitName<T> for StructName<U>;
```

### Struct

```facet
struct StructName<'a, T> where T: TraitBound {
    mut field1: Type1,
    field2: Type2,
    ref_field: &'a Type3,
    ...
}
```

型引数、where句は省略可能。

ライフタイムパラメータは指定可能だが、必須ではない。

### Struct Instance

```facet
let instance_name: StructName<'a, T> = StructName::<'a, T> {
    field1: value1,
    field2: value2,
    ref_field: &value3,
    ...
};
```

- instance_nameの型は省略可能。推論する。
- StructName::<'a, T> { ... } と型引数を指定可能だが、型引数、ライフタイム引数は省略可能で、その場合は推論する。
- instantiation時には、struct fieldの順序は問わない。
- struct literalは全field必須
- 重複field指定と未知field指定はエラー

### Field Access

```facet
instance_name.field1
```

instanceが参照の場合は、自動的にデリファレンスされる。以下の2つのコードは同等である。
ただし、auto dereferenceは、1段のみとする。

```facet
(*ref_instance).field1
```

```facet
ref_instance.field1
```

### Trait Bound

複数のtrait boundは、+で繋げる。

例:

```facet
trait TraitName<T> where T: TraitBound1 + TraitBound2;
```

## Linear/Affine Struct

linear/affine structは、全てのlinear/affine fieldをdrop or (partial) moveしてから、dropできる

例

```facet
struct LinearStruct {
    field1: linear Type1,
    field2: affine Type2,
}
```

の場合、以下のように、field1をdrop, moveしてから、instanceをdropできる。

```facet
let instance = LinearStruct {
    field1: value1,
    field2: value2,
};

(drop instance.field1);
(drop instance)
```

ただし、

- (drop instance.field1) 後に instance.field2 は使用可能で、&instance は禁止
- (drop instance)
  - field dropなしで、単に(drop instance)とされた場合
    - drop は構造的destructorであり、unconsumed fieldを全てdropすることを意味する
    - FIRで、unconsumed fieldを全てdrop
