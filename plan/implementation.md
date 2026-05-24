1. 小タスクに分類し、以下のように順に実装する
2. sub-agentsに小タスクを一つ割り当て、実装させる
  - sub-agentsが上限に達している場合、再利用するか、古いsub-agentsを閉じる
  - 実装中に、soundness holeや、仕様の不備を見つけた場合は、そこで終了
. - 将来の設計・実装をする際にCodexのcontext windowが少なくなるように、設計・実装をすること
3. sub-agentsが実装完了後レビューを行う
4. レビュー時に、soundness holeや、仕様の不備を見つけた場合は、そこで終了
5. レビューで問題が見つからなかった場合、GPG署名無しでgit commit
6. 2に戻り、次のタスクを実装する
7. after finishing the tasks, update plan/fn_generics.md
  - must remove unnecessary information for future tasks
  - must update this document for Codex
  - must keep plan/fn_generics.md clear, consice and compact

## Context消費を抑えるための指示

- まず関連ファイルだけを最小限読むこと。ファイル全体を読む前に、`rg`で対象箇所を絞り、該当箇所の前後だけ確認すること。
- `sed`で読む範囲は原則80行以内にすること。より広い範囲が必要な場合も、目的を明確にして分割して読むこと。
- 広い検索結果、長いdiff、長いビルドログは会話に展開せず、必要な事実だけを要約して使うこと。
- Rocqやビルドの失敗時は、まず最初のエラー位置と必要な周辺だけ確認すること。巨大なゴールや環境表示を会話に展開しないこと。
- 同じ事実を再検索しないこと。既に得た情報、既に読んだ定義、既に確認した補題を優先して使うこと。
- テストは最初から全体を回さず、変更箇所に近い対象theory、対象ファイル、対象fixtureから始めること。最後に必要な全体チェックを回すこと。
- 中間報告は短くすること。変更点、失敗箇所、次の一手だけを書くこと。
- 最終報告は、変更点と実行した検証を中心に短くまとめること。

## Sub-agents Rule

- must not use sub-agents for exploring
- must not use sub-agents when planning
