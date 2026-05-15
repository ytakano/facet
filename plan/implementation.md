1. 小タスクに分類し、以下のように順に実装する
2. sub-agentsに小タスクを一つ割り当て、実装させる
  - sub-agentsが上限に達している場合、再利用するか、古いsub-agentsを閉じる
  - 実装中に、soundness holeや、仕様の不備を見つけた場合は、そこで終了
3. sub-agentsが実装完了後レビューを行う
4. レビュー時に、soundness holeや、仕様の不備を見つけた場合は、そこで終了
5. レビューで問題が見つからなかった場合、GPG署名無しでgit commit
6. 2に戻り、次のタスクを実装する
7. after finishing the tasks, update plan/type_safety_roadmap.md