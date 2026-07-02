# リファクタリング計画

2026-07-01 策定。現状調査・バグの実証・優先順位付けまでを本計画で行い、実装は後続セッションが本書に従って進める。

同日改訂: 実証したAPIバグ2件を個別修正する方針から、「推論コアと対話層の分離」で設計ごと解消する方針に変更した（下記「アーキテクチャ方針」参照）。

## 現状評価

- 構成: `src/lib.rs`（約1,300行、`Line`/`Solver`/テスト同居）+ `src/util.rs`（`Segments`, `SetMinMax`）。
- **コアの推論ロジックは健全**。4x4全列挙（65,536盤面）+ 5x5/7x7ランダム40万盤面の総当たり検証で、誤確定・偽Contradictionは0件だった。この検証は `tests/soundness.rs` として同梱済み（デバッグビルドで約14秒）。
- 問題は推論規則そのものではなく、**公開APIの状態管理**と**構造・依存の整理**に集中している。
- 性能の目安: 30x30 のフルsolveが数ms（統合テスト9本の合計で0.1秒）。この速さが下記アーキテクチャ方針の前提になる。

## アーキテクチャ方針: 推論コアと対話層の分離

solve は速度優先のまま、対話的な使い方（ユーザーが盤面を埋め、ヒントや矛盾チェックを受ける）は速度不要という前提を設計に反映する。フルsolveが数msなので、**対話の1操作ごとにソルバを毎回ゼロから作り直してよい**。

### コア: `Solver`（不変入力の推論エンジン）

- 制約（＋任意で初期盤面）を受け取って推論するだけにする。コンストラクタは `Solver::new(constraints)` に加えて `Solver::with_grid(constraints, grid)` を用意し、確定済みセルを種として与えられるようにする。
- **`set` と `rollback` を削除する**。外部からの書き換えがなくなることで、「`possible_block_ids` は狭まる一方向にしか更新されない」という内部不変条件が構築後に壊れないことが保証される。
- 残す公開API: `solve` / `advance` / `hint` / `state` / `judge` / `turn` / `Display`。

### 対話層: `Session`（新設・薄い）

ユーザー盤面 `Vec<Vec<State>>` と操作履歴だけを真実（ground truth）として持つ。

- `set(i, j, state)`: 盤面配列の書き換え＋履歴への記録のみ。Unconfirmed への巻き戻しも自由（ただの配列操作なので常に正しい）。
- `hint()` / 矛盾チェック: 呼ばれるたびに `Solver::with_grid(制約, 現盤面)` を新品で構築して問い合わせる。
- undo / redo / rollback: 履歴の切り詰め＋盤面再構築で自明に正しい。
- 間違い検出（任意機能）: 制約だけで solve した結果（一意解ならそれ）と現盤面を突き合わせ、ヒントより先に「(3,4) の黒が間違っている」と指摘できる。現行設計では間違った黒を前提にヒントが伝播してしまうため、その改善にもなる。

この分離により、下記の実証済みバグ2件は「修正」ではなく**発生し得ない設計**として解消される。

## 確認済みバグ（再現テストで実証済み）

いずれも上記アーキテクチャ変更で設計ごと消える。個別のパッチは当てず、`Session` 導入時に以下を仕様テストとして書き直して回帰を防ぐこと。

### Bug 1: `set(_, _, State::Unconfirmed)` でセグメント情報が残留する

`Line::set_state`（`src/lib.rs:148`）は `Unconfirmed` への遷移で何もしないため、黒→未確定に戻しても `segments_black` にセルが残る。結果、`judge()` が誤判定し、以降の推論も汚染された状態を見る。

```rust
let mut solver = Solver::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
solver.set(0, 0, State::Black);
solver.set(0, 0, State::Unconfirmed); // segments_black に (0,0) が残る
solver.set(0, 0, State::White);
solver.set(0, 1, State::Black);
solver.set(1, 1, State::White);
solver.set(1, 0, State::Black);
assert!(solver.judge()); // ← 正解を置いたのに false になる
```

なお `possible_block_ids` は狭める方向にしか更新されないため、`Solver` 内部でこれを正しく直すには行・列の `Line` 再構築が必要になる。`Session` 方式なら毎回全体を再構築するので、この問題自体が存在しない。

### Bug 2: `solve()` 消化後の `set()` が伝播しない

`Solver::set`（`src/lib.rs:714`）は `set_state` を直接呼ぶだけで、ソルバのキューに行・列を再投入しない。`solve()` が一度キューを消化し切った後に `set` で情報を与えても、以降の `solve()`/`advance()` は何も推論しない。

```rust
let mut solver = Solver::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
solver.solve().unwrap_err();      // Indeterminate（解2通り）
solver.set(0, 0, State::Black);   // 正解の1つを教える
solver.solve().unwrap_err();      // ← まだ Indeterminate のまま
assert_eq!(solver.state(1, 1), State::Unconfirmed); // 黒に確定できるはずが未確定
```

`Session` 方式では `hint`/チェックのたびに新品の `Solver` を作るため、キュー再投入という概念自体がなくなる。

### Bug 3: 伝播矛盾のエラー座標が転置される

`Solver::advance` の直交伝播（`src/lib.rs:643-647`）はエラーを発生源の行の座標 `(axis, i)` でラップするが、`LineError` 側の `j` は**直交行内の位置**なので座標系が混ざる。

```rust
let mut solver = Solver::new([
    vec![vec![], vec![3, 1], vec![], vec![], vec![]],
    vec![vec![1, 3], vec![], vec![], vec![], vec![]],
]);
// 真の矛盾セルはグリッド (1, 0)（列0の中で検出）だが、
// エラーは Row[0][1] ＝グリッド (0, 1) を指す（転置）。さらに by は
// 流用された偽の BlackIfOverlap で、current=Unconfirmed → new=Black
// という「矛盾ですらないペア」が表示される。
println!("{}", solver.solve().unwrap_err());
```

修正は下記設計問題3（`Operation` と書き込み出所の分離）に含める。座標は「矛盾を検出した行」基準に統一し、出所は `Cause::Propagation` が持つ。

## 設計上の問題（バグ予備軍・中優先）

1. **`Solver::new` が panic する**（`assert_eq!` による正方形チェックのみ）。ライブラリとしては `Result` を返すべきで、あわせて入力検証を追加する: ブロックサイズ 0 の拒否、`sum(blocks) + gaps <= n` の検証。現状 `vec![0]` などを渡すと内部不変条件が壊れる（`wrapping_sub` 周りの演算が前提を失う）。`with_grid` では盤面サイズ・状態の整合も検証する。
2. **正方形盤面限定**。`n` を `(height, width)` に分離する。目的は長方形パズル対応そのものではなく、同じ `n` が高さ・幅・行長の3役を兼ねることで i/j の取り違えがテストで検出できない（正方形は転置しても同じ形）状態の解消。`Line` は既に自分の長さを持っているので、変更は `Solver` 側の対称性の仮定（`queue` 初期化、`solve` の走査、`judge`、`Display`）に限られる。**対応時は `tests/soundness.rs` に長方形（例: 5x8, 7x3）のランダム盤面を必ず追加すること**。正方形のテストだけでは取り違え検出という導入意図が実現されない。
3. **`Operation` と「書き込みの出所」の分離**。現状の `Operation` は2つの役割を同居させている: 8つの行内推論規則（`Action`/`Hint` に現れる）と、`SameStateAsOrthogonal`（矛盾エラーの `by` にしか現れない伝播マーカー。`hint()` にも `advance()` の戻り値にも一度も現れない）。さらに `update_possible_id` の「置き場所がない」矛盾が偽の `BlackIfOverlap` を流用している（`src/lib.rs:344`）。次の3層に分ける:
   - `Operation`: 8規則のみ。`Action.by` と `Hint` はこの型を持ち、**「ヒントは常に行内規則」が型レベルで保証される**（`SameStateAsOrthogonal` variant は削除）。
   - `Cause`: セル書き込みの出所。`Operation(Operation) | Propagation { axis: Axis, i: usize }`。矛盾エラーの `by` はこちらを持つ。伝播の発生源はこの variant のペイロードとして自然に載る。
   - `LineError`/`SolverError` に **`NoPlacement { id }` variant を新設**し、偽 `BlackIfOverlap` の流用を廃止（これはセル書き込みの矛盾ではなく行レベルの矛盾なので、`Cause` ではなくエラー variant が正しい置き場所）。
   矛盾エラーの座標は「矛盾を検出した行」基準（`axis.orthogonal(), j` に位置 `i`）に統一し、Bug 3 の転置を修正する。
4. **`update` に `Unconfirmed` を渡すと Contradiction 扱い**（`src/lib.rs:170`）。推論が書き込む状態は白か黒だけなので、キューに積む型を `enum Determined { White, Black }` のような確定値専用型にし、型レベルで排除する。
5. **`hint()` が残留キューを拾い得る**。`Solver::advance` は `Line` のキューから1件だけ取り出すため、`advance` と `hint` を混ぜて使うと `hint` がステップ実行結果ではなく残留項目を返し、「最も安いステップ順」の保証が崩れる。`Session` 経由（毎回新品の `Solver`）では発生しないが、コアAPIとして `advance` と併用した場合の仕様を明文化するか、クローン後にキューを先に消化してから探索する。
6. **`Solver::advance` のキューに重複投入がある**（dedup なし）。`(axis, i)` の in-queue フラグを持たせれば無駄な再走査が減る。
7. **`state()` が `assert_eq!` で panic し得る**getter。`debug_assert_eq!` に落とすか、行側を正とする。

（旧8「`rollback` がユーザーの `set` を巻き戻し再生に含めない」は、`rollback` の `Session` 移管により消滅。）

## リファクタリング本体（挙動不変の整理）

- **A. モジュール分割**: `lib.rs` → `solver.rs` / `line.rs` / `operation.rs` / `error.rs` / `session.rs`（`util.rs` は `segments.rs` に改名）。単体テストは各モジュールへ、公開APIの再エクスポートは `lib.rs` に集約。分割自体は機械的な移動のみで挙動変更を伴わないこと。
- **B. `Cell::possible_block_sizes`（セル毎の `FixedBitSet`）の廃止**: 使途は「候補ID範囲内のブロックサイズの min / max」の2種類だけ（`ones().next()`, `count_ones(..)` の3箇所）。`Line` がブロックサイズ列を持っているのだから、`possible_block_ids: Range<usize>` に対する範囲 min/max（ブロック数は小さいので素朴な走査で十分）で置き換えられる。これで:
  - セル毎 O(n) ビットセットのメモリと、`update_possible_id` 末尾の毎回全再構築（`src/lib.rs:349-357`）が消える
  - `fixedbitset` 依存を削除できる
- **C. `Display` の重複排除**: `Solver::fmt` に同型のループが3つある（`src/lib.rs:728-814`）。1盤面を描くヘルパに畳む。3面併記のデバッグ表示は `Debug` か別メソッドに逃がし、`Display` は素直な1盤面にするのが自然。
- **D. `Operation` のペイロードと `Action.range` の整合整理**: 例えば `BlackIfLeftBounded(l, r)` は塗った範囲 `j..r` と異なる区間を持つなど、variant ごとに意味がまちまち。「塗った範囲は `Action.range`、`Operation` は根拠の区間・ID」と役割を統一し、docコメントに明記する。あわせてペイロードの線引きを次で固定する:
  - **`Operation` は数ワードの `Copy` を上限**とし、発火箇所で既知の `usize` は持たせてよい。具体的には `BlackIfOverlap` に根拠ブロックの id（ブロックごとのループ内で既知）、`WhiteIfTooLong` に唯一候補の id（計算済み）。いずれも追加計算ゼロで、矛盾エラーの `by` の情報量も上がる。伝播の発生源 `(Axis, usize)` は設計問題3の分離後は `Cause::Propagation` のペイロードとなり、`Operation` からは消える。
  - **アロケーションを伴う説明データ**（候補ID範囲の列など）は `Operation` に入れず、`hint()` がスナップショットから事後算出して `Hint` に載せる（現行 `Hint.possible_ids` の方式を一般化）。`hint` は `Session` 経由の使い捨て `Solver` 上で人間の操作頻度でしか呼ばれないため、コストを掛けてよい。solve のホットパスに乗るのは前者のみ、という分離が `Session` 方式の利点。
  - **ペイロード追加の判定基準**: 「アンカー＋ヒント時点のスナップショットから、その推論の説明を一意に再構成できるか」。できないものだけペイロードに昇格させる（`BlackIfOverlap` は同じ範囲を複数ブロックが説明し得るので id を `Operation` に、伝播の発生源は行内から復元不能なので `Cause::Propagation` に）。残る6規則はアンカー `(l, r)` でインスタンスが一意なので追加不要。variant ごとに説明データを足していくと各 variant が行状態を内蔵する方向に肥大するため、この基準で歯止めをかける。
  - 説明の根拠データは `Hint` を「行コンテキスト」に一般化して一枚で持つ: セルごとの候補ID範囲（`possible_ids`、導入済み）に加え、**ブロックごとの配置可能範囲とサイズ**を追加する。例えば `WhiteIfNoBlockCovers` の「ブロック#1は左からここまで、#2はここから先」は配置範囲から、`BlackIfLeftBounded`/`BlackIfBounded` の「最小候補サイズ m」は候補×サイズ列から導出できる。人間向けの文言化（説明文の組み立て）は `Session`/UI 層の仕事とし、コアの enum には入れない。
- **E. 小物**: 単一 variant の `LineError` を struct に、`Line::n` は `cells.len()` と重複、`possible_id()` の `Range` clone 頻発、など。

## 周辺整備

- **CI**: GitHub Actions で `cargo fmt --check` / `cargo clippy -- -D warnings` / `cargo test`。soundness テストはデバッグビルド約14秒なのでそのまま常時実行できる。なお現時点で `src/lib.rs` と `src/util.rs` に既存の fmt 違反があるため、CI 導入時に `cargo fmt` を一度かけること。
- **依存とエディション**: `thiserror` 1.x → 2.x、`edition = "2024"`、`rust-version` の明記。B 完了後に `fixedbitset` を削除。
- **ドキュメント**: README（制約の与え方 `[rows, cols]`、`Solver` と `Session` の使い分け、`solve`/`advance`/`hint` の説明）、公開APIの rustdoc + doc-test。現状 README が存在しない。
- **ベンチ**: 任意。現状 30x30 が数msで実用上問題ないため、B/C の前後比較をしたい場合のみ criterion を導入。

## 実施順序（PR分割案）

| # | 内容 | 依存 |
|---|------|------|
| 1 | 安全網: CI 追加＋既存 fmt 違反の一括整形（soundness テストは導入済み） | なし |
| 2 | `Solver` から `set`/`rollback` を削除し、`with_grid` と `Session` 層を新設。Bug 1・Bug 2 の再現ケースを `Session` の仕様テストとして収録 | 1 |
| 3 | モジュール分割 A（機械的移動のみ） | 1 |
| 4 | B: `possible_block_sizes` 置換 + `fixedbitset` 削除 | 3 |
| 5 | 設計問題 1〜4: 入力検証・`Result` 化・長方形対応・確定値型 | 2, 3 |
| 6 | C/D/E + 設計問題 5〜7 + `Session` の間違い検出（任意）+ ドキュメント・依存更新 | 3 |

各PRで `cargo test`（soundness 含む）が通ることを確認してから次へ進む。特に 4 と 5 は推論の等価性が要なので、soundness テストの乱数シードを変えた追加ランで確認するとよい。

PR 2 は破壊的変更（`Solver::set`/`rollback` の削除）を含む。既存の利用側があれば `Session` への移行がそのまま置き換え手順になる。

## 非目標

- 推論規則の強化（背理法・二択試行など線形推論を超える探索）は本リファクタリングの範囲外。`Indeterminate` の解消率向上は別トピックとして扱う。なお規則ベースのエンジンを完全な行DPソルバに置き換える案は、推論力は上がるが「人間に説明できる根拠（`Operation`）」というヒントUXの資産を失うため採用しない。
- 全面的な書き直し。難しくて価値のある部分（`update_possible_id` と8つの推論規則）は総当たり検証済みの資産であり温存する。書き直すのは薄いAPI層（`Session`）のみ。
- 並列化・SIMD 等の高速化。現状性能で困っていない。
