# リファクタリング計画

2026-07-01 策定。現状調査・バグの実証・優先順位付けまでを本計画で行い、実装は後続セッションが本書に従って進める。

## 現状評価

- 構成: `src/lib.rs`（約1,300行、`Line`/`Solver`/テスト同居）+ `src/util.rs`（`Segments`, `SetMinMax`）。
- **コアの推論ロジックは健全**。4x4全列挙（65,536盤面）+ 5x5/7x7ランダム40万盤面の総当たり検証で、誤確定・偽Contradictionは0件だった。この検証は `tests/soundness.rs` として同梱済み（デバッグビルドで約14秒）。
- 問題は推論規則そのものではなく、**公開APIの状態管理**と**構造・依存の整理**に集中している。

## 確認済みバグ（再現テストで実証済み・最優先で修正）

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

**修正方針**: 単に `Unconfirmed` 時に `segments_black.erase` / `segments_non_white.insert` / `segments_unconfirmed.insert` するだけでは不十分。`possible_block_ids` は狭める方向にしか更新されない（単調）ので、セルを未確定に戻したら広げ直せない。正しくは、`set` で状態を消す場合に**該当する行・列の `Line` を `Line::new` から再構築**し、現在のセル状態を流し込んで `update_possible_id` をかけ直す（`possible_block_ids` はセル状態から導出される値なので再構築で正しく復元できる）。

### Bug 2: `solve()` 消化後の `set()` が伝播しない

`Solver::set`（`src/lib.rs:714`）は `set_state` を直接呼ぶだけで、ソルバのキューに行・列を再投入しない。`solve()` が一度キューを消化し切った後に `set` で情報を与えても、以降の `solve()`/`advance()` は何も推論しない。

```rust
let mut solver = Solver::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
solver.solve().unwrap_err();      // Indeterminate（解2通り）
solver.set(0, 0, State::Black);   // 正解の1つを教える
solver.solve().unwrap_err();      // ← まだ Indeterminate のまま
assert_eq!(solver.state(1, 1), State::Unconfirmed); // 黒に確定できるはずが未確定
```

**修正方針**: `set` で両軸の `(axis, i)` / `(axis.orthogonal(), j)` をキューへ再投入する。あわせて `set` を `Result<(), SolverError>` にし、`update()` 経由にして既存確定との矛盾（例: 白のセルに黒を置く）を検出可能にする。Bug 1 の再構築方針と統合して設計すること。

## 設計上の問題（バグ予備軍・中優先）

1. **`Solver::new` が panic する**（`assert_eq!` による正方形チェックのみ）。ライブラリとしては `Result` を返すべきで、あわせて入力検証を追加する: ブロックサイズ 0 の拒否、`sum(blocks) + gaps <= n` の検証。現状 `vec![0]` などを渡すと内部不変条件が壊れる（`wrapping_sub` 周りの演算が前提を失う）。
2. **正方形盤面限定**。イラストロジックは長方形が普通。`n` を `(height, width)` に分離する。`Line` は既に自分の長さを持っているので、変更は `Solver` 側の対称性の仮定（`queue` 初期化、`solve` の走査、`judge`、`Display`）に限られる。
3. **`update_possible_id` の矛盾報告が `Operation::BlackIfOverlap` を流用**（`src/lib.rs:344`）。「ブロックの置き場所がない」という別種の矛盾なので、専用のエラー表現（例: `Operation::NoPlacement(id)` か `SolverError` の新 variant）にする。
4. **`update` に `Unconfirmed` を渡すと Contradiction 扱い**（`src/lib.rs:170`）。推論が書き込む状態は白か黒だけなので、キューに積む型を `enum Determined { White, Black }` のような確定値専用型にし、型レベルで排除する。
5. **`hint()` が残留キューを拾う**。`Solver::advance` は `Line` のキューから1件だけ取り出すため、`Line::queue` に未消化の項目が残ることがある。`hint()` はクローンした line の `pop_front` がステップ実行結果ではなく残留項目を返し得るので、「最も安いステップ順に返す」という保証が崩れる。仕様を明文化するか、クローン後にキューを先に消化してから探索する。
6. **`Solver::advance` のキューに重複投入がある**（dedup なし）。`(axis, i)` の in-queue フラグを持たせれば無駄な再走査が減る。
7. **`state()` が `assert_eq!` で panic し得る**getter。`debug_assert_eq!` に落とすか、行側を正とする。
8. **`rollback` はユーザーの `set` を巻き戻し再生に含めない**。`clear()` からの replay は `advance` 由来の手のみ再現するため、`set` 済みセルは黙って消える。仕様として明記するか、`set` も履歴に記録する。

## リファクタリング本体（挙動不変の整理）

- **A. モジュール分割**: `lib.rs` → `solver.rs` / `line.rs` / `operation.rs` / `error.rs`（`util.rs` は `segments.rs` に改名）。単体テストは各モジュールへ、公開APIの再エクスポートは `lib.rs` に集約。機械的な移動のみで挙動変更を伴わないこと。
- **B. `Cell::possible_block_sizes`（セル毎の `FixedBitSet`）の廃止**: 使途は「候補ID範囲内のブロックサイズの min / max」の2種類だけ（`ones().next()`, `count_ones(..)` の3箇所）。`Line` がブロックサイズ列を持っているのだから、`possible_block_ids: Range<usize>` に対する範囲 min/max（ブロック数は小さいので素朴な走査で十分）で置き換えられる。これで:
  - セル毎 O(n) ビットセットのメモリと、`update_possible_id` 末尾の毎回全再構築（`src/lib.rs:349-357`）が消える
  - `fixedbitset` 依存を削除できる
- **C. `Display` の重複排除**: `Solver::fmt` に同型のループが3つある（`src/lib.rs:728-814`）。1盤面を描くヘルパに畳む。3面併記のデバッグ表示は `Debug` か別メソッドに逃がし、`Display` は素直な1盤面にするのが自然。
- **D. `Operation` のペイロードと `Action.range` の整合整理**: 例えば `BlackIfLeftBounded(l, r)` は塗った範囲 `j..r` と異なる区間を持つなど、variant ごとに意味がまちまち。「塗った範囲は `Action.range`、`Operation` は根拠の区間・ID」と役割を統一し、docコメントに明記する。
- **E. 小物**: 単一 variant の `LineError` を struct に、`Line::n` は `cells.len()` と重複、`possible_id()` の `Range` clone 頻発、など。

## 周辺整備

- **CI**: GitHub Actions で `cargo fmt --check` / `cargo clippy -- -D warnings` / `cargo test`。soundness テストはデバッグビルド約14秒なのでそのまま常時実行できる。なお現時点で `src/lib.rs` と `src/util.rs` に既存の fmt 違反があるため、CI 導入時に `cargo fmt` を一度かけること。
- **依存とエディション**: `thiserror` 1.x → 2.x、`edition = "2024"`、`rust-version` の明記。B 完了後に `fixedbitset` を削除。
- **ドキュメント**: README（制約の与え方 `[rows, cols]`、`solve`/`advance`/`hint`/`rollback` の使い分け）、公開APIの rustdoc + doc-test。現状 README が存在しない。
- **ベンチ**: 任意。現状 30x30 が数ms〜数十msで実用上問題ないため、B/C の前後比較をしたい場合のみ criterion を導入。

## 実施順序（PR分割案）

| # | 内容 | 依存 |
|---|------|------|
| 1 | 安全網: CI 追加（soundness テストは導入済み） | なし |
| 2 | Bug 1 + Bug 2 の修正と再現テスト（`set` の仕様確定を含む） | 1 |
| 3 | モジュール分割 A（機械的移動のみ） | 1 |
| 4 | B: `possible_block_sizes` 置換 + `fixedbitset` 削除 | 3 |
| 5 | 設計問題 1〜4: 入力検証・`Result` 化・長方形対応・確定値型 | 2, 3 |
| 6 | C/D/E + 設計問題 5〜8 + ドキュメント・依存更新 | 3 |

各PRで `cargo test`（soundness 含む）が通ることを確認してから次へ進む。特に 4 と 5 は推論の等価性が要なので、soundness テストの乱数シードを変えた追加ランで確認するとよい。

## 非目標

- 推論規則の強化（背理法・二択試行など線形推論を超える探索）は本リファクタリングの範囲外。`Indeterminate` の解消率向上は別トピックとして扱う。
- 並列化・SIMD 等の高速化。現状性能で困っていない。
