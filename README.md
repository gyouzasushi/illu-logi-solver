# illu-logi-solver

イラストロジック（ノノグラム、お絵かきロジック）のルールベースソルバです。
各行・各列の「黒マスの連続長の並び」という制約から、人間が使う8つの
基本推論規則を行・列交互に適用して盤面を埋めます。

- 30×30程度のパズルなら数msでフルソルブできる速度を持ちます。
- 背理法や二択試行のような線形推論を超える探索は行いません（非目標）。
  そのぶん、確定した各マスについて「なぜそう言えるか（根拠の規則）」を
  常に説明できます。人間向けヒント機能はこの資産の上に成り立っています。
- 一意に解けないパズル（複数の解があり得る）は `Indeterminate` として
  区別され、その時点までに確定した部分盤面はそのまま読み出せます。

## インストール

```toml
[dependencies]
illu-logi-solver = { path = "." } # または git 依存など
```

## 制約の与え方

制約は `[Vec<Vec<usize>>; 2]` で、`[行の制約, 列の制約]` の順に並べます。
各要素はその行・列の「黒マスの連続長」を左（上）から順に並べたものです。
空リストはその行・列が全マス白であることを表します。

```rust
use illu_logi_solver::Solver;

// 5行5列。行は上から、列は左から。
let constraints = [
    // 行の制約（5本）
    vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
    // 列の制約（5本）
    vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
];
let mut solver = Solver::new(constraints).unwrap();
```

高さ（行の本数）と幅（列の本数）は独立に決まります
（`height = constraints[0].len()`, `width = constraints[1].len()`）。
正方形である必要はなく、H×Wの長方形パズルをそのまま扱えます。

```rust
use illu_logi_solver::Solver;

// 2行3列の長方形パズルも問題なく作れる。
let constraints = [
    vec![vec![3], vec![]],           // 行2本
    vec![vec![1], vec![1], vec![1]], // 列3本
];
assert!(Solver::new(constraints).is_ok());
```

制約は構築時に検証されます。ブロックサイズ0は拒否され、
`sum(blocks) + (blocks.len() - 1) <= 線長` を満たさない（どう詰めても
線に収まらない）制約も拒否されます。違反すると `Solver::new` は
`Err(SolverError::InvalidBlockSize | SolverError::ConstraintTooLong)`
を返します。

## `Solver` と `Session` の使い分け

このクレートは推論コアと対話層の2層構成です。

### `Solver`: 速度優先の推論エンジン

制約（＋任意で初期盤面）を受け取って推論するだけの、不変入力のエンジンです。
外部から盤面を書き換える手段を持たず、構築後は一方向に確定が進みます。

- `Solver::new(constraints)`: 空盤面から構築。
- `Solver::with_grid(constraints, grid)`: 既知のマスを種にして構築
  （盤面の次元は制約と一致している必要があります）。
- `solve()`: 確定できる限り推論し尽くす。一意に解ければ `Ok(())`、
  矛盾があれば `Err(SolverError::Contradiction | SolverError::NoPlacement)`、
  一意に解けなければ `Err(SolverError::Indeterminate)`（このときも
  部分確定した盤面は `state(i, j)` で読める）。
- `advance()`: 最も安い推論ステップを1件だけ進める。可視化やステップ実行に。
- `hint()`: 現盤面から次の1手とその根拠を非破壊で求める。
- `state(i, j)` / `judge()`: 現在のマスの状態 / 制約を満たしているか。

```rust
use illu_logi_solver::Solver;

let mut solver = Solver::new([
    vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
    vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
])
.unwrap();
solver.solve().expect("この5x5は一意に解ける");
assert!(solver.judge());
```

30×30程度ならフルソルブが数msで終わるため、対話的な用途（後述の
`Session`）は「1操作ごとに `Solver` を毎回ゼロから作り直す」という
単純な方針を取っています。

### `Session`: ユーザーとの対話用の薄い層

ユーザーが盤面を埋めながらヒントや間違いチェックを受ける、といった
対話的な用途向けのラッパーです。`Session` 自身はソルバの状態を一切持たず、
ユーザーの盤面 `Vec<Vec<State>>` と操作履歴だけを真実（ground truth）として
持ちます。`hint`/`deduce`/`judge`/`mistakes` を呼ぶたびに、現在の盤面から
使い捨ての `Solver` を新品で構築して問い合わせます。

- `set(i, j, state)`: 盤面を書き換え、履歴に記録する
  （`State::Unconfirmed` への巻き戻しも含めて常に正しく動く）。
- `hint()`: 次の1手とその根拠を非破壊で求める。
- `deduce()`: 現盤面から確定できる範囲まで推論した結果の盤面を返す
  （`Session` 自体の盤面・履歴は変更しない）。
- `judge()`: 現盤面が制約を満たしているか。
- `mistakes()`: 制約だけから求めた正解と現盤面を突き合わせ、
  食い違う確定セルの座標を返す（ユーザーの誤記入がヒントの前提に
  混ざらない、独立した間違い検出）。
- `undo()` / `rollback(t)`: 直近の `set` を取り消す / 履歴を `t` 件まで
  巻き戻す。

```rust
use illu_logi_solver::{Session, State};

let mut session = Session::new([
    vec![vec![2], vec![]],
    vec![vec![1], vec![1]],
])
.unwrap();

session.set(0, 0, State::Black);
session.set(0, 1, State::Black);
session.set(1, 0, State::White);
session.set(1, 1, State::White);

assert!(session.judge());
assert_eq!(session.mistakes().unwrap(), Vec::new());
```

## ヒント（`hint`）の中身

`hint()`/`Session::hint()` が返す `Hint` は、確定操作 `action`
（どこを・何色に・なぜ塗れるか）に加えて、その `action` と同じ
スナップショットから読み出した行コンテキスト（`possible_ids`:
セルごとの候補ブロックID範囲、`blocks`: ブロックごとの配置可能範囲と
サイズ）を持ちます。これらを組み合わせれば「なぜこのマスが確定するのか」
を人間向けに説明する文言を組み立てられます（実際の文言化はUI側の仕事とし、
このクレートは生データだけを提供します）。

## テスト

```sh
cargo test
```

`tests/soundness.rs` は実在する盤面から生成した制約に対して、
誤確定や偽の矛盾が出ないことを総当たりで検証します
（4×4全列挙、5×5/7×7/10×10ランダム、長方形5×8/7×3ランダム）。
`tests/completeness.rs` は8規則による行推論の完全性（全配置列挙との比較）
を回帰的に検証します。詳しい設計判断は `REFACTORING_PLAN.md` を参照してください。
