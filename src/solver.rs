use crate::{
    error::{Cause, SolverError},
    line::{HintBlock, Line, State},
    operation::Operation,
};
use std::{collections::VecDeque, ops::Range};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Axis {
    Row,
    Column,
}
impl Axis {
    fn orthogonal(&self) -> Self {
        match self {
            Axis::Row => Axis::Column,
            Axis::Column => Axis::Row,
        }
    }
}
impl From<Axis> for usize {
    fn from(axis: Axis) -> Self {
        match axis {
            Axis::Row => 0,
            Axis::Column => 1,
        }
    }
}

/// 制約を検証し、盤面の高さ・幅 `(height, width)` を返す。
///
/// 高さは行の本数（`constraints[Row].len()`）、幅は列の本数
/// （`constraints[Column].len()`）で、両者が一致する必要はない
/// （長方形の盤面を許容する）。行の `Line` は幅、列の `Line` は高さを
/// 自分の線長として持つ。
///
/// 検証内容: 各行・各列の制約についてブロックサイズ 0 を拒否し、
/// 行なら `sum(blocks) + (blocks.len() - 1) <= width`、
/// 列なら同様に `<= height` を要求する。
pub(crate) fn validate_constraints(
    constraints: &[Vec<Vec<usize>>; 2],
) -> Result<(usize, usize), SolverError> {
    let height = constraints[Axis::Row as usize].len();
    let width = constraints[Axis::Column as usize].len();
    for (i, blocks) in constraints[Axis::Row as usize].iter().enumerate() {
        validate_line_constraint(Axis::Row, i, blocks, width)?;
    }
    for (i, blocks) in constraints[Axis::Column as usize].iter().enumerate() {
        validate_line_constraint(Axis::Column, i, blocks, height)?;
    }
    Ok((height, width))
}

fn validate_line_constraint(
    axis: Axis,
    i: usize,
    blocks: &[usize],
    line_len: usize,
) -> Result<(), SolverError> {
    if blocks.contains(&0) {
        return Err(SolverError::InvalidBlockSize { axis, i });
    }
    let min_len = blocks.iter().sum::<usize>() + blocks.len().saturating_sub(1);
    if min_len > line_len {
        return Err(SolverError::ConstraintTooLong { axis, i, line_len });
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct Action {
    pub axis: Axis,
    pub i: usize,
    pub range: Range<usize>,
    pub state: State,
    pub by: Operation,
}

/// 確定の根拠ブロックまで含む、自己完結したヒント。
///
/// `action` に加えて、その `action` を算出したのと **同一のスナップショット**
/// （`hint()` 内部で作る `Line` の clone）から読み出した行コンテキストを持つ。
/// `possible_ids`/`blocks` はいずれもそのスナップショット由来なので、常に
/// `action` と矛盾なく組み合わせて説明文を組み立てられる。人間向けの文言化
/// （どのセルがなぜ塗られるかの説明文の組み立て）は `Session`/UI 層の仕事とし、
/// ここでは行の生データだけを持つ（REFACTORING_PLAN.md D項）。
#[derive(Debug, Clone)]
pub struct Hint {
    pub action: Action,
    /// `action.range` と同じ並びで、各セルの候補ブロックID範囲。
    /// ヒント算出と同一スナップショット上で読み出すため、常に `action` と整合する。
    pub possible_ids: Vec<Range<usize>>,
    /// `action.axis`/`action.i` が指す行の、全ブロックの配置可能範囲とサイズ。
    /// `possible_ids` と同じスナップショットから読み出す。詳細は [`HintBlock`]。
    pub blocks: Vec<HintBlock>,
}

/// 制約（＋任意で初期盤面）を受け取って推論するだけの、不変入力の推論エンジン。
///
/// 構築後に外部から盤面を書き換える手段は持たない（`possible_block_ids` が
/// 狭まる一方向にしか更新されないという内部不変条件が構築後に壊れないことを
/// 保証するための設計）。ユーザーが盤面を埋めながらヒントや矛盾チェックを
/// 受けるような対話的な用途には、この `Solver` を毎回使い捨てで組み立てる
/// 薄い層である [`crate::Session`] を使うこと。
pub struct Solver {
    height: usize,
    width: usize,
    constraints: [Vec<Vec<usize>>; 2],
    lines: [Vec<Line>; 2],
    queue: VecDeque<(Axis, usize)>,
    /// `(axis, i)` が現在 `queue` に入っているかどうか（設計問題6）。
    /// `advance` は処理済みの行から複数の直交行へ伝播するたびに
    /// `push_front((axis.orthogonal(), j))` するが、同じ `(axis, j)` が
    /// まだキューに残っている間に何度も積むと無駄な再走査が増える。
    /// この重複投入を防ぐためのフラグ。`queue` に積むときに立て、
    /// その行が完全に消化されて `pop_front` されるときに下ろす。
    in_queue: [Vec<bool>; 2],
    turn_count: usize,
}
impl Solver {
    /// `axis` 方向の `Line` の本数。行なら高さ、列なら幅。
    fn line_count(&self, axis: Axis) -> usize {
        match axis {
            Axis::Row => self.height,
            Axis::Column => self.width,
        }
    }

    /// 制約からソルバを構築する。
    ///
    /// 入力検証: 各行・列の制約についてブロックサイズ 0 を拒否し、
    /// `sum(blocks) + (blocks.len() - 1) <= 線長` を要求する
    /// （満たさない制約はどう埋めても盤面に収まらない）。
    pub fn new(constraints: [Vec<Vec<usize>>; 2]) -> Result<Self, SolverError> {
        let (height, width) = validate_constraints(&constraints)?;
        let lines = [
            constraints[Axis::Row as usize]
                .iter()
                .map(|constraint| Line::new(width, constraint.clone()))
                .collect(),
            constraints[Axis::Column as usize]
                .iter()
                .map(|constraint| Line::new(height, constraint.clone()))
                .collect(),
        ];
        let queue = [Axis::Row, Axis::Column]
            .iter()
            .flat_map(|&axis| {
                let count = if axis == Axis::Row { height } else { width };
                (0..count).map(move |i| (axis, i))
            })
            .collect();
        // 初期状態では全 (axis, i) がちょうど1回ずつ queue に入っている。
        let in_queue = [vec![true; height], vec![true; width]];
        Ok(Self {
            height,
            width,
            constraints,
            lines,
            queue,
            in_queue,
            turn_count: 0,
        })
    }

    /// `new` 同様に構築したうえで、`grid` の `Unconfirmed` 以外のセルを
    /// 確定済みの種として行・列両方の `Line` に流し込む。
    ///
    /// 新品の `Line` に前進方向で流し込むだけなので `possible_block_ids` の
    /// 単調性は壊れない。矛盾検出はここでは行わず、後続の `solve`/`advance`/
    /// `hint` に委ねる。制約の検証に加え、`grid` の次元が制約の次元
    /// （`height` 行 × `width` 列）と一致することも検証する。
    pub fn with_grid(
        constraints: [Vec<Vec<usize>>; 2],
        grid: &[Vec<State>],
    ) -> Result<Self, SolverError> {
        let mut solver = Self::new(constraints)?;
        if grid.len() != solver.height {
            return Err(SolverError::GridHeightMismatch {
                expected: solver.height,
                actual: grid.len(),
            });
        }
        for (i, row) in grid.iter().enumerate() {
            if row.len() != solver.width {
                return Err(SolverError::GridWidthMismatch {
                    i,
                    expected: solver.width,
                    actual: row.len(),
                });
            }
        }
        for (i, row) in grid.iter().enumerate() {
            for (j, &state) in row.iter().enumerate() {
                if state != State::Unconfirmed {
                    solver.lines[Axis::Row as usize][i].set_state(j, state);
                    solver.lines[Axis::Column as usize][j].set_state(i, state);
                }
            }
        }
        Ok(solver)
    }

    pub fn solve(&mut self) -> Result<(), SolverError> {
        while self.advance()?.is_some() {}
        if self.lines[Axis::Row as usize]
            .iter()
            .flat_map(|line| line.cells.iter().map(|cell| cell.state))
            .any(|state| matches!(state, State::Unconfirmed))
        {
            Err(SolverError::Indeterminate)
        } else {
            Ok(())
        }
    }

    pub fn advance(&mut self) -> Result<Option<Action>, SolverError> {
        while let Some(&(axis, i)) = self.queue.front() {
            if let Some((range, state, by)) = self.lines[axis as usize][i]
                .advance()
                .map_err(|err| err.to_solver_error(axis, i))?
            {
                for j in range.clone() {
                    // 矛盾エラーの座標は「矛盾を検出した行」基準に統一する
                    // （REFACTORING_PLAN.md Bug 3）。ここで書き込み先は
                    // axis.orthogonal() 上の行 j なので、失敗時の報告も
                    // (axis.orthogonal(), j) を使う。伝播の発生源
                    // (axis, i) は Cause::Propagation のペイロードとして残す。
                    let orthogonal = axis.orthogonal();
                    self.lines[orthogonal as usize][j]
                        .update(i..i + 1, state, Cause::Propagation { axis, i })
                        .map_err(|err| err.to_solver_error(orthogonal, j))?;
                    // 設計問題6: 同じ (orthogonal, j) がまだキューに残っている間は
                    // 積み直さない（dedup）。無駄な再走査を避けるだけで、
                    // 積むかどうかに関わらず上の update はキューの有無と独立に
                    // 必ず実行する必要がある（cell の状態自体は毎回反映すべきため）。
                    if !self.in_queue[orthogonal as usize][j] {
                        self.in_queue[orthogonal as usize][j] = true;
                        self.queue.push_front((orthogonal, j));
                    }
                }
                self.turn_count += 1;
                return Ok(Some(Action {
                    axis,
                    i,
                    range,
                    state: state.into(),
                    by,
                }));
            } else {
                self.queue.pop_front().unwrap();
                self.in_queue[axis as usize][i] = false;
            }
        }
        Ok(None)
    }

    /// 現盤面から、最も安い推論ステップ1件を非破壊で求める。
    ///
    /// # `advance` と併用したときの挙動（設計問題5）
    ///
    /// `advance` は1回の呼び出しにつき `Line` のキューから1件しか消化しない。
    /// ところが1回の規則発火（`Line::STEPS` の1関数の実行）は複数件を
    /// キューに積むことがあるため、`advance` を繰り返す過程で、まだ消化されて
    /// いない「残留キュー」を持つ行が生まれ得る。この状態で `hint` を呼ぶと、
    /// 以下の順で結果を決める:
    ///
    /// 1. **まず全行を走査し、残留キューを持つ行があれば、その中で最初に
    ///    見つかった行の最も古い保留項目（`queue.front()`）を返す**。
    ///    複数の行に残留があるときは `axis`（Row → Column）→ `i` 昇順で
    ///    決める（`Line` は行ごとの到着順しか保持しないため、行をまたいだ
    ///    真の時系列は追跡していない）。
    /// 2. 残留が1件もなければ、通常どおり `Line::STEPS` を安い順に全行へ
    ///    試し、最初に見つかった結果を返す（従来の挙動）。
    ///
    /// 残留を優先させないと、コストの高い規則が生成した残留項目と、
    /// 別の行でこれから安い規則が見つける結果とが `Line` のFIFOキュー内で
    /// 混ざり、「最も安いステップから返す」という保証が崩れる
    /// （residual はすでに判明済みの推論なので、探索し直す前に返すのが自然）。
    /// `Session` 経由（呼び出しのたびに新品の `Solver` を使い捨てる）では
    /// `advance` を呼ばないため、この経路自体に入らない。
    pub fn hint(&self) -> Result<Option<Hint>, SolverError> {
        for &axis in &[Axis::Row, Axis::Column] {
            for i in 0..self.line_count(axis) {
                let line = &self.lines[axis as usize][i];
                if let Some((range, state, by)) = line.queue.front().cloned() {
                    let possible_ids = range.clone().map(|j| line.possible_id(j)).collect();
                    let blocks = line.hint_blocks();
                    let action = Action {
                        axis,
                        i,
                        range,
                        state: state.into(),
                        by,
                    };
                    return Ok(Some(Hint {
                        action,
                        possible_ids,
                        blocks,
                    }));
                }
            }
        }

        for step_idx in 0..Line::STEPS.len() {
            for &axis in &[Axis::Row, Axis::Column] {
                for i in 0..self.line_count(axis) {
                    let mut line = self.lines[axis as usize][i].clone();
                    line.update_possible_id()
                        .map_err(|e| e.to_solver_error(axis, i))?;
                    Line::STEPS[step_idx](&mut line);
                    if let Some((range, state, by)) = line.queue.pop_front() {
                        // ヒント算出に使った同じスナップショット（この clone）から候補IDを読み出す。
                        // 別呼び出し・別スナップショットを挟まないため、常に action と整合する。
                        let possible_ids = range.clone().map(|j| line.possible_id(j)).collect();
                        let blocks = line.hint_blocks();
                        let action = Action {
                            axis,
                            i,
                            range,
                            state: state.into(),
                            by,
                        };
                        return Ok(Some(Hint {
                            action,
                            possible_ids,
                            blocks,
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    pub fn turn(&self) -> usize {
        self.turn_count
    }

    pub fn judge(&self) -> bool {
        for &axis in &[Axis::Row, Axis::Column] {
            for i in 0..self.line_count(axis) {
                let v = self.lines[axis as usize][i]
                    .segments_black
                    .segments()
                    .iter()
                    .map(|(l, r)| r - l)
                    .collect::<Vec<_>>();
                if v != self.constraints[axis as usize][i] {
                    return false;
                }
            }
        }
        true
    }

    /// セル `(i, j)` の現在の状態。
    ///
    /// 行の `Line` と列の `Line` は同じセルを独立に持っているため、内部
    /// 不変条件として両者は常に一致するはずである（設計問題7）。ただし
    /// これはあくまで自己診断であり、呼び出し側の入力ミスでは起こり得ない
    /// 種類のバグ（ソルバ内部の実装ミス）でしか崩れない。素の `getter` を
    /// リリースビルドで panic させたくないため `debug_assert_eq!` にとどめ、
    /// 不一致時はリリースビルドでは行側を正としてそのまま返す。
    pub fn state(&self, i: usize, j: usize) -> State {
        debug_assert_eq!(
            self.lines[Axis::Row as usize][i].cells[j].state,
            self.lines[Axis::Column as usize][j].cells[i].state
        );
        self.lines[Axis::Row as usize][i].cells[j].state
    }
}

impl Solver {
    /// 1マス幅の区切り線（5マスごとに空白を挟んだ `-` の並び）。
    fn separator_line(width: usize) -> String {
        let mut line = String::new();
        for x in 0..width {
            if x > 0 && x % 5 == 0 {
                line.push(' ');
            }
            line.push('-');
        }
        line
    }

    /// 1盤面をテキスト行のリストとして描画する。`cell(y, x)` はセル
    /// `(y, x)` の表示文字列（1文字幅を想定）を返す。5行・5列ごとに
    /// 区切り線／区切り文字を挟む。`Display` と [`Solver::debug_display`]
    /// はどちらもこのヘルパに畳んでいるので、盤面の描き方（罫線の間隔など）
    /// を変えるときはここ1箇所を直せばよい。
    fn render_board(&self, cell: impl Fn(usize, usize) -> String) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.height);
        for y in 0..self.height {
            if y > 0 && y % 5 == 0 {
                lines.push(Self::separator_line(self.width));
            }
            let mut line = String::new();
            for x in 0..self.width {
                if x > 0 && x % 5 == 0 {
                    line.push('|');
                }
                line.push_str(&cell(y, x));
            }
            lines.push(line);
        }
        lines
    }

    /// セル `(y, x)` の素の表示文字列（`.`/`x`/`o`）。
    fn plain_cell(&self, y: usize, x: usize) -> String {
        match self.lines[Axis::Row as usize][y].cells[x].state {
            State::Unconfirmed => ".".to_string(),
            State::White => "x".to_string(),
            State::Black => "o".to_string(),
        }
    }

    /// セル `(y, x)` の表示文字列。黒セルは確定済みブロックIDが分かれば
    /// それを数字で表示し（`Line::confirmed_id`）、分からなければ `o`。
    fn cell_with_confirmed_id(state: State, confirmed_id: Option<usize>) -> String {
        match state {
            State::Unconfirmed => ".".to_string(),
            State::White => "x".to_string(),
            State::Black => confirmed_id.map_or_else(|| "o".to_string(), |id| id.to_string()),
        }
    }

    /// 3面併記のデバッグ表示: 素の盤面、列 `Line` 視点で確定ブロックIDを
    /// 添えた盤面、行 `Line` 視点で確定ブロックIDを添えた盤面を横に並べる。
    /// `Display`（[`std::fmt::Display`] 実装）は素の盤面だけを描く簡素な
    /// 表示なので、行・列どちらの視点で見てもブロックIDが一致しているか
    /// （内部不変条件の目視確認）などデバッグ用途にはこちらを使う。
    pub fn debug_display(&self) -> String {
        let plain = self.render_board(|y, x| self.plain_cell(y, x));
        let by_column = self.render_board(|y, x| {
            let line = &self.lines[Axis::Column as usize][x];
            Self::cell_with_confirmed_id(line.cells[y].state, line.confirmed_id(y))
        });
        let by_row = self.render_board(|y, x| {
            let line = &self.lines[Axis::Row as usize][y];
            Self::cell_with_confirmed_id(line.cells[x].state, line.confirmed_id(x))
        });

        let mut out = String::new();
        for ((row1, row2), row3) in plain.iter().zip(&by_column).zip(&by_row) {
            out.push_str(row1);
            out.push_str("  ");
            out.push_str(row2);
            out.push_str("  ");
            out.push_str(row3);
            out.push('\n');
        }
        out
    }
}

impl std::fmt::Display for Solver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for line in self.render_board(|y, x| self.plain_cell(y, x)) {
            writeln!(f, "{line}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // 設計問題5の再現・回帰テスト（REFACTORING_PLAN.md）: 1回の規則発火
    // （`Line::STEPS` の1関数）が複数件をキューに積む一方、`advance` は
    // 1件しか消化しない。よって `advance` を繰り返すと、消化されない
    // 残留キューを持つ行が生まれ得る。この状態で `hint` を呼んだとき、
    // STEPS を安い順に探索し直すのではなく、既に判明している残留を
    // 優先して返すことを検証する（`hint` のdocコメント参照）。
    #[test]
    fn hint_prioritizes_residual_queue_over_step_search() {
        let mut solver = Solver::new([
            vec![
                vec![2, 4, 5],
                vec![4, 1, 1],
                vec![3, 3, 1],
                vec![8, 1],
                vec![1, 3, 1, 5],
                vec![2, 2, 4],
                vec![1, 1, 1, 2, 1, 2],
                vec![1, 7, 2],
                vec![1, 1, 3],
                vec![5, 1, 2, 1, 1],
                vec![3, 4, 1],
                vec![1, 1, 1, 1, 1],
                vec![2, 6],
                vec![10, 1],
                vec![7, 2],
            ],
            vec![
                vec![1, 3, 2, 1],
                vec![1, 2, 1, 3, 2],
                vec![3, 2, 2, 2],
                vec![4, 1, 4],
                vec![2, 4, 1, 3],
                vec![2, 1, 2, 1, 2],
                vec![2, 1, 2, 2, 2],
                vec![4, 2, 1, 1],
                vec![3, 4, 2],
                vec![1, 1, 1, 1, 3],
                vec![1, 4, 3],
                vec![2, 3, 3, 1],
                vec![1, 1, 3, 1, 2],
                vec![1, 1, 3, 1],
                vec![2, 1, 1, 5],
            ],
        ])
        .unwrap();

        // hint() 自身と同じ順序（Row→Column, iは昇順）で「先頭に何か
        // 残っている行」を探す。hint() はこれと同じものを返すはず。
        let find_earliest_residual = |solver: &Solver| {
            [Axis::Row, Axis::Column].iter().find_map(|&axis| {
                (0..solver.line_count(axis))
                    .find(|&i| !solver.lines[axis as usize][i].queue.is_empty())
                    .map(|i| (axis, i))
            })
        };

        let mut checked = false;
        let mut saw_multi_item_push = false;
        while solver.advance().unwrap().is_some() {
            // 1回の規則発火が複数件を積むケースが本当に起きていることの確認
            // （起きていなければ、このテストは設計問題5の状況を再現できていない）。
            saw_multi_item_push |= [Axis::Row, Axis::Column].iter().any(|&axis| {
                (0..solver.line_count(axis)).any(|i| solver.lines[axis as usize][i].queue.len() > 1)
            });

            let Some((axis, i)) = find_earliest_residual(&solver) else {
                continue;
            };
            // このLineの実際のキュー先頭（＝既に判明している最も古い保留推論）。
            let expected = solver.lines[axis as usize][i]
                .queue
                .front()
                .cloned()
                .unwrap();
            let hint = solver
                .hint()
                .unwrap()
                .expect("残留キューが存在するので hint は必ず何かを返す");
            assert_eq!(hint.action.axis, axis);
            assert_eq!(hint.action.i, i);
            assert_eq!(hint.action.range, expected.0);
            assert_eq!(hint.action.state, expected.1.into());
            assert_eq!(hint.action.by, expected.2);
            checked = true;
            if saw_multi_item_push {
                break;
            }
        }
        assert!(checked, "残留キューが一度も生まれなかった");
        assert!(
            saw_multi_item_push,
            "この15x15フィクスチャなら advance() の初期段階で残留キュー（1回の規則発火が\
             複数件を積むケース）が生まれるはず。生まれなくなった場合はテストの前提\
             （フィクスチャ）を見直すこと。"
        );
    }
}
