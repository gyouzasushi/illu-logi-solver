use crate::{
    error::SolverError,
    line::{Line, State},
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
#[derive(Debug, Clone)]
pub struct Hint {
    pub action: Action,
    /// `action.range` と同じ並びで、各セルの候補ブロックID範囲。
    /// ヒント算出と同一スナップショット上で読み出すため、常に `action` と整合する。
    pub possible_ids: Vec<Range<usize>>,
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
        Ok(Self {
            height,
            width,
            constraints,
            lines,
            queue,
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
                    self.lines[axis.orthogonal() as usize][j]
                        .update(i..i + 1, state, Operation::SameStateAsOrthogonal)
                        .map_err(|err| err.to_solver_error(axis, i))?;
                    self.queue.push_front((axis.orthogonal(), j));
                }
                self.turn_count += 1;
                return Ok(Some(Action {
                    axis,
                    i,
                    range,
                    state,
                    by,
                }));
            } else {
                self.queue.pop_front().unwrap();
            }
        }
        Ok(None)
    }

    pub fn hint(&self) -> Result<Option<Hint>, SolverError> {
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
                        let action = Action {
                            axis,
                            i,
                            range,
                            state,
                            by,
                        };
                        return Ok(Some(Hint {
                            action,
                            possible_ids,
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

    pub fn state(&self, i: usize, j: usize) -> State {
        assert_eq!(
            self.lines[Axis::Row as usize][i].cells[j].state,
            self.lines[Axis::Column as usize][j].cells[i].state
        );
        self.lines[Axis::Row as usize][i].cells[j].state
    }
}

impl std::fmt::Display for Solver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..self.height {
            if y > 0 && y % 5 == 0 {
                for x in 0..self.width {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                write!(f, "  ")?;
                for x in 0..self.width {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                write!(f, "  ")?;
                for x in 0..self.width {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                writeln!(f)?;
            }
            for x in 0..self.width {
                if x > 0 && x % 5 == 0 {
                    write!(f, "|")?;
                }
                write!(
                    f,
                    "{}",
                    match self.lines[0][y].cells[x].state {
                        State::Unconfirmed => ".".to_string(),
                        State::White => "x".to_string(),
                        State::Black => "o".to_string(),
                    }
                )?
            }
            write!(f, "  ")?;
            for x in 0..self.width {
                if x > 0 && x % 5 == 0 {
                    write!(f, "|")?;
                }
                write!(
                    f,
                    "{}",
                    match self.lines[1][x].cells[y].state {
                        State::Unconfirmed => ".".to_string(),
                        State::White => "x".to_string(),
                        State::Black => {
                            if let Some(id) = self.lines[1][x].confirmed_id(y) {
                                format!("{id}")
                            } else {
                                "o".to_string()
                            }
                        }
                    }
                )?
            }
            write!(f, "  ")?;
            for x in 0..self.width {
                if x > 0 && x % 5 == 0 {
                    write!(f, "|")?;
                }
                write!(
                    f,
                    "{}",
                    match self.lines[0][y].cells[x].state {
                        State::Unconfirmed => ".".to_string(),
                        State::White => "x".to_string(),
                        State::Black => {
                            if let Some(id) = self.lines[0][y].confirmed_id(x) {
                                format!("{id}")
                            } else {
                                "o".to_string()
                            }
                        }
                    }
                )?
            }
            writeln!(f)?;
        }
        Ok(())
    }
}
