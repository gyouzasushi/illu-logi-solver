use crate::{
    line::{Determined, State},
    operation::Operation,
    solver::Axis,
};
use thiserror::Error;

/// セル書き込みの出所。
///
/// `Operation` は8つの行内推論規則だけを表すのに対し、`Cause` は
/// 「そのセルがなぜ書き換わったか」を表す。行内の推論なら `Operation` を
/// そのまま包み、直交する行/列からの伝播なら発生源 `(axis, i)` を持つ
/// `Propagation` になる。矛盾エラーの `by` はこちらを持つことで、
/// 行内規則と伝播が型として混ざらない
/// （`Hint`/`Action.by` は常に `Operation` のみを持つ）。
#[derive(Clone, Copy, Debug)]
pub enum Cause {
    Operation(Operation),
    Propagation { axis: Axis, i: usize },
}

#[derive(Debug)]
pub(crate) enum LineError {
    Contradiction(usize, State, Determined, Cause),
    /// ブロック `id` の置き場所がどこにもない（行レベルの矛盾で、
    /// 特定のセルの書き込み衝突ではない）。
    NoPlacement(usize),
}
impl LineError {
    pub(crate) fn to_solver_error(&self, axis: Axis, i: usize) -> SolverError {
        match self {
            LineError::Contradiction(j, current_state, new_state, by) => {
                SolverError::Contradiction {
                    axis,
                    i,
                    j: *j,
                    current_state: *current_state,
                    new_state: State::from(*new_state),
                    by: *by,
                }
            }
            LineError::NoPlacement(id) => SolverError::NoPlacement { axis, i, id: *id },
        }
    }
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("contradiction on {axis:?}[{i}][{j}]: attempt to set {new_state:?} by {by:?}, but {current_state:?} is already set.")]
    Contradiction {
        axis: Axis,
        i: usize,
        j: usize,
        current_state: State,
        new_state: State,
        by: Cause,
    },
    #[error("could not find a solution: there might be multiple possible solutions.")]
    Indeterminate,
    #[error("no valid placement for block {id} on {axis:?}[{i}]: it does not fit anywhere given the current cells.")]
    NoPlacement { axis: Axis, i: usize, id: usize },
    #[error("{axis:?}[{i}] contains a block of size 0, which is not a valid constraint.")]
    InvalidBlockSize { axis: Axis, i: usize },
    #[error(
        "{axis:?}[{i}] cannot fit in a line of length {line_len}: blocks require at least sum(blocks) + (blocks.len() - 1) cells."
    )]
    ConstraintTooLong {
        axis: Axis,
        i: usize,
        line_len: usize,
    },
    #[error("grid has {actual} rows but constraints expect {expected} rows.")]
    GridHeightMismatch { expected: usize, actual: usize },
    #[error("grid row {i} has {actual} cells but constraints expect {expected}.")]
    GridWidthMismatch {
        i: usize,
        expected: usize,
        actual: usize,
    },
}
