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
    /// 行内の8規則のいずれかによる書き込み。
    Operation(Operation),
    /// 直交する行・列から伝播した書き込み。`axis`/`i` は伝播元の行の座標
    /// （書き込み先ではない）で、書き込み先自体はこの `Cause` を持つ
    /// `SolverError::Contradiction` の `axis`/`i`/`j` が表す。
    Propagation {
        /// 伝播元の行の向き。
        axis: Axis,
        /// 伝播元の行番号。
        i: usize,
    },
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

/// [`Solver`](crate::Solver)/[`Session`](crate::Session) の失敗を表す。
///
/// 構築時の入力検証（`InvalidBlockSize`/`ConstraintTooLong`/
/// `GridHeightMismatch`/`GridWidthMismatch`）と、推論中に見つかる矛盾
/// （`Contradiction`/`NoPlacement`/`Indeterminate`）の2系統がある。
#[derive(Debug, Error)]
pub enum SolverError {
    /// セル `(axis, i, j)`（`axis` 上の `i` 本目の行の `j` 番目のセル）を
    /// `by` の根拠で `new_state` にしようとしたが、既に矛盾する
    /// `current_state` が入っていた。座標は「矛盾を検出した行」基準
    /// （`axis.orthogonal()` ではなく `axis` 自身）に統一している
    /// （REFACTORING_PLAN.md Bug 3）。
    #[error(
        "contradiction on {axis:?}[{i}][{j}]: attempt to set {new_state:?} by {by:?}, but {current_state:?} is already set."
    )]
    Contradiction {
        /// 矛盾を検出した行の向き。
        axis: Axis,
        /// 矛盾を検出した行番号。
        i: usize,
        /// その行内での矛盾セルの位置。
        j: usize,
        /// 書き込み前の状態。
        current_state: State,
        /// 書き込もうとした状態。
        new_state: State,
        /// 書き込みの根拠。
        by: Cause,
    },
    /// 矛盾なく推論を尽くしたが、一意に確定しきれなかった（複数の解が
    /// あり得る）。[`Solver::solve`](crate::Solver::solve) 参照。
    #[error("could not find a solution: there might be multiple possible solutions.")]
    Indeterminate,
    /// `axis` 上の `i` 本目の行で、ブロック `id` の置き場所がどこにもない。
    /// 特定のセルの書き込み衝突ではなく行レベルの矛盾なので、`Contradiction`
    /// とは別の variant として区別している。
    #[error(
        "no valid placement for block {id} on {axis:?}[{i}]: it does not fit anywhere given the current cells."
    )]
    NoPlacement {
        /// 矛盾を検出した行の向き。
        axis: Axis,
        /// 矛盾を検出した行番号。
        i: usize,
        /// 置き場所がなかったブロックのID（0始まり）。
        id: usize,
    },
    /// `axis` 上の `i` 本目の制約にサイズ0のブロックが含まれていた
    /// （不正な入力）。
    #[error("{axis:?}[{i}] contains a block of size 0, which is not a valid constraint.")]
    InvalidBlockSize {
        /// 不正な制約を持つ行の向き。
        axis: Axis,
        /// 不正な制約を持つ行番号。
        i: usize,
    },
    /// `axis` 上の `i` 本目の制約が、線の長さ `line_len` に収まらない
    /// （`sum(blocks) + (blocks.len() - 1) > line_len`）。
    #[error(
        "{axis:?}[{i}] cannot fit in a line of length {line_len}: blocks require at least sum(blocks) + (blocks.len() - 1) cells."
    )]
    ConstraintTooLong {
        /// 収まらない制約を持つ行の向き。
        axis: Axis,
        /// 収まらない制約を持つ行番号。
        i: usize,
        /// その行の実際の長さ。
        line_len: usize,
    },
    /// [`Solver::with_grid`](crate::Solver::with_grid) に渡した `grid` の
    /// 行数が制約の高さと一致しない。
    #[error("grid has {actual} rows but constraints expect {expected} rows.")]
    GridHeightMismatch {
        /// 制約が期待する高さ（行数）。
        expected: usize,
        /// 実際に渡された `grid` の行数。
        actual: usize,
    },
    /// [`Solver::with_grid`](crate::Solver::with_grid) に渡した `grid` の
    /// `i` 行目の列数が制約の幅と一致しない。
    #[error("grid row {i} has {actual} cells but constraints expect {expected}.")]
    GridWidthMismatch {
        /// 列数が食い違った行番号。
        i: usize,
        /// 制約が期待する幅（列数）。
        expected: usize,
        /// 実際に渡された `grid` の `i` 行目の列数。
        actual: usize,
    },
}
