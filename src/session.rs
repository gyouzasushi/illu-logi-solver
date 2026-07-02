//! 対話層。ユーザーの盤面と操作履歴だけを真実（ground truth）として持つ、
//! [`crate::Solver`] の薄いラッパー。
//!
//! `Session` はソルバの状態を一切保持しない。`hint`/`deduce`/`judge` を
//! 呼ぶたびに、現在の盤面から [`crate::Solver::with_grid`] で使い捨ての
//! `Solver` を毎回新品で構築して問い合わせる。フルsolveが数msという前提の
//! もと、対話1操作ごとに全体を再構築しても実用上問題ない
//! （詳細はリポジトリの REFACTORING_PLAN.md 参照）。
//!
//! この設計により、`Solver` に `set`/`rollback` があった頃の2つのバグ
//! （`Unconfirmed` への巻き戻しでセグメント情報が残留する／`solve` 消化後の
//! 書き込みが伝播しない）は「発生し得ない設計」として解消される。

use crate::{solver::validate_constraints, Hint, Solver, SolverError, State};

/// `Session::set` 1回分の記録。`undo`/`rollback` の再生に使う。
#[derive(Debug, Clone, Copy)]
struct Edit {
    i: usize,
    j: usize,
    state: State,
}

/// ユーザーとの対話用の薄い層。
///
/// 保持するのは制約・盤面 `Vec<Vec<State>>`・操作履歴のみ。ソルバ状態は
/// 一切持たず、推論が必要になるたびに使い捨ての `Solver` を構築する。
pub struct Session {
    constraints: [Vec<Vec<usize>>; 2],
    grid: Vec<Vec<State>>,
    history: Vec<Edit>,
}

impl Session {
    /// 制約から空盤面のセッションを作る（現状は正方形前提）。
    ///
    /// `Solver::new` と同じ検証（ブロックサイズ 0 の拒否、
    /// `sum(blocks) + (blocks.len() - 1) <= n` ）を行う。
    pub fn new(constraints: [Vec<Vec<usize>>; 2]) -> Result<Self, SolverError> {
        let n = validate_constraints(&constraints)?;
        let grid = vec![vec![State::Unconfirmed; n]; n];
        Ok(Self {
            constraints,
            grid,
            history: Vec::new(),
        })
    }

    fn n(&self) -> usize {
        self.grid.len()
    }

    /// 盤面 `(i, j)` を `state` に書き換え、履歴に記録する。
    ///
    /// 盤面配列の書き換えと履歴への記録のみ。`State::Unconfirmed` への
    /// 巻き戻しもただの配列操作なので常に正しい。
    pub fn set(&mut self, i: usize, j: usize, state: State) {
        self.grid[i][j] = state;
        self.history.push(Edit { i, j, state });
    }

    /// 盤面 `(i, j)` の現在の状態。
    pub fn state(&self, i: usize, j: usize) -> State {
        self.grid[i][j]
    }

    /// 現盤面を種にした使い捨てソルバを構築する。
    ///
    /// `Session` は構築時（`new`）に制約を検証済みで、`grid` は常に
    /// その制約と同じ次元に保たれる（`rebuild_grid` 参照）。そのためここでの
    /// `with_grid` の失敗は `Session` 自体の不変条件違反であり、`expect` で
    /// 検出してよい。
    fn solver(&self) -> Solver {
        Solver::with_grid(self.constraints.clone(), &self.grid)
            .expect("Session の盤面は常に制約の次元と整合するように保たれる")
    }

    /// 現盤面から、最も安い推論ステップ1件を非破壊で求める。
    ///
    /// 毎回 `Solver::with_grid` で新品のソルバを構築して `Solver::hint` に
    /// 委譲するため、直前の `hint`/`deduce` 呼び出しの影響を受けない。
    pub fn hint(&self) -> Result<Option<Hint>, SolverError> {
        self.solver().hint()
    }

    /// 現盤面から確定できる範囲まで推論し、結果の盤面を返す。
    ///
    /// 内部で新品のソルバに対して `solve` を走らせるだけで、`Session` の
    /// 盤面・履歴は一切変更しない。一意に確定しきれない場合も、そこまでで
    /// 確定した部分盤面を `Ok` で返す。全確定したかどうかは、返った盤面に
    /// `State::Unconfirmed` が残っているかで判定できる。`Err` になるのは
    /// 矛盾（`SolverError::Contradiction`）のみ（制約自体の検証エラーは
    /// `Session::new` の時点で弾かれているため、ここでは起こり得ない）。
    pub fn deduce(&self) -> Result<Vec<Vec<State>>, SolverError> {
        let mut solver = self.solver();
        match solver.solve() {
            // Indeterminate でもソルバ内部には部分確定が残っているので読み出す。
            Ok(()) | Err(SolverError::Indeterminate) => {}
            Err(e) => return Err(e),
        }
        let n = self.n();
        Ok((0..n)
            .map(|i| (0..n).map(|j| solver.state(i, j)).collect())
            .collect())
    }

    /// 現盤面が制約を満たしているかどうか。
    pub fn judge(&self) -> bool {
        self.solver().judge()
    }

    fn rebuild_grid(&mut self) {
        let n = self.n();
        self.grid = vec![vec![State::Unconfirmed; n]; n];
        for edit in &self.history {
            self.grid[edit.i][edit.j] = edit.state;
        }
    }

    /// これまでの `set` の回数（＝現在の履歴件数）。
    ///
    /// [`Session::rollback`] に渡す `t` の基準になる。
    pub fn turn(&self) -> usize {
        self.history.len()
    }

    /// 直近の `set` を1回取り消す。
    pub fn undo(&mut self) {
        self.history.pop();
        self.rebuild_grid();
    }

    /// 履歴を先頭 `t` 件に切り詰め、盤面を再構築する。
    ///
    /// 現在の履歴件数は [`Session::turn`] で取得できる。`t` がそれ以上なら
    /// 何もしない（`Vec::truncate` と同じ挙動）。
    pub fn rollback(&mut self, t: usize) {
        self.history.truncate(t);
        self.rebuild_grid();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Bug 1・Bug 2 の再現シナリオ（REFACTORING_PLAN.md「確認済みバグ」参照）は
    // 公開APIだけで再現できるため tests/lib.rs に仕様テストとして置く。
    // ここではモジュール内部の細かい積み木（undo/rollback の履歴再生）だけ見る。
    #[test]
    fn undo_and_rollback_replay_history() {
        let mut session = Session::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]).unwrap();
        session.set(0, 0, State::Black);
        session.set(0, 1, State::White);
        session.set(1, 0, State::White);

        session.undo();
        assert_eq!(session.state(1, 0), State::Unconfirmed);
        assert_eq!(session.state(0, 0), State::Black);

        session.set(1, 0, State::White);
        session.set(1, 1, State::Black);
        assert!(session.judge());

        session.rollback(1);
        assert_eq!(session.state(0, 0), State::Black);
        assert_eq!(session.state(0, 1), State::Unconfirmed);
        assert_eq!(session.state(1, 0), State::Unconfirmed);
        assert_eq!(session.state(1, 1), State::Unconfirmed);
    }
}
