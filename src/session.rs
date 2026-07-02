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
    /// 制約から空盤面のセッションを作る。高さ・幅は独立でよい
    /// （`height = constraints[Row].len()`, `width = constraints[Column].len()`）。
    ///
    /// `Solver::new` と同じ検証（ブロックサイズ 0 の拒否、
    /// `sum(blocks) + (blocks.len() - 1) <= 線長` ）を行う。
    pub fn new(constraints: [Vec<Vec<usize>>; 2]) -> Result<Self, SolverError> {
        let (height, width) = validate_constraints(&constraints)?;
        let grid = vec![vec![State::Unconfirmed; width]; height];
        Ok(Self {
            constraints,
            grid,
            history: Vec::new(),
        })
    }

    fn height(&self) -> usize {
        self.constraints[0].len()
    }

    fn width(&self) -> usize {
        self.constraints[1].len()
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
        let (height, width) = (self.height(), self.width());
        Ok((0..height)
            .map(|i| (0..width).map(|j| solver.state(i, j)).collect())
            .collect())
    }

    /// 現盤面が制約を満たしているかどうか。
    pub fn judge(&self) -> bool {
        self.solver().judge()
    }

    /// 制約だけから使い捨てソルバを構築する（`grid` を種にしない点が
    /// [`Session::solver`] と異なる）。制約は `new` で検証済みなので、
    /// ここでの構築失敗は `Session` 自体の不変条件違反として `expect` で
    /// 検出してよい。
    fn solver_from_constraints_only(&self) -> Solver {
        Solver::new(self.constraints.clone())
            .expect("Session の制約は new() で検証済みなので常に構築できる")
    }

    /// 制約だけから求めた正解と現盤面を突き合わせ、食い違う確定セルの
    /// 座標 `(i, j)` を返す。
    ///
    /// `hint`/`deduce` は現盤面（ユーザーの記入を含む）を種にソルバを
    /// 構築するため、ユーザーが誤って置いた黒がそのまま推論の前提に
    /// なり、以後の確定がその誤りを引きずってしまう弱点がある。
    /// `mistakes` はこれを避けるため、`grid` を種にせず**制約のみ**から
    /// 解いた結果を「正解」として使う。
    ///
    /// 比較は次の2条件を両方満たすセルについてのみ行う: ユーザー側が
    /// `State::Unconfirmed`（未記入）でないこと、かつ制約だけの解答側が
    /// `State::Unconfirmed`（まだ確定できていない）でないこと。前者は
    /// 「書いていないマスは間違いではない」ため、後者は「制約だけからは
    /// まだ判断がつかないマスについて、ユーザー側の記入の是非を判定
    /// しようがない」ため対象外にする。
    ///
    /// # 制約だけでは一意に解けない場合の設計判断
    ///
    /// 制約だけの解答が一意に定まらない（`SolverError::Indeterminate`）
    /// 場合でも、`solve` はそこまでに確定できた部分解を返す（`deduce` と
    /// 同じ挙動）。この部分解を使って比較を続ける、つまり「制約だけの
    /// 段階で確定できたセルに限って間違いを検出し、それ以上はあいまいな
    /// ままにする」という best-effort な設計にした。全く判定しない
    /// （`Indeterminate` をそのまま `Err` として伝播する）案も検討したが、
    /// 採用しなかった: `deduce` が既に「部分解を返す」という前例を作って
    /// おり、`mistakes` だけ別挙動にする理由がないこと、また多くの実用的な
    /// 盤面ではパズル全体は一意に解けなくても各行の内部だけで確定できる
    /// マスがそれなりにあり、それだけでも間違いを早期に指摘できる価値が
    /// あるためである。制約自体が矛盾していて解を持たない場合
    /// （`SolverError::Contradiction`/`NoPlacement`）はそのまま `Err` を返す。
    pub fn mistakes(&self) -> Result<Vec<(usize, usize)>, SolverError> {
        let mut solver = self.solver_from_constraints_only();
        match solver.solve() {
            Ok(()) | Err(SolverError::Indeterminate) => {}
            Err(e) => return Err(e),
        }
        let (height, width) = (self.height(), self.width());
        let mut mistakes = Vec::new();
        for i in 0..height {
            for j in 0..width {
                let user = self.grid[i][j];
                let correct = solver.state(i, j);
                if user != State::Unconfirmed && correct != State::Unconfirmed && user != correct {
                    mistakes.push((i, j));
                }
            }
        }
        Ok(mistakes)
    }

    fn rebuild_grid(&mut self) {
        let (height, width) = (self.height(), self.width());
        self.grid = vec![vec![State::Unconfirmed; width]; height];
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
