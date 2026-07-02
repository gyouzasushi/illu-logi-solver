use crate::{
    error::{Cause, LineError},
    operation::Operation,
    segments::{Segments, SetMinMax},
};
use std::{collections::VecDeque, fmt::Display, ops::Range};

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum State {
    Unconfirmed,
    White,
    Black,
}

/// 推論が書き込める値。白か黒のみで、`Unconfirmed` を表現できない。
///
/// `Line` のキューと `update`/`set`/`set_range` はこの型を扱うことで、
/// 「推論結果として `Unconfirmed` を書き込む」という本来あり得ない経路を
/// 型レベルで排除する（`State` のままだと `update` に `Unconfirmed` を
/// 渡すコードが書けてしまい、実行時に矛盾扱いされるまで気付けなかった）。
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) enum Determined {
    White,
    Black,
}
impl From<Determined> for State {
    fn from(determined: Determined) -> Self {
        match determined {
            Determined::White => State::White,
            Determined::Black => State::Black,
        }
    }
}

#[derive(Clone, PartialEq)]
pub(crate) struct Cell {
    pub(crate) state: State,
    possible_block_ids: Range<usize>,
}

#[derive(Clone)]
struct Block {
    size: usize,
    possible_placement: Range<usize>,
}

/// ヒント算出と同一スナップショットにおける、1ブロックの配置可能範囲とサイズ。
///
/// [`crate::Hint::possible_ids`] と同じく、[`crate::Solver::hint`] が読み出した
/// スナップショット（`Line` の clone）から作られるため、常に同じ呼び出しの
/// `action` と整合する。例えば `WhiteIfNoBlockCovers` が「ブロック#1は
/// 左からここまで、#2はここから先」を主張しているとき、その根拠は
/// `blocks[1].possible_placement` / `blocks[2].possible_placement` から読み取れる。
#[derive(Debug, Clone)]
pub struct HintBlock {
    pub size: usize,
    pub possible_placement: Range<usize>,
}

#[derive(Clone)]
pub(crate) struct Line {
    n: usize,
    pub(crate) cells: Vec<Cell>,
    blocks: Vec<Block>,
    pub(crate) segments_black: Segments,
    segments_non_white: Segments,
    segments_unconfirmed: Segments,
    next_step: usize,
    pub(crate) queue: VecDeque<(Range<usize>, Determined, Operation)>,
}

impl Line {
    pub(crate) fn new(n: usize, constraint: Vec<usize>) -> Self {
        let num_blocks = constraint.len();
        let default_cell = Cell {
            state: State::Unconfirmed,
            possible_block_ids: 0..num_blocks,
        };
        let blocks = constraint
            .into_iter()
            .map(|size| Block {
                size,
                possible_placement: 0..n,
            })
            .collect();
        Self {
            n,
            cells: vec![default_cell; n],
            blocks,
            segments_black: Segments::new(vec![false; n]),
            segments_non_white: Segments::new(vec![true; n]),
            segments_unconfirmed: Segments::new(vec![true; n]),
            next_step: 0,
            queue: VecDeque::new(),
        }
    }
    pub(crate) fn possible_id(&self, j: usize) -> Range<usize> {
        self.cells[j].possible_block_ids.clone()
    }
    /// 現在のスナップショットにおける全ブロックの配置可能範囲とサイズ。
    /// [`Solver::hint`](crate::Solver::hint) が action と同一の clone から
    /// 呼ぶことで整合性を保つ（[`HintBlock`] のdocコメント参照）。
    pub(crate) fn hint_blocks(&self) -> Vec<HintBlock> {
        self.blocks
            .iter()
            .map(|block| HintBlock {
                size: block.size,
                possible_placement: block.possible_placement.clone(),
            })
            .collect()
    }
    // セル `j` の候補ブロックID範囲に含まれるブロックのうち、最小/最大のサイズ。
    // ブロック数は小さいので素朴に走査する。候補が空集合なら None。
    fn min_possible_size(&self, j: usize) -> Option<usize> {
        self.possible_id(j).map(|id| self.blocks[id].size).min()
    }
    fn max_possible_size(&self, j: usize) -> Option<usize> {
        self.possible_id(j).map(|id| self.blocks[id].size).max()
    }
    fn set(&mut self, j: usize, state: Determined, by: Operation) {
        self.set_range(j..j + 1, state, by)
    }
    fn set_range(&mut self, range: Range<usize>, state: Determined, by: Operation) {
        if range.is_empty() {
            return;
        }
        if range
            .clone()
            .all(|j| self.cells[j].state == State::from(state))
        {
            return;
        }
        self.queue.push_back((range, state, by));
    }
    pub(crate) fn set_state(&mut self, j: usize, state: State) {
        self.cells[j].state = state;
        match state {
            State::Unconfirmed => {}
            State::White => {
                self.segments_non_white.erase(j);
                self.segments_unconfirmed.erase(j);
            }
            State::Black => {
                self.segments_black.insert(j);
                self.segments_unconfirmed.erase(j);
            }
        }
    }
    pub(crate) fn update(
        &mut self,
        range: Range<usize>,
        state: Determined,
        by: Cause,
    ) -> Result<(), LineError> {
        for j in range {
            match (self.cells[j].state, state) {
                (State::White, Determined::Black) | (State::Black, Determined::White) => {
                    return Err(LineError::Contradiction(j, self.cells[j].state, state, by));
                }
                _ => (),
            };
            self.set_state(j, state.into());
        }
        self.update_possible_id()?;
        Ok(())
    }
    pub(crate) fn confirmed_id(&self, j: usize) -> Option<usize> {
        if self.possible_id(j).len() == 1 {
            Some(self.possible_id(j).start)
        } else {
            None
        }
    }
    fn has_update(&self) -> bool {
        !self.queue.is_empty()
    }
    pub(crate) const STEPS: [fn(&mut Line); 8] = [
        Line::set_black_if_overlap,
        Line::set_black_if_bounded,
        Line::set_black_if_left_bounded,
        Line::set_black_if_right_bounded,
        Line::set_white_if_segment_complete,
        Line::set_white_if_too_long,
        Line::set_white_if_too_short,
        Line::set_white_if_no_block_covers,
    ];

    fn execute_step(&mut self) {
        Self::STEPS[self.next_step](self);
        self.next_step = (self.next_step + 1) % Self::STEPS.len();
    }
    pub(crate) fn advance(
        &mut self,
    ) -> Result<Option<(Range<usize>, Determined, Operation)>, LineError> {
        self.next_step = 0;
        self.update_possible_id()?;
        while !self.has_update() {
            self.execute_step();
            if self.next_step == 0 {
                break;
            }
        }
        if let Some((range, state, by)) = self.queue.pop_front() {
            self.update(range.clone(), state, Cause::Operation(by))?;
            Ok(Some((range, state, by)))
        } else {
            Ok(None)
        }
    }
    #[cfg(test)]
    fn flush_queue(&mut self) -> Result<(), LineError> {
        while let Some((range, state, by)) = self.queue.pop_front() {
            self.update(range.clone(), state, Cause::Operation(by))?;
        }
        Ok(())
    }
    // 各ループは `id` を `self.blocks[id]` と `min_starts[id]`/`max_ends[id]` の
    // 両方の添字に使っており、`enumerate()`化すると可読性が落ちるため許容する。
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn update_possible_id(&mut self) -> Result<(), LineError> {
        let n = self.n;
        let num_blocks = self.blocks.len();
        loop {
            let mut changed = false;

            /* 左に寄せる */
            let mut min_starts = vec![0; num_blocks];
            let mut j = n;
            for id in (0..num_blocks).rev() {
                j = (1..=j)
                    .rfind(|&j| {
                        matches!(self.cells[j - 1].state, State::Black)
                            && self.cells[j - 1].possible_block_ids.end <= id + 1
                    })
                    .unwrap_or(0);
                if j > self.blocks[id].size {
                    min_starts[id].setmax(j - self.blocks[id].size);
                }
            }
            let mut j = n;
            for id in (0..num_blocks).rev() {
                j = (1..=j)
                    .rfind(|&j| self.cells[j - 1].possible_block_ids.end <= id)
                    .unwrap_or(0);
                min_starts[id].setmax(j);
            }
            let mut l = 0;
            for id in 0..num_blocks {
                l.setmax(min_starts[id]);
                let mut r = l + self.blocks[id].size;
                if r <= n {
                    while let Some(j) = (l..r).rfind(|&j| self.cells[j].state == State::White) {
                        l = j + 1;
                        r = l + self.blocks[id].size;
                        if r > n {
                            break;
                        }
                    }
                }
                self.blocks[id].possible_placement.start = l;
                for j in 0..l.min(n) {
                    changed |= self.cells[j].possible_block_ids.end.setmin(id);
                }
                l = r + 1;
            }

            /* 右に寄せる */
            let mut max_ends = vec![n; num_blocks];
            let mut j = 0;
            for id in 0..num_blocks {
                j = (j..n)
                    .find(|&j| {
                        matches!(self.cells[j].state, State::Black)
                            && self.cells[j].possible_block_ids.start >= id
                    })
                    .unwrap_or(n);
                if j + self.blocks[id].size <= n {
                    max_ends[id].setmin(j + self.blocks[id].size);
                }
            }
            let mut j = 0;
            for id in 0..num_blocks {
                j = (j..n)
                    .find(|&j| self.cells[j].possible_block_ids.start > id)
                    .unwrap_or(n);
                max_ends[id].setmin(j);
            }
            let mut r = n;
            for id in (0..num_blocks).rev() {
                r.setmin(max_ends[id]);
                let mut l = r.wrapping_sub(self.blocks[id].size);
                if l < n {
                    while let Some(j) = (l..r).find(|&j| self.cells[j].state == State::White) {
                        r = j;
                        l = r.wrapping_sub(self.blocks[id].size);
                        if l >= n {
                            break;
                        }
                    }
                }
                self.blocks[id].possible_placement.end = r;
                for j in r..n {
                    changed |= self.cells[j].possible_block_ids.start.setmax(id + 1);
                }
                r = l.wrapping_sub(1);
            }

            for (l, r) in self.segments_black.segments() {
                let mut lo = 0;
                let mut hi = num_blocks;
                for j in l..r {
                    lo.setmax(self.cells[j].possible_block_ids.start);
                    hi.setmin(self.cells[j].possible_block_ids.end);
                }
                for j in l..r {
                    changed |= self.cells[j].possible_block_ids.start.setmax(lo);
                    changed |= self.cells[j].possible_block_ids.end.setmin(hi);
                }
            }

            if !changed {
                break;
            }
        }

        for id in 0..num_blocks {
            let start = self.blocks[id].possible_placement.start;
            let end = self.blocks[id].possible_placement.end;
            if start + self.blocks[id].size > end {
                // ブロック `id` がどこにも収まらない。特定のセルの書き込み衝突
                // ではなく行レベルの矛盾なので、`Cause`/`Operation` を捏造せず
                // 専用の `NoPlacement` として報告する。
                return Err(LineError::NoPlacement(id));
            }
        }

        Ok(())
    }
    // 最左配置と最右配置の重複部分は必ず黒
    fn set_black_if_overlap(&mut self) {
        let num_blocks = self.blocks.len();
        for id in 0..num_blocks {
            let l = self.blocks[id].possible_placement.start;
            let r = self.blocks[id].possible_placement.end;
            if r < l + self.blocks[id].size {
                continue;
            }
            let (l, r) = (r - self.blocks[id].size, l + self.blocks[id].size);
            self.set_range(
                l..r,
                Determined::Black,
                Operation::BlackIfOverlap { l, r, id },
            );
        }
    }
    // どのブロックにも属せないセルは白
    fn set_white_if_no_block_covers(&mut self) {
        let mut l = 0;
        while l < self.n {
            l = (l..self.n)
                .find(|&j| self.possible_id(j).is_empty())
                .unwrap_or(self.n);
            let r = (l..self.n)
                .find(|&j| !self.possible_id(j).is_empty())
                .unwrap_or(self.n);
            self.set_range(
                l..r,
                Determined::White,
                Operation::WhiteIfNoBlockCovers(l, r),
            );
            l = r;
        }
    }
    // 非白領域の左端が確定しているとき、最小ブロックサイズ分だけ右へ黒を延ばせる
    fn set_black_if_left_bounded(&mut self) {
        for (j, _) in self.segments_black.segments() {
            let l = self.segments_non_white.left(j);
            let r_max = self.segments_non_white.right(j);
            let mut r = j;
            let mut min = (l..=r)
                .map(|j| self.min_possible_size(j).unwrap_or(0))
                .min()
                .unwrap_or(0);
            while r < r_max && {
                min.setmin(self.min_possible_size(r).unwrap_or(0));
                min
            } > r - l
            {
                r += 1;
            }
            self.set_range(j..r, Determined::Black, Operation::BlackIfLeftBounded(l, r));
        }
    }
    // 非白領域の右端が確定しているとき、最小ブロックサイズ分だけ左へ黒を延ばせる
    fn set_black_if_right_bounded(&mut self) {
        for (_, j) in self.segments_black.segments() {
            let j = j - 1;
            let r = self.segments_non_white.right(j);
            let l_min = self.segments_non_white.left(j);
            let mut l = j;
            let mut min = (l..r)
                .map(|j| self.min_possible_size(j).unwrap_or(0))
                .min()
                .unwrap_or(0);
            while l > l_min && {
                min.setmin(self.min_possible_size(l).unwrap_or(0));
                min
            } > r - l
            {
                l -= 1;
            }
            self.set_range(
                l..j,
                Determined::Black,
                Operation::BlackIfRightBounded(l, r),
            );
        }
    }
    // 両端が確定した非白領域で全セルの可能ブロックサイズが領域長以上なら全体が黒
    fn set_black_if_bounded(&mut self) {
        for (l, r) in self.segments_non_white.segments() {
            if (l..r).all(|j| self.cells[j].state == State::Unconfirmed) {
                continue;
            }
            let size = r - l;
            if (l..r).all(|j| self.min_possible_size(j).is_none_or(|m| m >= size)) {
                self.set_range(l..r, Determined::Black, Operation::BlackIfBounded(l, r));
            }
        }
    }
    // 黒セグメントのサイズが最大の可能ブロックサイズと一致すれば両端は白
    fn set_white_if_segment_complete(&mut self) {
        for (l, r) in self.segments_black.segments() {
            if (l == 0 || self.cells[l - 1].state == State::White)
                && (r == self.n || self.cells[r].state == State::White)
            {
                continue;
            }
            let size = r - l;
            for j in l..r {
                if self.max_possible_size(j) == Some(size) {
                    if l > 0 {
                        self.set(
                            l - 1,
                            Determined::White,
                            Operation::WhiteIfSegmentComplete(l, r),
                        );
                    }
                    if r < self.n {
                        self.set(
                            r,
                            Determined::White,
                            Operation::WhiteIfSegmentComplete(l, r),
                        );
                    }
                    break;
                }
            }
        }
    }
    // このセルを黒にすると唯一の可能ブロックのサイズを超えるなら白
    fn set_white_if_too_long(&mut self) {
        for j in 0..self.n {
            if !(self.cells[j].state == State::Unconfirmed && self.possible_id(j).len() == 1) {
                continue;
            }
            let id = self.possible_id(j).start;
            let mut size = 1;
            if j > 0 && matches!(self.cells[j - 1].state, State::Black) {
                size += self.segments_black.size(j - 1);
            }
            if j + 1 < self.n && matches!(self.cells[j + 1].state, State::Black) {
                size += self.segments_black.size(j + 1);
            }
            if size > self.blocks[id].size {
                self.set(j, Determined::White, Operation::WhiteIfTooLong { j, id });
            }
        }
    }
    // 両端が確定した未確定領域の最小ブロックサイズが領域長を超えるなら全体が白
    fn set_white_if_too_short(&mut self) {
        for (l, r) in self.segments_unconfirmed.segments() {
            if l > 0 && self.cells[l - 1].state != State::White {
                continue;
            }
            if r < self.n && self.cells[r].state != State::White {
                continue;
            }
            if (l..r).any(|j| self.min_possible_size(j).unwrap_or(0) > r - l) {
                self.set_range(l..r, Determined::White, Operation::WhiteIfTooShort(l, r));
            }
        }
    }
}
impl Display for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for j in 0..self.n {
            if j > 0 && j % 5 == 0 {
                write!(f, "|")?;
            }
            match self.cells[j].state {
                State::Unconfirmed => write!(f, "?")?,
                State::White => write!(f, "x")?,
                State::Black => write!(f, "o")?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_update_possible_id() {
        let mut line = Line::new(20, vec![5, 1, 1, 1]);
        // xxooo|ooxxx|...xo|xoxxo
        line.set_state(0, State::White);
        line.set_state(1, State::White);
        line.set_state(2, State::Black);
        line.set_state(3, State::Black);
        line.set_state(4, State::Black);
        line.set_state(5, State::Black);
        line.set_state(6, State::Black);
        line.set_state(7, State::White);
        line.set_state(8, State::White);
        line.set_state(9, State::White);
        line.set_state(13, State::White);
        line.set_state(14, State::Black);
        line.set_state(15, State::White);
        line.set_state(16, State::Black);
        line.set_state(17, State::White);
        line.set_state(18, State::White);
        line.set_state(19, State::Black);
        line.update_possible_id().unwrap();
        for j in 0..20 {
            match j {
                2..=6 => assert_eq!(line.confirmed_id(j), Some(0)),
                14 => assert_eq!(line.confirmed_id(j), Some(1)),
                16 => assert_eq!(line.confirmed_id(j), Some(2)),
                19 => assert_eq!(line.confirmed_id(j), Some(3)),
                _ => assert_eq!(line.confirmed_id(j), None),
            }
        }
    }

    #[test]
    fn test_set_black_if_overlap() {
        // .....
        let mut line = Line::new(5, vec![4]);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Black,
                State::Black,
                State::Black,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(1), Some(0));
        assert_eq!(line.confirmed_id(2), Some(0));
        assert_eq!(line.confirmed_id(3), Some(0));

        // .....
        let mut line = Line::new(5, vec![3, 1]);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Black,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Black,
            ]
        );
        assert_eq!(line.confirmed_id(0), Some(0));
        assert_eq!(line.confirmed_id(1), Some(0));
        assert_eq!(line.confirmed_id(2), Some(0));
        assert_eq!(line.confirmed_id(4), Some(1));

        // .xoo.
        let mut line = Line::new(5, vec![1, 2]);
        line.set_state(1, State::White);
        line.set_state(2, State::Black);
        line.set_state(3, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.flush_queue().unwrap();

        // ..........
        let mut line = Line::new(10, vec![3, 2, 2]);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(1), Some(0));
        assert_eq!(line.confirmed_id(2), Some(0));
        assert_eq!(line.confirmed_id(5), Some(1));
        assert_eq!(line.confirmed_id(8), Some(2));

        // ....xoo.oo....x..x..
        let mut line = Line::new(20, vec![1, 2, 5, 1, 1]);
        line.set_state(4, State::White);
        line.set_state(5, State::Black);
        line.set_state(6, State::Black);
        line.set_state(8, State::Black);
        line.set_state(9, State::Black);
        line.set_state(14, State::White);
        line.set_state(17, State::White);
        line.update_possible_id().unwrap();
        for _ in 0..2 {
            line.update_possible_id().unwrap();
            line.set_black_if_overlap();
            line.flush_queue().unwrap();
            assert_eq!(
                line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
                vec![
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::White,
                    State::Black,
                    State::Black,
                    State::Unconfirmed,
                    State::Black,
                    State::Black,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::White,
                    State::Unconfirmed,
                    State::Unconfirmed,
                    State::White,
                    State::Unconfirmed,
                    State::Unconfirmed,
                ]
            );
            assert_eq!(line.confirmed_id(5), None);
            assert_eq!(line.confirmed_id(6), None);
            assert_eq!(line.confirmed_id(8), Some(2));
            assert_eq!(line.confirmed_id(9), Some(2));
        }
    }
    #[test]
    fn test_set_white_if_segment_complete() {
        // ....oo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::Black);
        line.set_state(5, State::Black);
        line.set_white_if_segment_complete();
        line.flush_queue().unwrap();
        assert_eq!(line.cells[3].state, State::White);
        assert_eq!(line.cells[6].state, State::White);

        // xoox..... — 左隣が白で確定済みのセグメントは正しくスキップされる
        let mut line = Line::new(9, vec![2, 2]);
        line.set_state(0, State::White);
        line.set_state(1, State::Black);
        line.set_state(2, State::Black);
        line.set_state(3, State::White);
        line.update_possible_id().unwrap();
        line.set_white_if_segment_complete();
        line.flush_queue().unwrap();
        // すでに両隣が白なので余計な変化はない
        assert_eq!(line.cells[0].state, State::White);
        assert_eq!(line.cells[1].state, State::Black);
        assert_eq!(line.cells[2].state, State::Black);
        assert_eq!(line.cells[3].state, State::White);
    }

    #[test]
    fn test_set_white_if_no_block_covers() {
        // .o......o.
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(1, State::Black);
        line.set_state(8, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.set_white_if_no_block_covers();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Black,
                State::Unconfirmed,
                State::White,
                State::White,
                State::White,
                State::White,
                State::Unconfirmed,
                State::Black,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(1), Some(0));
        assert_eq!(line.confirmed_id(8), Some(1));
    }
    #[test]
    fn test_set_black_if_left_bounded() {
        // ....xo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::White);
        line.set_state(5, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_left_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(5), None);
        assert_eq!(line.confirmed_id(6), None);

        let mut line = Line::new(30, vec![2, 6, 5, 2, 1]);
        line.set_state(0, State::Black);
        line.set_state(1, State::Black);
        line.set_state(2, State::White);
        line.set_state(9, State::White);
        line.set_state(12, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.set_black_if_left_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Black,
                State::Black,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(0), Some(0));
        assert_eq!(line.confirmed_id(1), Some(0));
        assert_eq!(line.confirmed_id(12), None);
        assert_eq!(line.confirmed_id(13), None);
        assert_eq!(line.confirmed_id(14), None);

        // ....xoo.oo....x..x..
        let mut line = Line::new(20, vec![1, 2, 5, 1, 1]);
        line.set_state(4, State::White);
        line.set_state(5, State::Black);
        line.set_state(6, State::Black);
        line.set_state(8, State::Black);
        line.set_state(9, State::Black);
        line.set_state(14, State::White);
        line.set_state(17, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.set_black_if_overlap();
        line.set_black_if_left_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Black,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(5), None);
        assert_eq!(line.confirmed_id(6), None);
        assert_eq!(line.confirmed_id(8), Some(2));
        assert_eq!(line.confirmed_id(9), Some(2));
    }

    #[test]
    fn test_set_black_if_right_bounded() {
        // ....ox....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::Black);
        line.set_state(5, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_right_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black,
                State::Black,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(3), None);
        assert_eq!(line.confirmed_id(4), None);

        // .ox.......
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(1, State::Black);
        line.set_state(2, State::White);
        line.set_black_if_right_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Black,
                State::Black,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(0), Some(0));
        assert_eq!(line.confirmed_id(1), Some(0));
    }

    #[test]
    fn test_set_black_if_bounded() {
        // ...x.o.x...
        let mut line = Line::new(11, vec![3, 3]);
        line.set_state(3, State::White);
        line.set_state(5, State::Black);
        line.set_state(7, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_bounded();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black,
                State::Black,
                State::Black,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(4), None);
        assert_eq!(line.confirmed_id(5), None);
        assert_eq!(line.confirmed_id(6), None);
    }
    #[test]
    fn test_set_white_if_too_long() {
        // ..o.......
        let mut line = Line::new(10, vec![1, 2]);
        line.set_state(2, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.set_white_if_too_long();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::White,
                State::Black,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(2), None);
    }
    #[test]
    fn test_set_white_if_too_short() {
        // .....ox.x......
        let mut line = Line::new(15, vec![1, 2, 2]);
        line.set_state(5, State::Black);
        line.set_state(6, State::White);
        line.set_state(8, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_overlap();
        line.set_white_if_too_short();
        line.flush_queue().unwrap();
        assert_eq!(
            line.cells.iter().map(|c| c.state).collect::<Vec<_>>(),
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black,
                State::White,
                State::White,
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
        assert_eq!(line.confirmed_id(5), None);
    }
}
