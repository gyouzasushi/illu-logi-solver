mod util;

use crate::util::{Segments, SetMinMax};
use fixedbitset::FixedBitSet;
use std::{collections::VecDeque, fmt::Display, ops::Range};
use thiserror::Error;

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
impl From<usize> for Axis {
    fn from(value: usize) -> Self {
        match value {
            0 => Axis::Row,
            1 => Axis::Column,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum State {
    Unconfirmed,
    White,
    Black,
}

#[derive(Clone, Copy, Debug)]
pub enum Operation {
    BlackIfLeftmostAndRightmostIntersect(usize, usize),
    WhiteIfPossibleIdIsEmpty(usize, usize),
    BlackIfBothEndIsConfirmed(usize, usize),
    BlackIfLeftEndIsConfirmed(usize, usize),
    BlackIfRightEndIsConfirmed(usize, usize),
    WhiteIfTheLengthIsConfirmed(usize, usize),
    WhiteIfTooLong(usize),
    WhiteIfTooShort(usize, usize),
    SameStateAsOrthogonal,
}

#[derive(Debug)]
enum LineError {
    Contradiction(usize, State, State, Operation),
}
impl LineError {
    fn to_solver_error(&self, axis: Axis, i: usize) -> SolverError {
        match self {
            LineError::Contradiction(j, current_state, new_state, by) => {
                SolverError::Contradiction {
                    axis,
                    i,
                    j: *j,
                    current_state: *current_state,
                    new_state: *new_state,
                    by: *by,
                }
            }
        }
    }
}

#[derive(Clone, PartialEq)]
struct Cell {
    state: State,
    possible_block_ids: Range<usize>,
    possible_block_sizes: FixedBitSet,
}

#[derive(Clone)]
struct Block {
    size: usize,
    possible_placement: Range<usize>,
}

#[derive(Clone)]
struct Line {
    n: usize,
    cells: Vec<Cell>,
    blocks: Vec<Block>,
    segments_black: Segments,
    segments_non_white: Segments,
    segments_unconfirmed: Segments,
    next_step: usize,
    queue: VecDeque<(Range<usize>, State, Operation)>,
}

impl Line {
    fn new(n: usize, constraint: Vec<usize>) -> Self {
        let num_blocks = constraint.len();
        let mut possible_block_sizes = FixedBitSet::with_capacity(n + 1);
        (0..num_blocks).for_each(|id| possible_block_sizes.insert(constraint[id]));
        let default_cell = Cell {
            state: State::Unconfirmed,
            possible_block_ids: 0..num_blocks,
            possible_block_sizes,
        };
        let blocks = constraint
            .into_iter()
            .map(|size| Block { size, possible_placement: 0..n })
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
    fn possible_id(&self, j: usize) -> Range<usize> {
        self.cells[j].possible_block_ids.clone()
    }
    fn set(&mut self, j: usize, state: State, by: Operation) {
        self.set_range(j..j + 1, state, by)
    }
    fn set_range(&mut self, range: Range<usize>, state: State, by: Operation) {
        if range.is_empty() {
            return;
        }
        if range.clone().all(|j| self.cells[j].state == state) {
            return;
        }
        self.queue.push_back((range, state, by));
    }
    fn update(
        &mut self,
        range: Range<usize>,
        state: State,
        by: Operation,
    ) -> Result<(), LineError> {
        for j in range {
            match (self.cells[j].state, state) {
                (State::White, State::Unconfirmed | State::Black)
                | (State::Black, State::Unconfirmed | State::White) => {
                    return Err(LineError::Contradiction(j, self.cells[j].state, state, by));
                }
                _ => (),
            };
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
            };
        }
        self.update_possible_id()?;
        Ok(())
    }
    fn set_state(&mut self, j: usize, state: State) {
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
        };
    }
    fn confirmed_id(&self, j: usize) -> Option<usize> {
        if self.possible_id(j).len() == 1 {
            Some(self.possible_id(j).start)
        } else {
            None
        }
    }
    fn has_update(&self) -> bool {
        !self.queue.is_empty()
    }
    const STEPS: [fn(&mut Line); 8] = [
        Line::set_black_if_leftmost_and_rightmost_intersect,
        Line::set_black_if_both_end_is_confirmed,
        Line::set_black_if_left_end_is_confirmed,
        Line::set_black_if_right_end_is_confirmed,
        Line::set_white_if_the_length_is_confirmed,
        Line::set_white_if_too_long,
        Line::set_white_if_too_short,
        Line::set_white_if_possible_id_is_empty,
    ];

    fn execute_step(&mut self) {
        Self::STEPS[self.next_step](self);
        self.next_step = (self.next_step + 1) % Self::STEPS.len();
    }
    fn advance(&mut self) -> Result<Option<(Range<usize>, State, Operation)>, LineError> {
        self.next_step = 0;
        self.update_possible_id()?;
        while !self.has_update() {
            self.execute_step();
            if self.next_step == 0 {
                break;
            }
        }
        if let Some((range, state, by)) = self.queue.pop_front() {
            self.update(range.clone(), state, by)?;
            Ok(Some((range, state, by)))
        } else {
            Ok(None)
        }
    }
    #[cfg(test)]
    fn flush_queue(&mut self) -> Result<(), LineError> {
        while let Some((range, state, by)) = self.queue.pop_front() {
            self.update(range.clone(), state, by)?;
        }
        Ok(())
    }
    fn update_possible_id(&mut self) -> Result<(), LineError> {
        let n = self.n;
        let num_blocks = self.blocks.len();
        loop {
            let prev: Vec<Range<usize>> = self.cells.iter()
                .map(|c| c.possible_block_ids.clone())
                .collect();

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
                        if r > n { break; }
                    }
                }
                self.blocks[id].possible_placement.start = l;
                for j in 0..l.min(n) {
                    self.cells[j].possible_block_ids.end.setmin(id);
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
                        if l >= n { break; }
                    }
                }
                self.blocks[id].possible_placement.end = r;
                for j in r..n {
                    self.cells[j].possible_block_ids.start.setmax(id + 1);
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
                    self.cells[j].possible_block_ids.start.setmax(lo);
                    self.cells[j].possible_block_ids.end.setmin(hi);
                }
            }

            let current: Vec<Range<usize>> = self.cells.iter()
                .map(|c| c.possible_block_ids.clone())
                .collect();
            if current == prev {
                break;
            }
        }

        for id in 0..num_blocks {
            let start = self.blocks[id].possible_placement.start;
            let end = self.blocks[id].possible_placement.end;
            if start + self.blocks[id].size > end {
                let j = start.min(n.saturating_sub(1));
                return Err(LineError::Contradiction(
                    j,
                    self.cells[j].state,
                    State::Black,
                    Operation::BlackIfLeftmostAndRightmostIntersect(
                        start, start + self.blocks[id].size,
                    ),
                ));
            }
        }

        for j in 0..n {
            self.cells[j].possible_block_sizes.clear();
            let ids = self.cells[j].possible_block_ids.clone();
            for id in ids {
                self.cells[j].possible_block_sizes.insert(self.blocks[id].size);
            }
        }

        Ok(())
    }
    fn set_black_if_leftmost_and_rightmost_intersect(&mut self) {
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
                State::Black,
                Operation::BlackIfLeftmostAndRightmostIntersect(l, r),
            );
        }
    }
    fn set_white_if_possible_id_is_empty(&mut self) {
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
                State::White,
                Operation::WhiteIfPossibleIdIsEmpty(l, r),
            );
            l = r;
        }
    }
    fn set_black_if_left_end_is_confirmed(&mut self) {
        for (j, _) in self.segments_black.segments() {
            let l = self.segments_non_white.left(j);
            let r_max = self.segments_non_white.right(j);
            let mut r = j;
            let mut min = self.cells[l..=r]
                .iter()
                .map(|cell| cell.possible_block_sizes.ones().next().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while r < r_max && {
                min.setmin(self.cells[r].possible_block_sizes.ones().next().unwrap_or(0));
                min
            } > r - l
            {
                r += 1;
            }
            self.set_range(
                j..r,
                State::Black,
                Operation::BlackIfLeftEndIsConfirmed(l, r),
            );
        }
    }
    fn set_black_if_right_end_is_confirmed(&mut self) {
        for (_, j) in self.segments_black.segments() {
            let j = j - 1;
            let r = self.segments_non_white.right(j);
            let l_min = self.segments_non_white.left(j);
            let mut l = j;
            let mut min = self.cells[l..r]
                .iter()
                .map(|cell| cell.possible_block_sizes.ones().next().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while l > l_min && {
                min.setmin(self.cells[l].possible_block_sizes.ones().next().unwrap_or(0));
                min
            } > r - l
            {
                l -= 1;
            }
            self.set_range(
                l..j,
                State::Black,
                Operation::BlackIfRightEndIsConfirmed(l, r),
            );
        }
    }
    fn set_black_if_both_end_is_confirmed(&mut self) {
        for (l, r) in self.segments_non_white.segments() {
            if (l..r).all(|j| self.cells[j].state == State::Unconfirmed) {
                continue;
            }
            let size = r - l;
            if self.cells[l..r]
                .iter()
                .all(|cell| cell.possible_block_sizes.count_ones(0..size) == 0)
            {
                self.set_range(
                    l..r,
                    State::Black,
                    Operation::BlackIfBothEndIsConfirmed(l, r),
                );
            }
        }
    }
    fn set_white_if_the_length_is_confirmed(&mut self) {
        for (l, r) in self.segments_black.segments() {
            if (l == 0 || self.cells[l - 1].state == State::White)
                && (r == self.n || self.cells[r].state == State::White)
            {
                continue;
            }
            let size = r - l;
            for j in l..r {
                if self.cells[j].possible_block_sizes.contains(size)
                    && self.cells[j].possible_block_sizes.count_ones(size..self.n) == 1
                {
                    if l > 0 {
                        self.set(
                            l - 1,
                            State::White,
                            Operation::WhiteIfTheLengthIsConfirmed(l, r),
                        );
                    }
                    if r < self.n {
                        self.set(
                            r,
                            State::White,
                            Operation::WhiteIfTheLengthIsConfirmed(l, r),
                        );
                    }
                    break;
                }
            }
        }
    }
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
                self.set(j, State::White, Operation::WhiteIfTooLong(j));
            }
        }
    }
    fn set_white_if_too_short(&mut self) {
        for (l, r) in self.segments_unconfirmed.segments() {
            if l > 0 && self.cells[l - 1].state != State::White {
                continue;
            }
            if r < self.n && self.cells[r].state != State::White {
                continue;
            }
            if (l..r).any(|j| self.cells[j].possible_block_sizes.ones().next().unwrap_or(0) > r - l) {
                self.set_range(l..r, State::White, Operation::WhiteIfTooShort(l, r));
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

#[derive(Debug, Clone)]
pub struct Action {
    pub axis: Axis,
    pub i: usize,
    pub range: Range<usize>,
    pub state: State,
    pub by: Operation,
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
        by: Operation,
    },
    #[error("could not find a solution: there might be multiple possible solutions.")]
    MultipleSolutions,
}

pub struct Solver {
    n: usize,
    constraints: [Vec<Vec<usize>>; 2],
    lines: [Vec<Line>; 2],
    queue: VecDeque<(Axis, usize)>,
    turn_count: usize,
}
impl Solver {
    pub fn new(constraints: [Vec<Vec<usize>>; 2]) -> Self {
        assert_eq!(constraints[0].len(), constraints[1].len());
        let n = constraints[0].len();
        let lines = [
            constraints[0]
                .iter()
                .map(|constraint| Line::new(n, constraint.clone()))
                .collect(),
            constraints[1]
                .iter()
                .map(|constraint| Line::new(n, constraint.clone()))
                .collect(),
        ];
        let queue = (0..2)
            .flat_map(|axis| (0..n).map(move |i| (axis.into(), i)))
            .collect();
        Self {
            n,
            constraints,
            lines,
            queue,
            turn_count: 0,
        }
    }

    fn clear(&mut self) {
        *self = Self::new(std::mem::take(&mut self.constraints));
    }

    pub fn solve(&mut self) -> Result<(), SolverError> {
        while self.advance()?.is_some() {}
        if self.lines[0]
            .iter()
            .flat_map(|line| line.cells.iter().map(|cell| cell.state))
            .any(|state| matches!(state, State::Unconfirmed))
        {
            Err(SolverError::MultipleSolutions)
        } else {
            Ok(())
        }
    }

    pub fn rollback(&mut self, t: usize) -> Result<Option<Action>, SolverError> {
        if self.turn_count > t {
            self.clear();
        }
        let mut ret = None;
        while self.turn_count < t {
            ret = self.advance()?;
            if ret.is_none() {
                break;
            }
        }
        Ok(ret)
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

    pub fn turn(&self) -> usize {
        self.turn_count
    }

    pub fn judge(&self) -> bool {
        for i in 0..self.n {
            let v = self.lines[Axis::Row as usize][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.constraints[Axis::Row as usize][i] {
                return false;
            }
            let v = self.lines[Axis::Column as usize][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.constraints[Axis::Column as usize][i] {
                return false;
            }
        }
        true
    }

    pub fn set(&mut self, i: usize, j: usize, state: State) {
        self.lines[Axis::Row as usize][i].set_state(j, state);
        self.lines[Axis::Column as usize][j].set_state(i, state);
    }

    pub fn state(&self, i: usize, j: usize) -> State {
        assert_eq!(
            self.lines[Axis::Row as usize][i].cells[j].state,
            self.lines[Axis::Column as usize][j].cells[i].state
        );
        self.lines[Axis::Row as usize][i].cells[j].state
    }

    pub fn possible_id(&self, axis: Axis, i: usize, j: usize) -> Range<usize> {
        self.lines[axis as usize][i].possible_id(j)
    }
}

impl std::fmt::Display for Solver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for y in 0..self.n {
            if y > 0 && y % 5 == 0 {
                for x in 0..self.n {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                write!(f, "  ")?;
                for x in 0..self.n {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                write!(f, "  ")?;
                for x in 0..self.n {
                    if x > 0 && x % 5 == 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "-")?;
                }
                writeln!(f)?;
            }
            for x in 0..self.n {
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
            for x in 0..self.n {
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
            for x in 0..self.n {
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
    fn test_set_black_if_leftmost_and_rightmost_intersect() {
        // .....
        let mut line = Line::new(5, vec![4]);
        line.update_possible_id().unwrap();
        line.set_black_if_leftmost_and_rightmost_intersect();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.flush_queue().unwrap();

        // ..........
        let mut line = Line::new(10, vec![3, 2, 2]);
        line.update_possible_id().unwrap();
        line.set_black_if_leftmost_and_rightmost_intersect();
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
            line.set_black_if_leftmost_and_rightmost_intersect();
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
    fn test_set_white_if_the_length_is_confirmed() {
        // ....oo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::Black);
        line.set_state(5, State::Black);
        line.set_white_if_the_length_is_confirmed();
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
        line.set_white_if_the_length_is_confirmed();
        line.flush_queue().unwrap();
        // すでに両隣が白なので余計な変化はない
        assert_eq!(line.cells[0].state, State::White);
        assert_eq!(line.cells[1].state, State::Black);
        assert_eq!(line.cells[2].state, State::Black);
        assert_eq!(line.cells[3].state, State::White);
    }

    #[test]
    fn test_set_white_if_possible_id_is_empty() {
        // .o......o.
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(1, State::Black);
        line.set_state(8, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_white_if_possible_id_is_empty();
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
    fn test_set_black_if_left_end_is_confirmed() {
        // ....xo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::White);
        line.set_state(5, State::Black);
        line.update_possible_id().unwrap();
        line.set_black_if_left_end_is_confirmed();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_left_end_is_confirmed();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_left_end_is_confirmed();
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
    fn test_set_black_if_right_end_is_confirmed() {
        // ....ox....
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(4, State::Black);
        line.set_state(5, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_right_end_is_confirmed();
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
        line.set_black_if_right_end_is_confirmed();
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
    fn test_set_black_if_both_end_is_confirmed() {
        // ...x.o.x...
        let mut line = Line::new(11, vec![3, 3]);
        line.set_state(3, State::White);
        line.set_state(5, State::Black);
        line.set_state(7, State::White);
        line.update_possible_id().unwrap();
        line.set_black_if_both_end_is_confirmed();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
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
        line.set_black_if_leftmost_and_rightmost_intersect();
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
