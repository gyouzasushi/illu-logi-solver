mod util;
use std::{collections::VecDeque, fmt::Display, ops::Range};

use crate::util::{BitSet, Segments, SetMinMax};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SolverError {
    #[error("There is an issue with the solver.")]
    InternalError,

    #[error("The solver could not solve this problem.")]
    Unsolvable,
}

pub type Hints = [Vec<Vec<usize>>; 2];

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum State {
    Unconfirmed,
    White,
    Black(Option<usize>),
}

enum Operation {
    CheckLeftmostAndRightmost,
    SetWhiteIfNoCandidates,
    SetBlackIfLeftEndIsConfirmed,
    SetBlackIfRightEndIsConfirmed,
    SetBlackIfBothEndIsConfirmed,
    SetWhiteIfTheLengthIsConfirmed,
    SetWhiteIfTooLong,
    SetWhiteIfTooShort,
    SetIdIfTheLengthIsConfirmed,
    SetIdIfEnoughLong,
    SetSameStateAsOrthogonal,
}
struct Line {
    n: usize,
    hint: Vec<usize>,
    states: Vec<State>,
    segments_black: Segments,
    segments_non_white: Segments,
    segments_unconfirmed: Segments,
    _id_ranges: Vec<(usize, usize)>,
    size_candidates: Vec<BitSet>,
    updates: VecDeque<(usize, State, Operation)>,
}
impl Line {
    fn new(n: usize, hint: Vec<usize>) -> Self {
        let m = hint.len();
        let mut size_candidate = BitSet::new();
        (0..m).for_each(|id| size_candidate.insert(hint[id]));
        Self {
            n,
            hint,
            states: vec![State::Unconfirmed; n],
            segments_black: Segments::new(),
            segments_non_white: Segments::new().initialize(n),
            segments_unconfirmed: Segments::new().initialize(n),
            _id_ranges: vec![(0, m); n],
            size_candidates: vec![size_candidate; n],
            updates: VecDeque::new(),
        }
    }
    fn id_range(&self, j: usize) -> Range<usize> {
        self._id_ranges[j].0..self._id_ranges[j].1
    }
    fn get_update(&mut self) -> Option<(usize, State, Operation)> {
        self.updates.pop_front()
    }
    fn set(&mut self, j: usize, state: State, by: Operation) -> Result<(), SolverError> {
        match (self.states[j], state) {
            (State::Unconfirmed, State::Unconfirmed) => return Ok(()),
            (State::Unconfirmed, State::White) => {}
            (State::Unconfirmed, State::Black(_)) => {}

            (State::White, State::Unconfirmed | State::Black(_)) => {
                return Err(SolverError::InternalError)
            }
            (State::White, State::White) => return Ok(()),

            (State::Black(_), State::Unconfirmed | State::White) => {
                return Err(SolverError::InternalError)
            }
            (State::Black(_), State::Black(None)) => return Ok(()),
            (State::Black(None), State::Black(Some(_))) => {}
            (State::Black(Some(x)), State::Black(Some(y))) => {
                if x != y {
                    return Err(SolverError::InternalError);
                }
                return Ok(());
            }
        };
        self.states[j] = state;
        match state {
            State::Unconfirmed => {}
            State::White => {
                self.segments_non_white.erase(j);
                self.segments_unconfirmed.erase(j);
            }
            State::Black(Some(id)) => {
                self.segments_black.insert(j);
                self.segments_unconfirmed.erase(j);
                let (l, r) = (self.segments_black.left(j), self.segments_black.right(j));
                for j in l..r {
                    self.states[j] = State::Black(Some(id));
                    self._id_ranges[j] = (id, id + 1);
                }
            }
            State::Black(None) => {
                self.segments_black.insert(j);
                self.segments_unconfirmed.erase(j);
            }
        };
        if !matches!(by, Operation::SetSameStateAsOrthogonal) {
            self.updates.push_back((j, self.states[j], by));
        }
        Ok(())
    }

    fn solve(&mut self) -> Result<(), SolverError> {
        loop {
            let prev = self.states.clone();
            self.check_leftmost_and_rightmost()?;
            self.set_white_if_no_candidates()?;
            self.set_black_if_left_end_is_confirmed()?;
            self.set_black_if_right_end_is_confirmed()?;
            self.set_black_if_both_end_is_confirmed()?;
            self.set_white_if_the_length_is_confirmed()?;
            self.set_white_if_too_long()?;
            self.set_white_if_too_short()?;
            self.set_id_if_the_length_is_confirmed()?;
            self.set_id_if_enough_long()?;
            if self.states == prev {
                break;
            }
        }
        Ok(())
    }

    fn check_leftmost_and_rightmost(&mut self) -> Result<(), SolverError> {
        let (n, m) = (self.n, self.hint.len());
        /* 左に寄せる */
        let mut segments_left = vec![(0, 0); m];
        let mut ls = vec![0; m];
        let mut j = n;
        for id in (0..m).rev() {
            j = (1..=j)
                .rfind(|&j| {
                    matches!(self.states[j - 1], State::Black(_))
                        && self._id_ranges[j - 1].1 <= id + 1
                })
                .unwrap_or(0);
            if j > self.hint[id] {
                ls[id].setmax(j - self.hint[id]);
            }
        }
        let mut j = n;
        for id in (0..m).rev() {
            j = (1..=j)
                .rfind(|&j| self._id_ranges[j - 1].1 <= id)
                .unwrap_or(0);
            ls[id].setmax(j);
        }
        let mut l = 0;
        for id in 0..m {
            l.setmax(ls[id]);
            let mut r = l + self.hint[id];
            while let Some(j) = (l..r).rfind(|&j| self.states[j] == State::White) {
                l = j + 1;
                r = l + self.hint[id];
            }
            segments_left[id] = (l, r);
            l = r + 1;
        }

        /* 右に寄せる */
        let mut segments_right = vec![(0, 0); m];
        let mut rs = vec![n; m];
        let mut j = 0;
        for id in 0..m {
            j = (j..self.n)
                .find(|&j| matches!(self.states[j], State::Black(_)) && self._id_ranges[j].0 >= id)
                .unwrap_or(self.n);
            if j + self.hint[id] <= self.n {
                rs[id].setmin(j + self.hint[id]);
            }
        }
        let mut j = 0;
        for id in 0..m {
            j = (j..self.n)
                .find(|&j| self._id_ranges[j].0 > id)
                .unwrap_or(self.n);
            rs[id].setmin(j);
        }
        let mut r = n;
        for id in (0..m).rev() {
            r.setmin(rs[id]);
            let mut l = r - self.hint[id];
            while let Some(j) = (l..r).find(|&j| self.states[j] == State::White) {
                r = j;
                l = r - self.hint[id];
            }
            segments_right[id] = (l, r);
            r = l.wrapping_sub(1);
        }

        for id in 0..m {
            let (l1, r1) = segments_left[id];
            let (l2, r2) = segments_right[id];
            let (l, r) = (l1.max(l2), r1.min(r2));
            for j in l..r {
                self.set(
                    j,
                    State::Black(Some(id)),
                    Operation::CheckLeftmostAndRightmost,
                )?;
            }
        }
        for id in 0..m {
            let (l, r) = (segments_left[id].0, segments_right[id].1);
            for j in 0..l {
                self._id_ranges[j].1.setmin(id);
            }
            for j in r..n {
                self._id_ranges[j].0.setmax(id + 1);
            }
        }
        for j in 0..n {
            self.size_candidates[j].clear();
            self.id_range(j)
                .for_each(|id| self.size_candidates[j].insert(self.hint[id]));
        }

        Ok(())
    }
    fn set_id_if_enough_long(&mut self) -> Result<(), SolverError> {
        for j in 0..self.n {
            if self.states[j] != State::Black(None) {
                continue;
            }
            let size = self.segments_black.size(j);
            if self.id_range(j).filter(|&id| size <= self.hint[id]).count() == 1 {
                let id = self.id_range(j).find(|&id| size <= self.hint[id]).unwrap();
                self.set(j, State::Black(Some(id)), Operation::SetIdIfEnoughLong)?;
            }
        }
        Ok(())
    }
    fn set_white_if_the_length_is_confirmed(&mut self) -> Result<(), SolverError> {
        for (l, r) in self.segments_black.segments() {
            if (l == 0 || self.states[l] == State::White)
                && (r == self.n || self.states[r] == State::White)
            {
                continue;
            }
            let size = r - l;
            for j in l..r {
                if self.size_candidates[j].contains(&size)
                    && self.size_candidates[j].count_ge(&size) == 1
                {
                    if l > 0 {
                        self.set(
                            l - 1,
                            State::White,
                            Operation::SetWhiteIfTheLengthIsConfirmed,
                        )?;
                    }
                    if r < self.n {
                        self.set(r, State::White, Operation::SetWhiteIfTheLengthIsConfirmed)?;
                    }
                    break;
                }
            }
        }
        Ok(())
    }
    fn set_id_if_the_length_is_confirmed(&mut self) -> Result<(), SolverError> {
        for (l, r) in self.segments_black.segments() {
            if !((l == 0 || self.states[l - 1] == State::White)
                && (r == self.n || self.states[r] == State::White))
            {
                continue;
            }
            for j in l..r {
                let mut cand = self.id_range(j).filter(|&id| self.hint[id] == r - l);
                if let Some(id) = cand.next() {
                    if cand.next().is_some() {
                        continue;
                    }
                    self.set(
                        j,
                        State::Black(Some(id)),
                        Operation::SetIdIfTheLengthIsConfirmed,
                    )?;
                    break;
                }
            }
        }
        Ok(())
    }
    fn set_white_if_no_candidates(&mut self) -> Result<(), SolverError> {
        for j in 0..self.n {
            if self.id_range(j).is_empty() {
                self.set(j, State::White, Operation::SetWhiteIfNoCandidates)?;
            }
        }
        Ok(())
    }
    fn set_black_if_left_end_is_confirmed(&mut self) -> Result<(), SolverError> {
        for (j, _) in self.segments_black.segments() {
            let l = self.segments_non_white.left(j);
            let r_max = self.segments_non_white.right(j);
            let mut r = j;
            let mut min = self.size_candidates[l..=r]
                .iter()
                .map(|size_candidate| size_candidate.min().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while r < r_max && {
                min.setmin(self.size_candidates[r].min().unwrap_or(0));
                min
            } > r - l
            {
                r += 1;
            }
            for k in j..r {
                self.set(
                    k,
                    State::Black(None),
                    Operation::SetBlackIfLeftEndIsConfirmed,
                )?;
            }
        }
        Ok(())
    }
    fn set_black_if_right_end_is_confirmed(&mut self) -> Result<(), SolverError> {
        for (_, j) in self.segments_black.segments() {
            let j = j - 1;
            let r = self.segments_non_white.right(j);
            let l_min = self.segments_non_white.left(j);
            let mut l = j;
            let mut min = self.size_candidates[l..r]
                .iter()
                .map(|size_candidate| size_candidate.min().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while l > l_min && {
                min.setmin(self.size_candidates[l].min().unwrap_or(0));
                min
            } > r - l
            {
                l -= 1;
            }
            for k in l..j {
                self.set(
                    k,
                    State::Black(None),
                    Operation::SetBlackIfRightEndIsConfirmed,
                )?;
            }
        }
        Ok(())
    }
    fn set_black_if_both_end_is_confirmed(&mut self) -> Result<(), SolverError> {
        for (l, r) in self.segments_non_white.segments() {
            if (l..r).all(|j| self.states[j] == State::Unconfirmed) {
                continue;
            }
            let size = r - l;
            if self.size_candidates[l..r]
                .iter()
                .all(|size_candidate| size_candidate.count_lt(&size) == 0)
            {
                for j in l..r {
                    self.set(
                        j,
                        State::Black(None),
                        Operation::SetBlackIfBothEndIsConfirmed,
                    )?;
                }
            }
        }
        Ok(())
    }
    fn set_white_if_too_long(&mut self) -> Result<(), SolverError> {
        for j in 0..self.n {
            if !(self.states[j] == State::Unconfirmed && self.id_range(j).len() == 1) {
                continue;
            }
            let id = self.id_range(j).start;
            let mut size = 1;
            if j > 0 && matches!(self.states[j - 1], State::Black(_)) {
                size += self.segments_black.size(j - 1);
            }
            if j + 1 < self.n && matches!(self.states[j + 1], State::Black(_)) {
                size += self.segments_black.size(j + 1);
            }
            if size > self.hint[id] {
                self.set(j, State::White, Operation::SetWhiteIfTooLong)?;
            }
        }
        Ok(())
    }
    fn set_white_if_too_short(&mut self) -> Result<(), SolverError> {
        for (l, r) in self.segments_unconfirmed.segments() {
            if l > 0 && self.states[l - 1] != State::White {
                continue;
            }
            if r < self.n && self.states[r] != State::White {
                continue;
            }
            for j in l..r {
                if self.id_range(j).all(|id| self.hint[id] > r - l) {
                    for j in l..r {
                        self.set(j, State::White, Operation::SetWhiteIfTooShort)?;
                    }
                    break;
                }
            }
        }
        Ok(())
    }
}
impl Display for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for j in 0..self.n {
            if j > 0 && j % 5 == 0 {
                write!(f, "|")?;
            }
            match self.states[j] {
                State::Unconfirmed => write!(f, "?")?,
                State::White => write!(f, "x")?,
                State::Black(_) => write!(f, "o")?,
            }
        }
        Ok(())
    }
}

pub struct Solver {
    n: usize,
    lines: [Vec<Line>; 2],
    queue: VecDeque<(usize, usize)>,
    history: VecDeque<((usize, usize, usize), Operation)>,
}
impl Solver {
    pub fn new(hints: [Vec<Vec<usize>>; 2]) -> Self {
        assert_eq!(hints[0].len(), hints[1].len());
        assert_eq!(
            hints[0]
                .iter()
                .map(|hints| hints.iter().sum::<usize>())
                .sum::<usize>(),
            hints[1]
                .iter()
                .map(|hints| hints.iter().sum::<usize>())
                .sum::<usize>(),
        );
        let n = hints[0].len();
        let lines = [
            hints[0]
                .iter()
                .map(|hint| Line::new(n, hint.clone()))
                .collect(),
            hints[1]
                .iter()
                .map(|hint| Line::new(n, hint.clone()))
                .collect(),
        ];
        let queue = (0..n).flat_map(|i| [(0, i), (1, i)]).collect();
        let history = VecDeque::new();
        Self {
            n,
            lines,
            queue,
            history,
        }
    }

    pub fn solve(&mut self) -> Result<(), SolverError> {
        while let Some((axis, i)) = self.queue.pop_front() {
            self.lines[axis][i].solve()?;
            while let Some((j, state, by)) = self.lines[axis][i].get_update() {
                self.history.push_back(((axis, i, j), by));
                let state = match state {
                    State::Black(Some(_)) => State::Black(None),
                    _ => state,
                };
                self.lines[axis ^ 1][j].set(i, state, Operation::SetSameStateAsOrthogonal)?;
                self.queue.push_back((axis ^ 1, j));
            }
        }
        if self.lines[0]
            .iter()
            .flat_map(|segment| segment.states.clone())
            .any(|state| matches!(state, State::Unconfirmed))
        {
            return Err(SolverError::Unsolvable);
        }
        Ok(())
    }

    // 一度 solve() を呼んでから使う。
    // solve() はコンストラクタで呼ぶべきか
    pub fn advance() {}

    pub fn judge(&self) -> bool {
        for i in 0..self.n {
            for j in 0..self.n {
                if matches!(self.lines[0][i].states[j], State::White)
                    != matches!(self.lines[1][j].states[i], State::White)
                {
                    return false;
                }
            }
        }
        for i in 0..self.n {
            let v = self.lines[0][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.lines[0][i].hint {
                return false;
            }

            let v = self.lines[1][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.lines[1][i].hint {
                return false;
            }
        }
        true
    }
    pub fn get_state(&self, y: usize, x: usize) -> State {
        self.lines[0][y].states[x]
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
                    match self.lines[0][y].states[x] {
                        State::Unconfirmed => ".".to_string(),
                        State::White => "x".to_string(),
                        State::Black(k) => {
                            match k {
                                Some(k) => format!("{k}"),
                                None => "o".to_string(),
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
                    match self.lines[1][x].states[y] {
                        State::Unconfirmed => ".".to_string(),
                        State::White => "x".to_string(),
                        State::Black(k) => {
                            match k {
                                Some(k) => format!("{k}"),
                                None => "o".to_string(),
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
                    match self.lines[0][y].states[x] {
                        State::Unconfirmed => "?".to_string(),
                        State::White => ".".to_string(),
                        State::Black(_) => "o".to_string(),
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
    fn test_check_leftmost_and_rightmost() {
        // .....
        let mut line = Line::new(5, vec![4]);
        line.check_leftmost_and_rightmost();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Black(Some(0)),
                State::Black(Some(0)),
                State::Black(Some(0)),
                State::Unconfirmed,
            ]
        );

        // .....
        let mut line = Line::new(5, vec![3, 1]);
        line.check_leftmost_and_rightmost();
        assert_eq!(
            line.states,
            vec![
                State::Black(Some(0)),
                State::Black(Some(0)),
                State::Black(Some(0)),
                State::Unconfirmed,
                State::Black(Some(1)),
            ]
        );

        // .xoo.
        let mut line = Line::new(5, vec![1, 2]);
        line.set(1, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(2, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(3, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();

        // ..........
        let mut line = Line::new(10, vec![3, 2, 2]);
        line.check_leftmost_and_rightmost();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Black(Some(0)),
                State::Black(Some(0)),
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black(Some(1)),
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black(Some(2)),
                State::Unconfirmed,
            ]
        );

        // ....xoo.oo....x..x..
        let mut line = Line::new(20, vec![1, 2, 5, 1, 1]);
        line.set(4, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(6, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(8, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(9, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(14, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(17, State::White, Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Black(None),
                State::Unconfirmed,
                State::Black(Some(2)),
                State::Black(Some(2)),
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
        line.check_leftmost_and_rightmost();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Black(None),
                State::Unconfirmed,
                State::Black(Some(2)),
                State::Black(Some(2)),
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
    }

    #[test]
    fn test_set_id_if_enough_long() {
        // ....oo....
        let mut line = Line::new(10, vec![1, 3]);
        line.set(4, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.set_id_if_enough_long();
        assert_eq!(line.states[4], State::Black(Some(1)));
        assert_eq!(line.states[5], State::Black(Some(1)));
    }
    #[test]
    fn test_set_white_if_the_length_is_confirmed() {
        // ....oo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set(4, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set_white_if_the_length_is_confirmed();
        assert_eq!(line.states[3], State::White);
        assert_eq!(line.states[6], State::White);
    }
    #[test]
    fn test_set_id_if_the_length_is_confirmed() {
        let mut line = Line::new(10, vec![2, 3]);
        line.set(3, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(4, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(6, State::White, Operation::SetSameStateAsOrthogonal);
        line.set_id_if_the_length_is_confirmed();
        assert_eq!(line.states[4], State::Black(Some(0)));
        assert_eq!(line.states[5], State::Black(Some(0)));
    }
    #[test]
    fn test_set_white_if_no_candidates() {
        // .o......o.
        let mut line = Line::new(10, vec![2, 2]);
        line.set(1, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(8, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.set_white_if_no_candidates();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Black(Some(0)),
                State::Unconfirmed,
                State::White,
                State::White,
                State::White,
                State::White,
                State::Unconfirmed,
                State::Black(Some(1)),
                State::Unconfirmed,
            ]
        );
    }
    #[test]
    fn test_set_black_if_left_end_is_confirmed() {
        // ....xo....
        let mut line = Line::new(10, vec![2, 2]);
        line.set(4, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set_black_if_left_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Black(None),
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );

        let mut line = Line::new(30, vec![2, 6, 5, 2, 1]);
        line.set(0, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(1, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(2, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(9, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(12, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.set_black_if_left_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Black(Some(0,),),
                State::Black(Some(0,),),
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
                State::Black(None,),
                State::Black(None,),
                State::Black(None,),
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

        // ....xoo.oo....x..x..
        let mut line = Line::new(20, vec![1, 2, 5, 1, 1]);
        line.set(4, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(6, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(8, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(9, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(14, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(17, State::White, Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.check_leftmost_and_rightmost();
        line.set_black_if_left_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Black(None),
                State::Unconfirmed,
                State::Black(Some(2)),
                State::Black(Some(2)),
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
    }

    #[test]
    fn test_set_black_if_right_end_is_confirmed() {
        // ....ox....
        let mut line = Line::new(10, vec![2, 2]);
        line.set(4, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(5, State::White, Operation::SetSameStateAsOrthogonal);
        line.set_black_if_right_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black(None),
                State::Black(None),
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );

        // .ox.......
        let mut line = Line::new(10, vec![2, 2]);
        line.set(1, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(2, State::White, Operation::SetSameStateAsOrthogonal);
        line.set_black_if_right_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Black(None),
                State::Black(None),
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
    }

    #[test]
    fn test_set_black_if_both_end_is_confirmed() {
        // ...x.o.x...
        let mut line = Line::new(11, vec![3, 3]);
        line.set(3, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(7, State::White, Operation::SetSameStateAsOrthogonal);
        line.set_black_if_both_end_is_confirmed();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Black(None),
                State::Black(None),
                State::White,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
    }
    #[test]
    fn test_set_white_if_too_long() {
        // ..o.......
        let mut line = Line::new(10, vec![1, 2]);
        line.set(2, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.set_white_if_too_long();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::White,
                State::Black(None),
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
            ]
        );
    }
    #[test]
    fn test_set_white_if_too_short() {
        // .....ox.x......
        let mut line = Line::new(15, vec![1, 2, 2]);
        line.set(5, State::Black(None), Operation::SetSameStateAsOrthogonal);
        line.set(6, State::White, Operation::SetSameStateAsOrthogonal);
        line.set(8, State::White, Operation::SetSameStateAsOrthogonal);
        line.check_leftmost_and_rightmost();
        line.set_white_if_too_short();
        assert_eq!(
            line.states,
            vec![
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Unconfirmed,
                State::Black(None),
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
    }
    #[test]
    fn test_5x5() {
        let mut solver = Solver::new([
            vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
            vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
        ]);
        assert!(solver.solve().is_ok());
        solver.judge();
    }
    #[test]
    fn test_10x10() {
        let mut solver = Solver::new([
            vec![
                vec![5, 1],
                vec![2, 3],
                vec![2, 2, 1],
                vec![3, 2, 2],
                vec![1, 3, 1],
                vec![2, 3],
                vec![1, 3, 1],
                vec![1, 1, 2, 2],
                vec![1, 6, 1],
                vec![5, 2],
            ],
            vec![
                vec![1, 2, 2],
                vec![7],
                vec![2, 1, 1, 2],
                vec![1, 1, 4],
                vec![2, 1, 1, 2],
                vec![9],
                vec![3, 1, 3],
                vec![3, 1],
                vec![1, 1, 1, 1],
                vec![2, 3],
            ],
        ]);
        assert!(solver.solve().is_ok());
        assert!(solver.judge());
    }
    #[test]
    fn test_15x15() {
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
        ]);
        assert!(solver.solve().is_ok());
        assert!(solver.judge());
    }

    #[test]
    fn test_20x20() {
        let mut solver = Solver::new([
            vec![
                vec![2, 8, 3, 1],
                vec![2, 1, 2, 1, 3],
                vec![1, 2, 1, 2, 1, 4],
                vec![4, 5, 2, 3],
                vec![2, 3, 1, 2, 1, 2],
                vec![1, 3, 1, 2, 1, 6],
                vec![1, 3, 1, 4, 2],
                vec![1, 7, 1, 2],
                vec![3, 2, 4, 4, 1],
                vec![1, 11],
                vec![1, 2, 1, 1, 3, 1],
                vec![1, 1, 1, 2, 2],
                vec![2, 1, 2, 2, 2],
                vec![1, 1, 3, 2, 3],
                vec![1, 3, 1, 1, 1, 1],
                vec![2, 1, 3, 5, 1],
                vec![2, 6, 1, 3, 2],
                vec![1, 1, 2, 1, 1, 1],
                vec![3, 1, 1, 2, 1, 2, 1],
                vec![1, 1, 1, 1, 6],
            ],
            vec![
                vec![1, 4, 4, 4, 2],
                vec![2, 2, 1, 1, 2, 1],
                vec![3, 1, 1, 1, 2, 2],
                vec![5, 1, 1, 1],
                vec![1, 3, 1, 1, 6],
                vec![1, 3, 3, 1, 2, 1, 1],
                vec![1, 1, 1, 1, 1, 2, 2, 1],
                vec![1, 2, 2, 3],
                vec![1, 1, 1, 2, 1, 5],
                vec![2, 1, 5, 1, 2],
                vec![3, 1, 4, 1, 2],
                vec![1, 9, 2, 1, 1],
                vec![1, 1, 1, 1, 6, 2],
                vec![1, 1, 4, 2, 1],
                vec![1, 1, 3, 5, 4, 1],
                vec![1, 2, 5, 1, 1],
                vec![4, 1, 2, 2],
                vec![5, 1, 2, 2],
                vec![6, 3, 3, 1],
                vec![1, 1, 3, 1, 2, 1],
            ],
        ]);
        assert!(solver.solve().is_ok());
        assert!(solver.judge());
    }
    #[test]
    fn test_30x30() {
        let mut solver = Solver::new([
            vec![
                vec![4, 3],
                vec![1, 3, 1, 3],
                vec![1, 2, 1, 1],
                vec![2, 2, 3, 1, 1],
                vec![1, 1, 1, 9, 3],
                vec![1, 2, 2, 2, 7, 1],
                vec![1, 5, 2, 2, 5, 1],
                vec![1, 1, 1, 1, 1, 1, 1, 5, 1],
                vec![1, 1, 1, 1, 1, 1, 5],
                vec![2, 1, 1, 2, 2, 1, 2, 1],
                vec![3, 3, 1, 1, 3, 1],
                vec![1, 4, 1, 1, 5, 1],
                vec![3, 4, 1, 1, 5],
                vec![1, 1, 3, 1, 1, 2, 2],
                vec![1, 1, 2, 1, 4, 2],
                vec![2, 6, 1, 1, 2, 3, 1],
                vec![2, 9, 2, 2, 2, 1],
                vec![4, 12, 2, 4],
                vec![14, 1, 2, 4],
                vec![8, 5, 1, 3, 4, 1],
                vec![1, 1, 4, 4, 1, 2, 3, 3, 1],
                vec![2, 6, 2, 3, 2, 1],
                vec![9, 3, 1, 3, 2, 1],
                vec![5, 1, 2, 4, 2, 8],
                vec![6, 4, 3, 3],
                vec![1, 1, 7, 3, 3],
                vec![2, 9, 3],
                vec![4, 1, 6, 3],
                vec![4, 2, 1, 6],
                vec![6, 5],
            ],
            vec![
                vec![3, 6],
                vec![3, 2, 3, 6],
                vec![2, 2, 1, 6, 3, 2],
                vec![1, 1, 2, 2, 6, 5, 2],
                vec![1, 4, 3, 8, 3],
                vec![1, 1, 1, 5, 6],
                vec![1, 4, 4, 7, 2, 2],
                vec![2, 1, 2, 3, 8, 4, 1],
                vec![3, 2, 3, 4, 6, 2],
                vec![2, 3, 5, 6, 7],
                vec![1, 7, 2, 6, 4, 1],
                vec![1, 2, 2, 6, 1, 4],
                vec![1, 3, 3, 6, 1, 2, 1],
                vec![1, 6, 4, 2, 3],
                vec![5, 5, 3, 3],
                vec![1, 2, 4, 2, 4, 1, 2],
                vec![1, 3, 2, 2, 2, 2],
                vec![1, 5, 2, 1, 3, 1],
                vec![1, 3, 3, 2, 3, 2],
                vec![2, 2, 1, 4, 2],
                vec![1, 3, 2, 2, 7],
                vec![1, 5, 2, 7],
                vec![1, 4, 2, 1, 4],
                vec![3, 3, 2, 2, 1],
                vec![1, 4, 1, 1],
                vec![1, 4, 3, 2],
                vec![3, 10],
                vec![2, 4, 2, 1],
                vec![2, 2, 1],
                vec![4, 3],
            ],
        ]);
        assert!(solver.solve().is_ok());
        assert!(solver.judge());
    }
    #[test]
    fn test_30x30_2() {
        let mut solver = Solver::new([
            vec![
                vec![3, 5, 14, 1],
                vec![2, 2, 2, 4, 7, 1],
                vec![2, 1, 1, 7, 3, 1],
                vec![3, 1, 1, 3, 3, 3, 3],
                vec![2, 1, 1, 2, 1, 2, 5, 2],
                vec![4, 2, 2, 4, 4, 4, 1],
                vec![3, 10, 4],
                vec![1, 1, 1, 3, 1, 1, 9, 3],
                vec![2, 1, 1, 1, 2, 8, 2],
                vec![2, 4, 4, 5, 4],
                vec![4, 5, 12],
                vec![4, 12],
                vec![1, 1, 7, 3],
                vec![3, 5, 1, 2],
                vec![3, 4, 3],
                vec![2, 7],
                vec![2, 1, 1, 6, 1],
                vec![3, 1, 1, 5, 1],
                vec![2, 2, 1, 4, 1],
                vec![1, 2, 1, 1, 3, 2],
                vec![4, 2, 1, 2, 2],
                vec![3, 1, 1, 2, 1, 1, 3],
                vec![10, 1, 4],
                vec![4, 1, 1, 6],
                vec![8, 1, 6, 1],
                vec![4, 2, 2, 6],
                vec![8, 1, 1, 2, 3, 4],
                vec![3, 8, 2, 3],
                vec![8, 2, 1, 8],
                vec![3, 1, 1, 1, 3],
            ],
            vec![
                vec![4, 3, 9, 3, 2],
                vec![7, 4, 6, 3, 1, 2],
                vec![1, 4, 1, 5, 2, 5, 2],
                vec![2, 1, 1, 3, 2, 3, 1, 1],
                vec![1, 2, 6, 1],
                vec![2, 1, 1, 2, 5, 1],
                vec![1, 1, 1, 2, 1, 2, 3, 1],
                vec![1, 1, 1, 2, 1, 3, 1],
                vec![1, 2, 1, 4, 1, 2],
                vec![1, 1, 1, 4, 3],
                vec![1, 1, 1, 2, 1, 2],
                vec![2, 1, 1, 2, 1],
                vec![1, 2, 1, 1, 1],
                vec![2, 1, 1, 1, 2, 7],
                vec![1, 4, 1, 2, 5, 3],
                vec![7, 5, 1, 1],
                vec![4, 3, 5],
                vec![3, 1, 8, 2],
                vec![4, 10],
                vec![1, 14, 2],
                vec![9, 7, 3],
                vec![3, 8, 5, 4],
                vec![2, 2, 6, 1, 7, 3, 1],
                vec![2, 2, 7, 7, 1, 1],
                vec![2, 3, 13, 3, 1],
                vec![3, 3, 8, 3, 1],
                vec![3, 5, 5, 1],
                vec![1, 2, 4, 7, 1],
                vec![1, 2, 2, 5, 3, 1],
                vec![1, 4, 12, 1],
            ],
        ]);
        assert!(solver.solve().is_ok());
        assert!(solver.judge());
    }
}
