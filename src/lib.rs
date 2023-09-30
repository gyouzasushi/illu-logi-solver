mod util;

use crate::util::{BitSet, Segments, SetMinMax};
use std::{collections::VecDeque, fmt::Display, ops::Range};
use thiserror::Error;

#[derive(Debug, Clone, Copy)]
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

#[derive(Clone, Debug, PartialEq)]
enum ExecutingOperation {
    BlackIfLeftmostAndRightmostIntersect,
    WhiteIfPossibleIdIsEmpty,
    BlackIfBothEndIsConfirmed,
    BlackIfLeftEndIsConfirmed,
    BlackIfRightEndIsConfirmed,
    WhiteIfTheLengthIsConfirmed,
    WhiteIfTooLong,
    WhiteIfTooShort,
}
impl ExecutingOperation {
    fn advance(&mut self) {
        *self = match self {
            Self::BlackIfLeftmostAndRightmostIntersect => Self::WhiteIfPossibleIdIsEmpty,
            Self::WhiteIfPossibleIdIsEmpty => Self::BlackIfBothEndIsConfirmed,
            Self::BlackIfBothEndIsConfirmed => Self::BlackIfLeftEndIsConfirmed,
            Self::BlackIfLeftEndIsConfirmed => Self::BlackIfRightEndIsConfirmed,
            Self::BlackIfRightEndIsConfirmed => Self::WhiteIfTheLengthIsConfirmed,
            Self::WhiteIfTheLengthIsConfirmed => Self::WhiteIfTooLong,
            Self::WhiteIfTooLong => Self::WhiteIfTooShort,
            Self::WhiteIfTooShort => Self::BlackIfLeftmostAndRightmostIntersect,
        };
    }
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

struct Line {
    n: usize,
    hint: Vec<usize>,
    states: Vec<State>,
    segments_black: Segments,
    segments_non_white: Segments,
    segments_unconfirmed: Segments,
    _possible_id: Vec<(usize, usize)>,
    possible_size: Vec<BitSet>,
    id_range: Vec<(usize, usize)>,
    next_operation: ExecutingOperation,
    queue: VecDeque<(Range<usize>, State, Operation)>,
}

impl Line {
    fn new(n: usize, hint: Vec<usize>) -> Self {
        let m = hint.len();
        let mut possible_size = BitSet::new();
        (0..m).for_each(|id| possible_size.insert(hint[id]));
        Self {
            n,
            hint,
            states: vec![State::Unconfirmed; n],
            segments_black: Segments::new(),
            segments_non_white: Segments::new().initialize(n),
            segments_unconfirmed: Segments::new().initialize(n),
            _possible_id: vec![(0, m); n],
            possible_size: vec![possible_size; n],
            id_range: vec![(0, n); m],
            next_operation: ExecutingOperation::BlackIfLeftmostAndRightmostIntersect,
            queue: VecDeque::new(),
        }
    }
    fn possible_id(&self, j: usize) -> Range<usize> {
        self._possible_id[j].0..self._possible_id[j].1
    }
    fn set(&mut self, j: usize, state: State, by: Operation) {
        self.set_range(j..j + 1, state, by)
    }
    fn set_range(&mut self, range: Range<usize>, state: State, by: Operation) {
        if range.is_empty() {
            return;
        }
        if range.clone().all(|j| self.states[j] == state) {
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
            match (self.states[j], state) {
                (State::White, State::Unconfirmed | State::Black)
                | (State::Black, State::Unconfirmed | State::White) => {
                    return Err(LineError::Contradiction(j, self.states[j], state, by));
                }
                _ => (),
            };
            self.states[j] = state;
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
        self.states[j] = state;
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
    fn execute_operation(&mut self) {
        match self.next_operation {
            ExecutingOperation::BlackIfLeftmostAndRightmostIntersect => {
                self.set_black_if_leftmost_and_rightmost_intersect()
            }
            ExecutingOperation::WhiteIfPossibleIdIsEmpty => {
                self.set_white_if_possible_id_is_empty()
            }
            ExecutingOperation::BlackIfLeftEndIsConfirmed => {
                self.set_black_if_left_end_is_confirmed()
            }
            ExecutingOperation::BlackIfRightEndIsConfirmed => {
                self.set_black_if_right_end_is_confirmed()
            }
            ExecutingOperation::BlackIfBothEndIsConfirmed => {
                self.set_black_if_both_end_is_confirmed()
            }
            ExecutingOperation::WhiteIfTheLengthIsConfirmed => {
                self.set_white_if_the_length_is_confirmed()
            }
            ExecutingOperation::WhiteIfTooLong => self.set_white_if_too_long(),
            ExecutingOperation::WhiteIfTooShort => self.set_white_if_too_short(),
        }
        self.next_operation.advance();
    }
    fn advance(&mut self) -> Result<Option<(Range<usize>, State, Operation)>, LineError> {
        let initial_operation = self.next_operation.clone();
        self.update_possible_id()?;
        while !self.has_update() {
            self.execute_operation();
            if self.next_operation == initial_operation {
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
        let (n, m) = (self.n, self.hint.len());
        loop {
            let prev = self._possible_id.clone();
            /* 左に寄せる */
            let mut ls = vec![0; m];
            let mut j = n;
            for id in (0..m).rev() {
                j = (1..=j)
                    .rfind(|&j| {
                        matches!(self.states[j - 1], State::Black)
                            && self._possible_id[j - 1].1 <= id + 1
                    })
                    .unwrap_or(0);
                if j > self.hint[id] {
                    ls[id].setmax(j - self.hint[id]);
                }
            }
            let mut j = n;
            for id in (0..m).rev() {
                j = (1..=j)
                    .rfind(|&j| self._possible_id[j - 1].1 <= id)
                    .unwrap_or(0);
                ls[id].setmax(j);
            }
            let mut l = 0;
            for id in 0..m {
                l.setmax(ls[id]);
                let mut r = l + self.hint[id];
                if r <= self.n {
                    while let Some(j) = (l..r).rfind(|&j| self.states[j] == State::White) {
                        l = j + 1;
                        r = l + self.hint[id];
                        if r > self.n {
                            break;
                        }
                    }
                }
                self.id_range[id].0 = l;
                for j in 0..l {
                    self._possible_id[j].1.setmin(id);
                }
                l = r + 1;
            }

            /* 右に寄せる */
            let mut rs = vec![n; m];
            let mut j = 0;
            for id in 0..m {
                j = (j..self.n)
                    .find(|&j| {
                        matches!(self.states[j], State::Black) && self._possible_id[j].0 >= id
                    })
                    .unwrap_or(self.n);
                if j + self.hint[id] <= self.n {
                    rs[id].setmin(j + self.hint[id]);
                }
            }
            let mut j = 0;
            for id in 0..m {
                j = (j..self.n)
                    .find(|&j| self._possible_id[j].0 > id)
                    .unwrap_or(self.n);
                rs[id].setmin(j);
            }
            let mut r = n;
            for id in (0..m).rev() {
                r.setmin(rs[id]);
                let mut l = r.wrapping_sub(self.hint[id]);
                if l < self.n {
                    while let Some(j) = (l..r).find(|&j| self.states[j] == State::White) {
                        r = j;
                        l = r.wrapping_sub(self.hint[id]);
                        if l >= self.n {
                            break;
                        }
                    }
                }
                self.id_range[id].1 = r;
                for j in r..n {
                    self._possible_id[j].0.setmax(id + 1);
                }
                r = l.wrapping_sub(1);
            }

            for (l, r) in self.segments_black.segments() {
                let mut possible_id = (0, m);
                for j in l..r {
                    possible_id.0.setmax(self.possible_id(j).start);
                    possible_id.1.setmin(self.possible_id(j).end);
                }
                for j in l..r {
                    self._possible_id[j].0.setmax(possible_id.0);
                    self._possible_id[j].1.setmin(possible_id.1);
                }
            }

            if prev == self._possible_id {
                break;
            }
        }

        for j in 0..n {
            self.possible_size[j].clear();
            self.possible_id(j)
                .for_each(|id| self.possible_size[j].insert(self.hint[id]));
        }

        Ok(())
    }
    fn set_black_if_leftmost_and_rightmost_intersect(&mut self) {
        let m = self.hint.len();
        for id in 0..m {
            let (l, r) = self.id_range[id];
            if l >= r {
                continue;
            }
            let (l, r) = (r - self.hint[id], l + self.hint[id]);
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
            let mut min = self.possible_size[l..=r]
                .iter()
                .map(|possible_size| possible_size.min().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while r < r_max && {
                min.setmin(self.possible_size[r].min().unwrap_or(0));
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
            let mut min = self.possible_size[l..r]
                .iter()
                .map(|possible_size| possible_size.min().unwrap_or(0))
                .min()
                .unwrap_or(0);
            while l > l_min && {
                min.setmin(self.possible_size[l].min().unwrap_or(0));
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
            if (l..r).all(|j| self.states[j] == State::Unconfirmed) {
                continue;
            }
            let size = r - l;
            if self.possible_size[l..r]
                .iter()
                .all(|possible_size| possible_size.count_lt(&size) == 0)
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
            if (l == 0 || self.states[l] == State::White)
                && (r == self.n || self.states[r] == State::White)
            {
                continue;
            }
            let size = r - l;
            for j in l..r {
                if self.possible_size[j].contains(&size)
                    && self.possible_size[j].count_ge(&size) == 1
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
            if !(self.states[j] == State::Unconfirmed && self.possible_id(j).len() == 1) {
                continue;
            }
            let id = self.possible_id(j).start;
            let mut size = 1;
            if j > 0 && matches!(self.states[j - 1], State::Black) {
                size += self.segments_black.size(j - 1);
            }
            if j + 1 < self.n && matches!(self.states[j + 1], State::Black) {
                size += self.segments_black.size(j + 1);
            }
            if size > self.hint[id] {
                self.set(j, State::White, Operation::WhiteIfTooLong(j));
            }
        }
    }
    fn set_white_if_too_short(&mut self) {
        for (l, r) in self.segments_unconfirmed.segments() {
            if l > 0 && self.states[l - 1] != State::White {
                continue;
            }
            if r < self.n && self.states[r] != State::White {
                continue;
            }
            if (l..r).any(|j| self.possible_size[j].min().unwrap_or(0) > r - l) {
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
            match self.states[j] {
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
    hints: [Vec<Vec<usize>>; 2],
    lines: [Vec<Line>; 2],
    queue: VecDeque<(Axis, usize)>,
    _turn: usize,
    _max_turn: usize,
}
impl Solver {
    pub fn new(hints: [Vec<Vec<usize>>; 2]) -> Self {
        assert_eq!(hints[0].len(), hints[1].len());
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
        let queue = (0..2)
            .flat_map(|axis| (0..n).map(move |i| (axis.into(), i)))
            .collect();
        Self {
            n,
            hints,
            lines,
            queue,
            _turn: 0,
            _max_turn: 0,
        }
    }

    fn clear(&mut self) {
        self.lines = [
            self.hints[0]
                .iter()
                .map(|hint| Line::new(self.n, hint.clone()))
                .collect(),
            self.hints[1]
                .iter()
                .map(|hint| Line::new(self.n, hint.clone()))
                .collect(),
        ];
        self.queue = (0..2)
            .flat_map(|axis| (0..self.n).map(move |i| (axis.into(), i)))
            .collect();
        self._turn = 0;
    }

    pub fn solve(&mut self) -> Result<(), SolverError> {
        self._max_turn = 0;
        while let Some((axis, i)) = self.queue.pop_front() {
            while let Some((range, state, _by)) = self.lines[axis as usize][i]
                .advance()
                .map_err(|err| err.to_solver_error(axis, i))?
            {
                for j in range {
                    self.lines[axis.orthogonal() as usize][j]
                        .update(i..i + 1, state, Operation::SameStateAsOrthogonal)
                        .map_err(|err| err.to_solver_error(axis, i))?;
                    self.queue.push_back((axis.orthogonal(), j));
                }
                self._max_turn += 1;
            }
        }
        if self.lines[0]
            .iter()
            .flat_map(|segment| segment.states.clone())
            .any(|state| matches!(state, State::Unconfirmed))
        {
            Err(SolverError::MultipleSolutions)
        } else {
            assert!(self.judge());
            Ok(())
        }
    }

    pub fn rollback(&mut self, t: usize) -> Result<Option<Action>, SolverError> {
        let t = t.min(self._max_turn);
        if self._turn > t {
            self.clear();
        }
        let mut ret = None;
        while self._turn < t {
            ret = self.advance()?;
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
                    self.queue.push_back((axis.orthogonal(), j));
                }
                self._turn += 1;
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
        self._turn
    }
    pub fn max_turn(&self) -> usize {
        self._max_turn
    }

    fn judge(&self) -> bool {
        for i in 0..self.n {
            for j in 0..self.n {
                if (self.lines[0][i].states[j] == State::White)
                    ^ (self.lines[1][j].states[i] == State::White)
                {
                    return false;
                }
            }
        }
        for i in 0..self.n {
            let v = self.lines[Axis::Row as usize][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.lines[Axis::Row as usize][i].hint {
                return false;
            }
            let v = self.lines[Axis::Column as usize][i]
                .segments_black
                .segments()
                .iter()
                .map(|(l, r)| r - l)
                .collect::<Vec<_>>();
            if v != self.lines[Axis::Column as usize][i].hint {
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
            self.lines[Axis::Row as usize][i].states[j],
            self.lines[Axis::Column as usize][j].states[i]
        );
        self.lines[Axis::Row as usize][i].states[j]
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
                    match self.lines[0][y].states[x] {
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
                    match self.lines[1][x].states[y] {
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
                    match self.lines[0][y].states[x] {
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
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.flush_queue().unwrap();

        // ..........
        let mut line = Line::new(10, vec![3, 2, 2]);
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
            line.update_possible_id();
            line.set_black_if_leftmost_and_rightmost_intersect();
            line.flush_queue().unwrap();
            assert_eq!(
                line.states,
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
        assert_eq!(line.states[3], State::White);
        assert_eq!(line.states[6], State::White);
    }

    #[test]
    fn test_set_white_if_possible_id_is_empty() {
        // .o......o.
        let mut line = Line::new(10, vec![2, 2]);
        line.set_state(1, State::Black);
        line.set_state(8, State::Black);
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_white_if_possible_id_is_empty();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_left_end_is_confirmed();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_black_if_left_end_is_confirmed();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
        eprintln!("{:#?}", line.queue);
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
            line.states,
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
        line.update_possible_id();
        line.set_black_if_both_end_is_confirmed();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_white_if_too_long();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
        line.update_possible_id();
        line.set_black_if_leftmost_and_rightmost_intersect();
        line.set_white_if_too_short();
        line.flush_queue().unwrap();
        assert_eq!(
            line.states,
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
