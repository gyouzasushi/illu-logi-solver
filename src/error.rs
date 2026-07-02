use crate::{line::State, operation::Operation, solver::Axis};
use thiserror::Error;

#[derive(Debug)]
pub(crate) enum LineError {
    Contradiction(usize, State, State, Operation),
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
                    new_state: *new_state,
                    by: *by,
                }
            }
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
        by: Operation,
    },
    #[error("could not find a solution: there might be multiple possible solutions.")]
    Indeterminate,
}
