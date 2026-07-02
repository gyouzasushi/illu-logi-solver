//! イラストロジック（ノノグラム）のルールベースソルバ。
//!
//! 制約（各行・各列の黒マスの連続長の並び）を [`Solver::new`] に渡すと、
//! 8つの行内推論規則を行・列交互に適用して盤面を埋める。速度優先の
//! コア [`Solver`] と、対話的な用途（ユーザーが盤面を埋めながらヒントや
//! 間違いチェックを受ける）向けの薄いラッパー [`Session`] の2層構成。
//! 使い分けの指針はそれぞれの型のdocコメントを参照。
//!
//! # クイックスタート
//!
//! ```
//! use illu_logi_solver::Solver;
//!
//! // 制約は [行の制約, 列の制約] で、各行・列は「黒マスの連続長」の並び。
//! let mut solver = Solver::new([
//!     vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
//!     vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
//! ])
//! .unwrap();
//! solver.solve().unwrap();
//! assert!(solver.judge());
//! ```
//!
//! 詳しい使い方（制約の与え方、`Solver` と `Session` の使い分け）は
//! リポジトリの README を参照。
#![warn(missing_docs)]
mod error;
mod line;
mod operation;
mod segments;
mod session;
mod solver;

pub use error::{Cause, SolverError};
pub use line::{HintBlock, State};
pub use operation::Operation;
pub use session::Session;
pub use solver::{Action, Axis, Hint, Solver};
