use illu_logi_solver::*;

#[test]
fn test_no_solution() {
    let mut solver = Solver::new([
        vec![vec![], vec![3, 1], vec![], vec![], vec![]],
        vec![vec![1, 3], vec![], vec![], vec![], vec![]],
    ]);
    let result = solver.solve();
    assert!(matches!(result, Err(SolverError::Contradiction { .. })));

    let mut solver = Solver::new([
        vec![vec![5], vec![1], vec![], vec![], vec![]],
        vec![vec![5], vec![], vec![], vec![], vec![]],
    ]);
    let result = solver.solve();
    assert!(matches!(result, Err(SolverError::Contradiction { .. })));

    let mut solver = Solver::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
    let result = solver.solve();
    assert!(matches!(result, Err(SolverError::Indeterminate)));
}

#[test]
fn test_5x5() {
    let _solver = Solver::new([
        vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
        vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
    ]);
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
            vec![1, 1, 2, 3, 1, 3, 1],
            vec![1, 2, 1, 1, 1, 1, 2, 2, 2],
            vec![4, 3, 1, 2, 2, 1, 5, 1, 1],
            vec![2, 1, 1, 1, 2, 4, 1, 1, 1],
            vec![1, 3, 1, 2, 1, 1, 2],
            vec![1, 2, 6, 3, 1, 1, 7],
            vec![2, 1, 1, 1, 1, 3, 1, 2],
            vec![1, 1, 2, 3, 1, 1, 1, 2],
            vec![6, 7, 2, 4, 1, 2],
            vec![2, 1, 6, 2, 1, 3, 1, 1, 2],
            vec![1, 2, 7, 1, 1, 1, 1, 2, 1],
            vec![2, 1, 1, 1, 2, 2, 1, 1, 1, 3],
            vec![1, 1, 2, 3, 1, 1, 6],
            vec![1, 2, 3, 2, 1, 2, 4],
            vec![2, 4, 1, 4, 4, 1],
            vec![1, 1, 3, 6, 1, 2, 2, 2],
            vec![2, 3, 1, 3, 3, 1, 3, 1, 1],
            vec![1, 2, 1, 1, 1, 1, 1, 3, 1],
            vec![1, 1, 1, 1, 2, 2, 2, 1, 1, 1],
            vec![2, 3, 10, 1, 1, 2],
            vec![1, 9, 1, 5, 1, 3],
            vec![3, 5, 2, 8, 2, 3],
            vec![1, 1, 2, 1, 1, 1, 3, 2, 1],
            vec![2, 3, 3, 4, 1, 4],
            vec![5, 1, 1, 1, 1, 1, 3, 1],
            vec![1, 1, 6, 1, 1, 2, 2, 2],
            vec![3, 1, 1, 3, 1, 5, 3],
            vec![1, 1, 1, 1, 1, 1, 8, 2],
            vec![1, 1, 2, 2, 1, 1, 2, 1, 2, 1],
            vec![5, 3, 1, 1, 4, 1, 2, 1],
        ],
        vec![
            vec![1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1],
            vec![3, 2, 1, 1, 1, 1, 6, 2],
            vec![2, 1, 4, 3, 1, 2, 2, 1],
            vec![1, 4, 1, 1, 1, 3, 2],
            vec![1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1],
            vec![2, 2, 1, 1, 4, 5, 1],
            vec![1, 3, 3, 12, 2, 2],
            vec![1, 2, 1, 1, 2, 3, 2, 1, 1, 3],
            vec![2, 6, 7, 2, 1],
            vec![1, 1, 3, 2, 1, 3, 1, 1],
            vec![2, 5, 4, 2, 2, 1, 1],
            vec![4, 5, 2, 2, 3, 2, 1, 1],
            vec![1, 2, 1, 3, 2, 2, 1, 2],
            vec![1, 2, 1, 2, 2, 2, 2, 2, 2],
            vec![4, 1, 5, 3, 1, 1, 1, 1],
            vec![2, 1, 4, 2, 2, 1],
            vec![4, 4, 5, 1, 1, 5],
            vec![1, 4, 1, 4, 1, 4, 1, 1],
            vec![2, 1, 1, 1, 3, 4],
            vec![2, 1, 4, 1, 6, 1],
            vec![1, 2, 3, 2, 2, 4],
            vec![4, 1, 2, 1, 1, 1, 2, 4],
            vec![2, 2, 1, 2, 1, 1, 1, 1, 2, 1],
            vec![1, 1, 1, 1, 4, 2, 2, 1, 1],
            vec![1, 4, 6, 4, 2, 1],
            vec![3, 1, 2, 3, 3, 2, 3, 1, 1],
            vec![1, 2, 1, 1, 2, 1, 1, 2, 1],
            vec![1, 1, 1, 1, 3, 8, 1, 1],
            vec![2, 6, 2, 1, 1, 1, 3],
            vec![4, 1, 1, 3, 1, 3, 1, 2, 2],
        ],
    ]);
    assert!(solver.solve().is_ok());
    assert!(solver.judge());
}

#[test]
fn test_advance() {
    let mut solver = Solver::new([
        vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
        vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
    ]);
    while solver.advance().unwrap().is_some() {}

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
    while solver.advance().unwrap().is_some() {}
}

#[test]
fn test_hint() {
    let mut solver = Solver::new([
        vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
        vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
    ]);
    let hint = solver.hint().unwrap().expect("a hint should be available");
    // possible_ids は action.range と同じ並び・同じ長さで、各セルの候補ブロックが揃う。
    assert_eq!(hint.possible_ids.len(), hint.action.range.len());
    assert!(hint.possible_ids.iter().all(|ids| !ids.is_empty()));
    solver.solve().unwrap();
    assert!(solver.hint().unwrap().is_none());
}

#[test]
fn test_session_rollback() {
    let constraints = [
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
    ];
    // 正解盤面から、矛盾なく置ける値を拾って set に使う。
    let mut solved = Solver::new(constraints_for_10x10());
    solved.solve().unwrap();
    let correct = |i: usize, j: usize| solved.state(i, j);

    let mut session = Session::new(constraints);
    session.set(0, 0, correct(0, 0));
    session.set(0, 1, correct(0, 1));
    session.set(1, 1, correct(1, 1));
    assert_eq!(session.state(1, 1), correct(1, 1));

    // 履歴を先頭1件に切り詰めると、それ以降の set は巻き戻る。
    session.rollback(1);
    assert_eq!(session.state(0, 0), correct(0, 0));
    assert_eq!(session.state(0, 1), State::Unconfirmed);
    assert_eq!(session.state(1, 1), State::Unconfirmed);

    // 巻き戻し後も deduce/judge は現盤面から使い捨てソルバで正しく動く。
    let grid = session.deduce().expect("この10x10は一意に解けるはず");
    for (i, row) in grid.iter().enumerate() {
        for (j, &cell) in row.iter().enumerate() {
            assert_eq!(cell, solved.state(i, j));
        }
    }
}

fn constraints_for_10x10() -> [Vec<Vec<usize>>; 2] {
    [
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
    ]
}

// REFACTORING_PLAN.md「確認済みバグ」Bug 1 の再現シナリオ:
// `Line::set_state` は `Unconfirmed` への遷移で何もしないため、
// 黒 → 未確定 に戻しても `segments_black` にセルが残る旧実装があった
// （`Solver::set` はこれをそのまま公開していた）。`Session` は `judge`
// を呼ぶたびに現盤面から `Solver::with_grid` で使い捨てソルバを
// 組み立てるため、巻き戻しの残留自体が発生しない設計になっている。
#[test]
fn test_session_bug1_unconfirmed_rollback_then_correct_placement_judges_true() {
    let mut session = Session::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
    session.set(0, 0, State::Black);
    session.set(0, 0, State::Unconfirmed); // 旧 Solver::set ではここで segments_black が残留する
    session.set(0, 0, State::White);
    session.set(0, 1, State::Black);
    session.set(1, 1, State::White);
    session.set(1, 0, State::Black);
    assert!(session.judge()); // 正解を置いたのに false になっていた（Bug 1）
}

// REFACTORING_PLAN.md「確認済みバグ」Bug 2 の再現シナリオ:
// 旧 `Solver::set` はキューに行・列を再投入しないため、`solve` が
// 一度キューを消化し切った後に `set` で情報を与えても、以降の
// `solve`/`advance` は何も推論しなかった。`Session::deduce` は
// 呼ばれるたびに新品のソルバを組み立てるので「キューの消化」という
// 概念自体が存在せず、追加の `set` がそのまま次の `deduce` に伝播する。
#[test]
fn test_session_bug2_set_after_exhausted_deduce_propagates() {
    let mut session = Session::new([vec![vec![1], vec![1]], vec![vec![1], vec![1]]]);
    assert!(matches!(session.deduce(), Err(SolverError::Indeterminate))); // 2通りの解があり未確定

    session.set(0, 0, State::Black); // 正解の1つを教える
    let grid = session
        .deduce()
        .expect("(0,0)=Black を与えれば一意に解けるはず"); // 旧実装ではまだ Indeterminate のままだった
    assert_eq!(grid[0][0], State::Black);
    assert_eq!(grid[0][1], State::White);
    assert_eq!(grid[1][0], State::White);
    assert_eq!(grid[1][1], State::Black); // 黒に確定できるはずが未確定のままだった（Bug 2）
}
