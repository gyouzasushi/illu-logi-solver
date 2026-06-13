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
fn test_rollback() {
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
    let _ = solver.rollback(3);
}
