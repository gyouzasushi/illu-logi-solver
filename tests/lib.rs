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
    assert!(matches!(result, Err(SolverError::MultipleSolutions)));
}

#[test]
fn test_5x5() {
    let mut solver = Solver::new([
        vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
        vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
    ]);
    assert!(solver.solve().is_ok());
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
    eprintln!("{}", solver.turn());
}

#[test]
fn test_advance() {
    let mut solver = Solver::new([
        vec![vec![2, 1], vec![3], vec![2, 2], vec![1, 2], vec![1, 1]],
        vec![vec![3, 1], vec![4], vec![1, 1], vec![2], vec![1, 2]],
    ]);
    while let Some(Action {
        axis,
        i,
        range,
        state,
        by,
    }) = solver.advance().unwrap()
    {
        let range = if range.len() > 1 {
            format!("{:?}", (range.start..=range.end - 1))
        } else {
            format!("{}", range.start)
        };
        eprintln!("set {state:?} on {axis:?}[{i}][{range}] by {by:?}");
        eprintln!("{solver}");
    }

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
    while let Some(Action {
        axis,
        i,
        range,
        state,
        by,
    }) = solver.advance().unwrap()
    {
        let range = if range.len() > 1 {
            format!("{:?}", (range.start..=range.end - 1))
        } else {
            format!("{}", range.start)
        };
        eprintln!("set {state:?} on {axis:?}[{i}][{range}] by {by:?}");
        eprintln!("{solver}");
    }
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
    solver.rollback(3);
    eprintln!("{}", solver);
}
