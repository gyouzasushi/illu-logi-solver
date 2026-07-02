//! 規則セットの完全性の回帰テスト。
//!
//! 8規則の行推論を「完全な行推論（全配置列挙の不動点）」と比較し、
//! 完全行推論なら解けるのに Indeterminate になる盤面（gap）の数が
//! 悪化していないことを確認する。2026-07 時点の実測: 4x4全列挙 0件、
//! 5x5ランダム2万件中 0件、7x7ランダム1万件中 2件。
//! gap の正体はセル毎の候補を Range で持つ表現が候補間の相関を
//! 表せないことによる原理的限界で、規則の追加漏れではない
//! （詳細は REFACTORING_PLAN.md）。規則や候補管理を変更した際に
//! ここが増えたら推論力が退行している。
use illu_logi_solver::*;

// 現在の states と制約に整合する全配置を列挙し、
// (黒になり得るマスク, 白になり得るマスク) を返す。整合配置ゼロなら None。
fn line_masks(states: &[State], blocks: &[usize]) -> Option<(u64, u64)> {
    let mut can_black = 0u64;
    let mut can_white = 0u64;
    let mut found = false;
    // rec(i, k, mask): セル i 以降にブロック k 以降を配置
    #[allow(clippy::too_many_arguments)]
    fn rec(
        i: usize,
        k: usize,
        mask: u64,
        states: &[State],
        blocks: &[usize],
        can_black: &mut u64,
        can_white: &mut u64,
        found: &mut bool,
    ) {
        let n = states.len();
        if k == blocks.len() {
            if (i..n).any(|j| states[j] == State::Black) {
                return;
            }
            *found = true;
            *can_black |= mask;
            *can_white |= !mask & ((1u64 << n) - 1);
            return;
        }
        let b = blocks[k];
        let mut start = i;
        loop {
            if start + b > n {
                return;
            }
            // start..start+b を黒にできるか
            let ok_black = (start..start + b).all(|j| states[j] != State::White);
            // 直後のセルは白にできるか
            let ok_gap = start + b == n || states[start + b] != State::Black;
            if ok_black && ok_gap {
                let next = if start + b == n { n } else { start + b + 1 };
                let mut m = mask;
                for j in start..start + b {
                    m |= 1 << j;
                }
                rec(next, k + 1, m, states, blocks, can_black, can_white, found);
            }
            // start を白にして次へ（start が黒確定ならここで打ち切り）
            if states[start] == State::Black {
                return;
            }
            start += 1;
        }
    }
    rec(
        0,
        0,
        0,
        states,
        blocks,
        &mut can_black,
        &mut can_white,
        &mut found,
    );
    found.then_some((can_black, can_white))
}

// 完全な行推論の不動点。全確定なら Some(true)、途中で止まれば Some(false)、矛盾は None。
// axis/j は grid[i][j] と grid[j][i] を切り替えて使うため、enumerate() 化は適さない。
#[allow(clippy::needless_range_loop)]
fn dp_fixpoint(constraints: &[Vec<Vec<usize>>; 2]) -> Option<bool> {
    let n = constraints[0].len();
    let mut grid = vec![vec![State::Unconfirmed; n]; n];
    loop {
        let mut changed = false;
        for axis in 0..2 {
            for i in 0..n {
                let states: Vec<State> = (0..n)
                    .map(|j| if axis == 0 { grid[i][j] } else { grid[j][i] })
                    .collect();
                let (cb, cw) = line_masks(&states, &constraints[axis][i])?;
                for j in 0..n {
                    let b = cb >> j & 1 == 1;
                    let w = cw >> j & 1 == 1;
                    let new = match (b, w) {
                        (true, false) => State::Black,
                        (false, true) => State::White,
                        (true, true) => continue,
                        (false, false) => return None,
                    };
                    let cell = if axis == 0 {
                        &mut grid[i][j]
                    } else {
                        &mut grid[j][i]
                    };
                    if *cell != new {
                        *cell = new;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            let solved = grid
                .iter()
                .all(|row| row.iter().all(|&s| s != State::Unconfirmed));
            return Some(solved);
        }
    }
}

fn constraints_of(grid: &[Vec<bool>]) -> [Vec<Vec<usize>>; 2] {
    let n = grid.len();
    let runs = |cells: &mut dyn Iterator<Item = bool>| -> Vec<usize> {
        let mut v = Vec::new();
        let mut run = 0;
        for cell in cells {
            if cell {
                run += 1;
            } else if run > 0 {
                v.push(run);
                run = 0;
            }
        }
        if run > 0 {
            v.push(run);
        }
        v
    };
    [
        (0..n)
            .map(|y| runs(&mut (0..n).map(|x| grid[y][x])))
            .collect(),
        (0..n)
            .map(|x| runs(&mut (0..n).map(|y| grid[y][x])))
            .collect(),
    ]
}

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn run_experiment(grids: impl Iterator<Item = Vec<Vec<bool>>>, label: &str, max_gap: u64) {
    let mut total = 0u64;
    let mut solver_ok = 0u64;
    let mut both_stuck = 0u64; // 完全行推論でも未確定 → 規則セットのせいではない
    let mut gap = 0u64; // 完全行推論なら解けるのに Indeterminate → 規則の不足
    for grid in grids {
        total += 1;
        let constraints = constraints_of(&grid);
        let mut solver = Solver::new(constraints.clone());
        match solver.solve() {
            Ok(()) => solver_ok += 1,
            Err(SolverError::Indeterminate) => match dp_fixpoint(&constraints) {
                Some(true) => gap += 1,
                Some(false) => both_stuck += 1,
                None => panic!("dp contradiction on solvable grid: {grid:?}"),
            },
            Err(e) => panic!("contradiction on solvable grid: {grid:?}\n{e}"),
        }
    }
    println!("{label}: total={total} solver_ok={solver_ok} both_stuck={both_stuck} gap={gap}");
    assert!(
        gap <= max_gap,
        "{label}: gap={gap} > {max_gap}: 完全行推論なら解ける盤面の取りこぼしが増えた（推論力の退行）"
    );
}

#[test]
fn completeness_4x4_exhaustive() {
    let n = 4;
    run_experiment(
        (0u64..1 << (n * n)).map(|bits| {
            (0..n)
                .map(|y| (0..n).map(|x| bits >> (y * n + x) & 1 == 1).collect())
                .collect()
        }),
        "4x4 exhaustive",
        0,
    );
}

#[test]
fn completeness_5x5_random() {
    let mut rng = XorShift(0x243F6A8885A308D3);
    run_experiment(
        (0..20_000).map(move |_| {
            (0..5)
                .map(|_| {
                    let bits = rng.next();
                    (0..5).map(|x| bits >> x & 1 == 1).collect()
                })
                .collect()
        }),
        "5x5 random",
        0,
    );
}

#[test]
fn completeness_7x7_random() {
    let mut rng = XorShift(0x9E3779B97F4A7C15);
    run_experiment(
        (0..10_000).map(move |_| {
            (0..7)
                .map(|_| {
                    let bits = rng.next();
                    (0..7).map(|x| bits >> x & 1 == 1).collect()
                })
                .collect()
        }),
        "7x7 random",
        2,
    );
}

// gap の中身を目視したいとき用: cargo test --test completeness show_gap_cases -- --ignored --nocapture
#[test]
#[ignore]
fn show_gap_cases() {
    let mut rng = XorShift(0x9E3779B97F4A7C15);
    for iter in 0..10_000 {
        let grid: Vec<Vec<bool>> = (0..7)
            .map(|_| {
                let bits = rng.next();
                (0..7).map(|x| bits >> x & 1 == 1).collect()
            })
            .collect();
        let constraints = constraints_of(&grid);
        let mut solver = Solver::new(constraints.clone());
        if matches!(solver.solve(), Err(SolverError::Indeterminate))
            && dp_fixpoint(&constraints) == Some(true)
        {
            println!("=== gap case iter {iter} ===");
            println!("rows: {:?}", constraints[0]);
            println!("cols: {:?}", constraints[1]);
            println!("solver stuck at:\n{solver}");
        }
    }
}
