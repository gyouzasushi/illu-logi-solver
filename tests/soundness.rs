//! 総当たりによる健全性テスト。
//!
//! 実在の盤面から制約を生成してソルバに与える。盤面が実在する以上、
//! - `Contradiction` が返るのは確実にバグ
//! - `Ok` が返るなら `judge()` を満たさなければならない
//! - `Indeterminate` の場合も、確定済みの黒セルは元盤面と一致しなければならない
//!   （白は複数解の可能性があるため元盤面とは比較しない）
use illu_logi_solver::*;

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
    let rows = (0..n)
        .map(|y| runs(&mut (0..n).map(|x| grid[y][x])))
        .collect();
    let cols = (0..n)
        .map(|x| runs(&mut (0..n).map(|y| grid[y][x])))
        .collect();
    [rows, cols]
}

fn check(grid: &[Vec<bool>]) {
    let mut solver = Solver::new(constraints_of(grid));
    match solver.solve() {
        Ok(()) => {
            assert!(solver.judge(), "judge failed for solvable grid: {grid:?}");
        }
        Err(SolverError::Indeterminate) => {
            let n = grid.len();
            for i in 0..n {
                for j in 0..n {
                    if solver.state(i, j) == State::Black {
                        assert!(grid[i][j], "wrong Black at ({i},{j}) for grid: {grid:?}");
                    }
                }
            }
        }
        Err(e @ SolverError::Contradiction { .. }) => {
            panic!("contradiction on solvable grid: {grid:?}\n{e}");
        }
    }
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

fn random_grid(n: usize, rng: &mut XorShift) -> Vec<Vec<bool>> {
    (0..n)
        .map(|_| {
            let bits = rng.next();
            (0..n).map(|x| bits >> x & 1 == 1).collect()
        })
        .collect()
}

#[test]
fn brute_force_4x4_exhaustive() {
    let n = 4;
    for bits in 0u64..(1 << (n * n)) {
        let grid: Vec<Vec<bool>> = (0..n)
            .map(|y| (0..n).map(|x| bits >> (y * n + x) & 1 == 1).collect())
            .collect();
        check(&grid);
    }
}

#[test]
fn brute_force_5x5_random() {
    let mut rng = XorShift(0x243F6A8885A308D3);
    for _ in 0..20_000 {
        check(&random_grid(5, &mut rng));
    }
}

#[test]
fn brute_force_7x7_random() {
    let mut rng = XorShift(0x9E3779B97F4A7C15);
    for _ in 0..10_000 {
        check(&random_grid(7, &mut rng));
    }
}

#[test]
fn brute_force_10x10_random() {
    let mut rng = XorShift(0xB5026F5AA96619E9);
    for _ in 0..2_000 {
        check(&random_grid(10, &mut rng));
    }
}
