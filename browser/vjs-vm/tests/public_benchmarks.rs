//! Public benchmark measurement & end-to-end equivalence test suite for `vjs_vm`.
//!
//! Runs 6 classic public benchmark kernels (`fib(28)`, `sieve(8192)`, `tak(18, 12, 6)`,
//! `gcd_sum(5000)`, `collatz_max(2000)`, `bubble_sort(256)`) on BOTH the verified AST
//! tree-walk evaluator (`eval_program`) and the verified Stack Bytecode VM (`run_vm`),
//! asserting identical computed results (and heap state) against independent native Rust
//! reference functions, measuring real wall-clock execution time, and writing
//! `browser/vjs-vm/benchmarks.json`.

use std::hint::black_box;
use std::path::PathBuf;
use std::time::Instant;

use vjs_vm::ast::{
    eval_program, expr_list_from_vec, BinOp, ExecProgramOutcome, Expr, Func, Program, Stmt,
    VmError,
};
use vjs_vm::bytecode::run_vm;
use vjs_vm::compiler::compile_program;
use vjs_vm::compiler_proof::compile_and_run_verified;

// ---------------------------------------------------------------------------
// Concise AST builders for readable kernel construction
// ---------------------------------------------------------------------------

fn c(n: i64) -> Expr {
    Expr::Const(n)
}
fn loc(i: usize) -> Expr {
    Expr::Local(i)
}
fn glob(i: usize) -> Expr {
    Expr::Global(i)
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::BinOp(op, Box::new(l), Box::new(r))
}
fn add(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Add, l, r)
}
fn sub(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Sub, l, r)
}
fn mul(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Mul, l, r)
}
fn div(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Div, l, r)
}
fn rem(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Mod, l, r)
}
fn bit_and(l: Expr, r: Expr) -> Expr {
    bin(BinOp::BitAnd, l, r)
}
fn eq_e(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Eq, l, r)
}
fn lt_e(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Lt, l, r)
}
fn le_e(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Le, l, r)
}
fn not_e(e: Expr) -> Expr {
    Expr::Not(Box::new(e))
}
fn call(f: usize, args: Vec<Expr>) -> Expr {
    Expr::Call(f, Box::new(expr_list_from_vec(args)))
}
fn arr_new(len: Expr) -> Expr {
    Expr::ArrayNew(Box::new(len))
}
fn arr_get(a: Expr, i: Expr) -> Expr {
    Expr::ArrayGet(Box::new(a), Box::new(i))
}

fn seq_all(mut stmts: Vec<Stmt>) -> Stmt {
    if stmts.is_empty() {
        return Stmt::Nop;
    }
    let mut acc = stmts.pop().unwrap();
    while let Some(prev) = stmts.pop() {
        acc = Stmt::Seq(Box::new(prev), Box::new(acc));
    }
    acc
}

fn set_l(slot: usize, e: Expr) -> Stmt {
    Stmt::SetLocal(slot, e)
}
fn arr_set(a: Expr, i: Expr, v: Expr) -> Stmt {
    Stmt::ArraySet(a, i, v)
}
fn if_s(cond: Expr, t: Stmt, e: Stmt) -> Stmt {
    Stmt::If(cond, Box::new(t), Box::new(e))
}
fn while_s(cond: Expr, body: Stmt) -> Stmt {
    Stmt::While(cond, Box::new(body))
}
fn ret(e: Expr) -> Stmt {
    Stmt::Return(e)
}

// ---------------------------------------------------------------------------
// 6 Classic Public Benchmark Kernels (AST + Native Oracle)
// ---------------------------------------------------------------------------

/// 1. `fib(28)`: recursive Fibonacci `fib(n - 1) + fib(n - 2)`
fn build_fib_program() -> Program {
    // local 0 = n
    let fib_fn = Func {
        num_params: 1,
        num_locals: 1,
        body: if_s(
            le_e(loc(0), c(1)),
            ret(loc(0)),
            ret(add(
                call(0, vec![sub(loc(0), c(1))]),
                call(0, vec![sub(loc(0), c(2))]),
            )),
        ),
    };
    Program {
        funcs: vec![fib_fn],
        entry: 0,
        num_globals: 0,
    }
}

fn native_fib(n: i64) -> i64 {
    if n <= 1 {
        n
    } else {
        native_fib(n - 1) + native_fib(n - 2)
    }
}

/// 2. `sieve(8192)`: Sieve of Eratosthenes counting primes in `2..=n`
fn build_sieve_program() -> Program {
    // local 0 = limit (8192)
    // local 1 = arr (ArrayNew(limit + 1), 0 = prime, 1 = composite)
    // local 2 = p
    // local 3 = m
    // local 4 = count
    let sieve_fn = Func {
        num_params: 1,
        num_locals: 5,
        body: seq_all(vec![
            set_l(1, arr_new(add(loc(0), c(1)))),
            set_l(2, c(2)),
            while_s(
                le_e(mul(loc(2), loc(2)), loc(0)),
                seq_all(vec![
                    if_s(
                        eq_e(arr_get(loc(1), loc(2)), c(0)),
                        seq_all(vec![
                            set_l(3, mul(loc(2), loc(2))),
                            while_s(
                                le_e(loc(3), loc(0)),
                                seq_all(vec![
                                    arr_set(loc(1), loc(3), c(1)),
                                    set_l(3, add(loc(3), loc(2))),
                                ]),
                            ),
                        ]),
                        Stmt::Nop,
                    ),
                    set_l(2, add(loc(2), c(1))),
                ]),
            ),
            set_l(4, c(0)),
            set_l(2, c(2)),
            while_s(
                le_e(loc(2), loc(0)),
                seq_all(vec![
                    if_s(
                        eq_e(arr_get(loc(1), loc(2)), c(0)),
                        set_l(4, add(loc(4), c(1))),
                        Stmt::Nop,
                    ),
                    set_l(2, add(loc(2), c(1))),
                ]),
            ),
            ret(loc(4)),
        ]),
    };
    Program {
        funcs: vec![sieve_fn],
        entry: 0,
        num_globals: 0,
    }
}

fn native_sieve(limit: usize) -> i64 {
    let mut comp = vec![false; limit + 1];
    let mut p = 2;
    while p * p <= limit {
        if !comp[p] {
            let mut m = p * p;
            while m <= limit {
                comp[m] = true;
                m += p;
            }
        }
        p += 1;
    }
    (2..=limit).filter(|&i| !comp[i]).count() as i64
}

/// 3. `tak(18, 12, 6)`: Takeuchi triple-recursion benchmark
fn build_tak_program() -> Program {
    // local 0 = x, local 1 = y, local 2 = z
    let tak_fn = Func {
        num_params: 3,
        num_locals: 3,
        body: if_s(
            not_e(lt_e(loc(1), loc(0))),
            ret(loc(2)),
            ret(call(
                0,
                vec![
                    call(0, vec![sub(loc(0), c(1)), loc(1), loc(2)]),
                    call(0, vec![sub(loc(1), c(1)), loc(2), loc(0)]),
                    call(0, vec![sub(loc(2), c(1)), loc(0), loc(1)]),
                ],
            )),
        ),
    };
    Program {
        funcs: vec![tak_fn],
        entry: 0,
        num_globals: 0,
    }
}

fn native_tak(x: i64, y: i64, z: i64) -> i64 {
    if !(y < x) {
        z
    } else {
        native_tak(
            native_tak(x - 1, y, z),
            native_tak(y - 1, z, x),
            native_tak(z - 1, x, y),
        )
    }
}

/// 4. `gcd_sum(5000)`: Euclidean GCD summed over 5,000 deterministic pairs
fn build_gcd_sum_program() -> Program {
    // func 0: gcd(a, b): local 0 = a, local 1 = b, local 2 = tmp
    let gcd_fn = Func {
        num_params: 2,
        num_locals: 3,
        body: seq_all(vec![
            while_s(
                not_e(eq_e(loc(1), c(0))),
                seq_all(vec![
                    set_l(2, rem(loc(0), loc(1))),
                    set_l(0, loc(1)),
                    set_l(1, loc(2)),
                ]),
            ),
            ret(loc(0)),
        ]),
    };
    // func 1 (entry): gcd_sum(n): local 0 = n, local 1 = i, local 2 = acc
    let entry_fn = Func {
        num_params: 1,
        num_locals: 3,
        body: seq_all(vec![
            set_l(1, c(1)),
            set_l(2, c(0)),
            while_s(
                le_e(loc(1), loc(0)),
                seq_all(vec![
                    set_l(
                        2,
                        add(
                            loc(2),
                            call(
                                0,
                                vec![
                                    add(mul(loc(1), c(37)), c(13)),
                                    add(mul(loc(1), c(91)), c(29)),
                                ],
                            ),
                        ),
                    ),
                    set_l(1, add(loc(1), c(1))),
                ]),
            ),
            ret(loc(2)),
        ]),
    };
    Program {
        funcs: vec![gcd_fn, entry_fn],
        entry: 1,
        num_globals: 0,
    }
}

fn native_gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn native_gcd_sum(n: i64) -> i64 {
    (1..=n).map(|i| native_gcd(i * 37 + 13, i * 91 + 29)).sum()
}

/// 5. `collatz_max(2000)`: Maximum Collatz stopping time over `1..=2000`
fn build_collatz_max_program() -> Program {
    // local 0 = limit, local 1 = i, local 2 = x, local 3 = steps, local 4 = max_steps
    let collatz_fn = Func {
        num_params: 1,
        num_locals: 5,
        body: seq_all(vec![
            set_l(1, c(1)),
            set_l(4, c(0)),
            while_s(
                le_e(loc(1), loc(0)),
                seq_all(vec![
                    set_l(2, loc(1)),
                    set_l(3, c(0)),
                    while_s(
                        lt_e(c(1), loc(2)),
                        seq_all(vec![
                            if_s(
                                eq_e(bit_and(loc(2), c(1)), c(0)),
                                set_l(2, div(loc(2), c(2))),
                                set_l(2, add(mul(c(3), loc(2)), c(1))),
                            ),
                            set_l(3, add(loc(3), c(1))),
                        ]),
                    ),
                    if_s(lt_e(loc(4), loc(3)), set_l(4, loc(3)), Stmt::Nop),
                    set_l(1, add(loc(1), c(1))),
                ]),
            ),
            ret(loc(4)),
        ]),
    };
    Program {
        funcs: vec![collatz_fn],
        entry: 0,
        num_globals: 0,
    }
}

fn native_collatz_max(limit: i64) -> i64 {
    let mut max_steps = 0i64;
    for i in 1..=limit {
        let mut x = i;
        let mut steps = 0i64;
        while x > 1 {
            if (x & 1) == 0 {
                x /= 2;
            } else {
                x = 3 * x + 1;
            }
            steps += 1;
        }
        if steps > max_steps {
            max_steps = steps;
        }
    }
    max_steps
}

/// 6. `bubble_sort(256)`: In-place O(N^2) sort of 256 LCG-generated integers + weighted checksum
fn build_bubble_sort_program() -> Program {
    // local 0 = n (256)
    // local 1 = arr
    // local 2 = i
    // local 3 = j
    // local 4 = seed
    // local 5 = a
    // local 6 = b
    // local 7 = checksum
    let bsort_fn = Func {
        num_params: 1,
        num_locals: 8,
        body: seq_all(vec![
            set_l(1, arr_new(loc(0))),
            set_l(4, c(1234567)),
            set_l(2, c(0)),
            while_s(
                lt_e(loc(2), loc(0)),
                seq_all(vec![
                    set_l(4, bit_and(add(mul(loc(4), c(1103515245)), c(12345)), c(0x7fff))),
                    arr_set(loc(1), loc(2), loc(4)),
                    set_l(2, add(loc(2), c(1))),
                ]),
            ),
            set_l(2, c(0)),
            while_s(
                lt_e(loc(2), loc(0)),
                seq_all(vec![
                    set_l(3, c(0)),
                    while_s(
                        lt_e(add(loc(3), c(1)), sub(loc(0), loc(2))),
                        seq_all(vec![
                            set_l(5, arr_get(loc(1), loc(3))),
                            set_l(6, arr_get(loc(1), add(loc(3), c(1)))),
                            if_s(
                                lt_e(loc(6), loc(5)),
                                seq_all(vec![
                                    arr_set(loc(1), loc(3), loc(6)),
                                    arr_set(loc(1), add(loc(3), c(1)), loc(5)),
                                ]),
                                Stmt::Nop,
                            ),
                            set_l(3, add(loc(3), c(1))),
                        ]),
                    ),
                    set_l(2, add(loc(2), c(1))),
                ]),
            ),
            set_l(7, c(0)),
            set_l(2, c(0)),
            while_s(
                lt_e(loc(2), loc(0)),
                seq_all(vec![
                    set_l(
                        7,
                        add(loc(7), mul(arr_get(loc(1), loc(2)), add(loc(2), c(1)))),
                    ),
                    set_l(2, add(loc(2), c(1))),
                ]),
            ),
            ret(loc(7)),
        ]),
    };
    Program {
        funcs: vec![bsort_fn],
        entry: 0,
        num_globals: 0,
    }
}

fn native_bubble_sort_checksum(n: usize) -> i64 {
    let mut arr = vec![0i64; n];
    let mut seed = 1234567i64;
    for slot in arr.iter_mut() {
        seed = (seed.wrapping_mul(1103515245).wrapping_add(12345)) & 0x7fff;
        *slot = seed;
    }
    arr.sort();
    arr.iter()
        .enumerate()
        .map(|(i, &v)| v * ((i as i64) + 1))
        .sum()
}

// ---------------------------------------------------------------------------
// Unit tests for operators, short-circuiting, globals, arrays, and traps
// ---------------------------------------------------------------------------

#[test]
fn semantic_equivalence_edge_cases_and_traps() {
    // 1. Short-circuit LogAnd / LogOr: RHS divides by zero if evaluated!
    let sc_prog = Program {
        funcs: vec![Func {
            num_params: 2,
            num_locals: 2,
            body: ret(add(
                mul(
                    c(10),
                    Expr::LogAnd(Box::new(loc(0)), Box::new(div(c(100), loc(1)))),
                ),
                Expr::LogOr(Box::new(not_e(loc(0))), Box::new(div(c(100), loc(1)))),
            )),
        }],
        entry: 0,
        num_globals: 2,
    };
    // loc(0) = 0, loc(1) = 0: LogAnd short-circuits to 0, LogOr(not(0), 100/0) short-circuits to 1!
    let (ast_out, vm_out) = compile_and_run_verified(&sc_prog, &[0, 0], 500, 5_000).unwrap();
    assert_eq!(ast_out, vm_out);
    assert!(matches!(ast_out, ExecProgramOutcome::Done { val: 1, .. }));

    // When loc(0) = 1, loc(1) = 0: LogAnd evaluates RHS `100 / 0` -> BOTH trap identically with DivisionByZero!
    let (ast_trap, vm_trap) = compile_and_run_verified(&sc_prog, &[1, 0], 500, 5_000).unwrap();
    assert_eq!(ast_trap, ExecProgramOutcome::Trap(VmError::DivisionByZero));
    assert_eq!(vm_trap, ExecProgramOutcome::Trap(VmError::DivisionByZero));

    // 2. Signed i64::MIN / -1 and i64::MIN % -1 + globals + bitwise ops
    let edge_prog = Program {
        funcs: vec![Func {
            num_params: 2,
            num_locals: 2,
            body: seq_all(vec![
                Stmt::SetGlobal(0, div(loc(0), loc(1))),
                Stmt::SetGlobal(1, rem(loc(0), loc(1))),
                ret(bin(
                    BinOp::BitXor,
                    bin(BinOp::BitOr, glob(0), c(0x55)),
                    glob(1),
                )),
            ]),
        }],
        entry: 0,
        num_globals: 2,
    };
    let (ast_edge, vm_edge) =
        compile_and_run_verified(&edge_prog, &[i64::MIN, -1], 500, 5_000).unwrap();
    assert_eq!(ast_edge, vm_edge);
    if let ExecProgramOutcome::Done { val, globals, .. } = ast_edge {
        assert_eq!(globals, vec![i64::MIN, 0]);
        assert_eq!(val, i64::MIN | 0x55);
    } else {
        panic!("expected Done");
    }

    // 3. Out-of-bounds array access traps identically on AST and Bytecode VM
    let oob_prog = Program {
        funcs: vec![Func {
            num_params: 0,
            num_locals: 1,
            body: seq_all(vec![
                set_l(0, arr_new(c(4))),
                arr_set(loc(0), c(4), c(99)),
                ret(c(0)),
            ]),
        }],
        entry: 0,
        num_globals: 0,
    };
    let (ast_oob, vm_oob) = compile_and_run_verified(&oob_prog, &[], 500, 5_000).unwrap();
    assert_eq!(ast_oob, ExecProgramOutcome::Trap(VmError::ArrayOutOfBounds));
    assert_eq!(vm_oob, ExecProgramOutcome::Trap(VmError::ArrayOutOfBounds));
}

// ---------------------------------------------------------------------------
// Public Benchmark Harness -> writes `browser/vjs-vm/benchmarks.json`
// ---------------------------------------------------------------------------

struct BenchSpec {
    name: &'static str,
    prog: Program,
    args: Vec<i64>,
    expected: i64,
    ast_fuel: usize,
    vm_fuel: usize,
    iterations: usize,
}

#[test]
fn run_public_benchmarks_and_write_report() {
    let is_release = !cfg!(debug_assertions);
    let specs = vec![
        BenchSpec {
            name: "fib(28)",
            prog: build_fib_program(),
            args: vec![28],
            expected: native_fib(28),
            ast_fuel: 2_000_000,
            vm_fuel: 20_000_000,
            iterations: if is_release { 3 } else { 1 },
        },
        BenchSpec {
            name: "sieve(8192)",
            prog: build_sieve_program(),
            args: vec![8192],
            expected: native_sieve(8192),
            ast_fuel: 500_000,
            vm_fuel: 5_000_000,
            iterations: if is_release { 40 } else { 3 },
        },
        BenchSpec {
            name: "tak(18, 12, 6)",
            prog: build_tak_program(),
            args: vec![18, 12, 6],
            expected: native_tak(18, 12, 6),
            ast_fuel: 500_000,
            vm_fuel: 5_000_000,
            iterations: if is_release { 10 } else { 1 },
        },
        BenchSpec {
            name: "gcd_sum(5000)",
            prog: build_gcd_sum_program(),
            args: vec![5000],
            expected: native_gcd_sum(5000),
            ast_fuel: 500_000,
            vm_fuel: 5_000_000,
            iterations: if is_release { 20 } else { 2 },
        },
        BenchSpec {
            name: "collatz_max(2000)",
            prog: build_collatz_max_program(),
            args: vec![2000],
            expected: native_collatz_max(2000),
            ast_fuel: 500_000,
            vm_fuel: 5_000_000,
            iterations: if is_release { 15 } else { 2 },
        },
        BenchSpec {
            name: "bubble_sort(256)",
            prog: build_bubble_sort_program(),
            args: vec![256],
            expected: native_bubble_sort_checksum(256),
            ast_fuel: 500_000,
            vm_fuel: 5_000_000,
            iterations: if is_release { 20 } else { 2 },
        },
    ];

    let mut rows = Vec::new();
    let mut log_speedup_sum = 0.0f64;
    let mut total_ast_ms = 0.0f64;
    let mut total_bytecode_ms = 0.0f64;

    for b in &specs {
        let compiled = compile_program(&b.prog).expect("benchmark program must compile");
        let instr_count: usize = compiled.funcs.iter().map(|f| f.code.len()).sum();

        // Warmup + exact equivalence check (value, globals, AND heap arrays!)
        let warm_ast = eval_program(black_box(&b.prog), black_box(&b.args), b.ast_fuel);
        let warm_vm = run_vm(black_box(&compiled), black_box(&b.args), b.vm_fuel);
        assert_eq!(
            warm_ast, warm_vm,
            "{}: AST and Bytecode VM outcomes diverged",
            b.name
        );
        let computed = match &warm_vm {
            ExecProgramOutcome::Done { val, .. } => *val,
            other => panic!("{}: unexpected outcome {:?}", b.name, other),
        };
        assert_eq!(
            computed, b.expected,
            "{}: computed {} != native oracle {}",
            b.name, computed, b.expected
        );

        // Measure AST tree-walk evaluator
        let t0 = Instant::now();
        for _ in 0..b.iterations {
            let out = eval_program(black_box(&b.prog), black_box(&b.args), b.ast_fuel);
            match black_box(out) {
                ExecProgramOutcome::Done { val, .. } => assert_eq!(val, b.expected),
                other => panic!("{}: AST failed {:?}", b.name, other),
            }
        }
        let ast_ms = t0.elapsed().as_secs_f64() * 1000.0;

        // Measure Verified Stack Bytecode VM
        let t1 = Instant::now();
        for _ in 0..b.iterations {
            let out = run_vm(black_box(&compiled), black_box(&b.args), b.vm_fuel);
            match black_box(out) {
                ExecProgramOutcome::Done { val, .. } => assert_eq!(val, b.expected),
                other => panic!("{}: VM failed {:?}", b.name, other),
            }
        }
        let bytecode_ms = t1.elapsed().as_secs_f64() * 1000.0;

        let speedup = ast_ms / bytecode_ms.max(1e-6);
        log_speedup_sum += speedup.ln();
        total_ast_ms += ast_ms;
        total_bytecode_ms += bytecode_ms;

        let ast_ms_r = (ast_ms * 1000.0).round() / 1000.0;
        let bytecode_ms_r = (bytecode_ms * 1000.0).round() / 1000.0;
        let speedup_r = (speedup * 100.0).round() / 100.0;

        println!(
            "{:<20} iters={:<3} ast={:>8.3} ms  vm={:>8.3} ms  speedup={:>5.2}x  result={}",
            b.name, b.iterations, ast_ms_r, bytecode_ms_r, speedup_r, computed
        );

        rows.push(serde_json::json!({
            "name": b.name,
            "iterations": b.iterations,
            "ast_ms": ast_ms_r,
            "bytecode_ms": bytecode_ms_r,
            "speedup": speedup_r,
            "computed_result": computed,
            "bytecode_instructions": instr_count,
            "result_verified_equal": true
        }));
    }

    let geomean = (log_speedup_sum / (specs.len() as f64)).exp();
    let report = serde_json::json!({
        "crate": "vjs_vm",
        "profile": if is_release { "release" } else { "debug" },
        "kernel_count": specs.len(),
        "all_verified_equal": true,
        "total_ast_ms": (total_ast_ms * 1000.0).round() / 1000.0,
        "total_bytecode_ms": (total_bytecode_ms * 1000.0).round() / 1000.0,
        "geometric_mean_speedup": (geomean * 100.0).round() / 100.0,
        "benchmarks": rows,
    });

    // Only write canonical benchmarks.json in --release runs (or if file does not yet exist)
    // so `cargo test` in debug mode never overwrites release benchmark measurements.
    let report_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmarks.json");
    if is_release || !report_path.exists() {
        std::fs::write(&report_path, serde_json::to_string_pretty(&report).unwrap() + "\n")
            .expect("write benchmarks.json");
    }
}
