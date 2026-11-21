//! Machine-checked CompCert/CakeML-style Compiler Correctness & Simulation Proof (`vjs_vm`).
//!
//! Proves that `compile_expr`, `compile_stmt`, `compile_func`, and `compile_program` preserve
//! the exact big-step AST evaluation semantics on the small-step stack bytecode VM:
//!
//! 1. **Small-step Composition & Fuel Monotonicity**:
//!    - `lemma_vm_run_steps_add`: multi-step transitivity `Running(s0) --f1--> Running(s1) --f2--> out`.
//!    - `lemma_vm_run_steps_terminal`: terminal outcomes (`Done` / `Trap`) are stable for all larger fuels.
//! 2. **Arbitrary Code-Context & Bottom-Stack Preservation (`lemma_compile_expr_sim`, `theorem_compile_expr_prefix_suffix`)**:
//!    - Executing `spec_compile_expr(e)` embedded at `pc` inside ANY surrounding bytecode
//!      `prefix + spec_compile_expr(e) + suffix` with ANY bottom value stack `stk` and ANY
//!      caller frame stack `callers` advances `pc` to `pc + spec_compile_expr(e).len()`,
//!      preserves `locals` and `callers`, and leaves `stk.push(val)` on the stack (or produces
//!      the identical runtime `Trap`).
//! 3. **Structured Control-Flow & Statement Simulation (`lemma_compile_stmt_sim`)**:
//!    - Proves PC-relative `JumpIfFalse` + `Jump` (`If`/`Else`) and `JumpIfFalse` + `JumpBack`
//!      (`While`) simulation for arbitrary surrounding prefix/suffix and bottom stack `stk`.
//! 4. **Top-Level & End-to-End Compiler Correctness (`theorem_compile_program_correct`, `compile_and_run_verified`)**:
//!    - Proves `spec_run_vm(spec_compile_program(prog), init_locals, vm_fuel) == spec_eval_program(prog, init_locals, ast_fuel)`
//!      for all `vm_fuel >= spec_program_vm_fuel(prog, init_locals, ast_fuel)`, and connects
//!      executable `eval_program`, `compile_program`, and `run_vm` end-to-end.

use vstd::prelude::*;
use crate::ast::{eval_program, ExecProgramOutcome, Program};
use crate::bytecode::run_vm;
use crate::compiler::{compile_program, CompileError};
#[cfg(verus_keep_ghost)]
use crate::ast::{
    spec_binop, spec_eval_args, spec_eval_call_body, spec_eval_expr, spec_eval_program,
    spec_eval_stmt, spec_expr_list_len, spec_expr_list_size, spec_expr_size, spec_heap_alloc,
    spec_heap_get, spec_heap_set, spec_not, spec_pad_locals, spec_stmt_size, spec_zeros, BinOp,
    Expr, ExprList, SpecArgsOutcome, SpecExprOutcome, SpecHeap, SpecProgram, SpecProgramOutcome,
    SpecStmtOutcome, Stmt, VmError, MAX_GLOBALS,
};
#[cfg(verus_keep_ghost)]
use crate::bytecode::{
    spec_frame_return, spec_run_vm, spec_vm_run_steps, spec_vm_step, Instr, SpecCompiledProgram,
    SpecFrame, SpecVmRunOutcome, SpecVmState, SpecVmStep,
};
#[cfg(verus_keep_ghost)]
use crate::compiler::{
    lemma_expr_list_len_le_compiled, spec_binop_instr, spec_compile_args, spec_compile_expr,
    spec_compile_func, spec_compile_program, spec_compile_stmt, spec_program_code_bounded,
    MAX_CODE_LEN,
};

verus! {

// ---------------------------------------------------------------------------
// 1. Small-step execution algebra: composition & fuel monotonicity
// ---------------------------------------------------------------------------

pub proof fn lemma_vm_run_steps_zero(prog: SpecCompiledProgram, st: SpecVmState)
    ensures
        spec_vm_run_steps(prog, st, 0) == SpecVmRunOutcome::Running(st),
{
}

pub proof fn lemma_vm_run_steps_one(prog: SpecCompiledProgram, st: SpecVmState)
    ensures
        spec_vm_run_steps(prog, st, 1) == match spec_vm_step(prog, st) {
            SpecVmStep::Running(st1) => SpecVmRunOutcome::Running(st1),
            SpecVmStep::Done { val, globals, heap } =>
                SpecVmRunOutcome::Done { val, globals, heap },
            SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
        },
{
    reveal_with_fuel(spec_vm_run_steps, 2);
}

pub proof fn lemma_vm_run_steps_add(
    prog: SpecCompiledProgram,
    st: SpecVmState,
    f1: nat,
    f2: nat,
)
    requires
        spec_vm_run_steps(prog, st, f1) matches SpecVmRunOutcome::Running(_),
    ensures
        ({
            let mid = match spec_vm_run_steps(prog, st, f1) {
                SpecVmRunOutcome::Running(m) => m,
                _ => st,
            };
            spec_vm_run_steps(prog, st, f1 + f2) == spec_vm_run_steps(prog, mid, f2)
        }),
    decreases f1,
{
    if f1 == 0 {
        assert(f1 + f2 == f2);
    } else {
        match spec_vm_step(prog, st) {
            SpecVmStep::Running(st1) => {
                lemma_vm_run_steps_add(prog, st1, (f1 - 1) as nat, f2);
                assert(((f1 + f2) - 1) as nat == ((f1 - 1) as nat) + f2);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_vm_run_steps_terminal(
    prog: SpecCompiledProgram,
    st: SpecVmState,
    f1: nat,
    f2: nat,
)
    requires
        !(spec_vm_run_steps(prog, st, f1) matches SpecVmRunOutcome::Running(_)),
        f2 >= f1,
    ensures
        spec_vm_run_steps(prog, st, f2) == spec_vm_run_steps(prog, st, f1),
    decreases f1,
{
    if f1 == 0 {
    } else {
        match spec_vm_step(prog, st) {
            SpecVmStep::Running(st1) => {
                lemma_vm_run_steps_terminal(prog, st1, (f1 - 1) as nat, (f2 - 1) as nat);
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Code-embedding algebra (position-independent prefix/suffix composition)
// ---------------------------------------------------------------------------

pub open spec fn spec_code_at(code: Seq<Instr>, pc: nat, frag: Seq<Instr>) -> bool {
    pc + frag.len() <= code.len()
        && code.subrange(pc as int, (pc + frag.len()) as int) == frag
}

pub proof fn lemma_prefix_suffix_embeds(
    prefix: Seq<Instr>,
    frag: Seq<Instr>,
    suffix: Seq<Instr>,
)
    ensures
        spec_code_at(prefix + frag + suffix, prefix.len(), frag),
{
    let code = prefix + frag + suffix;
    assert(code.subrange(prefix.len() as int, (prefix.len() + frag.len()) as int) =~= frag);
}

pub proof fn lemma_code_at_split(
    code: Seq<Instr>,
    pc: nat,
    a: Seq<Instr>,
    b: Seq<Instr>,
)
    requires
        spec_code_at(code, pc, a + b),
    ensures
        spec_code_at(code, pc, a),
        spec_code_at(code, pc + a.len(), b),
{
    let ab = a + b;
    assert(code.subrange(pc as int, (pc + a.len()) as int)
        =~= ab.subrange(0, a.len() as int));
    assert(ab.subrange(0, a.len() as int) =~= a);
    assert(code.subrange((pc + a.len()) as int, (pc + a.len() + b.len()) as int)
        =~= ab.subrange(a.len() as int, (a.len() + b.len()) as int));
    assert(ab.subrange(a.len() as int, (a.len() + b.len()) as int) =~= b);
}

pub proof fn lemma_code_at_split3(
    code: Seq<Instr>,
    pc: nat,
    a: Seq<Instr>,
    b: Seq<Instr>,
    c: Seq<Instr>,
)
    requires
        spec_code_at(code, pc, a + b + c),
    ensures
        spec_code_at(code, pc, a),
        spec_code_at(code, pc + a.len(), b),
        spec_code_at(code, pc + a.len() + b.len(), c),
{
    lemma_code_at_split(code, pc, a + b, c);
    lemma_code_at_split(code, pc, a, b);
}

pub proof fn lemma_code_at_split4(
    code: Seq<Instr>,
    pc: nat,
    a: Seq<Instr>,
    b: Seq<Instr>,
    c: Seq<Instr>,
    d: Seq<Instr>,
)
    requires
        spec_code_at(code, pc, a + b + c + d),
    ensures
        spec_code_at(code, pc, a),
        spec_code_at(code, pc + a.len(), b),
        spec_code_at(code, pc + a.len() + b.len(), c),
        spec_code_at(code, pc + a.len() + b.len() + c.len(), d),
{
    lemma_code_at_split(code, pc, a + b + c, d);
    lemma_code_at_split3(code, pc, a, b, c);
}

pub proof fn lemma_code_at_single(code: Seq<Instr>, pc: nat, ins: Instr)
    requires
        spec_code_at(code, pc, seq![ins]),
    ensures
        pc < code.len(),
        code[pc as int] == ins,
{
    let sub = code.subrange(pc as int, (pc + 1) as int);
    assert(sub[0] == code[pc as int]);
    assert(seq![ins][0] == ins);
}

// ---------------------------------------------------------------------------
// 3. Call-presence predicate & compiled-environment invariant
// ---------------------------------------------------------------------------

pub open spec fn spec_expr_has_call(e: Expr) -> bool
    decreases spec_expr_size(e),
{
    match e {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) => false,
        Expr::Not(inner) => spec_expr_has_call(*inner),
        Expr::BinOp(_, l, r) | Expr::LogAnd(l, r) | Expr::LogOr(l, r) | Expr::ArrayGet(l, r) =>
            spec_expr_has_call(*l) || spec_expr_has_call(*r),
        Expr::Call(_, _) => true,
        Expr::ArrayNew(len_e) => spec_expr_has_call(*len_e),
    }
}

pub open spec fn spec_args_has_call(args: ExprList) -> bool
    decreases spec_expr_list_size(args),
{
    match args {
        ExprList::Nil => false,
        ExprList::Cons(h, t) => spec_expr_has_call(*h) || spec_args_has_call(*t),
    }
}

pub open spec fn spec_stmt_has_call(s: Stmt) -> bool
    decreases spec_stmt_size(s),
{
    match s {
        Stmt::Nop => false,
        Stmt::SetLocal(_, e) | Stmt::SetGlobal(_, e) | Stmt::ExprStmt(e) | Stmt::Return(e) =>
            spec_expr_has_call(e),
        Stmt::ArraySet(a, i, v) =>
            spec_expr_has_call(a) || spec_expr_has_call(i) || spec_expr_has_call(v),
        Stmt::If(c, t, f) =>
            spec_expr_has_call(c) || spec_stmt_has_call(*t) || spec_stmt_has_call(*f),
        Stmt::While(c, b) =>
            spec_expr_has_call(c) || spec_stmt_has_call(*b),
        Stmt::Seq(s1, s2) =>
            spec_stmt_has_call(*s1) || spec_stmt_has_call(*s2),
    }
}

pub open spec fn spec_env_compiled(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    has_calls: bool,
) -> bool {
    !has_calls || (
        vm_prog == spec_compile_program(ast_prog)
        && spec_program_code_bounded(ast_prog)
    )
}

// ---------------------------------------------------------------------------
// 4. Constructive VM step-count witnesses
// ---------------------------------------------------------------------------

pub open spec fn spec_expr_vm_steps(
    prog: SpecProgram,
    e: Expr,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> nat
    decreases fuel, 0nat, spec_expr_size(e),
{
    match e {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) => 1,
        Expr::Not(inner) => {
            let k1 = spec_expr_vm_steps(prog, *inner, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *inner, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { .. } => k1 + 1,
                _ => k1,
            }
        },
        Expr::BinOp(_, lhs, rhs) | Expr::ArrayGet(lhs, rhs) => {
            let k1 = spec_expr_vm_steps(prog, *lhs, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: _, globals: g1, heap: h1 } => {
                    let k2 = spec_expr_vm_steps(prog, *rhs, locals, g1, h1, fuel);
                    match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                        SpecExprOutcome::Ok { .. } => k1 + k2 + 1,
                        _ => k1 + k2,
                    }
                },
                _ => k1,
            }
        },
        Expr::LogAnd(lhs, rhs) => {
            let k1 = spec_expr_vm_steps(prog, *lhs, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    if v1 == 0 {
                        k1 + 2
                    } else {
                        let k2 = spec_expr_vm_steps(prog, *rhs, locals, g1, h1, fuel);
                        match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                            SpecExprOutcome::Ok { .. } => k1 + 1 + k2 + 3,
                            _ => k1 + 1 + k2,
                        }
                    }
                },
                _ => k1,
            }
        },
        Expr::LogOr(lhs, rhs) => {
            let k1 = spec_expr_vm_steps(prog, *lhs, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    if v1 != 0 {
                        k1 + 3
                    } else {
                        let k2 = spec_expr_vm_steps(prog, *rhs, locals, g1, h1, fuel);
                        match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                            SpecExprOutcome::Ok { .. } => k1 + 2 + k2 + 3,
                            _ => k1 + 2 + k2,
                        }
                    }
                },
                _ => k1,
            }
        },
        Expr::Call(func_idx, args) => {
            let ka = spec_args_vm_steps(prog, *args, locals, globals, heap, fuel);
            match spec_eval_args(prog, *args, locals, globals, heap, fuel) {
                SpecArgsOutcome::Ok { vals, globals: g1, heap: h1 } => {
                    if (func_idx as nat) >= prog.funcs.len() {
                        ka + 1
                    } else {
                        let callee = prog.funcs[func_idx as int];
                        if vals.len() != callee.num_params as nat {
                            ka + 1
                        } else {
                            match spec_pad_locals(vals, callee.num_locals) {
                                None => ka + 1,
                                Some(callee_locals) => {
                                    if fuel == 0 {
                                        0
                                    } else {
                                        ka + 1 + spec_call_vm_steps(
                                            prog,
                                            func_idx,
                                            callee_locals,
                                            g1,
                                            h1,
                                            (fuel - 1) as nat,
                                        )
                                    }
                                },
                            }
                        }
                    }
                },
                _ => ka,
            }
        },
        Expr::ArrayNew(len_e) => {
            let k1 = spec_expr_vm_steps(prog, *len_e, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *len_e, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { .. } => k1 + 1,
                _ => k1,
            }
        },
    }
}

pub open spec fn spec_args_vm_steps(
    prog: SpecProgram,
    args: ExprList,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> nat
    decreases fuel, 0nat, spec_expr_list_size(args), 1nat,
{
    match args {
        ExprList::Nil => 0,
        ExprList::Cons(head, tail) => {
            let kh = spec_expr_vm_steps(prog, *head, locals, globals, heap, fuel);
            match spec_eval_expr(prog, *head, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: _, globals: g1, heap: h1 } =>
                    kh + spec_args_vm_steps(prog, *tail, locals, g1, h1, fuel),
                _ => kh,
            }
        },
    }
}

pub open spec fn spec_call_vm_steps(
    prog: SpecProgram,
    func_idx: usize,
    callee_locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> nat
    decreases fuel, 1nat, 0nat, 1nat,
{
    if (func_idx as nat) >= prog.funcs.len() {
        1
    } else {
        let body = prog.funcs[func_idx as int].body;
        let ks = spec_stmt_vm_steps(prog, body, callee_locals, globals, heap, fuel);
        match spec_eval_stmt(prog, body, callee_locals, globals, heap, fuel) {
            SpecStmtOutcome::Normal { .. } => ks + 2,
            _ => ks,
        }
    }
}

pub open spec fn spec_stmt_vm_steps(
    prog: SpecProgram,
    s: Stmt,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> nat
    decreases fuel, 0nat, spec_stmt_size(s),
{
    match s {
        Stmt::Nop => 0,
        Stmt::SetLocal(_, expr)
        | Stmt::SetGlobal(_, expr)
        | Stmt::ExprStmt(expr)
        | Stmt::Return(expr) => {
            let ke = spec_expr_vm_steps(prog, expr, locals, globals, heap, fuel);
            match spec_eval_expr(prog, expr, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { .. } => ke + 1,
                _ => ke,
            }
        },
        Stmt::ArraySet(arr_e, idx_e, val_e) => {
            let k1 = spec_expr_vm_steps(prog, arr_e, locals, globals, heap, fuel);
            match spec_eval_expr(prog, arr_e, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: _, globals: g1, heap: h1 } => {
                    let k2 = spec_expr_vm_steps(prog, idx_e, locals, g1, h1, fuel);
                    match spec_eval_expr(prog, idx_e, locals, g1, h1, fuel) {
                        SpecExprOutcome::Ok { val: _, globals: g2, heap: h2 } => {
                            let k3 = spec_expr_vm_steps(prog, val_e, locals, g2, h2, fuel);
                            match spec_eval_expr(prog, val_e, locals, g2, h2, fuel) {
                                SpecExprOutcome::Ok { .. } => k1 + k2 + k3 + 1,
                                _ => k1 + k2 + k3,
                            }
                        },
                        _ => k1 + k2,
                    }
                },
                _ => k1,
            }
        },
        Stmt::If(cond, then_s, else_s) => {
            let kc = spec_expr_vm_steps(prog, cond, locals, globals, heap, fuel);
            match spec_eval_expr(prog, cond, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
                    if vc != 0 {
                        let kt = spec_stmt_vm_steps(prog, *then_s, locals, g1, h1, fuel);
                        match spec_eval_stmt(prog, *then_s, locals, g1, h1, fuel) {
                            SpecStmtOutcome::Normal { .. } => kc + 1 + kt + 1,
                            _ => kc + 1 + kt,
                        }
                    } else {
                        let ke = spec_stmt_vm_steps(prog, *else_s, locals, g1, h1, fuel);
                        kc + 1 + ke
                    }
                },
                _ => kc,
            }
        },
        Stmt::While(cond, body) => {
            if fuel == 0 {
                0
            } else {
                let f1 = (fuel - 1) as nat;
                let kc = spec_expr_vm_steps(prog, cond, locals, globals, heap, f1);
                match spec_eval_expr(prog, cond, locals, globals, heap, f1) {
                    SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
                        if vc == 0 {
                            kc + 1
                        } else {
                            let kb = spec_stmt_vm_steps(prog, *body, locals, g1, h1, f1);
                            match spec_eval_stmt(prog, *body, locals, g1, h1, f1) {
                                SpecStmtOutcome::Normal { locals: l2, globals: g2, heap: h2 } =>
                                    kc + 1 + kb + 1 + spec_stmt_vm_steps(
                                        prog,
                                        Stmt::While(cond, body),
                                        l2,
                                        g2,
                                        h2,
                                        f1,
                                    ),
                                _ => kc + 1 + kb,
                            }
                        }
                    },
                    _ => kc,
                }
            }
        },
        Stmt::Seq(s1, s2) => {
            let k1 = spec_stmt_vm_steps(prog, *s1, locals, globals, heap, fuel);
            match spec_eval_stmt(prog, *s1, locals, globals, heap, fuel) {
                SpecStmtOutcome::Normal { locals: l1, globals: g1, heap: h1 } =>
                    k1 + spec_stmt_vm_steps(prog, *s2, l1, g1, h1, fuel),
                _ => k1,
            }
        },
    }
}

pub open spec fn spec_program_vm_fuel(
    prog: SpecProgram,
    init_locals: Seq<i64>,
    ast_fuel: nat,
) -> nat {
    if (prog.entry as nat) >= prog.funcs.len() || prog.num_globals > MAX_GLOBALS {
        1
    } else {
        match spec_pad_locals(init_locals, prog.funcs[prog.entry as int].num_locals) {
            None => 1,
            Some(locals0) => spec_call_vm_steps(
                prog,
                prog.entry,
                locals0,
                spec_zeros(prog.num_globals as nat),
                Seq::empty(),
                ast_fuel,
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// 5. Single-Instruction Atomic Step Lemmas (isolating `spec_vm_step` unfolding)
// ---------------------------------------------------------------------------

pub proof fn lemma_eval_args_len(
    prog: SpecProgram,
    args: ExprList,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
)
    ensures
        match spec_eval_args(prog, args, locals, globals, heap, fuel) {
            SpecArgsOutcome::Ok { vals, .. } => vals.len() == spec_expr_list_len(args),
            _ => true,
        },
    decreases spec_expr_list_size(args),
{
    match args {
        ExprList::Nil => {},
        ExprList::Cons(head, tail) => {
            match spec_eval_expr(prog, *head, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: _, globals: g1, heap: h1 } => {
                    lemma_eval_args_len(prog, *tail, locals, g1, h1, fuel);
                },
                _ => {},
            }
        },
    }
}

proof fn lemma_step_push_const(vm_prog: SpecCompiledProgram, st: SpecVmState, n: i64)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::PushConst(n)]),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st.cur.pc + 1,
                stack: st.cur.stack.push(n),
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::PushConst(n));
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_load_local(vm_prog: SpecCompiledProgram, st: SpecVmState, slot: usize)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::LoadLocal(slot)]),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == if (slot as nat) < st.cur.locals.len() {
            SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: st.cur.stack.push(st.cur.locals[slot as int]),
                    ..st.cur
                },
                ..st
            })
        } else {
            SpecVmRunOutcome::Trap(VmError::InvalidLocal)
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::LoadLocal(slot));
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_load_global(vm_prog: SpecCompiledProgram, st: SpecVmState, slot: usize)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::LoadGlobal(slot)]),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == if (slot as nat) < st.globals.len() {
            SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: st.cur.stack.push(st.globals[slot as int]),
                    ..st.cur
                },
                ..st
            })
        } else {
            SpecVmRunOutcome::Trap(VmError::InvalidGlobal)
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::LoadGlobal(slot));
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_not(vm_prog: SpecCompiledProgram, st: SpecVmState, stk: Seq<i64>, v: i64)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::Not]),
        st.cur.stack == stk.push(v),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st.cur.pc + 1,
                stack: stk.push(spec_not(v)),
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::Not);
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_pop(vm_prog: SpecCompiledProgram, st: SpecVmState, stk: Seq<i64>, v: i64)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::Pop]),
        st.cur.stack == stk.push(v),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st.cur.pc + 1,
                stack: stk,
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::Pop);
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_store_local(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    val: i64,
    slot: usize,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::StoreLocal(slot)]),
        st.cur.stack == stk.push(val),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == if (slot as nat) < st.cur.locals.len() {
            SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    locals: st.cur.locals.update(slot as int, val),
                    stack: stk,
                    ..st.cur
                },
                ..st
            })
        } else {
            SpecVmRunOutcome::Trap(VmError::InvalidLocal)
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::StoreLocal(slot));
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_store_global(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    val: i64,
    slot: usize,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::StoreGlobal(slot)]),
        st.cur.stack == stk.push(val),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == if (slot as nat) < st.globals.len() {
            SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: stk,
                    ..st.cur
                },
                globals: st.globals.update(slot as int, val),
                ..st
            })
        } else {
            SpecVmRunOutcome::Trap(VmError::InvalidGlobal)
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::StoreGlobal(slot));
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_binop(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    v1: i64,
    v2: i64,
    op: BinOp,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![spec_binop_instr(op)]),
        st.cur.stack == stk.push(v1).push(v2),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == match spec_binop(op, v1, v2) {
            Ok(res) => SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: stk.push(res),
                    ..st.cur
                },
                ..st
            }),
            Err(err) => SpecVmRunOutcome::Trap(err),
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, spec_binop_instr(op));
    let s = stk.push(v1).push(v2);
    assert(s.subrange(0, s.len() - 2) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_jump(vm_prog: SpecCompiledProgram, st: SpecVmState, offset: usize)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::Jump(offset)]),
        st.cur.pc + 1 + (offset as nat) <= vm_prog.funcs[st.cur.func_idx as int].code.len(),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st.cur.pc + 1 + (offset as nat),
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::Jump(offset));
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_jump_back(vm_prog: SpecCompiledProgram, st: SpecVmState, offset: usize)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::JumpBack(offset)]),
        (offset as nat) <= st.cur.pc,
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: (st.cur.pc - (offset as nat)) as nat,
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::JumpBack(offset));
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_jump_if_false(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    cond: i64,
    offset: usize,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::JumpIfFalse(offset)]),
        st.cur.stack == stk.push(cond),
        st.cur.pc + 1 + (offset as nat) <= vm_prog.funcs[st.cur.func_idx as int].code.len(),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: if cond == 0 { st.cur.pc + 1 + (offset as nat) } else { st.cur.pc + 1 },
                stack: stk,
                ..st.cur
            },
            ..st
        }),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::JumpIfFalse(offset));
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_ret(vm_prog: SpecCompiledProgram, st: SpecVmState, stk: Seq<i64>, rv: i64)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::Ret]),
        st.cur.stack == stk.push(rv),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == match spec_frame_return(st.callers, rv, st.globals, st.heap) {
            SpecVmStep::Running(sr) => SpecVmRunOutcome::Running(sr),
            SpecVmStep::Done { val, globals, heap } => SpecVmRunOutcome::Done { val, globals, heap },
            SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::Ret);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_call(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    vals: Seq<i64>,
    callee_idx: usize,
    argc: usize,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::Call(callee_idx, argc)]),
        st.cur.stack == stk + vals,
        vals.len() == argc as nat,
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == (
            if (callee_idx as nat) >= vm_prog.funcs.len() {
                SpecVmRunOutcome::Trap(VmError::InvalidCall)
            } else if argc != vm_prog.funcs[callee_idx as int].num_params {
                SpecVmRunOutcome::Trap(VmError::InvalidCall)
            } else {
                match spec_pad_locals(vals, vm_prog.funcs[callee_idx as int].num_locals) {
                    None => SpecVmRunOutcome::Trap(VmError::InvalidCall),
                    Some(callee_locals) => {
                        let saved = SpecFrame {
                            func_idx: st.cur.func_idx,
                            pc: st.cur.pc + 1,
                            locals: st.cur.locals,
                            stack: stk,
                        };
                        SpecVmRunOutcome::Running(SpecVmState {
                            cur: SpecFrame {
                                func_idx: callee_idx,
                                pc: 0,
                                locals: callee_locals,
                                stack: Seq::empty(),
                            },
                            callers: st.callers.push(saved),
                            globals: st.globals,
                            heap: st.heap,
                        })
                    },
                }
            }
        ),
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::Call(callee_idx, argc));
    let split = (st.cur.stack.len() - (argc as nat)) as int;
    assert(split == stk.len() as int);
    assert(st.cur.stack.subrange(0, split) =~= stk);
    assert(st.cur.stack.subrange(split, st.cur.stack.len() as int) =~= vals);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_array_new(vm_prog: SpecCompiledProgram, st: SpecVmState, stk: Seq<i64>, len: i64)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::ArrayNew]),
        st.cur.stack == stk.push(len),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == match spec_heap_alloc(st.heap, len) {
            Ok((id, h2)) => SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: stk.push(id),
                    ..st.cur
                },
                heap: h2,
                ..st
            }),
            Err(err) => SpecVmRunOutcome::Trap(err),
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::ArrayNew);
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 1) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_array_get(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    arr: i64,
    idx: i64,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::ArrayGet]),
        st.cur.stack == stk.push(arr).push(idx),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == match spec_heap_get(st.heap, arr, idx) {
            Ok(elem) => SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: stk.push(elem),
                    ..st.cur
                },
                ..st
            }),
            Err(err) => SpecVmRunOutcome::Trap(err),
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::ArrayGet);
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 2) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

proof fn lemma_step_array_set(
    vm_prog: SpecCompiledProgram,
    st: SpecVmState,
    stk: Seq<i64>,
    arr: i64,
    idx: i64,
    val: i64,
)
    requires
        (st.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_code_at(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, seq![Instr::ArraySet]),
        st.cur.stack == stk.push(arr).push(idx).push(val),
    ensures
        spec_vm_run_steps(vm_prog, st, 1) == match spec_heap_set(st.heap, arr, idx, val) {
            Ok(h2) => SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: stk,
                    ..st.cur
                },
                heap: h2,
                ..st
            }),
            Err(err) => SpecVmRunOutcome::Trap(err),
        },
{
    lemma_code_at_single(vm_prog.funcs[st.cur.func_idx as int].code, st.cur.pc, Instr::ArraySet);
    assert(st.cur.stack.subrange(0, st.cur.stack.len() - 3) =~= stk);
    lemma_vm_run_steps_one(vm_prog, st);
}

// Multi-step short-circuit helpers (using ONLY the atomic step lemmas!)

proof fn lemma_log_and_short_circuit(
    vm_prog: SpecCompiledProgram,
    st_mid: SpecVmState,
    stk: Seq<i64>,
    c2: Seq<Instr>,
)
    requires
        (st_mid.cur.func_idx as nat) < vm_prog.funcs.len(),
        c2.len() + 3 <= MAX_CODE_LEN as nat,
        st_mid.cur.stack == stk.push(0i64),
        spec_code_at(
            vm_prog.funcs[st_mid.cur.func_idx as int].code,
            st_mid.cur.pc,
            seq![Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)],
        ),
    ensures
        spec_vm_run_steps(vm_prog, st_mid, 2) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st_mid.cur.pc + 1 + c2.len() + 4,
                stack: stk.push(0i64),
                ..st_mid.cur
            },
            ..st_mid
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st_mid.cur.func_idx as int].code;
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)];
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    lemma_code_at_split3(code, st_mid.cur.pc, seq![jins], c2, tail);
    let pre3 = seq![Instr::Not, Instr::Not, Instr::Jump(1)];
    let last1 = seq![Instr::PushConst(0)];
    assert(pre3 + last1 =~= tail);
    lemma_code_at_split(code, st_mid.cur.pc + 1 + c2.len(), pre3, last1);
    let pc_push = st_mid.cur.pc + 1 + c2.len() + 3;
    lemma_step_jump_if_false(vm_prog, st_mid, stk, 0, (c2.len() + 3) as usize);
    let st_after_jump = SpecVmState {
        cur: SpecFrame { pc: pc_push, stack: stk, ..st_mid.cur },
        ..st_mid
    };
    lemma_step_push_const(vm_prog, st_after_jump, 0);
    lemma_vm_run_steps_add(vm_prog, st_mid, 1, 1);
}

proof fn lemma_normalize_bool_tail(
    vm_prog: SpecCompiledProgram,
    st_after_c2: SpecVmState,
    stk: Seq<i64>,
    v2: i64,
    fallback_const: i64,
)
    requires
        (st_after_c2.cur.func_idx as nat) < vm_prog.funcs.len(),
        st_after_c2.cur.stack == stk.push(v2),
        spec_code_at(
            vm_prog.funcs[st_after_c2.cur.func_idx as int].code,
            st_after_c2.cur.pc,
            seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(fallback_const)],
        ),
    ensures
        spec_vm_run_steps(vm_prog, st_after_c2, 3) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st_after_c2.cur.pc + 4,
                stack: stk.push(spec_not(spec_not(v2))),
                ..st_after_c2.cur
            },
            ..st_after_c2
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st_after_c2.cur.func_idx as int].code;
    let pc0 = st_after_c2.cur.pc;
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(fallback_const)];
    assert(seq![Instr::Not] + seq![Instr::Not] + seq![Instr::Jump(1)] + seq![Instr::PushConst(fallback_const)] =~= tail);
    lemma_code_at_split4(
        code,
        pc0,
        seq![Instr::Not],
        seq![Instr::Not],
        seq![Instr::Jump(1)],
        seq![Instr::PushConst(fallback_const)],
    );
    lemma_step_not(vm_prog, st_after_c2, stk, v2);
    let st1 = SpecVmState {
        cur: SpecFrame { pc: pc0 + 1, stack: stk.push(spec_not(v2)), ..st_after_c2.cur },
        ..st_after_c2
    };
    lemma_step_not(vm_prog, st1, stk, spec_not(v2));
    let st2 = SpecVmState {
        cur: SpecFrame { pc: pc0 + 2, stack: stk.push(spec_not(spec_not(v2))), ..st_after_c2.cur },
        ..st_after_c2
    };
    lemma_step_jump(vm_prog, st2, 1);
    lemma_vm_run_steps_add(vm_prog, st_after_c2, 1, 1);
    lemma_vm_run_steps_add(vm_prog, st_after_c2, 2, 1);
}

proof fn lemma_log_or_short_circuit(
    vm_prog: SpecCompiledProgram,
    st_mid: SpecVmState,
    stk: Seq<i64>,
    v1: i64,
    c2: Seq<Instr>,
)
    requires
        (st_mid.cur.func_idx as nat) < vm_prog.funcs.len(),
        c2.len() + 3 <= MAX_CODE_LEN as nat,
        v1 != 0,
        st_mid.cur.stack == stk.push(v1),
        spec_code_at(
            vm_prog.funcs[st_mid.cur.func_idx as int].code,
            st_mid.cur.pc,
            seq![Instr::Not, Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)],
        ),
    ensures
        spec_vm_run_steps(vm_prog, st_mid, 3) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                pc: st_mid.cur.pc + 2 + c2.len() + 4,
                stack: stk.push(1i64),
                ..st_mid.cur
            },
            ..st_mid
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st_mid.cur.func_idx as int].code;
    let pc0 = st_mid.cur.pc;
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)];
    assert(seq![Instr::Not] + seq![jins] =~= seq![Instr::Not, jins]);
    lemma_code_at_split4(code, pc0, seq![Instr::Not], seq![jins], c2, tail);
    let pre3 = seq![Instr::Not, Instr::Not, Instr::Jump(1)];
    let last1 = seq![Instr::PushConst(1)];
    assert(pre3 + last1 =~= tail);
    lemma_code_at_split(code, pc0 + 2 + c2.len(), pre3, last1);

    lemma_step_not(vm_prog, st_mid, stk, v1);
    let st1 = SpecVmState {
        cur: SpecFrame { pc: pc0 + 1, stack: stk.push(0i64), ..st_mid.cur },
        ..st_mid
    };
    lemma_step_jump_if_false(vm_prog, st1, stk, 0, (c2.len() + 3) as usize);
    let st2 = SpecVmState {
        cur: SpecFrame { pc: pc0 + 2 + c2.len() + 3, stack: stk, ..st_mid.cur },
        ..st_mid
    };
    lemma_step_push_const(vm_prog, st2, 1);
    lemma_vm_run_steps_add(vm_prog, st_mid, 1, 1);
    lemma_vm_run_steps_add(vm_prog, st_mid, 2, 1);
}

#[verifier::spinoff_prover]
proof fn lemma_log_and_prepare_rhs(
    vm_prog: SpecCompiledProgram,
    st0: SpecVmState,
    st1: SpecVmState,
    stk: Seq<i64>,
    v1: i64,
    k1: nat,
    c1: Seq<Instr>,
    c2: Seq<Instr>,
)
    requires
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        c1.len() + c2.len() + 5 <= MAX_CODE_LEN as nat,
        v1 != 0,
        st1 == (SpecVmState {
            cur: SpecFrame {
                func_idx: st0.cur.func_idx,
                pc: st0.cur.pc + c1.len(),
                locals: st0.cur.locals,
                stack: stk.push(v1),
            },
            ..st1
        }),
        spec_vm_run_steps(vm_prog, st0, k1) == SpecVmRunOutcome::Running(st1),
        spec_code_at(
            vm_prog.funcs[st0.cur.func_idx as int].code,
            st1.cur.pc,
            seq![Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)],
        ),
    ensures
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st1.cur.pc + 1, c2),
        spec_code_at(
            vm_prog.funcs[st0.cur.func_idx as int].code,
            st1.cur.pc + 1 + c2.len(),
            seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)],
        ),
        spec_vm_run_steps(vm_prog, st0, k1 + 1) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame { pc: st1.cur.pc + 1, stack: stk, ..st1.cur },
            ..st1
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)];
    lemma_code_at_split3(code, st1.cur.pc, seq![jins], c2, tail);
    lemma_step_jump_if_false(vm_prog, st1, stk, v1, (c2.len() + 3) as usize);
    lemma_vm_run_steps_add(vm_prog, st0, k1, 1);
}

#[verifier::spinoff_prover]
proof fn lemma_log_or_prepare_rhs(
    vm_prog: SpecCompiledProgram,
    st0: SpecVmState,
    st1: SpecVmState,
    stk: Seq<i64>,
    k1: nat,
    c1: Seq<Instr>,
    c2: Seq<Instr>,
)
    requires
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        c1.len() + c2.len() + 6 <= MAX_CODE_LEN as nat,
        st1 == (SpecVmState {
            cur: SpecFrame {
                func_idx: st0.cur.func_idx,
                pc: st0.cur.pc + c1.len(),
                locals: st0.cur.locals,
                stack: stk.push(0i64),
            },
            ..st1
        }),
        spec_vm_run_steps(vm_prog, st0, k1) == SpecVmRunOutcome::Running(st1),
        spec_code_at(
            vm_prog.funcs[st0.cur.func_idx as int].code,
            st1.cur.pc,
            seq![Instr::Not, Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)],
        ),
    ensures
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st1.cur.pc + 2, c2),
        spec_code_at(
            vm_prog.funcs[st0.cur.func_idx as int].code,
            st1.cur.pc + 2 + c2.len(),
            seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)],
        ),
        spec_vm_run_steps(vm_prog, st0, k1 + 2) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame { pc: st1.cur.pc + 2, stack: stk, ..st1.cur },
            ..st1
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)];
    assert(seq![Instr::Not] + seq![jins] =~= seq![Instr::Not, jins]);
    lemma_code_at_split4(code, st1.cur.pc, seq![Instr::Not], seq![jins], c2, tail);
    lemma_step_not(vm_prog, st1, stk, 0);
    let st_not = SpecVmState {
        cur: SpecFrame { pc: st1.cur.pc + 1, stack: stk.push(1i64), ..st1.cur },
        ..st1
    };
    lemma_step_jump_if_false(vm_prog, st_not, stk, 1, (c2.len() + 3) as usize);
    lemma_vm_run_steps_add(vm_prog, st0, k1, 1);
    lemma_vm_run_steps_add(vm_prog, st0, k1 + 1, 1);
}

#[verifier::spinoff_prover]
proof fn lemma_call_epilogue_normal(
    vm_prog: SpecCompiledProgram,
    st_callee: SpecVmState,
    func_idx: usize,
    cb: Seq<Instr>,
    lf: Seq<i64>,
    gf: Seq<i64>,
    hf: SpecHeap,
    ks: nat,
)
    requires
        (func_idx as nat) < vm_prog.funcs.len(),
        st_callee.cur.func_idx == func_idx,
        vm_prog.funcs[func_idx as int].code == cb + seq![Instr::PushConst(0), Instr::Ret],
        spec_vm_run_steps(vm_prog, st_callee, ks) == SpecVmRunOutcome::Running(SpecVmState {
            cur: SpecFrame {
                func_idx,
                pc: cb.len(),
                locals: lf,
                stack: st_callee.cur.stack,
            },
            callers: st_callee.callers,
            globals: gf,
            heap: hf,
        }),
    ensures
        spec_vm_run_steps(vm_prog, st_callee, ks + 2) == match spec_frame_return(st_callee.callers, 0, gf, hf) {
            SpecVmStep::Running(s) => SpecVmRunOutcome::Running(s),
            SpecVmStep::Done { val, globals, heap } => SpecVmRunOutcome::Done { val, globals, heap },
            SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
        },
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[func_idx as int].code;
    let epilogue = seq![Instr::PushConst(0), Instr::Ret];
    assert(Seq::<Instr>::empty() + (cb + epilogue) + Seq::<Instr>::empty() =~= code);
    lemma_prefix_suffix_embeds(Seq::<Instr>::empty(), cb + epilogue, Seq::<Instr>::empty());
    lemma_code_at_split(code, 0, cb, epilogue);
    assert(seq![Instr::PushConst(0)] + seq![Instr::Ret] =~= epilogue);
    lemma_code_at_split(code, cb.len(), seq![Instr::PushConst(0)], seq![Instr::Ret]);
    let st_end = SpecVmState {
        cur: SpecFrame {
            func_idx,
            pc: cb.len(),
            locals: lf,
            stack: st_callee.cur.stack,
        },
        callers: st_callee.callers,
        globals: gf,
        heap: hf,
    };
    lemma_step_push_const(vm_prog, st_end, 0);
    let st_ret = SpecVmState {
        cur: SpecFrame {
            func_idx,
            pc: cb.len() + 1,
            locals: lf,
            stack: st_callee.cur.stack.push(0i64),
        },
        callers: st_callee.callers,
        globals: gf,
        heap: hf,
    };
    lemma_step_ret(vm_prog, st_ret, st_callee.cur.stack, 0);
    lemma_vm_run_steps_add(vm_prog, st_callee, ks, 1);
    lemma_vm_run_steps_add(vm_prog, st_callee, ks + 1, 1);
}

pub open spec fn spec_expr_sim_post(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    e: Expr,
    st0: SpecVmState,
    fuel: nat,
) -> bool {
    let steps = spec_expr_vm_steps(ast_prog, e, st0.cur.locals, st0.globals, st0.heap, fuel);
    let run = spec_vm_run_steps(vm_prog, st0, steps);
    match spec_eval_expr(ast_prog, e, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val, globals: gf, heap: hf } =>
            run == SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + spec_compile_expr(e).len(),
                    locals: st0.cur.locals,
                    stack: st0.cur.stack.push(val),
                },
                callers: st0.callers,
                globals: gf,
                heap: hf,
            }),
        SpecExprOutcome::Trap(err) => run == SpecVmRunOutcome::Trap(err),
        SpecExprOutcome::OutOfFuel => true,
    }
}

pub open spec fn spec_stmt_sim_post(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    s: Stmt,
    st0: SpecVmState,
    fuel: nat,
) -> bool {
    let steps = spec_stmt_vm_steps(ast_prog, s, st0.cur.locals, st0.globals, st0.heap, fuel);
    let run = spec_vm_run_steps(vm_prog, st0, steps);
    match spec_eval_stmt(ast_prog, s, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecStmtOutcome::Normal { locals: lf, globals: gf, heap: hf } =>
            run == SpecVmRunOutcome::Running(SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + spec_compile_stmt(s).len(),
                    locals: lf,
                    stack: st0.cur.stack,
                },
                callers: st0.callers,
                globals: gf,
                heap: hf,
            }),
        SpecStmtOutcome::Return { val: rv, locals: _, globals: gf, heap: hf } =>
            run == match spec_frame_return(st0.callers, rv, gf, hf) {
                SpecVmStep::Running(sr) => SpecVmRunOutcome::Running(sr),
                SpecVmStep::Done { val, globals, heap } =>
                    SpecVmRunOutcome::Done { val, globals, heap },
                SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
            },
        SpecStmtOutcome::Trap(err) => run == SpecVmRunOutcome::Trap(err),
        SpecStmtOutcome::OutOfFuel => true,
    }
}

// ---------------------------------------------------------------------------
// 6. Core Mutual Simulation Theorem (per-constructor parallel spinoff provers)
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
proof fn lemma_sim_binop(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    op: BinOp,
    lhs: Box<Expr>,
    rhs: Box<Expr>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(Expr::BinOp(op, lhs, rhs))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(Expr::BinOp(op, lhs, rhs)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(Expr::BinOp(op, lhs, rhs))),
        !(spec_eval_expr(ast_prog, Expr::BinOp(op, lhs, rhs), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, Expr::BinOp(op, lhs, rhs), st0, fuel),
    decreases fuel, 0nat, spec_expr_size(Expr::BinOp(op, lhs, rhs)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let c1 = spec_compile_expr(*lhs);
    let c2 = spec_compile_expr(*rhs);
    lemma_code_at_split3(code, st0.cur.pc, c1, c2, seq![spec_binop_instr(op)]);
    lemma_compile_expr_sim(ast_prog, vm_prog, *lhs, st0, fuel);
    let k1 = spec_expr_vm_steps(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
            let st1 = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + c1.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(v1),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            let k2 = spec_expr_vm_steps(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel);
            lemma_compile_expr_sim(ast_prog, vm_prog, *rhs, st1, fuel);
            lemma_vm_run_steps_add(vm_prog, st0, k1, k2);
            match spec_eval_expr(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel) {
                SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } => {
                    let st2 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + c1.len() + c2.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(v1).push(v2),
                        },
                        callers: st0.callers,
                        globals: g2,
                        heap: h2,
                    };
                    lemma_step_binop(vm_prog, st2, stk, v1, v2, op);
                    lemma_vm_run_steps_add(vm_prog, st0, k1 + k2, 1);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_log_and(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    lhs: Box<Expr>,
    rhs: Box<Expr>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(Expr::LogAnd(lhs, rhs))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(Expr::LogAnd(lhs, rhs)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(Expr::LogAnd(lhs, rhs))),
        !(spec_eval_expr(ast_prog, Expr::LogAnd(lhs, rhs), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, Expr::LogAnd(lhs, rhs), st0, fuel),
    decreases fuel, 0nat, spec_expr_size(Expr::LogAnd(lhs, rhs)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let e = Expr::LogAnd(lhs, rhs);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let c1 = spec_compile_expr(*lhs);
    let c2 = spec_compile_expr(*rhs);
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)];
    assert(spec_compile_expr(e) =~= c1 + (seq![jins] + c2 + tail));
    lemma_code_at_split(code, st0.cur.pc, c1, seq![jins] + c2 + tail);
    lemma_compile_expr_sim(ast_prog, vm_prog, *lhs, st0, fuel);
    let k1 = spec_expr_vm_steps(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
            let st1 = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + c1.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(v1),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            if v1 == 0 {
                lemma_log_and_short_circuit(vm_prog, st1, stk, c2);
                lemma_vm_run_steps_add(vm_prog, st0, k1, 2);
            } else {
                lemma_log_and_prepare_rhs(vm_prog, st0, st1, stk, v1, k1, c1, c2);
                let st_c2 = SpecVmState {
                    cur: SpecFrame { pc: st1.cur.pc + 1, stack: stk, ..st1.cur },
                    ..st1
                };
                let k2 = spec_expr_vm_steps(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel);
                lemma_compile_expr_sim(ast_prog, vm_prog, *rhs, st_c2, fuel);
                lemma_vm_run_steps_add(vm_prog, st0, k1 + 1, k2);
                match spec_eval_expr(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel) {
                    SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } => {
                        let st_tail = SpecVmState {
                            cur: SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st1.cur.pc + 1 + c2.len(),
                                locals: st0.cur.locals,
                                stack: stk.push(v2),
                            },
                            callers: st0.callers,
                            globals: g2,
                            heap: h2,
                        };
                        lemma_normalize_bool_tail(vm_prog, st_tail, stk, v2, 0);
                        lemma_vm_run_steps_add(vm_prog, st0, k1 + 1 + k2, 3);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_log_or(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    lhs: Box<Expr>,
    rhs: Box<Expr>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(Expr::LogOr(lhs, rhs))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(Expr::LogOr(lhs, rhs)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(Expr::LogOr(lhs, rhs))),
        !(spec_eval_expr(ast_prog, Expr::LogOr(lhs, rhs), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, Expr::LogOr(lhs, rhs), st0, fuel),
    decreases fuel, 0nat, spec_expr_size(Expr::LogOr(lhs, rhs)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let e = Expr::LogOr(lhs, rhs);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let c1 = spec_compile_expr(*lhs);
    let c2 = spec_compile_expr(*rhs);
    let jins = Instr::JumpIfFalse((c2.len() + 3) as usize);
    let tail = seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)];
    let rest = seq![Instr::Not, jins] + c2 + tail;
    assert(spec_compile_expr(e) =~= c1 + rest);
    lemma_code_at_split(code, st0.cur.pc, c1, rest);
    lemma_compile_expr_sim(ast_prog, vm_prog, *lhs, st0, fuel);
    let k1 = spec_expr_vm_steps(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, *lhs, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
            let st1 = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + c1.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(v1),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            if v1 != 0 {
                lemma_log_or_short_circuit(vm_prog, st1, stk, v1, c2);
                lemma_vm_run_steps_add(vm_prog, st0, k1, 3);
            } else {
                lemma_log_or_prepare_rhs(vm_prog, st0, st1, stk, k1, c1, c2);
                let st_c2 = SpecVmState {
                    cur: SpecFrame { pc: st1.cur.pc + 2, stack: stk, ..st1.cur },
                    ..st1
                };
                let k2 = spec_expr_vm_steps(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel);
                lemma_compile_expr_sim(ast_prog, vm_prog, *rhs, st_c2, fuel);
                lemma_vm_run_steps_add(vm_prog, st0, k1 + 2, k2);
                match spec_eval_expr(ast_prog, *rhs, st0.cur.locals, g1, h1, fuel) {
                    SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } => {
                        let st_tail = SpecVmState {
                            cur: SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st1.cur.pc + 2 + c2.len(),
                                locals: st0.cur.locals,
                                stack: stk.push(v2),
                            },
                            callers: st0.callers,
                            globals: g2,
                            heap: h2,
                        };
                        lemma_normalize_bool_tail(vm_prog, st_tail, stk, v2, 1);
                        lemma_vm_run_steps_add(vm_prog, st0, k1 + 2 + k2, 3);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_call_expr(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    func_idx: usize,
    args: Box<ExprList>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(Expr::Call(func_idx, args))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(Expr::Call(func_idx, args)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(Expr::Call(func_idx, args))),
        !(spec_eval_expr(ast_prog, Expr::Call(func_idx, args), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, Expr::Call(func_idx, args), st0, fuel),
    decreases fuel, 0nat, spec_expr_size(Expr::Call(func_idx, args)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let ca = spec_compile_args(*args);
    let argc_nat = spec_expr_list_len(*args);
    lemma_expr_list_len_le_compiled(*args);
    let call_ins = Instr::Call(func_idx, argc_nat as usize);
    lemma_code_at_split(code, st0.cur.pc, ca, seq![call_ins]);
    lemma_compile_args_sim(ast_prog, vm_prog, *args, st0, fuel);
    lemma_eval_args_len(ast_prog, *args, st0.cur.locals, st0.globals, st0.heap, fuel);
    let ka = spec_args_vm_steps(ast_prog, *args, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_args(ast_prog, *args, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecArgsOutcome::Ok { vals, globals: g1, heap: h1 } => {
            let st_call = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + ca.len(),
                    locals: st0.cur.locals,
                    stack: stk + vals,
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            lemma_step_call(vm_prog, st_call, stk, vals, func_idx, argc_nat as usize);
            lemma_vm_run_steps_add(vm_prog, st0, ka, 1);
            if (func_idx as nat) < ast_prog.funcs.len() {
                let callee = ast_prog.funcs[func_idx as int];
                assert(vm_prog.funcs[func_idx as int] == spec_compile_func(callee));
                if vals.len() == callee.num_params as nat {
                    match spec_pad_locals(vals, callee.num_locals) {
                        None => {},
                        Some(callee_locals) => {
                            let saved_caller = SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st0.cur.pc + ca.len() + 1,
                                locals: st0.cur.locals,
                                stack: stk,
                            };
                            let st_callee = SpecVmState {
                                cur: SpecFrame {
                                    func_idx,
                                    pc: 0,
                                    locals: callee_locals,
                                    stack: Seq::empty(),
                                },
                                callers: st0.callers.push(saved_caller),
                                globals: g1,
                                heap: h1,
                            };
                            let kb = spec_call_vm_steps(
                                ast_prog,
                                func_idx,
                                callee_locals,
                                g1,
                                h1,
                                (fuel - 1) as nat,
                            );
                            lemma_compile_call_sim(
                                ast_prog,
                                vm_prog,
                                func_idx,
                                st_callee,
                                (fuel - 1) as nat,
                            );
                            lemma_vm_run_steps_add(vm_prog, st0, ka + 1, kb);
                            let pushed = st0.callers.push(saved_caller);
                            assert(pushed[pushed.len() - 1] == saved_caller);
                            assert(pushed.subrange(0, pushed.len() - 1) =~= st0.callers);
                        },
                    }
                }
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_array_get(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    arr_e: Box<Expr>,
    idx_e: Box<Expr>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(Expr::ArrayGet(arr_e, idx_e))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(Expr::ArrayGet(arr_e, idx_e)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(Expr::ArrayGet(arr_e, idx_e))),
        !(spec_eval_expr(ast_prog, Expr::ArrayGet(arr_e, idx_e), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, Expr::ArrayGet(arr_e, idx_e), st0, fuel),
    decreases fuel, 0nat, spec_expr_size(Expr::ArrayGet(arr_e, idx_e)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let c1 = spec_compile_expr(*arr_e);
    let c2 = spec_compile_expr(*idx_e);
    lemma_code_at_split3(code, st0.cur.pc, c1, c2, seq![Instr::ArrayGet]);
    lemma_compile_expr_sim(ast_prog, vm_prog, *arr_e, st0, fuel);
    let k1 = spec_expr_vm_steps(ast_prog, *arr_e, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, *arr_e, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: arr, globals: g1, heap: h1 } => {
            let st1 = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + c1.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(arr),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            let k2 = spec_expr_vm_steps(ast_prog, *idx_e, st0.cur.locals, g1, h1, fuel);
            lemma_compile_expr_sim(ast_prog, vm_prog, *idx_e, st1, fuel);
            lemma_vm_run_steps_add(vm_prog, st0, k1, k2);
            match spec_eval_expr(ast_prog, *idx_e, st0.cur.locals, g1, h1, fuel) {
                SpecExprOutcome::Ok { val: idx, globals: g2, heap: h2 } => {
                    let st2 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + c1.len() + c2.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(arr).push(idx),
                        },
                        callers: st0.callers,
                        globals: g2,
                        heap: h2,
                    };
                    lemma_step_array_get(vm_prog, st2, stk, arr, idx);
                    lemma_vm_run_steps_add(vm_prog, st0, k1 + k2, 1);
                },
                _ => {},
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_compile_expr_sim(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    e: Expr,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(e)),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_expr(e).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_expr(e)),
        !(spec_eval_expr(ast_prog, e, st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        spec_expr_sim_post(ast_prog, vm_prog, e, st0, fuel),
    decreases fuel, 0nat, spec_expr_size(e), 1nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    match e {
        Expr::Const(n) => lemma_step_push_const(vm_prog, st0, n),
        Expr::Local(slot) => lemma_step_load_local(vm_prog, st0, slot),
        Expr::Global(slot) => lemma_step_load_global(vm_prog, st0, slot),
        Expr::Not(inner) => {
            let ci = spec_compile_expr(*inner);
            lemma_code_at_split(code, st0.cur.pc, ci, seq![Instr::Not]);
            lemma_compile_expr_sim(ast_prog, vm_prog, *inner, st0, fuel);
            let k1 = spec_expr_vm_steps(ast_prog, *inner, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, *inner, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ci.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(v1),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_not(vm_prog, st1, stk, v1);
                    lemma_vm_run_steps_add(vm_prog, st0, k1, 1);
                },
                _ => {},
            }
        },
        Expr::BinOp(op, lhs, rhs) => lemma_sim_binop(ast_prog, vm_prog, op, lhs, rhs, st0, fuel),
        Expr::LogAnd(lhs, rhs) => lemma_sim_log_and(ast_prog, vm_prog, lhs, rhs, st0, fuel),
        Expr::LogOr(lhs, rhs) => lemma_sim_log_or(ast_prog, vm_prog, lhs, rhs, st0, fuel),
        Expr::Call(func_idx, args) => lemma_sim_call_expr(ast_prog, vm_prog, func_idx, args, st0, fuel),
        Expr::ArrayNew(len_e) => {
            let cl = spec_compile_expr(*len_e);
            lemma_code_at_split(code, st0.cur.pc, cl, seq![Instr::ArrayNew]);
            lemma_compile_expr_sim(ast_prog, vm_prog, *len_e, st0, fuel);
            let k1 = spec_expr_vm_steps(ast_prog, *len_e, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, *len_e, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val: len, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + cl.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(len),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_array_new(vm_prog, st1, stk, len);
                    lemma_vm_run_steps_add(vm_prog, st0, k1, 1);
                },
                _ => {},
            }
        },
        Expr::ArrayGet(arr_e, idx_e) => lemma_sim_array_get(ast_prog, vm_prog, arr_e, idx_e, st0, fuel),
    }
}

pub proof fn lemma_compile_args_sim(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    args: ExprList,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_args_has_call(args)),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_args(args).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_args(args)),
        !(spec_eval_args(ast_prog, args, st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecArgsOutcome::OutOfFuel),
    ensures
        ({
            let steps = spec_args_vm_steps(ast_prog, args, st0.cur.locals, st0.globals, st0.heap, fuel);
            let run = spec_vm_run_steps(vm_prog, st0, steps);
            match spec_eval_args(ast_prog, args, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecArgsOutcome::Ok { vals, globals: gf, heap: hf } =>
                    run == SpecVmRunOutcome::Running(SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + spec_compile_args(args).len(),
                            locals: st0.cur.locals,
                            stack: st0.cur.stack + vals,
                        },
                        callers: st0.callers,
                        globals: gf,
                        heap: hf,
                    }),
                SpecArgsOutcome::Trap(err) => run == SpecVmRunOutcome::Trap(err),
                SpecArgsOutcome::OutOfFuel => true,
            }
        }),
    decreases fuel, 0nat, spec_expr_list_size(args), 1nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    match args {
        ExprList::Nil => {
            lemma_vm_run_steps_zero(vm_prog, st0);
            assert(st0.cur.stack + Seq::<i64>::empty() =~= st0.cur.stack);
        },
        ExprList::Cons(head, tail) => {
            let code = vm_prog.funcs[st0.cur.func_idx as int].code;
            let ch = spec_compile_expr(*head);
            let ct = spec_compile_args(*tail);
            lemma_code_at_split(code, st0.cur.pc, ch, ct);
            lemma_compile_expr_sim(ast_prog, vm_prog, *head, st0, fuel);
            let kh = spec_expr_vm_steps(ast_prog, *head, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, *head, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val: vh, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ch.len(),
                            locals: st0.cur.locals,
                            stack: st0.cur.stack.push(vh),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    let kt = spec_args_vm_steps(ast_prog, *tail, st0.cur.locals, g1, h1, fuel);
                    lemma_compile_args_sim(ast_prog, vm_prog, *tail, st1, fuel);
                    lemma_vm_run_steps_add(vm_prog, st0, kh, kt);
                    match spec_eval_args(ast_prog, *tail, st0.cur.locals, g1, h1, fuel) {
                        SpecArgsOutcome::Ok { vals: vt, .. } => {
                            assert(st0.cur.stack.push(vh) + vt =~= st0.cur.stack + (seq![vh] + vt));
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub proof fn lemma_compile_call_sim(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    func_idx: usize,
    st_callee: SpecVmState,
    fuel: nat,
)
    requires
        vm_prog == spec_compile_program(ast_prog),
        spec_program_code_bounded(ast_prog),
        (func_idx as nat) < ast_prog.funcs.len(),
        st_callee.cur.func_idx == func_idx,
        st_callee.cur.pc == 0,
        !(spec_eval_call_body(ast_prog, func_idx, st_callee.cur.locals, st_callee.globals, st_callee.heap, fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        ({
            let steps = spec_call_vm_steps(
                ast_prog,
                func_idx,
                st_callee.cur.locals,
                st_callee.globals,
                st_callee.heap,
                fuel,
            );
            let run = spec_vm_run_steps(vm_prog, st_callee, steps);
            match spec_eval_call_body(
                ast_prog,
                func_idx,
                st_callee.cur.locals,
                st_callee.globals,
                st_callee.heap,
                fuel,
            ) {
                SpecExprOutcome::Ok { val: rv, globals: gf, heap: hf } =>
                    run == match spec_frame_return(st_callee.callers, rv, gf, hf) {
                        SpecVmStep::Running(s) => SpecVmRunOutcome::Running(s),
                        SpecVmStep::Done { val, globals, heap } =>
                            SpecVmRunOutcome::Done { val, globals, heap },
                        SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
                    },
                SpecExprOutcome::Trap(err) => run == SpecVmRunOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => true,
            }
        }),
    decreases fuel, 1nat, 0nat, 1nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let f = ast_prog.funcs[func_idx as int];
    let cf = spec_compile_func(f);
    assert(vm_prog.funcs[func_idx as int] == cf);
    assert(cf.code.len() <= MAX_CODE_LEN as nat);
    let cb = spec_compile_stmt(f.body);
    let epilogue = seq![Instr::PushConst(0), Instr::Ret];
    assert(cf.code =~= Seq::<Instr>::empty() + cb + epilogue);
    lemma_prefix_suffix_embeds(Seq::<Instr>::empty(), cb, epilogue);

    lemma_compile_stmt_sim(ast_prog, vm_prog, f.body, st_callee, fuel);
    let ks = spec_stmt_vm_steps(
        ast_prog,
        f.body,
        st_callee.cur.locals,
        st_callee.globals,
        st_callee.heap,
        fuel,
    );
    match spec_eval_stmt(
        ast_prog,
        f.body,
        st_callee.cur.locals,
        st_callee.globals,
        st_callee.heap,
        fuel,
    ) {
        SpecStmtOutcome::Normal { locals: lf, globals: gf, heap: hf } => {
            lemma_call_epilogue_normal(vm_prog, st_callee, func_idx, cb, lf, gf, hf, ks);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_array_set(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    arr_e: Expr,
    idx_e: Expr,
    val_e: Expr,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_stmt_has_call(Stmt::ArraySet(arr_e, idx_e, val_e))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_stmt(Stmt::ArraySet(arr_e, idx_e, val_e)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_stmt(Stmt::ArraySet(arr_e, idx_e, val_e))),
        !(spec_eval_stmt(ast_prog, Stmt::ArraySet(arr_e, idx_e, val_e), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecStmtOutcome::OutOfFuel),
    ensures
        spec_stmt_sim_post(ast_prog, vm_prog, Stmt::ArraySet(arr_e, idx_e, val_e), st0, fuel),
    decreases fuel, 0nat, spec_stmt_size(Stmt::ArraySet(arr_e, idx_e, val_e)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let c1 = spec_compile_expr(arr_e);
    let c2 = spec_compile_expr(idx_e);
    let c3 = spec_compile_expr(val_e);
    lemma_code_at_split4(code, st0.cur.pc, c1, c2, c3, seq![Instr::ArraySet]);
    lemma_compile_expr_sim(ast_prog, vm_prog, arr_e, st0, fuel);
    let k1 = spec_expr_vm_steps(ast_prog, arr_e, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, arr_e, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: arr, globals: g1, heap: h1 } => {
            let st1 = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + c1.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(arr),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            let k2 = spec_expr_vm_steps(ast_prog, idx_e, st0.cur.locals, g1, h1, fuel);
            lemma_compile_expr_sim(ast_prog, vm_prog, idx_e, st1, fuel);
            lemma_vm_run_steps_add(vm_prog, st0, k1, k2);
            match spec_eval_expr(ast_prog, idx_e, st0.cur.locals, g1, h1, fuel) {
                SpecExprOutcome::Ok { val: idx, globals: g2, heap: h2 } => {
                    let st2 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + c1.len() + c2.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(arr).push(idx),
                        },
                        callers: st0.callers,
                        globals: g2,
                        heap: h2,
                    };
                    let k3 = spec_expr_vm_steps(ast_prog, val_e, st0.cur.locals, g2, h2, fuel);
                    lemma_compile_expr_sim(ast_prog, vm_prog, val_e, st2, fuel);
                    lemma_vm_run_steps_add(vm_prog, st0, k1 + k2, k3);
                    match spec_eval_expr(ast_prog, val_e, st0.cur.locals, g2, h2, fuel) {
                        SpecExprOutcome::Ok { val, globals: g3, heap: h3 } => {
                            let st3 = SpecVmState {
                                cur: SpecFrame {
                                    func_idx: st0.cur.func_idx,
                                    pc: st0.cur.pc + c1.len() + c2.len() + c3.len(),
                                    locals: st0.cur.locals,
                                    stack: stk.push(arr).push(idx).push(val),
                                },
                                callers: st0.callers,
                                globals: g3,
                                heap: h3,
                            };
                            lemma_step_array_set(vm_prog, st3, stk, arr, idx, val);
                            lemma_vm_run_steps_add(vm_prog, st0, k1 + k2 + k3, 1);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_if(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    cond: Expr,
    then_s: Box<Stmt>,
    else_s: Box<Stmt>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_stmt_has_call(Stmt::If(cond, then_s, else_s))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_stmt(Stmt::If(cond, then_s, else_s)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_stmt(Stmt::If(cond, then_s, else_s))),
        !(spec_eval_stmt(ast_prog, Stmt::If(cond, then_s, else_s), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecStmtOutcome::OutOfFuel),
    ensures
        spec_stmt_sim_post(ast_prog, vm_prog, Stmt::If(cond, then_s, else_s), st0, fuel),
    decreases fuel, 0nat, spec_stmt_size(Stmt::If(cond, then_s, else_s)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let s = Stmt::If(cond, then_s, else_s);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let cc = spec_compile_expr(cond);
    let ct = spec_compile_stmt(*then_s);
    let ce = spec_compile_stmt(*else_s);
    let jfalse = Instr::JumpIfFalse((ct.len() + 1) as usize);
    let jend = Instr::Jump(ce.len() as usize);
    assert(spec_compile_stmt(s) =~= cc + seq![jfalse] + ct + (seq![jend] + ce));
    lemma_code_at_split4(code, st0.cur.pc, cc, seq![jfalse], ct, seq![jend] + ce);
    lemma_code_at_split(code, st0.cur.pc + cc.len() + 1 + ct.len(), seq![jend], ce);
    lemma_compile_expr_sim(ast_prog, vm_prog, cond, st0, fuel);
    let kc = spec_expr_vm_steps(ast_prog, cond, st0.cur.locals, st0.globals, st0.heap, fuel);
    match spec_eval_expr(ast_prog, cond, st0.cur.locals, st0.globals, st0.heap, fuel) {
        SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
            let st_jf = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + cc.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(vc),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            lemma_step_jump_if_false(vm_prog, st_jf, stk, vc, (ct.len() + 1) as usize);
            lemma_vm_run_steps_add(vm_prog, st0, kc, 1);
            if vc != 0 {
                let st_then = SpecVmState {
                    cur: SpecFrame { pc: st0.cur.pc + cc.len() + 1, stack: stk, ..st_jf.cur },
                    ..st_jf
                };
                let kt = spec_stmt_vm_steps(ast_prog, *then_s, st0.cur.locals, g1, h1, fuel);
                lemma_compile_stmt_sim(ast_prog, vm_prog, *then_s, st_then, fuel);
                lemma_vm_run_steps_add(vm_prog, st0, kc + 1, kt);
                match spec_eval_stmt(ast_prog, *then_s, st0.cur.locals, g1, h1, fuel) {
                    SpecStmtOutcome::Normal { locals: lt, globals: gt, heap: ht } => {
                        let st_jend = SpecVmState {
                            cur: SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st0.cur.pc + cc.len() + 1 + ct.len(),
                                locals: lt,
                                stack: stk,
                            },
                            callers: st0.callers,
                            globals: gt,
                            heap: ht,
                        };
                        lemma_step_jump(vm_prog, st_jend, ce.len() as usize);
                        lemma_vm_run_steps_add(vm_prog, st0, kc + 1 + kt, 1);
                    },
                    _ => {},
                }
            } else {
                let st_else = SpecVmState {
                    cur: SpecFrame {
                        pc: st0.cur.pc + cc.len() + 1 + ct.len() + 1,
                        stack: stk,
                        ..st_jf.cur
                    },
                    ..st_jf
                };
                let ke = spec_stmt_vm_steps(ast_prog, *else_s, st0.cur.locals, g1, h1, fuel);
                lemma_compile_stmt_sim(ast_prog, vm_prog, *else_s, st_else, fuel);
                lemma_vm_run_steps_add(vm_prog, st0, kc + 1, ke);
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_sim_while(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    cond: Expr,
    body: Box<Stmt>,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_stmt_has_call(Stmt::While(cond, body))),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_stmt(Stmt::While(cond, body)).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_stmt(Stmt::While(cond, body))),
        !(spec_eval_stmt(ast_prog, Stmt::While(cond, body), st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecStmtOutcome::OutOfFuel),
    ensures
        spec_stmt_sim_post(ast_prog, vm_prog, Stmt::While(cond, body), st0, fuel),
    decreases fuel, 0nat, spec_stmt_size(Stmt::While(cond, body)), 0nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let s = Stmt::While(cond, body);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    let f1 = (fuel - 1) as nat;
    let cc = spec_compile_expr(cond);
    let cb = spec_compile_stmt(*body);
    let jfalse = Instr::JumpIfFalse((cb.len() + 1) as usize);
    let jback = Instr::JumpBack((cc.len() + 1 + cb.len()) as usize);
    lemma_code_at_split4(code, st0.cur.pc, cc, seq![jfalse], cb, seq![jback]);
    lemma_compile_expr_sim(ast_prog, vm_prog, cond, st0, f1);
    let kc = spec_expr_vm_steps(ast_prog, cond, st0.cur.locals, st0.globals, st0.heap, f1);
    match spec_eval_expr(ast_prog, cond, st0.cur.locals, st0.globals, st0.heap, f1) {
        SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
            let st_jf = SpecVmState {
                cur: SpecFrame {
                    func_idx: st0.cur.func_idx,
                    pc: st0.cur.pc + cc.len(),
                    locals: st0.cur.locals,
                    stack: stk.push(vc),
                },
                callers: st0.callers,
                globals: g1,
                heap: h1,
            };
            lemma_step_jump_if_false(vm_prog, st_jf, stk, vc, (cb.len() + 1) as usize);
            lemma_vm_run_steps_add(vm_prog, st0, kc, 1);
            if vc == 0 {
            } else {
                let st_body = SpecVmState {
                    cur: SpecFrame { pc: st0.cur.pc + cc.len() + 1, stack: stk, ..st_jf.cur },
                    ..st_jf
                };
                let kb = spec_stmt_vm_steps(ast_prog, *body, st0.cur.locals, g1, h1, f1);
                lemma_compile_stmt_sim(ast_prog, vm_prog, *body, st_body, f1);
                lemma_vm_run_steps_add(vm_prog, st0, kc + 1, kb);
                match spec_eval_stmt(ast_prog, *body, st0.cur.locals, g1, h1, f1) {
                    SpecStmtOutcome::Normal { locals: l2, globals: g2, heap: h2 } => {
                        let st_jb = SpecVmState {
                            cur: SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st0.cur.pc + cc.len() + 1 + cb.len(),
                                locals: l2,
                                stack: stk,
                            },
                            callers: st0.callers,
                            globals: g2,
                            heap: h2,
                        };
                        lemma_step_jump_back(vm_prog, st_jb, (cc.len() + 1 + cb.len()) as usize);
                        lemma_vm_run_steps_add(vm_prog, st0, kc + 1 + kb, 1);
                        let st_loop = SpecVmState {
                            cur: SpecFrame {
                                func_idx: st0.cur.func_idx,
                                pc: st0.cur.pc,
                                locals: l2,
                                stack: stk,
                            },
                            callers: st0.callers,
                            globals: g2,
                            heap: h2,
                        };
                        let kw = spec_stmt_vm_steps(ast_prog, s, l2, g2, h2, f1);
                        lemma_compile_stmt_sim(ast_prog, vm_prog, s, st_loop, f1);
                        lemma_vm_run_steps_add(vm_prog, st0, kc + 1 + kb + 1, kw);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_compile_stmt_sim(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    s: Stmt,
    st0: SpecVmState,
    fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_stmt_has_call(s)),
        (st0.cur.func_idx as nat) < vm_prog.funcs.len(),
        spec_compile_stmt(s).len() <= MAX_CODE_LEN as nat,
        spec_code_at(vm_prog.funcs[st0.cur.func_idx as int].code, st0.cur.pc, spec_compile_stmt(s)),
        !(spec_eval_stmt(ast_prog, s, st0.cur.locals, st0.globals, st0.heap, fuel)
            matches SpecStmtOutcome::OutOfFuel),
    ensures
        spec_stmt_sim_post(ast_prog, vm_prog, s, st0, fuel),
    decreases fuel, 0nat, spec_stmt_size(s), 1nat,
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let code = vm_prog.funcs[st0.cur.func_idx as int].code;
    let stk = st0.cur.stack;
    match s {
        Stmt::Nop => lemma_vm_run_steps_zero(vm_prog, st0),
        Stmt::SetLocal(slot, expr) => {
            let ce = spec_compile_expr(expr);
            lemma_code_at_split(code, st0.cur.pc, ce, seq![Instr::StoreLocal(slot)]);
            lemma_compile_expr_sim(ast_prog, vm_prog, expr, st0, fuel);
            let ke = spec_expr_vm_steps(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ce.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(val),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_store_local(vm_prog, st1, stk, val, slot);
                    lemma_vm_run_steps_add(vm_prog, st0, ke, 1);
                },
                _ => {},
            }
        },
        Stmt::SetGlobal(slot, expr) => {
            let ce = spec_compile_expr(expr);
            lemma_code_at_split(code, st0.cur.pc, ce, seq![Instr::StoreGlobal(slot)]);
            lemma_compile_expr_sim(ast_prog, vm_prog, expr, st0, fuel);
            let ke = spec_expr_vm_steps(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ce.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(val),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_store_global(vm_prog, st1, stk, val, slot);
                    lemma_vm_run_steps_add(vm_prog, st0, ke, 1);
                },
                _ => {},
            }
        },
        Stmt::ArraySet(arr_e, idx_e, val_e) =>
            lemma_sim_array_set(ast_prog, vm_prog, arr_e, idx_e, val_e, st0, fuel),
        Stmt::ExprStmt(expr) => {
            let ce = spec_compile_expr(expr);
            lemma_code_at_split(code, st0.cur.pc, ce, seq![Instr::Pop]);
            lemma_compile_expr_sim(ast_prog, vm_prog, expr, st0, fuel);
            let ke = spec_expr_vm_steps(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ce.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(val),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_pop(vm_prog, st1, stk, val);
                    lemma_vm_run_steps_add(vm_prog, st0, ke, 1);
                },
                _ => {},
            }
        },
        Stmt::If(cond, then_s, else_s) =>
            lemma_sim_if(ast_prog, vm_prog, cond, then_s, else_s, st0, fuel),
        Stmt::While(cond, body) =>
            lemma_sim_while(ast_prog, vm_prog, cond, body, st0, fuel),
        Stmt::Seq(s1, s2) => {
            let c1 = spec_compile_stmt(*s1);
            let c2 = spec_compile_stmt(*s2);
            lemma_code_at_split(code, st0.cur.pc, c1, c2);
            lemma_compile_stmt_sim(ast_prog, vm_prog, *s1, st0, fuel);
            let k1 = spec_stmt_vm_steps(ast_prog, *s1, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_stmt(ast_prog, *s1, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecStmtOutcome::Normal { locals: l1, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + c1.len(),
                            locals: l1,
                            stack: stk,
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    let k2 = spec_stmt_vm_steps(ast_prog, *s2, l1, g1, h1, fuel);
                    lemma_compile_stmt_sim(ast_prog, vm_prog, *s2, st1, fuel);
                    lemma_vm_run_steps_add(vm_prog, st0, k1, k2);
                },
                _ => {},
            }
        },
        Stmt::Return(expr) => {
            let ce = spec_compile_expr(expr);
            lemma_code_at_split(code, st0.cur.pc, ce, seq![Instr::Ret]);
            lemma_compile_expr_sim(ast_prog, vm_prog, expr, st0, fuel);
            let ke = spec_expr_vm_steps(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel);
            match spec_eval_expr(ast_prog, expr, st0.cur.locals, st0.globals, st0.heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    let st1 = SpecVmState {
                        cur: SpecFrame {
                            func_idx: st0.cur.func_idx,
                            pc: st0.cur.pc + ce.len(),
                            locals: st0.cur.locals,
                            stack: stk.push(val),
                        },
                        callers: st0.callers,
                        globals: g1,
                        heap: h1,
                    };
                    lemma_step_ret(vm_prog, st1, stk, val);
                    lemma_vm_run_steps_add(vm_prog, st0, ke, 1);
                },
                _ => {},
            }
        },
    }
}

// ---------------------------------------------------------------------------
// 7. Public Top-Level Theorems: Code-Composition & Full Program Preservation
// ---------------------------------------------------------------------------

/// Explicit CompCert/CakeML-style expression code-composition & stack-preservation theorem:
/// For ANY surrounding bytecode `prefix` and `suffix`, ANY bottom stack `stk`, and ANY caller
/// frames `callers`, executing `spec_compile_expr(e)` starting at `pc = prefix.len()` advances
/// `pc` to `prefix.len() + spec_compile_expr(e).len()` and pushes `val` onto `stk`.
pub proof fn theorem_compile_expr_prefix_suffix(
    ast_prog: SpecProgram,
    vm_prog: SpecCompiledProgram,
    func_idx: usize,
    prefix: Seq<Instr>,
    e: Expr,
    suffix: Seq<Instr>,
    stk: Seq<i64>,
    callers: Seq<SpecFrame>,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    ast_fuel: nat,
)
    requires
        spec_env_compiled(ast_prog, vm_prog, spec_expr_has_call(e)),
        (func_idx as nat) < vm_prog.funcs.len(),
        vm_prog.funcs[func_idx as int].code == prefix + spec_compile_expr(e) + suffix,
        spec_compile_expr(e).len() <= MAX_CODE_LEN as nat,
        !(spec_eval_expr(ast_prog, e, locals, globals, heap, ast_fuel)
            matches SpecExprOutcome::OutOfFuel),
    ensures
        ({
            let st0 = SpecVmState {
                cur: SpecFrame { func_idx, pc: prefix.len(), locals, stack: stk },
                callers,
                globals,
                heap,
            };
            let steps = spec_expr_vm_steps(ast_prog, e, locals, globals, heap, ast_fuel);
            match spec_eval_expr(ast_prog, e, locals, globals, heap, ast_fuel) {
                SpecExprOutcome::Ok { val, globals: gf, heap: hf } =>
                    spec_vm_run_steps(vm_prog, st0, steps) == SpecVmRunOutcome::Running(SpecVmState {
                        cur: SpecFrame {
                            func_idx,
                            pc: prefix.len() + spec_compile_expr(e).len(),
                            locals,
                            stack: stk.push(val),
                        },
                        callers,
                        globals: gf,
                        heap: hf,
                    }),
                SpecExprOutcome::Trap(err) =>
                    spec_vm_run_steps(vm_prog, st0, steps) == SpecVmRunOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => true,
            }
        }),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    lemma_prefix_suffix_embeds(prefix, spec_compile_expr(e), suffix);
    let st0 = SpecVmState {
        cur: SpecFrame { func_idx, pc: prefix.len(), locals, stack: stk },
        callers,
        globals,
        heap,
    };
    lemma_compile_expr_sim(ast_prog, vm_prog, e, st0, ast_fuel);
}

/// Top-level compiler semantic preservation theorem:
/// Whenever `spec_eval_program(prog, init_locals, ast_fuel)` terminates (`Done` or `Trap`),
/// `spec_run_vm(spec_compile_program(prog), init_locals, vm_fuel)` produces the EXACT SAME
/// outcome (`val`, `globals`, `heap`, or `Trap(err)`) for all `vm_fuel >= spec_program_vm_fuel(...)`.
pub proof fn theorem_compile_program_correct(
    prog: SpecProgram,
    init_locals: Seq<i64>,
    ast_fuel: nat,
    vm_fuel: nat,
)
    requires
        spec_program_code_bounded(prog),
        !(spec_eval_program(prog, init_locals, ast_fuel) matches SpecProgramOutcome::OutOfFuel),
        vm_fuel >= spec_program_vm_fuel(prog, init_locals, ast_fuel),
    ensures
        spec_run_vm(spec_compile_program(prog), init_locals, vm_fuel)
            == spec_eval_program(prog, init_locals, ast_fuel),
{
    hide(spec_vm_step);
    hide(spec_vm_run_steps);
    let vm_prog = spec_compile_program(prog);
    if (prog.entry as nat) >= prog.funcs.len() || prog.num_globals > MAX_GLOBALS {
    } else {
        let entry_fn = prog.funcs[prog.entry as int];
        assert(vm_prog.funcs[prog.entry as int] == spec_compile_func(entry_fn));
        match spec_pad_locals(init_locals, entry_fn.num_locals) {
            None => {},
            Some(locals0) => {
                let globals0 = spec_zeros(prog.num_globals as nat);
                let heap0 = Seq::<Seq<i64>>::empty();
                let init_state = SpecVmState {
                    cur: SpecFrame {
                        func_idx: prog.entry,
                        pc: 0,
                        locals: locals0,
                        stack: Seq::empty(),
                    },
                    callers: Seq::empty(),
                    globals: globals0,
                    heap: heap0,
                };
                let needed = spec_call_vm_steps(
                    prog,
                    prog.entry,
                    locals0,
                    globals0,
                    heap0,
                    ast_fuel,
                );
                lemma_compile_call_sim(prog, vm_prog, prog.entry, init_state, ast_fuel);
                lemma_vm_run_steps_terminal(vm_prog, init_state, needed, vm_fuel);
            },
        }
    }
}

/// End-to-end executable compiler + VM equivalence:
/// Compiling `prog` with `compile_program` and executing on `run_vm` produces the exact same
/// `SpecProgramOutcome` (return value, globals, and heap arrays) as `eval_program` on the AST.
pub fn compile_and_run_verified(
    prog: &Program,
    init_locals: &[i64],
    ast_fuel: usize,
    vm_fuel: usize,
) -> (r: Result<(ExecProgramOutcome, ExecProgramOutcome), CompileError>)
    ensures
        match r {
            Ok((ast_out, vm_out)) =>
                ast_out@ == spec_eval_program(prog@, init_locals@, ast_fuel as nat)
                    && vm_out@ == spec_run_vm(spec_compile_program(prog@), init_locals@, vm_fuel as nat)
                    && (!(ast_out@ matches SpecProgramOutcome::OutOfFuel)
                        && (vm_fuel as nat) >= spec_program_vm_fuel(prog@, init_locals@, ast_fuel as nat)
                        ==> vm_out@ == ast_out@),
            Err(_) => !spec_program_code_bounded(prog@),
        },
{
    let compiled = compile_program(prog)?;
    let ast_out = eval_program(prog, init_locals, ast_fuel);
    let vm_out = run_vm(&compiled, init_locals, vm_fuel);
    proof {
        if !(ast_out@ matches SpecProgramOutcome::OutOfFuel)
            && (vm_fuel as nat) >= spec_program_vm_fuel(prog@, init_locals@, ast_fuel as nat)
        {
            theorem_compile_program_correct(prog@, init_locals@, ast_fuel as nat, vm_fuel as nat);
        }
    }
    Ok((ast_out, vm_out))
}

} // verus!
