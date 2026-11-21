//! Verified AST syntax and big-step/fuel-bounded reference semantics for `vjs_vm`.
//!
//! Covers integer/boolean constants, local & global slots, arithmetic/bitwise/comparison/logical
//! operators (including short-circuit `LogAnd` / `LogOr`), conditionals (`If`/`Else`), bounded
//! `While` loops, sequencing (`Seq`), early `Return`, multi-argument recursive function `Call`s,
//! and bounds-checked heap-allocated mutable arrays (`ArrayNew`, `ArrayGet`, `ArraySet`).

use vstd::prelude::*;

verus! {

pub const MAX_ARRAY_LEN: i64 = 1_048_576;
pub const MAX_HEAP_ARRAYS: usize = 65_536;
pub const MAX_LOCALS: usize = 4_096;
pub const MAX_GLOBALS: usize = 65_536;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VmError {
    DivisionByZero,
    InvalidLocal,
    InvalidGlobal,
    InvalidCall,
    InvalidArrayLength,
    HeapLimitExceeded,
    InvalidArrayHandle,
    ArrayOutOfBounds,
    StackUnderflow,
    InvalidJump,
    InvalidEntry,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Lt,
    Le,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Expr {
    Const(i64),
    Local(usize),
    Global(usize),
    Not(Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    LogAnd(Box<Expr>, Box<Expr>),
    LogOr(Box<Expr>, Box<Expr>),
    Call(usize, Box<ExprList>),
    ArrayNew(Box<Expr>),
    ArrayGet(Box<Expr>, Box<Expr>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum ExprList {
    Nil,
    Cons(Box<Expr>, Box<ExprList>),
}

#[derive(PartialEq, Eq, Debug)]
pub enum Stmt {
    Nop,
    SetLocal(usize, Expr),
    SetGlobal(usize, Expr),
    ArraySet(Expr, Expr, Expr),
    ExprStmt(Expr),
    If(Expr, Box<Stmt>, Box<Stmt>),
    While(Expr, Box<Stmt>),
    Seq(Box<Stmt>, Box<Stmt>),
    Return(Expr),
}

#[derive(PartialEq, Eq, Debug)]
pub struct Func {
    pub num_params: usize,
    pub num_locals: usize,
    pub body: Stmt,
}

#[derive(PartialEq, Eq, Debug)]
pub struct Program {
    pub funcs: Vec<Func>,
    pub entry: usize,
    pub num_globals: usize,
}

pub struct SpecProgram {
    pub funcs: Seq<Func>,
    pub entry: usize,
    pub num_globals: usize,
}

impl View for Program {
    type V = SpecProgram;

    open spec fn view(&self) -> SpecProgram {
        SpecProgram {
            funcs: self.funcs@,
            entry: self.entry,
            num_globals: self.num_globals,
        }
    }
}

pub type SpecHeap = Seq<Seq<i64>>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExecHeap {
    pub arrays: Vec<Vec<i64>>,
}

impl View for ExecHeap {
    type V = SpecHeap;

    open spec fn view(&self) -> SpecHeap {
        Seq::new(self.arrays@.len(), |i: int| self.arrays@[i]@)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExecProgramOutcome {
    Done { val: i64, globals: Vec<i64>, heap: ExecHeap },
    Trap(VmError),
    OutOfFuel,
}

pub enum SpecProgramOutcome {
    Done { val: i64, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
    OutOfFuel,
}

impl View for ExecProgramOutcome {
    type V = SpecProgramOutcome;

    open spec fn view(&self) -> SpecProgramOutcome {
        match self {
            ExecProgramOutcome::Done { val, globals, heap } =>
                SpecProgramOutcome::Done { val: *val, globals: globals@, heap: heap@ },
            ExecProgramOutcome::Trap(e) => SpecProgramOutcome::Trap(*e),
            ExecProgramOutcome::OutOfFuel => SpecProgramOutcome::OutOfFuel,
        }
    }
}

pub enum SpecExprOutcome {
    Ok { val: i64, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
    OutOfFuel,
}

pub enum SpecArgsOutcome {
    Ok { vals: Seq<i64>, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
    OutOfFuel,
}

pub enum SpecStmtOutcome {
    Normal { locals: Seq<i64>, globals: Seq<i64>, heap: SpecHeap },
    Return { val: i64, locals: Seq<i64>, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
    OutOfFuel,
}

enum ExecExprOutcome {
    Ok(i64),
    Trap(VmError),
    OutOfFuel,
}

enum ExecArgsOutcome {
    Ok(Vec<i64>),
    Trap(VmError),
    OutOfFuel,
}

enum ExecStmtOutcome {
    Normal,
    Return(i64),
    Trap(VmError),
    OutOfFuel,
}

// ---------------------------------------------------------------------------
// Primitive operator & heap specifications
// ---------------------------------------------------------------------------

pub open spec fn spec_not(a: i64) -> i64 {
    if a == 0 { 1 } else { 0 }
}

pub fn eval_not(a: i64) -> (r: i64)
    ensures
        r == spec_not(a),
{
    if a == 0 { 1 } else { 0 }
}

pub open spec fn spec_binop(op: BinOp, a: i64, b: i64) -> Result<i64, VmError> {
    match op {
        BinOp::Add => Ok(a.wrapping_add(b)),
        BinOp::Sub => Ok(a.wrapping_sub(b)),
        BinOp::Mul => Ok(a.wrapping_mul(b)),
        BinOp::Div => {
            if b == 0 {
                Err(VmError::DivisionByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(i64::MIN)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(VmError::DivisionByZero),
                }
            }
        },
        BinOp::Mod => {
            if b == 0 {
                Err(VmError::DivisionByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(r) => Ok(r),
                    None => Err(VmError::DivisionByZero),
                }
            }
        },
        BinOp::BitAnd => Ok(((a as u64) & (b as u64)) as i64),
        BinOp::BitOr => Ok(((a as u64) | (b as u64)) as i64),
        BinOp::BitXor => Ok(((a as u64) ^ (b as u64)) as i64),
        BinOp::Eq => Ok(if a == b { 1 } else { 0 }),
        BinOp::Lt => Ok(if a < b { 1 } else { 0 }),
        BinOp::Le => Ok(if a <= b { 1 } else { 0 }),
    }
}

pub fn eval_binop(op: BinOp, a: i64, b: i64) -> (r: Result<i64, VmError>)
    ensures
        r == spec_binop(op, a, b),
{
    match op {
        BinOp::Add => Ok(a.wrapping_add(b)),
        BinOp::Sub => Ok(a.wrapping_sub(b)),
        BinOp::Mul => Ok(a.wrapping_mul(b)),
        BinOp::Div => {
            if b == 0 {
                Err(VmError::DivisionByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(i64::MIN)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(VmError::DivisionByZero),
                }
            }
        },
        BinOp::Mod => {
            if b == 0 {
                Err(VmError::DivisionByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(rem) => Ok(rem),
                    None => Err(VmError::DivisionByZero),
                }
            }
        },
        BinOp::BitAnd => Ok(((a as u64) & (b as u64)) as i64),
        BinOp::BitOr => Ok(((a as u64) | (b as u64)) as i64),
        BinOp::BitXor => Ok(((a as u64) ^ (b as u64)) as i64),
        BinOp::Eq => Ok(if a == b { 1 } else { 0 }),
        BinOp::Lt => Ok(if a < b { 1 } else { 0 }),
        BinOp::Le => Ok(if a <= b { 1 } else { 0 }),
    }
}

pub open spec fn spec_zeros(n: nat) -> Seq<i64> {
    Seq::new(n, |_i: int| 0i64)
}

pub fn alloc_zeros(n: usize) -> (v: Vec<i64>)
    ensures
        v@ == spec_zeros(n as nat),
{
    let mut v: Vec<i64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> v@[k] == 0i64,
        decreases n - i,
    {
        v.push(0);
        i = i + 1;
    }
    proof {
        assert(v@ =~= spec_zeros(n as nat));
    }
    v
}

pub open spec fn spec_pad_locals(passed: Seq<i64>, num_locals: usize) -> Option<Seq<i64>> {
    if passed.len() > num_locals as nat || num_locals > MAX_LOCALS {
        None
    } else {
        Some(passed + spec_zeros((num_locals as nat - passed.len()) as nat))
    }
}

pub fn pad_locals_from_slice(passed: &[i64], num_locals: usize) -> (r: Option<Vec<i64>>)
    ensures
        match (r, spec_pad_locals(passed@, num_locals)) {
            (Some(v), Some(sv)) => v@ == sv,
            (None, None) => true,
            _ => false,
        },
{
    if passed.len() > num_locals || num_locals > MAX_LOCALS {
        return None;
    }
    let mut out: Vec<i64> = Vec::with_capacity(num_locals);
    let p_len = passed.len();
    let mut i: usize = 0;
    while i < p_len
        invariant
            i <= p_len,
            p_len == passed@.len(),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> out@[k] == passed@[k],
        decreases p_len - i,
    {
        out.push(passed[i]);
        i = i + 1;
    }
    let rem = num_locals - p_len;
    let mut zeros = alloc_zeros(rem);
    proof {
        assert(out@ =~= passed@);
    }
    out.append(&mut zeros);
    Some(out)
}

pub fn pad_locals_owned(mut passed: Vec<i64>, num_locals: usize) -> (r: Option<Vec<i64>>)
    ensures
        match (r, spec_pad_locals(passed@, num_locals)) {
            (Some(v), Some(sv)) => v@ == sv,
            (None, None) => true,
            _ => false,
        },
{
    if passed.len() > num_locals || num_locals > MAX_LOCALS {
        return None;
    }
    let rem = num_locals - passed.len();
    let mut zeros = alloc_zeros(rem);
    passed.append(&mut zeros);
    Some(passed)
}

pub open spec fn spec_heap_alloc(heap: SpecHeap, len: i64) -> Result<(i64, SpecHeap), VmError> {
    if len < 0 || len > MAX_ARRAY_LEN {
        Err(VmError::InvalidArrayLength)
    } else if heap.len() >= MAX_HEAP_ARRAYS as nat {
        Err(VmError::HeapLimitExceeded)
    } else {
        let id = heap.len() as i64;
        Ok((id, heap.push(spec_zeros(len as nat))))
    }
}

pub open spec fn spec_heap_get(heap: SpecHeap, arr: i64, idx: i64) -> Result<i64, VmError> {
    if arr < 0 || (arr as nat) >= heap.len() {
        Err(VmError::InvalidArrayHandle)
    } else if idx < 0 || (idx as nat) >= heap[arr as int].len() {
        Err(VmError::ArrayOutOfBounds)
    } else {
        Ok(heap[arr as int][idx as int])
    }
}

pub open spec fn spec_heap_set(
    heap: SpecHeap,
    arr: i64,
    idx: i64,
    val: i64,
) -> Result<SpecHeap, VmError> {
    if arr < 0 || (arr as nat) >= heap.len() {
        Err(VmError::InvalidArrayHandle)
    } else if idx < 0 || (idx as nat) >= heap[arr as int].len() {
        Err(VmError::ArrayOutOfBounds)
    } else {
        Ok(heap.update(arr as int, heap[arr as int].update(idx as int, val)))
    }
}

impl ExecHeap {
    pub fn new() -> (h: Self)
        ensures
            h@ == Seq::<Seq<i64>>::empty(),
    {
        let h = ExecHeap { arrays: Vec::new() };
        proof {
            assert(h@ =~= Seq::<Seq<i64>>::empty());
        }
        h
    }

    pub fn alloc_array(&mut self, len: i64) -> (r: Result<i64, VmError>)
        ensures
            match (r, spec_heap_alloc(old(self)@, len)) {
                (Ok(id), Ok((sid, sh))) => id == sid && final(self)@ == sh,
                (Err(e), Err(se)) => e == se && final(self)@ == old(self)@,
                _ => false,
            },
    {
        if len < 0 || len > MAX_ARRAY_LEN {
            return Err(VmError::InvalidArrayLength);
        }
        if self.arrays.len() >= MAX_HEAP_ARRAYS {
            return Err(VmError::HeapLimitExceeded);
        }
        let id = self.arrays.len() as i64;
        let arr = alloc_zeros(len as usize);
        let ghost old_h = self@;
        self.arrays.push(arr);
        proof {
            assert(self@ =~= old_h.push(spec_zeros(len as nat)));
        }
        Ok(id)
    }

    pub fn array_get(&self, arr: i64, idx: i64) -> (r: Result<i64, VmError>)
        ensures
            r == spec_heap_get(self@, arr, idx),
    {
        if arr < 0 || (arr as u64) >= (self.arrays.len() as u64) {
            return Err(VmError::InvalidArrayHandle);
        }
        let a_idx = arr as usize;
        let slice = &self.arrays[a_idx];
        if idx < 0 || (idx as u64) >= (slice.len() as u64) {
            return Err(VmError::ArrayOutOfBounds);
        }
        Ok(slice[idx as usize])
    }

    pub fn array_set(&mut self, arr: i64, idx: i64, val: i64) -> (r: Result<(), VmError>)
        ensures
            match (r, spec_heap_set(old(self)@, arr, idx, val)) {
                (Ok(()), Ok(sh)) => final(self)@ == sh,
                (Err(e), Err(se)) => e == se && final(self)@ == old(self)@,
                _ => false,
            },
    {
        if arr < 0 || (arr as u64) >= (self.arrays.len() as u64) {
            return Err(VmError::InvalidArrayHandle);
        }
        let a_idx = arr as usize;
        if idx < 0 || (idx as u64) >= (self.arrays[a_idx].len() as u64) {
            return Err(VmError::ArrayOutOfBounds);
        }
        let i_idx = idx as usize;
        let ghost old_h = self@;
        self.arrays[a_idx][i_idx] = val;
        proof {
            assert(self@ =~= old_h.update(a_idx as int, old_h[a_idx as int].update(i_idx as int, val)));
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Structural AST size measures for mutual lexicographic termination
// ---------------------------------------------------------------------------

pub open spec fn spec_expr_size(e: Expr) -> nat
    decreases e,
{
    match e {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) => 1,
        Expr::Not(inner) => 1 + spec_expr_size(*inner),
        Expr::BinOp(_, l, r) | Expr::LogAnd(l, r) | Expr::LogOr(l, r) | Expr::ArrayGet(l, r) =>
            1 + spec_expr_size(*l) + spec_expr_size(*r),
        Expr::Call(_, args) => 1 + spec_expr_list_size(*args),
        Expr::ArrayNew(len_e) => 1 + spec_expr_size(*len_e),
    }
}

pub open spec fn spec_expr_list_size(args: ExprList) -> nat
    decreases args,
{
    match args {
        ExprList::Nil => 1,
        ExprList::Cons(h, t) => 1 + spec_expr_size(*h) + spec_expr_list_size(*t),
    }
}

pub open spec fn spec_expr_list_len(args: ExprList) -> nat
    decreases args,
{
    match args {
        ExprList::Nil => 0,
        ExprList::Cons(_, t) => 1 + spec_expr_list_len(*t),
    }
}

pub open spec fn spec_stmt_size(s: Stmt) -> nat
    decreases s,
{
    match s {
        Stmt::Nop => 1,
        Stmt::SetLocal(_, e) | Stmt::SetGlobal(_, e) | Stmt::ExprStmt(e) | Stmt::Return(e) =>
            1 + spec_expr_size(e),
        Stmt::ArraySet(a, i, v) =>
            1 + spec_expr_size(a) + spec_expr_size(i) + spec_expr_size(v),
        Stmt::If(c, t, f) =>
            1 + spec_expr_size(c) + spec_stmt_size(*t) + spec_stmt_size(*f),
        Stmt::While(c, b) =>
            1 + spec_expr_size(c) + spec_stmt_size(*b),
        Stmt::Seq(s1, s2) =>
            1 + spec_stmt_size(*s1) + spec_stmt_size(*s2),
    }
}

// ---------------------------------------------------------------------------
// AST Reference Evaluator Specification
// ---------------------------------------------------------------------------

pub open spec fn spec_eval_expr(
    prog: SpecProgram,
    e: Expr,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> SpecExprOutcome
    decreases fuel, 0nat, spec_expr_size(e),
{
    match e {
        Expr::Const(n) => SpecExprOutcome::Ok { val: n, globals, heap },
        Expr::Local(slot) => {
            if (slot as nat) < locals.len() {
                SpecExprOutcome::Ok { val: locals[slot as int], globals, heap }
            } else {
                SpecExprOutcome::Trap(VmError::InvalidLocal)
            }
        },
        Expr::Global(slot) => {
            if (slot as nat) < globals.len() {
                SpecExprOutcome::Ok { val: globals[slot as int], globals, heap }
            } else {
                SpecExprOutcome::Trap(VmError::InvalidGlobal)
            }
        },
        Expr::Not(inner) => {
            match spec_eval_expr(prog, *inner, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } =>
                    SpecExprOutcome::Ok { val: spec_not(val), globals: g1, heap: h1 },
                other => other,
            }
        },
        Expr::BinOp(op, lhs, rhs) => {
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                        SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } => {
                            match spec_binop(op, v1, v2) {
                                Ok(res) => SpecExprOutcome::Ok { val: res, globals: g2, heap: h2 },
                                Err(err) => SpecExprOutcome::Trap(err),
                            }
                        },
                        other => other,
                    }
                },
                other => other,
            }
        },
        Expr::LogAnd(lhs, rhs) => {
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    if v1 == 0 {
                        SpecExprOutcome::Ok { val: 0, globals: g1, heap: h1 }
                    } else {
                        match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                            SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } =>
                                SpecExprOutcome::Ok {
                                    val: spec_not(spec_not(v2)),
                                    globals: g2,
                                    heap: h2,
                                },
                            other => other,
                        }
                    }
                },
                other => other,
            }
        },
        Expr::LogOr(lhs, rhs) => {
            match spec_eval_expr(prog, *lhs, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: v1, globals: g1, heap: h1 } => {
                    if v1 != 0 {
                        SpecExprOutcome::Ok { val: 1, globals: g1, heap: h1 }
                    } else {
                        match spec_eval_expr(prog, *rhs, locals, g1, h1, fuel) {
                            SpecExprOutcome::Ok { val: v2, globals: g2, heap: h2 } =>
                                SpecExprOutcome::Ok {
                                    val: spec_not(spec_not(v2)),
                                    globals: g2,
                                    heap: h2,
                                },
                            other => other,
                        }
                    }
                },
                other => other,
            }
        },
        Expr::Call(func_idx, args) => {
            match spec_eval_args(prog, *args, locals, globals, heap, fuel) {
                SpecArgsOutcome::Ok { vals, globals: g1, heap: h1 } => {
                    if (func_idx as nat) >= prog.funcs.len() {
                        SpecExprOutcome::Trap(VmError::InvalidCall)
                    } else {
                        let callee = prog.funcs[func_idx as int];
                        if vals.len() != callee.num_params as nat {
                            SpecExprOutcome::Trap(VmError::InvalidCall)
                        } else {
                            match spec_pad_locals(vals, callee.num_locals) {
                                None => SpecExprOutcome::Trap(VmError::InvalidCall),
                                Some(callee_locals) => {
                                    if fuel == 0 {
                                        SpecExprOutcome::OutOfFuel
                                    } else {
                                        spec_eval_call_body(
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
                SpecArgsOutcome::Trap(err) => SpecExprOutcome::Trap(err),
                SpecArgsOutcome::OutOfFuel => SpecExprOutcome::OutOfFuel,
            }
        },
        Expr::ArrayNew(len_e) => {
            match spec_eval_expr(prog, *len_e, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: len, globals: g1, heap: h1 } => {
                    match spec_heap_alloc(h1, len) {
                        Ok((id, h2)) => SpecExprOutcome::Ok { val: id, globals: g1, heap: h2 },
                        Err(err) => SpecExprOutcome::Trap(err),
                    }
                },
                other => other,
            }
        },
        Expr::ArrayGet(arr_e, idx_e) => {
            match spec_eval_expr(prog, *arr_e, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: arr, globals: g1, heap: h1 } => {
                    match spec_eval_expr(prog, *idx_e, locals, g1, h1, fuel) {
                        SpecExprOutcome::Ok { val: idx, globals: g2, heap: h2 } => {
                            match spec_heap_get(h2, arr, idx) {
                                Ok(elem) => SpecExprOutcome::Ok { val: elem, globals: g2, heap: h2 },
                                Err(err) => SpecExprOutcome::Trap(err),
                            }
                        },
                        other => other,
                    }
                },
                other => other,
            }
        },
    }
}

pub open spec fn spec_eval_args(
    prog: SpecProgram,
    args: ExprList,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> SpecArgsOutcome
    decreases fuel, 0nat, spec_expr_list_size(args),
{
    match args {
        ExprList::Nil => SpecArgsOutcome::Ok { vals: Seq::empty(), globals, heap },
        ExprList::Cons(head, tail) => {
            match spec_eval_expr(prog, *head, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: vh, globals: g1, heap: h1 } => {
                    match spec_eval_args(prog, *tail, locals, g1, h1, fuel) {
                        SpecArgsOutcome::Ok { vals: vt, globals: g2, heap: h2 } =>
                            SpecArgsOutcome::Ok { vals: seq![vh] + vt, globals: g2, heap: h2 },
                        other => other,
                    }
                },
                SpecExprOutcome::Trap(err) => SpecArgsOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecArgsOutcome::OutOfFuel,
            }
        },
    }
}

pub open spec fn spec_eval_call_body(
    prog: SpecProgram,
    func_idx: usize,
    callee_locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> SpecExprOutcome
    decreases fuel, 1nat, 0nat,
{
    if (func_idx as nat) >= prog.funcs.len() {
        SpecExprOutcome::Trap(VmError::InvalidCall)
    } else {
        match spec_eval_stmt(prog, prog.funcs[func_idx as int].body, callee_locals, globals, heap, fuel) {
            SpecStmtOutcome::Normal { locals: _, globals: g2, heap: h2 } =>
                SpecExprOutcome::Ok { val: 0, globals: g2, heap: h2 },
            SpecStmtOutcome::Return { val: rv, locals: _, globals: g2, heap: h2 } =>
                SpecExprOutcome::Ok { val: rv, globals: g2, heap: h2 },
            SpecStmtOutcome::Trap(err) => SpecExprOutcome::Trap(err),
            SpecStmtOutcome::OutOfFuel => SpecExprOutcome::OutOfFuel,
        }
    }
}

pub open spec fn spec_eval_stmt(
    prog: SpecProgram,
    s: Stmt,
    locals: Seq<i64>,
    globals: Seq<i64>,
    heap: SpecHeap,
    fuel: nat,
) -> SpecStmtOutcome
    decreases fuel, 0nat, spec_stmt_size(s),
{
    match s {
        Stmt::Nop => SpecStmtOutcome::Normal { locals, globals, heap },
        Stmt::SetLocal(slot, expr) => {
            match spec_eval_expr(prog, expr, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    if (slot as nat) < locals.len() {
                        SpecStmtOutcome::Normal {
                            locals: locals.update(slot as int, val),
                            globals: g1,
                            heap: h1,
                        }
                    } else {
                        SpecStmtOutcome::Trap(VmError::InvalidLocal)
                    }
                },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::SetGlobal(slot, expr) => {
            match spec_eval_expr(prog, expr, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } => {
                    if (slot as nat) < g1.len() {
                        SpecStmtOutcome::Normal {
                            locals,
                            globals: g1.update(slot as int, val),
                            heap: h1,
                        }
                    } else {
                        SpecStmtOutcome::Trap(VmError::InvalidGlobal)
                    }
                },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::ArraySet(arr_e, idx_e, val_e) => {
            match spec_eval_expr(prog, arr_e, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: arr, globals: g1, heap: h1 } => {
                    match spec_eval_expr(prog, idx_e, locals, g1, h1, fuel) {
                        SpecExprOutcome::Ok { val: idx, globals: g2, heap: h2 } => {
                            match spec_eval_expr(prog, val_e, locals, g2, h2, fuel) {
                                SpecExprOutcome::Ok { val, globals: g3, heap: h3 } => {
                                    match spec_heap_set(h3, arr, idx, val) {
                                        Ok(h4) => SpecStmtOutcome::Normal { locals, globals: g3, heap: h4 },
                                        Err(err) => SpecStmtOutcome::Trap(err),
                                    }
                                },
                                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
                            }
                        },
                        SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                        SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
                    }
                },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::ExprStmt(expr) => {
            match spec_eval_expr(prog, expr, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: _, globals: g1, heap: h1 } =>
                    SpecStmtOutcome::Normal { locals, globals: g1, heap: h1 },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::If(cond, then_s, else_s) => {
            match spec_eval_expr(prog, cond, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
                    if vc != 0 {
                        spec_eval_stmt(prog, *then_s, locals, g1, h1, fuel)
                    } else {
                        spec_eval_stmt(prog, *else_s, locals, g1, h1, fuel)
                    }
                },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::While(cond, body) => {
            if fuel == 0 {
                SpecStmtOutcome::OutOfFuel
            } else {
                let f1 = (fuel - 1) as nat;
                match spec_eval_expr(prog, cond, locals, globals, heap, f1) {
                    SpecExprOutcome::Ok { val: vc, globals: g1, heap: h1 } => {
                        if vc == 0 {
                            SpecStmtOutcome::Normal { locals, globals: g1, heap: h1 }
                        } else {
                            match spec_eval_stmt(prog, *body, locals, g1, h1, f1) {
                                SpecStmtOutcome::Normal { locals: l2, globals: g2, heap: h2 } =>
                                    spec_eval_stmt(prog, Stmt::While(cond, body), l2, g2, h2, f1),
                                other => other,
                            }
                        }
                    },
                    SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                    SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
                }
            }
        },
        Stmt::Seq(s1, s2) => {
            match spec_eval_stmt(prog, *s1, locals, globals, heap, fuel) {
                SpecStmtOutcome::Normal { locals: l1, globals: g1, heap: h1 } =>
                    spec_eval_stmt(prog, *s2, l1, g1, h1, fuel),
                other => other,
            }
        },
        Stmt::Return(expr) => {
            match spec_eval_expr(prog, expr, locals, globals, heap, fuel) {
                SpecExprOutcome::Ok { val, globals: g1, heap: h1 } =>
                    SpecStmtOutcome::Return { val, locals, globals: g1, heap: h1 },
                SpecExprOutcome::Trap(err) => SpecStmtOutcome::Trap(err),
                SpecExprOutcome::OutOfFuel => SpecStmtOutcome::OutOfFuel,
            }
        },
    }
}

pub open spec fn spec_eval_program(
    prog: SpecProgram,
    init_locals: Seq<i64>,
    fuel: nat,
) -> SpecProgramOutcome {
    if (prog.entry as nat) >= prog.funcs.len() || prog.num_globals > MAX_GLOBALS {
        SpecProgramOutcome::Trap(VmError::InvalidEntry)
    } else {
        let entry_fn = prog.funcs[prog.entry as int];
        match spec_pad_locals(init_locals, entry_fn.num_locals) {
            None => SpecProgramOutcome::Trap(VmError::InvalidLocal),
            Some(locals0) => {
                let globals0 = spec_zeros(prog.num_globals as nat);
                let heap0 = Seq::<Seq<i64>>::empty();
                match spec_eval_stmt(prog, entry_fn.body, locals0, globals0, heap0, fuel) {
                    SpecStmtOutcome::Normal { locals: _, globals: gf, heap: hf } =>
                        SpecProgramOutcome::Done { val: 0, globals: gf, heap: hf },
                    SpecStmtOutcome::Return { val: rv, locals: _, globals: gf, heap: hf } =>
                        SpecProgramOutcome::Done { val: rv, globals: gf, heap: hf },
                    SpecStmtOutcome::Trap(err) => SpecProgramOutcome::Trap(err),
                    SpecStmtOutcome::OutOfFuel => SpecProgramOutcome::OutOfFuel,
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Verified Executable AST Tree-Walk Evaluator (proved exec == spec)
// ---------------------------------------------------------------------------

fn exec_eval_expr(
    prog: &Program,
    e: &Expr,
    locals: &[i64],
    globals: &mut Vec<i64>,
    heap: &mut ExecHeap,
    fuel: usize,
) -> (r: ExecExprOutcome)
    ensures
        match (r, spec_eval_expr(prog@, *e, locals@, old(globals)@, old(heap)@, fuel as nat)) {
            (ExecExprOutcome::Ok(v), SpecExprOutcome::Ok { val: sv, globals: sg, heap: sh }) =>
                v == sv && final(globals)@ == sg && final(heap)@ == sh,
            (ExecExprOutcome::Trap(err), SpecExprOutcome::Trap(serr)) => err == serr,
            (ExecExprOutcome::OutOfFuel, SpecExprOutcome::OutOfFuel) => true,
            _ => false,
        },
    decreases fuel, 0nat, spec_expr_size(*e),
{
    match e {
        Expr::Const(n) => ExecExprOutcome::Ok(*n),
        Expr::Local(slot) => {
            if *slot < locals.len() {
                ExecExprOutcome::Ok(locals[*slot])
            } else {
                ExecExprOutcome::Trap(VmError::InvalidLocal)
            }
        },
        Expr::Global(slot) => {
            if *slot < globals.len() {
                ExecExprOutcome::Ok(globals[*slot])
            } else {
                ExecExprOutcome::Trap(VmError::InvalidGlobal)
            }
        },
        Expr::Not(inner) => {
            match exec_eval_expr(prog, inner, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(v) => ExecExprOutcome::Ok(eval_not(v)),
                other => other,
            }
        },
        Expr::BinOp(op, lhs, rhs) => {
            match exec_eval_expr(prog, lhs, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(v1) => {
                    match exec_eval_expr(prog, rhs, locals, globals, heap, fuel) {
                        ExecExprOutcome::Ok(v2) => {
                            match eval_binop(*op, v1, v2) {
                                Ok(res) => ExecExprOutcome::Ok(res),
                                Err(err) => ExecExprOutcome::Trap(err),
                            }
                        },
                        other => other,
                    }
                },
                other => other,
            }
        },
        Expr::LogAnd(lhs, rhs) => {
            match exec_eval_expr(prog, lhs, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(v1) => {
                    if v1 == 0 {
                        ExecExprOutcome::Ok(0)
                    } else {
                        match exec_eval_expr(prog, rhs, locals, globals, heap, fuel) {
                            ExecExprOutcome::Ok(v2) => ExecExprOutcome::Ok(eval_not(eval_not(v2))),
                            other => other,
                        }
                    }
                },
                other => other,
            }
        },
        Expr::LogOr(lhs, rhs) => {
            match exec_eval_expr(prog, lhs, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(v1) => {
                    if v1 != 0 {
                        ExecExprOutcome::Ok(1)
                    } else {
                        match exec_eval_expr(prog, rhs, locals, globals, heap, fuel) {
                            ExecExprOutcome::Ok(v2) => ExecExprOutcome::Ok(eval_not(eval_not(v2))),
                            other => other,
                        }
                    }
                },
                other => other,
            }
        },
        Expr::Call(func_idx, args) => {
            match exec_eval_args(prog, args, locals, globals, heap, fuel) {
                ExecArgsOutcome::Ok(vals) => {
                    if *func_idx >= prog.funcs.len() {
                        ExecExprOutcome::Trap(VmError::InvalidCall)
                    } else {
                        let callee = &prog.funcs[*func_idx];
                        if vals.len() != callee.num_params {
                            ExecExprOutcome::Trap(VmError::InvalidCall)
                        } else {
                            match pad_locals_owned(vals, callee.num_locals) {
                                None => ExecExprOutcome::Trap(VmError::InvalidCall),
                                Some(callee_locals) => {
                                    if fuel == 0 {
                                        ExecExprOutcome::OutOfFuel
                                    } else {
                                        exec_eval_call_body(
                                            prog,
                                            *func_idx,
                                            callee_locals,
                                            globals,
                                            heap,
                                            fuel - 1,
                                        )
                                    }
                                },
                            }
                        }
                    }
                },
                ExecArgsOutcome::Trap(err) => ExecExprOutcome::Trap(err),
                ExecArgsOutcome::OutOfFuel => ExecExprOutcome::OutOfFuel,
            }
        },
        Expr::ArrayNew(len_e) => {
            match exec_eval_expr(prog, len_e, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(len) => {
                    match heap.alloc_array(len) {
                        Ok(id) => ExecExprOutcome::Ok(id),
                        Err(err) => ExecExprOutcome::Trap(err),
                    }
                },
                other => other,
            }
        },
        Expr::ArrayGet(arr_e, idx_e) => {
            match exec_eval_expr(prog, arr_e, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(arr) => {
                    match exec_eval_expr(prog, idx_e, locals, globals, heap, fuel) {
                        ExecExprOutcome::Ok(idx) => {
                            match heap.array_get(arr, idx) {
                                Ok(elem) => ExecExprOutcome::Ok(elem),
                                Err(err) => ExecExprOutcome::Trap(err),
                            }
                        },
                        other => other,
                    }
                },
                other => other,
            }
        },
    }
}

fn exec_eval_args(
    prog: &Program,
    args: &ExprList,
    locals: &[i64],
    globals: &mut Vec<i64>,
    heap: &mut ExecHeap,
    fuel: usize,
) -> (r: ExecArgsOutcome)
    ensures
        match (r, spec_eval_args(prog@, *args, locals@, old(globals)@, old(heap)@, fuel as nat)) {
            (ExecArgsOutcome::Ok(vals), SpecArgsOutcome::Ok { vals: svals, globals: sg, heap: sh }) =>
                vals@ == svals && final(globals)@ == sg && final(heap)@ == sh,
            (ExecArgsOutcome::Trap(err), SpecArgsOutcome::Trap(serr)) => err == serr,
            (ExecArgsOutcome::OutOfFuel, SpecArgsOutcome::OutOfFuel) => true,
            _ => false,
        },
    decreases fuel, 0nat, spec_expr_list_size(*args),
{
    match args {
        ExprList::Nil => ExecArgsOutcome::Ok(Vec::new()),
        ExprList::Cons(head, tail) => {
            match exec_eval_expr(prog, head, locals, globals, heap, fuel) {
                ExecExprOutcome::Ok(vh) => {
                    match exec_eval_args(prog, tail, locals, globals, heap, fuel) {
                        ExecArgsOutcome::Ok(mut vt) => {
                            let mut out: Vec<i64> = Vec::new();
                            out.push(vh);
                            proof {
                                assert(out@ =~= seq![vh]);
                            }
                            out.append(&mut vt);
                            ExecArgsOutcome::Ok(out)
                        },
                        other => other,
                    }
                },
                ExecExprOutcome::Trap(err) => ExecArgsOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecArgsOutcome::OutOfFuel,
            }
        },
    }
}

fn exec_eval_call_body(
    prog: &Program,
    func_idx: usize,
    mut callee_locals: Vec<i64>,
    globals: &mut Vec<i64>,
    heap: &mut ExecHeap,
    fuel: usize,
) -> (r: ExecExprOutcome)
    ensures
        match (r, spec_eval_call_body(prog@, func_idx, callee_locals@, old(globals)@, old(heap)@, fuel as nat)) {
            (ExecExprOutcome::Ok(v), SpecExprOutcome::Ok { val: sv, globals: sg, heap: sh }) =>
                v == sv && final(globals)@ == sg && final(heap)@ == sh,
            (ExecExprOutcome::Trap(err), SpecExprOutcome::Trap(serr)) => err == serr,
            (ExecExprOutcome::OutOfFuel, SpecExprOutcome::OutOfFuel) => true,
            _ => false,
        },
    decreases fuel, 1nat, 0nat,
{
    if func_idx >= prog.funcs.len() {
        return ExecExprOutcome::Trap(VmError::InvalidCall);
    }
    match exec_eval_stmt(prog, &prog.funcs[func_idx].body, &mut callee_locals, globals, heap, fuel) {
        ExecStmtOutcome::Normal => ExecExprOutcome::Ok(0),
        ExecStmtOutcome::Return(rv) => ExecExprOutcome::Ok(rv),
        ExecStmtOutcome::Trap(err) => ExecExprOutcome::Trap(err),
        ExecStmtOutcome::OutOfFuel => ExecExprOutcome::OutOfFuel,
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn exec_eval_stmt(
    prog: &Program,
    s: &Stmt,
    locals: &mut Vec<i64>,
    globals: &mut Vec<i64>,
    heap: &mut ExecHeap,
    fuel: usize,
) -> (r: ExecStmtOutcome)
    ensures
        match (r, spec_eval_stmt(prog@, *s, old(locals)@, old(globals)@, old(heap)@, fuel as nat)) {
            (ExecStmtOutcome::Normal, SpecStmtOutcome::Normal { locals: sl, globals: sg, heap: sh }) =>
                final(locals)@ == sl && final(globals)@ == sg && final(heap)@ == sh,
            (ExecStmtOutcome::Return(rv), SpecStmtOutcome::Return { val: srv, locals: sl, globals: sg, heap: sh }) =>
                rv == srv && final(locals)@ == sl && final(globals)@ == sg && final(heap)@ == sh,
            (ExecStmtOutcome::Trap(err), SpecStmtOutcome::Trap(serr)) => err == serr,
            (ExecStmtOutcome::OutOfFuel, SpecStmtOutcome::OutOfFuel) => true,
            _ => false,
        },
    decreases fuel, 0nat, spec_stmt_size(*s),
{
    match s {
        Stmt::Nop => ExecStmtOutcome::Normal,
        Stmt::SetLocal(slot, expr) => {
            match exec_eval_expr(prog, expr, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(val) => {
                    if *slot < locals.len() {
                        locals[*slot] = val;
                        ExecStmtOutcome::Normal
                    } else {
                        ExecStmtOutcome::Trap(VmError::InvalidLocal)
                    }
                },
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::SetGlobal(slot, expr) => {
            match exec_eval_expr(prog, expr, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(val) => {
                    if *slot < globals.len() {
                        globals[*slot] = val;
                        ExecStmtOutcome::Normal
                    } else {
                        ExecStmtOutcome::Trap(VmError::InvalidGlobal)
                    }
                },
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::ArraySet(arr_e, idx_e, val_e) => {
            match exec_eval_expr(prog, arr_e, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(arr) => {
                    match exec_eval_expr(prog, idx_e, locals.as_slice(), globals, heap, fuel) {
                        ExecExprOutcome::Ok(idx) => {
                            match exec_eval_expr(prog, val_e, locals.as_slice(), globals, heap, fuel) {
                                ExecExprOutcome::Ok(val) => {
                                    match heap.array_set(arr, idx, val) {
                                        Ok(()) => ExecStmtOutcome::Normal,
                                        Err(err) => ExecStmtOutcome::Trap(err),
                                    }
                                },
                                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
                            }
                        },
                        ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                        ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
                    }
                },
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::ExprStmt(expr) => {
            match exec_eval_expr(prog, expr, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(_) => ExecStmtOutcome::Normal,
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::If(cond, then_s, else_s) => {
            match exec_eval_expr(prog, cond, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(vc) => {
                    if vc != 0 {
                        exec_eval_stmt(prog, then_s, locals, globals, heap, fuel)
                    } else {
                        exec_eval_stmt(prog, else_s, locals, globals, heap, fuel)
                    }
                },
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
        Stmt::While(cond, body) => {
            if fuel == 0 {
                ExecStmtOutcome::OutOfFuel
            } else {
                let f1 = fuel - 1;
                match exec_eval_expr(prog, cond, locals.as_slice(), globals, heap, f1) {
                    ExecExprOutcome::Ok(vc) => {
                        if vc == 0 {
                            ExecStmtOutcome::Normal
                        } else {
                            match exec_eval_stmt(prog, body, locals, globals, heap, f1) {
                                ExecStmtOutcome::Normal =>
                                    exec_eval_stmt(prog, s, locals, globals, heap, f1),
                                other => other,
                            }
                        }
                    },
                    ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                    ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
                }
            }
        },
        Stmt::Seq(s1, s2) => {
            match exec_eval_stmt(prog, s1, locals, globals, heap, fuel) {
                ExecStmtOutcome::Normal => exec_eval_stmt(prog, s2, locals, globals, heap, fuel),
                other => other,
            }
        },
        Stmt::Return(expr) => {
            match exec_eval_expr(prog, expr, locals.as_slice(), globals, heap, fuel) {
                ExecExprOutcome::Ok(val) => ExecStmtOutcome::Return(val),
                ExecExprOutcome::Trap(err) => ExecStmtOutcome::Trap(err),
                ExecExprOutcome::OutOfFuel => ExecStmtOutcome::OutOfFuel,
            }
        },
    }
}

pub fn eval_program(prog: &Program, init_locals: &[i64], fuel: usize) -> (r: ExecProgramOutcome)
    ensures
        r@ == spec_eval_program(prog@, init_locals@, fuel as nat),
{
    if prog.entry >= prog.funcs.len() || prog.num_globals > MAX_GLOBALS {
        return ExecProgramOutcome::Trap(VmError::InvalidEntry);
    }
    let entry_fn = &prog.funcs[prog.entry];
    match pad_locals_from_slice(init_locals, entry_fn.num_locals) {
        None => ExecProgramOutcome::Trap(VmError::InvalidLocal),
        Some(mut locals) => {
            let mut globals = alloc_zeros(prog.num_globals);
            let mut heap = ExecHeap::new();
            match exec_eval_stmt(prog, &entry_fn.body, &mut locals, &mut globals, &mut heap, fuel) {
                ExecStmtOutcome::Normal => ExecProgramOutcome::Done { val: 0, globals, heap },
                ExecStmtOutcome::Return(rv) => ExecProgramOutcome::Done { val: rv, globals, heap },
                ExecStmtOutcome::Trap(err) => ExecProgramOutcome::Trap(err),
                ExecStmtOutcome::OutOfFuel => ExecProgramOutcome::OutOfFuel,
            }
        },
    }
}

// Ergonomic AST builder helpers (also verified)
pub fn expr_list_from_vec(mut items: Vec<Expr>) -> (r: ExprList) {
    let mut acc = ExprList::Nil;
    while items.len() > 0
        decreases items.len(),
    {
        let e = items.pop().unwrap();
        acc = ExprList::Cons(Box::new(e), Box::new(acc));
    }
    acc
}

} // verus!
