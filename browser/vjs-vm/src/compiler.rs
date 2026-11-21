//! Verified AST-to-Bytecode Compiler (`vjs_vm::compiler`).
//!
//! Compiles `Expr`, `Stmt`, `Func`, and `Program` into position-independent relative-jump stack
//! bytecode (`Instr`), proving `compile_program` refines `spec_compile_program` whenever function
//! bytecode lengths are within `MAX_CODE_LEN`.

use vstd::prelude::*;
use crate::ast::{BinOp, Expr, ExprList, Func, Program, Stmt};
use crate::bytecode::{CompiledFunc, CompiledProgram, Instr};
#[cfg(verus_keep_ghost)]
use crate::ast::{
    spec_expr_list_len, spec_expr_list_size, spec_expr_size, spec_stmt_size, SpecProgram,
};
#[cfg(verus_keep_ghost)]
use crate::bytecode::{SpecCompiledFunc, SpecCompiledProgram};

verus! {

pub const MAX_CODE_LEN: usize = 16_777_216;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompileError {
    CodeSizeExceeded,
}

pub open spec fn spec_binop_instr(op: BinOp) -> Instr {
    match op {
        BinOp::Add => Instr::Add,
        BinOp::Sub => Instr::Sub,
        BinOp::Mul => Instr::Mul,
        BinOp::Div => Instr::Div,
        BinOp::Mod => Instr::Mod,
        BinOp::BitAnd => Instr::BitAnd,
        BinOp::BitOr => Instr::BitOr,
        BinOp::BitXor => Instr::BitXor,
        BinOp::Eq => Instr::Eq,
        BinOp::Lt => Instr::Lt,
        BinOp::Le => Instr::Le,
    }
}

pub fn binop_instr(op: BinOp) -> (r: Instr)
    ensures
        r == spec_binop_instr(op),
{
    match op {
        BinOp::Add => Instr::Add,
        BinOp::Sub => Instr::Sub,
        BinOp::Mul => Instr::Mul,
        BinOp::Div => Instr::Div,
        BinOp::Mod => Instr::Mod,
        BinOp::BitAnd => Instr::BitAnd,
        BinOp::BitOr => Instr::BitOr,
        BinOp::BitXor => Instr::BitXor,
        BinOp::Eq => Instr::Eq,
        BinOp::Lt => Instr::Lt,
        BinOp::Le => Instr::Le,
    }
}

// ---------------------------------------------------------------------------
// Compiler Specification
// ---------------------------------------------------------------------------

pub open spec fn spec_compile_expr(e: Expr) -> Seq<Instr>
    decreases spec_expr_size(e),
{
    match e {
        Expr::Const(n) => seq![Instr::PushConst(n)],
        Expr::Local(slot) => seq![Instr::LoadLocal(slot)],
        Expr::Global(slot) => seq![Instr::LoadGlobal(slot)],
        Expr::Not(inner) => spec_compile_expr(*inner) + seq![Instr::Not],
        Expr::BinOp(op, lhs, rhs) =>
            spec_compile_expr(*lhs) + spec_compile_expr(*rhs) + seq![spec_binop_instr(op)],
        Expr::LogAnd(lhs, rhs) => {
            let c1 = spec_compile_expr(*lhs);
            let c2 = spec_compile_expr(*rhs);
            c1 + seq![Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(0)]
        },
        Expr::LogOr(lhs, rhs) => {
            let c1 = spec_compile_expr(*lhs);
            let c2 = spec_compile_expr(*rhs);
            c1 + seq![Instr::Not, Instr::JumpIfFalse((c2.len() + 3) as usize)]
                + c2
                + seq![Instr::Not, Instr::Not, Instr::Jump(1), Instr::PushConst(1)]
        },
        Expr::Call(func_idx, args) => {
            let ca = spec_compile_args(*args);
            let argc = spec_expr_list_len(*args);
            ca + seq![Instr::Call(func_idx, argc as usize)]
        },
        Expr::ArrayNew(len_e) => spec_compile_expr(*len_e) + seq![Instr::ArrayNew],
        Expr::ArrayGet(arr_e, idx_e) =>
            spec_compile_expr(*arr_e) + spec_compile_expr(*idx_e) + seq![Instr::ArrayGet],
    }
}

pub open spec fn spec_compile_args(args: ExprList) -> Seq<Instr>
    decreases spec_expr_list_size(args),
{
    match args {
        ExprList::Nil => Seq::empty(),
        ExprList::Cons(head, tail) => spec_compile_expr(*head) + spec_compile_args(*tail),
    }
}

pub open spec fn spec_compile_stmt(s: Stmt) -> Seq<Instr>
    decreases spec_stmt_size(s),
{
    match s {
        Stmt::Nop => Seq::empty(),
        Stmt::SetLocal(slot, expr) => spec_compile_expr(expr) + seq![Instr::StoreLocal(slot)],
        Stmt::SetGlobal(slot, expr) => spec_compile_expr(expr) + seq![Instr::StoreGlobal(slot)],
        Stmt::ArraySet(arr_e, idx_e, val_e) =>
            spec_compile_expr(arr_e)
                + spec_compile_expr(idx_e)
                + spec_compile_expr(val_e)
                + seq![Instr::ArraySet],
        Stmt::ExprStmt(expr) => spec_compile_expr(expr) + seq![Instr::Pop],
        Stmt::If(cond, then_s, else_s) => {
            let cc = spec_compile_expr(cond);
            let ct = spec_compile_stmt(*then_s);
            let ce = spec_compile_stmt(*else_s);
            cc + seq![Instr::JumpIfFalse((ct.len() + 1) as usize)]
                + ct
                + seq![Instr::Jump(ce.len() as usize)]
                + ce
        },
        Stmt::While(cond, body) => {
            let cc = spec_compile_expr(cond);
            let cb = spec_compile_stmt(*body);
            cc + seq![Instr::JumpIfFalse((cb.len() + 1) as usize)]
                + cb
                + seq![Instr::JumpBack((cc.len() + 1 + cb.len()) as usize)]
        },
        Stmt::Seq(s1, s2) => spec_compile_stmt(*s1) + spec_compile_stmt(*s2),
        Stmt::Return(expr) => spec_compile_expr(expr) + seq![Instr::Ret],
    }
}

pub open spec fn spec_compile_func(f: Func) -> SpecCompiledFunc {
    SpecCompiledFunc {
        num_params: f.num_params,
        num_locals: f.num_locals,
        code: spec_compile_stmt(f.body) + seq![Instr::PushConst(0), Instr::Ret],
    }
}

pub open spec fn spec_compile_program(p: SpecProgram) -> SpecCompiledProgram {
    SpecCompiledProgram {
        funcs: Seq::new(p.funcs.len(), |i: int| spec_compile_func(p.funcs[i])),
        entry: p.entry,
        num_globals: p.num_globals,
    }
}

pub open spec fn spec_program_code_bounded(p: SpecProgram) -> bool {
    forall|i: int|
        0 <= i < p.funcs.len() ==> (#[trigger] spec_compile_func(p.funcs[i])).code.len()
            <= MAX_CODE_LEN as nat
}

// ---------------------------------------------------------------------------
// Structural length lemmas for lossless offset/arity encoding
// ---------------------------------------------------------------------------

pub proof fn lemma_compile_expr_nonempty(e: Expr)
    ensures
        spec_compile_expr(e).len() >= 1,
    decreases spec_expr_size(e),
{
    match e {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) => {},
        Expr::Not(inner) => lemma_compile_expr_nonempty(*inner),
        Expr::BinOp(_, l, r) | Expr::LogAnd(l, r) | Expr::LogOr(l, r) | Expr::ArrayGet(l, r) => {
            lemma_compile_expr_nonempty(*l);
            lemma_compile_expr_nonempty(*r);
        },
        Expr::Call(_, _) => {},
        Expr::ArrayNew(len_e) => lemma_compile_expr_nonempty(*len_e),
    }
}

pub proof fn lemma_expr_list_len_le_compiled(args: ExprList)
    ensures
        spec_expr_list_len(args) <= spec_compile_args(args).len(),
    decreases spec_expr_list_size(args),
{
    match args {
        ExprList::Nil => {},
        ExprList::Cons(h, t) => {
            lemma_compile_expr_nonempty(*h);
            lemma_expr_list_len_le_compiled(*t);
        },
    }
}

// ---------------------------------------------------------------------------
// Verified Executable Compiler
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn compile_expr(e: &Expr) -> (r: Result<Vec<Instr>, CompileError>)
    ensures
        match r {
            Ok(v) => v@ == spec_compile_expr(*e) && v@.len() <= MAX_CODE_LEN as nat,
            Err(_) => spec_compile_expr(*e).len() > MAX_CODE_LEN as nat,
        },
    decreases spec_expr_size(*e),
{
    match e {
        Expr::Const(n) => {
            let mut v = Vec::new();
            v.push(Instr::PushConst(*n));
            proof {
                assert(v@ =~= seq![Instr::PushConst(*n)]);
            }
            Ok(v)
        },
        Expr::Local(slot) => {
            let mut v = Vec::new();
            v.push(Instr::LoadLocal(*slot));
            proof {
                assert(v@ =~= seq![Instr::LoadLocal(*slot)]);
            }
            Ok(v)
        },
        Expr::Global(slot) => {
            let mut v = Vec::new();
            v.push(Instr::LoadGlobal(*slot));
            proof {
                assert(v@ =~= seq![Instr::LoadGlobal(*slot)]);
            }
            Ok(v)
        },
        Expr::Not(inner) => {
            let mut v = compile_expr(inner)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost old_v = v@;
            v.push(Instr::Not);
            proof {
                assert(v@ =~= old_v + seq![Instr::Not]);
            }
            Ok(v)
        },
        Expr::BinOp(op, lhs, rhs) => {
            let mut c1 = compile_expr(lhs)?;
            let mut c2 = compile_expr(rhs)?;
            if c1.len() >= MAX_CODE_LEN || c2.len() >= MAX_CODE_LEN - c1.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ins = binop_instr(*op);
            let ghost s1 = c1@;
            let ghost s2 = c2@;
            c1.append(&mut c2);
            c1.push(ins);
            proof {
                assert(c1@ =~= s1 + s2 + seq![ins]);
            }
            Ok(c1)
        },
        Expr::LogAnd(lhs, rhs) => {
            let mut c1 = compile_expr(lhs)?;
            let mut c2 = compile_expr(rhs)?;
            if c1.len() > MAX_CODE_LEN - 5 || c2.len() > MAX_CODE_LEN - 5 - c1.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let skip = c2.len() + 3;
            let ghost s1 = c1@;
            let ghost s2 = c2@;
            c1.push(Instr::JumpIfFalse(skip));
            c1.append(&mut c2);
            c1.push(Instr::Not);
            c1.push(Instr::Not);
            c1.push(Instr::Jump(1));
            c1.push(Instr::PushConst(0));
            proof {
                assert(c1@ =~= s1 + seq![Instr::JumpIfFalse(skip)] + s2 + seq![
                    Instr::Not,
                    Instr::Not,
                    Instr::Jump(1),
                    Instr::PushConst(0),
                ]);
            }
            Ok(c1)
        },
        Expr::LogOr(lhs, rhs) => {
            let mut c1 = compile_expr(lhs)?;
            let mut c2 = compile_expr(rhs)?;
            if c1.len() > MAX_CODE_LEN - 6 || c2.len() > MAX_CODE_LEN - 6 - c1.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let skip = c2.len() + 3;
            let ghost s1 = c1@;
            let ghost s2 = c2@;
            c1.push(Instr::Not);
            c1.push(Instr::JumpIfFalse(skip));
            c1.append(&mut c2);
            c1.push(Instr::Not);
            c1.push(Instr::Not);
            c1.push(Instr::Jump(1));
            c1.push(Instr::PushConst(1));
            proof {
                assert(c1@ =~= s1 + seq![Instr::Not, Instr::JumpIfFalse(skip)] + s2 + seq![
                    Instr::Not,
                    Instr::Not,
                    Instr::Jump(1),
                    Instr::PushConst(1),
                ]);
            }
            Ok(c1)
        },
        Expr::Call(func_idx, args) => {
            let (mut ca, argc) = compile_args(args)?;
            if ca.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sa = ca@;
            ca.push(Instr::Call(*func_idx, argc));
            proof {
                assert(ca@ =~= sa + seq![Instr::Call(*func_idx, argc)]);
            }
            Ok(ca)
        },
        Expr::ArrayNew(len_e) => {
            let mut v = compile_expr(len_e)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sv = v@;
            v.push(Instr::ArrayNew);
            proof {
                assert(v@ =~= sv + seq![Instr::ArrayNew]);
            }
            Ok(v)
        },
        Expr::ArrayGet(arr_e, idx_e) => {
            let mut c1 = compile_expr(arr_e)?;
            let mut c2 = compile_expr(idx_e)?;
            if c1.len() >= MAX_CODE_LEN || c2.len() >= MAX_CODE_LEN - c1.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost s1 = c1@;
            let ghost s2 = c2@;
            c1.append(&mut c2);
            c1.push(Instr::ArrayGet);
            proof {
                assert(c1@ =~= s1 + s2 + seq![Instr::ArrayGet]);
            }
            Ok(c1)
        },
    }
}

pub fn compile_args(args: &ExprList) -> (r: Result<(Vec<Instr>, usize), CompileError>)
    ensures
        match r {
            Ok((v, argc)) =>
                v@ == spec_compile_args(*args)
                    && v@.len() <= MAX_CODE_LEN as nat
                    && argc as nat == spec_expr_list_len(*args)
                    && argc <= v.len(),
            Err(_) => spec_compile_args(*args).len() > MAX_CODE_LEN as nat,
        },
    decreases spec_expr_list_size(*args),
{
    match args {
        ExprList::Nil => Ok((Vec::new(), 0)),
        ExprList::Cons(head, tail) => {
            let mut ch = compile_expr(head)?;
            let (mut ct, tail_argc) = compile_args(tail)?;
            if ch.len() > MAX_CODE_LEN - ct.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            proof {
                lemma_compile_expr_nonempty(**head);
            }
            let ghost sh = ch@;
            let ghost st = ct@;
            ch.append(&mut ct);
            proof {
                assert(ch@ =~= sh + st);
            }
            Ok((ch, 1 + tail_argc))
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn compile_stmt(s: &Stmt) -> (r: Result<Vec<Instr>, CompileError>)
    ensures
        match r {
            Ok(v) => v@ == spec_compile_stmt(*s) && v@.len() <= MAX_CODE_LEN as nat,
            Err(_) => spec_compile_stmt(*s).len() > MAX_CODE_LEN as nat,
        },
    decreases spec_stmt_size(*s),
{
    match s {
        Stmt::Nop => Ok(Vec::new()),
        Stmt::SetLocal(slot, expr) => {
            let mut v = compile_expr(expr)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sv = v@;
            v.push(Instr::StoreLocal(*slot));
            proof {
                assert(v@ =~= sv + seq![Instr::StoreLocal(*slot)]);
            }
            Ok(v)
        },
        Stmt::SetGlobal(slot, expr) => {
            let mut v = compile_expr(expr)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sv = v@;
            v.push(Instr::StoreGlobal(*slot));
            proof {
                assert(v@ =~= sv + seq![Instr::StoreGlobal(*slot)]);
            }
            Ok(v)
        },
        Stmt::ArraySet(arr_e, idx_e, val_e) => {
            let mut c1 = compile_expr(arr_e)?;
            let mut c2 = compile_expr(idx_e)?;
            let mut c3 = compile_expr(val_e)?;
            if c1.len() >= MAX_CODE_LEN
                || c2.len() >= MAX_CODE_LEN - c1.len()
                || c3.len() >= MAX_CODE_LEN - c1.len() - c2.len()
            {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost s1 = c1@;
            let ghost s2 = c2@;
            let ghost s3 = c3@;
            c1.append(&mut c2);
            c1.append(&mut c3);
            c1.push(Instr::ArraySet);
            proof {
                assert(c1@ =~= s1 + s2 + s3 + seq![Instr::ArraySet]);
            }
            Ok(c1)
        },
        Stmt::ExprStmt(expr) => {
            let mut v = compile_expr(expr)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sv = v@;
            v.push(Instr::Pop);
            proof {
                assert(v@ =~= sv + seq![Instr::Pop]);
            }
            Ok(v)
        },
        Stmt::If(cond, then_s, else_s) => {
            let mut cc = compile_expr(cond)?;
            let mut ct = compile_stmt(then_s)?;
            let mut ce = compile_stmt(else_s)?;
            if cc.len() > MAX_CODE_LEN - 2
                || ct.len() > MAX_CODE_LEN - 2 - cc.len()
                || ce.len() > MAX_CODE_LEN - 2 - cc.len() - ct.len()
            {
                return Err(CompileError::CodeSizeExceeded);
            }
            let jfalse_off = ct.len() + 1;
            let jend_off = ce.len();
            let ghost sc = cc@;
            let ghost st = ct@;
            let ghost se = ce@;
            cc.push(Instr::JumpIfFalse(jfalse_off));
            cc.append(&mut ct);
            cc.push(Instr::Jump(jend_off));
            cc.append(&mut ce);
            proof {
                assert(cc@ =~= sc + seq![Instr::JumpIfFalse(jfalse_off)] + st + seq![Instr::Jump(jend_off)] + se);
            }
            Ok(cc)
        },
        Stmt::While(cond, body) => {
            let mut cc = compile_expr(cond)?;
            let mut cb = compile_stmt(body)?;
            if cc.len() > MAX_CODE_LEN - 2 || cb.len() > MAX_CODE_LEN - 2 - cc.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let jfalse_off = cb.len() + 1;
            let jback_off = cc.len() + 1 + cb.len();
            let ghost sc = cc@;
            let ghost sb = cb@;
            cc.push(Instr::JumpIfFalse(jfalse_off));
            cc.append(&mut cb);
            cc.push(Instr::JumpBack(jback_off));
            proof {
                assert(cc@ =~= sc + seq![Instr::JumpIfFalse(jfalse_off)] + sb + seq![Instr::JumpBack(jback_off)]);
            }
            Ok(cc)
        },
        Stmt::Seq(s1, s2) => {
            let mut c1 = compile_stmt(s1)?;
            let mut c2 = compile_stmt(s2)?;
            if c1.len() > MAX_CODE_LEN - c2.len() {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sc1 = c1@;
            let ghost sc2 = c2@;
            c1.append(&mut c2);
            proof {
                assert(c1@ =~= sc1 + sc2);
            }
            Ok(c1)
        },
        Stmt::Return(expr) => {
            let mut v = compile_expr(expr)?;
            if v.len() >= MAX_CODE_LEN {
                return Err(CompileError::CodeSizeExceeded);
            }
            let ghost sv = v@;
            v.push(Instr::Ret);
            proof {
                assert(v@ =~= sv + seq![Instr::Ret]);
            }
            Ok(v)
        },
    }
}

pub fn compile_func(f: &Func) -> (r: Result<CompiledFunc, CompileError>)
    ensures
        match r {
            Ok(cf) => cf@ == spec_compile_func(*f) && cf.code@.len() <= MAX_CODE_LEN as nat,
            Err(_) => spec_compile_func(*f).code.len() > MAX_CODE_LEN as nat,
        },
{
    let mut body_code = compile_stmt(&f.body)?;
    if body_code.len() > MAX_CODE_LEN - 2 {
        return Err(CompileError::CodeSizeExceeded);
    }
    let ghost sb = body_code@;
    body_code.push(Instr::PushConst(0));
    body_code.push(Instr::Ret);
    proof {
        assert(body_code@ =~= sb + seq![Instr::PushConst(0), Instr::Ret]);
    }
    Ok(CompiledFunc {
        num_params: f.num_params,
        num_locals: f.num_locals,
        code: body_code,
    })
}

pub fn compile_program(prog: &Program) -> (r: Result<CompiledProgram, CompileError>)
    ensures
        match r {
            Ok(cp) => cp@ == spec_compile_program(prog@) && spec_program_code_bounded(prog@),
            Err(_) => !spec_program_code_bounded(prog@),
        },
{
    let n = prog.funcs.len();
    let mut out_funcs: Vec<CompiledFunc> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == prog.funcs@.len(),
            out_funcs@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> out_funcs@[k]@ == spec_compile_func(prog.funcs@[k]),
            forall|k: int|
                0 <= k < i as int ==> (#[trigger] spec_compile_func(prog.funcs@[k])).code.len()
                    <= MAX_CODE_LEN as nat,
        decreases n - i,
    {
        match compile_func(&prog.funcs[i]) {
            Ok(cf) => {
                out_funcs.push(cf);
                i = i + 1;
            },
            Err(e) => {
                proof {
                    let ghost idx = i as int;
                    let ghost bad = spec_compile_func(prog@.funcs[idx]);
                    assert(0 <= idx < prog@.funcs.len());
                    assert(bad.code.len() > MAX_CODE_LEN as nat);
                }
                return Err(e);
            },
        }
    }
    let cp = CompiledProgram {
        funcs: out_funcs,
        entry: prog.entry,
        num_globals: prog.num_globals,
    };
    proof {
        assert(cp@.funcs =~= spec_compile_program(prog@).funcs);
    }
    Ok(cp)
}

} // verus!
