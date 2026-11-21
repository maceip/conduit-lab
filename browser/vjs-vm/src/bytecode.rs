//! Verified Stack Bytecode VM for `vjs_vm`.
//!
//! Defines the flat bytecode instruction set (`Instr`), call-frame stack machine (`SpecVmState` /
//! `ExecFrame`), small-step transition semantics (`spec_vm_step`), fuel-bounded execution
//! (`spec_vm_run_steps`, `spec_run_vm`), and the register-friendly executable interpreter
//! `run_vm` proved equivalent to `spec_run_vm` (`ensures r@ == spec_run_vm(...)`).

use vstd::prelude::*;
use crate::ast::{
    alloc_zeros, eval_binop, eval_not, pad_locals_from_slice, BinOp, ExecHeap, ExecProgramOutcome,
    SpecHeap, VmError, MAX_GLOBALS, MAX_LOCALS,
};
#[cfg(verus_keep_ghost)]
use crate::ast::{spec_binop, spec_not, spec_pad_locals, spec_zeros, SpecProgramOutcome};

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Instr {
    PushConst(i64),
    Pop,
    LoadLocal(usize),
    StoreLocal(usize),
    LoadGlobal(usize),
    StoreGlobal(usize),
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
    Not,
    /// Forward PC-relative jump: `pc' = pc + 1 + offset`.
    Jump(usize),
    /// Backward PC-relative jump: `pc' = pc - offset`.
    JumpBack(usize),
    /// Conditional forward PC-relative jump: pops `cond`; if `cond == 0`, `pc' = pc + 1 + offset`, else `pc + 1`.
    JumpIfFalse(usize),
    /// Function call: `(func_idx, argc)`.
    Call(usize, usize),
    /// Return top of stack from current frame.
    Ret,
    /// Pops `len`, allocates zero-initialized array on `heap`, pushes handle.
    ArrayNew,
    /// Pops `idx` then `arr`, pushes `heap[arr][idx]`.
    ArrayGet,
    /// Pops `val`, `idx`, `arr`, sets `heap[arr][idx] = val`.
    ArraySet,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CompiledFunc {
    pub num_params: usize,
    pub num_locals: usize,
    pub code: Vec<Instr>,
}

pub struct SpecCompiledFunc {
    pub num_params: usize,
    pub num_locals: usize,
    pub code: Seq<Instr>,
}

impl View for CompiledFunc {
    type V = SpecCompiledFunc;

    open spec fn view(&self) -> SpecCompiledFunc {
        SpecCompiledFunc {
            num_params: self.num_params,
            num_locals: self.num_locals,
            code: self.code@,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CompiledProgram {
    pub funcs: Vec<CompiledFunc>,
    pub entry: usize,
    pub num_globals: usize,
}

pub struct SpecCompiledProgram {
    pub funcs: Seq<SpecCompiledFunc>,
    pub entry: usize,
    pub num_globals: usize,
}

impl View for CompiledProgram {
    type V = SpecCompiledProgram;

    open spec fn view(&self) -> SpecCompiledProgram {
        SpecCompiledProgram {
            funcs: Seq::new(self.funcs@.len(), |i: int| self.funcs@[i]@),
            entry: self.entry,
            num_globals: self.num_globals,
        }
    }
}

pub struct SpecFrame {
    pub func_idx: usize,
    pub pc: nat,
    pub locals: Seq<i64>,
    pub stack: Seq<i64>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExecFrame {
    pub func_idx: usize,
    pub pc: usize,
    pub locals: Vec<i64>,
    pub stack: Vec<i64>,
}

impl View for ExecFrame {
    type V = SpecFrame;

    open spec fn view(&self) -> SpecFrame {
        SpecFrame {
            func_idx: self.func_idx,
            pc: self.pc as nat,
            locals: self.locals@,
            stack: self.stack@,
        }
    }
}

pub open spec fn spec_frames_view(frames: Seq<ExecFrame>) -> Seq<SpecFrame> {
    Seq::new(frames.len(), |i: int| frames[i]@)
}

pub struct SpecVmState {
    pub cur: SpecFrame,
    pub callers: Seq<SpecFrame>,
    pub globals: Seq<i64>,
    pub heap: SpecHeap,
}

pub enum SpecVmStep {
    Running(SpecVmState),
    Done { val: i64, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
}

pub enum SpecVmRunOutcome {
    Running(SpecVmState),
    Done { val: i64, globals: Seq<i64>, heap: SpecHeap },
    Trap(VmError),
}

enum ExecStepStatus {
    Running,
    Done(i64),
    Trap(VmError),
}

// ---------------------------------------------------------------------------
// Small-step VM semantics
// ---------------------------------------------------------------------------

pub open spec fn spec_instr_binop(instr: Instr) -> Option<BinOp> {
    match instr {
        Instr::Add => Some(BinOp::Add),
        Instr::Sub => Some(BinOp::Sub),
        Instr::Mul => Some(BinOp::Mul),
        Instr::Div => Some(BinOp::Div),
        Instr::Mod => Some(BinOp::Mod),
        Instr::BitAnd => Some(BinOp::BitAnd),
        Instr::BitOr => Some(BinOp::BitOr),
        Instr::BitXor => Some(BinOp::BitXor),
        Instr::Eq => Some(BinOp::Eq),
        Instr::Lt => Some(BinOp::Lt),
        Instr::Le => Some(BinOp::Le),
        _ => None,
    }
}

pub open spec fn spec_vm_step_binop(op: BinOp, st: SpecVmState) -> SpecVmStep {
    let stk = st.cur.stack;
    if stk.len() < 2 {
        SpecVmStep::Trap(VmError::StackUnderflow)
    } else {
        let b = stk[stk.len() - 1];
        let a = stk[stk.len() - 2];
        let rem = stk.subrange(0, stk.len() - 2);
        match spec_binop(op, a, b) {
            Ok(res) => SpecVmStep::Running(SpecVmState {
                cur: SpecFrame {
                    pc: st.cur.pc + 1,
                    stack: rem.push(res),
                    ..st.cur
                },
                ..st
            }),
            Err(err) => SpecVmStep::Trap(err),
        }
    }
}

pub open spec fn spec_frame_return(
    callers: Seq<SpecFrame>,
    rv: i64,
    globals: Seq<i64>,
    heap: SpecHeap,
) -> SpecVmStep {
    if callers.len() == 0 {
        SpecVmStep::Done { val: rv, globals, heap }
    } else {
        let caller = callers[callers.len() - 1];
        let rem_callers = callers.subrange(0, callers.len() - 1);
        SpecVmStep::Running(SpecVmState {
            cur: SpecFrame {
                stack: caller.stack.push(rv),
                ..caller
            },
            callers: rem_callers,
            globals,
            heap,
        })
    }
}

pub open spec fn spec_vm_step(prog: SpecCompiledProgram, st: SpecVmState) -> SpecVmStep {
    if (st.cur.func_idx as nat) >= prog.funcs.len() {
        SpecVmStep::Trap(VmError::InvalidCall)
    } else {
        let code = prog.funcs[st.cur.func_idx as int].code;
        if st.cur.pc >= code.len() {
            SpecVmStep::Trap(VmError::InvalidJump)
        } else {
            let instr = code[st.cur.pc as int];
            match instr {
                Instr::PushConst(n) => SpecVmStep::Running(SpecVmState {
                    cur: SpecFrame {
                        pc: st.cur.pc + 1,
                        stack: st.cur.stack.push(n),
                        ..st.cur
                    },
                    ..st
                }),
                Instr::Pop => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                stack: st.cur.stack.subrange(0, st.cur.stack.len() - 1),
                                ..st.cur
                            },
                            ..st
                        })
                    }
                },
                Instr::LoadLocal(slot) => {
                    if (slot as nat) < st.cur.locals.len() {
                        let v = st.cur.locals[slot as int];
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                stack: st.cur.stack.push(v),
                                ..st.cur
                            },
                            ..st
                        })
                    } else {
                        SpecVmStep::Trap(VmError::InvalidLocal)
                    }
                },
                Instr::StoreLocal(slot) => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else if (slot as nat) >= st.cur.locals.len() {
                        SpecVmStep::Trap(VmError::InvalidLocal)
                    } else {
                        let v = st.cur.stack[st.cur.stack.len() - 1];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 1);
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                locals: st.cur.locals.update(slot as int, v),
                                stack: rem,
                                ..st.cur
                            },
                            ..st
                        })
                    }
                },
                Instr::LoadGlobal(slot) => {
                    if (slot as nat) < st.globals.len() {
                        let v = st.globals[slot as int];
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                stack: st.cur.stack.push(v),
                                ..st.cur
                            },
                            ..st
                        })
                    } else {
                        SpecVmStep::Trap(VmError::InvalidGlobal)
                    }
                },
                Instr::StoreGlobal(slot) => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else if (slot as nat) >= st.globals.len() {
                        SpecVmStep::Trap(VmError::InvalidGlobal)
                    } else {
                        let v = st.cur.stack[st.cur.stack.len() - 1];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 1);
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                stack: rem,
                                ..st.cur
                            },
                            globals: st.globals.update(slot as int, v),
                            ..st
                        })
                    }
                },
                Instr::Add => spec_vm_step_binop(BinOp::Add, st),
                Instr::Sub => spec_vm_step_binop(BinOp::Sub, st),
                Instr::Mul => spec_vm_step_binop(BinOp::Mul, st),
                Instr::Div => spec_vm_step_binop(BinOp::Div, st),
                Instr::Mod => spec_vm_step_binop(BinOp::Mod, st),
                Instr::BitAnd => spec_vm_step_binop(BinOp::BitAnd, st),
                Instr::BitOr => spec_vm_step_binop(BinOp::BitOr, st),
                Instr::BitXor => spec_vm_step_binop(BinOp::BitXor, st),
                Instr::Eq => spec_vm_step_binop(BinOp::Eq, st),
                Instr::Lt => spec_vm_step_binop(BinOp::Lt, st),
                Instr::Le => spec_vm_step_binop(BinOp::Le, st),
                Instr::Not => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let v = st.cur.stack[st.cur.stack.len() - 1];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 1);
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1,
                                stack: rem.push(spec_not(v)),
                                ..st.cur
                            },
                            ..st
                        })
                    }
                },
                Instr::Jump(offset) => {
                    if st.cur.pc + 1 + (offset as nat) <= code.len() {
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: st.cur.pc + 1 + (offset as nat),
                                ..st.cur
                            },
                            ..st
                        })
                    } else {
                        SpecVmStep::Trap(VmError::InvalidJump)
                    }
                },
                Instr::JumpBack(offset) => {
                    if (offset as nat) <= st.cur.pc {
                        SpecVmStep::Running(SpecVmState {
                            cur: SpecFrame {
                                pc: (st.cur.pc - (offset as nat)) as nat,
                                ..st.cur
                            },
                            ..st
                        })
                    } else {
                        SpecVmStep::Trap(VmError::InvalidJump)
                    }
                },
                Instr::JumpIfFalse(offset) => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let cond = st.cur.stack[st.cur.stack.len() - 1];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 1);
                        if cond == 0 {
                            if st.cur.pc + 1 + (offset as nat) <= code.len() {
                                SpecVmStep::Running(SpecVmState {
                                    cur: SpecFrame {
                                        pc: st.cur.pc + 1 + (offset as nat),
                                        stack: rem,
                                        ..st.cur
                                    },
                                    ..st
                                })
                            } else {
                                SpecVmStep::Trap(VmError::InvalidJump)
                            }
                        } else {
                            SpecVmStep::Running(SpecVmState {
                                cur: SpecFrame {
                                    pc: st.cur.pc + 1,
                                    stack: rem,
                                    ..st.cur
                                },
                                ..st
                            })
                        }
                    }
                },
                Instr::Call(callee_idx, argc) => {
                    if st.cur.stack.len() < (argc as nat) {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else if (callee_idx as nat) >= prog.funcs.len() {
                        SpecVmStep::Trap(VmError::InvalidCall)
                    } else {
                        let callee = prog.funcs[callee_idx as int];
                        if argc != callee.num_params {
                            SpecVmStep::Trap(VmError::InvalidCall)
                        } else {
                            let split = (st.cur.stack.len() - (argc as nat)) as int;
                            let rem_stack = st.cur.stack.subrange(0, split);
                            let arg_vals = st.cur.stack.subrange(split, st.cur.stack.len() as int);
                            match spec_pad_locals(arg_vals, callee.num_locals) {
                                None => SpecVmStep::Trap(VmError::InvalidCall),
                                Some(callee_locals) => {
                                    let saved_caller = SpecFrame {
                                        func_idx: st.cur.func_idx,
                                        pc: st.cur.pc + 1,
                                        locals: st.cur.locals,
                                        stack: rem_stack,
                                    };
                                    let callee_frame = SpecFrame {
                                        func_idx: callee_idx,
                                        pc: 0,
                                        locals: callee_locals,
                                        stack: Seq::empty(),
                                    };
                                    SpecVmStep::Running(SpecVmState {
                                        cur: callee_frame,
                                        callers: st.callers.push(saved_caller),
                                        globals: st.globals,
                                        heap: st.heap,
                                    })
                                },
                            }
                        }
                    }
                },
                Instr::Ret => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let rv = st.cur.stack[st.cur.stack.len() - 1];
                        spec_frame_return(st.callers, rv, st.globals, st.heap)
                    }
                },
                Instr::ArrayNew => {
                    if st.cur.stack.len() == 0 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let len = st.cur.stack[st.cur.stack.len() - 1];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 1);
                        match crate::ast::spec_heap_alloc(st.heap, len) {
                            Ok((id, h2)) => SpecVmStep::Running(SpecVmState {
                                cur: SpecFrame {
                                    pc: st.cur.pc + 1,
                                    stack: rem.push(id),
                                    ..st.cur
                                },
                                heap: h2,
                                ..st
                            }),
                            Err(err) => SpecVmStep::Trap(err),
                        }
                    }
                },
                Instr::ArrayGet => {
                    if st.cur.stack.len() < 2 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let idx = st.cur.stack[st.cur.stack.len() - 1];
                        let arr = st.cur.stack[st.cur.stack.len() - 2];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 2);
                        match crate::ast::spec_heap_get(st.heap, arr, idx) {
                            Ok(elem) => SpecVmStep::Running(SpecVmState {
                                cur: SpecFrame {
                                    pc: st.cur.pc + 1,
                                    stack: rem.push(elem),
                                    ..st.cur
                                },
                                ..st
                            }),
                            Err(err) => SpecVmStep::Trap(err),
                        }
                    }
                },
                Instr::ArraySet => {
                    if st.cur.stack.len() < 3 {
                        SpecVmStep::Trap(VmError::StackUnderflow)
                    } else {
                        let val = st.cur.stack[st.cur.stack.len() - 1];
                        let idx = st.cur.stack[st.cur.stack.len() - 2];
                        let arr = st.cur.stack[st.cur.stack.len() - 3];
                        let rem = st.cur.stack.subrange(0, st.cur.stack.len() - 3);
                        match crate::ast::spec_heap_set(st.heap, arr, idx, val) {
                            Ok(h2) => SpecVmStep::Running(SpecVmState {
                                cur: SpecFrame {
                                    pc: st.cur.pc + 1,
                                    stack: rem,
                                    ..st.cur
                                },
                                heap: h2,
                                ..st
                            }),
                            Err(err) => SpecVmStep::Trap(err),
                        }
                    }
                },
            }
        }
    }
}

pub open spec fn spec_vm_run_steps(
    prog: SpecCompiledProgram,
    st: SpecVmState,
    fuel: nat,
) -> SpecVmRunOutcome
    decreases fuel,
{
    if fuel == 0 {
        SpecVmRunOutcome::Running(st)
    } else {
        match spec_vm_step(prog, st) {
            SpecVmStep::Running(st1) => spec_vm_run_steps(prog, st1, (fuel - 1) as nat),
            SpecVmStep::Done { val, globals, heap } =>
                SpecVmRunOutcome::Done { val, globals, heap },
            SpecVmStep::Trap(err) => SpecVmRunOutcome::Trap(err),
        }
    }
}

pub open spec fn spec_run_vm(
    prog: SpecCompiledProgram,
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
                let init_state = SpecVmState {
                    cur: SpecFrame {
                        func_idx: prog.entry,
                        pc: 0,
                        locals: locals0,
                        stack: Seq::empty(),
                    },
                    callers: Seq::empty(),
                    globals: spec_zeros(prog.num_globals as nat),
                    heap: Seq::empty(),
                };
                match spec_vm_run_steps(prog, init_state, fuel) {
                    SpecVmRunOutcome::Done { val, globals, heap } =>
                        SpecProgramOutcome::Done { val, globals, heap },
                    SpecVmRunOutcome::Trap(err) => SpecProgramOutcome::Trap(err),
                    SpecVmRunOutcome::Running(_) => SpecProgramOutcome::OutOfFuel,
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Verified Executable Stack VM
// ---------------------------------------------------------------------------

fn exec_step_binop(op: BinOp, cur: &mut ExecFrame) -> (r: Result<(), VmError>)
    requires
        old(cur).pc < usize::MAX,
    ensures
        match (r, spec_vm_step_binop(op, SpecVmState {
            cur: old(cur)@,
            callers: Seq::empty(),
            globals: Seq::empty(),
            heap: Seq::empty(),
        })) {
            (Ok(()), SpecVmStep::Running(st1)) => final(cur)@ == st1.cur,
            (Err(e), SpecVmStep::Trap(se)) => e == se,
            _ => false,
        },
{
    if cur.stack.len() < 2 {
        return Err(VmError::StackUnderflow);
    }
    let ghost s0 = cur.stack@;
    let b = cur.stack.pop().unwrap();
    let a = cur.stack.pop().unwrap();
    match eval_binop(op, a, b) {
        Ok(res) => {
            cur.stack.push(res);
            cur.pc = cur.pc + 1;
            proof {
                assert(cur.stack@ =~= s0.subrange(0, s0.len() - 2).push(res));
            }
            Ok(())
        },
        Err(err) => Err(err),
    }
}

fn pop_args_and_pad_into(
    stack: &mut Vec<i64>,
    argc: usize,
    num_locals: usize,
    mut callee_locals: Vec<i64>,
) -> (out: Vec<i64>)
    requires
        old(stack)@.len() >= argc as nat,
        argc <= num_locals,
        num_locals <= MAX_LOCALS,
    ensures
        final(stack)@ == old(stack)@.subrange(0, (old(stack)@.len() - (argc as nat)) as int),
        Some(out@) == spec_pad_locals(
            old(stack)@.subrange((old(stack)@.len() - (argc as nat)) as int, old(stack)@.len() as int),
            num_locals,
        ),
{
    let total = stack.len();
    let base = total - argc;
    let ghost orig = stack@;
    let ghost arg_slice = orig.subrange(base as int, orig.len() as int);
    callee_locals.truncate(0);
    proof {
        assert(callee_locals@ =~= Seq::<i64>::empty());
    }
    let mut i: usize = 0;
    while i < argc
        invariant
            i <= argc,
            argc <= total,
            base == total - argc,
            total == stack@.len(),
            stack@ == orig,
            callee_locals@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> callee_locals@[k] == orig[(base as int) + k],
        decreases argc - i,
    {
        callee_locals.push(stack[base + i]);
        i = i + 1;
    }
    stack.truncate(base);
    proof {
        assert(stack@ =~= orig.subrange(0, base as int));
        assert(callee_locals@ =~= arg_slice);
    }
    while callee_locals.len() < num_locals
        invariant
            argc <= callee_locals@.len() <= num_locals,
            callee_locals@.subrange(0, argc as int) == arg_slice,
            forall|k: int| argc as int <= k < callee_locals@.len() ==> callee_locals@[k] == 0i64,
        decreases num_locals - callee_locals.len(),
    {
        callee_locals.push(0);
    }
    proof {
        assert(callee_locals@ =~= arg_slice + spec_zeros((num_locals - argc) as nat));
    }
    callee_locals
}

fn exec_step_call(
    prog: &CompiledProgram,
    callee_idx: usize,
    argc: usize,
    cur: &mut ExecFrame,
    callers: &mut Vec<ExecFrame>,
    free_frames: &mut Vec<ExecFrame>,
    _globals: &Vec<i64>,
    _heap: &ExecHeap,
) -> (r: ExecStepStatus)
    requires
        old(cur).pc < usize::MAX,
        old(cur).func_idx < prog.funcs@.len(),
        old(cur).pc < prog.funcs@[old(cur).func_idx as int].code@.len(),
        prog.funcs@[old(cur).func_idx as int].code@[old(cur).pc as int] == Instr::Call(callee_idx, argc),
    ensures
        ({
            let st0 = SpecVmState {
                cur: old(cur)@,
                callers: spec_frames_view(old(callers)@),
                globals: _globals@,
                heap: _heap@,
            };
            match (r, spec_vm_step(prog@, st0)) {
                (ExecStepStatus::Running, SpecVmStep::Running(st1)) =>
                    final(cur)@ == st1.cur
                        && spec_frames_view(final(callers)@) == st1.callers
                        && _globals@ == st1.globals
                        && _heap@ == st1.heap,
                (ExecStepStatus::Trap(e), SpecVmStep::Trap(se)) => e == se,
                _ => false,
            }
        }),
{
    if cur.stack.len() < argc {
        ExecStepStatus::Trap(VmError::StackUnderflow)
    } else if callee_idx >= prog.funcs.len() {
        ExecStepStatus::Trap(VmError::InvalidCall)
    } else {
        let callee = &prog.funcs[callee_idx];
        if argc != callee.num_params || argc > callee.num_locals || callee.num_locals > MAX_LOCALS {
            ExecStepStatus::Trap(VmError::InvalidCall)
        } else {
            let (raw_locals, mut raw_stack) = match free_frames.pop() {
                Some(recycled) => (recycled.locals, recycled.stack),
                None => (Vec::with_capacity(callee.num_locals), Vec::with_capacity(8)),
            };
            raw_stack.truncate(0);
            proof {
                assert(raw_stack@ =~= Seq::<i64>::empty());
            }
            let callee_locals = pop_args_and_pad_into(&mut cur.stack, argc, callee.num_locals, raw_locals);
            let mut next_frame = ExecFrame {
                func_idx: callee_idx,
                pc: 0,
                locals: callee_locals,
                stack: raw_stack,
            };
            cur.pc = cur.pc + 1;
            let ghost old_callers_view = spec_frames_view(callers@);
            let ghost saved_view = cur@;
            core::mem::swap(cur, &mut next_frame);
            callers.push(next_frame);
            proof {
                assert(spec_frames_view(callers@) =~= old_callers_view.push(saved_view));
            }
            ExecStepStatus::Running
        }
    }
}

fn exec_step_ret(
    _prog: &CompiledProgram,
    cur: &mut ExecFrame,
    callers: &mut Vec<ExecFrame>,
    free_frames: &mut Vec<ExecFrame>,
    _globals: &Vec<i64>,
    _heap: &ExecHeap,
) -> (r: ExecStepStatus)
    requires
        old(cur).func_idx < _prog.funcs@.len(),
        old(cur).pc < _prog.funcs@[old(cur).func_idx as int].code@.len(),
        _prog.funcs@[old(cur).func_idx as int].code@[old(cur).pc as int] == Instr::Ret,
    ensures
        ({
            let st0 = SpecVmState {
                cur: old(cur)@,
                callers: spec_frames_view(old(callers)@),
                globals: _globals@,
                heap: _heap@,
            };
            match (r, spec_vm_step(_prog@, st0)) {
                (ExecStepStatus::Running, SpecVmStep::Running(st1)) =>
                    final(cur)@ == st1.cur
                        && spec_frames_view(final(callers)@) == st1.callers
                        && _globals@ == st1.globals
                        && _heap@ == st1.heap,
                (ExecStepStatus::Done(v), SpecVmStep::Done { val: sv, globals: sg, heap: sh }) =>
                    v == sv && _globals@ == sg && _heap@ == sh,
                (ExecStepStatus::Trap(e), SpecVmStep::Trap(se)) => e == se,
                _ => false,
            }
        }),
{
    if cur.stack.len() == 0 {
        ExecStepStatus::Trap(VmError::StackUnderflow)
    } else {
        let rv = cur.stack.pop().unwrap();
        if callers.len() == 0 {
            ExecStepStatus::Done(rv)
        } else {
            let ghost old_callers_view = spec_frames_view(callers@);
            let mut caller = callers.pop().unwrap();
            caller.stack.push(rv);
            core::mem::swap(cur, &mut caller);
            free_frames.push(caller);
            proof {
                assert(spec_frames_view(callers@) =~= old_callers_view.subrange(0, old_callers_view.len() - 1));
            }
            ExecStepStatus::Running
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn exec_vm_step(
    prog: &CompiledProgram,
    cur: &mut ExecFrame,
    callers: &mut Vec<ExecFrame>,
    free_frames: &mut Vec<ExecFrame>,
    globals: &mut Vec<i64>,
    heap: &mut ExecHeap,
) -> (r: ExecStepStatus)
    ensures
        ({
            let st0 = SpecVmState {
                cur: old(cur)@,
                callers: spec_frames_view(old(callers)@),
                globals: old(globals)@,
                heap: old(heap)@,
            };
            match (r, spec_vm_step(prog@, st0)) {
                (ExecStepStatus::Running, SpecVmStep::Running(st1)) =>
                    final(cur)@ == st1.cur
                        && spec_frames_view(final(callers)@) == st1.callers
                        && final(globals)@ == st1.globals
                        && final(heap)@ == st1.heap,
                (ExecStepStatus::Done(v), SpecVmStep::Done { val: sv, globals: sg, heap: sh }) =>
                    v == sv && final(globals)@ == sg && final(heap)@ == sh,
                (ExecStepStatus::Trap(e), SpecVmStep::Trap(se)) => e == se,
                _ => false,
            }
        }),
{
    if cur.func_idx >= prog.funcs.len() {
        return ExecStepStatus::Trap(VmError::InvalidCall);
    }
    let code = &prog.funcs[cur.func_idx].code;
    if cur.pc >= code.len() {
        return ExecStepStatus::Trap(VmError::InvalidJump);
    }
    let instr = code[cur.pc];
    match instr {
        Instr::PushConst(n) => {
            cur.stack.push(n);
            cur.pc = cur.pc + 1;
            ExecStepStatus::Running
        },
        Instr::Pop => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let _ = cur.stack.pop();
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            }
        },
        Instr::LoadLocal(slot) => {
            if slot < cur.locals.len() {
                let v = cur.locals[slot];
                cur.stack.push(v);
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            } else {
                ExecStepStatus::Trap(VmError::InvalidLocal)
            }
        },
        Instr::StoreLocal(slot) => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else if slot >= cur.locals.len() {
                ExecStepStatus::Trap(VmError::InvalidLocal)
            } else {
                let v = cur.stack.pop().unwrap();
                cur.locals[slot] = v;
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            }
        },
        Instr::LoadGlobal(slot) => {
            if slot < globals.len() {
                let v = globals[slot];
                cur.stack.push(v);
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            } else {
                ExecStepStatus::Trap(VmError::InvalidGlobal)
            }
        },
        Instr::StoreGlobal(slot) => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else if slot >= globals.len() {
                ExecStepStatus::Trap(VmError::InvalidGlobal)
            } else {
                let v = cur.stack.pop().unwrap();
                globals[slot] = v;
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            }
        },
        Instr::Add => match exec_step_binop(BinOp::Add, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Sub => match exec_step_binop(BinOp::Sub, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Mul => match exec_step_binop(BinOp::Mul, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Div => match exec_step_binop(BinOp::Div, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Mod => match exec_step_binop(BinOp::Mod, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::BitAnd => match exec_step_binop(BinOp::BitAnd, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::BitOr => match exec_step_binop(BinOp::BitOr, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::BitXor => match exec_step_binop(BinOp::BitXor, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Eq => match exec_step_binop(BinOp::Eq, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Lt => match exec_step_binop(BinOp::Lt, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Le => match exec_step_binop(BinOp::Le, cur) {
            Ok(()) => ExecStepStatus::Running,
            Err(e) => ExecStepStatus::Trap(e),
        },
        Instr::Not => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let v = cur.stack.pop().unwrap();
                cur.stack.push(eval_not(v));
                cur.pc = cur.pc + 1;
                ExecStepStatus::Running
            }
        },
        Instr::Jump(offset) => {
            let rem_code = code.len() - (cur.pc + 1);
            if offset <= rem_code {
                cur.pc = cur.pc + 1 + offset;
                ExecStepStatus::Running
            } else {
                ExecStepStatus::Trap(VmError::InvalidJump)
            }
        },
        Instr::JumpBack(offset) => {
            if offset <= cur.pc {
                cur.pc = cur.pc - offset;
                ExecStepStatus::Running
            } else {
                ExecStepStatus::Trap(VmError::InvalidJump)
            }
        },
        Instr::JumpIfFalse(offset) => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let cond = cur.stack.pop().unwrap();
                if cond == 0 {
                    let rem_code = code.len() - (cur.pc + 1);
                    if offset <= rem_code {
                        cur.pc = cur.pc + 1 + offset;
                        ExecStepStatus::Running
                    } else {
                        ExecStepStatus::Trap(VmError::InvalidJump)
                    }
                } else {
                    cur.pc = cur.pc + 1;
                    ExecStepStatus::Running
                }
            }
        },
        Instr::Call(callee_idx, argc) =>
            exec_step_call(prog, callee_idx, argc, cur, callers, free_frames, globals, heap),
        Instr::Ret => exec_step_ret(prog, cur, callers, free_frames, globals, heap),
        Instr::ArrayNew => {
            if cur.stack.len() == 0 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let len = cur.stack.pop().unwrap();
                match heap.alloc_array(len) {
                    Ok(id) => {
                        cur.stack.push(id);
                        cur.pc = cur.pc + 1;
                        ExecStepStatus::Running
                    },
                    Err(err) => ExecStepStatus::Trap(err),
                }
            }
        },
        Instr::ArrayGet => {
            if cur.stack.len() < 2 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let ghost s0 = cur.stack@;
                let idx = cur.stack.pop().unwrap();
                let arr = cur.stack.pop().unwrap();
                match heap.array_get(arr, idx) {
                    Ok(elem) => {
                        cur.stack.push(elem);
                        cur.pc = cur.pc + 1;
                        proof {
                            assert(cur.stack@ =~= s0.subrange(0, s0.len() - 2).push(elem));
                        }
                        ExecStepStatus::Running
                    },
                    Err(err) => ExecStepStatus::Trap(err),
                }
            }
        },
        Instr::ArraySet => {
            if cur.stack.len() < 3 {
                ExecStepStatus::Trap(VmError::StackUnderflow)
            } else {
                let ghost s0 = cur.stack@;
                let val = cur.stack.pop().unwrap();
                let idx = cur.stack.pop().unwrap();
                let arr = cur.stack.pop().unwrap();
                match heap.array_set(arr, idx, val) {
                    Ok(()) => {
                        cur.pc = cur.pc + 1;
                        proof {
                            assert(cur.stack@ =~= s0.subrange(0, s0.len() - 3));
                        }
                        ExecStepStatus::Running
                    },
                    Err(err) => ExecStepStatus::Trap(err),
                }
            }
        },
    }
}

pub fn run_vm(prog: &CompiledProgram, init_locals: &[i64], fuel: usize) -> (r: ExecProgramOutcome)
    ensures
        r@ == spec_run_vm(prog@, init_locals@, fuel as nat),
{
    if prog.entry >= prog.funcs.len() || prog.num_globals > MAX_GLOBALS {
        return ExecProgramOutcome::Trap(VmError::InvalidEntry);
    }
    let entry_fn = &prog.funcs[prog.entry];
    match pad_locals_from_slice(init_locals, entry_fn.num_locals) {
        None => ExecProgramOutcome::Trap(VmError::InvalidLocal),
        Some(locals0) => {
            let mut cur = ExecFrame {
                func_idx: prog.entry,
                pc: 0,
                locals: locals0,
                stack: Vec::new(),
            };
            let mut callers: Vec<ExecFrame> = Vec::new();
            let mut free_frames: Vec<ExecFrame> = Vec::new();
            let mut globals = alloc_zeros(prog.num_globals);
            let mut heap = ExecHeap::new();
            proof {
                assert(spec_frames_view(callers@) =~= Seq::<SpecFrame>::empty());
            }
            let ghost init_state = SpecVmState {
                cur: cur@,
                callers: spec_frames_view(callers@),
                globals: globals@,
                heap: heap@,
            };
            let mut rem: usize = fuel;
            while rem > 0
                invariant
                    rem <= fuel,
                    (prog@.entry as nat) < prog@.funcs.len(),
                    prog@.num_globals <= MAX_GLOBALS,
                    spec_pad_locals(init_locals@, prog@.funcs[prog@.entry as int].num_locals)
                        == Some(init_state.cur.locals),
                    init_state.cur.func_idx == prog@.entry,
                    init_state.cur.pc == 0,
                    init_state.cur.stack == Seq::<i64>::empty(),
                    init_state.callers == Seq::<SpecFrame>::empty(),
                    init_state.globals == spec_zeros(prog@.num_globals as nat),
                    init_state.heap == Seq::<Seq<i64>>::empty(),
                    spec_vm_run_steps(prog@, init_state, fuel as nat)
                        == spec_vm_run_steps(
                            prog@,
                            SpecVmState {
                                cur: cur@,
                                callers: spec_frames_view(callers@),
                                globals: globals@,
                                heap: heap@,
                            },
                            rem as nat,
                        ),
                decreases rem,
            {
                let ghost pre_state = SpecVmState {
                    cur: cur@,
                    callers: spec_frames_view(callers@),
                    globals: globals@,
                    heap: heap@,
                };
                let status = exec_vm_step(prog, &mut cur, &mut callers, &mut free_frames, &mut globals, &mut heap);
                match status {
                    ExecStepStatus::Running => {
                        rem = rem - 1;
                    },
                    ExecStepStatus::Done(val) => {
                        let out = ExecProgramOutcome::Done { val, globals, heap };
                        proof {
                            assert(spec_vm_run_steps(prog@, pre_state, rem as nat)
                                == SpecVmRunOutcome::Done { val: out.arrow_Done_val(), globals: out.arrow_Done_globals()@, heap: out.arrow_Done_heap()@ });
                        }
                        return out;
                    },
                    ExecStepStatus::Trap(err) => {
                        proof {
                            assert(spec_vm_run_steps(prog@, pre_state, rem as nat)
                                == SpecVmRunOutcome::Trap(err));
                        }
                        return ExecProgramOutcome::Trap(err);
                    },
                }
            }
            ExecProgramOutcome::OutOfFuel
        },
    }
}

} // verus!
