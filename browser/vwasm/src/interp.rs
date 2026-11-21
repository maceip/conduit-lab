//! Formally verified WebAssembly 1.0 sandboxed interpreter and containment proofs (`vwasm`).
//!
//! Provides:
//! - `WasmInstance` & `SpecWasmInstance::wf` (page-aligned linear memory bounded by `max_pages`,
//!   typed mutable/immutable globals, indirect function table, zero host capabilities).
//! - `instantiate_module`: verified module instantiation checking memory/table/data/elem bounds.
//! - `wasm_step` == `spec_wasm_step`: verified small-step Wasm 1.0 execution covering `i32` & `i64`
//!   numeric/bitwise/shift/rotate/bitcount/div/rem ops, structured control flow (`block`, `loop`,
//!   `if`/`else`, `br`, `br_if`, `br_table`, `return`, `call`, `call_indirect`, `drop`, `select`,
//!   `unreachable`), locals, globals, and linear memory (`load*`, `store*`, `memory.size`, `memory.grow`).
//! - `wasm_invoke` == `spec_wasm_invoke`: verified fuel-bounded entrypoint (`decreases fuel`).
//! - Machine-checked Wasm Sandbox Containment Theorems:
//!   1. `lemma_mem_access_oob_traps_cleanly`: every out-of-bounds effective address
//!      `((addr as u32) as nat) + (offset as nat) + width > inst.memory.len()` deterministically
//!      traps with `WasmTrap::OutOfBoundsMemoryAccess` leaving `inst.memory` identical.
//!   2. `lemma_mem_store_in_bounds_framing`: every in-bounds store preserves `inst.memory.len()`,
//!      preserves `inst.wf()`, and leaves every byte outside `[ea, ea + width)` identical.
//!   3. `lemma_wasm_step_sandbox_containment`: for any untrusted `SpecWasmModule`, any well-formed
//!      `SpecWasmInstance`, and any execution state, `spec_wasm_step` preserves `inst.wf()`,
//!      keeps `inst.max_pages` invariant, keeps `inst.memory.len() <= max_pages * 65536`,
//!      never mutates memory on trap, and performs zero host operations.
//!   4. `theorem_wasm_invoke_sandbox_containment`: by induction on `fuel`, `spec_wasm_invoke`
//!      (and `wasm_invoke`) terminates within `fuel` steps while preserving `inst.wf()`,
//!      `inst.max_pages`, and `inst.memory.len() <= max_pages * 65536` for any untrusted module.

use vstd::prelude::*;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// 1. Sandbox Instance, Call Frames, and Execution State
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WasmInstance {
    pub has_memory: bool,
    pub memory: Vec<u8>,
    pub mem_pages: u32,
    pub max_pages: u32,
    pub globals: Vec<WasmVal>,
    pub global_types: Vec<ValType>,
    pub global_mut: Vec<bool>,
    pub has_table: bool,
    pub table: Vec<Option<u32>>,
}

pub struct SpecWasmInstance {
    pub has_memory: bool,
    pub memory: Seq<u8>,
    pub mem_pages: u32,
    pub max_pages: u32,
    pub globals: Seq<WasmVal>,
    pub global_types: Seq<ValType>,
    pub global_mut: Seq<bool>,
    pub has_table: bool,
    pub table: Seq<Option<u32>>,
}

impl View for WasmInstance {
    type V = SpecWasmInstance;

    open spec fn view(&self) -> SpecWasmInstance {
        SpecWasmInstance {
            has_memory: self.has_memory,
            memory: self.memory@,
            mem_pages: self.mem_pages,
            max_pages: self.max_pages,
            globals: self.globals@,
            global_types: self.global_types@,
            global_mut: self.global_mut@,
            has_table: self.has_table,
            table: self.table@,
        }
    }
}

impl SpecWasmInstance {
    /// Fundamental WebAssembly sandbox invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.memory.len() == (self.mem_pages as nat) * (WASM_PAGE_SIZE as nat)
        &&& (!self.has_memory ==> (self.mem_pages == 0 && self.max_pages == 0))
        &&& self.mem_pages <= self.max_pages
        &&& self.max_pages <= MAX_SPEC_PAGES
        &&& self.mem_pages <= MAX_SANDBOX_PAGES
        &&& self.globals.len() == self.global_types.len()
        &&& self.globals.len() == self.global_mut.len()
        &&& (forall|i: int| 0 <= i < self.globals.len() ==>
            #[trigger] spec_val_has_type(self.globals[i], self.global_types[i]))
        &&& (!self.has_table ==> self.table.len() == 0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CtrlLabel {
    pub target_pc: usize,
    pub stack_height: usize,
    pub arity: usize,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallFrame {
    pub func_idx: usize,
    pub pc: usize,
    pub locals: Vec<WasmVal>,
    pub local_types: Vec<ValType>,
    pub stack: Vec<WasmVal>,
    pub labels: Vec<CtrlLabel>,
    pub return_arity: usize,
}

pub struct SpecCallFrame {
    pub func_idx: usize,
    pub pc: usize,
    pub locals: Seq<WasmVal>,
    pub local_types: Seq<ValType>,
    pub stack: Seq<WasmVal>,
    pub labels: Seq<CtrlLabel>,
    pub return_arity: usize,
}

impl View for CallFrame {
    type V = SpecCallFrame;

    open spec fn view(&self) -> SpecCallFrame {
        SpecCallFrame {
            func_idx: self.func_idx,
            pc: self.pc,
            locals: self.locals@,
            local_types: self.local_types@,
            stack: self.stack@,
            labels: self.labels@,
            return_arity: self.return_arity,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct WasmExecState {
    pub frames: Vec<CallFrame>,
}

pub struct SpecWasmExecState {
    pub frames: Seq<SpecCallFrame>,
}

impl View for WasmExecState {
    type V = SpecWasmExecState;

    open spec fn view(&self) -> SpecWasmExecState {
        SpecWasmExecState {
            frames: Seq::new(self.frames@.len(), |i: int| self.frames@[i]@),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StepOutcome {
    Continue,
    Done(Vec<WasmVal>),
    Trap(WasmTrap),
    Unsupported(u8),
}

pub enum SpecStepOutcome {
    Continue,
    Done(Seq<WasmVal>),
    Trap(WasmTrap),
    Unsupported(u8),
}

impl View for StepOutcome {
    type V = SpecStepOutcome;

    open spec fn view(&self) -> SpecStepOutcome {
        match self {
            StepOutcome::Continue => SpecStepOutcome::Continue,
            StepOutcome::Done(vals) => SpecStepOutcome::Done(vals@),
            StepOutcome::Trap(t) => SpecStepOutcome::Trap(*t),
            StepOutcome::Unsupported(op) => SpecStepOutcome::Unsupported(*op),
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Structural Type Helpers (`exec == spec`)
// ---------------------------------------------------------------------------

pub open spec fn spec_val_type_eq(a: ValType, b: ValType) -> bool {
    match (a, b) {
        (ValType::I32, ValType::I32) => true,
        (ValType::I64, ValType::I64) => true,
        (ValType::F32, ValType::F32) => true,
        (ValType::F64, ValType::F64) => true,
        _ => false,
    }
}

pub fn val_type_eq(a: ValType, b: ValType) -> (eq: bool)
    ensures
        eq == spec_val_type_eq(a, b),
        eq <==> (a == b),
{
    match (a, b) {
        (ValType::I32, ValType::I32) => true,
        (ValType::I64, ValType::I64) => true,
        (ValType::F32, ValType::F32) => true,
        (ValType::F64, ValType::F64) => true,
        _ => false,
    }
}

pub open spec fn spec_same_wasm_val_type(a: WasmVal, b: WasmVal) -> bool {
    match (a, b) {
        (WasmVal::I32(_), WasmVal::I32(_)) => true,
        (WasmVal::I64(_), WasmVal::I64(_)) => true,
        (WasmVal::F32Bits(_), WasmVal::F32Bits(_)) => true,
        (WasmVal::F64Bits(_), WasmVal::F64Bits(_)) => true,
        _ => false,
    }
}

pub fn same_wasm_val_type(a: WasmVal, b: WasmVal) -> (eq: bool)
    ensures
        eq == spec_same_wasm_val_type(a, b),
{
    match (a, b) {
        (WasmVal::I32(_), WasmVal::I32(_)) => true,
        (WasmVal::I64(_), WasmVal::I64(_)) => true,
        (WasmVal::F32Bits(_), WasmVal::F32Bits(_)) => true,
        (WasmVal::F64Bits(_), WasmVal::F64Bits(_)) => true,
        _ => false,
    }
}

pub open spec fn spec_val_types_eq(a: Seq<ValType>, b: Seq<ValType>) -> bool {
    a.len() == b.len()
        && (forall|i: int| 0 <= i < a.len() ==> #[trigger] spec_val_type_eq(a[i], b[i]))
}

pub fn val_types_eq(a: &[ValType], b: &[ValType]) -> (eq: bool)
    ensures
        eq == spec_val_types_eq(a@, b@),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] spec_val_type_eq(a@[k], b@[k]),
        decreases n - i,
    {
        if !val_type_eq(a[i], b[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}

pub open spec fn spec_func_type_eq(a: SpecFuncType, b: SpecFuncType) -> bool {
    spec_val_types_eq(a.params, b.params) && spec_val_types_eq(a.results, b.results)
}

pub fn func_type_eq(a: &FuncType, b: &FuncType) -> (eq: bool)
    ensures
        eq == spec_func_type_eq(a@, b@),
{
    val_types_eq(&a.params, &b.params) && val_types_eq(&a.results, &b.results)
}

// ---------------------------------------------------------------------------
// 3. Verified Module Instantiation (`instantiate_module`)
// ---------------------------------------------------------------------------

#[verifier::spinoff_prover]
pub fn instantiate_module(module: &WasmModule) -> (r: Result<WasmInstance, WasmTrap>)
    ensures
        match r {
            Ok(inst) => inst@.wf(),
            Err(_) => true,
        },
{
    let (has_memory, mem_pages, max_pages, mut memory): (bool, u32, u32, Vec<u8>) =
        match module.memory {
            Some(limits) => {
                let eff_max = match limits.max_pages {
                    Some(mx) => mx,
                    None => MAX_SPEC_PAGES,
                };
                if limits.min_pages > eff_max
                    || eff_max > MAX_SPEC_PAGES
                    || limits.min_pages > MAX_SANDBOX_PAGES
                {
                    return Err(WasmTrap::OutOfBoundsMemoryAccess);
                }
                let byte_len: usize = (limits.min_pages as usize) * WASM_PAGE_SIZE;
                let mut mem: Vec<u8> = Vec::new();
                mem.resize(byte_len, 0u8);
                (true, limits.min_pages, eff_max, mem)
            },
            None => (false, 0u32, 0u32, Vec::new()),
        };

    let mut globals: Vec<WasmVal> = Vec::with_capacity(module.globals.len());
    let mut global_types: Vec<ValType> = Vec::with_capacity(module.globals.len());
    let mut global_mut: Vec<bool> = Vec::with_capacity(module.globals.len());
    let g_len = module.globals.len();
    let mut gi: usize = 0;
    while gi < g_len
        invariant
            gi <= g_len,
            g_len == module.globals@.len(),
            globals@.len() == gi as nat,
            global_types@.len() == gi as nat,
            global_mut@.len() == gi as nat,
            forall|k: int| 0 <= k < gi as int ==>
                #[trigger] spec_val_has_type(globals@[k], global_types@[k]),
        decreases g_len - gi,
    {
        let gd = module.globals[gi];
        if !val_has_type(gd.init, gd.val_type) {
            return Err(WasmTrap::TypeMismatch);
        }
        globals.push(gd.init);
        global_types.push(gd.val_type);
        global_mut.push(gd.mutable);
        gi = gi + 1;
    }

    let (has_table, mut table): (bool, Vec<Option<u32>>) = match module.table {
        Some(tlimits) => {
            if tlimits.min_entries > MAX_TABLE_ENTRIES {
                return Err(WasmTrap::UndefinedElement);
            }
            if let Some(mx) = tlimits.max_entries {
                if tlimits.min_entries > mx || mx > MAX_TABLE_ENTRIES {
                    return Err(WasmTrap::UndefinedElement);
                }
            }
            let mut tbl: Vec<Option<u32>> = Vec::new();
            tbl.resize(tlimits.min_entries as usize, None);
            (true, tbl)
        },
        None => (false, Vec::new()),
    };

    // Validate all elem segments and data segments before copying (Wasm 1.0 §4.5.3.10-12).
    let elem_len = module.elem_segments.len();
    let mut ei: usize = 0;
    while ei < elem_len
        invariant
            ei <= elem_len,
            elem_len == module.elem_segments@.len(),
            !has_table ==> table@.len() == 0,
        decreases elem_len - ei,
    {
        let seg = &module.elem_segments[ei];
        if !has_table {
            return Err(WasmTrap::UndefinedElement);
        }
        if seg.func_indices.len() > table.len()
            || (seg.offset as u64) > ((table.len() - seg.func_indices.len()) as u64)
        {
            return Err(WasmTrap::UndefinedElement);
        }
        ei = ei + 1;
    }

    let data_len = module.data_segments.len();
    let mut di: usize = 0;
    while di < data_len
        invariant
            di <= data_len,
            data_len == module.data_segments@.len(),
            memory@.len() == (mem_pages as nat) * (WASM_PAGE_SIZE as nat),
        decreases data_len - di,
    {
        let seg = &module.data_segments[di];
        if !has_memory || seg.mem_idx != 0 {
            return Err(WasmTrap::OutOfBoundsMemoryAccess);
        }
        if seg.init.len() > memory.len()
            || (seg.offset as u64) > ((memory.len() - seg.init.len()) as u64)
        {
            return Err(WasmTrap::OutOfBoundsMemoryAccess);
        }
        di = di + 1;
    }

    // Apply elem segments.
    ei = 0;
    while ei < elem_len
        invariant
            ei <= elem_len,
            elem_len == module.elem_segments@.len(),
            !has_table ==> table@.len() == 0,
        decreases elem_len - ei,
    {
        let seg = &module.elem_segments[ei];
        let tlen = table.len();
        let flen = seg.func_indices.len();
        if !has_table || flen > tlen || (seg.offset as u64) > ((tlen - flen) as u64) {
            return Err(WasmTrap::UndefinedElement);
        }
        let base = seg.offset as usize;
        let mut j: usize = 0;
        while j < flen
            invariant
                j <= flen,
                flen == seg.func_indices@.len(),
                tlen == table@.len(),
                base + flen <= tlen,
                has_table,
            decreases flen - j,
        {
            table[base + j] = Some(seg.func_indices[j]);
            j = j + 1;
        }
        ei = ei + 1;
    }

    // Apply data segments into linear memory.
    di = 0;
    while di < data_len
        invariant
            di <= data_len,
            data_len == module.data_segments@.len(),
            memory@.len() == (mem_pages as nat) * (WASM_PAGE_SIZE as nat),
        decreases data_len - di,
    {
        let seg = &module.data_segments[di];
        let mlen = memory.len();
        let ilen = seg.init.len();
        if !has_memory || ilen > mlen || (seg.offset as u64) > ((mlen - ilen) as u64) {
            return Err(WasmTrap::OutOfBoundsMemoryAccess);
        }
        let base = seg.offset as usize;
        let mut j: usize = 0;
        while j < ilen
            invariant
                j <= ilen,
                ilen == seg.init@.len(),
                mlen == memory@.len(),
                base + ilen <= mlen,
                memory@.len() == (mem_pages as nat) * (WASM_PAGE_SIZE as nat),
            decreases ilen - j,
        {
            memory[base + j] = seg.init[j];
            j = j + 1;
        }
        di = di + 1;
    }

    Ok(WasmInstance {
        has_memory,
        memory,
        mem_pages,
        max_pages,
        globals,
        global_types,
        global_mut,
        has_table,
        table,
    })
}

pub fn check_instance_wf(inst: &WasmInstance) -> (ok: bool)
    ensures
        ok ==> inst@.wf(),
{
    if !inst.has_memory && (inst.mem_pages != 0 || inst.max_pages != 0) {
        return false;
    }
    if inst.mem_pages > inst.max_pages
        || inst.max_pages > MAX_SPEC_PAGES
        || inst.mem_pages > MAX_SANDBOX_PAGES
    {
        return false;
    }
    let expected_bytes: usize = (inst.mem_pages as usize) * WASM_PAGE_SIZE;
    if inst.memory.len() != expected_bytes {
        return false;
    }
    if inst.globals.len() != inst.global_types.len()
        || inst.globals.len() != inst.global_mut.len()
    {
        return false;
    }
    let g_len = inst.globals.len();
    let mut i: usize = 0;
    while i < g_len
        invariant
            i <= g_len,
            g_len == inst.globals@.len(),
            g_len == inst.global_types@.len(),
            forall|k: int| 0 <= k < i as int ==>
                #[trigger] spec_val_has_type(inst.globals@[k], inst.global_types@[k]),
        decreases g_len - i,
    {
        if !val_has_type(inst.globals[i], inst.global_types[i]) {
            return false;
        }
        i = i + 1;
    }
    if !inst.has_table && inst.table.len() != 0 {
        return false;
    }
    true
}

// ---------------------------------------------------------------------------
// 4. Verified Wasm 1.0 Integer Arithmetic, Bitwise, Shift, Rotate, Bitcount
// ---------------------------------------------------------------------------

pub open spec fn spec_i32_to_u32(v: i32) -> u32 {
    0u32.wrapping_add_signed(v)
}

pub open spec fn spec_u32_to_i32(u: u32) -> i32 {
    0i32.wrapping_add_unsigned(u)
}

pub open spec fn spec_i64_to_u64(v: i64) -> u64 {
    0u64.wrapping_add_signed(v)
}

pub open spec fn spec_u64_to_i64(u: u64) -> i64 {
    0i64.wrapping_add_unsigned(u)
}

pub open spec fn spec_i32_unop(op: I32UnOp, v: i32) -> i32 {
    let u = 0u32.wrapping_add_signed(v);
    match op {
        I32UnOp::Clz => 0i32.wrapping_add_unsigned(u.leading_zeros()),
        I32UnOp::Ctz => 0i32.wrapping_add_unsigned(u.trailing_zeros()),
        I32UnOp::Popcnt => 0i32.wrapping_add_unsigned(u.count_ones()),
    }
}

pub fn eval_i32_unop(op: I32UnOp, v: i32) -> (r: i32)
    ensures
        r == spec_i32_unop(op, v),
{
    let u = 0u32.wrapping_add_signed(v);
    match op {
        I32UnOp::Clz => 0i32.wrapping_add_unsigned(u.leading_zeros()),
        I32UnOp::Ctz => 0i32.wrapping_add_unsigned(u.trailing_zeros()),
        I32UnOp::Popcnt => 0i32.wrapping_add_unsigned(u.count_ones()),
    }
}

pub open spec fn spec_i64_unop(op: I64UnOp, v: i64) -> i64 {
    let u = 0u64.wrapping_add_signed(v);
    match op {
        I64UnOp::Clz => (vstd::std_specs::bits::u64_leading_zeros(u) as u32 as u64) as i64,
        I64UnOp::Ctz => (u.trailing_zeros() as u64) as i64,
        I64UnOp::Popcnt => (u.count_ones() as u64) as i64,
    }
}

pub fn eval_i64_unop(op: I64UnOp, v: i64) -> (r: i64)
    ensures
        r == spec_i64_unop(op, v),
{
    let u = 0u64.wrapping_add_signed(v);
    match op {
        I64UnOp::Clz => {
            let lz = u.leading_zeros();
            proof {
                vstd::std_specs::bits::axiom_u64_leading_zeros(u);
            }
            (lz as u64) as i64
        },
        I64UnOp::Ctz => {
            let tz = u.trailing_zeros();
            (tz as u64) as i64
        },
        I64UnOp::Popcnt => {
            let pc = u.count_ones();
            (pc as u64) as i64
        },
    }
}

pub open spec fn spec_i32_rel(op: IntRelOp, a: i32, b: i32) -> i32 {
    let au = 0u32.wrapping_add_signed(a);
    let bu = 0u32.wrapping_add_signed(b);
    let cond = match op {
        IntRelOp::Eq => a == b,
        IntRelOp::Ne => a != b,
        IntRelOp::LtS => a < b,
        IntRelOp::LtU => au < bu,
        IntRelOp::GtS => a > b,
        IntRelOp::GtU => au > bu,
        IntRelOp::LeS => a <= b,
        IntRelOp::LeU => au <= bu,
        IntRelOp::GeS => a >= b,
        IntRelOp::GeU => au >= bu,
    };
    if cond { 1 } else { 0 }
}

pub fn eval_i32_rel(op: IntRelOp, a: i32, b: i32) -> (r: i32)
    ensures
        r == spec_i32_rel(op, a, b),
{
    let au = 0u32.wrapping_add_signed(a);
    let bu = 0u32.wrapping_add_signed(b);
    let cond = match op {
        IntRelOp::Eq => a == b,
        IntRelOp::Ne => a != b,
        IntRelOp::LtS => a < b,
        IntRelOp::LtU => au < bu,
        IntRelOp::GtS => a > b,
        IntRelOp::GtU => au > bu,
        IntRelOp::LeS => a <= b,
        IntRelOp::LeU => au <= bu,
        IntRelOp::GeS => a >= b,
        IntRelOp::GeU => au >= bu,
    };
    if cond { 1 } else { 0 }
}

pub open spec fn spec_i64_rel(op: IntRelOp, a: i64, b: i64) -> i32 {
    let au = 0u64.wrapping_add_signed(a);
    let bu = 0u64.wrapping_add_signed(b);
    let cond = match op {
        IntRelOp::Eq => a == b,
        IntRelOp::Ne => a != b,
        IntRelOp::LtS => a < b,
        IntRelOp::LtU => au < bu,
        IntRelOp::GtS => a > b,
        IntRelOp::GtU => au > bu,
        IntRelOp::LeS => a <= b,
        IntRelOp::LeU => au <= bu,
        IntRelOp::GeS => a >= b,
        IntRelOp::GeU => au >= bu,
    };
    if cond { 1 } else { 0 }
}

pub fn eval_i64_rel(op: IntRelOp, a: i64, b: i64) -> (r: i32)
    ensures
        r == spec_i64_rel(op, a, b),
{
    let au = 0u64.wrapping_add_signed(a);
    let bu = 0u64.wrapping_add_signed(b);
    let cond = match op {
        IntRelOp::Eq => a == b,
        IntRelOp::Ne => a != b,
        IntRelOp::LtS => a < b,
        IntRelOp::LtU => au < bu,
        IntRelOp::GtS => a > b,
        IntRelOp::GtU => au > bu,
        IntRelOp::LeS => a <= b,
        IntRelOp::LeU => au <= bu,
        IntRelOp::GeS => a >= b,
        IntRelOp::GeU => au >= bu,
    };
    if cond { 1 } else { 0 }
}

pub open spec fn spec_i32_binop(op: I32BinOp, a: i32, b: i32) -> Result<i32, WasmTrap> {
    let au = 0u32.wrapping_add_signed(a);
    let bu = 0u32.wrapping_add_signed(b);
    let sh = bu & 31u32;
    match op {
        I32BinOp::Add => Ok(a.wrapping_add(b)),
        I32BinOp::Sub => Ok(a.wrapping_sub(b)),
        I32BinOp::Mul => Ok(a.wrapping_mul(b)),
        I32BinOp::DivS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i32::MIN && b == -1 {
                Err(WasmTrap::IntegerOverflow)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(WasmTrap::IntegerOverflow),
                }
            }
        },
        I32BinOp::DivU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i32.wrapping_add_unsigned(au / bu))
            }
        },
        I32BinOp::RemS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i32::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(r) => Ok(r),
                    None => Ok(0),
                }
            }
        },
        I32BinOp::RemU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i32.wrapping_add_unsigned(au % bu))
            }
        },
        I32BinOp::And => Ok(a & b),
        I32BinOp::Or => Ok(a | b),
        I32BinOp::Xor => Ok(a ^ b),
        I32BinOp::Shl => Ok(a.wrapping_shl(sh)),
        I32BinOp::ShrS => Ok(a.wrapping_shr(sh)),
        I32BinOp::ShrU => Ok(0i32.wrapping_add_unsigned(au.wrapping_shr(sh))),
        I32BinOp::Rotl => Ok(0i32.wrapping_add_unsigned(au.rotate_left(sh))),
        I32BinOp::Rotr => Ok(0i32.wrapping_add_unsigned(au.rotate_right(sh))),
    }
}

pub fn eval_i32_binop(op: I32BinOp, a: i32, b: i32) -> (r: Result<i32, WasmTrap>)
    ensures
        r == spec_i32_binop(op, a, b),
{
    let au = 0u32.wrapping_add_signed(a);
    let bu = 0u32.wrapping_add_signed(b);
    let sh = bu & 31u32;
    match op {
        I32BinOp::Add => Ok(a.wrapping_add(b)),
        I32BinOp::Sub => Ok(a.wrapping_sub(b)),
        I32BinOp::Mul => Ok(a.wrapping_mul(b)),
        I32BinOp::DivS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i32::MIN && b == -1 {
                Err(WasmTrap::IntegerOverflow)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(WasmTrap::IntegerOverflow),
                }
            }
        },
        I32BinOp::DivU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i32.wrapping_add_unsigned(au / bu))
            }
        },
        I32BinOp::RemS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i32::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(r) => Ok(r),
                    None => Ok(0),
                }
            }
        },
        I32BinOp::RemU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i32.wrapping_add_unsigned(au % bu))
            }
        },
        I32BinOp::And => Ok(a & b),
        I32BinOp::Or => Ok(a | b),
        I32BinOp::Xor => Ok(a ^ b),
        I32BinOp::Shl => Ok(a.wrapping_shl(sh)),
        I32BinOp::ShrS => Ok(a.wrapping_shr(sh)),
        I32BinOp::ShrU => Ok(0i32.wrapping_add_unsigned(au.wrapping_shr(sh))),
        I32BinOp::Rotl => Ok(0i32.wrapping_add_unsigned(au.rotate_left(sh))),
        I32BinOp::Rotr => Ok(0i32.wrapping_add_unsigned(au.rotate_right(sh))),
    }
}

pub open spec fn spec_i64_binop(op: I64BinOp, a: i64, b: i64) -> Result<i64, WasmTrap> {
    let au = 0u64.wrapping_add_signed(a);
    let bu = 0u64.wrapping_add_signed(b);
    let sh: u32 = ((bu % 64u64) as u32);
    match op {
        I64BinOp::Add => Ok(a.wrapping_add(b)),
        I64BinOp::Sub => Ok(a.wrapping_sub(b)),
        I64BinOp::Mul => Ok(a.wrapping_mul(b)),
        I64BinOp::DivS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i64::MIN && b == -1 {
                Err(WasmTrap::IntegerOverflow)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(WasmTrap::IntegerOverflow),
                }
            }
        },
        I64BinOp::DivU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i64.wrapping_add_unsigned(au / bu))
            }
        },
        I64BinOp::RemS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(r) => Ok(r),
                    None => Ok(0),
                }
            }
        },
        I64BinOp::RemU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i64.wrapping_add_unsigned(au % bu))
            }
        },
        I64BinOp::And => Ok(a & b),
        I64BinOp::Or => Ok(a | b),
        I64BinOp::Xor => Ok(a ^ b),
        I64BinOp::Shl => Ok(a.wrapping_shl(sh)),
        I64BinOp::ShrS => Ok(a.wrapping_shr(sh)),
        I64BinOp::ShrU => Ok(0i64.wrapping_add_unsigned(au.wrapping_shr(sh))),
        I64BinOp::Rotl => Ok(0i64.wrapping_add_unsigned(au.rotate_left(sh))),
        I64BinOp::Rotr => Ok(0i64.wrapping_add_unsigned(au.rotate_right(sh))),
    }
}

pub fn eval_i64_binop(op: I64BinOp, a: i64, b: i64) -> (r: Result<i64, WasmTrap>)
    ensures
        r == spec_i64_binop(op, a, b),
{
    let au = 0u64.wrapping_add_signed(a);
    let bu = 0u64.wrapping_add_signed(b);
    let sh: u32 = (bu % 64u64) as u32;
    match op {
        I64BinOp::Add => Ok(a.wrapping_add(b)),
        I64BinOp::Sub => Ok(a.wrapping_sub(b)),
        I64BinOp::Mul => Ok(a.wrapping_mul(b)),
        I64BinOp::DivS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i64::MIN && b == -1 {
                Err(WasmTrap::IntegerOverflow)
            } else {
                match a.checked_div(b) {
                    Some(q) => Ok(q),
                    None => Err(WasmTrap::IntegerOverflow),
                }
            }
        },
        I64BinOp::DivU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i64.wrapping_add_unsigned(au / bu))
            }
        },
        I64BinOp::RemS => {
            if b == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else if a == i64::MIN && b == -1 {
                Ok(0)
            } else {
                match a.checked_rem(b) {
                    Some(r) => Ok(r),
                    None => Ok(0),
                }
            }
        },
        I64BinOp::RemU => {
            if bu == 0 {
                Err(WasmTrap::IntegerDivideByZero)
            } else {
                Ok(0i64.wrapping_add_unsigned(au % bu))
            }
        },
        I64BinOp::And => Ok(a & b),
        I64BinOp::Or => Ok(a | b),
        I64BinOp::Xor => Ok(a ^ b),
        I64BinOp::Shl => Ok(a.wrapping_shl(sh)),
        I64BinOp::ShrS => Ok(a.wrapping_shr(sh)),
        I64BinOp::ShrU => Ok(0i64.wrapping_add_unsigned(au.wrapping_shr(sh))),
        I64BinOp::Rotl => Ok(0i64.wrapping_add_unsigned(au.rotate_left(sh))),
        I64BinOp::Rotr => Ok(0i64.wrapping_add_unsigned(au.rotate_right(sh))),
    }
}

/// Machine-checked proof that Wasm integer division/remainder traps deterministically
/// on division by zero and signed `MIN / -1`, while `MIN % -1` evaluates to `0` without trapping.
pub proof fn lemma_div_rem_trap_characterization(a32: i32, a64: i64)
    ensures
        spec_i32_binop(I32BinOp::DivS, a32, 0i32) == Err::<i32, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i32_binop(I32BinOp::DivU, a32, 0i32) == Err::<i32, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i32_binop(I32BinOp::RemS, a32, 0i32) == Err::<i32, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i32_binop(I32BinOp::RemU, a32, 0i32) == Err::<i32, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i32_binop(I32BinOp::DivS, i32::MIN, -1i32) == Err::<i32, WasmTrap>(WasmTrap::IntegerOverflow),
        spec_i32_binop(I32BinOp::RemS, i32::MIN, -1i32) == Ok::<i32, WasmTrap>(0i32),
        spec_i64_binop(I64BinOp::DivS, a64, 0i64) == Err::<i64, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i64_binop(I64BinOp::DivU, a64, 0i64) == Err::<i64, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i64_binop(I64BinOp::RemS, a64, 0i64) == Err::<i64, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i64_binop(I64BinOp::RemU, a64, 0i64) == Err::<i64, WasmTrap>(WasmTrap::IntegerDivideByZero),
        spec_i64_binop(I64BinOp::DivS, i64::MIN, -1i64) == Err::<i64, WasmTrap>(WasmTrap::IntegerOverflow),
        spec_i64_binop(I64BinOp::RemS, i64::MIN, -1i64) == Ok::<i64, WasmTrap>(0i64),
{
}

// ---------------------------------------------------------------------------
// 5. Verified Sandboxed Linear Memory (`load*`, `store*`, `size`, `grow`)
// ---------------------------------------------------------------------------

/// Unbounded mathematical effective address per WebAssembly 1.0 §4.4.7:
/// `ea = u32(addr) + offset` (never modular 32-bit wrap!).
pub open spec fn spec_effective_addr(addr: i32, offset: u32) -> nat {
    (0u32.wrapping_add_signed(addr) as nat) + (offset as nat)
}

pub fn effective_addr(addr: i32, offset: u32) -> (ea: u64)
    ensures
        ea as nat == spec_effective_addr(addr, offset),
        ea <= 0x1_FFFF_FFFEu64,
{
    (0u32.wrapping_add_signed(addr) as u64) + (offset as u64)
}

pub open spec fn spec_read_u16_le(mem: Seq<u8>, ea: int) -> u16 {
    (mem[ea] as u16) | ((mem[ea + 1] as u16).wrapping_shl(8))
}

pub open spec fn spec_read_u32_le_mem(mem: Seq<u8>, ea: int) -> u32 {
    (mem[ea] as u32)
        | ((mem[ea + 1] as u32).wrapping_shl(8))
        | ((mem[ea + 2] as u32).wrapping_shl(16))
        | ((mem[ea + 3] as u32).wrapping_shl(24))
}

pub open spec fn spec_read_u64_le_mem(mem: Seq<u8>, ea: int) -> u64 {
    (mem[ea] as u64)
        | ((mem[ea + 1] as u64).wrapping_shl(8))
        | ((mem[ea + 2] as u64).wrapping_shl(16))
        | ((mem[ea + 3] as u64).wrapping_shl(24))
        | ((mem[ea + 4] as u64).wrapping_shl(32))
        | ((mem[ea + 5] as u64).wrapping_shl(40))
        | ((mem[ea + 6] as u64).wrapping_shl(48))
        | ((mem[ea + 7] as u64).wrapping_shl(56))
}

pub open spec fn spec_mem_load(
    inst: SpecWasmInstance,
    kind: LoadKind,
    offset: u32,
    addr: i32,
) -> Result<WasmVal, WasmTrap> {
    let ea = spec_effective_addr(addr, offset);
    let w = spec_load_width(kind);
    if !inst.has_memory || ea + w > inst.memory.len() {
        Err(WasmTrap::OutOfBoundsMemoryAccess)
    } else {
        let base = ea as int;
        let v = match kind {
            LoadKind::I32Load => WasmVal::I32(0i32.wrapping_add_unsigned(spec_read_u32_le_mem(inst.memory, base))),
            LoadKind::I64Load => WasmVal::I64(0i64.wrapping_add_unsigned(spec_read_u64_le_mem(inst.memory, base))),
            LoadKind::F32Load => WasmVal::F32Bits(spec_read_u32_le_mem(inst.memory, base)),
            LoadKind::F64Load => WasmVal::F64Bits(spec_read_u64_le_mem(inst.memory, base)),
            LoadKind::I32Load8S => WasmVal::I32((0i8.wrapping_add_unsigned(inst.memory[base])) as i32),
            LoadKind::I32Load8U => WasmVal::I32((inst.memory[base] as u32) as i32),
            LoadKind::I32Load16S => WasmVal::I32((0i16.wrapping_add_unsigned(spec_read_u16_le(inst.memory, base))) as i32),
            LoadKind::I32Load16U => WasmVal::I32((spec_read_u16_le(inst.memory, base) as u32) as i32),
            LoadKind::I64Load8S => WasmVal::I64((0i8.wrapping_add_unsigned(inst.memory[base])) as i64),
            LoadKind::I64Load8U => WasmVal::I64((inst.memory[base] as u64) as i64),
            LoadKind::I64Load16S => WasmVal::I64((0i16.wrapping_add_unsigned(spec_read_u16_le(inst.memory, base))) as i64),
            LoadKind::I64Load16U => WasmVal::I64((spec_read_u16_le(inst.memory, base) as u64) as i64),
            LoadKind::I64Load32S => WasmVal::I64((0i32.wrapping_add_unsigned(spec_read_u32_le_mem(inst.memory, base))) as i64),
            LoadKind::I64Load32U => WasmVal::I64((spec_read_u32_le_mem(inst.memory, base) as u64) as i64),
        };
        Ok(v)
    }
}

#[verifier::spinoff_prover]
pub fn exec_mem_load(
    inst: &WasmInstance,
    kind: LoadKind,
    offset: u32,
    addr: i32,
) -> (r: Result<WasmVal, WasmTrap>)
    ensures
        r == spec_mem_load(inst@, kind, offset, addr),
{
    let ea = effective_addr(addr, offset);
    let w = load_width(kind);
    if !inst.has_memory || ea + (w as u64) > (inst.memory.len() as u64) {
        return Err(WasmTrap::OutOfBoundsMemoryAccess);
    }
    let base: usize = ea as usize;
    let mem = &inst.memory;
    let v = match kind {
        LoadKind::I32Load => {
            let u = (mem[base] as u32)
                | ((mem[base + 1] as u32).wrapping_shl(8))
                | ((mem[base + 2] as u32).wrapping_shl(16))
                | ((mem[base + 3] as u32).wrapping_shl(24));
            WasmVal::I32(0i32.wrapping_add_unsigned(u))
        },
        LoadKind::I64Load => {
            let u = (mem[base] as u64)
                | ((mem[base + 1] as u64).wrapping_shl(8))
                | ((mem[base + 2] as u64).wrapping_shl(16))
                | ((mem[base + 3] as u64).wrapping_shl(24))
                | ((mem[base + 4] as u64).wrapping_shl(32))
                | ((mem[base + 5] as u64).wrapping_shl(40))
                | ((mem[base + 6] as u64).wrapping_shl(48))
                | ((mem[base + 7] as u64).wrapping_shl(56));
            WasmVal::I64(0i64.wrapping_add_unsigned(u))
        },
        LoadKind::F32Load => {
            let u = (mem[base] as u32)
                | ((mem[base + 1] as u32).wrapping_shl(8))
                | ((mem[base + 2] as u32).wrapping_shl(16))
                | ((mem[base + 3] as u32).wrapping_shl(24));
            WasmVal::F32Bits(u)
        },
        LoadKind::F64Load => {
            let u = (mem[base] as u64)
                | ((mem[base + 1] as u64).wrapping_shl(8))
                | ((mem[base + 2] as u64).wrapping_shl(16))
                | ((mem[base + 3] as u64).wrapping_shl(24))
                | ((mem[base + 4] as u64).wrapping_shl(32))
                | ((mem[base + 5] as u64).wrapping_shl(40))
                | ((mem[base + 6] as u64).wrapping_shl(48))
                | ((mem[base + 7] as u64).wrapping_shl(56));
            WasmVal::F64Bits(u)
        },
        LoadKind::I32Load8S => WasmVal::I32((0i8.wrapping_add_unsigned(mem[base])) as i32),
        LoadKind::I32Load8U => WasmVal::I32((mem[base] as u32) as i32),
        LoadKind::I32Load16S => {
            let u = (mem[base] as u16) | ((mem[base + 1] as u16).wrapping_shl(8));
            WasmVal::I32((0i16.wrapping_add_unsigned(u)) as i32)
        },
        LoadKind::I32Load16U => {
            let u = (mem[base] as u16) | ((mem[base + 1] as u16).wrapping_shl(8));
            WasmVal::I32((u as u32) as i32)
        },
        LoadKind::I64Load8S => WasmVal::I64((0i8.wrapping_add_unsigned(mem[base])) as i64),
        LoadKind::I64Load8U => WasmVal::I64((mem[base] as u64) as i64),
        LoadKind::I64Load16S => {
            let u = (mem[base] as u16) | ((mem[base + 1] as u16).wrapping_shl(8));
            WasmVal::I64((0i16.wrapping_add_unsigned(u)) as i64)
        },
        LoadKind::I64Load16U => {
            let u = (mem[base] as u16) | ((mem[base + 1] as u16).wrapping_shl(8));
            WasmVal::I64((u as u64) as i64)
        },
        LoadKind::I64Load32S => {
            let u = (mem[base] as u32)
                | ((mem[base + 1] as u32).wrapping_shl(8))
                | ((mem[base + 2] as u32).wrapping_shl(16))
                | ((mem[base + 3] as u32).wrapping_shl(24));
            WasmVal::I64((0i32.wrapping_add_unsigned(u)) as i64)
        },
        LoadKind::I64Load32U => {
            let u = (mem[base] as u32)
                | ((mem[base + 1] as u32).wrapping_shl(8))
                | ((mem[base + 2] as u32).wrapping_shl(16))
                | ((mem[base + 3] as u32).wrapping_shl(24));
            WasmVal::I64((u as u64) as i64)
        },
    };
    Ok(v)
}

pub open spec fn spec_write_u16_le(mem: Seq<u8>, ea: int, v: u16) -> Seq<u8> {
    mem.update(ea, (v % 0x100u16) as u8)
        .update(ea + 1, (v.wrapping_shr(8) % 0x100u16) as u8)
}

pub open spec fn spec_write_u32_le(mem: Seq<u8>, ea: int, v: u32) -> Seq<u8> {
    mem.update(ea, (v % 0x100u32) as u8)
        .update(ea + 1, (v.wrapping_shr(8) % 0x100u32) as u8)
        .update(ea + 2, (v.wrapping_shr(16) % 0x100u32) as u8)
        .update(ea + 3, (v.wrapping_shr(24) % 0x100u32) as u8)
}

pub open spec fn spec_write_u64_le(mem: Seq<u8>, ea: int, v: u64) -> Seq<u8> {
    mem.update(ea, (v % 0x100u64) as u8)
        .update(ea + 1, (v.wrapping_shr(8) % 0x100u64) as u8)
        .update(ea + 2, (v.wrapping_shr(16) % 0x100u64) as u8)
        .update(ea + 3, (v.wrapping_shr(24) % 0x100u64) as u8)
        .update(ea + 4, (v.wrapping_shr(32) % 0x100u64) as u8)
        .update(ea + 5, (v.wrapping_shr(40) % 0x100u64) as u8)
        .update(ea + 6, (v.wrapping_shr(48) % 0x100u64) as u8)
        .update(ea + 7, (v.wrapping_shr(56) % 0x100u64) as u8)
}

pub open spec fn spec_mem_store(
    inst: SpecWasmInstance,
    kind: StoreKind,
    offset: u32,
    addr: i32,
    val: WasmVal,
) -> Result<SpecWasmInstance, WasmTrap> {
    let ea = spec_effective_addr(addr, offset);
    let w = spec_store_width(kind);
    if !inst.has_memory || ea + w > inst.memory.len() {
        Err(WasmTrap::OutOfBoundsMemoryAccess)
    } else {
        let base = ea as int;
        let new_mem_res: Result<Seq<u8>, WasmTrap> = match (kind, val) {
            (StoreKind::I32Store, WasmVal::I32(v)) => Ok(spec_write_u32_le(inst.memory, base, 0u32.wrapping_add_signed(v))),
            (StoreKind::I32Store8, WasmVal::I32(v)) => Ok(inst.memory.update(base, (0u32.wrapping_add_signed(v) % 0x100u32) as u8)),
            (StoreKind::I32Store16, WasmVal::I32(v)) => Ok(spec_write_u16_le(inst.memory, base, (0u32.wrapping_add_signed(v) % 0x1_0000u32) as u16)),
            (StoreKind::I64Store, WasmVal::I64(v)) => Ok(spec_write_u64_le(inst.memory, base, 0u64.wrapping_add_signed(v))),
            (StoreKind::I64Store8, WasmVal::I64(v)) => Ok(inst.memory.update(base, (0u64.wrapping_add_signed(v) % 0x100u64) as u8)),
            (StoreKind::I64Store16, WasmVal::I64(v)) => Ok(spec_write_u16_le(inst.memory, base, (0u64.wrapping_add_signed(v) % 0x1_0000u64) as u16)),
            (StoreKind::I64Store32, WasmVal::I64(v)) => Ok(spec_write_u32_le(inst.memory, base, (0u64.wrapping_add_signed(v) % 0x1_0000_0000u64) as u32)),
            (StoreKind::F32Store, WasmVal::F32Bits(v)) => Ok(spec_write_u32_le(inst.memory, base, v)),
            (StoreKind::F64Store, WasmVal::F64Bits(v)) => Ok(spec_write_u64_le(inst.memory, base, v)),
            _ => Err(WasmTrap::TypeMismatch),
        };
        match new_mem_res {
            Ok(new_mem) => Ok(SpecWasmInstance { memory: new_mem, ..inst }),
            Err(t) => Err(t),
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_mem_store(
    inst: &mut WasmInstance,
    kind: StoreKind,
    offset: u32,
    addr: i32,
    val: WasmVal,
) -> (r: Result<(), WasmTrap>)
    requires
        old(inst)@.wf(),
    ensures
        match (r, spec_mem_store(old(inst)@, kind, offset, addr, val)) {
            (Ok(()), Ok(next_inst)) => final(inst)@ == next_inst && final(inst)@.wf(),
            (Err(t1), Err(t2)) => t1 == t2 && final(inst)@ == old(inst)@ && final(inst)@.wf(),
            _ => false,
        },
{
    let ea = effective_addr(addr, offset);
    let w = store_width(kind);
    if !inst.has_memory || ea + (w as u64) > (inst.memory.len() as u64) {
        return Err(WasmTrap::OutOfBoundsMemoryAccess);
    }
    let base: usize = ea as usize;
    match (kind, val) {
        (StoreKind::I32Store, WasmVal::I32(v)) => {
            let u = 0u32.wrapping_add_signed(v);
            inst.memory[base] = (u % 0x100u32) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u32) as u8;
            inst.memory[base + 2] = (u.wrapping_shr(16) % 0x100u32) as u8;
            inst.memory[base + 3] = (u.wrapping_shr(24) % 0x100u32) as u8;
        },
        (StoreKind::I32Store8, WasmVal::I32(v)) => {
            let u = 0u32.wrapping_add_signed(v);
            inst.memory[base] = (u % 0x100u32) as u8;
        },
        (StoreKind::I32Store16, WasmVal::I32(v)) => {
            let u = (0u32.wrapping_add_signed(v) % 0x1_0000u32) as u16;
            inst.memory[base] = (u % 0x100u16) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u16) as u8;
        },
        (StoreKind::I64Store, WasmVal::I64(v)) => {
            let u = 0u64.wrapping_add_signed(v);
            inst.memory[base] = (u % 0x100u64) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u64) as u8;
            inst.memory[base + 2] = (u.wrapping_shr(16) % 0x100u64) as u8;
            inst.memory[base + 3] = (u.wrapping_shr(24) % 0x100u64) as u8;
            inst.memory[base + 4] = (u.wrapping_shr(32) % 0x100u64) as u8;
            inst.memory[base + 5] = (u.wrapping_shr(40) % 0x100u64) as u8;
            inst.memory[base + 6] = (u.wrapping_shr(48) % 0x100u64) as u8;
            inst.memory[base + 7] = (u.wrapping_shr(56) % 0x100u64) as u8;
        },
        (StoreKind::I64Store8, WasmVal::I64(v)) => {
            let u = 0u64.wrapping_add_signed(v);
            inst.memory[base] = (u % 0x100u64) as u8;
        },
        (StoreKind::I64Store16, WasmVal::I64(v)) => {
            let u = (0u64.wrapping_add_signed(v) % 0x1_0000u64) as u16;
            inst.memory[base] = (u % 0x100u16) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u16) as u8;
        },
        (StoreKind::I64Store32, WasmVal::I64(v)) => {
            let u = (0u64.wrapping_add_signed(v) % 0x1_0000_0000u64) as u32;
            inst.memory[base] = (u % 0x100u32) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u32) as u8;
            inst.memory[base + 2] = (u.wrapping_shr(16) % 0x100u32) as u8;
            inst.memory[base + 3] = (u.wrapping_shr(24) % 0x100u32) as u8;
        },
        (StoreKind::F32Store, WasmVal::F32Bits(u)) => {
            inst.memory[base] = (u % 0x100u32) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u32) as u8;
            inst.memory[base + 2] = (u.wrapping_shr(16) % 0x100u32) as u8;
            inst.memory[base + 3] = (u.wrapping_shr(24) % 0x100u32) as u8;
        },
        (StoreKind::F64Store, WasmVal::F64Bits(u)) => {
            inst.memory[base] = (u % 0x100u64) as u8;
            inst.memory[base + 1] = (u.wrapping_shr(8) % 0x100u64) as u8;
            inst.memory[base + 2] = (u.wrapping_shr(16) % 0x100u64) as u8;
            inst.memory[base + 3] = (u.wrapping_shr(24) % 0x100u64) as u8;
            inst.memory[base + 4] = (u.wrapping_shr(32) % 0x100u64) as u8;
            inst.memory[base + 5] = (u.wrapping_shr(40) % 0x100u64) as u8;
            inst.memory[base + 6] = (u.wrapping_shr(48) % 0x100u64) as u8;
            inst.memory[base + 7] = (u.wrapping_shr(56) % 0x100u64) as u8;
        },
        _ => {
            return Err(WasmTrap::TypeMismatch);
        },
    }
    proof {
        assert(inst@ == spec_mem_store(old(inst)@, kind, offset, addr, val).unwrap());
    }
    Ok(())
}

pub open spec fn spec_memory_grow(
    inst: SpecWasmInstance,
    delta: i32,
) -> Result<(SpecWasmInstance, i32), WasmTrap> {
    if !inst.has_memory {
        Err(WasmTrap::OutOfBoundsMemoryAccess)
    } else {
        let delta_u32 = 0u32.wrapping_add_signed(delta);
        let old_pages = inst.mem_pages;
        if (old_pages as nat) + (delta_u32 as nat) <= (inst.max_pages as nat)
            && (old_pages as nat) + (delta_u32 as nat) <= (MAX_SANDBOX_PAGES as nat)
        {
            let new_pages = (old_pages + delta_u32) as u32;
            let extra_bytes = (delta_u32 as nat) * (WASM_PAGE_SIZE as nat);
            let new_mem = inst.memory + Seq::new(extra_bytes, |_i: int| 0u8);
            Ok((
                SpecWasmInstance {
                    memory: new_mem,
                    mem_pages: new_pages,
                    ..inst
                },
                0i32.wrapping_add_unsigned(old_pages),
            ))
        } else {
            Ok((inst, -1i32))
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_memory_grow(
    inst: &mut WasmInstance,
    delta: i32,
) -> (r: Result<i32, WasmTrap>)
    requires
        old(inst)@.wf(),
    ensures
        match (r, spec_memory_grow(old(inst)@, delta)) {
            (Ok(res), Ok((next_inst, sres))) =>
                res == sres && final(inst)@ == next_inst && final(inst)@.wf(),
            (Err(t1), Err(t2)) =>
                t1 == t2 && final(inst)@ == old(inst)@ && final(inst)@.wf(),
            _ => false,
        },
{
    if !inst.has_memory {
        return Err(WasmTrap::OutOfBoundsMemoryAccess);
    }
    let delta_u32 = 0u32.wrapping_add_signed(delta);
    let old_pages = inst.mem_pages;
    if (old_pages as u64) + (delta_u32 as u64) <= (inst.max_pages as u64)
        && (old_pages as u64) + (delta_u32 as u64) <= (MAX_SANDBOX_PAGES as u64)
    {
        let new_pages: u32 = old_pages + delta_u32;
        let new_byte_len: usize = (new_pages as usize) * WASM_PAGE_SIZE;
        let ghost pre_mem = inst.memory@;
        inst.memory.resize(new_byte_len, 0u8);
        inst.mem_pages = new_pages;
        proof {
            let extra_bytes: nat = (delta_u32 as nat) * (WASM_PAGE_SIZE as nat);
            assert(pre_mem.len() + extra_bytes == new_byte_len as nat) by (nonlinear_arith)
                requires
                    pre_mem.len() == (old_pages as nat) * (WASM_PAGE_SIZE as nat),
                    extra_bytes == (delta_u32 as nat) * (WASM_PAGE_SIZE as nat),
                    new_pages as nat == (old_pages as nat) + (delta_u32 as nat),
                    new_byte_len as nat == (new_pages as nat) * (WASM_PAGE_SIZE as nat);
            let target_mem = pre_mem + Seq::new(extra_bytes, |_i: int| 0u8);
            assert(inst.memory@ =~= target_mem);
        }
        Ok(0i32.wrapping_add_unsigned(old_pages))
    } else {
        Ok(-1i32)
    }
}

// ---------------------------------------------------------------------------
// 6. Frame Stack & Structured Branch Unwinding Helpers (`exec == spec`)
// ---------------------------------------------------------------------------

pub open spec fn spec_pop_val(stack: Seq<WasmVal>) -> Result<(Seq<WasmVal>, WasmVal), WasmTrap> {
    if stack.len() == 0 {
        Err(WasmTrap::StackUnderflow)
    } else {
        Ok((stack.drop_last(), stack.last()))
    }
}

pub open spec fn spec_pop_i32(stack: Seq<WasmVal>) -> Result<(Seq<WasmVal>, i32), WasmTrap> {
    match spec_pop_val(stack) {
        Err(t) => Err(t),
        Ok((rest, WasmVal::I32(v))) => Ok((rest, v)),
        Ok(_) => Err(WasmTrap::TypeMismatch),
    }
}

pub open spec fn spec_pop_i64(stack: Seq<WasmVal>) -> Result<(Seq<WasmVal>, i64), WasmTrap> {
    match spec_pop_val(stack) {
        Err(t) => Err(t),
        Ok((rest, WasmVal::I64(v))) => Ok((rest, v)),
        Ok(_) => Err(WasmTrap::TypeMismatch),
    }
}

pub fn pop_val_vec(stack: &mut Vec<WasmVal>) -> (r: Result<WasmVal, WasmTrap>)
    ensures
        match (r, spec_pop_val(old(stack)@)) {
            (Ok(v), Ok((s_rest, sv))) => v == sv && final(stack)@ == s_rest,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    match stack.pop() {
        Some(v) => Ok(v),
        None => Err(WasmTrap::StackUnderflow),
    }
}

pub fn pop_i32_vec(stack: &mut Vec<WasmVal>) -> (r: Result<i32, WasmTrap>)
    ensures
        match (r, spec_pop_i32(old(stack)@)) {
            (Ok(v), Ok((s_rest, sv))) => v == sv && final(stack)@ == s_rest,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    let v = pop_val_vec(stack)?;
    match v {
        WasmVal::I32(x) => Ok(x),
        _ => Err(WasmTrap::TypeMismatch),
    }
}

pub fn pop_i64_vec(stack: &mut Vec<WasmVal>) -> (r: Result<i64, WasmTrap>)
    ensures
        match (r, spec_pop_i64(old(stack)@)) {
            (Ok(v), Ok((s_rest, sv))) => v == sv && final(stack)@ == s_rest,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    let v = pop_val_vec(stack)?;
    match v {
        WasmVal::I64(x) => Ok(x),
        _ => Err(WasmTrap::TypeMismatch),
    }
}

/// Extract the top `arity` values from `stack` in bottom-to-top order.
pub open spec fn spec_extract_top_arity(
    stack: Seq<WasmVal>,
    arity: usize,
) -> Result<Seq<WasmVal>, WasmTrap> {
    if stack.len() < arity as nat {
        Err(WasmTrap::StackUnderflow)
    } else {
        let start = stack.len() - (arity as int);
        Ok(stack.subrange(start, stack.len() as int))
    }
}

pub fn extract_top_arity(stack: &[WasmVal], arity: usize) -> (r: Result<Vec<WasmVal>, WasmTrap>)
    ensures
        match (r, spec_extract_top_arity(stack@, arity)) {
            (Ok(vals), Ok(svals)) => vals@ == svals,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    let slen = stack.len();
    if slen < arity {
        return Err(WasmTrap::StackUnderflow);
    }
    let start = slen - arity;
    let mut out: Vec<WasmVal> = Vec::with_capacity(arity);
    let mut i: usize = 0;
    while i < arity
        invariant
            i <= arity,
            slen == stack@.len(),
            start + arity == slen,
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> out@[k] == stack@[start as int + k],
        decreases arity - i,
    {
        out.push(stack[start + i]);
        i = i + 1;
    }
    proof {
        assert(out@ =~= stack@.subrange(start as int, stack@.len() as int));
    }
    Ok(out)
}

/// Unwind `stack` to `base_height` while preserving the top `arity` values.
pub open spec fn spec_unwind_stack_with_arity(
    stack: Seq<WasmVal>,
    base_height: usize,
    arity: usize,
) -> Result<Seq<WasmVal>, WasmTrap> {
    if stack.len() < (base_height as nat) + (arity as nat) {
        Err(WasmTrap::StackUnderflow)
    } else {
        let start = stack.len() - (arity as int);
        let kept = stack.subrange(start, stack.len() as int);
        Ok(stack.subrange(0, base_height as int) + kept)
    }
}

pub fn unwind_stack_with_arity(
    stack: &mut Vec<WasmVal>,
    base_height: usize,
    arity: usize,
) -> (r: Result<(), WasmTrap>)
    ensures
        match (r, spec_unwind_stack_with_arity(old(stack)@, base_height, arity)) {
            (Ok(()), Ok(s_new)) => final(stack)@ == s_new,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    if arity > stack.len() || base_height > stack.len() - arity {
        return Err(WasmTrap::StackUnderflow);
    }
    let mut kept = extract_top_arity(stack, arity)?;
    stack.truncate(base_height);
    stack.append(&mut kept);
    Ok(())
}

/// Return from the current frame (`callee`), either completing execution (if `caller_frames` is empty)
/// or pushing `return_arity` results onto the caller frame's stack.
pub open spec fn spec_return_from_frame(
    caller_frames: Seq<SpecCallFrame>,
    callee: SpecCallFrame,
) -> (SpecWasmExecState, SpecStepOutcome) {
    match spec_extract_top_arity(callee.stack, callee.return_arity) {
        Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
        Ok(ret_vals) => {
            if caller_frames.len() == 0 {
                (
                    SpecWasmExecState { frames: Seq::empty() },
                    SpecStepOutcome::Done(ret_vals),
                )
            } else {
                let caller = caller_frames.last();
                let updated_caller = SpecCallFrame {
                    stack: caller.stack + ret_vals,
                    ..caller
                };
                (
                    SpecWasmExecState {
                        frames: caller_frames.drop_last().push(updated_caller),
                    },
                    SpecStepOutcome::Continue,
                )
            }
        },
    }
}

pub fn exec_return_from_frame(
    state: &mut WasmExecState,
    callee: CallFrame,
) -> (out: StepOutcome)
    ensures
        ({
            let (s_next, s_out) = spec_return_from_frame(old(state)@.frames, callee@);
            final(state)@ == s_next && out@ == s_out
        }),
{
    let ghost pre_frames = state@.frames;
    match extract_top_arity(&callee.stack, callee.return_arity) {
        Err(t) => StepOutcome::Trap(t),
        Ok(mut ret_vals) => {
            if state.frames.len() == 0 {
                proof {
                    assert(state@.frames =~= Seq::<SpecCallFrame>::empty());
                }
                StepOutcome::Done(ret_vals)
            } else {
                let mut caller = state.frames.pop().unwrap();
                let ghost popped_frames = state@.frames;
                proof {
                    assert(caller@ == pre_frames.last());
                    assert(popped_frames =~= pre_frames.drop_last());
                }
                caller.stack.append(&mut ret_vals);
                let ghost updated_caller_spec = caller@;
                state.frames.push(caller);
                proof {
                    assert(state@.frames =~= pre_frames.drop_last().push(updated_caller_spec));
                }
                StepOutcome::Continue
            }
        },
    }
}

/// Branch to label depth `depth` in `frame`:
/// - `depth < frame.labels.len()`: pops `depth + 1` structured labels, unwinds `frame.stack`
///   to `label.stack_height` keeping `label.arity` values, and jumps to `label.target_pc`.
/// - `depth == frame.labels.len()`: branches to the implicit function-body label (returns!).
/// - `depth > frame.labels.len()`: traps with `InvalidLabel`.
pub open spec fn spec_branch_in_frame(
    caller_frames: Seq<SpecCallFrame>,
    frame: SpecCallFrame,
    depth: u32,
) -> (SpecWasmExecState, SpecStepOutcome) {
    if (depth as nat) > frame.labels.len() {
        (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidLabel))
    } else if (depth as nat) == frame.labels.len() {
        spec_return_from_frame(caller_frames, frame)
    } else {
        let target_idx = frame.labels.len() - 1 - (depth as int);
        let lbl = frame.labels[target_idx];
        match spec_unwind_stack_with_arity(frame.stack, lbl.stack_height, lbl.arity) {
            Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
            Ok(new_stack) => {
                let new_labels = frame.labels.subrange(0, target_idx);
                let new_frame = SpecCallFrame {
                    pc: lbl.target_pc,
                    stack: new_stack,
                    labels: new_labels,
                    ..frame
                };
                (
                    SpecWasmExecState { frames: caller_frames.push(new_frame) },
                    SpecStepOutcome::Continue,
                )
            },
        }
    }
}

pub fn exec_branch_in_frame(
    state: &mut WasmExecState,
    mut frame: CallFrame,
    depth: u32,
) -> (out: StepOutcome)
    ensures
        ({
            let (s_next, s_out) = spec_branch_in_frame(old(state)@.frames, frame@, depth);
            final(state)@ == s_next && out@ == s_out
        }),
{
    let ghost pre_frames = state@.frames;
    let ghost init_frame = frame@;
    if (depth as u64) > (frame.labels.len() as u64) {
        return StepOutcome::Trap(WasmTrap::InvalidLabel);
    }
    if (depth as u64) == (frame.labels.len() as u64) {
        return exec_return_from_frame(state, frame);
    }
    let d: usize = depth as usize;
    let target_idx: usize = frame.labels.len() - 1 - d;
    let lbl = frame.labels[target_idx];
    match unwind_stack_with_arity(&mut frame.stack, lbl.stack_height, lbl.arity) {
        Err(t) => StepOutcome::Trap(t),
        Ok(()) => {
            frame.labels.truncate(target_idx);
            frame.pc = lbl.target_pc;
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(nf == SpecCallFrame {
                    pc: lbl.target_pc,
                    stack: init_frame.stack.subrange(0, lbl.stack_height as int)
                        + init_frame.stack.subrange(init_frame.stack.len() - (lbl.arity as int), init_frame.stack.len() as int),
                    labels: init_frame.labels.subrange(0, target_idx as int),
                    ..init_frame
                });
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
    }
}

// ---------------------------------------------------------------------------
// 7. Function Invocation Frame Builder (`Call`, `CallIndirect`, Top-Level)
// ---------------------------------------------------------------------------

pub open spec fn spec_args_match_params(args: Seq<WasmVal>, params: Seq<ValType>) -> bool {
    args.len() == params.len()
        && (forall|i: int| 0 <= i < args.len() ==> #[trigger] spec_val_has_type(args[i], params[i]))
}

pub fn check_args_match_params(args: &[WasmVal], params: &[ValType]) -> (ok: bool)
    ensures
        ok == spec_args_match_params(args@, params@),
{
    if args.len() != params.len() {
        return false;
    }
    let n = args.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == args@.len(),
            n == params@.len(),
            forall|k: int| 0 <= k < i as int ==> #[trigger] spec_val_has_type(args@[k], params@[k]),
        decreases n - i,
    {
        if !val_has_type(args[i], params[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}

pub open spec fn spec_build_callee_frame(
    module: SpecWasmModule,
    func_idx: usize,
    args: Seq<WasmVal>,
) -> Result<SpecCallFrame, WasmTrap> {
    if (func_idx as nat) >= module.funcs.len() {
        Err(WasmTrap::InvalidFunctionIndex)
    } else {
        let fbody = module.funcs[func_idx as int];
        if (fbody.type_idx as nat) >= module.types.len() {
            Err(WasmTrap::InvalidFunctionIndex)
        } else {
            let ftype = module.types[fbody.type_idx as int];
            if !spec_args_match_params(args, ftype.params) {
                Err(WasmTrap::TypeMismatch)
            } else if ftype.params.len() + fbody.locals.len() > MAX_LOCALS_PER_FUNC as nat {
                Err(WasmTrap::InvalidLocalIndex)
            } else {
                let extra_vals = Seq::new(fbody.locals.len(), |i: int| spec_default_val(fbody.locals[i]));
                Ok(SpecCallFrame {
                    func_idx,
                    pc: 0,
                    locals: args + extra_vals,
                    local_types: ftype.params + fbody.locals,
                    stack: Seq::empty(),
                    labels: Seq::empty(),
                    return_arity: ftype.results.len() as usize,
                })
            }
        }
    }
}

#[verifier::spinoff_prover]
pub fn build_callee_frame(
    module: &WasmModule,
    func_idx: usize,
    args: &[WasmVal],
) -> (r: Result<CallFrame, WasmTrap>)
    ensures
        match (r, spec_build_callee_frame(module@, func_idx, args@)) {
            (Ok(f), Ok(sf)) => f@ == sf,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    if func_idx >= module.funcs.len() {
        return Err(WasmTrap::InvalidFunctionIndex);
    }
    let fbody = &module.funcs[func_idx];
    if (fbody.type_idx as u64) >= (module.types.len() as u64) {
        return Err(WasmTrap::InvalidFunctionIndex);
    }
    let ftype = &module.types[fbody.type_idx as usize];
    if !check_args_match_params(args, &ftype.params) {
        return Err(WasmTrap::TypeMismatch);
    }
    if ftype.params.len() > MAX_LOCALS_PER_FUNC
        || fbody.locals.len() > MAX_LOCALS_PER_FUNC - ftype.params.len()
    {
        return Err(WasmTrap::InvalidLocalIndex);
    }
    let total_locals = ftype.params.len() + fbody.locals.len();
    let mut locals: Vec<WasmVal> = Vec::with_capacity(total_locals);
    let mut local_types: Vec<ValType> = Vec::with_capacity(total_locals);

    let plen = ftype.params.len();
    let mut i: usize = 0;
    while i < plen
        invariant
            i <= plen,
            plen == args@.len(),
            plen == ftype.params@.len(),
            locals@.len() == i as nat,
            local_types@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> locals@[k] == args@[k],
            forall|k: int| 0 <= k < i as int ==> local_types@[k] == ftype.params@[k],
        decreases plen - i,
    {
        locals.push(args[i]);
        local_types.push(ftype.params[i]);
        i = i + 1;
    }

    let llen = fbody.locals.len();
    let mut j: usize = 0;
    while j < llen
        invariant
            j <= llen,
            llen == fbody.locals@.len(),
            plen == args@.len(),
            plen == ftype.params@.len(),
            locals@.len() == (plen + j) as nat,
            local_types@.len() == (plen + j) as nat,
            forall|k: int| 0 <= k < plen as int ==> locals@[k] == args@[k],
            forall|k: int| 0 <= k < plen as int ==> local_types@[k] == ftype.params@[k],
            forall|k: int| 0 <= k < j as int ==> locals@[plen as int + k] == spec_default_val(fbody.locals@[k]),
            forall|k: int| 0 <= k < j as int ==> local_types@[plen as int + k] == fbody.locals@[k],
        decreases llen - j,
    {
        let vt = fbody.locals[j];
        locals.push(default_val(vt));
        local_types.push(vt);
        j = j + 1;
    }

    proof {
        let extra_vals = Seq::new(fbody.locals@.len(), |k: int| spec_default_val(fbody.locals@[k]));
        assert(locals@ =~= args@ + extra_vals);
        assert(local_types@ =~= ftype.params@ + fbody.locals@);
    }

    Ok(CallFrame {
        func_idx,
        pc: 0,
        locals,
        local_types,
        stack: Vec::new(),
        labels: Vec::new(),
        return_arity: ftype.results.len(),
    })
}

pub open spec fn spec_invoke_callee_from_frame(
    module: SpecWasmModule,
    caller_frames: Seq<SpecCallFrame>,
    caller: SpecCallFrame,
    func_idx: usize,
) -> (SpecWasmExecState, SpecStepOutcome) {
    // caller_frames already has `caller` popped; total active depth is caller_frames.len() + 1.
    if caller_frames.len() + 1 >= MAX_WASM_CALL_DEPTH as nat {
        (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::CallStackExhausted))
    } else if (func_idx as nat) >= module.funcs.len() {
        (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
    } else {
        let fbody = module.funcs[func_idx as int];
        if (fbody.type_idx as nat) >= module.types.len() {
            (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
        } else {
            let ftype = module.types[fbody.type_idx as int];
            let arity = ftype.params.len() as usize;
            if ftype.params.len() > usize::MAX as nat {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidLocalIndex))
            } else {
                match spec_extract_top_arity(caller.stack, arity) {
                    Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                    Ok(args) => {
                        match spec_build_callee_frame(module, func_idx, args) {
                            Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                            Ok(callee_frame) => {
                                if caller.pc >= usize::MAX {
                                    (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
                                } else {
                                    let new_caller = SpecCallFrame {
                                        pc: (caller.pc + 1) as usize,
                                        stack: caller.stack.subrange(0, caller.stack.len() - (arity as int)),
                                        ..caller
                                    };
                                    (
                                        SpecWasmExecState {
                                            frames: caller_frames.push(new_caller).push(callee_frame),
                                        },
                                        SpecStepOutcome::Continue,
                                    )
                                }
                            },
                        }
                    },
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_invoke_callee_from_frame(
    module: &WasmModule,
    state: &mut WasmExecState,
    mut caller: CallFrame,
    func_idx: usize,
) -> (out: StepOutcome)
    ensures
        ({
            let (s_next, s_out) = spec_invoke_callee_from_frame(
                module@,
                old(state)@.frames,
                caller@,
                func_idx,
            );
            final(state)@ == s_next && out@ == s_out
        }),
{
    let ghost pre_frames = state@.frames;
    let ghost init_caller = caller@;
    if state.frames.len() >= MAX_WASM_CALL_DEPTH - 1 {
        return StepOutcome::Trap(WasmTrap::CallStackExhausted);
    }
    if func_idx >= module.funcs.len() {
        return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
    }
    let fbody = &module.funcs[func_idx];
    if (fbody.type_idx as u64) >= (module.types.len() as u64) {
        return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
    }
    let ftype = &module.types[fbody.type_idx as usize];
    let arity = ftype.params.len();
    let args = match extract_top_arity(&caller.stack, arity) {
        Ok(a) => a,
        Err(t) => return StepOutcome::Trap(t),
    };
    let callee_frame = match build_callee_frame(module, func_idx, &args) {
        Ok(cf) => cf,
        Err(t) => return StepOutcome::Trap(t),
    };
    if caller.pc == usize::MAX {
        return StepOutcome::Trap(WasmTrap::Unreachable);
    }
    let rem = caller.stack.len() - arity;
    caller.stack.truncate(rem);
    caller.pc = caller.pc + 1;
    let ghost nc = caller@;
    let ghost ncf = callee_frame@;
    state.frames.push(caller);
    state.frames.push(callee_frame);
    proof {
        assert(nc == SpecCallFrame {
            pc: (init_caller.pc + 1) as usize,
            stack: init_caller.stack.subrange(0, init_caller.stack.len() - (arity as int)),
            ..init_caller
        });
        assert(state@.frames =~= pre_frames.push(nc).push(ncf));
    }
    StepOutcome::Continue
}

// ---------------------------------------------------------------------------
// 8. Category Step Helpers (`Numeric`, `Local`, `Global`, `Memory`, `Control`)
// ---------------------------------------------------------------------------

pub open spec fn spec_step_numeric_op(
    frame: SpecCallFrame,
    op: WasmOp,
) -> Result<SpecCallFrame, WasmTrap> {
    if frame.pc >= usize::MAX {
        Err(WasmTrap::Unreachable)
    } else {
        let next_pc = (frame.pc + 1) as usize;
        match op {
            WasmOp::Nop => Ok(SpecCallFrame { pc: next_pc, ..frame }),
            WasmOp::Drop => {
                match spec_pop_val(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, _)) => Ok(SpecCallFrame { pc: next_pc, stack: s1, ..frame }),
                }
            },
            WasmOp::Select => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, c)) => match spec_pop_val(s1) {
                        Err(t) => Err(t),
                        Ok((s2, v2)) => match spec_pop_val(s2) {
                            Err(t) => Err(t),
                            Ok((s3, v1)) => {
                                if !spec_same_wasm_val_type(v1, v2) {
                                    Err(WasmTrap::TypeMismatch)
                                } else {
                                    let chosen = if c != 0 { v1 } else { v2 };
                                    Ok(SpecCallFrame { pc: next_pc, stack: s3.push(chosen), ..frame })
                                }
                            },
                        },
                    },
                }
            },
            WasmOp::I32Const(v) => Ok(SpecCallFrame { pc: next_pc, stack: frame.stack.push(WasmVal::I32(v)), ..frame }),
            WasmOp::I64Const(v) => Ok(SpecCallFrame { pc: next_pc, stack: frame.stack.push(WasmVal::I64(v)), ..frame }),
            WasmOp::F32Const(v) => Ok(SpecCallFrame { pc: next_pc, stack: frame.stack.push(WasmVal::F32Bits(v)), ..frame }),
            WasmOp::F64Const(v) => Ok(SpecCallFrame { pc: next_pc, stack: frame.stack.push(WasmVal::F64Bits(v)), ..frame }),
            WasmOp::I32Eqz => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        let r = if v == 0 { 1i32 } else { 0i32 };
                        Ok(SpecCallFrame { pc: next_pc, stack: s1.push(WasmVal::I32(r)), ..frame })
                    },
                }
            },
            WasmOp::I64Eqz => {
                match spec_pop_i64(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        let r = if v == 0 { 1i32 } else { 0i32 };
                        Ok(SpecCallFrame { pc: next_pc, stack: s1.push(WasmVal::I32(r)), ..frame })
                    },
                }
            },
            WasmOp::I32Rel(rop) => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, b)) => match spec_pop_i32(s1) {
                        Err(t) => Err(t),
                        Ok((s2, a)) => Ok(SpecCallFrame {
                            pc: next_pc,
                            stack: s2.push(WasmVal::I32(spec_i32_rel(rop, a, b))),
                            ..frame
                        }),
                    },
                }
            },
            WasmOp::I64Rel(rop) => {
                match spec_pop_i64(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, b)) => match spec_pop_i64(s1) {
                        Err(t) => Err(t),
                        Ok((s2, a)) => Ok(SpecCallFrame {
                            pc: next_pc,
                            stack: s2.push(WasmVal::I32(spec_i64_rel(rop, a, b))),
                            ..frame
                        }),
                    },
                }
            },
            WasmOp::I32Unary(uop) => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => Ok(SpecCallFrame {
                        pc: next_pc,
                        stack: s1.push(WasmVal::I32(spec_i32_unop(uop, v))),
                        ..frame
                    }),
                }
            },
            WasmOp::I32Binary(bop) => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, b)) => match spec_pop_i32(s1) {
                        Err(t) => Err(t),
                        Ok((s2, a)) => match spec_i32_binop(bop, a, b) {
                            Err(t) => Err(t),
                            Ok(r) => Ok(SpecCallFrame {
                                pc: next_pc,
                                stack: s2.push(WasmVal::I32(r)),
                                ..frame
                            }),
                        },
                    },
                }
            },
            WasmOp::I64Unary(uop) => {
                match spec_pop_i64(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => Ok(SpecCallFrame {
                        pc: next_pc,
                        stack: s1.push(WasmVal::I64(spec_i64_unop(uop, v))),
                        ..frame
                    }),
                }
            },
            WasmOp::I64Binary(bop) => {
                match spec_pop_i64(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, b)) => match spec_pop_i64(s1) {
                        Err(t) => Err(t),
                        Ok((s2, a)) => match spec_i64_binop(bop, a, b) {
                            Err(t) => Err(t),
                            Ok(r) => Ok(SpecCallFrame {
                                pc: next_pc,
                                stack: s2.push(WasmVal::I64(r)),
                                ..frame
                            }),
                        },
                    },
                }
            },
            WasmOp::I32WrapI64 => {
                match spec_pop_i64(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        let u32_val = (0u64.wrapping_add_signed(v) % 0x1_0000_0000u64) as u32;
                        Ok(SpecCallFrame {
                            pc: next_pc,
                            stack: s1.push(WasmVal::I32(0i32.wrapping_add_unsigned(u32_val))),
                            ..frame
                        })
                    },
                }
            },
            WasmOp::I64ExtendI32S => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => Ok(SpecCallFrame {
                        pc: next_pc,
                        stack: s1.push(WasmVal::I64(v as i64)),
                        ..frame
                    }),
                }
            },
            WasmOp::I64ExtendI32U => {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => Ok(SpecCallFrame {
                        pc: next_pc,
                        stack: s1.push(WasmVal::I64((0u32.wrapping_add_signed(v) as u64) as i64)),
                        ..frame
                    }),
                }
            },
            _ => Err(WasmTrap::Unreachable),
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_step_numeric_op(
    mut frame: CallFrame,
    op: WasmOp,
) -> (r: Result<CallFrame, WasmTrap>)
    ensures
        match (r, spec_step_numeric_op(frame@, op)) {
            (Ok(nf), Ok(snf)) => nf@ == snf,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    if frame.pc == usize::MAX {
        return Err(WasmTrap::Unreachable);
    }
    let next_pc = frame.pc + 1;
    match op {
        WasmOp::Nop => {
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::Drop => {
            let _ = pop_val_vec(&mut frame.stack)?;
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::Select => {
            let c = pop_i32_vec(&mut frame.stack)?;
            let v2 = pop_val_vec(&mut frame.stack)?;
            let v1 = pop_val_vec(&mut frame.stack)?;
            if !same_wasm_val_type(v1, v2) {
                return Err(WasmTrap::TypeMismatch);
            }
            let chosen = if c != 0 { v1 } else { v2 };
            frame.stack.push(chosen);
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32Const(v) => {
            frame.stack.push(WasmVal::I32(v));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64Const(v) => {
            frame.stack.push(WasmVal::I64(v));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::F32Const(v) => {
            frame.stack.push(WasmVal::F32Bits(v));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::F64Const(v) => {
            frame.stack.push(WasmVal::F64Bits(v));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32Eqz => {
            let v = pop_i32_vec(&mut frame.stack)?;
            let r = if v == 0 { 1i32 } else { 0i32 };
            frame.stack.push(WasmVal::I32(r));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64Eqz => {
            let v = pop_i64_vec(&mut frame.stack)?;
            let r = if v == 0 { 1i32 } else { 0i32 };
            frame.stack.push(WasmVal::I32(r));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32Rel(rop) => {
            let b = pop_i32_vec(&mut frame.stack)?;
            let a = pop_i32_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I32(eval_i32_rel(rop, a, b)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64Rel(rop) => {
            let b = pop_i64_vec(&mut frame.stack)?;
            let a = pop_i64_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I32(eval_i64_rel(rop, a, b)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32Unary(uop) => {
            let v = pop_i32_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I32(eval_i32_unop(uop, v)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32Binary(bop) => {
            let b = pop_i32_vec(&mut frame.stack)?;
            let a = pop_i32_vec(&mut frame.stack)?;
            let r = eval_i32_binop(bop, a, b)?;
            frame.stack.push(WasmVal::I32(r));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64Unary(uop) => {
            let v = pop_i64_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I64(eval_i64_unop(uop, v)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64Binary(bop) => {
            let b = pop_i64_vec(&mut frame.stack)?;
            let a = pop_i64_vec(&mut frame.stack)?;
            let r = eval_i64_binop(bop, a, b)?;
            frame.stack.push(WasmVal::I64(r));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I32WrapI64 => {
            let v = pop_i64_vec(&mut frame.stack)?;
            let u32_val = (0u64.wrapping_add_signed(v) % 0x1_0000_0000u64) as u32;
            frame.stack.push(WasmVal::I32(0i32.wrapping_add_unsigned(u32_val)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64ExtendI32S => {
            let v = pop_i32_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I64(v as i64));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::I64ExtendI32U => {
            let v = pop_i32_vec(&mut frame.stack)?;
            frame.stack.push(WasmVal::I64((0u32.wrapping_add_signed(v) as u64) as i64));
            frame.pc = next_pc;
            Ok(frame)
        },
        _ => Err(WasmTrap::Unreachable),
    }
}

pub open spec fn spec_step_local_op(
    frame: SpecCallFrame,
    op: WasmOp,
) -> Result<SpecCallFrame, WasmTrap> {
    if frame.pc >= usize::MAX {
        Err(WasmTrap::Unreachable)
    } else {
        let next_pc = (frame.pc + 1) as usize;
        match op {
            WasmOp::LocalGet(idx) => {
                if (idx as nat) >= frame.locals.len() {
                    Err(WasmTrap::InvalidLocalIndex)
                } else {
                    let v = frame.locals[idx as int];
                    Ok(SpecCallFrame { pc: next_pc, stack: frame.stack.push(v), ..frame })
                }
            },
            WasmOp::LocalSet(idx) => {
                match spec_pop_val(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        if (idx as nat) >= frame.locals.len() || (idx as nat) >= frame.local_types.len() {
                            Err(WasmTrap::InvalidLocalIndex)
                        } else if !spec_val_has_type(v, frame.local_types[idx as int]) {
                            Err(WasmTrap::TypeMismatch)
                        } else {
                            Ok(SpecCallFrame {
                                pc: next_pc,
                                locals: frame.locals.update(idx as int, v),
                                stack: s1,
                                ..frame
                            })
                        }
                    },
                }
            },
            WasmOp::LocalTee(idx) => {
                match spec_pop_val(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        if (idx as nat) >= frame.locals.len() || (idx as nat) >= frame.local_types.len() {
                            Err(WasmTrap::InvalidLocalIndex)
                        } else if !spec_val_has_type(v, frame.local_types[idx as int]) {
                            Err(WasmTrap::TypeMismatch)
                        } else {
                            Ok(SpecCallFrame {
                                pc: next_pc,
                                locals: frame.locals.update(idx as int, v),
                                stack: s1.push(v),
                                ..frame
                            })
                        }
                    },
                }
            },
            _ => Err(WasmTrap::Unreachable),
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_step_local_op(
    mut frame: CallFrame,
    op: WasmOp,
) -> (r: Result<CallFrame, WasmTrap>)
    ensures
        match (r, spec_step_local_op(frame@, op)) {
            (Ok(nf), Ok(snf)) => nf@ == snf,
            (Err(t1), Err(t2)) => t1 == t2,
            _ => false,
        },
{
    if frame.pc == usize::MAX {
        return Err(WasmTrap::Unreachable);
    }
    let next_pc = frame.pc + 1;
    match op {
        WasmOp::LocalGet(idx) => {
            if (idx as u64) >= (frame.locals.len() as u64) {
                return Err(WasmTrap::InvalidLocalIndex);
            }
            let v = frame.locals[idx as usize];
            frame.stack.push(v);
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::LocalSet(idx) => {
            let v = pop_val_vec(&mut frame.stack)?;
            if (idx as u64) >= (frame.locals.len() as u64)
                || (idx as u64) >= (frame.local_types.len() as u64)
            {
                return Err(WasmTrap::InvalidLocalIndex);
            }
            let u = idx as usize;
            if !val_has_type(v, frame.local_types[u]) {
                return Err(WasmTrap::TypeMismatch);
            }
            frame.locals[u] = v;
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::LocalTee(idx) => {
            let v = pop_val_vec(&mut frame.stack)?;
            if (idx as u64) >= (frame.locals.len() as u64)
                || (idx as u64) >= (frame.local_types.len() as u64)
            {
                return Err(WasmTrap::InvalidLocalIndex);
            }
            let u = idx as usize;
            if !val_has_type(v, frame.local_types[u]) {
                return Err(WasmTrap::TypeMismatch);
            }
            frame.locals[u] = v;
            frame.stack.push(v);
            frame.pc = next_pc;
            Ok(frame)
        },
        _ => Err(WasmTrap::Unreachable),
    }
}

pub open spec fn spec_step_global_op(
    inst: SpecWasmInstance,
    frame: SpecCallFrame,
    op: WasmOp,
) -> Result<(SpecWasmInstance, SpecCallFrame), WasmTrap> {
    if frame.pc >= usize::MAX {
        Err(WasmTrap::Unreachable)
    } else {
        let next_pc = (frame.pc + 1) as usize;
        match op {
            WasmOp::GlobalGet(idx) => {
                if (idx as nat) >= inst.globals.len() {
                    Err(WasmTrap::InvalidGlobalIndex)
                } else {
                    let v = inst.globals[idx as int];
                    Ok((inst, SpecCallFrame { pc: next_pc, stack: frame.stack.push(v), ..frame }))
                }
            },
            WasmOp::GlobalSet(idx) => {
                match spec_pop_val(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, v)) => {
                        if (idx as nat) >= inst.globals.len()
                            || (idx as nat) >= inst.global_types.len()
                            || (idx as nat) >= inst.global_mut.len()
                        {
                            Err(WasmTrap::InvalidGlobalIndex)
                        } else if !inst.global_mut[idx as int] {
                            Err(WasmTrap::ImmutableGlobalWrite)
                        } else if !spec_val_has_type(v, inst.global_types[idx as int]) {
                            Err(WasmTrap::TypeMismatch)
                        } else {
                            let next_inst = SpecWasmInstance {
                                globals: inst.globals.update(idx as int, v),
                                ..inst
                            };
                            let next_frame = SpecCallFrame { pc: next_pc, stack: s1, ..frame };
                            Ok((next_inst, next_frame))
                        }
                    },
                }
            },
            _ => Err(WasmTrap::Unreachable),
        }
    }
}

#[verifier::spinoff_prover]
pub fn exec_step_global_op(
    inst: &mut WasmInstance,
    mut frame: CallFrame,
    op: WasmOp,
) -> (r: Result<CallFrame, WasmTrap>)
    requires
        old(inst)@.wf(),
    ensures
        match (r, spec_step_global_op(old(inst)@, frame@, op)) {
            (Ok(nf), Ok((s_inst, snf))) =>
                final(inst)@ == s_inst && nf@ == snf && final(inst)@.wf(),
            (Err(t1), Err(t2)) =>
                t1 == t2 && final(inst)@ == old(inst)@ && final(inst)@.wf(),
            _ => false,
        },
{
    if frame.pc == usize::MAX {
        return Err(WasmTrap::Unreachable);
    }
    let next_pc = frame.pc + 1;
    match op {
        WasmOp::GlobalGet(idx) => {
            if (idx as u64) >= (inst.globals.len() as u64) {
                return Err(WasmTrap::InvalidGlobalIndex);
            }
            let v = inst.globals[idx as usize];
            frame.stack.push(v);
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::GlobalSet(idx) => {
            let v = pop_val_vec(&mut frame.stack)?;
            if (idx as u64) >= (inst.globals.len() as u64)
                || (idx as u64) >= (inst.global_types.len() as u64)
                || (idx as u64) >= (inst.global_mut.len() as u64)
            {
                return Err(WasmTrap::InvalidGlobalIndex);
            }
            let u = idx as usize;
            if !inst.global_mut[u] {
                return Err(WasmTrap::ImmutableGlobalWrite);
            }
            if !val_has_type(v, inst.global_types[u]) {
                return Err(WasmTrap::TypeMismatch);
            }
            inst.globals[u] = v;
            frame.pc = next_pc;
            Ok(frame)
        },
        _ => Err(WasmTrap::Unreachable),
    }
}

pub open spec fn spec_step_memory_op(
    inst: SpecWasmInstance,
    frame: SpecCallFrame,
    op: WasmOp,
) -> Result<(SpecWasmInstance, SpecCallFrame), WasmTrap> {
    match op {
        WasmOp::MemLoad { load_kind, offset } => {
            match spec_pop_i32(frame.stack) {
                Err(t) => Err(t),
                Ok((s1, addr)) => match spec_mem_load(inst, load_kind, offset, addr) {
                    Err(t) => Err(t),
                    Ok(v) => {
                        if frame.pc >= usize::MAX {
                            Err(WasmTrap::Unreachable)
                        } else {
                            Ok((
                                inst,
                                SpecCallFrame { pc: (frame.pc + 1) as usize, stack: s1.push(v), ..frame },
                            ))
                        }
                    },
                },
            }
        },
        WasmOp::MemStore { store_kind, offset } => {
            match spec_pop_val(frame.stack) {
                Err(t) => Err(t),
                Ok((s1, val)) => match spec_pop_i32(s1) {
                    Err(t) => Err(t),
                    Ok((s2, addr)) => {
                        let ea = spec_effective_addr(addr, offset);
                        let w = spec_store_width(store_kind);
                        if !inst.has_memory || ea + w > inst.memory.len() {
                            Err(WasmTrap::OutOfBoundsMemoryAccess)
                        } else if frame.pc >= usize::MAX {
                            Err(WasmTrap::Unreachable)
                        } else {
                            match spec_mem_store(inst, store_kind, offset, addr, val) {
                                Err(t) => Err(t),
                                Ok(next_inst) => Ok((
                                    next_inst,
                                    SpecCallFrame { pc: (frame.pc + 1) as usize, stack: s2, ..frame },
                                )),
                            }
                        }
                    },
                },
            }
        },
        WasmOp::MemorySize => {
            if !inst.has_memory {
                Err(WasmTrap::OutOfBoundsMemoryAccess)
            } else if frame.pc >= usize::MAX {
                Err(WasmTrap::Unreachable)
            } else {
                Ok((
                    inst,
                    SpecCallFrame {
                        pc: (frame.pc + 1) as usize,
                        stack: frame.stack.push(WasmVal::I32(0i32.wrapping_add_unsigned(inst.mem_pages))),
                        ..frame
                    },
                ))
            }
        },
        WasmOp::MemoryGrow => {
            if frame.pc >= usize::MAX {
                Err(WasmTrap::Unreachable)
            } else {
                match spec_pop_i32(frame.stack) {
                    Err(t) => Err(t),
                    Ok((s1, delta)) => match spec_memory_grow(inst, delta) {
                        Err(t) => Err(t),
                        Ok((next_inst, old_pages)) => Ok((
                            next_inst,
                            SpecCallFrame {
                                pc: (frame.pc + 1) as usize,
                                stack: s1.push(WasmVal::I32(old_pages)),
                                ..frame
                            },
                        )),
                    },
                }
            }
        },
        _ => Err(WasmTrap::Unreachable),
    }
}

#[verifier::spinoff_prover]
pub fn exec_step_memory_op(
    inst: &mut WasmInstance,
    mut frame: CallFrame,
    op: WasmOp,
) -> (r: Result<CallFrame, WasmTrap>)
    requires
        old(inst)@.wf(),
        frame.pc < usize::MAX,
    ensures
        match (r, spec_step_memory_op(old(inst)@, frame@, op)) {
            (Ok(nf), Ok((s_inst, snf))) =>
                final(inst)@ == s_inst && nf@ == snf && final(inst)@.wf(),
            (Err(t1), Err(t2)) =>
                t1 == t2 && final(inst)@ == old(inst)@ && final(inst)@.wf(),
            _ => false,
        },
{
    let next_pc = frame.pc + 1;
    match op {
        WasmOp::MemLoad { load_kind, offset } => {
            let addr = pop_i32_vec(&mut frame.stack)?;
            let v = exec_mem_load(inst, load_kind, offset, addr)?;
            frame.stack.push(v);
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::MemStore { store_kind, offset } => {
            let val = pop_val_vec(&mut frame.stack)?;
            let addr = pop_i32_vec(&mut frame.stack)?;
            exec_mem_store(inst, store_kind, offset, addr, val)?;
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::MemorySize => {
            if !inst.has_memory {
                return Err(WasmTrap::OutOfBoundsMemoryAccess);
            }
            frame.stack.push(WasmVal::I32(0i32.wrapping_add_unsigned(inst.mem_pages)));
            frame.pc = next_pc;
            Ok(frame)
        },
        WasmOp::MemoryGrow => {
            let delta = pop_i32_vec(&mut frame.stack)?;
            let old_pages = exec_memory_grow(inst, delta)?;
            frame.stack.push(WasmVal::I32(old_pages));
            frame.pc = next_pc;
            Ok(frame)
        },
        _ => Err(WasmTrap::Unreachable),
    }
}

pub open spec fn spec_step_ctrl_op(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    caller_frames: Seq<SpecCallFrame>,
    frame: SpecCallFrame,
    op: WasmOp,
) -> (SpecWasmExecState, SpecStepOutcome) {
    match op {
        WasmOp::Unreachable => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable)),
        WasmOp::Unsupported(code) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Unsupported(code)),
        WasmOp::FuncEnd | WasmOp::Return => spec_return_from_frame(caller_frames, frame),
        WasmOp::Block { end_pc, arity } => {
            if frame.pc >= usize::MAX || frame.stack.len() > usize::MAX as nat {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
            } else {
                let lbl = CtrlLabel {
                    target_pc: end_pc,
                    stack_height: frame.stack.len() as usize,
                    arity,
                };
                let nf = SpecCallFrame {
                    pc: (frame.pc + 1) as usize,
                    labels: frame.labels.push(lbl),
                    ..frame
                };
                (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
            }
        },
        WasmOp::Loop { loop_pc } => {
            if frame.pc >= usize::MAX || frame.stack.len() > usize::MAX as nat {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
            } else {
                let lbl = CtrlLabel {
                    target_pc: loop_pc,
                    stack_height: frame.stack.len() as usize,
                    arity: 0,
                };
                let nf = SpecCallFrame {
                    pc: (frame.pc + 1) as usize,
                    labels: frame.labels.push(lbl),
                    ..frame
                };
                (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
            }
        },
        WasmOp::If { else_pc, end_pc, arity } => {
            if frame.pc >= usize::MAX {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
            } else {
                match spec_pop_i32(frame.stack) {
                    Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                    Ok((s1, c)) => {
                        if s1.len() > usize::MAX as nat {
                            (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
                        } else {
                            let lbl = CtrlLabel {
                                target_pc: end_pc,
                                stack_height: s1.len() as usize,
                                arity,
                            };
                            let next_pc = if c != 0 { (frame.pc + 1) as usize } else { else_pc };
                            let nf = SpecCallFrame {
                                pc: next_pc,
                                stack: s1,
                                labels: frame.labels.push(lbl),
                                ..frame
                            };
                            (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
                        }
                    },
                }
            }
        },
        WasmOp::ElseJump { end_pc } => {
            if frame.labels.len() == 0 {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidLabel))
            } else {
                let nf = SpecCallFrame {
                    pc: end_pc,
                    labels: frame.labels.drop_last(),
                    ..frame
                };
                (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
            }
        },
        WasmOp::End => {
            if frame.pc >= usize::MAX || frame.labels.len() == 0 {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidLabel))
            } else {
                let nf = SpecCallFrame {
                    pc: (frame.pc + 1) as usize,
                    labels: frame.labels.drop_last(),
                    ..frame
                };
                (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
            }
        },
        WasmOp::Br(depth) => spec_branch_in_frame(caller_frames, frame, depth),
        WasmOp::BrIf(depth) => {
            if frame.pc >= usize::MAX {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable))
            } else {
                match spec_pop_i32(frame.stack) {
                    Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                    Ok((s1, c)) => {
                        let f_popped = SpecCallFrame { stack: s1, ..frame };
                        if c != 0 {
                            spec_branch_in_frame(caller_frames, f_popped, depth)
                        } else {
                            let nf = SpecCallFrame { pc: (frame.pc + 1) as usize, ..f_popped };
                            (SpecWasmExecState { frames: caller_frames.push(nf) }, SpecStepOutcome::Continue)
                        }
                    },
                }
            }
        },
        WasmOp::BrTable { table_idx, default_label } => {
            if (frame.func_idx as nat) >= module.funcs.len() {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
            } else {
                let fbody = module.funcs[frame.func_idx as int];
                if (table_idx as nat) >= fbody.br_tables.len() {
                    (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidLabel))
                } else {
                    match spec_pop_i32(frame.stack) {
                        Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                        Ok((s1, idx_i32)) => {
                            let f_popped = SpecCallFrame { stack: s1, ..frame };
                            let u = 0u32.wrapping_add_signed(idx_i32);
                            let targets = fbody.br_tables[table_idx as int];
                            let chosen = if (u as nat) < targets.len() {
                                targets[u as int]
                            } else {
                                default_label
                            };
                            spec_branch_in_frame(caller_frames, f_popped, chosen)
                        },
                    }
                }
            }
        },
        WasmOp::Call(fidx) => {
            if (fidx as nat) >= module.funcs.len() || (fidx as nat) > usize::MAX as nat {
                (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
            } else {
                spec_invoke_callee_from_frame(module, caller_frames, frame, fidx as usize)
            }
        },
        WasmOp::CallIndirect(expected_tidx) => {
            match spec_pop_i32(frame.stack) {
                Err(t) => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(t)),
                Ok((s1, elem_i32)) => {
                    let f_popped = SpecCallFrame { stack: s1, ..frame };
                    let elem_u32 = 0u32.wrapping_add_signed(elem_i32);
                    if !inst.has_table || (elem_u32 as nat) >= inst.table.len() {
                        (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::UndefinedElement))
                    } else {
                        match inst.table[elem_u32 as int] {
                            None => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::UndefinedElement)),
                            Some(fidx) => {
                                if (fidx as nat) >= module.funcs.len() || (fidx as nat) > usize::MAX as nat {
                                    (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
                                } else if (expected_tidx as nat) >= module.types.len() {
                                    (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::IndirectCallTypeMismatch))
                                } else {
                                    let callee_body = module.funcs[fidx as int];
                                    if (callee_body.type_idx as nat) >= module.types.len() {
                                        (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex))
                                    } else {
                                        let actual_ty = module.types[callee_body.type_idx as int];
                                        let expected_ty = module.types[expected_tidx as int];
                                        if !spec_func_type_eq(actual_ty, expected_ty) {
                                            (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::IndirectCallTypeMismatch))
                                        } else {
                                            spec_invoke_callee_from_frame(module, caller_frames, f_popped, fidx as usize)
                                        }
                                    }
                                }
                            },
                        }
                    }
                },
            }
        },
        _ => (SpecWasmExecState { frames: caller_frames }, SpecStepOutcome::Trap(WasmTrap::Unreachable)),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn exec_step_ctrl_op(
    module: &WasmModule,
    inst: &WasmInstance,
    state: &mut WasmExecState,
    mut frame: CallFrame,
    op: WasmOp,
) -> (out: StepOutcome)
    ensures
        ({
            let (s_next, s_out) = spec_step_ctrl_op(module@, inst@, old(state)@.frames, frame@, op);
            final(state)@ == s_next && out@ == s_out
        }),
{
    let ghost pre_frames = state@.frames;
    let ghost init_frame = frame@;
    match op {
        WasmOp::Unreachable => StepOutcome::Trap(WasmTrap::Unreachable),
        WasmOp::Unsupported(code) => StepOutcome::Unsupported(code),
        WasmOp::FuncEnd | WasmOp::Return => exec_return_from_frame(state, frame),
        WasmOp::Block { end_pc, arity } => {
            if frame.pc == usize::MAX {
                return StepOutcome::Trap(WasmTrap::Unreachable);
            }
            let lbl = CtrlLabel {
                target_pc: end_pc,
                stack_height: frame.stack.len(),
                arity,
            };
            frame.labels.push(lbl);
            frame.pc = frame.pc + 1;
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
        WasmOp::Loop { loop_pc } => {
            if frame.pc == usize::MAX {
                return StepOutcome::Trap(WasmTrap::Unreachable);
            }
            let lbl = CtrlLabel {
                target_pc: loop_pc,
                stack_height: frame.stack.len(),
                arity: 0,
            };
            frame.labels.push(lbl);
            frame.pc = frame.pc + 1;
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
        WasmOp::If { else_pc, end_pc, arity } => {
            if frame.pc == usize::MAX {
                return StepOutcome::Trap(WasmTrap::Unreachable);
            }
            let c = match pop_i32_vec(&mut frame.stack) {
                Ok(v) => v,
                Err(t) => return StepOutcome::Trap(t),
            };
            let lbl = CtrlLabel {
                target_pc: end_pc,
                stack_height: frame.stack.len(),
                arity,
            };
            frame.labels.push(lbl);
            frame.pc = if c != 0 { frame.pc + 1 } else { else_pc };
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
        WasmOp::ElseJump { end_pc } => {
            if frame.labels.len() == 0 {
                return StepOutcome::Trap(WasmTrap::InvalidLabel);
            }
            let _ = frame.labels.pop();
            frame.pc = end_pc;
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(nf == SpecCallFrame { pc: end_pc, labels: init_frame.labels.drop_last(), ..init_frame });
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
        WasmOp::End => {
            if frame.pc == usize::MAX || frame.labels.len() == 0 {
                return StepOutcome::Trap(WasmTrap::InvalidLabel);
            }
            let _ = frame.labels.pop();
            frame.pc = frame.pc + 1;
            let ghost nf = frame@;
            state.frames.push(frame);
            proof {
                assert(nf == SpecCallFrame { pc: (init_frame.pc + 1) as usize, labels: init_frame.labels.drop_last(), ..init_frame });
                assert(state@.frames =~= pre_frames.push(nf));
            }
            StepOutcome::Continue
        },
        WasmOp::Br(depth) => exec_branch_in_frame(state, frame, depth),
        WasmOp::BrIf(depth) => {
            if frame.pc == usize::MAX {
                return StepOutcome::Trap(WasmTrap::Unreachable);
            }
            let c = match pop_i32_vec(&mut frame.stack) {
                Ok(v) => v,
                Err(t) => return StepOutcome::Trap(t),
            };
            if c != 0 {
                exec_branch_in_frame(state, frame, depth)
            } else {
                frame.pc = frame.pc + 1;
                let ghost nf = frame@;
                state.frames.push(frame);
                proof {
                    assert(state@.frames =~= pre_frames.push(nf));
                }
                StepOutcome::Continue
            }
        },
        WasmOp::BrTable { table_idx, default_label } => {
            if frame.func_idx >= module.funcs.len() {
                return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
            }
            let fbody = &module.funcs[frame.func_idx];
            if table_idx >= fbody.br_tables.len() {
                return StepOutcome::Trap(WasmTrap::InvalidLabel);
            }
            let idx_i32 = match pop_i32_vec(&mut frame.stack) {
                Ok(v) => v,
                Err(t) => return StepOutcome::Trap(t),
            };
            let u = 0u32.wrapping_add_signed(idx_i32);
            let targets = &fbody.br_tables[table_idx];
            let chosen = if (u as u64) < (targets.len() as u64) {
                targets[u as usize]
            } else {
                default_label
            };
            exec_branch_in_frame(state, frame, chosen)
        },
        WasmOp::Call(fidx) => {
            if (fidx as u64) >= (module.funcs.len() as u64) {
                return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
            }
            exec_invoke_callee_from_frame(module, state, frame, fidx as usize)
        },
        WasmOp::CallIndirect(expected_tidx) => {
            let elem_i32 = match pop_i32_vec(&mut frame.stack) {
                Ok(v) => v,
                Err(t) => return StepOutcome::Trap(t),
            };
            let elem_u32 = 0u32.wrapping_add_signed(elem_i32);
            if !inst.has_table || (elem_u32 as u64) >= (inst.table.len() as u64) {
                return StepOutcome::Trap(WasmTrap::UndefinedElement);
            }
            match inst.table[elem_u32 as usize] {
                None => StepOutcome::Trap(WasmTrap::UndefinedElement),
                Some(fidx) => {
                    if (fidx as u64) >= (module.funcs.len() as u64) {
                        return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
                    }
                    if (expected_tidx as u64) >= (module.types.len() as u64) {
                        return StepOutcome::Trap(WasmTrap::IndirectCallTypeMismatch);
                    }
                    let callee_body = &module.funcs[fidx as usize];
                    if (callee_body.type_idx as u64) >= (module.types.len() as u64) {
                        return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
                    }
                    let actual_ty = &module.types[callee_body.type_idx as usize];
                    let expected_ty = &module.types[expected_tidx as usize];
                    if !func_type_eq(actual_ty, expected_ty) {
                        return StepOutcome::Trap(WasmTrap::IndirectCallTypeMismatch);
                    }
                    exec_invoke_callee_from_frame(module, state, frame, fidx as usize)
                },
            }
        },
        _ => StepOutcome::Trap(WasmTrap::Unreachable),
    }
}

// ---------------------------------------------------------------------------
// 9. Small-Step `wasm_step` & Fuel-Bounded `wasm_invoke` (`exec == spec`)
// ---------------------------------------------------------------------------

pub open spec fn spec_op_category(op: WasmOp) -> nat {
    match op {
        WasmOp::Nop
        | WasmOp::Drop
        | WasmOp::Select
        | WasmOp::I32Const(_)
        | WasmOp::I64Const(_)
        | WasmOp::F32Const(_)
        | WasmOp::F64Const(_)
        | WasmOp::I32Eqz
        | WasmOp::I64Eqz
        | WasmOp::I32Rel(_)
        | WasmOp::I64Rel(_)
        | WasmOp::I32Unary(_)
        | WasmOp::I32Binary(_)
        | WasmOp::I64Unary(_)
        | WasmOp::I64Binary(_)
        | WasmOp::I32WrapI64
        | WasmOp::I64ExtendI32S
        | WasmOp::I64ExtendI32U => 0,
        WasmOp::LocalGet(_) | WasmOp::LocalSet(_) | WasmOp::LocalTee(_) => 1,
        WasmOp::GlobalGet(_) | WasmOp::GlobalSet(_) => 2,
        WasmOp::MemLoad { .. } | WasmOp::MemStore { .. } | WasmOp::MemorySize | WasmOp::MemoryGrow => 3,
        _ => 4,
    }
}

pub fn op_category(op: WasmOp) -> (c: u8)
    ensures
        c as nat == spec_op_category(op),
{
    match op {
        WasmOp::Nop
        | WasmOp::Drop
        | WasmOp::Select
        | WasmOp::I32Const(_)
        | WasmOp::I64Const(_)
        | WasmOp::F32Const(_)
        | WasmOp::F64Const(_)
        | WasmOp::I32Eqz
        | WasmOp::I64Eqz
        | WasmOp::I32Rel(_)
        | WasmOp::I64Rel(_)
        | WasmOp::I32Unary(_)
        | WasmOp::I32Binary(_)
        | WasmOp::I64Unary(_)
        | WasmOp::I64Binary(_)
        | WasmOp::I32WrapI64
        | WasmOp::I64ExtendI32S
        | WasmOp::I64ExtendI32U => 0,
        WasmOp::LocalGet(_) | WasmOp::LocalSet(_) | WasmOp::LocalTee(_) => 1,
        WasmOp::GlobalGet(_) | WasmOp::GlobalSet(_) => 2,
        WasmOp::MemLoad { .. } | WasmOp::MemStore { .. } | WasmOp::MemorySize | WasmOp::MemoryGrow => 3,
        _ => 4,
    }
}

pub open spec fn spec_wasm_step(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    state: SpecWasmExecState,
) -> (SpecWasmInstance, SpecWasmExecState, SpecStepOutcome) {
    if state.frames.len() == 0 {
        (inst, state, SpecStepOutcome::Trap(WasmTrap::Unreachable))
    } else {
        let frame = state.frames.last();
        let caller_frames = state.frames.drop_last();
        if (frame.func_idx as nat) >= module.funcs.len() {
            (
                inst,
                SpecWasmExecState { frames: caller_frames },
                SpecStepOutcome::Trap(WasmTrap::InvalidFunctionIndex),
            )
        } else {
            let fbody = module.funcs[frame.func_idx as int];
            if (frame.pc as nat) >= fbody.ops.len() {
                (
                    inst,
                    SpecWasmExecState { frames: caller_frames },
                    SpecStepOutcome::Trap(WasmTrap::Unreachable),
                )
            } else {
                let op = fbody.ops[frame.pc as int];
                let cat = spec_op_category(op);
                if cat == 0 {
                    match spec_step_numeric_op(frame, op) {
                        Ok(nf) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames.push(nf) },
                            SpecStepOutcome::Continue,
                        ),
                        Err(t) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames },
                            SpecStepOutcome::Trap(t),
                        ),
                    }
                } else if cat == 1 {
                    match spec_step_local_op(frame, op) {
                        Ok(nf) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames.push(nf) },
                            SpecStepOutcome::Continue,
                        ),
                        Err(t) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames },
                            SpecStepOutcome::Trap(t),
                        ),
                    }
                } else if cat == 2 {
                    match spec_step_global_op(inst, frame, op) {
                        Ok((next_inst, nf)) => (
                            next_inst,
                            SpecWasmExecState { frames: caller_frames.push(nf) },
                            SpecStepOutcome::Continue,
                        ),
                        Err(t) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames },
                            SpecStepOutcome::Trap(t),
                        ),
                    }
                } else if cat == 3 {
                    match spec_step_memory_op(inst, frame, op) {
                        Ok((next_inst, nf)) => (
                            next_inst,
                            SpecWasmExecState { frames: caller_frames.push(nf) },
                            SpecStepOutcome::Continue,
                        ),
                        Err(t) => (
                            inst,
                            SpecWasmExecState { frames: caller_frames },
                            SpecStepOutcome::Trap(t),
                        ),
                    }
                } else {
                    let (next_state, out) = spec_step_ctrl_op(module, inst, caller_frames, frame, op);
                    (inst, next_state, out)
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
pub fn wasm_step(
    module: &WasmModule,
    inst: &mut WasmInstance,
    state: &mut WasmExecState,
) -> (out: StepOutcome)
    requires
        old(inst)@.wf(),
    ensures
        ({
            let (s_inst, s_state, s_out) = spec_wasm_step(module@, old(inst)@, old(state)@);
            final(inst)@ == s_inst && final(state)@ == s_state && out@ == s_out && final(inst)@.wf()
        }),
{
    if state.frames.len() == 0 {
        return StepOutcome::Trap(WasmTrap::Unreachable);
    }
    let ghost pre_frames = state@.frames;
    let frame = state.frames.pop().unwrap();
    let ghost caller_frames = state@.frames;
    proof {
        assert(frame@ == pre_frames.last());
        assert(caller_frames =~= pre_frames.drop_last());
    }
    if frame.func_idx >= module.funcs.len() {
        return StepOutcome::Trap(WasmTrap::InvalidFunctionIndex);
    }
    let fbody = &module.funcs[frame.func_idx];
    if frame.pc >= fbody.ops.len() {
        return StepOutcome::Trap(WasmTrap::Unreachable);
    }
    let op = fbody.ops[frame.pc];
    let cat = op_category(op);
    if cat == 0 {
        match exec_step_numeric_op(frame, op) {
            Ok(nf) => {
                let ghost snf = nf@;
                state.frames.push(nf);
                proof {
                    assert(state@.frames =~= caller_frames.push(snf));
                }
                StepOutcome::Continue
            },
            Err(t) => StepOutcome::Trap(t),
        }
    } else if cat == 1 {
        match exec_step_local_op(frame, op) {
            Ok(nf) => {
                let ghost snf = nf@;
                state.frames.push(nf);
                proof {
                    assert(state@.frames =~= caller_frames.push(snf));
                }
                StepOutcome::Continue
            },
            Err(t) => StepOutcome::Trap(t),
        }
    } else if cat == 2 {
        match exec_step_global_op(inst, frame, op) {
            Ok(nf) => {
                let ghost snf = nf@;
                state.frames.push(nf);
                proof {
                    assert(state@.frames =~= caller_frames.push(snf));
                }
                StepOutcome::Continue
            },
            Err(t) => StepOutcome::Trap(t),
        }
    } else if cat == 3 {
        match exec_step_memory_op(inst, frame, op) {
            Ok(nf) => {
                let ghost snf = nf@;
                state.frames.push(nf);
                proof {
                    assert(state@.frames =~= caller_frames.push(snf));
                }
                StepOutcome::Continue
            },
            Err(t) => StepOutcome::Trap(t),
        }
    } else {
        exec_step_ctrl_op(module, inst, state, frame, op)
    }
}

pub open spec fn spec_wasm_run_steps(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    state: SpecWasmExecState,
    fuel: nat,
) -> (SpecWasmInstance, SpecWasmOutcome)
    decreases fuel,
{
    if fuel == 0 {
        (inst, SpecWasmOutcome::OutOfFuel)
    } else {
        let (next_inst, next_state, step_out) = spec_wasm_step(module, inst, state);
        match step_out {
            SpecStepOutcome::Continue =>
                spec_wasm_run_steps(module, next_inst, next_state, (fuel - 1) as nat),
            SpecStepOutcome::Done(vals) => (next_inst, SpecWasmOutcome::Done(vals)),
            SpecStepOutcome::Trap(t) => (next_inst, SpecWasmOutcome::Trap(t)),
            SpecStepOutcome::Unsupported(code) => (next_inst, SpecWasmOutcome::Unsupported(code)),
        }
    }
}

pub open spec fn spec_wasm_invoke(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    func_idx: u32,
    args: Seq<WasmVal>,
    fuel: nat,
) -> (SpecWasmInstance, SpecWasmOutcome) {
    if (func_idx as nat) >= module.funcs.len() || (func_idx as nat) > usize::MAX as nat {
        (inst, SpecWasmOutcome::Trap(WasmTrap::InvalidFunctionIndex))
    } else {
        match spec_build_callee_frame(module, func_idx as usize, args) {
            Err(t) => (inst, SpecWasmOutcome::Trap(t)),
            Ok(entry_frame) => {
                let init_state = SpecWasmExecState { frames: seq![entry_frame] };
                spec_wasm_run_steps(module, inst, init_state, fuel)
            },
        }
    }
}

proof fn lemma_unfold_wasm_run_steps(
    module: SpecWasmModule,
    pre_inst: SpecWasmInstance,
    pre_state: SpecWasmExecState,
    fuel: nat,
)
    requires
        fuel > 0,
    ensures
        spec_wasm_run_steps(module, pre_inst, pre_state, fuel) == ({
            let (next_inst, next_state, s_out) = spec_wasm_step(module, pre_inst, pre_state);
            match s_out {
                SpecStepOutcome::Continue =>
                    spec_wasm_run_steps(module, next_inst, next_state, (fuel - 1) as nat),
                SpecStepOutcome::Done(vals) => (next_inst, SpecWasmOutcome::Done(vals)),
                SpecStepOutcome::Trap(t) => (next_inst, SpecWasmOutcome::Trap(t)),
                SpecStepOutcome::Unsupported(code) => (next_inst, SpecWasmOutcome::Unsupported(code)),
            }
        }),
{
    hide(spec_wasm_step);
}

#[verifier::spinoff_prover]
pub fn wasm_run_steps(
    module: &WasmModule,
    inst: &mut WasmInstance,
    state: &mut WasmExecState,
    fuel: u64,
) -> (out: WasmOutcome)
    requires
        old(inst)@.wf(),
    ensures
        ({
            let (s_inst, s_out) = spec_wasm_run_steps(module@, old(inst)@, old(state)@, fuel as nat);
            final(inst)@ == s_inst && out@ == s_out && final(inst)@.wf()
        }),
{
    let mut rem: u64 = fuel;
    while rem > 0
        invariant
            rem <= fuel,
            inst@.wf(),
            spec_wasm_run_steps(module@, old(inst)@, old(state)@, fuel as nat)
                == spec_wasm_run_steps(module@, inst@, state@, rem as nat),
        decreases rem,
    {
        let ghost pre_inst = inst@;
        let ghost pre_state = state@;
        let step_out = wasm_step(module, inst, state);
        proof {
            lemma_unfold_wasm_run_steps(module@, pre_inst, pre_state, rem as nat);
        }
        match step_out {
            StepOutcome::Continue => {
                rem = rem - 1;
            },
            StepOutcome::Done(vals) => {
                return WasmOutcome::Done(vals);
            },
            StepOutcome::Trap(t) => {
                return WasmOutcome::Trap(t);
            },
            StepOutcome::Unsupported(code) => {
                return WasmOutcome::Unsupported(code);
            },
        }
    }
    WasmOutcome::OutOfFuel
}

#[verifier::spinoff_prover]
pub fn wasm_invoke(
    module: &WasmModule,
    inst: &mut WasmInstance,
    func_idx: u32,
    args: &[WasmVal],
    fuel: u64,
) -> (out: WasmOutcome)
    requires
        old(inst)@.wf(),
    ensures
        ({
            let (s_inst, s_out) = spec_wasm_invoke(module@, old(inst)@, func_idx, args@, fuel as nat);
            final(inst)@ == s_inst && out@ == s_out && final(inst)@.wf()
        }),
{
    if (func_idx as u64) >= (module.funcs.len() as u64) {
        return WasmOutcome::Trap(WasmTrap::InvalidFunctionIndex);
    }
    let entry_frame = match build_callee_frame(module, func_idx as usize, args) {
        Ok(f) => f,
        Err(t) => return WasmOutcome::Trap(t),
    };
    let ghost sf = entry_frame@;
    let mut frames: Vec<CallFrame> = Vec::with_capacity(16);
    frames.push(entry_frame);
    let mut state = WasmExecState { frames };
    proof {
        assert(state@.frames =~= seq![sf]);
    }
    wasm_run_steps(module, inst, &mut state, fuel)
}

/// Convenience exported-function lookup & invocation (`exec` wrapper around `wasm_invoke`).
pub fn invoke_export_by_name(
    module: &WasmModule,
    inst: &mut WasmInstance,
    name: &[u8],
    args: &[WasmVal],
    fuel: u64,
) -> (out: Result<WasmOutcome, WasmTrap>)
    requires
        old(inst)@.wf(),
    ensures
        final(inst)@.wf(),
{
    let n = module.exports.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == module.exports@.len(),
            inst@ == old(inst)@,
            inst@.wf(),
        decreases n - i,
    {
        let exp = &module.exports[i];
        if matches!(exp.kind, ExportKind::Func) && bytes_eq(&exp.name, name) {
            let res = wasm_invoke(module, inst, exp.index, args, fuel);
            return Ok(res);
        }
        i = i + 1;
    }
    Err(WasmTrap::InvalidFunctionIndex)
}

/// Exported global value reader (`get` action in `.wast` scripts).
pub fn get_export_global_by_name(
    module: &WasmModule,
    inst: &WasmInstance,
    name: &[u8],
) -> (out: Result<WasmVal, WasmTrap>) {
    let n = module.exports.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == module.exports@.len(),
        decreases n - i,
    {
        let exp = &module.exports[i];
        if matches!(exp.kind, ExportKind::Global) && bytes_eq(&exp.name, name) {
            if (exp.index as u64) >= (inst.globals.len() as u64) {
                return Err(WasmTrap::InvalidGlobalIndex);
            }
            return Ok(inst.globals[exp.index as usize]);
        }
        i = i + 1;
    }
    Err(WasmTrap::InvalidGlobalIndex)
}

fn bytes_eq(a: &[u8], b: &[u8]) -> (eq: bool)
    ensures
        eq == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i as int ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

// ===========================================================================
// 10. Machine-Checked WebAssembly Sandbox Containment Theorems
// ===========================================================================

/// Theorem 1 (Out-of-Bounds Memory Containment):
/// Every load or store whose mathematical effective address `((addr as u32) as nat) + (offset as nat) + width`
/// exceeds `inst.memory.len()` (or targets an instance without memory) deterministically traps with
/// `WasmTrap::OutOfBoundsMemoryAccess` and leaves `inst` (and `inst.memory`) completely unchanged.
pub proof fn lemma_mem_access_oob_traps_cleanly(
    inst: SpecWasmInstance,
    load_kind: LoadKind,
    store_kind: StoreKind,
    offset: u32,
    addr: i32,
    val: WasmVal,
)
    ensures
        (!inst.has_memory
            || spec_effective_addr(addr, offset) + spec_load_width(load_kind) > inst.memory.len())
            ==> spec_mem_load(inst, load_kind, offset, addr)
                == Err::<WasmVal, WasmTrap>(WasmTrap::OutOfBoundsMemoryAccess),
        (!inst.has_memory
            || spec_effective_addr(addr, offset) + spec_store_width(store_kind) > inst.memory.len())
            ==> spec_mem_store(inst, store_kind, offset, addr, val)
                == Err::<SpecWasmInstance, WasmTrap>(WasmTrap::OutOfBoundsMemoryAccess),
{
}

/// Corollary at the full VM step level: when the top frame executes `MemLoad` or `MemStore`
/// with an out-of-bounds effective address, `spec_wasm_step` deterministically traps with
/// `WasmTrap::OutOfBoundsMemoryAccess` and leaves `inst.memory` byte-for-byte identical.
pub proof fn lemma_wasm_step_oob_mem_traps_unchanged(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    state: SpecWasmExecState,
)
    ensures
        ({
            let (next_inst, _next_state, out) = spec_wasm_step(module, inst, state);
            state.frames.len() > 0 ==> ({
                let frame = state.frames.last();
                (frame.func_idx as nat) < module.funcs.len()
                && (frame.pc as nat) < module.funcs[frame.func_idx as int].ops.len()
                ==> match module.funcs[frame.func_idx as int].ops[frame.pc as int] {
                    WasmOp::MemLoad { load_kind, offset } => {
                        match spec_pop_i32(frame.stack) {
                            Ok((_, addr)) => {
                                (!inst.has_memory
                                    || spec_effective_addr(addr, offset) + spec_load_width(load_kind) > inst.memory.len())
                                ==> (out == SpecStepOutcome::Trap(WasmTrap::OutOfBoundsMemoryAccess)
                                     && next_inst == inst)
                            },
                            Err(_) => next_inst == inst,
                        }
                    },
                    WasmOp::MemStore { store_kind, offset } => {
                        match spec_pop_val(frame.stack) {
                            Ok((s1, _val)) => match spec_pop_i32(s1) {
                                Ok((_, addr)) => {
                                    (!inst.has_memory
                                        || spec_effective_addr(addr, offset) + spec_store_width(store_kind) > inst.memory.len())
                                    ==> (out == SpecStepOutcome::Trap(WasmTrap::OutOfBoundsMemoryAccess)
                                         && next_inst == inst)
                                },
                                Err(_) => next_inst == inst,
                            },
                            Err(_) => next_inst == inst,
                        }
                    },
                    _ => true,
                }
            })
        }),
{
}

/// Theorem 2 (In-Bounds Linear Memory Store Framing):
/// Any successful store preserves `inst.wf()`, preserves `inst.memory.len()`,
/// keeps `inst.max_pages` invariant, and modifies ONLY bytes within `[ea, ea + width)`.
pub proof fn lemma_mem_store_in_bounds_framing(
    inst: SpecWasmInstance,
    kind: StoreKind,
    offset: u32,
    addr: i32,
    val: WasmVal,
)
    requires
        inst.wf(),
    ensures
        match spec_mem_store(inst, kind, offset, addr, val) {
            Ok(next_inst) => {
                let ea = spec_effective_addr(addr, offset);
                let w = spec_store_width(kind);
                &&& inst.has_memory
                &&& ea + w <= inst.memory.len()
                &&& next_inst.wf()
                &&& next_inst.memory.len() == inst.memory.len()
                &&& next_inst.mem_pages == inst.mem_pages
                &&& next_inst.max_pages == inst.max_pages
                &&& (forall|j: int|
                    (0 <= j < ea as int || (ea + w) as int <= j < inst.memory.len() as int)
                    ==> #[trigger] next_inst.memory[j] == inst.memory[j])
            },
            Err(_) => true,
        },
{
}

/// Theorem 3 (Single-Step Sandbox Containment):
/// For ANY untrusted `SpecWasmModule`, ANY well-formed `SpecWasmInstance`, and ANY execution state,
/// one step of Wasm execution (`spec_wasm_step`):
///   (a) preserves the full sandbox invariant `next_inst.wf()`,
///   (b) keeps `next_inst.max_pages == inst.max_pages` and `next_inst.has_memory == inst.has_memory`,
///   (c) keeps `next_inst.memory.len() <= (inst.max_pages as nat) * WASM_PAGE_SIZE`,
///   (d) monotonically preserves or grows `next_inst.mem_pages >= inst.mem_pages`,
///   (e) leaves `next_inst.memory == inst.memory` whenever `spec_wasm_step` traps or hits unsupported.
#[verifier::spinoff_prover]
pub proof fn lemma_wasm_step_sandbox_containment(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    state: SpecWasmExecState,
)
    requires
        inst.wf(),
    ensures
        ({
            let (next_inst, _next_state, out) = spec_wasm_step(module, inst, state);
            &&& next_inst.wf()
            &&& next_inst.has_memory == inst.has_memory
            &&& next_inst.max_pages == inst.max_pages
            &&& next_inst.mem_pages >= inst.mem_pages
            &&& next_inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)
            &&& (match out {
                SpecStepOutcome::Trap(_) | SpecStepOutcome::Unsupported(_) =>
                    next_inst.memory == inst.memory && next_inst.mem_pages == inst.mem_pages,
                _ => true,
            })
        }),
{
    let (next_inst, _next_state, out) = spec_wasm_step(module, inst, state);
    if state.frames.len() > 0 {
        let frame = state.frames.last();
        if (frame.func_idx as nat) < module.funcs.len() {
            let fbody = module.funcs[frame.func_idx as int];
            if (frame.pc as nat) < fbody.ops.len() {
                let op = fbody.ops[frame.pc as int];
                if spec_op_category(op) == 3 {
                    if let WasmOp::MemoryGrow = op {
                        if frame.pc < usize::MAX {
                            if let Ok((_s1, delta)) = spec_pop_i32(frame.stack) {
                                if inst.has_memory {
                                    let delta_u32 = 0u32.wrapping_add_signed(delta);
                                    let old_pages = inst.mem_pages;
                                    if (old_pages as nat) + (delta_u32 as nat) <= (inst.max_pages as nat)
                                        && (old_pages as nat) + (delta_u32 as nat) <= (MAX_SANDBOX_PAGES as nat)
                                    {
                                        let new_pages = (old_pages + delta_u32) as u32;
                                        let extra_bytes = (delta_u32 as nat) * (WASM_PAGE_SIZE as nat);
                                        assert(inst.memory.len() + extra_bytes
                                            == (new_pages as nat) * (WASM_PAGE_SIZE as nat)) by (nonlinear_arith)
                                            requires
                                                inst.memory.len() == (old_pages as nat) * (WASM_PAGE_SIZE as nat),
                                                extra_bytes == (delta_u32 as nat) * (WASM_PAGE_SIZE as nat),
                                                new_pages as nat == (old_pages as nat) + (delta_u32 as nat);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert(next_inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)) by (nonlinear_arith)
        requires
            next_inst.memory.len() == (next_inst.mem_pages as nat) * (WASM_PAGE_SIZE as nat),
            next_inst.mem_pages <= next_inst.max_pages,
            next_inst.max_pages == inst.max_pages;
}

/// Inductive multi-step containment lemma over `fuel`.
pub proof fn lemma_wasm_run_steps_sandbox_containment(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    state: SpecWasmExecState,
    fuel: nat,
)
    requires
        inst.wf(),
    ensures
        ({
            let (final_inst, _outcome) = spec_wasm_run_steps(module, inst, state, fuel);
            &&& final_inst.wf()
            &&& final_inst.has_memory == inst.has_memory
            &&& final_inst.max_pages == inst.max_pages
            &&& final_inst.mem_pages >= inst.mem_pages
            &&& final_inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)
        }),
    decreases fuel,
{
    if fuel == 0 {
        assert(inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)) by (nonlinear_arith)
            requires
                inst.memory.len() == (inst.mem_pages as nat) * (WASM_PAGE_SIZE as nat),
                inst.mem_pages <= inst.max_pages;
    } else {
        lemma_wasm_step_sandbox_containment(module, inst, state);
        let (next_inst, next_state, step_out) = spec_wasm_step(module, inst, state);
        if let SpecStepOutcome::Continue = step_out {
            lemma_wasm_run_steps_sandbox_containment(module, next_inst, next_state, (fuel - 1) as nat);
        }
    }
}

/// Top-Level Machine-Checked WebAssembly Sandbox Containment Theorem:
/// For ANY untrusted `SpecWasmModule`, ANY well-formed `SpecWasmInstance`, ANY `func_idx`,
/// ANY untrusted `args`, and ANY `fuel`:
///   1. `spec_wasm_invoke` (which `wasm_invoke` implements identically) terminates within `fuel` steps;
///   2. `final_inst.wf()` holds unconditionally;
///   3. `final_inst.max_pages == inst.max_pages` and `final_inst.memory.len() <= max_pages * 65536`;
///   4. combined with `lemma_mem_access_oob_traps_cleanly`, `lemma_wasm_step_oob_mem_traps_unchanged`,
///      and `#![forbid(unsafe_code)]`, untrusted Wasm code can NEVER read or write outside
///      `0 .. instance.memory.len()` and has zero ambient host access.
pub proof fn theorem_wasm_invoke_sandbox_containment(
    module: SpecWasmModule,
    inst: SpecWasmInstance,
    func_idx: u32,
    args: Seq<WasmVal>,
    fuel: nat,
)
    requires
        inst.wf(),
    ensures
        ({
            let (final_inst, _outcome) = spec_wasm_invoke(module, inst, func_idx, args, fuel);
            &&& final_inst.wf()
            &&& final_inst.has_memory == inst.has_memory
            &&& final_inst.max_pages == inst.max_pages
            &&& final_inst.mem_pages >= inst.mem_pages
            &&& final_inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)
        }),
{
    assert(inst.memory.len() <= (inst.max_pages as nat) * (WASM_PAGE_SIZE as nat)) by (nonlinear_arith)
        requires
            inst.memory.len() == (inst.mem_pages as nat) * (WASM_PAGE_SIZE as nat),
            inst.mem_pages <= inst.max_pages;
    if (func_idx as nat) < module.funcs.len() && (func_idx as nat) <= usize::MAX as nat {
        if let Ok(entry_frame) = spec_build_callee_frame(module, func_idx as usize, args) {
            let init_state = SpecWasmExecState { frames: seq![entry_frame] };
            lemma_wasm_run_steps_sandbox_containment(module, inst, init_state, fuel);
        }
    }
}

/// End-to-end verified untrusted-binary sandbox entrypoint:
/// Decodes raw untrusted Wasm 1.0 bytes, instantiates the sandbox, and invokes `func_idx`
/// with `fuel`, guaranteeing termination, well-formedness, and `memory.len() <= max_pages * 65536`.
pub fn run_sandboxed_wasm_bytes(
    wasm_bytes: &[u8],
    func_idx: u32,
    args: &[WasmVal],
    fuel: u64,
) -> (r: Result<(WasmInstance, WasmOutcome), WasmTrap>)
    ensures
        match r {
            Ok((final_inst, _outcome)) =>
                final_inst@.wf()
                    && final_inst@.memory.len() <= (final_inst@.max_pages as nat) * (WASM_PAGE_SIZE as nat)
                    && final_inst@.max_pages <= MAX_SPEC_PAGES,
            Err(_) => true,
        },
{
    let module = match crate::binary::decode_module(wasm_bytes) {
        Ok(m) => m,
        Err(_) => return Err(WasmTrap::Unreachable),
    };
    let mut inst = instantiate_module(&module)?;
    let ghost init_inst = inst@;
    let out = wasm_invoke(&module, &mut inst, func_idx, args, fuel);
    proof {
        theorem_wasm_invoke_sandbox_containment(module@, init_inst, func_idx, args@, fuel as nat);
    }
    Ok((inst, out))
}

} // verus!
