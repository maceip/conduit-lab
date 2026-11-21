//! ECMAScript Generators (§27.5) & Async Continuation Frames (§27.7.5), formally verified in Verus.
//!
//! Machine-checked invariants:
//! 1. **Generator State Machine (§27.5.2 / §27.5.3)**:
//!    - States: `SuspendedStart`, `SuspendedYield { pc, locals }`, `Executing`, `Completed`.
//!    - **`Completed` is absorbing**: once a generator reaches `Completed`, no `.next(v)`,
//!      `.return(v)`, or `.throw(e)` transition can ever move it out of `Completed`.
//!    - **Re-entrancy safety (`GeneratorValidate` §27.5.3.2)**: attempting to re-enter an
//!      `Executing` generator via `.next`, `.return`, or `.throw` ALWAYS returns
//!      `Err(JsError::TypeError)` and leaves the generator state untouched.
//! 2. **Async Continuation State Machine (§27.7.5)**:
//!    - States: `SuspendedStart`, `SuspendedAwait { pc, locals }`, `Executing`, `Completed`.
//!    - `Await` suspends the frame into `SuspendedAwait { pc, locals }` and yields control back to
//!      the Promise microtask queue (`promise_jobs.rs`), which resumes the frame once settled.
use vstd::prelude::*;

verus! {

use crate::types::{JsError, JsVal, PromiseId};

// -----------------------------------------------------------------------------------------------
// Iterator Result Record (§7.4.8 `CreateIterResultObject`)
// -----------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct IterResult {
    pub value: JsVal,
    pub done: bool,
}

// -----------------------------------------------------------------------------------------------
// Generator State Machine (§27.5)
// -----------------------------------------------------------------------------------------------

/// Abstract state tag for crisp specification of state-transition invariants.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GenStateTag {
    SuspendedStart,
    SuspendedYield,
    Executing,
    Completed,
}

/// Concrete `[[GeneratorState]]` internal slot (§27.5.2).
pub enum GeneratorState {
    SuspendedStart,
    SuspendedYield { pc: usize, locals: Vec<JsVal> },
    Executing,
    Completed,
}

impl GeneratorState {
    pub open spec fn tag(&self) -> GenStateTag {
        match self {
            GeneratorState::SuspendedStart => GenStateTag::SuspendedStart,
            GeneratorState::SuspendedYield { .. } => GenStateTag::SuspendedYield,
            GeneratorState::Executing => GenStateTag::Executing,
            GeneratorState::Completed => GenStateTag::Completed,
        }
    }
}

/// Generator frame instruction set (fuel-bounded so loops inside generator bodies always terminate).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GenOp {
    /// `locals[dst] = val`
    Const { dst: usize, val: JsVal },
    /// `locals[dst] = locals[src]`
    Copy { dst: usize, src: usize },
    /// `locals[dst] = locals[src] + delta` (for `JsVal::Int`)
    AddInt { dst: usize, src: usize, delta: i64 },
    /// `locals[resume_dst] = yield locals[src]`
    Yield { src: usize, resume_dst: usize },
    /// `return locals[src]`
    Return { src: usize },
    /// `throw locals[src]`
    Throw { src: usize },
    /// Unconditional branch to `target_pc`
    Jump { target_pc: usize },
    /// Branch to `target_pc` when `locals[cond_slot] == JsVal::Int(0)` or `JsVal::Bool(false)`
    JumpIfZero { cond_slot: usize, target_pc: usize },
    /// Re-entrancy probe (`g.next()` / `g.return()` / `g.throw()` invoked while `g` is `Executing`,
    /// matching `test262/built-ins/GeneratorPrototype/*/from-state-executing.js`).
    SelfReenterProbe,
}

/// Optional `try`/`catch`/`finally` region covering `[start_pc, end_pc)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TryRegion {
    pub start_pc: usize,
    pub end_pc: usize,
    pub catch_pc: Option<usize>,
    pub catch_err_slot: usize,
    pub finally_pc: Option<usize>,
}

/// Generator exotic instance (§27.5.2).
pub struct GeneratorObject {
    pub state: GeneratorState,
    pub code: Vec<GenOp>,
    pub try_regions: Vec<TryRegion>,
    pub locals_count: usize,
    pub initial_arg: JsVal,
    /// When suspended at `Yield`, records which local slot receives the next `.next(v)` argument.
    pub pending_resume_slot: Option<usize>,
    /// Persisted abrupt `Return(v)` completion across any `yield` expressions inside `finally` (§14.15.3 / §27.5.3.4).
    pub pending_finally_return: Option<JsVal>,
}

pub fn clone_jsval_vec(v: &Vec<JsVal>) -> (out: Vec<JsVal>)
    ensures
        out@ == v@,
{
    let n = v.len();
    let mut out: Vec<JsVal> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == v@.len(),
            out@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> out@[k] == v@[k],
        decreases n - i,
    {
        out.push(v[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= v@);
    }
    out
}

pub fn make_locals(count: usize, arg0: JsVal) -> (locals: Vec<JsVal>)
    ensures
        locals@.len() == count as int,
{
    let mut locals: Vec<JsVal> = Vec::new();
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            locals@.len() == i as int,
        decreases count - i,
    {
        if i == 0 {
            locals.push(arg0);
        } else {
            locals.push(JsVal::Undefined);
        }
        i += 1;
    }
    locals
}

fn read_local(locals: &Vec<JsVal>, slot: usize) -> JsVal {
    if slot < locals.len() {
        locals[slot]
    } else {
        JsVal::Undefined
    }
}

fn write_local(locals: &mut Vec<JsVal>, slot: usize, val: JsVal)
    ensures
        final(locals)@.len() == old(locals)@.len(),
{
    if slot < locals.len() {
        locals.set(slot, val);
    }
}

/// Find innermost enclosing `TryRegion` covering `pc` (`start_pc <= pc < end_pc`).
fn find_enclosing_catch(regions: &Vec<TryRegion>, pc: usize) -> Option<(usize, usize)> {
    let n = regions.len();
    let mut i: usize = 0;
    let mut best: Option<(usize, usize)> = None;
    while i < n
        invariant
            i <= n,
            n == regions@.len(),
        decreases n - i,
    {
        let reg = regions[i];
        if reg.start_pc <= pc && pc < reg.end_pc {
            if let Some(cpc) = reg.catch_pc {
                best = Some((cpc, reg.catch_err_slot));
            }
        }
        i += 1;
    }
    best
}

fn find_enclosing_finally(regions: &Vec<TryRegion>, pc: usize) -> Option<usize> {
    let n = regions.len();
    let mut i: usize = 0;
    let mut best: Option<usize> = None;
    while i < n
        invariant
            i <= n,
            n == regions@.len(),
        decreases n - i,
    {
        let reg = regions[i];
        if reg.start_pc <= pc && pc < reg.end_pc {
            if let Some(fpc) = reg.finally_pc {
                best = Some(fpc);
            }
        }
        i += 1;
    }
    best
}

impl GeneratorObject {
    pub fn new(
        code: Vec<GenOp>,
        try_regions: Vec<TryRegion>,
        locals_count: usize,
        initial_arg: JsVal,
    ) -> (g: Self)
        ensures
            g.state.tag() == GenStateTag::SuspendedStart,
    {
        GeneratorObject {
            state: GeneratorState::SuspendedStart,
            code,
            try_regions,
            locals_count,
            initial_arg,
            pending_resume_slot: None,
            pending_finally_return: None,
        }
    }
}

/// ECMA-262 §27.5.3.2 `GeneratorValidate(generator, generatorBrand)`:
/// If `generator.[[GeneratorState]]` is `executing`, throw a `TypeError` exception!
pub fn generator_validate(gen_obj: &GeneratorObject) -> (res: Result<GenStateTag, JsError>)
    ensures
        match res {
            Ok(tag) => tag == gen_obj.state.tag() && tag != GenStateTag::Executing,
            Err(e) => e == JsError::TypeError && gen_obj.state.tag() == GenStateTag::Executing,
        },
{
    match &gen_obj.state {
        GeneratorState::Executing => Err(JsError::TypeError),
        GeneratorState::SuspendedStart => Ok(GenStateTag::SuspendedStart),
        GeneratorState::SuspendedYield { .. } => Ok(GenStateTag::SuspendedYield),
        GeneratorState::Completed => Ok(GenStateTag::Completed),
    }
}

/// Internal step loop executing a generator body while `gen_obj.state` is `Executing`.
fn run_generator_from(
    gen_obj: &mut GeneratorObject,
    mut pc: usize,
    mut locals: Vec<JsVal>,
    mut step_fuel: usize,
) -> (res: Result<IterResult, JsError>)
    requires
        old(gen_obj).state.tag() == GenStateTag::Executing,
    ensures
        final(gen_obj).state.tag() == GenStateTag::SuspendedYield
            || final(gen_obj).state.tag() == GenStateTag::Completed,
        match res {
            Ok(ir) => {
                (ir.done ==> final(gen_obj).state.tag() == GenStateTag::Completed)
                && (!ir.done ==> final(gen_obj).state.tag() == GenStateTag::SuspendedYield)
            },
            Err(_) => final(gen_obj).state.tag() == GenStateTag::Completed,
        },
{
    while pc < gen_obj.code.len()
        invariant
            gen_obj.state.tag() == GenStateTag::Executing,
        decreases step_fuel,
    {
        if step_fuel == 0 {
            gen_obj.state = GeneratorState::Completed;
            gen_obj.pending_resume_slot = None;
            gen_obj.pending_finally_return = None;
            return Err(JsError::QuotaExceeded);
        }
        step_fuel -= 1;
        let op = gen_obj.code[pc];
        match op {
            GenOp::Const { dst, val } => {
                write_local(&mut locals, dst, val);
                pc += 1;
            },
            GenOp::Copy { dst, src } => {
                let v = read_local(&locals, src);
                write_local(&mut locals, dst, v);
                pc += 1;
            },
            GenOp::AddInt { dst, src, delta } => {
                let cur = read_local(&locals, src);
                let next_v = match cur {
                    JsVal::Int(x) => JsVal::Int(x.wrapping_add(delta)),
                    _ => JsVal::Int(delta),
                };
                write_local(&mut locals, dst, next_v);
                pc += 1;
            },
            GenOp::Yield { src, resume_dst } => {
                let yielded = read_local(&locals, src);
                gen_obj.pending_resume_slot = Some(resume_dst);
                // Note: `gen_obj.pending_finally_return` stays preserved on `gen_obj` across yields inside `finally`!
                gen_obj.state = GeneratorState::SuspendedYield {
                    pc: pc + 1,
                    locals,
                };
                return Ok(IterResult { value: yielded, done: false });
            },
            GenOp::Return { src } => {
                // Explicit `return` inside `finally` overrides any earlier `pending_finally_return` (§14.15.3)
                let ret_v = read_local(&locals, src);
                gen_obj.pending_resume_slot = None;
                gen_obj.pending_finally_return = None;
                gen_obj.state = GeneratorState::Completed;
                return Ok(IterResult { value: ret_v, done: true });
            },
            GenOp::Throw { src } => {
                let err_v = read_local(&locals, src);
                match find_enclosing_catch(&gen_obj.try_regions, pc) {
                    Some((catch_pc, err_slot)) => {
                        write_local(&mut locals, err_slot, err_v);
                        pc = catch_pc;
                    },
                    None => {
                        gen_obj.pending_resume_slot = None;
                        gen_obj.pending_finally_return = None;
                        gen_obj.state = GeneratorState::Completed;
                        return Err(JsError::Thrown(err_v));
                    },
                }
            },
            GenOp::Jump { target_pc } => {
                pc = target_pc;
            },
            GenOp::JumpIfZero { cond_slot, target_pc } => {
                let cv = read_local(&locals, cond_slot);
                if matches!(cv, JsVal::Int(0) | JsVal::Bool(false) | JsVal::Undefined | JsVal::Null) {
                    pc = target_pc;
                } else {
                    pc += 1;
                }
            },
            GenOp::SelfReenterProbe => {
                // Re-entering `gen_obj` while `gen_obj.state == Executing` MUST fail `GeneratorValidate` with TypeError!
                let check = generator_validate(gen_obj);
                match check {
                    Err(JsError::TypeError) => {
                        match find_enclosing_catch(&gen_obj.try_regions, pc) {
                            Some((catch_pc, err_slot)) => {
                                write_local(&mut locals, err_slot, JsVal::Int(-1));
                                pc = catch_pc;
                            },
                            None => {
                                gen_obj.pending_resume_slot = None;
                                gen_obj.pending_finally_return = None;
                                gen_obj.state = GeneratorState::Completed;
                                return Err(JsError::TypeError);
                            },
                        }
                    },
                    _ => {
                        proof { assert(false); }
                        gen_obj.pending_finally_return = None;
                        gen_obj.state = GeneratorState::Completed;
                        return Err(JsError::TypeError);
                    },
                }
            },
        }
    }

    let pending_ret = gen_obj.pending_finally_return;
    gen_obj.pending_finally_return = None;
    gen_obj.pending_resume_slot = None;
    gen_obj.state = GeneratorState::Completed;
    match pending_ret {
        Some(rv) => Ok(IterResult { value: rv, done: true }),
        None => Ok(IterResult { value: JsVal::Undefined, done: true }),
    }
}

/// ECMA-262 §27.5.1.2 / §27.5.3.3 `Generator.prototype.next(value)` / `GeneratorResume`.
pub fn generator_next(
    gen_obj: &mut GeneratorObject,
    resume_val: JsVal,
    step_fuel: usize,
) -> (res: Result<IterResult, JsError>)
    ensures
        // (1) Re-entering an `Executing` generator ALWAYS throws `TypeError` and leaves state `Executing`
        old(gen_obj).state.tag() == GenStateTag::Executing ==> (
            res == Err::<IterResult, JsError>(JsError::TypeError)
            && final(gen_obj).state.tag() == GenStateTag::Executing
        ),
        // (2) `Completed` is absorbing and returns `{ value: undefined, done: true }`
        old(gen_obj).state.tag() == GenStateTag::Completed ==> (
            res == Ok::<IterResult, JsError>(IterResult { value: JsVal::Undefined, done: true })
            && final(gen_obj).state.tag() == GenStateTag::Completed
        ),
        // (3) Valid suspended transition never leaves generator stuck in `Executing`
        old(gen_obj).state.tag() != GenStateTag::Executing ==> (
            final(gen_obj).state.tag() == GenStateTag::SuspendedYield
            || final(gen_obj).state.tag() == GenStateTag::Completed
        ),
{
    let tag = generator_validate(gen_obj)?;
    if matches!(tag, GenStateTag::Completed) {
        return Ok(IterResult { value: JsVal::Undefined, done: true });
    }
    let (start_pc, mut locals) = match &gen_obj.state {
        GeneratorState::SuspendedStart => {
            (0usize, make_locals(gen_obj.locals_count, gen_obj.initial_arg))
        },
        GeneratorState::SuspendedYield { pc, locals: saved } => {
            (*pc, clone_jsval_vec(saved))
        },
        _ => {
            proof { assert(false); }
            (0usize, Vec::new())
        },
    };
    if matches!(tag, GenStateTag::SuspendedYield) {
        if let Some(dst) = gen_obj.pending_resume_slot {
            write_local(&mut locals, dst, resume_val);
        }
    }
    gen_obj.pending_resume_slot = None;
    gen_obj.state = GeneratorState::Executing;
    run_generator_from(gen_obj, start_pc, locals, step_fuel)
}

/// ECMA-262 §27.5.1.3 / §27.5.3.4 `Generator.prototype.return(value)` / `GeneratorResumeAbrupt(Return(value))`.
pub fn generator_return(
    gen_obj: &mut GeneratorObject,
    ret_val: JsVal,
    step_fuel: usize,
) -> (res: Result<IterResult, JsError>)
    ensures
        // (1) Re-entering an `Executing` generator ALWAYS throws `TypeError` and leaves state `Executing`
        old(gen_obj).state.tag() == GenStateTag::Executing ==> (
            res == Err::<IterResult, JsError>(JsError::TypeError)
            && final(gen_obj).state.tag() == GenStateTag::Executing
        ),
        // (2) `Completed` is absorbing and returns `{ value: ret_val, done: true }`
        old(gen_obj).state.tag() == GenStateTag::Completed ==> (
            res == Ok::<IterResult, JsError>(IterResult { value: ret_val, done: true })
            && final(gen_obj).state.tag() == GenStateTag::Completed
        ),
        // (3) `SuspendedStart` transitions directly to `Completed` and returns `{ value: ret_val, done: true }`
        old(gen_obj).state.tag() == GenStateTag::SuspendedStart ==> (
            res == Ok::<IterResult, JsError>(IterResult { value: ret_val, done: true })
            && final(gen_obj).state.tag() == GenStateTag::Completed
        ),
        old(gen_obj).state.tag() != GenStateTag::Executing ==> (
            final(gen_obj).state.tag() == GenStateTag::SuspendedYield
            || final(gen_obj).state.tag() == GenStateTag::Completed
        ),
{
    let tag = generator_validate(gen_obj)?;
    if matches!(tag, GenStateTag::Completed) {
        return Ok(IterResult { value: ret_val, done: true });
    }
    if matches!(tag, GenStateTag::SuspendedStart) {
        gen_obj.pending_resume_slot = None;
        gen_obj.pending_finally_return = None;
        gen_obj.state = GeneratorState::Completed;
        return Ok(IterResult { value: ret_val, done: true });
    }
    // `SuspendedYield`: check if suspended inside a `try ... finally` block!
    let (susp_pc, saved_locals) = match &gen_obj.state {
        GeneratorState::SuspendedYield { pc, locals } => (*pc, clone_jsval_vec(locals)),
        _ => {
            proof { assert(false); }
            (0usize, Vec::new())
        },
    };
    // Note `susp_pc` is `yield_pc + 1`, so check `susp_pc - 1` for enclosing `try ... finally`.
    let check_pc = if susp_pc > 0 { susp_pc - 1 } else { 0 };
    match find_enclosing_finally(&gen_obj.try_regions, check_pc) {
        Some(finally_pc) => {
            gen_obj.pending_resume_slot = None;
            gen_obj.pending_finally_return = Some(ret_val);
            gen_obj.state = GeneratorState::Executing;
            run_generator_from(gen_obj, finally_pc, saved_locals, step_fuel)
        },
        None => {
            gen_obj.pending_resume_slot = None;
            gen_obj.pending_finally_return = None;
            gen_obj.state = GeneratorState::Completed;
            Ok(IterResult { value: ret_val, done: true })
        },
    }
}

/// ECMA-262 §27.5.1.4 / §27.5.3.4 `Generator.prototype.throw(exception)` / `GeneratorResumeAbrupt(Throw(exception))`.
pub fn generator_throw(
    gen_obj: &mut GeneratorObject,
    err_val: JsVal,
    step_fuel: usize,
) -> (res: Result<IterResult, JsError>)
    ensures
        // (1) Re-entering an `Executing` generator ALWAYS throws `TypeError` and leaves state `Executing`
        old(gen_obj).state.tag() == GenStateTag::Executing ==> (
            res == Err::<IterResult, JsError>(JsError::TypeError)
            && final(gen_obj).state.tag() == GenStateTag::Executing
        ),
        // (2) `Completed` is absorbing and rethrows `Thrown(err_val)`
        old(gen_obj).state.tag() == GenStateTag::Completed ==> (
            res == Err::<IterResult, JsError>(JsError::Thrown(err_val))
            && final(gen_obj).state.tag() == GenStateTag::Completed
        ),
        // (3) `SuspendedStart` transitions to `Completed` and throws `Thrown(err_val)`
        old(gen_obj).state.tag() == GenStateTag::SuspendedStart ==> (
            res == Err::<IterResult, JsError>(JsError::Thrown(err_val))
            && final(gen_obj).state.tag() == GenStateTag::Completed
        ),
        old(gen_obj).state.tag() != GenStateTag::Executing ==> (
            final(gen_obj).state.tag() == GenStateTag::SuspendedYield
            || final(gen_obj).state.tag() == GenStateTag::Completed
        ),
{
    let tag = generator_validate(gen_obj)?;
    if matches!(tag, GenStateTag::Completed) {
        return Err(JsError::Thrown(err_val));
    }
    if matches!(tag, GenStateTag::SuspendedStart) {
        gen_obj.pending_resume_slot = None;
        gen_obj.pending_finally_return = None;
        gen_obj.state = GeneratorState::Completed;
        return Err(JsError::Thrown(err_val));
    }
    let (susp_pc, mut saved_locals) = match &gen_obj.state {
        GeneratorState::SuspendedYield { pc, locals } => (*pc, clone_jsval_vec(locals)),
        _ => {
            proof { assert(false); }
            (0usize, Vec::new())
        },
    };
    let check_pc = if susp_pc > 0 { susp_pc - 1 } else { 0 };
    match find_enclosing_catch(&gen_obj.try_regions, check_pc) {
        Some((catch_pc, err_slot)) => {
            write_local(&mut saved_locals, err_slot, err_val);
            gen_obj.pending_resume_slot = None;
            gen_obj.state = GeneratorState::Executing;
            run_generator_from(gen_obj, catch_pc, saved_locals, step_fuel)
        },
        None => {
            gen_obj.pending_resume_slot = None;
            gen_obj.pending_finally_return = None;
            gen_obj.state = GeneratorState::Completed;
            Err(JsError::Thrown(err_val))
        },
    }
}

// -----------------------------------------------------------------------------------------------
// Async Function Continuation State Machine (§27.7.5 `AsyncBlockStart` / `Await`)
// -----------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AsyncStateTag {
    SuspendedStart,
    SuspendedAwait,
    Executing,
    Completed,
}

pub enum AsyncState {
    SuspendedStart,
    SuspendedAwait { pc: usize, locals: Vec<JsVal> },
    Executing,
    Completed,
}

impl AsyncState {
    pub open spec fn tag(&self) -> AsyncStateTag {
        match self {
            AsyncState::SuspendedStart => AsyncStateTag::SuspendedStart,
            AsyncState::SuspendedAwait { .. } => AsyncStateTag::SuspendedAwait,
            AsyncState::Executing => AsyncStateTag::Executing,
            AsyncState::Completed => AsyncStateTag::Completed,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AsyncOp {
    Const { dst: usize, val: JsVal },
    AddInt { dst: usize, src: usize, delta: i64 },
    MulInt { dst: usize, src: usize, factor: i64 },
    /// Append `event_id` to runtime execution trace (verifies exact interleaving order vs V8!).
    EmitTrace { event_id: u32 },
    /// `locals[dst] = await locals[src]` (§27.7.5.3 `Await(value)`).
    Await { src: usize, dst: usize },
    /// `return locals[src]` — fulfills the async function's capability promise.
    Return { src: usize },
    /// `throw locals[src]` — rejects the async function's capability promise.
    Throw { src: usize },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AsyncStepOutcome {
    SuspendedOnAwait { awaited: JsVal, resume_dst: usize },
    Returned(JsVal),
    Threw(JsVal),
}

pub struct AsyncFrame {
    pub state: AsyncState,
    pub code: Vec<AsyncOp>,
    pub try_regions: Vec<TryRegion>,
    pub locals_count: usize,
    pub result_promise: PromiseId,
    pub step_budget: usize,
}

impl AsyncFrame {
    pub fn new(
        code: Vec<AsyncOp>,
        try_regions: Vec<TryRegion>,
        locals_count: usize,
        result_promise: PromiseId,
        step_budget: usize,
    ) -> (f: Self)
        ensures
            f.state.tag() == AsyncStateTag::SuspendedStart,
    {
        AsyncFrame {
            state: AsyncState::SuspendedStart,
            code,
            try_regions,
            locals_count,
            result_promise,
            step_budget,
        }
    }
}

/// Step an `AsyncFrame` from `SuspendedStart` or `SuspendedAwait` until it either suspends at
/// `Await` (returning `SuspendedOnAwait` so `PromiseRuntime` attaches reaction jobs) or settles
/// into `Completed` (`Returned` / `Threw`).
pub fn step_async_frame(
    frame: &mut AsyncFrame,
    resume_val: JsVal,
    resume_dst: usize,
    is_reject: bool,
    trace_log: &mut Vec<u32>,
) -> (res: Result<AsyncStepOutcome, JsError>)
    ensures
        // (1) Re-entering an `Executing` async frame throws `TypeError`
        old(frame).state.tag() == AsyncStateTag::Executing ==> (
            res == Err::<AsyncStepOutcome, JsError>(JsError::TypeError)
            && final(frame).state.tag() == AsyncStateTag::Executing
        ),
        // (2) `Completed` is absorbing
        old(frame).state.tag() == AsyncStateTag::Completed ==> (
            res == Err::<AsyncStepOutcome, JsError>(JsError::TypeError)
            && final(frame).state.tag() == AsyncStateTag::Completed
        ),
        // (3) Valid step either suspends on `Await` or completes (`Completed`)
        match res {
            Ok(AsyncStepOutcome::SuspendedOnAwait { .. }) =>
                final(frame).state.tag() == AsyncStateTag::SuspendedAwait,
            Ok(AsyncStepOutcome::Returned(_)) | Ok(AsyncStepOutcome::Threw(_)) =>
                final(frame).state.tag() == AsyncStateTag::Completed,
            Err(_) => true,
        },
{
    let (mut pc, mut locals, started_from_await) = match &frame.state {
        AsyncState::Executing | AsyncState::Completed => {
            return Err(JsError::TypeError);
        },
        AsyncState::SuspendedStart => {
            (0usize, make_locals(frame.locals_count, JsVal::Undefined), false)
        },
        AsyncState::SuspendedAwait { pc: spc, locals: sloc } => {
            (*spc, clone_jsval_vec(sloc), true)
        },
    };

    frame.state = AsyncState::Executing;

    if started_from_await {
        if is_reject {
            let check_pc = if pc > 0 { pc - 1 } else { 0 };
            match find_enclosing_catch(&frame.try_regions, check_pc) {
                Some((catch_pc, err_slot)) => {
                    write_local(&mut locals, err_slot, resume_val);
                    pc = catch_pc;
                },
                None => {
                    frame.state = AsyncState::Completed;
                    return Ok(AsyncStepOutcome::Threw(resume_val));
                },
            }
        } else {
            write_local(&mut locals, resume_dst, resume_val);
        }
    }

    let mut fuel = frame.step_budget;
    while pc < frame.code.len()
        invariant
            frame.state.tag() == AsyncStateTag::Executing,
            old(frame).state.tag() != AsyncStateTag::Executing,
            old(frame).state.tag() != AsyncStateTag::Completed,
        decreases fuel,
    {
        if fuel == 0 {
            frame.state = AsyncState::Completed;
            return Ok(AsyncStepOutcome::Threw(JsVal::Undefined));
        }
        fuel -= 1;
        let op = frame.code[pc];
        match op {
            AsyncOp::Const { dst, val } => {
                write_local(&mut locals, dst, val);
                pc += 1;
            },
            AsyncOp::AddInt { dst, src, delta } => {
                let cur = read_local(&locals, src);
                let nv = match cur {
                    JsVal::Int(x) => JsVal::Int(x.wrapping_add(delta)),
                    _ => JsVal::Int(delta),
                };
                write_local(&mut locals, dst, nv);
                pc += 1;
            },
            AsyncOp::MulInt { dst, src, factor } => {
                let cur = read_local(&locals, src);
                let nv = match cur {
                    JsVal::Int(x) => JsVal::Int(x.wrapping_mul(factor)),
                    _ => JsVal::Int(0),
                };
                write_local(&mut locals, dst, nv);
                pc += 1;
            },
            AsyncOp::EmitTrace { event_id } => {
                trace_log.push(event_id);
                pc += 1;
            },
            AsyncOp::Await { src, dst } => {
                let awaited = read_local(&locals, src);
                frame.state = AsyncState::SuspendedAwait {
                    pc: pc + 1,
                    locals,
                };
                return Ok(AsyncStepOutcome::SuspendedOnAwait {
                    awaited,
                    resume_dst: dst,
                });
            },
            AsyncOp::Return { src } => {
                let rv = read_local(&locals, src);
                frame.state = AsyncState::Completed;
                return Ok(AsyncStepOutcome::Returned(rv));
            },
            AsyncOp::Throw { src } => {
                let ev = read_local(&locals, src);
                match find_enclosing_catch(&frame.try_regions, pc) {
                    Some((catch_pc, err_slot)) => {
                        write_local(&mut locals, err_slot, ev);
                        pc = catch_pc;
                    },
                    None => {
                        frame.state = AsyncState::Completed;
                        return Ok(AsyncStepOutcome::Threw(ev));
                    },
                }
            },
        }
    }

    frame.state = AsyncState::Completed;
    Ok(AsyncStepOutcome::Returned(JsVal::Undefined))
}

} // verus!
