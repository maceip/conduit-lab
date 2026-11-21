//! ECMA-262 §6.2.4 Completion Record Specification Type, `UpdateEmpty` (§6.2.4.2),
//! and top-level `RunResult` / `SpecOutcome` outcomes (`docs/verified-browser-engine.md` §3.3).
use crate::ast::UnsupportedFeature;
use crate::value::{JsStr, SpecVal, Val};
#[cfg(verus_keep_ghost)]
use crate::ast::spec_opt_str_view;
use vstd::prelude::*;

verus! {

/// Completion record `[[Value]]` slot: either `EMPTY` or an ECMAScript value (§6.2.4).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CompletionValue {
    Empty,
    Present(Val),
}

pub enum SpecCompletionValue {
    Empty,
    Present(SpecVal),
}

impl View for CompletionValue {
    type V = SpecCompletionValue;

    open spec fn view(&self) -> SpecCompletionValue {
        match self {
            CompletionValue::Empty => SpecCompletionValue::Empty,
            CompletionValue::Present(v) => SpecCompletionValue::Present(v@),
        }
    }
}

/// ECMA-262 §6.2.4 Completion Record (`Normal`, `Return`, `Throw`, `Break`, `Continue`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Completion {
    Normal(CompletionValue),
    Return(Val),
    Throw(Val),
    Break(CompletionValue, Option<JsStr>),
    Continue(CompletionValue, Option<JsStr>),
}

pub enum SpecCompletion {
    Normal(SpecCompletionValue),
    Return(SpecVal),
    Throw(SpecVal),
    Break(SpecCompletionValue, Option<Seq<u16>>),
    Continue(SpecCompletionValue, Option<Seq<u16>>),
}

impl View for Completion {
    type V = SpecCompletion;

    open spec fn view(&self) -> SpecCompletion {
        match self {
            Completion::Normal(cv) => SpecCompletion::Normal(cv@),
            Completion::Return(v) => SpecCompletion::Return(v@),
            Completion::Throw(v) => SpecCompletion::Throw(v@),
            Completion::Break(cv, lbl) => SpecCompletion::Break(cv@, spec_opt_str_view(lbl)),
            Completion::Continue(cv, lbl) => SpecCompletion::Continue(cv@, spec_opt_str_view(lbl)),
        }
    }
}

impl Completion {
    pub fn normal_val(v: Val) -> (c: Self)
        ensures c@ == SpecCompletion::Normal(SpecCompletionValue::Present(v@)),
    {
        Completion::Normal(CompletionValue::Present(v))
    }

    pub fn normal_empty() -> (c: Self)
        ensures c@ == SpecCompletion::Normal(SpecCompletionValue::Empty),
    {
        Completion::Normal(CompletionValue::Empty)
    }

    pub fn is_abrupt(&self) -> (b: bool)
        ensures b == !(self@ is Normal),
    {
        match self {
            Completion::Normal(_) => false,
            _ => true,
        }
    }
}

/// ECMA-262 §6.2.4.2 UpdateEmpty ( completionRecord, value )
pub open spec fn spec_update_empty_val(cv: SpecCompletionValue, fallback: SpecCompletionValue) -> SpecCompletionValue {
    match cv {
        SpecCompletionValue::Empty => fallback,
        SpecCompletionValue::Present(v) => SpecCompletionValue::Present(v),
    }
}

pub fn update_empty_val(cv: CompletionValue, fallback: CompletionValue) -> (r: CompletionValue)
    ensures r@ == spec_update_empty_val(cv@, fallback@),
{
    match cv {
        CompletionValue::Empty => fallback,
        CompletionValue::Present(v) => CompletionValue::Present(v),
    }
}

/// ECMA-262 §6.2.4.2 UpdateEmpty ( completionRecord, value )
/// 1. Assert: If completionRecord.[[Type]] is either return or throw, then completionRecord.[[Value]] is not empty.
/// 2. If completionRecord.[[Value]] is not empty, return ? completionRecord.
/// 3. Return CompletionRecord { [[Type]]: completionRecord.[[Type]], [[Value]]: value, [[Target]]: completionRecord.[[Target]] }.
pub open spec fn spec_update_empty(c: SpecCompletion, fallback: SpecCompletionValue) -> SpecCompletion {
    match c {
        SpecCompletion::Normal(cv) => SpecCompletion::Normal(spec_update_empty_val(cv, fallback)),
        SpecCompletion::Return(v) => SpecCompletion::Return(v),
        SpecCompletion::Throw(v) => SpecCompletion::Throw(v),
        SpecCompletion::Break(cv, lbl) => SpecCompletion::Break(spec_update_empty_val(cv, fallback), lbl),
        SpecCompletion::Continue(cv, lbl) => SpecCompletion::Continue(spec_update_empty_val(cv, fallback), lbl),
    }
}

pub fn update_empty(c: Completion, fallback: CompletionValue) -> (r: Completion)
    ensures r@ == spec_update_empty(c@, fallback@),
{
    match c {
        Completion::Normal(cv) => Completion::Normal(update_empty_val(cv, fallback)),
        Completion::Return(v) => Completion::Return(v),
        Completion::Throw(v) => Completion::Throw(v),
        Completion::Break(cv, lbl) => Completion::Break(update_empty_val(cv, fallback), lbl),
        Completion::Continue(cv, lbl) => Completion::Continue(update_empty_val(cv, fallback), lbl),
    }
}

pub open spec fn spec_unwrap_or_undefined(cv: SpecCompletionValue) -> SpecVal {
    match cv {
        SpecCompletionValue::Empty => SpecVal::Undefined,
        SpecCompletionValue::Present(v) => v,
    }
}

pub fn unwrap_or_undefined(cv: CompletionValue) -> (r: Val)
    ensures r@ == spec_unwrap_or_undefined(cv@),
{
    match cv {
        CompletionValue::Empty => Val::Undefined,
        CompletionValue::Present(v) => v,
    }
}

/// Algebraic lemma: `UpdateEmpty` is idempotent with the same fallback value.
pub proof fn lemma_update_empty_idempotent(c: SpecCompletion, v: SpecCompletionValue)
    ensures spec_update_empty(spec_update_empty(c, v), v) == spec_update_empty(c, v),
{
}

/// Algebraic lemma: `UpdateEmpty` never alters `Return` or `Throw` completions (§6.2.4.2 step 1).
pub proof fn lemma_update_empty_preserves_return_throw(c: SpecCompletion, v: SpecCompletionValue)
    ensures
        (c is Return) ==> spec_update_empty(c, v) == c,
        (c is Throw) ==> spec_update_empty(c, v) == c,
{
}

// ---------------------------------------------------------------------------
// Internal Step Result & Top-Level `RunResult` / `SpecOutcome` (§3.3)
// ---------------------------------------------------------------------------

/// Step outcome for expression evaluation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprStep {
    Val(Val),
    Throw(Val),
    HeapQuotaExceeded,
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

pub enum SpecExprStep {
    Val(SpecVal),
    Throw(SpecVal),
    HeapQuotaExceeded,
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

impl View for ExprStep {
    type V = SpecExprStep;

    open spec fn view(&self) -> SpecExprStep {
        match self {
            ExprStep::Val(v) => SpecExprStep::Val(v@),
            ExprStep::Throw(v) => SpecExprStep::Throw(v@),
            ExprStep::HeapQuotaExceeded => SpecExprStep::HeapQuotaExceeded,
            ExprStep::OutOfFuel => SpecExprStep::OutOfFuel,
            ExprStep::Unsupported(f) => SpecExprStep::Unsupported(*f),
        }
    }
}

/// Step outcome for statement / block / loop / function evaluation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StmtStep {
    Comp(Completion),
    HeapQuotaExceeded,
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

pub enum SpecStmtStep {
    Comp(SpecCompletion),
    HeapQuotaExceeded,
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

impl View for StmtStep {
    type V = SpecStmtStep;

    open spec fn view(&self) -> SpecStmtStep {
        match self {
            StmtStep::Comp(c) => SpecStmtStep::Comp(c@),
            StmtStep::HeapQuotaExceeded => SpecStmtStep::HeapQuotaExceeded,
            StmtStep::OutOfFuel => SpecStmtStep::OutOfFuel,
            StmtStep::Unsupported(f) => SpecStmtStep::Unsupported(*f),
        }
    }
}

/// Completed script outcome inside `RunResult::Done(...)`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScriptCompletion {
    /// Normal script completion (`[[Type]] == normal`) with final value.
    Normal(Val),
    /// Uncaught abrupt exception (`[[Type]] == throw`) with thrown ECMAScript value.
    Throw(Val),
    /// Static syntax or early-error rejection from script parsing.
    SyntaxError(JsStr),
    /// Per-realm arena heap quota reached even after mark-sweep reclamation.
    HeapQuotaExceeded,
}

pub enum SpecScriptCompletion {
    Normal(SpecVal),
    Throw(SpecVal),
    SyntaxError(Seq<u16>),
    HeapQuotaExceeded,
}

impl View for ScriptCompletion {
    type V = SpecScriptCompletion;

    open spec fn view(&self) -> SpecScriptCompletion {
        match self {
            ScriptCompletion::Normal(v) => SpecScriptCompletion::Normal(v@),
            ScriptCompletion::Throw(v) => SpecScriptCompletion::Throw(v@),
            ScriptCompletion::SyntaxError(msg) => SpecScriptCompletion::SyntaxError(msg@),
            ScriptCompletion::HeapQuotaExceeded => SpecScriptCompletion::HeapQuotaExceeded,
        }
    }
}

/// Top-level `vjs::run` / `vjs::eval_script` outcome (`docs/verified-browser-engine.md` §3.3):
/// - `Done(v)` with `spec_eval_program(p@, n) == SpecOutcome::Done(v@)`
/// - `OutOfFuel` with `spec_eval_program(p@, n) == SpecOutcome::OutOfFuel`
/// - `Unsupported(feature)` with `spec_eval_program(p@, n) == SpecOutcome::Unsupported(feature@)`
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum RunResult {
    Done(ScriptCompletion),
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

pub enum SpecOutcome {
    Done(SpecScriptCompletion),
    OutOfFuel,
    Unsupported(UnsupportedFeature),
}

impl View for RunResult {
    type V = SpecOutcome;

    open spec fn view(&self) -> SpecOutcome {
        match self {
            RunResult::Done(v) => SpecOutcome::Done(v@),
            RunResult::OutOfFuel => SpecOutcome::OutOfFuel,
            RunResult::Unsupported(f) => SpecOutcome::Unsupported(f@),
        }
    }
}

} // verus!
