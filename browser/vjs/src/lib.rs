//! `vjs`: Formally verified ECMAScript interpreter core (J4 of `docs/verified-browser-engine.md` §3.3).
#![forbid(unsafe_code)]

pub mod utf16;
pub mod bigint;
pub mod number;
pub mod value;
pub mod ast;
pub mod completion;
pub mod env;
pub mod heap;
pub mod eval;
pub mod frontend;

pub use ast::{ChainStep, ForEachLhs, Program, UnsupportedFeature};
pub use completion::{Completion, CompletionValue, RunResult, ScriptCompletion};
pub use env::{EnvArena, EnvId};
pub use eval::{
    run, run_state_with_quota, run_with_quota, VmState, DEFAULT_REALM_HEAP_QUOTA,
};
#[cfg(verus_keep_ghost)]
pub use ast::{spec_prog_wf, SpecProgram};
#[cfg(verus_keep_ghost)]
pub use completion::{SpecOutcome, SpecScriptCompletion};
#[cfg(verus_keep_ghost)]
pub use env::env_wf;
#[cfg(verus_keep_ghost)]
pub use eval::{
    spec_eval_program, spec_eval_program_state, spec_eval_program_with_quota,
    theorem_end_to_end_step_refinement,
};
pub use frontend::{parse_script, parse_script_bytes, parse_script_utf16, ParseOutcome};
pub use heap::{ErrorKind, Heap, ObjectKind, RealmId};
pub use value::{JsNum, JsStr, ObjId, Val};

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// Helper cloning `JsStr` inside `lib.rs` so `eval_script_parsed` can return both `ParseOutcome` and `RunResult`.
fn clone_syntax_msg(s: &JsStr) -> (out: JsStr)
    ensures out@ == s@,
{
    let n = s.0.len();
    let mut u: Vec<u16> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == s.0@.len(),
            u@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> u@[k] == s.0@[k],
        decreases n - i,
    {
        u.push(s.0[i]);
        i += 1;
    }
    proof { assert(u@ =~= s.0@); }
    JsStr(u)
}

/// Parse and evaluate an ECMAScript source `&str` via verified UTF-8 -> UTF-16 decoding,
/// returning `(ParseOutcome, Option<VmState>, RunResult)` with exact deterministic refinement
/// on `ParseOutcome::Ok(prog)` to `spec_eval_program_state` / `spec_eval_program_with_quota`.
pub fn eval_script_parsed(
    js_source: &str,
    fuel: usize,
    heap_quota: usize,
) -> (out: (ParseOutcome, Option<VmState>, RunResult))
    ensures
        (crate::utf16::spec_utf8_to_utf16(js_source.spec_bytes()) is None) ==>
            matches!(out.0, ParseOutcome::SyntaxError(_))
            && out.1 is None
            && matches!(out.2, RunResult::Done(ScriptCompletion::SyntaxError(_))),
        match out.0 {
            ParseOutcome::Ok(ref prog) =>
                spec_prog_wf(prog@)
                && match out.1 {
                    Some(ref st) =>
                        (st@, out.2@) == spec_eval_program_state(prog@, fuel as nat, heap_quota as nat)
                        && env_wf(st@.envs)
                        && st.fuel <= fuel
                        && match out.2 {
                            RunResult::Done(ref v) =>
                                spec_eval_program_with_quota(prog@, fuel as nat, heap_quota as nat)
                                    == SpecOutcome::Done(v@),
                            RunResult::OutOfFuel =>
                                spec_eval_program_with_quota(prog@, fuel as nat, heap_quota as nat)
                                    == SpecOutcome::OutOfFuel
                                && st.fuel == 0,
                            RunResult::Unsupported(feat) =>
                                spec_eval_program_with_quota(prog@, fuel as nat, heap_quota as nat)
                                    == SpecOutcome::Unsupported(feat@),
                        },
                    None => false,
                },
            ParseOutcome::SyntaxError(ref msg) =>
                out.1 is None
                && out.2@ == SpecOutcome::Done(SpecScriptCompletion::SyntaxError(msg@)),
            ParseOutcome::Unsupported(feat) =>
                out.1 is None
                && out.2@ == SpecOutcome::Unsupported(feat@),
        },
{
    match parse_script(js_source) {
        ParseOutcome::Ok(prog) => {
            let (st, res) = run_state_with_quota(&prog, fuel, heap_quota);
            (ParseOutcome::Ok(prog), Some(st), res)
        }
        ParseOutcome::SyntaxError(msg) => {
            let msg2 = clone_syntax_msg(&msg);
            (
                ParseOutcome::SyntaxError(msg),
                None,
                RunResult::Done(ScriptCompletion::SyntaxError(msg2)),
            )
        }
        ParseOutcome::Unsupported(feat) => {
            (ParseOutcome::Unsupported(feat), None, RunResult::Unsupported(feat))
        }
    }
}

/// Parse and evaluate an ECMAScript source string end-to-end under explicit `fuel` and `heap_quota`,
/// returning `(Option<VmState>, RunResult)` with machine-checked step-refinement, `env_wf` preservation,
/// and exact fuel-exhaustion (`OutOfFuel ==> st.fuel == 0`).
pub fn eval_script_state(
    js_source: &str,
    fuel: usize,
    heap_quota: usize,
) -> (out: (Option<VmState>, RunResult))
    ensures
        (crate::utf16::spec_utf8_to_utf16(js_source.spec_bytes()) is None) ==>
            out.0 is None
            && matches!(out.1, RunResult::Done(ScriptCompletion::SyntaxError(_))),
        match out.0 {
            Some(ref st) =>
                env_wf(st@.envs)
                && st.fuel <= fuel
                && ((out.1 is OutOfFuel) ==> st.fuel == 0)
                && (exists|prog: SpecProgram|
                    #[trigger] spec_prog_wf(prog)
                    && (st@, out.1@) == spec_eval_program_state(prog, fuel as nat, heap_quota as nat)
                    && match out.1 {
                        RunResult::Done(ref v) =>
                            spec_eval_program_with_quota(prog, fuel as nat, heap_quota as nat)
                                == SpecOutcome::Done(v@),
                        RunResult::OutOfFuel =>
                            spec_eval_program_with_quota(prog, fuel as nat, heap_quota as nat)
                                == SpecOutcome::OutOfFuel
                            && st.fuel == 0,
                        RunResult::Unsupported(feat) =>
                            spec_eval_program_with_quota(prog, fuel as nat, heap_quota as nat)
                                == SpecOutcome::Unsupported(feat@),
                    }),
            None =>
                matches!(
                    out.1,
                    RunResult::Done(ScriptCompletion::SyntaxError(_))
                    | RunResult::Unsupported(_)
                ),
        },
{
    let (_po, opt_st, res) = eval_script_parsed(js_source, fuel, heap_quota);
    proof {
        if let ParseOutcome::Ok(ref prog) = _po {
            assert(spec_prog_wf(prog@));
        }
    }
    (opt_st, res)
}

/// Parse and evaluate an ECMAScript source string end-to-end under explicit `fuel` and `heap_quota`
/// (`docs/verified-browser-engine.md` §3.3), with machine-checked refinement to `spec_eval_program_with_quota`
/// and fuel-exhaustion exactness (`OutOfFuel ==> remaining_fuel == 0`).
pub fn eval_script(js_source: &str, fuel: usize, heap_quota: usize) -> (res: RunResult)
    ensures
        (crate::utf16::spec_utf8_to_utf16(js_source.spec_bytes()) is None) ==>
            matches!(res, RunResult::Done(ScriptCompletion::SyntaxError(_))),
        match res {
            RunResult::Done(ScriptCompletion::SyntaxError(_)) => true,
            RunResult::Done(ref v) =>
                exists|prog: SpecProgram|
                    #[trigger] spec_prog_wf(prog)
                    && spec_eval_program_with_quota(prog, fuel as nat, heap_quota as nat)
                        == SpecOutcome::Done(v@),
            RunResult::OutOfFuel =>
                exists|prog: SpecProgram|
                    #[trigger] spec_prog_wf(prog)
                    && spec_eval_program_with_quota(prog, fuel as nat, heap_quota as nat)
                        == SpecOutcome::OutOfFuel
                    && spec_eval_program_state(prog, fuel as nat, heap_quota as nat).0.fuel == 0,
            RunResult::Unsupported(_) => true,
        },
{
    let (_po, _opt_st, res) = eval_script_parsed(js_source, fuel, heap_quota);
    proof {
        if let ParseOutcome::Ok(ref prog) = _po {
            assert(spec_prog_wf(prog@));
        }
    }
    res
}

} // verus!
