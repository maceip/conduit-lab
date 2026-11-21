//! ECMAScript Promises (§27.2), FIFO Microtask Job Queue (§9.5), and Async/Await Continuation
//! Driver (§27.7.5), formally verified in Verus.
//!
//! Machine-checked theorems:
//! 1. **Settle-Once Monotonicity**: Once a Promise is `Fulfilled(v)` or `Rejected(r)`, NO single
//!    transition or arbitrary sequence of `fulfill` / `reject` / `resolve` / `then` / `all` /
//!    `race` / `drain_jobs` transitions can ever alter its state or settled value.
//! 2. **Liveness Under Fuel & Strict FIFO Ordering**: `drain_jobs(runtime, fuel)` terminates
//!    (`decreases fuel`), executes jobs strictly in FIFO order (`queue@[0]` dequeued first, new
//!    jobs appended strictly at tail), and either empties the queue (`DrainOutcome::Done` with
//!    `queue@.len() == 0`) or executes `fuel` genuine microtask steps (`DrainOutcome::OutOfFuel`
//!    with `executed_jobs@.len() == old.executed_jobs@.len() + fuel`).
use vstd::prelude::*;

verus! {

use crate::generator::{
    step_async_frame, AsyncFrame, AsyncOp, AsyncStepOutcome, TryRegion,
};
use crate::types::{AsyncId, JsError, JsVal, PromiseId};

// -----------------------------------------------------------------------------------------------
// Promise State, Capabilities, Reactions, and FIFO Job Queue (§27.2 & §9.5)
// -----------------------------------------------------------------------------------------------

/// `[[PromiseState]]` + `[[PromiseResult]]` (§27.2.6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PromiseState {
    Pending,
    Fulfilled(JsVal),
    Rejected(JsVal),
}

pub open spec fn spec_is_settled(s: PromiseState) -> bool {
    !(s is Pending)
}

pub fn is_settled_state(s: PromiseState) -> (b: bool)
    ensures
        b == spec_is_settled(s),
{
    !matches!(s, PromiseState::Pending)
}

/// `PromiseCapability` record (§27.2.1.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PromiseCapability {
    pub promise_id: PromiseId,
}

/// Reaction handler behavior for `PromiseReaction` records (§27.2.1.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReactionHandler {
    /// Default fulfill handler (`Identity`): passes value straight through.
    Identity,
    /// Default reject handler (`Thrower`): re-rejects with same reason.
    Thrower,
    /// Returns constant value `JsVal` (may be `JsVal::Promise(pid)` to chain promises!).
    ReturnConst(JsVal),
    /// Throws abrupt reason `JsVal`.
    ThrowConst(JsVal),
    /// Adds `delta` to `JsVal::Int(x)` (with optional trace event if `trace_id != 0`).
    AddInt { delta: i64, trace_id: u32 },
    /// Multiplies `JsVal::Int(x)` by `factor` (with optional trace event if `trace_id != 0`).
    MulInt { factor: i64, trace_id: u32 },
    /// Appends `event_id` to `trace_log` and passes argument (or rethrows if `is_throw`).
    TracePass { event_id: u32, is_throw: bool },
    /// Appends `event_id` to `trace_log` and returns `ret` (supports returning another `Promise`!).
    TraceReturn { event_id: u32, ret: JsVal },
    /// `Promise.all` per-element fulfill reaction (§27.2.4.1.2).
    AllFulfillElement { group_id: usize, index: usize },
    /// `async`/`await` continuation resumption (§27.7.5.3).
    ResumeAsync { async_id: AsyncId, resume_dst: usize, is_reject: bool },
}

/// `PromiseReaction` record (§27.2.1.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PromiseReaction {
    pub capability: Option<PromiseCapability>,
    pub handler: ReactionHandler,
}

/// Microtask job queued on the host's FIFO Promise Job Queue (§9.5 / §27.2.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MicrotaskJob {
    /// `NewPromiseReactionJob(reaction, argument)` (§27.2.2.1).
    Reaction {
        reaction: PromiseReaction,
        argument: JsVal,
    },
    /// `NewPromiseResolveThenableJob(promiseToResolve, thenable)` (§27.2.2.2).
    ResolveThenable {
        promise_to_resolve: PromiseId,
        thenable_promise: PromiseId,
    },
}

/// Verified O(1)-dequeue FIFO Microtask `JobQueue` (§9.5).
pub struct JobQueue {
    pub jobs: Vec<MicrotaskJob>,
    pub head: usize,
}

impl View for JobQueue {
    type V = Seq<MicrotaskJob>;

    open spec fn view(&self) -> Seq<MicrotaskJob> {
        if (self.head as int) <= self.jobs@.len() {
            self.jobs@.subrange(self.head as int, self.jobs@.len() as int)
        } else {
            Seq::empty()
        }
    }
}

impl JobQueue {
    pub open spec fn wf(&self) -> bool {
        (self.head as int) <= self.jobs@.len()
            && self.jobs@.len() < usize::MAX as int
    }

    pub fn new() -> (q: Self)
        ensures
            q.wf(),
            q@.len() == 0,
    {
        JobQueue { jobs: Vec::new(), head: 0 }
    }

    pub fn len(&self) -> (n: usize)
        requires
            self.wf(),
        ensures
            n as int == self@.len(),
    {
        self.jobs.len() - self.head
    }

    pub fn is_empty(&self) -> (empty: bool)
        requires
            self.wf(),
        ensures
            empty == (self@.len() == 0),
    {
        self.head == self.jobs.len()
    }

    /// Enqueue `job` strictly at the back of the FIFO queue.
    pub fn enqueue(&mut self, job: MicrotaskJob) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                Ok(()) => final(self)@ == old(self)@ + seq![job],
                Err(e) => e == JsError::QuotaExceeded && final(self)@ == old(self)@,
            },
    {
        if self.jobs.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let ghost prev = self@;
        self.jobs.push(job);
        proof {
            assert(self@ =~= prev + seq![job]);
        }
        Ok(())
    }

    /// Dequeue the oldest job strictly from the front (`self@[0]`) of the FIFO queue.
    pub fn dequeue(&mut self) -> (res: Option<MicrotaskJob>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                None => old(self)@.len() == 0 && final(self)@ == old(self)@,
                Some(job) => {
                    &&& old(self)@.len() > 0
                    &&& job == old(self)@[0]
                    &&& final(self)@ == old(self)@.subrange(1, old(self)@.len() as int)
                },
            },
    {
        if self.head >= self.jobs.len() {
            return None;
        }
        let ghost prev = self@;
        let job = self.jobs[self.head];
        self.head += 1;
        proof {
            assert(job == prev[0]);
            assert(self@ =~= prev.subrange(1, prev.len() as int));
        }
        Some(job)
    }
}

/// Concrete `Promise` record (§27.2.6).
pub struct PromiseRecord {
    pub state: PromiseState,
    pub fulfill_reactions: Vec<PromiseReaction>,
    pub reject_reactions: Vec<PromiseReaction>,
    pub is_handled: bool,
    /// Per §27.2.1.3 `CreateResolvingFunctions` `alreadyResolved` record: once `resolve(x)` or
    /// `reject(r)` has been called on the outer resolving function pair, further external resolve
    /// calls on the same `alreadyResolved` cell are ignored (while internal thenable resolution
    /// jobs settle the still-`Pending` promise via `fulfill_promise` / `reject_promise`).
    pub already_resolved: bool,
}

/// Shared state record for `Promise.all` (§27.2.4.1.2).
pub struct PromiseAllGroup {
    pub values: Vec<JsVal>,
    pub already_called: Vec<bool>,
    pub remaining: usize,
    pub result_promise: PromiseId,
}

/// Outcome of `drain_jobs(runtime, fuel)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DrainOutcome {
    Done { steps_executed: usize },
    OutOfFuel { steps_executed: usize },
}

pub open spec fn spec_promise_states(promises: Seq<PromiseRecord>) -> Seq<PromiseState> {
    Seq::new(promises.len(), |i: int| promises[i].state)
}

/// **Settle-Once Monotonicity Relation**:
/// Every promise present in `before` still exists in `after`, and if `before[pid]` was already
/// settled (`Fulfilled(v)` or `Rejected(r)`), then `after[pid] == before[pid]` identically!
pub open spec fn spec_settled_monotonic(
    before: Seq<PromiseState>,
    after: Seq<PromiseState>,
) -> bool {
    &&& before.len() <= after.len()
    &&& forall|pid: int| 0 <= pid < before.len() && spec_is_settled(#[trigger] before[pid])
        ==> after[pid] == before[pid]
}

pub proof fn lemma_settled_monotonic_reflexive(s: Seq<PromiseState>)
    ensures
        spec_settled_monotonic(s, s),
{
}

pub proof fn lemma_settled_monotonic_transitive(
    s0: Seq<PromiseState>,
    s1: Seq<PromiseState>,
    s2: Seq<PromiseState>,
)
    requires
        spec_settled_monotonic(s0, s1),
        spec_settled_monotonic(s1, s2),
    ensures
        spec_settled_monotonic(s0, s2),
{
    assert forall|pid: int| 0 <= pid < s0.len() && spec_is_settled(#[trigger] s0[pid])
        implies s2[pid] == s0[pid]
    by {
        assert(s1[pid] == s0[pid]);
        assert(spec_is_settled(s1[pid]));
        assert(s2[pid] == s1[pid]);
    };
}

/// Complete Promise + FIFO Microtask Job Queue + Async/Await Runtime.
pub struct PromiseRuntime {
    pub promises: Vec<PromiseRecord>,
    pub queue: JobQueue,
    pub all_groups: Vec<PromiseAllGroup>,
    pub async_frames: Vec<AsyncFrame>,
    pub trace_log: Vec<u32>,
    pub executed_jobs: Vec<MicrotaskJob>,
}

impl PromiseRuntime {
    pub open spec fn wf(&self) -> bool {
        &&& self.promises@.len() < usize::MAX as int
        &&& self.queue.wf()
        &&& self.all_groups@.len() < usize::MAX as int
        &&& self.async_frames@.len() < usize::MAX as int
        &&& self.executed_jobs@.len() < usize::MAX as int
    }

    pub open spec fn states(&self) -> Seq<PromiseState> {
        spec_promise_states(self.promises@)
    }

    pub fn new() -> (rt: Self)
        ensures
            rt.wf(),
            rt.states().len() == 0,
            rt.queue@.len() == 0,
            rt.executed_jobs@.len() == 0,
    {
        PromiseRuntime {
            promises: Vec::new(),
            queue: JobQueue::new(),
            all_groups: Vec::new(),
            async_frames: Vec::new(),
            trace_log: Vec::new(),
            executed_jobs: Vec::new(),
        }
    }

    pub fn promise_state(&self, pid: PromiseId) -> (res: Option<PromiseState>)
        ensures
            match res {
                Some(st) => (pid as int) < self.states().len() && self.states()[pid as int] == st,
                None => (pid as int) >= self.states().len(),
            },
    {
        if pid < self.promises.len() {
            Some(self.promises[pid].state)
        } else {
            None
        }
    }

    pub fn all_group_values(&self, group_id: usize) -> Option<&Vec<JsVal>> {
        if group_id < self.all_groups.len() {
            Some(&self.all_groups[group_id].values)
        } else {
            None
        }
    }

    /// Allocate a fresh `Pending` Promise.
    pub fn new_promise(&mut self) -> (res: Result<PromiseId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).queue@ == old(self).queue@,
            final(self).executed_jobs@ == old(self).executed_jobs@,
            match res {
                Ok(pid) => {
                    &&& (pid as int) == old(self).states().len()
                    &&& final(self).states().len() == old(self).states().len() + 1
                    &&& final(self).states()[pid as int] == PromiseState::Pending
                },
                Err(_) => final(self).states() == old(self).states(),
            },
    {
        if self.promises.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let pid = self.promises.len();
        let ghost pre = self.states();
        self.promises.push(PromiseRecord {
            state: PromiseState::Pending,
            fulfill_reactions: Vec::new(),
            reject_reactions: Vec::new(),
            is_handled: false,
            already_resolved: false,
        });
        proof {
            assert forall|i: int| 0 <= i < pre.len() && spec_is_settled(#[trigger] pre[i])
                implies self.states()[i] == pre[i]
            by {
                assert(self.promises@[i] == old(self).promises@[i]);
            };
        }
        Ok(pid)
    }

    /// §27.2.1.5 `NewPromiseCapability`.
    pub fn new_promise_capability(&mut self) -> (res: Result<PromiseCapability, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).queue@ == old(self).queue@,
            final(self).executed_jobs@ == old(self).executed_jobs@,
            match res {
                Ok(cap) => {
                    &&& (cap.promise_id as int) < final(self).states().len()
                    &&& final(self).states()[cap.promise_id as int] == PromiseState::Pending
                },
                Err(_) => final(self).states() == old(self).states(),
            },
    {
        let pid = self.new_promise()?;
        Ok(PromiseCapability { promise_id: pid })
    }

    /// §27.2.1.4 `FulfillPromise(promise, value)` (guarded: if already settled, no-op!).
    /// Enqueues all registered `fulfill_reactions` onto the FIFO `JobQueue` in registration order!
    pub fn fulfill_promise(&mut self, pid: PromiseId, value: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            // If `pid` was Pending and operation succeeded, `pid` is now `Fulfilled(value)`
            (res is Ok && (pid as int) < old(self).states().len() && old(self).states()[pid as int] == PromiseState::Pending)
                ==> final(self).states()[pid as int] == PromiseState::Fulfilled(value),
            // If `pid` was already settled, its state is 100% unchanged!
            ((pid as int) < old(self).states().len() && spec_is_settled(old(self).states()[pid as int]))
                ==> final(self).states()[pid as int] == old(self).states()[pid as int],
            ((pid as int) < old(self).promises@.len() && old(self).promises@[pid as int].already_resolved)
                ==> final(self).promises@[pid as int].already_resolved,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if is_settled_state(self.promises[pid].state) {
            return Ok(());
        }
        let n_rxns = self.promises[pid].fulfill_reactions.len();
        let mut rxns: Vec<PromiseReaction> = Vec::new();
        let mut i: usize = 0;
        while i < n_rxns
            invariant
                i <= n_rxns,
                pid < self.promises@.len(),
                n_rxns == self.promises@[pid as int].fulfill_reactions@.len(),
                rxns@.len() == i as int,
            decreases n_rxns - i,
        {
            rxns.push(self.promises[pid].fulfill_reactions[i]);
            i += 1;
        }

        let ghost pre_states = self.states();
        self.promises.set(pid, PromiseRecord {
            state: PromiseState::Fulfilled(value),
            fulfill_reactions: Vec::new(),
            reject_reactions: Vec::new(),
            is_handled: self.promises[pid].is_handled,
            already_resolved: true,
        });
        proof {
            assert forall|k: int| 0 <= k < pre_states.len() && spec_is_settled(#[trigger] pre_states[k])
                implies self.states()[k] == pre_states[k]
            by {
                assert(k != pid as int);
                assert(self.promises@[k] == old(self).promises@[k]);
            };
        }

        let mut j: usize = 0;
        while j < n_rxns
            invariant
                j <= n_rxns,
                n_rxns == rxns@.len(),
                self.wf(),
                pre_states == old(self).states(),
                (pid as int) < pre_states.len(),
                self.states().len() == pre_states.len(),
                spec_settled_monotonic(pre_states, self.states()),
                self.states()[pid as int] == PromiseState::Fulfilled(value),
                self.promises@[pid as int].already_resolved,
                self.executed_jobs@ == old(self).executed_jobs@,
            decreases n_rxns - j,
        {
            self.queue.enqueue(MicrotaskJob::Reaction {
                reaction: rxns[j],
                argument: value,
            })?;
            j += 1;
        }
        Ok(())
    }

    /// §27.2.1.7 `RejectPromise(promise, reason)` (guarded: if already settled, no-op!).
    /// Enqueues all registered `reject_reactions` onto the FIFO `JobQueue` in registration order!
    pub fn reject_promise(&mut self, pid: PromiseId, reason: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            (res is Ok && (pid as int) < old(self).states().len() && old(self).states()[pid as int] == PromiseState::Pending)
                ==> final(self).states()[pid as int] == PromiseState::Rejected(reason),
            ((pid as int) < old(self).states().len() && spec_is_settled(old(self).states()[pid as int]))
                ==> final(self).states()[pid as int] == old(self).states()[pid as int],
            ((pid as int) < old(self).promises@.len() && old(self).promises@[pid as int].already_resolved)
                ==> final(self).promises@[pid as int].already_resolved,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if is_settled_state(self.promises[pid].state) {
            return Ok(());
        }
        let n_rxns = self.promises[pid].reject_reactions.len();
        let mut rxns: Vec<PromiseReaction> = Vec::new();
        let mut i: usize = 0;
        while i < n_rxns
            invariant
                i <= n_rxns,
                pid < self.promises@.len(),
                n_rxns == self.promises@[pid as int].reject_reactions@.len(),
                rxns@.len() == i as int,
            decreases n_rxns - i,
        {
            rxns.push(self.promises[pid].reject_reactions[i]);
            i += 1;
        }

        let ghost pre_states = self.states();
        self.promises.set(pid, PromiseRecord {
            state: PromiseState::Rejected(reason),
            fulfill_reactions: Vec::new(),
            reject_reactions: Vec::new(),
            is_handled: self.promises[pid].is_handled,
            already_resolved: true,
        });
        proof {
            assert forall|k: int| 0 <= k < pre_states.len() && spec_is_settled(#[trigger] pre_states[k])
                implies self.states()[k] == pre_states[k]
            by {
                assert(k != pid as int);
                assert(self.promises@[k] == old(self).promises@[k]);
            };
        }

        let mut j: usize = 0;
        while j < n_rxns
            invariant
                j <= n_rxns,
                n_rxns == rxns@.len(),
                self.wf(),
                pre_states == old(self).states(),
                (pid as int) < pre_states.len(),
                self.states().len() == pre_states.len(),
                spec_settled_monotonic(pre_states, self.states()),
                self.states()[pid as int] == PromiseState::Rejected(reason),
                self.promises@[pid as int].already_resolved,
                self.executed_jobs@ == old(self).executed_jobs@,
            decreases n_rxns - j,
        {
            self.queue.enqueue(MicrotaskJob::Reaction {
                reaction: rxns[j],
                argument: reason,
            })?;
            j += 1;
        }
        Ok(())
    }

    /// Internal Promise resolution mechanics (§27.2.1.3.2 steps 7–13, after `alreadyResolved` guard):
    /// - If already settled, returns `Ok(())` without mutating state.
    /// - If `SameValue(resolution, promise)`, rejects `pid` with `TypeError` marker.
    /// - If `resolution == JsVal::Promise(other_pid)`, enqueues `ResolveThenable` microtask without
    ///   touching the external executor's `already_resolved` flag.
    /// - Otherwise fulfills `pid` with `resolution`.
    pub fn resolve_promise_internal(&mut self, pid: PromiseId, resolution: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            ((pid as int) < old(self).promises@.len() && old(self).promises@[pid as int].already_resolved)
                ==> final(self).promises@[pid as int].already_resolved,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if is_settled_state(self.promises[pid].state) {
            return Ok(());
        }
        match resolution {
            JsVal::Promise(other_pid) => {
                if other_pid == pid {
                    // §27.2.1.3.2 step 7: self-resolution rejects with TypeError!
                    self.reject_promise(pid, JsVal::Symbol(0xDEAD_719Eu32))
                } else if other_pid < self.promises.len() {
                    self.queue.enqueue(MicrotaskJob::ResolveThenable {
                        promise_to_resolve: pid,
                        thenable_promise: other_pid,
                    })
                } else {
                    Err(JsError::RangeError)
                }
            },
            _ => self.fulfill_promise(pid, resolution),
        }
    }

    /// §27.2.1.3.2 External Executor `resolve(resolution)` function (`CreateResolvingFunctions`):
    /// Guarded by `already_resolved`: once either `call_resolving_resolve` or `call_resolving_reject`
    /// has been called on `pid`, any subsequent call is a proved pure no-op!
    pub fn call_resolving_resolve(&mut self, pid: PromiseId, resolution: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            ((pid as int) < old(self).promises@.len() && old(self).promises@[pid as int].already_resolved) ==> (
                res == Ok::<(), JsError>(())
                && final(self).states() == old(self).states()
                && final(self).queue@ == old(self).queue@
                && final(self).promises@[pid as int].already_resolved
            ),
            (res is Ok && (pid as int) < final(self).promises@.len())
                ==> final(self).promises@[pid as int].already_resolved,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if self.promises[pid].already_resolved {
            return Ok(());
        }
        let ghost pre_states = self.states();
        self.promises[pid].already_resolved = true;
        proof {
            assert(self.states() =~= pre_states);
        }
        self.resolve_promise_internal(pid, resolution)
    }

    /// §27.2.1.3.1 External Executor `reject(reason)` function (`CreateResolvingFunctions`):
    /// Guarded by `already_resolved`: even if `pid` is still `Pending` (e.g. after `resolve(pendingThenable)`),
    /// calling `call_resolving_reject` is a proved pure no-op!
    pub fn call_resolving_reject(&mut self, pid: PromiseId, reason: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            ((pid as int) < old(self).promises@.len() && old(self).promises@[pid as int].already_resolved) ==> (
                res == Ok::<(), JsError>(())
                && final(self).states() == old(self).states()
                && final(self).queue@ == old(self).queue@
                && final(self).promises@[pid as int].already_resolved
            ),
            (res is Ok && (pid as int) < final(self).promises@.len())
                ==> final(self).promises@[pid as int].already_resolved,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if self.promises[pid].already_resolved {
            return Ok(());
        }
        let ghost pre_states = self.states();
        self.promises[pid].already_resolved = true;
        proof {
            assert(self.states() =~= pre_states);
        }
        let r = self.reject_promise(pid, reason);
        r
    }

    /// Convenience wrapper invoking external executor `call_resolving_resolve`.
    pub fn resolve_promise(&mut self, pid: PromiseId, resolution: JsVal) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states().len() == old(self).states().len(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        self.call_resolving_resolve(pid, resolution)
    }

    /// Internal adoption step executed by `ResolveThenable` (§27.2.2.2):
    /// Adopts `thenable_promise` onto `promise_to_resolve` via `PerformPromiseThen` WITHOUT
    /// clearing `promise_to_resolve.already_resolved` (so external resolving functions stay locked out!).
    fn adopt_promise(&mut self, promise_to_resolve: PromiseId, thenable_promise: PromiseId) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        if promise_to_resolve >= self.promises.len() || thenable_promise >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        if promise_to_resolve == thenable_promise {
            return self.reject_promise(promise_to_resolve, JsVal::Symbol(0xDEAD_719Eu32));
        }
        let cap = PromiseCapability { promise_id: promise_to_resolve };
        self.perform_promise_then(
            thenable_promise,
            Some(ReactionHandler::Identity),
            Some(ReactionHandler::Thrower),
            Some(cap),
        )
    }

    /// §27.2.5.4.1 `PerformPromiseThen(promise, onFulfilled, onRejected, resultCapability)`.
    pub fn perform_promise_then(
        &mut self,
        pid: PromiseId,
        on_fulfill: Option<ReactionHandler>,
        on_reject: Option<ReactionHandler>,
        result_capability: Option<PromiseCapability>,
    ) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).states() == old(self).states(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        if pid >= self.promises.len() {
            return Err(JsError::RangeError);
        }
        let f_handler = match on_fulfill {
            Some(h) => h,
            None => ReactionHandler::Identity,
        };
        let r_handler = match on_reject {
            Some(h) => h,
            None => ReactionHandler::Thrower,
        };
        let fulfill_rxn = PromiseReaction {
            capability: result_capability,
            handler: f_handler,
        };
        let reject_rxn = PromiseReaction {
            capability: result_capability,
            handler: r_handler,
        };

        let st = self.promises[pid].state;
        let ghost pre_states = self.states();
        match st {
            PromiseState::Pending => {
                self.promises[pid].fulfill_reactions.push(fulfill_rxn);
                self.promises[pid].reject_reactions.push(reject_rxn);
                self.promises[pid].is_handled = true;
                proof {
                    assert(self.states() =~= pre_states);
                }
                Ok(())
            },
            PromiseState::Fulfilled(v) => {
                self.promises[pid].is_handled = true;
                proof {
                    assert(self.states() =~= pre_states);
                }
                self.queue.enqueue(MicrotaskJob::Reaction {
                    reaction: fulfill_rxn,
                    argument: v,
                })
            },
            PromiseState::Rejected(r) => {
                self.promises[pid].is_handled = true;
                proof {
                    assert(self.states() =~= pre_states);
                }
                self.queue.enqueue(MicrotaskJob::Reaction {
                    reaction: reject_rxn,
                    argument: r,
                })
            },
        }
    }

    /// Convenience `.then(onFulfill, onReject)` creating and returning the chained child `PromiseId`.
    pub fn then(
        &mut self,
        pid: PromiseId,
        on_fulfill: Option<ReactionHandler>,
        on_reject: Option<ReactionHandler>,
    ) -> (res: Result<PromiseId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        let ghost s0 = self.states();
        let cap = self.new_promise_capability()?;
        let ghost s1 = self.states();
        let r = self.perform_promise_then(pid, on_fulfill, on_reject, Some(cap));
        proof {
            lemma_settled_monotonic_transitive(s0, s1, self.states());
        }
        match r {
            Ok(()) => Ok(cap.promise_id),
            Err(e) => Err(e),
        }
    }

    /// §27.2.4.7 `Promise.resolve(x)`: if `x` is already a valid `JsVal::Promise(pid)`, returns
    /// `pid` directly without wrapping; otherwise creates a capability and resolves it with `x`.
    pub fn promise_resolve(&mut self, x: JsVal) -> (res: Result<PromiseId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            match res {
                Ok(pid) => (pid as int) < final(self).states().len(),
                Err(_) => true,
            },
    {
        if let JsVal::Promise(pid) = x {
            if pid < self.promises.len() {
                return Ok(pid);
            } else {
                return Err(JsError::RangeError);
            }
        }
        let ghost s0 = self.states();
        let cap = self.new_promise_capability()?;
        let ghost s1 = self.states();
        let r = self.fulfill_promise(cap.promise_id, x);
        proof {
            lemma_settled_monotonic_transitive(s0, s1, self.states());
        }
        match r {
            Ok(()) => Ok(cap.promise_id),
            Err(e) => Err(e),
        }
    }

    /// §27.2.4.6 `Promise.reject(r)`.
    pub fn promise_reject(&mut self, reason: JsVal) -> (res: Result<PromiseId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
            match res {
                Ok(pid) => {
                    &&& (pid as int) < final(self).states().len()
                    &&& final(self).states()[pid as int] == PromiseState::Rejected(reason)
                },
                Err(_) => true,
            },
    {
        let ghost s0 = self.states();
        let cap = self.new_promise_capability()?;
        let ghost s1 = self.states();
        let r = self.reject_promise(cap.promise_id, reason);
        proof {
            lemma_settled_monotonic_transitive(s0, s1, self.states());
        }
        match r {
            Ok(()) => Ok(cap.promise_id),
            Err(e) => Err(e),
        }
    }

    /// §27.2.4.1 `Promise.all(iterable)` with exact `remainingElementsCount` + `alreadyCalled` guards!
    pub fn promise_all(&mut self, inputs: &[JsVal]) -> (res: Result<(PromiseId, usize), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        if inputs.len() >= usize::MAX - 2 {
            return Err(JsError::QuotaExceeded);
        }
        let result_cap = self.new_promise_capability()?;
        if self.all_groups.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let n = inputs.len();
        let mut values: Vec<JsVal> = Vec::new();
        let mut already_called: Vec<bool> = Vec::new();
        let mut init_i: usize = 0;
        while init_i < n
            invariant
                init_i <= n,
                values@.len() == init_i as int,
                already_called@.len() == init_i as int,
            decreases n - init_i,
        {
            values.push(JsVal::Undefined);
            already_called.push(false);
            init_i += 1;
        }
        let ghost pre_push_states = self.states();
        let group_id = self.all_groups.len();
        self.all_groups.push(PromiseAllGroup {
            values,
            already_called,
            remaining: 1,
            result_promise: result_cap.promise_id,
        });
        proof {
            assert(self.states() =~= pre_push_states);
        }

        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                n == inputs@.len(),
                n < usize::MAX - 2,
                self.wf(),
                group_id < self.all_groups@.len(),
                self.all_groups@[group_id as int].remaining <= idx + 1,
                spec_settled_monotonic(old(self).states(), self.states()),
                self.executed_jobs@ == old(self).executed_jobs@,
            decreases n - idx,
        {
            let ghost step_s0 = self.states();
            let cur_rem = self.all_groups[group_id].remaining;
            self.all_groups[group_id].remaining = cur_rem + 1;
            proof {
                assert(self.states() =~= step_s0);
            }
            let next_p_res = self.promise_resolve(inputs[idx]);
            proof {
                lemma_settled_monotonic_transitive(old(self).states(), step_s0, self.states());
            }
            let next_p = next_p_res?;
            if group_id >= self.all_groups.len() || self.all_groups[group_id].remaining > idx + 2 {
                return Err(JsError::QuotaExceeded);
            }
            let f_res = self.perform_promise_then(
                next_p,
                Some(ReactionHandler::AllFulfillElement { group_id, index: idx }),
                None,
                None,
            );
            let _ = f_res?;
            if group_id >= self.all_groups.len() || self.all_groups[group_id].remaining > idx + 2 {
                return Err(JsError::QuotaExceeded);
            }
            let r_res = self.perform_promise_then(
                next_p,
                None,
                Some(ReactionHandler::Thrower),
                Some(result_cap),
            );
            let _ = r_res?;
            if group_id >= self.all_groups.len() || self.all_groups[group_id].remaining > idx + 2 {
                return Err(JsError::QuotaExceeded);
            }
            idx += 1;
        }

        // Decrement the +1 sentinel (handles `Promise.all([])` fulfilling immediately!)
        let ghost pre_fin = self.states();
        let rem_after = self.all_groups[group_id].remaining;
        if rem_after > 0 {
            self.all_groups[group_id].remaining = rem_after - 1;
        }
        proof {
            assert(self.states() =~= pre_fin);
        }
        if self.all_groups[group_id].remaining == 0 {
            let ghost pre_fulfill = self.states();
            let f_done = self.fulfill_promise(result_cap.promise_id, JsVal::Object(group_id));
            proof {
                lemma_settled_monotonic_transitive(old(self).states(), pre_fulfill, self.states());
            }
            let _ = f_done?;
        }
        Ok((result_cap.promise_id, group_id))
    }

    /// §27.2.4.5 `Promise.race(iterable)`.
    pub fn promise_race(&mut self, inputs: &[JsVal]) -> (res: Result<PromiseId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        let result_cap = self.new_promise_capability()?;
        let n = inputs.len();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                n == inputs@.len(),
                self.wf(),
                spec_settled_monotonic(old(self).states(), self.states()),
                self.executed_jobs@ == old(self).executed_jobs@,
            decreases n - idx,
        {
            let ghost step_s0 = self.states();
            let next_p_res = self.promise_resolve(inputs[idx]);
            proof {
                lemma_settled_monotonic_transitive(old(self).states(), step_s0, self.states());
            }
            let next_p = next_p_res?;
            let r = self.perform_promise_then(
                next_p,
                Some(ReactionHandler::Identity),
                Some(ReactionHandler::Thrower),
                Some(result_cap),
            );
            let _ = r?;
            idx += 1;
        }
        Ok(result_cap.promise_id)
    }

    /// §27.7.5 `AsyncBlockStart`: spawn an `async` function frame, execute synchronously up to
    /// its first `await` (or completion), and return `(async_id, result_promise_id)`.
    pub fn spawn_async(
        &mut self,
        code: Vec<AsyncOp>,
        try_regions: Vec<TryRegion>,
        locals_count: usize,
        step_budget: usize,
    ) -> (res: Result<(AsyncId, PromiseId), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        let cap = self.new_promise_capability()?;
        if self.async_frames.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let ghost s1 = self.states();
        let async_id = self.async_frames.len();
        let frame = AsyncFrame::new(code, try_regions, locals_count, cap.promise_id, step_budget);
        self.async_frames.push(frame);
        proof {
            assert(self.states() =~= s1);
        }
        let ghost s2 = self.states();
        let d_res = self.drive_async_step(async_id, JsVal::Undefined, 0, false);
        proof {
            lemma_settled_monotonic_transitive(old(self).states(), s2, self.states());
        }
        let _ = d_res?;
        Ok((async_id, cap.promise_id))
    }

    /// Resume or start `async_id` and wire its outcome (`Await` -> Promise reactions, `Return` ->
    /// `fulfill_promise`, `Throw` -> `reject_promise`).
    fn drive_async_step(
        &mut self,
        async_id: AsyncId,
        resume_val: JsVal,
        resume_dst: usize,
        is_reject: bool,
    ) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            final(self).executed_jobs@ == old(self).executed_jobs@,
    {
        if async_id >= self.async_frames.len() {
            return Err(JsError::RangeError);
        }
        let ghost s0 = self.states();
        let result_pid = self.async_frames[async_id].result_promise;
        let step_res = step_async_frame(
            &mut self.async_frames[async_id],
            resume_val,
            resume_dst,
            is_reject,
            &mut self.trace_log,
        );
        proof {
            assert(self.states() =~= s0);
        }
        let outcome = step_res?;
        match outcome {
            AsyncStepOutcome::Returned(v) => {
                self.fulfill_promise(result_pid, v)
            },
            AsyncStepOutcome::Threw(e) => {
                self.reject_promise(result_pid, e)
            },
            AsyncStepOutcome::SuspendedOnAwait { awaited, resume_dst: dst } => {
                // §27.7.5.3 `Await(value)`: `let promise = ? PromiseResolve(%Promise%, value)`
                let awaited_pid = self.promise_resolve(awaited)?;
                let ghost s1 = self.states();
                let r = self.perform_promise_then(
                    awaited_pid,
                    Some(ReactionHandler::ResumeAsync {
                        async_id,
                        resume_dst: dst,
                        is_reject: false,
                    }),
                    Some(ReactionHandler::ResumeAsync {
                        async_id,
                        resume_dst: dst,
                        is_reject: true,
                    }),
                    None,
                );
                proof {
                    lemma_settled_monotonic_transitive(s0, s1, self.states());
                }
                r
            },
        }
    }

    /// Execute a single FIFO microtask job (`self.queue@[0]`) if the queue is non-empty!
    pub fn step_microtask(&mut self) -> (res: Result<bool, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_settled_monotonic(old(self).states(), final(self).states()),
            match res {
                Ok(false) => {
                    &&& old(self).queue@.len() == 0
                    &&& final(self).queue@ == old(self).queue@
                    &&& final(self).executed_jobs@ == old(self).executed_jobs@
                },
                Ok(true) => {
                    &&& old(self).queue@.len() > 0
                    &&& final(self).executed_jobs@ == old(self).executed_jobs@ + seq![old(self).queue@[0]]
                },
                Err(_) => true,
            },
    {
        if self.executed_jobs.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let ghost s0 = self.states();
        let ghost pre_exec = self.executed_jobs@;
        let dequeued = self.queue.dequeue();
        proof {
            assert(self.states() =~= s0);
        }
        let job = match dequeued {
            None => return Ok(false),
            Some(j) => j,
        };
        self.executed_jobs.push(job);
        let ghost post_push_exec = self.executed_jobs@;
        proof {
            assert(post_push_exec =~= pre_exec + seq![job]);
            assert(self.states() =~= s0);
        }

        match job {
            MicrotaskJob::ResolveThenable { promise_to_resolve, thenable_promise } => {
                let _ = self.adopt_promise(promise_to_resolve, thenable_promise)?;
                Ok(true)
            },
            MicrotaskJob::Reaction { reaction, argument } => {
                match reaction.handler {
                    ReactionHandler::AllFulfillElement { group_id, index } => {
                        if group_id < self.all_groups.len() && index < self.all_groups[group_id].values.len()
                            && index < self.all_groups[group_id].already_called.len()
                        {
                            if !self.all_groups[group_id].already_called[index] {
                                let ghost pre_upd = self.states();
                                self.all_groups[group_id].already_called.set(index, true);
                                self.all_groups[group_id].values.set(index, argument);
                                if self.all_groups[group_id].remaining > 0 {
                                    let rem = self.all_groups[group_id].remaining;
                                    self.all_groups[group_id].remaining = rem - 1;
                                }
                                proof {
                                    assert(self.states() =~= pre_upd);
                                }
                                if self.all_groups[group_id].remaining == 0 {
                                    let res_pid = self.all_groups[group_id].result_promise;
                                    let _ = self.fulfill_promise(res_pid, JsVal::Object(group_id))?;
                                }
                            }
                        }
                        Ok(true)
                    },
                    ReactionHandler::ResumeAsync { async_id, resume_dst, is_reject } => {
                        let _ = self.drive_async_step(async_id, argument, resume_dst, is_reject)?;
                        Ok(true)
                    },
                    _ => {
                        // Evaluate standard reaction handler into Normal(v) or Abrupt(err)
                        let eval_outcome: Result<JsVal, JsVal> = match reaction.handler {
                            ReactionHandler::Identity => Ok(argument),
                            ReactionHandler::Thrower => Err(argument),
                            ReactionHandler::ReturnConst(v) => Ok(v),
                            ReactionHandler::ThrowConst(e) => Err(e),
                            ReactionHandler::AddInt { delta, trace_id } => {
                                if trace_id != 0 {
                                    let ghost pre_t = self.states();
                                    self.trace_log.push(trace_id);
                                    proof { assert(self.states() =~= pre_t); }
                                }
                                match argument {
                                    JsVal::Int(x) => Ok(JsVal::Int(x.wrapping_add(delta))),
                                    _ => Ok(JsVal::Int(delta)),
                                }
                            },
                            ReactionHandler::MulInt { factor, trace_id } => {
                                if trace_id != 0 {
                                    let ghost pre_t = self.states();
                                    self.trace_log.push(trace_id);
                                    proof { assert(self.states() =~= pre_t); }
                                }
                                match argument {
                                    JsVal::Int(x) => Ok(JsVal::Int(x.wrapping_mul(factor))),
                                    _ => Ok(JsVal::Int(0)),
                                }
                            },
                            ReactionHandler::TracePass { event_id, is_throw } => {
                                let ghost pre_t = self.states();
                                self.trace_log.push(event_id);
                                proof { assert(self.states() =~= pre_t); }
                                if is_throw { Err(argument) } else { Ok(argument) }
                            },
                            ReactionHandler::TraceReturn { event_id, ret } => {
                                let ghost pre_t = self.states();
                                self.trace_log.push(event_id);
                                proof { assert(self.states() =~= pre_t); }
                                Ok(ret)
                            },
                            _ => Ok(argument),
                        };

                        match reaction.capability {
                            None => Ok(true),
                            Some(cap) => {
                                match eval_outcome {
                                    Ok(normal_val) => {
                                        let _ = self.resolve_promise_internal(cap.promise_id, normal_val)?;
                                        Ok(true)
                                    },
                                    Err(abrupt_reason) => {
                                        let _ = self.reject_promise(cap.promise_id, abrupt_reason)?;
                                        Ok(true)
                                    },
                                }
                            },
                        }
                    },
                }
            },
        }
    }

    /// **Verified Microtask Queue Drain (`decreases fuel`)**:
    /// Executes FIFO microtask transitions until either:
    /// - `DrainOutcome::Done { steps_executed }`: `self.queue@.len() == 0` and `steps_executed <= fuel`, OR
    /// - `DrainOutcome::OutOfFuel { steps_executed }`: `steps_executed == fuel` and `fuel` real
    ///   FIFO microtask transitions were executed (`executed_jobs@.len() == old.executed_jobs@.len() + fuel`).
    /// Preserves Settle-Once Monotonicity across the entire execution!
    pub fn drain_jobs(&mut self, fuel: usize) -> (res: Result<DrainOutcome, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            // (a) Settle-Once Monotonicity across arbitrary-length microtask chains!
            spec_settled_monotonic(old(self).states(), final(self).states()),
            // (b) Liveness Under Fuel!
            match res {
                Ok(DrainOutcome::Done { steps_executed }) => {
                    &&& steps_executed <= fuel
                    &&& final(self).queue@.len() == 0
                    &&& final(self).executed_jobs@.len() == old(self).executed_jobs@.len() + (steps_executed as int)
                },
                Ok(DrainOutcome::OutOfFuel { steps_executed }) => {
                    &&& steps_executed == fuel
                    &&& final(self).executed_jobs@.len() == old(self).executed_jobs@.len() + (fuel as int)
                },
                Err(_) => true,
            },
    {
        let mut steps: usize = 0;

        while steps < fuel
            invariant
                steps <= fuel,
                self.wf(),
                spec_settled_monotonic(old(self).states(), self.states()),
                self.executed_jobs@.len() == old(self).executed_jobs@.len() + (steps as int),
            decreases fuel - steps,
        {
            if self.queue.is_empty() {
                return Ok(DrainOutcome::Done { steps_executed: steps });
            }
            let ghost s_before = self.states();
            let stepped_res = self.step_microtask();
            proof {
                lemma_settled_monotonic_transitive(old(self).states(), s_before, self.states());
            }
            let stepped = stepped_res?;
            if !stepped {
                proof { assert(false); }
                return Ok(DrainOutcome::Done { steps_executed: steps });
            }
            steps += 1;
        }

        if self.queue.is_empty() {
            Ok(DrainOutcome::Done { steps_executed: steps })
        } else {
            Ok(DrainOutcome::OutOfFuel { steps_executed: steps })
        }
    }
}

pub open spec fn final_or_cur_states(promises: Seq<PromiseRecord>) -> Seq<PromiseState> {
    spec_promise_states(promises)
}

// -----------------------------------------------------------------------------------------------
// Pure Spec Model & Standalone Theorems for Settle-Once Monotonicity & FIFO Liveness
// -----------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpecPromiseOp {
    AllocPending,
    Fulfill { pid: usize, val: JsVal },
    Reject { pid: usize, reason: JsVal },
}

pub open spec fn spec_apply_op(states: Seq<PromiseState>, op: SpecPromiseOp) -> Seq<PromiseState> {
    match op {
        SpecPromiseOp::AllocPending => states.push(PromiseState::Pending),
        SpecPromiseOp::Fulfill { pid, val } => {
            if (pid as int) < states.len() && states[pid as int] == PromiseState::Pending {
                states.update(pid as int, PromiseState::Fulfilled(val))
            } else {
                states
            }
        },
        SpecPromiseOp::Reject { pid, reason } => {
            if (pid as int) < states.len() && states[pid as int] == PromiseState::Pending {
                states.update(pid as int, PromiseState::Rejected(reason))
            } else {
                states
            }
        },
    }
}

pub open spec fn spec_apply_ops(states: Seq<PromiseState>, ops: Seq<SpecPromiseOp>) -> Seq<PromiseState>
    decreases ops.len(),
{
    if ops.len() == 0 {
        states
    } else {
        spec_apply_ops(
            spec_apply_op(states, ops[0]),
            ops.subrange(1, ops.len() as int),
        )
    }
}

/// **Theorem (Settle-Once Monotonicity over Arbitrary Transition Sequences)**:
/// Once `states[pid]` is settled (`Fulfilled(v)` or `Rejected(r)`), NO sequence `ops` of
/// `AllocPending` / `Fulfill` / `Reject` transitions of ANY length can ever change `states[pid]`!
pub proof fn theorem_settle_once_monotonic_arbitrary_ops(
    states: Seq<PromiseState>,
    ops: Seq<SpecPromiseOp>,
)
    ensures
        spec_settled_monotonic(states, spec_apply_ops(states, ops)),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let s1 = spec_apply_op(states, ops[0]);
        assert(spec_settled_monotonic(states, s1));
        let rest = ops.subrange(1, ops.len() as int);
        theorem_settle_once_monotonic_arbitrary_ops(s1, rest);
        lemma_settled_monotonic_transitive(states, s1, spec_apply_ops(s1, rest));
    }
}

/// **Theorem (Pure FIFO Leaf Queue Liveness Under Fuel)**:
/// Modeling a pure FIFO leaf microtask queue (`q -> q.subrange(1, q.len())`), `spec_drain_leaf_fifo(q, fuel)`
/// executes jobs in exact index order `0, 1, ...` and empties `q` iff `fuel >= q.len()`.
pub open spec fn spec_drain_leaf_fifo(
    q: Seq<MicrotaskJob>,
    fuel: nat,
) -> (Seq<MicrotaskJob>, Seq<MicrotaskJob>)
    decreases fuel,
{
    if q.len() == 0 || fuel == 0 {
        (q, Seq::empty())
    } else {
        let (rem, ran) = spec_drain_leaf_fifo(q.subrange(1, q.len() as int), (fuel - 1) as nat);
        (rem, seq![q[0]] + ran)
    }
}

pub proof fn theorem_fifo_order_and_liveness_under_fuel(q: Seq<MicrotaskJob>, fuel: nat)
    ensures
        ({
            let (rem, ran) = spec_drain_leaf_fifo(q, fuel);
            // Exact FIFO preservation: `ran + rem == q`!
            &&& ran + rem == q
            // Liveness under sufficient fuel: `fuel >= q.len() ==> rem.len() == 0 && ran == q`!
            &&& (fuel >= q.len() ==> rem.len() == 0 && ran == q)
            // Exact fuel consumption when under-fueled: `fuel < q.len() ==> ran.len() == fuel && rem.len() == q.len() - fuel`!
            &&& (fuel < q.len() ==> ran.len() == fuel && rem.len() == q.len() - fuel)
        }),
    decreases fuel,
{
    if q.len() == 0 || fuel == 0 {
        assert(Seq::<MicrotaskJob>::empty() + q =~= q);
    } else {
        let tail = q.subrange(1, q.len() as int);
        theorem_fifo_order_and_liveness_under_fuel(tail, (fuel - 1) as nat);
        let (rem, ran) = spec_drain_leaf_fifo(tail, (fuel - 1) as nat);
        assert((seq![q[0]] + ran) + rem =~= seq![q[0]] + (ran + rem));
        assert(seq![q[0]] + tail =~= q);
    }
}

} // verus!
