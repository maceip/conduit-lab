//! Capability-gated Web IDL host dispatcher (`dispatch`) and machine-checked browser
//! security & non-interference theorems.
//!
//! Architecture: `docs/verified-browser-engine.md` §3.2–§3.3 (Quark-style verified shim + J4b).
//! Every host call from `vjs` enters `dispatch(table, arena, state, caller_realm, h, req)`:
//! 1. Validates `h` against the kernel's generational `KernelCapTable` (defeating handle
//!    forgery, tampering, use-after-revoke, and ABA use-after-realloc).
//! 2. Enforces strict realm and origin matching (`caller_realm == h.realm` and
//!    `slot.origin == req.target_origin`), refusing cross-realm/cross-origin calls with
//!    `Err(HostError::CrossRealmViolation)` and zero state mutation.
//! 3. Enforces capability kind and bitmask permissions (`spec_has_perms`).
//! 4. Runs verified Web IDL `ToIDL` conversions on untrusted `JsValue` arguments, mutates
//!    ONLY `(caller_realm, target_origin)`'s state partition, and returns a `ToJS` `JsValue`.

use vstd::prelude::*;
use crate::caps::{
    CapHandle, CapKind, HostError, KernelCapTable, OriginId, RealmId,
    PERM_LOG, PERM_NETWORK, PERM_READ, PERM_SCHEDULE, PERM_WRITE,
};
use crate::conversions::{
    IntAttr, JsObjectArena, JsValue, SpecJsValue,
    to_idl_byte_string, to_idl_dom_string, to_idl_node_op, to_idl_request_init,
    to_idl_storage_op, to_idl_unsigned_long, to_idl_url_href, to_idl_usv_string,
    to_js_boolean, to_js_nullable_dom_string, to_js_undefined, to_js_unsigned_long,
};

verus! {

#[cfg(verus_keep_ghost)]
use crate::caps::{
    KernelCapSlot,
    lemma_no_handle_tampering, lemma_perms_monotonicity, lemma_revoked_handle_permanently_dead,
    spec_handle_origin, spec_handle_resource, spec_has_perms, spec_perms_subset,
    spec_table_evolves, spec_valid_handle,
};
#[cfg(verus_keep_ghost)]
use crate::conversions::{spec_has_no_unpaired_surrogates, spec_to_idl_node_op};

// ---------------------------------------------------------------------------------------
// Partitioned Host World State
// ---------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DomNodeEntry {
    pub realm: RealmId,
    pub origin: OriginId,
    pub node_id: u32,
    pub text_content: Option<Vec<u16>>,
    pub last_attr: Option<(Vec<u16>, Vec<u16>)>,
}

pub struct SpecDomNodeEntry {
    pub realm: RealmId,
    pub origin: OriginId,
    pub node_id: u32,
    pub text_content: Option<Seq<u16>>,
    pub last_attr: Option<(Seq<u16>, Seq<u16>)>,
}

impl View for DomNodeEntry {
    type V = SpecDomNodeEntry;

    open spec fn view(&self) -> SpecDomNodeEntry {
        SpecDomNodeEntry {
            realm: self.realm,
            origin: self.origin,
            node_id: self.node_id,
            text_content: match &self.text_content {
                None => None,
                Some(t) => Some(t@),
            },
            last_attr: match &self.last_attr {
                None => None,
                Some((k, v)) => Some((k@, v@)),
            },
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StorageEntry {
    pub origin: OriginId,
    pub key: Vec<u16>,
    pub value: Vec<u16>,
}

pub struct SpecStorageEntry {
    pub origin: OriginId,
    pub key: Seq<u16>,
    pub value: Seq<u16>,
}

impl View for StorageEntry {
    type V = SpecStorageEntry;

    open spec fn view(&self) -> SpecStorageEntry {
        SpecStorageEntry {
            origin: self.origin,
            key: self.key@,
            value: self.value@,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CookieEntry {
    pub origin: OriginId,
    pub raw_cookie: Vec<u8>,
}

pub struct SpecCookieEntry {
    pub origin: OriginId,
    pub raw_cookie: Seq<u8>,
}

impl View for CookieEntry {
    type V = SpecCookieEntry;

    open spec fn view(&self) -> SpecCookieEntry {
        SpecCookieEntry {
            origin: self.origin,
            raw_cookie: self.raw_cookie@,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct QueuedFetchEntry {
    pub origin: OriginId,
    pub href: Vec<u16>,
    pub method: Vec<u8>,
    pub keepalive: bool,
}

pub struct SpecQueuedFetchEntry {
    pub origin: OriginId,
    pub href: Seq<u16>,
    pub method: Seq<u8>,
    pub keepalive: bool,
}

impl View for QueuedFetchEntry {
    type V = SpecQueuedFetchEntry;

    open spec fn view(&self) -> SpecQueuedFetchEntry {
        SpecQueuedFetchEntry {
            origin: self.origin,
            href: self.href@,
            method: self.method@,
            keepalive: self.keepalive,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConsoleLogEntry {
    pub realm: RealmId,
    pub origin: OriginId,
    pub message: Vec<u16>,
}

pub struct SpecConsoleLogEntry {
    pub realm: RealmId,
    pub origin: OriginId,
    pub message: Seq<u16>,
}

impl View for ConsoleLogEntry {
    type V = SpecConsoleLogEntry;

    open spec fn view(&self) -> SpecConsoleLogEntry {
        SpecConsoleLogEntry {
            realm: self.realm,
            origin: self.origin,
            message: self.message@,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TimerQueueEntry {
    pub realm: RealmId,
    pub origin: OriginId,
    pub delay_ms: u32,
    pub callback_id: u32,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HostState {
    pub dom_nodes: Vec<DomNodeEntry>,
    pub storage: Vec<StorageEntry>,
    pub cookies: Vec<CookieEntry>,
    pub fetches: Vec<QueuedFetchEntry>,
    pub console: Vec<ConsoleLogEntry>,
    pub timers: Vec<TimerQueueEntry>,
}

pub struct SpecHostState {
    pub dom_nodes: Seq<SpecDomNodeEntry>,
    pub storage: Seq<SpecStorageEntry>,
    pub cookies: Seq<SpecCookieEntry>,
    pub fetches: Seq<SpecQueuedFetchEntry>,
    pub console: Seq<SpecConsoleLogEntry>,
    pub timers: Seq<TimerQueueEntry>,
}

impl View for HostState {
    type V = SpecHostState;

    open spec fn view(&self) -> SpecHostState {
        SpecHostState {
            dom_nodes: Seq::new(self.dom_nodes@.len(), |i: int| self.dom_nodes@[i]@),
            storage: Seq::new(self.storage@.len(), |i: int| self.storage@[i]@),
            cookies: Seq::new(self.cookies@.len(), |i: int| self.cookies@[i]@),
            fetches: Seq::new(self.fetches@.len(), |i: int| self.fetches@[i]@),
            console: Seq::new(self.console@.len(), |i: int| self.console@[i]@),
            timers: self.timers@,
        }
    }
}

impl HostState {
    pub fn new() -> (s: Self)
        ensures
            s@.dom_nodes.len() == 0,
            s@.storage.len() == 0,
            s@.cookies.len() == 0,
            s@.fetches.len() == 0,
            s@.console.len() == 0,
            s@.timers.len() == 0,
    {
        HostState {
            dom_nodes: Vec::new(),
            storage: Vec::new(),
            cookies: Vec::new(),
            fetches: Vec::new(),
            console: Vec::new(),
            timers: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Per-Origin and Per-Realm State Partition Projections (for Non-Interference Proofs)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_filter_storage_by_origin(
    entries: Seq<SpecStorageEntry>,
    origin: OriginId,
) -> Seq<SpecStorageEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_storage_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_cookies_by_origin(
    entries: Seq<SpecCookieEntry>,
    origin: OriginId,
) -> Seq<SpecCookieEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_cookies_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_fetches_by_origin(
    entries: Seq<SpecQueuedFetchEntry>,
    origin: OriginId,
) -> Seq<SpecQueuedFetchEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_fetches_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_dom_by_realm(
    entries: Seq<SpecDomNodeEntry>,
    realm: RealmId,
) -> Seq<SpecDomNodeEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_dom_by_realm(entries.subrange(1, entries.len() as int), realm);
        if entries[0].realm == realm {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_console_by_realm(
    entries: Seq<SpecConsoleLogEntry>,
    realm: RealmId,
) -> Seq<SpecConsoleLogEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_console_by_realm(entries.subrange(1, entries.len() as int), realm);
        if entries[0].realm == realm {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_timers_by_realm(
    entries: Seq<TimerQueueEntry>,
    realm: RealmId,
) -> Seq<TimerQueueEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_timers_by_realm(entries.subrange(1, entries.len() as int), realm);
        if entries[0].realm == realm {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_dom_by_origin(
    entries: Seq<SpecDomNodeEntry>,
    origin: OriginId,
) -> Seq<SpecDomNodeEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_dom_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_console_by_origin(
    entries: Seq<SpecConsoleLogEntry>,
    origin: OriginId,
) -> Seq<SpecConsoleLogEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_console_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_timers_by_origin(
    entries: Seq<TimerQueueEntry>,
    origin: OriginId,
) -> Seq<TimerQueueEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_timers_by_origin(entries.subrange(1, entries.len() as int), origin);
        if entries[0].origin == origin {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

pub open spec fn spec_filter_dom_by_node_id(
    entries: Seq<SpecDomNodeEntry>,
    node_id: u32,
) -> Seq<SpecDomNodeEntry>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        let rest = spec_filter_dom_by_node_id(entries.subrange(1, entries.len() as int), node_id);
        if entries[0].node_id == node_id {
            seq![entries[0]] + rest
        } else {
            rest
        }
    }
}

/// True iff every state slice belonging to any realm `r != active_realm` or any origin
/// `o != active_origin` across ALL 6 host subsystems is identical between `before` and `after`.
pub open spec fn spec_non_interfering_transition(
    before: SpecHostState,
    after: SpecHostState,
    active_realm: RealmId,
    active_origin: OriginId,
) -> bool {
    (forall|o: OriginId| o != active_origin ==> (
        spec_filter_storage_by_origin(#[trigger] after.storage, o)
            == spec_filter_storage_by_origin(before.storage, o)
        && spec_filter_cookies_by_origin(after.cookies, o)
            == spec_filter_cookies_by_origin(before.cookies, o)
        && spec_filter_fetches_by_origin(after.fetches, o)
            == spec_filter_fetches_by_origin(before.fetches, o)
        && spec_filter_dom_by_origin(after.dom_nodes, o)
            == spec_filter_dom_by_origin(before.dom_nodes, o)
        && spec_filter_console_by_origin(after.console, o)
            == spec_filter_console_by_origin(before.console, o)
        && spec_filter_timers_by_origin(after.timers, o)
            == spec_filter_timers_by_origin(before.timers, o)
    ))
    && (forall|r: RealmId| r != active_realm ==> (
        spec_filter_dom_by_realm(#[trigger] after.dom_nodes, r)
            == spec_filter_dom_by_realm(before.dom_nodes, r)
        && spec_filter_console_by_realm(after.console, r)
            == spec_filter_console_by_realm(before.console, r)
        && spec_filter_timers_by_realm(after.timers, r)
            == spec_filter_timers_by_realm(before.timers, r)
    ))
}

proof fn lemma_push_storage_preserves_other_origins(
    entries: Seq<SpecStorageEntry>,
    item: SpecStorageEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_storage_by_origin(entries.push(item), other)
            == spec_filter_storage_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_storage_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecStorageEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_storage_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_update_storage_preserves_other_origins(
    entries: Seq<SpecStorageEntry>,
    idx: int,
    item: SpecStorageEntry,
    other: OriginId,
)
    requires
        0 <= idx < entries.len(),
        entries[idx].origin != other,
        item.origin != other,
    ensures
        spec_filter_storage_by_origin(entries.update(idx, item), other)
            == spec_filter_storage_by_origin(entries, other),
    decreases entries.len(),
{
    let upd = entries.update(idx, item);
    if idx == 0 {
        assert(upd[0] == item);
        assert(upd.subrange(1, upd.len() as int) =~= entries.subrange(1, entries.len() as int));
    } else {
        assert(upd[0] == entries[0]);
        let tail = entries.subrange(1, entries.len() as int);
        assert(upd.subrange(1, upd.len() as int) =~= tail.update(idx - 1, item));
        assert(tail[idx - 1] == entries[idx]);
        lemma_update_storage_preserves_other_origins(tail, idx - 1, item, other);
    }
}

proof fn lemma_push_cookie_preserves_other_origins(
    entries: Seq<SpecCookieEntry>,
    item: SpecCookieEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_cookies_by_origin(entries.push(item), other)
            == spec_filter_cookies_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_cookies_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecCookieEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_cookie_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_push_fetch_preserves_other_origins(
    entries: Seq<SpecQueuedFetchEntry>,
    item: SpecQueuedFetchEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_fetches_by_origin(entries.push(item), other)
            == spec_filter_fetches_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_fetches_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecQueuedFetchEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_fetch_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_push_dom_preserves_other_realms(
    entries: Seq<SpecDomNodeEntry>,
    item: SpecDomNodeEntry,
    other: RealmId,
)
    requires
        item.realm != other,
    ensures
        spec_filter_dom_by_realm(entries.push(item), other)
            == spec_filter_dom_by_realm(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_dom_by_realm, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecDomNodeEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_dom_preserves_other_realms(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_update_dom_preserves_other_realms(
    entries: Seq<SpecDomNodeEntry>,
    idx: int,
    item: SpecDomNodeEntry,
    other: RealmId,
)
    requires
        0 <= idx < entries.len(),
        entries[idx].realm != other,
        item.realm != other,
    ensures
        spec_filter_dom_by_realm(entries.update(idx, item), other)
            == spec_filter_dom_by_realm(entries, other),
    decreases entries.len(),
{
    let upd = entries.update(idx, item);
    if idx == 0 {
        assert(upd[0] == item);
        assert(upd.subrange(1, upd.len() as int) =~= entries.subrange(1, entries.len() as int));
    } else {
        assert(upd[0] == entries[0]);
        let tail = entries.subrange(1, entries.len() as int);
        assert(upd.subrange(1, upd.len() as int) =~= tail.update(idx - 1, item));
        assert(tail[idx - 1] == entries[idx]);
        lemma_update_dom_preserves_other_realms(tail, idx - 1, item, other);
    }
}

proof fn lemma_push_console_preserves_other_realms(
    entries: Seq<SpecConsoleLogEntry>,
    item: SpecConsoleLogEntry,
    other: RealmId,
)
    requires
        item.realm != other,
    ensures
        spec_filter_console_by_realm(entries.push(item), other)
            == spec_filter_console_by_realm(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_console_by_realm, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecConsoleLogEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_console_preserves_other_realms(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_push_timer_preserves_other_realms(
    entries: Seq<TimerQueueEntry>,
    item: TimerQueueEntry,
    other: RealmId,
)
    requires
        item.realm != other,
    ensures
        spec_filter_timers_by_realm(entries.push(item), other)
            == spec_filter_timers_by_realm(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_timers_by_realm, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<TimerQueueEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_timer_preserves_other_realms(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_push_dom_preserves_other_origins(
    entries: Seq<SpecDomNodeEntry>,
    item: SpecDomNodeEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_dom_by_origin(entries.push(item), other)
            == spec_filter_dom_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_dom_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecDomNodeEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_dom_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_update_dom_preserves_other_origins(
    entries: Seq<SpecDomNodeEntry>,
    idx: int,
    item: SpecDomNodeEntry,
    other: OriginId,
)
    requires
        0 <= idx < entries.len(),
        entries[idx].origin != other,
        item.origin != other,
    ensures
        spec_filter_dom_by_origin(entries.update(idx, item), other)
            == spec_filter_dom_by_origin(entries, other),
    decreases entries.len(),
{
    let upd = entries.update(idx, item);
    if idx == 0 {
        assert(upd[0] == item);
        assert(upd.subrange(1, upd.len() as int) =~= entries.subrange(1, entries.len() as int));
    } else {
        assert(upd[0] == entries[0]);
        let tail = entries.subrange(1, entries.len() as int);
        assert(upd.subrange(1, upd.len() as int) =~= tail.update(idx - 1, item));
        assert(tail[idx - 1] == entries[idx]);
        lemma_update_dom_preserves_other_origins(tail, idx - 1, item, other);
    }
}

proof fn lemma_update_dom_preserves_other_nodes(
    entries: Seq<SpecDomNodeEntry>,
    idx: int,
    item: SpecDomNodeEntry,
    other_node_id: u32,
)
    requires
        0 <= idx < entries.len(),
        entries[idx].node_id != other_node_id,
        item.node_id != other_node_id,
    ensures
        spec_filter_dom_by_node_id(entries.update(idx, item), other_node_id)
            == spec_filter_dom_by_node_id(entries, other_node_id),
    decreases entries.len(),
{
    let upd = entries.update(idx, item);
    if idx == 0 {
        assert(upd[0] == item);
        assert(upd.subrange(1, upd.len() as int) =~= entries.subrange(1, entries.len() as int));
    } else {
        assert(upd[0] == entries[0]);
        let tail = entries.subrange(1, entries.len() as int);
        assert(upd.subrange(1, upd.len() as int) =~= tail.update(idx - 1, item));
        assert(tail[idx - 1] == entries[idx]);
        lemma_update_dom_preserves_other_nodes(tail, idx - 1, item, other_node_id);
    }
}

proof fn lemma_push_console_preserves_other_origins(
    entries: Seq<SpecConsoleLogEntry>,
    item: SpecConsoleLogEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_console_by_origin(entries.push(item), other)
            == spec_filter_console_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_console_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<SpecConsoleLogEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_console_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

proof fn lemma_push_timer_preserves_other_origins(
    entries: Seq<TimerQueueEntry>,
    item: TimerQueueEntry,
    other: OriginId,
)
    requires
        item.origin != other,
    ensures
        spec_filter_timers_by_origin(entries.push(item), other)
            == spec_filter_timers_by_origin(entries, other),
    decreases entries.len(),
{
    let pushed = entries.push(item);
    reveal_with_fuel(spec_filter_timers_by_origin, 2);
    if entries.len() == 0 {
        assert(pushed =~= seq![item]);
        assert(pushed.subrange(1, 1) =~= Seq::<TimerQueueEntry>::empty());
    } else {
        assert(pushed[0] == entries[0]);
        assert(pushed.subrange(1, pushed.len() as int)
            =~= entries.subrange(1, entries.len() as int).push(item));
        lemma_push_timer_preserves_other_origins(
            entries.subrange(1, entries.len() as int),
            item,
            other,
        );
    }
}

// ---------------------------------------------------------------------------------------
// Host Requests Across All 7 `CapKind` Categories
// ---------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HostRequest {
    DomSetTitle {
        target_origin: OriginId,
        title_js: JsValue,
    },
    DomMutateNode {
        target_origin: OriginId,
        node_op_js: JsValue,
    },
    FetchSend {
        target_origin: OriginId,
        url_href_js: JsValue,
        request_init_js: JsValue,
    },
    CookieSet {
        target_origin: OriginId,
        cookie_js: JsValue,
    },
    CookieCount {
        target_origin: OriginId,
    },
    StorageCommand {
        target_origin: OriginId,
        storage_op_js: JsValue,
        is_write: bool,
    },
    ConsoleLog {
        target_origin: OriginId,
        message_js: JsValue,
    },
    TimerSetTimeout {
        target_origin: OriginId,
        delay_js: JsValue,
        callback_id_js: JsValue,
    },
}

pub enum SpecHostRequest {
    DomSetTitle {
        target_origin: OriginId,
        title_js: SpecJsValue,
    },
    DomMutateNode {
        target_origin: OriginId,
        node_op_js: SpecJsValue,
    },
    FetchSend {
        target_origin: OriginId,
        url_href_js: SpecJsValue,
        request_init_js: SpecJsValue,
    },
    CookieSet {
        target_origin: OriginId,
        cookie_js: SpecJsValue,
    },
    CookieCount {
        target_origin: OriginId,
    },
    StorageCommand {
        target_origin: OriginId,
        storage_op_js: SpecJsValue,
        is_write: bool,
    },
    ConsoleLog {
        target_origin: OriginId,
        message_js: SpecJsValue,
    },
    TimerSetTimeout {
        target_origin: OriginId,
        delay_js: SpecJsValue,
        callback_id_js: SpecJsValue,
    },
}

impl View for HostRequest {
    type V = SpecHostRequest;

    open spec fn view(&self) -> SpecHostRequest {
        match self {
            HostRequest::DomSetTitle { target_origin, title_js } =>
                SpecHostRequest::DomSetTitle {
                    target_origin: *target_origin,
                    title_js: title_js@,
                },
            HostRequest::DomMutateNode { target_origin, node_op_js } =>
                SpecHostRequest::DomMutateNode {
                    target_origin: *target_origin,
                    node_op_js: node_op_js@,
                },
            HostRequest::FetchSend { target_origin, url_href_js, request_init_js } =>
                SpecHostRequest::FetchSend {
                    target_origin: *target_origin,
                    url_href_js: url_href_js@,
                    request_init_js: request_init_js@,
                },
            HostRequest::CookieSet { target_origin, cookie_js } =>
                SpecHostRequest::CookieSet {
                    target_origin: *target_origin,
                    cookie_js: cookie_js@,
                },
            HostRequest::CookieCount { target_origin } =>
                SpecHostRequest::CookieCount { target_origin: *target_origin },
            HostRequest::StorageCommand { target_origin, storage_op_js, is_write } =>
                SpecHostRequest::StorageCommand {
                    target_origin: *target_origin,
                    storage_op_js: storage_op_js@,
                    is_write: *is_write,
                },
            HostRequest::ConsoleLog { target_origin, message_js } =>
                SpecHostRequest::ConsoleLog {
                    target_origin: *target_origin,
                    message_js: message_js@,
                },
            HostRequest::TimerSetTimeout { target_origin, delay_js, callback_id_js } =>
                SpecHostRequest::TimerSetTimeout {
                    target_origin: *target_origin,
                    delay_js: delay_js@,
                    callback_id_js: callback_id_js@,
                },
        }
    }
}

pub open spec fn spec_req_target_origin(req: SpecHostRequest) -> OriginId {
    match req {
        SpecHostRequest::DomSetTitle { target_origin, .. } => target_origin,
        SpecHostRequest::DomMutateNode { target_origin, .. } => target_origin,
        SpecHostRequest::FetchSend { target_origin, .. } => target_origin,
        SpecHostRequest::CookieSet { target_origin, .. } => target_origin,
        SpecHostRequest::CookieCount { target_origin } => target_origin,
        SpecHostRequest::StorageCommand { target_origin, .. } => target_origin,
        SpecHostRequest::ConsoleLog { target_origin, .. } => target_origin,
        SpecHostRequest::TimerSetTimeout { target_origin, .. } => target_origin,
    }
}

pub open spec fn spec_req_expected_kind(req: SpecHostRequest) -> CapKind {
    match req {
        SpecHostRequest::DomSetTitle { .. } => CapKind::DomDocument,
        SpecHostRequest::DomMutateNode { .. } => CapKind::DomNode,
        SpecHostRequest::FetchSend { .. } => CapKind::FetchOrigin,
        SpecHostRequest::CookieSet { .. } | SpecHostRequest::CookieCount { .. } =>
            CapKind::CookieJarOrigin,
        SpecHostRequest::StorageCommand { .. } => CapKind::StorageOrigin,
        SpecHostRequest::ConsoleLog { .. } => CapKind::ConsoleSink,
        SpecHostRequest::TimerSetTimeout { .. } => CapKind::TimerQueue,
    }
}

pub open spec fn spec_req_required_perms(req: SpecHostRequest) -> u8 {
    match req {
        SpecHostRequest::DomSetTitle { .. } => PERM_WRITE,
        SpecHostRequest::DomMutateNode { .. } => PERM_WRITE,
        SpecHostRequest::FetchSend { .. } => PERM_NETWORK,
        SpecHostRequest::CookieSet { .. } => PERM_WRITE,
        SpecHostRequest::CookieCount { .. } => PERM_READ,
        SpecHostRequest::StorageCommand { is_write, .. } =>
            if is_write { PERM_WRITE } else { PERM_READ },
        SpecHostRequest::ConsoleLog { .. } => PERM_LOG,
        SpecHostRequest::TimerSetTimeout { .. } => PERM_SCHEDULE,
    }
}

impl HostRequest {
    pub fn target_origin(&self) -> (o: OriginId)
        ensures
            o == spec_req_target_origin(self@),
    {
        match self {
            HostRequest::DomSetTitle { target_origin, .. } => *target_origin,
            HostRequest::DomMutateNode { target_origin, .. } => *target_origin,
            HostRequest::FetchSend { target_origin, .. } => *target_origin,
            HostRequest::CookieSet { target_origin, .. } => *target_origin,
            HostRequest::CookieCount { target_origin } => *target_origin,
            HostRequest::StorageCommand { target_origin, .. } => *target_origin,
            HostRequest::ConsoleLog { target_origin, .. } => *target_origin,
            HostRequest::TimerSetTimeout { target_origin, .. } => *target_origin,
        }
    }

    pub fn expected_kind(&self) -> (k: CapKind)
        ensures
            k == spec_req_expected_kind(self@),
    {
        match self {
            HostRequest::DomSetTitle { .. } => CapKind::DomDocument,
            HostRequest::DomMutateNode { .. } => CapKind::DomNode,
            HostRequest::FetchSend { .. } => CapKind::FetchOrigin,
            HostRequest::CookieSet { .. } | HostRequest::CookieCount { .. } =>
                CapKind::CookieJarOrigin,
            HostRequest::StorageCommand { .. } => CapKind::StorageOrigin,
            HostRequest::ConsoleLog { .. } => CapKind::ConsoleSink,
            HostRequest::TimerSetTimeout { .. } => CapKind::TimerQueue,
        }
    }

    pub fn required_perms(&self) -> (p: u8)
        ensures
            p == spec_req_required_perms(self@),
    {
        match self {
            HostRequest::DomSetTitle { .. } => PERM_WRITE,
            HostRequest::DomMutateNode { .. } => PERM_WRITE,
            HostRequest::FetchSend { .. } => PERM_NETWORK,
            HostRequest::CookieSet { .. } => PERM_WRITE,
            HostRequest::CookieCount { .. } => PERM_READ,
            HostRequest::StorageCommand { is_write, .. } =>
                if *is_write { PERM_WRITE } else { PERM_READ },
            HostRequest::ConsoleLog { .. } => PERM_LOG,
            HostRequest::TimerSetTimeout { .. } => PERM_SCHEDULE,
        }
    }
}

fn kind_eq(a: CapKind, b: CapKind) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (CapKind::DomDocument, CapKind::DomDocument) => true,
        (CapKind::DomNode, CapKind::DomNode) => true,
        (CapKind::FetchOrigin, CapKind::FetchOrigin) => true,
        (CapKind::CookieJarOrigin, CapKind::CookieJarOrigin) => true,
        (CapKind::StorageOrigin, CapKind::StorageOrigin) => true,
        (CapKind::ConsoleSink, CapKind::ConsoleSink) => true,
        (CapKind::TimerQueue, CapKind::TimerQueue) => true,
        _ => false,
    }
}

fn slice_u16_eq(a: &[u16], b: &[u16]) -> (r: bool)
    ensures
        r == (a@ == b@),
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
        i += 1;
    }
    proof { assert(a@ =~= b@); }
    true
}

fn copy_u16_vec(v: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == v@,
{
    let n = v.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == v@.len(),
            out@ == v@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(v[i]);
        i += 1;
        proof { assert(out@ =~= v@.subrange(0, i as int)); }
    }
    proof { assert(v@.subrange(0, n as int) =~= v@); }
    out
}

// ---------------------------------------------------------------------------------------
// Capability-Gated Host `dispatch`
// ---------------------------------------------------------------------------------------

/// Spec-level authorization gate for `dispatch` (checks 1–4 before Web IDL conversion).
pub open spec fn spec_dispatch_gate(
    slots: Seq<KernelCapSlot>,
    caller_realm: RealmId,
    h: CapHandle,
    req: SpecHostRequest,
) -> Result<(), HostError> {
    if !spec_valid_handle(slots, h) {
        Err(HostError::RevokedOrInvalidHandle)
    } else if caller_realm != h.realm || spec_handle_origin(slots, h) != spec_req_target_origin(req) {
        Err(HostError::CrossRealmViolation)
    } else if h.kind != spec_req_expected_kind(req) {
        Err(HostError::WrongCapabilityKind)
    } else if !spec_has_perms(h.perms, spec_req_required_perms(req)) {
        Err(HostError::InsufficientPermissions)
    } else {
        Ok(())
    }
}

/// Verified Capability-Gated Host Boundary Dispatcher (`dispatch`).
///
/// Guarantees:
/// 1. Invalid, forged, tampered, or revoked handles unconditionally return
///    `Err(HostError::RevokedOrInvalidHandle)` with `final(state)@ == old(state)@`.
/// 2. Cross-realm (`caller_realm != h.realm`) or cross-origin
///    (`cap_origin != req.target_origin`) attempts unconditionally return
///    `Err(HostError::CrossRealmViolation)` with `final(state)@ == old(state)@`.
/// 3. Kind mismatches return `Err(HostError::WrongCapabilityKind)` and missing permission
///    bits return `Err(HostError::InsufficientPermissions)`, with zero state mutation.
/// 4. Every error path leaves `final(state)@ == old(state)@`.
/// 5. Every successful execution satisfies `spec_non_interfering_transition`: all state
///    belonging to any other realm `r != caller_realm` or any other origin
///    `o != req.target_origin` is 100% untouched!
/// Per-node confinement predicate for `DomMutateNode`:
/// 1. If the untrusted Web IDL `NodeOp` dictionary requests `snop.node_id != slot.resource_id`,
///    `dispatch` MUST refuse with `Err(HostError::InsufficientPermissions)` (defeating
///    confused-deputy capability bypasses across sibling DOM nodes in the same realm/origin).
/// 2. On `Ok(_)`, every DOM node entry with `nid != slot.resource_id` is 100% untouched!
pub open spec fn spec_dom_mutate_node_confined(
    slots: Seq<KernelCapSlot>,
    arena: Seq<crate::conversions::SpecJsObjectRecord>,
    before: SpecHostState,
    after: SpecHostState,
    h: CapHandle,
    req: SpecHostRequest,
    res: Result<JsValue, HostError>,
) -> bool {
    match req {
        SpecHostRequest::DomMutateNode { node_op_js, .. } => {
            let bound_node = spec_handle_resource(slots, h);
            (match spec_to_idl_node_op(arena, node_op_js) {
                Ok(snop) => snop.node_id != bound_node ==> (
                    res == Err::<JsValue, HostError>(HostError::InsufficientPermissions)
                    && after == before
                ),
                Err(_) => true,
            })
            && (match res {
                Ok(_) => forall|nid: u32| nid != bound_node ==>
                    spec_filter_dom_by_node_id(#[trigger] after.dom_nodes, nid)
                        == spec_filter_dom_by_node_id(before.dom_nodes, nid),
                Err(_) => after == before,
            })
        },
        _ => true,
    }
}

#[verifier::spinoff_prover]
pub fn dispatch(
    table: &KernelCapTable,
    arena: &JsObjectArena,
    state: &mut HostState,
    caller_realm: RealmId,
    h: CapHandle,
    req: &HostRequest,
) -> (res: Result<JsValue, HostError>)
    ensures
        match spec_dispatch_gate(table.slots@, caller_realm, h, req@) {
            Err(gate_err) => {
                res == Err::<JsValue, HostError>(gate_err)
                && final(state)@ == old(state)@
            },
            Ok(()) => {
                spec_dom_mutate_node_confined(
                    table.slots@,
                    arena@,
                    old(state)@,
                    final(state)@,
                    h,
                    req@,
                    res,
                )
                && match res {
                    Err(_) => final(state)@ == old(state)@,
                    Ok(_) => spec_non_interfering_transition(
                        old(state)@,
                        final(state)@,
                        caller_realm,
                        spec_req_target_origin(req@),
                    ),
                }
            },
        },
{
    // Gate 1: Authoritative Generational Capability Lookup
    if !table.validate(&h) {
        return Err(HostError::RevokedOrInvalidHandle);
    }
    let slot = table.slots[h.slot];
    let target_origin = req.target_origin();

    // Gate 2: Cross-Realm & Cross-Origin Non-Interference Gate
    if caller_realm.0 != h.realm.0 || slot.origin.0 != target_origin.0 {
        return Err(HostError::CrossRealmViolation);
    }

    // Gate 3: Capability Kind Gate
    let expected_kind = req.expected_kind();
    if !kind_eq(h.kind, expected_kind) {
        return Err(HostError::WrongCapabilityKind);
    }

    // Gate 4: Capability Bitmask Permissions Gate
    let required_perms = req.required_perms();
    if (required_perms & !h.perms) != 0u8 {
        return Err(HostError::InsufficientPermissions);
    }

    // Gate 5: Verified Web IDL `ToIDL` Conversion + Partitioned Kernel Action + `ToJS`
    match req {
        HostRequest::DomSetTitle { title_js, .. } => {
            let title = match to_idl_dom_string(arena, title_js, false) {
                Ok(t) => t,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let ghost old_dom = state@.dom_nodes;
            let entry = DomNodeEntry {
                realm: caller_realm,
                origin: target_origin,
                node_id: slot.resource_id,
                text_content: Some(title),
                last_attr: None,
            };
            let ghost sentry = entry@;
            state.dom_nodes.push(entry);
            proof {
                assert(state@.dom_nodes =~= old_dom.push(sentry));
                assert forall|r: RealmId| r != caller_realm implies
                    spec_filter_dom_by_realm(#[trigger] state@.dom_nodes, r)
                        == spec_filter_dom_by_realm(old_dom, r)
                by {
                    lemma_push_dom_preserves_other_realms(old_dom, sentry, r);
                }
                assert forall|o: OriginId| o != target_origin implies (
                    spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                        == spec_filter_storage_by_origin(old(state)@.storage, o)
                    && spec_filter_cookies_by_origin(state@.cookies, o)
                        == spec_filter_cookies_by_origin(old(state)@.cookies, o)
                    && spec_filter_fetches_by_origin(state@.fetches, o)
                        == spec_filter_fetches_by_origin(old(state)@.fetches, o)
                    && spec_filter_dom_by_origin(state@.dom_nodes, o)
                        == spec_filter_dom_by_origin(old_dom, o)
                    && spec_filter_console_by_origin(state@.console, o)
                        == spec_filter_console_by_origin(old(state)@.console, o)
                    && spec_filter_timers_by_origin(state@.timers, o)
                        == spec_filter_timers_by_origin(old(state)@.timers, o)
                ) by {
                    lemma_push_dom_preserves_other_origins(old_dom, sentry, o);
                }
            }
            Ok(to_js_undefined())
        },

        HostRequest::DomMutateNode { node_op_js, .. } => {
            let nop = match to_idl_node_op(arena, node_op_js) {
                Ok(n) => n,
                Err(e) => return Err(HostError::Idl(e)),
            };
            // Per-Resource Object Capability Gate: `DomNode` handle is bound to `slot.resource_id`!
            if nop.node_id != slot.resource_id {
                return Err(HostError::InsufficientPermissions);
            }
            // Locate node inside `(caller_realm, target_origin, slot.resource_id)` partition ONLY!
            let n = state.dom_nodes.len();
            let mut idx: usize = 0;
            while idx < n
                invariant
                    idx <= n,
                    n == state.dom_nodes@.len(),
                    state@ == old(state)@,
                    nop.node_id == slot.resource_id,
                    slot.resource_id == spec_handle_resource(table.slots@, h),
                    target_origin == spec_req_target_origin(req@),
                    req@ == (SpecHostRequest::DomMutateNode {
                        target_origin,
                        node_op_js: node_op_js@,
                    }),
                    spec_to_idl_node_op(arena@, node_op_js@)
                        == Ok::<crate::conversions::SpecNodeOp, crate::conversions::IdlError>(nop@),
                    spec_dispatch_gate(table.slots@, caller_realm, h, req@) == Ok::<(), HostError>(()),
                decreases n - idx,
            {
                let cur = &state.dom_nodes[idx];
                if cur.realm.0 == caller_realm.0
                    && cur.origin.0 == target_origin.0
                    && cur.node_id == nop.node_id
                {
                    let new_tc = match &nop.text_content {
                        Some(tc_opt) => match tc_opt {
                            None => None,
                            Some(s) => Some(copy_u16_vec(s.as_slice())),
                        },
                        None => match &cur.text_content {
                            None => None,
                            Some(s) => Some(copy_u16_vec(s.as_slice())),
                        },
                    };
                    let new_attr = match (&nop.attr_name, &nop.attr_value) {
                        (Some(an), Some(av)) =>
                            Some((copy_u16_vec(an.as_slice()), copy_u16_vec(av.as_slice()))),
                        _ => match &cur.last_attr {
                            None => None,
                            Some((k, v)) =>
                                Some((copy_u16_vec(k.as_slice()), copy_u16_vec(v.as_slice()))),
                        },
                    };
                    let updated = DomNodeEntry {
                        realm: caller_realm,
                        origin: target_origin,
                        node_id: nop.node_id,
                        text_content: new_tc,
                        last_attr: new_attr,
                    };
                    let ghost old_dom = state@.dom_nodes;
                    let ghost supdated = updated@;
                    proof {
                        assert(old_dom[idx as int].realm == caller_realm);
                        assert(old_dom[idx as int].origin == target_origin);
                        assert(old_dom[idx as int].node_id == nop.node_id);
                    }
                    state.dom_nodes.set(idx, updated);
                    proof {
                        assert(state@.dom_nodes =~= old_dom.update(idx as int, supdated));
                        assert forall|r: RealmId| r != caller_realm implies
                            spec_filter_dom_by_realm(#[trigger] state@.dom_nodes, r)
                                == spec_filter_dom_by_realm(old_dom, r)
                        by {
                            lemma_update_dom_preserves_other_realms(
                                old_dom,
                                idx as int,
                                supdated,
                                r,
                            );
                        }
                        assert forall|o: OriginId| o != target_origin implies (
                            spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                                == spec_filter_storage_by_origin(old(state)@.storage, o)
                            && spec_filter_cookies_by_origin(state@.cookies, o)
                                == spec_filter_cookies_by_origin(old(state)@.cookies, o)
                            && spec_filter_fetches_by_origin(state@.fetches, o)
                                == spec_filter_fetches_by_origin(old(state)@.fetches, o)
                            && spec_filter_dom_by_origin(state@.dom_nodes, o)
                                == spec_filter_dom_by_origin(old_dom, o)
                            && spec_filter_console_by_origin(state@.console, o)
                                == spec_filter_console_by_origin(old(state)@.console, o)
                            && spec_filter_timers_by_origin(state@.timers, o)
                                == spec_filter_timers_by_origin(old(state)@.timers, o)
                        ) by {
                            lemma_update_dom_preserves_other_origins(
                                old_dom,
                                idx as int,
                                supdated,
                                o,
                            );
                        }
                        assert forall|nid: u32| nid != slot.resource_id implies
                            spec_filter_dom_by_node_id(#[trigger] state@.dom_nodes, nid)
                                == spec_filter_dom_by_node_id(old_dom, nid)
                        by {
                            lemma_update_dom_preserves_other_nodes(
                                old_dom,
                                idx as int,
                                supdated,
                                nid,
                            );
                        }
                    }
                    return Ok(to_js_boolean(true));
                }
                idx += 1;
            }
            Err(HostError::DomNodeNotFound)
        },

        HostRequest::FetchSend { url_href_js, request_init_js, .. } => {
            let url_href = match to_idl_url_href(arena, url_href_js) {
                Ok(u) => u,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let req_init = match to_idl_request_init(arena, request_init_js) {
                Ok(r) => r,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let ghost old_fetches = state@.fetches;
            let entry = QueuedFetchEntry {
                origin: target_origin,
                href: url_href.href,
                method: req_init.method,
                keepalive: req_init.keepalive,
            };
            let ghost sentry = entry@;
            state.fetches.push(entry);
            proof {
                assert(spec_has_no_unpaired_surrogates(sentry.href));
                assert(state@.fetches =~= old_fetches.push(sentry));
                assert forall|o: OriginId| o != target_origin implies
                    spec_filter_fetches_by_origin(alias_fetches(#[trigger] state@.fetches), o)
                        == spec_filter_fetches_by_origin(old_fetches, o)
                by {
                    lemma_push_fetch_preserves_other_origins(old_fetches, sentry, o);
                }
                assert forall|o: OriginId| o != target_origin implies (
                    spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                        == spec_filter_storage_by_origin(old(state)@.storage, o)
                    && spec_filter_cookies_by_origin(state@.cookies, o)
                        == spec_filter_cookies_by_origin(old(state)@.cookies, o)
                    && spec_filter_fetches_by_origin(state@.fetches, o)
                        == spec_filter_fetches_by_origin(old_fetches, o)
                ) by {
                    lemma_push_fetch_preserves_other_origins(old_fetches, sentry, o);
                }
            }
            Ok(to_js_boolean(true))
        },

        HostRequest::CookieSet { cookie_js, .. } => {
            let raw_cookie = match to_idl_byte_string(arena, cookie_js) {
                Ok(c) => c,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let ghost old_cookies = state@.cookies;
            let entry = CookieEntry {
                origin: target_origin,
                raw_cookie,
            };
            let ghost sentry = entry@;
            state.cookies.push(entry);
            proof {
                assert(state@.cookies =~= old_cookies.push(sentry));
                assert forall|o: OriginId| o != target_origin implies (
                    spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                        == spec_filter_storage_by_origin(old(state)@.storage, o)
                    && spec_filter_cookies_by_origin(state@.cookies, o)
                        == spec_filter_cookies_by_origin(old_cookies, o)
                    && spec_filter_fetches_by_origin(state@.fetches, o)
                        == spec_filter_fetches_by_origin(old(state)@.fetches, o)
                ) by {
                    lemma_push_cookie_preserves_other_origins(old_cookies, sentry, o);
                }
            }
            Ok(to_js_undefined())
        },

        HostRequest::CookieCount { .. } => {
            let n = state.cookies.len();
            let mut i: usize = 0;
            let mut count: u32 = 0;
            while i < n
                invariant
                    i <= n,
                    n == state.cookies@.len(),
                    state@ == old(state)@,
                decreases n - i,
            {
                if state.cookies[i].origin.0 == target_origin.0 && count < u32::MAX {
                    count += 1;
                }
                i += 1;
            }
            Ok(to_js_unsigned_long(count))
        },

        HostRequest::StorageCommand { storage_op_js, is_write, .. } => {
            let sop = match to_idl_storage_op(arena, storage_op_js) {
                Ok(s) => s,
                Err(e) => return Err(HostError::Idl(e)),
            };
            if !*is_write {
                // Read-only lookup inside `target_origin` partition ONLY!
                let lookup_key = match &sop.key {
                    Some(Some(k)) => k,
                    _ => return Ok(to_js_nullable_dom_string(&None)),
                };
                let n = state.storage.len();
                let mut i: usize = 0;
                while i < n
                    invariant
                        i <= n,
                        n == state.storage@.len(),
                        state@ == old(state)@,
                        target_origin == spec_req_target_origin(req@),
                        spec_req_expected_kind(req@) == CapKind::StorageOrigin,
                        spec_dispatch_gate(table.slots@, caller_realm, h, req@) == Ok::<(), HostError>(()),
                    decreases n - i,
                {
                    let e = &state.storage[i];
                    if e.origin.0 == target_origin.0
                        && slice_u16_eq(e.key.as_slice(), lookup_key.as_slice())
                    {
                        let found = Some(copy_u16_vec(e.value.as_slice()));
                        return Ok(to_js_nullable_dom_string(&found));
                    }
                    i += 1;
                }
                Ok(to_js_nullable_dom_string(&None))
            } else {
                let (write_key, write_val) = match (&sop.key, &sop.value) {
                    (Some(Some(k)), Some(v)) =>
                        (copy_u16_vec(k.as_slice()), copy_u16_vec(v.as_slice())),
                    _ => return Ok(to_js_undefined()),
                };
                let n = state.storage.len();
                let mut i: usize = 0;
                while i < n
                    invariant
                        i <= n,
                        n == state.storage@.len(),
                        state@ == old(state)@,
                        target_origin == spec_req_target_origin(req@),
                        spec_req_expected_kind(req@) == CapKind::StorageOrigin,
                        spec_dispatch_gate(table.slots@, caller_realm, h, req@) == Ok::<(), HostError>(()),
                    decreases n - i,
                {
                    if state.storage[i].origin.0 == target_origin.0
                        && slice_u16_eq(state.storage[i].key.as_slice(), write_key.as_slice())
                    {
                        let ghost old_st = state@.storage;
                        let updated = StorageEntry {
                            origin: target_origin,
                            key: write_key,
                            value: write_val,
                        };
                        let ghost supd = updated@;
                        proof {
                            assert(old_st[i as int].origin == target_origin);
                        }
                        state.storage.set(i, updated);
                        proof {
                            assert(state@.storage =~= old_st.update(i as int, supd));
                            assert forall|o: OriginId| o != target_origin implies
                                spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                                    == spec_filter_storage_by_origin(old_st, o)
                            by {
                                lemma_update_storage_preserves_other_origins(
                                    old_st,
                                    i as int,
                                    supd,
                                    o,
                                );
                            }
                        }
                        return Ok(to_js_undefined());
                    }
                    i += 1;
                }
                let ghost old_st = state@.storage;
                let entry = StorageEntry {
                    origin: target_origin,
                    key: write_key,
                    value: write_val,
                };
                let ghost sentry = entry@;
                state.storage.push(entry);
                proof {
                    assert(state@.storage =~= old_st.push(sentry));
                    assert forall|o: OriginId| o != target_origin implies
                        spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                            == spec_filter_storage_by_origin(old_st, o)
                    by {
                        lemma_push_storage_preserves_other_origins(old_st, sentry, o);
                    }
                }
                Ok(to_js_undefined())
            }
        },

        HostRequest::ConsoleLog { message_js, .. } => {
            let msg = match to_idl_usv_string(arena, message_js) {
                Ok(m) => m,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let ghost old_con = state@.console;
            let entry = ConsoleLogEntry {
                realm: caller_realm,
                origin: target_origin,
                message: msg,
            };
            let ghost sentry = entry@;
            state.console.push(entry);
            proof {
                assert(spec_has_no_unpaired_surrogates(sentry.message));
                assert(state@.console =~= old_con.push(sentry));
                assert forall|r: RealmId| r != caller_realm implies (
                    spec_filter_dom_by_realm(#[trigger] state@.dom_nodes, r)
                        == spec_filter_dom_by_realm(old(state)@.dom_nodes, r)
                    && spec_filter_console_by_realm(state@.console, r)
                        == spec_filter_console_by_realm(old_con, r)
                    && spec_filter_timers_by_realm(state@.timers, r)
                        == spec_filter_timers_by_realm(old(state)@.timers, r)
                ) by {
                    lemma_push_console_preserves_other_realms(old_con, sentry, r);
                }
                assert forall|o: OriginId| o != target_origin implies (
                    spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                        == spec_filter_storage_by_origin(old(state)@.storage, o)
                    && spec_filter_cookies_by_origin(state@.cookies, o)
                        == spec_filter_cookies_by_origin(old(state)@.cookies, o)
                    && spec_filter_fetches_by_origin(state@.fetches, o)
                        == spec_filter_fetches_by_origin(old(state)@.fetches, o)
                    && spec_filter_dom_by_origin(state@.dom_nodes, o)
                        == spec_filter_dom_by_origin(old(state)@.dom_nodes, o)
                    && spec_filter_console_by_origin(state@.console, o)
                        == spec_filter_console_by_origin(old_con, o)
                    && spec_filter_timers_by_origin(state@.timers, o)
                        == spec_filter_timers_by_origin(old(state)@.timers, o)
                ) by {
                    lemma_push_console_preserves_other_origins(old_con, sentry, o);
                }
            }
            Ok(to_js_undefined())
        },

        HostRequest::TimerSetTimeout { delay_js, callback_id_js, .. } => {
            let delay_ms = match to_idl_unsigned_long(arena, delay_js, IntAttr::Clamp) {
                Ok(d) => d,
                Err(e) => return Err(HostError::Idl(e)),
            };
            let callback_id = match to_idl_unsigned_long(arena, callback_id_js, IntAttr::EnforceRange) {
                Ok(c) => c,
                Err(e) => return Err(HostError::Idl(e)),
            };
            if state.timers.len() >= (u32::MAX as usize) {
                return Err(HostError::CapacityExhausted);
            }
            let timer_id: u32 = state.timers.len() as u32;
            let ghost old_timers = state@.timers;
            let entry = TimerQueueEntry {
                realm: caller_realm,
                origin: target_origin,
                delay_ms,
                callback_id,
            };
            state.timers.push(entry);
            proof {
                assert(state@.timers =~= old_timers.push(entry));
                assert forall|r: RealmId| r != caller_realm implies (
                    spec_filter_dom_by_realm(#[trigger] state@.dom_nodes, r)
                        == spec_filter_dom_by_realm(old(state)@.dom_nodes, r)
                    && spec_filter_console_by_realm(state@.console, r)
                        == spec_filter_console_by_realm(old(state)@.console, r)
                    && spec_filter_timers_by_realm(state@.timers, r)
                        == spec_filter_timers_by_realm(old_timers, r)
                ) by {
                    lemma_push_timer_preserves_other_realms(old_timers, entry, r);
                }
                assert forall|o: OriginId| o != target_origin implies (
                    spec_filter_storage_by_origin(#[trigger] state@.storage, o)
                        == spec_filter_storage_by_origin(old(state)@.storage, o)
                    && spec_filter_cookies_by_origin(state@.cookies, o)
                        == spec_filter_cookies_by_origin(old(state)@.cookies, o)
                    && spec_filter_fetches_by_origin(state@.fetches, o)
                        == spec_filter_fetches_by_origin(old(state)@.fetches, o)
                    && spec_filter_dom_by_origin(state@.dom_nodes, o)
                        == spec_filter_dom_by_origin(old(state)@.dom_nodes, o)
                    && spec_filter_console_by_origin(state@.console, o)
                        == spec_filter_console_by_origin(old(state)@.console, o)
                    && spec_filter_timers_by_origin(state@.timers, o)
                        == spec_filter_timers_by_origin(old_timers, o)
                ) by {
                    lemma_push_timer_preserves_other_origins(old_timers, entry, o);
                }
            }
            Ok(to_js_unsigned_long(timer_id))
        },
    }
}

pub open spec fn alias_fetches(f: Seq<SpecQueuedFetchEntry>) -> Seq<SpecQueuedFetchEntry> {
    f
}

// ---------------------------------------------------------------------------------------
// Top-Level Machine-Checked Security Theorems (J4b §2(a), §2(b), §2(c))
// ---------------------------------------------------------------------------------------

/// Security Theorem (a1) — No Use-After-Revoke:
/// Immediately after `revoke(h)` succeeds (producing `slots_after_revoke`), `spec_dispatch_gate`
/// (and therefore `dispatch`) is guaranteed to return `Err(HostError::RevokedOrInvalidHandle)`
/// and leave `HostState` completely unchanged for ALL `caller_realm` and ALL `req`.
pub proof fn theorem_use_after_revoke_rejected(
    slots_before: Seq<KernelCapSlot>,
    slots_after_revoke: Seq<KernelCapSlot>,
    caller_realm: RealmId,
    h: CapHandle,
    req: SpecHostRequest,
)
    requires
        spec_valid_handle(slots_before, h),
        (h.slot as int) < slots_after_revoke.len(),
        !slots_after_revoke[h.slot as int].active,
        slots_after_revoke[h.slot as int].generation == h.generation + 1,
    ensures
        !spec_valid_handle(slots_after_revoke, h),
        spec_dispatch_gate(slots_after_revoke, caller_realm, h, req)
            == Err::<(), HostError>(HostError::RevokedOrInvalidHandle),
{
}

/// Security Theorem (a2) — Permanent Use-After-Revoke Across Arbitrary Reallocations (No ABA):
/// Even after `revoke(h)` is followed by any arbitrary sequence of future `allocate`,
/// `attenuate`, and `revoke` calls (`spec_table_evolves(slots_after_revoke, slots_later)`),
/// `h` remains permanently invalid and `dispatch` unconditionally refuses `h` with
/// `Err(HostError::RevokedOrInvalidHandle)`.
pub proof fn theorem_use_after_revoke_and_realloc_rejected(
    slots_after_revoke: Seq<KernelCapSlot>,
    slots_later: Seq<KernelCapSlot>,
    caller_realm: RealmId,
    h: CapHandle,
    req: SpecHostRequest,
)
    requires
        (h.slot as int) < slots_after_revoke.len(),
        h.generation < slots_after_revoke[h.slot as int].generation,
        spec_table_evolves(slots_after_revoke, slots_later),
    ensures
        !spec_valid_handle(slots_later, h),
        spec_dispatch_gate(slots_later, caller_realm, h, req)
            == Err::<(), HostError>(HostError::RevokedOrInvalidHandle),
{
    lemma_revoked_handle_permanently_dead(slots_after_revoke, slots_later, h);
}

/// Security Theorem (a3) — No Handle Forgery / Tampering:
/// If `valid` is an active kernel-issued handle for slot `valid.slot`, ANY handle `forged`
/// targeting the same slot with any altered attribute (`perms`, `realm`, `kind`, or
/// `generation`) is unconditionally rejected with `Err(HostError::RevokedOrInvalidHandle)`.
pub proof fn theorem_forged_handle_rejected(
    slots: Seq<KernelCapSlot>,
    valid: CapHandle,
    forged: CapHandle,
    caller_realm: RealmId,
    req: SpecHostRequest,
)
    requires
        spec_valid_handle(slots, valid),
        forged.slot == valid.slot,
        forged != valid,
    ensures
        spec_dispatch_gate(slots, caller_realm, forged, req)
            == Err::<(), HostError>(HostError::RevokedOrInvalidHandle),
{
    lemma_no_handle_tampering(slots, valid, forged);
}

/// Security Theorem (b) — Cross-Realm & Cross-Origin Non-Interference:
/// For any valid handle `h`, if `caller_realm != h.realm` OR `h`'s kernel-bound origin
/// differs from `req`'s target origin, `dispatch` unconditionally refuses with
/// `Err(HostError::CrossRealmViolation)` and zero state mutation.
pub proof fn theorem_cross_realm_or_origin_refused(
    slots: Seq<KernelCapSlot>,
    caller_realm: RealmId,
    h: CapHandle,
    req: SpecHostRequest,
)
    requires
        spec_valid_handle(slots, h),
        caller_realm != h.realm || spec_handle_origin(slots, h) != spec_req_target_origin(req),
    ensures
        spec_dispatch_gate(slots, caller_realm, h, req)
            == Err::<(), HostError>(HostError::CrossRealmViolation),
{
}

/// End-to-End Executable Proof Harness for Use-After-Revoke (`revoke` + `dispatch`):
/// Machine-checks on the actual executable `KernelCapTable::revoke` and `dispatch` functions
/// that revoking a valid handle `h` and subsequently calling `dispatch` ALWAYS returns
/// `Err(HostError::RevokedOrInvalidHandle)` and leaves `state` unchanged!
pub fn verified_revoke_then_dispatch_refused(
    table: &mut KernelCapTable,
    arena: &JsObjectArena,
    state: &mut HostState,
    caller_realm: RealmId,
    h: CapHandle,
    req: &HostRequest,
) -> (res: Result<JsValue, HostError>)
    requires
        old(table).wf(),
        spec_valid_handle(old(table).slots@, h),
    ensures
        final(table).wf(),
        res == Err::<JsValue, HostError>(HostError::RevokedOrInvalidHandle),
        final(state)@ == old(state)@,
{
    let _rev = table.revoke(h);
    proof {
        assert(_rev == Ok::<(), HostError>(()));
        assert(!spec_valid_handle(table.slots@, h));
    }
    dispatch(table, arena, state, caller_realm, h, req)
}

/// Security Theorem (c) — Permission Attenuation Monotonicity:
/// Whenever `child` is derived from `parent` via `KernelCapTable::attenuate`:
/// 1. `child` never possesses any permission bit absent on `parent` (`spec_perms_subset`),
/// 2. Any `HostRequest` whose required permissions were absent on `parent` is guaranteed
///    to also fail permission checks on `child` (returning `Err(HostError::InsufficientPermissions)`
///    when realm, origin, and kind match).
pub proof fn theorem_permission_attenuation_monotonicity(
    slots: Seq<KernelCapSlot>,
    parent: CapHandle,
    child: CapHandle,
    req: SpecHostRequest,
)
    requires
        spec_valid_handle(slots, parent),
        spec_valid_handle(slots, child),
        spec_perms_subset(child.perms, parent.perms),
        child.realm == parent.realm,
        child.kind == parent.kind,
        spec_handle_origin(slots, child) == spec_handle_origin(slots, parent),
    ensures
        forall|mask: u8| spec_has_perms(child.perms, mask) ==> spec_has_perms(parent.perms, mask),
        (child.realm == spec_req_target_realm(parent)
            && spec_handle_origin(slots, child) == spec_req_target_origin(req)
            && child.kind == spec_req_expected_kind(req)
            && !spec_has_perms(parent.perms, spec_req_required_perms(req)))
            ==> spec_dispatch_gate(slots, child.realm, child, req)
                == Err::<(), HostError>(HostError::InsufficientPermissions),
{
    assert forall|mask: u8| spec_has_perms(child.perms, mask) implies spec_has_perms(parent.perms, mask) by {
        lemma_perms_monotonicity(child.perms, parent.perms, mask);
    }
    lemma_perms_monotonicity(child.perms, parent.perms, spec_req_required_perms(req));
}

pub open spec fn spec_req_target_realm(h: CapHandle) -> RealmId {
    h.realm
}

/// Security Theorem (d) — Per-Node Object Capability Confinement (No Confused Deputy):
/// A valid `DomNode` capability `h` bound to `slot.resource_id` can NEVER mutate any other
/// DOM node `other_nid != spec_handle_resource(slots, h)`:
/// 1. Passing a `NodeOp` with `snop.node_id != spec_handle_resource(slots, h)` unconditionally
///    fails with `Err(HostError::InsufficientPermissions)` and zero state mutation.
/// 2. Any successful `DomMutateNode` call leaves `spec_filter_dom_by_node_id(..., other_nid)`
///    identical for all `other_nid != spec_handle_resource(slots, h)`.
pub proof fn theorem_dom_node_confinement(
    slots: Seq<KernelCapSlot>,
    arena: Seq<crate::conversions::SpecJsObjectRecord>,
    before: SpecHostState,
    after: SpecHostState,
    h: CapHandle,
    target_origin: OriginId,
    node_op_js: SpecJsValue,
    res: Result<JsValue, HostError>,
    other_nid: u32,
)
    requires
        spec_dom_mutate_node_confined(
            slots,
            arena,
            before,
            after,
            h,
            SpecHostRequest::DomMutateNode { target_origin, node_op_js },
            res,
        ),
        other_nid != spec_handle_resource(slots, h),
    ensures
        match spec_to_idl_node_op(arena, node_op_js) {
            Ok(snop) => snop.node_id == other_nid ==> (
                res == Err::<JsValue, HostError>(HostError::InsufficientPermissions)
                && after == before
            ),
            Err(_) => true,
        },
        res.is_ok() ==> (
            spec_filter_dom_by_node_id(after.dom_nodes, other_nid)
                == spec_filter_dom_by_node_id(before.dom_nodes, other_nid)
        ),
{
}

} // verus!
