//! Kernel-issued capability handles and `KernelCapTable` for the `vjs` host boundary.
//!
//! Design: `docs/verified-browser-engine.md` §3.2–§3.3 (J4b).
//! The JS engine holds zero ambient authority; every host access requires a generational,
//! realm-bound, origin-scoped, permission-bitmasked `CapHandle` validated against the
//! kernel's authoritative `KernelCapTable`.

use vstd::prelude::*;
use crate::conversions::IdlError;

verus! {

/// Per-realm identifier isolating JavaScript execution realms (e.g. frames/workers).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RealmId(pub u32);

/// Origin identifier isolating same-origin security principals in the browser kernel.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OriginId(pub u32);

/// Host capability object categories mediated by the browser kernel.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CapKind {
    DomDocument,
    DomNode,
    FetchOrigin,
    CookieJarOrigin,
    StorageOrigin,
    ConsoleSink,
    TimerQueue,
}

/// Bitmask wrapper for capability permissions (`u8`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CapPerms(pub u8);

pub const PERM_NONE: u8 = 0x00;
pub const PERM_READ: u8 = 0x01;
pub const PERM_WRITE: u8 = 0x02;
pub const PERM_NETWORK: u8 = 0x04;
pub const PERM_CREATE: u8 = 0x08;
pub const PERM_DELETE: u8 = 0x10;
pub const PERM_SCHEDULE: u8 = 0x20;
pub const PERM_LOG: u8 = 0x40;
pub const PERM_ALL: u8 = 0x7F;

/// Generational capability handle held by an untrusted JS realm.
///
/// Unforgeability: every field (`slot`, `generation`, `realm`, `kind`, `perms`) is checked
/// against the kernel's authoritative `KernelCapSlot` on every `validate`, `attenuate`,
/// `revoke`, and `dispatch` call. Mutating any field produces an invalid handle unless the
/// kernel itself minted an active slot with those exact attributes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CapHandle {
    pub slot: usize,
    pub generation: u64,
    pub realm: RealmId,
    pub kind: CapKind,
    pub perms: u8,
}

/// Authoritative kernel capability table entry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct KernelCapSlot {
    pub active: bool,
    pub generation: u64,
    pub realm: RealmId,
    pub origin: OriginId,
    pub kind: CapKind,
    pub perms: u8,
    pub resource_id: u32,
}

/// Host boundary and capability table errors.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HostError {
    RevokedOrInvalidHandle,
    CrossRealmViolation,
    PermissionEscalation,
    InsufficientPermissions,
    WrongCapabilityKind,
    CapacityExhausted,
    DomNodeNotFound,
    Idl(IdlError),
}

/// Kernel-owned capability table mapping generational slots to authoritative grants.
pub struct KernelCapTable {
    pub slots: Vec<KernelCapSlot>,
}

// ---------------------------------------------------------------------------------------
// Permission Bitmask Specification & Monotonicity Lemmas
// ---------------------------------------------------------------------------------------

/// `child` permissions are a bitwise subset of `parent` permissions: no bit is set in
/// `child` unless it is also set in `parent`.
pub open spec fn spec_perms_subset(child: u8, parent: u8) -> bool {
    (child & !parent) == 0u8
}

/// All bits in `required` are present in `granted`.
pub open spec fn spec_has_perms(granted: u8, required: u8) -> bool {
    (required & !granted) == 0u8
}

pub proof fn lemma_perms_subset_reflexive(p: u8)
    ensures
        spec_perms_subset(p, p),
{
    assert((p & !p) == 0u8) by (bit_vector);
}

pub proof fn lemma_perms_subset_transitive(a: u8, b: u8, c: u8)
    requires
        spec_perms_subset(a, b),
        spec_perms_subset(b, c),
    ensures
        spec_perms_subset(a, c),
{
    assert(((a & !b) == 0u8 && (b & !c) == 0u8) ==> (a & !c) == 0u8) by (bit_vector);
}

/// Permission Monotonicity: if `child` is attenuated from `parent`, any single bit or
/// bitmask granted to `child` was necessarily already present in `parent`, and any
/// permission check that fails on `parent` necessarily fails on `child`.
pub proof fn lemma_perms_monotonicity(child: u8, parent: u8, required: u8)
    requires
        spec_perms_subset(child, parent),
    ensures
        spec_has_perms(child, required) ==> spec_has_perms(parent, required),
        !spec_has_perms(parent, required) ==> !spec_has_perms(child, required),
        (child & required) != 0u8 ==> (parent & required) != 0u8,
{
    assert(((child & !parent) == 0u8 && (required & !child) == 0u8) ==> (required & !parent) == 0u8)
        by (bit_vector);
    assert(((child & !parent) == 0u8 && (child & required) != 0u8) ==> (parent & required) != 0u8)
        by (bit_vector);
}

pub proof fn lemma_perms_mask_is_subset(parent: u8, mask: u8)
    ensures
        spec_perms_subset(parent & mask, parent),
{
    assert(((parent & mask) & !parent) == 0u8) by (bit_vector);
}

impl CapPerms {
    pub fn new(bits: u8) -> (r: Self)
        ensures
            r.0 == bits,
    {
        CapPerms(bits)
    }

    pub fn is_subset_of(&self, parent: CapPerms) -> (ok: bool)
        ensures
            ok == spec_perms_subset(self.0, parent.0),
    {
        (self.0 & !parent.0) == 0u8
    }

    pub fn has_all(&self, required: u8) -> (ok: bool)
        ensures
            ok == spec_has_perms(self.0, required),
    {
        (required & !self.0) == 0u8
    }

    pub fn intersect(&self, mask: u8) -> (out: Self)
        ensures
            out.0 == (self.0 & mask),
            spec_perms_subset(out.0, self.0),
    {
        proof {
            lemma_perms_mask_is_subset(self.0, mask);
        }
        CapPerms(self.0 & mask)
    }
}

// ---------------------------------------------------------------------------------------
// Capability Table Specification & Security Theorems
// ---------------------------------------------------------------------------------------

/// Well-formedness invariant of `KernelCapTable`:
/// Every allocated slot has `generation >= 1`, and every active slot has
/// `generation < u64::MAX` so `revoke` can always strictly bump `generation` without overflow.
pub open spec fn spec_table_wf(slots: Seq<KernelCapSlot>) -> bool {
    forall|i: int| 0 <= i < slots.len() ==> (
        (#[trigger] slots[i]).generation >= 1u64
        && (slots[i].active ==> slots[i].generation < u64::MAX)
    )
}

/// Authoritative handle validation predicate against `slots`.
pub open spec fn spec_valid_handle(slots: Seq<KernelCapSlot>, h: CapHandle) -> bool {
    (h.slot as int) < slots.len()
    && slots[h.slot as int].active
    && slots[h.slot as int].generation == h.generation
    && slots[h.slot as int].realm == h.realm
    && slots[h.slot as int].kind == h.kind
    && slots[h.slot as int].perms == h.perms
}

/// Origin bound to `h`'s kernel slot (meaningful when `spec_valid_handle(slots, h)`).
pub open spec fn spec_handle_origin(slots: Seq<KernelCapSlot>, h: CapHandle) -> OriginId {
    slots[h.slot as int].origin
}

/// Resource ID bound to `h`'s kernel slot.
pub open spec fn spec_handle_resource(slots: Seq<KernelCapSlot>, h: CapHandle) -> u32 {
    slots[h.slot as int].resource_id
}

/// Monotonic evolution relation on `KernelCapTable`: table length never shrinks and
/// each slot's generation is monotonically non-decreasing.
pub open spec fn spec_table_evolves(before: Seq<KernelCapSlot>, after: Seq<KernelCapSlot>) -> bool {
    before.len() <= after.len()
    && forall|i: int| 0 <= i < before.len() ==>
        before[i].generation <= (#[trigger] after[i]).generation
}

pub proof fn lemma_table_evolves_reflexive(s: Seq<KernelCapSlot>)
    ensures
        spec_table_evolves(s, s),
{
}

pub proof fn lemma_table_evolves_transitive(
    s1: Seq<KernelCapSlot>,
    s2: Seq<KernelCapSlot>,
    s3: Seq<KernelCapSlot>,
)
    requires
        spec_table_evolves(s1, s2),
        spec_table_evolves(s2, s3),
    ensures
        spec_table_evolves(s1, s3),
{
    assert forall|i: int| 0 <= i < s1.len() implies s1[i].generation <= (#[trigger] s3[i]).generation by {
        assert(s1[i].generation <= s2[i].generation);
        assert(s2[i].generation <= s3[i].generation);
    }
}

/// Security Theorem (Tamper / Forgery Resistance):
/// At any given slot `h.slot`, at most ONE `(generation, realm, kind, perms)` tuple can
/// pass `spec_valid_handle`. Any handle forged by altering permissions, realm, kind, or
/// generation is unconditionally rejected.
pub proof fn lemma_no_handle_tampering(
    slots: Seq<KernelCapSlot>,
    valid: CapHandle,
    forged: CapHandle,
)
    requires
        spec_valid_handle(slots, valid),
        forged.slot == valid.slot,
        forged != valid,
    ensures
        !spec_valid_handle(slots, forged),
{
}

/// Security Theorem (Permanent Non-Revivability Across Reallocations):
/// Once a handle `h` has `h.generation < slots_after_revoke[h.slot].generation` (as
/// established immediately by `revoke`), NO future valid evolution of the capability
/// table (including slot reuse by subsequent `allocate` or `attenuate` calls) can ever
/// make `h` valid again.
pub proof fn lemma_revoked_handle_permanently_dead(
    after_revoke: Seq<KernelCapSlot>,
    later: Seq<KernelCapSlot>,
    h: CapHandle,
)
    requires
        (h.slot as int) < after_revoke.len(),
        h.generation < after_revoke[h.slot as int].generation,
        spec_table_evolves(after_revoke, later),
    ensures
        !spec_valid_handle(later, h),
{
    assert(after_revoke[h.slot as int].generation <= later[h.slot as int].generation);
}

// ---------------------------------------------------------------------------------------
// Executable `KernelCapTable` Implementation
// ---------------------------------------------------------------------------------------

impl KernelCapTable {
    pub open spec fn wf(&self) -> bool {
        spec_table_wf(self.slots@)
    }

    pub fn new() -> (table: Self)
        ensures
            table.wf(),
            table.slots@.len() == 0,
    {
        KernelCapTable { slots: Vec::new() }
    }

    pub fn len(&self) -> (n: usize)
        ensures
            n == self.slots@.len(),
    {
        self.slots.len()
    }

    pub fn validate(&self, h: &CapHandle) -> (ok: bool)
        ensures
            ok == spec_valid_handle(self.slots@, *h),
    {
        if h.slot >= self.slots.len() {
            return false;
        }
        let s = &self.slots[h.slot];
        s.active
            && s.generation == h.generation
            && s.realm.0 == h.realm.0
            && match (s.kind, h.kind) {
                (CapKind::DomDocument, CapKind::DomDocument) => true,
                (CapKind::DomNode, CapKind::DomNode) => true,
                (CapKind::FetchOrigin, CapKind::FetchOrigin) => true,
                (CapKind::CookieJarOrigin, CapKind::CookieJarOrigin) => true,
                (CapKind::StorageOrigin, CapKind::StorageOrigin) => true,
                (CapKind::ConsoleSink, CapKind::ConsoleSink) => true,
                (CapKind::TimerQueue, CapKind::TimerQueue) => true,
                _ => false,
            }
            && s.perms == h.perms
    }

    pub fn lookup_entry(&self, h: &CapHandle) -> (res: Option<KernelCapSlot>)
        ensures
            spec_valid_handle(self.slots@, *h) ==> (
                res == Some(self.slots@[h.slot as int])
            ),
            !spec_valid_handle(self.slots@, *h) ==> res.is_none(),
    {
        if self.validate(h) {
            Some(self.slots[h.slot])
        } else {
            None
        }
    }

    /// Mint a fresh kernel capability handle (reusing a retired slot whose generation has
    /// headroom `< u64::MAX`, or appending a new slot at generation 1).
    pub fn allocate(
        &mut self,
        realm: RealmId,
        origin: OriginId,
        kind: CapKind,
        perms: u8,
        resource_id: u32,
    ) -> (res: Result<CapHandle, HostError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_table_evolves(old(self).slots@, final(self).slots@),
            match res {
                Ok(h) => {
                    spec_valid_handle(final(self).slots@, h)
                    && h.realm == realm
                    && h.kind == kind
                    && h.perms == perms
                    && spec_handle_origin(final(self).slots@, h) == origin
                    && spec_handle_resource(final(self).slots@, h) == resource_id
                    && forall|other: CapHandle|
                        spec_valid_handle(old(self).slots@, other) ==> (
                            #[trigger] spec_valid_handle(final(self).slots@, other)
                            && other.slot != h.slot
                            && spec_handle_origin(final(self).slots@, other)
                                == spec_handle_origin(old(self).slots@, other)
                            && spec_handle_resource(final(self).slots@, other)
                                == spec_handle_resource(old(self).slots@, other)
                        )
                },
                Err(e) => {
                    e == HostError::CapacityExhausted
                    && final(self).slots@ == old(self).slots@
                },
            },
    {
        let n = self.slots.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.slots@.len(),
                self.slots@ == old(self).slots@,
                self.wf(),
            decreases n - i,
        {
            let cur = self.slots[i];
            if !cur.active && cur.generation < u64::MAX {
                let gen = cur.generation;
                let entry = KernelCapSlot {
                    active: true,
                    generation: gen,
                    realm,
                    origin,
                    kind,
                    perms,
                    resource_id,
                };
                self.slots.set(i, entry);
                let h = CapHandle {
                    slot: i,
                    generation: gen,
                    realm,
                    kind,
                    perms,
                };
                proof {
                    assert forall|k: int| 0 <= k < self.slots@.len() implies (
                        (#[trigger] self.slots@[k]).generation >= 1u64
                        && (self.slots@[k].active ==> self.slots@[k].generation < u64::MAX)
                    ) by {
                        if k == i as int {
                            assert(old(self).slots@[k].generation >= 1u64);
                        } else {
                            assert(self.slots@[k] == old(self).slots@[k]);
                        }
                    }
                    assert forall|other: CapHandle|
                        spec_valid_handle(old(self).slots@, other) implies (
                            #[trigger] spec_valid_handle(self.slots@, other)
                            && other.slot != h.slot
                            && spec_handle_origin(self.slots@, other)
                                == spec_handle_origin(old(self).slots@, other)
                            && spec_handle_resource(self.slots@, other)
                                == spec_handle_resource(old(self).slots@, other)
                        ) by {
                        assert(old(self).slots@[other.slot as int].active);
                        assert(!old(self).slots@[i as int].active);
                        assert(other.slot != i);
                        assert(self.slots@[other.slot as int] == old(self).slots@[other.slot as int]);
                    }
                }
                return Ok(h);
            }
            i += 1;
        }

        if n == usize::MAX {
            return Err(HostError::CapacityExhausted);
        }

        let entry = KernelCapSlot {
            active: true,
            generation: 1u64,
            realm,
            origin,
            kind,
            perms,
            resource_id,
        };
        self.slots.push(entry);
        let h = CapHandle {
            slot: n,
            generation: 1u64,
            realm,
            kind,
            perms,
        };
        proof {
            assert forall|k: int| 0 <= k < self.slots@.len() implies (
                (#[trigger] self.slots@[k]).generation >= 1u64
                && (self.slots@[k].active ==> self.slots@[k].generation < u64::MAX)
            ) by {
                if k < n as int {
                    assert(self.slots@[k] == old(self).slots@[k]);
                }
            }
            assert forall|other: CapHandle|
                spec_valid_handle(old(self).slots@, other) implies (
                    #[trigger] spec_valid_handle(self.slots@, other)
                    && other.slot != h.slot
                    && spec_handle_origin(self.slots@, other)
                        == spec_handle_origin(old(self).slots@, other)
                    && spec_handle_resource(self.slots@, other)
                        == spec_handle_resource(old(self).slots@, other)
                ) by {
                assert((other.slot as int) < n as int);
                assert(self.slots@[other.slot as int] == old(self).slots@[other.slot as int]);
            }
        }
        Ok(h)
    }

    /// Derive a strictly or weakly attenuated capability handle (`requested_perms` must be
    /// a bitwise subset of `parent.perms`). Never adds permissions absent on `parent`.
    pub fn attenuate(
        &mut self,
        parent: CapHandle,
        requested_perms: u8,
    ) -> (res: Result<CapHandle, HostError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_table_evolves(old(self).slots@, final(self).slots@),
            !spec_valid_handle(old(self).slots@, parent) ==> (
                res == Err::<CapHandle, HostError>(HostError::RevokedOrInvalidHandle)
                && final(self).slots@ == old(self).slots@
            ),
            spec_valid_handle(old(self).slots@, parent)
                && !spec_perms_subset(requested_perms, parent.perms) ==> (
                res == Err::<CapHandle, HostError>(HostError::PermissionEscalation)
                && final(self).slots@ == old(self).slots@
            ),
            match res {
                Ok(child) => {
                    spec_valid_handle(old(self).slots@, parent)
                    && spec_valid_handle(final(self).slots@, parent)
                    && spec_valid_handle(final(self).slots@, child)
                    && spec_perms_subset(child.perms, parent.perms)
                    && child.perms == requested_perms
                    && child.realm == parent.realm
                    && child.kind == parent.kind
                    && spec_handle_origin(final(self).slots@, child)
                        == spec_handle_origin(old(self).slots@, parent)
                    && spec_handle_resource(final(self).slots@, child)
                        == spec_handle_resource(old(self).slots@, parent)
                },
                Err(_) => final(self).slots@ == old(self).slots@,
            },
    {
        if !self.validate(&parent) {
            return Err(HostError::RevokedOrInvalidHandle);
        }
        if (requested_perms & !parent.perms) != 0u8 {
            return Err(HostError::PermissionEscalation);
        }
        let p_slot = self.slots[parent.slot];
        self.allocate(
            parent.realm,
            p_slot.origin,
            parent.kind,
            requested_perms,
            p_slot.resource_id,
        )
    }

    /// Revoke an active handle by clearing `active` and bumping the slot's generation.
    pub fn revoke(&mut self, h: CapHandle) -> (res: Result<(), HostError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            spec_table_evolves(old(self).slots@, final(self).slots@),
            !spec_valid_handle(old(self).slots@, h) ==> (
                res == Err::<(), HostError>(HostError::RevokedOrInvalidHandle)
                && final(self).slots@ == old(self).slots@
            ),
            spec_valid_handle(old(self).slots@, h) ==> (
                res == Ok::<(), HostError>(())
                && !spec_valid_handle(final(self).slots@, h)
                && !final(self).slots@[h.slot as int].active
                && final(self).slots@[h.slot as int].generation == h.generation + 1
                && final(self).slots@.len() == old(self).slots@.len()
                && forall|other: CapHandle|
                    spec_valid_handle(old(self).slots@, other) && other.slot != h.slot ==> (
                        #[trigger] spec_valid_handle(final(self).slots@, other)
                        && spec_handle_origin(final(self).slots@, other)
                            == spec_handle_origin(old(self).slots@, other)
                    )
            ),
    {
        if !self.validate(&h) {
            return Err(HostError::RevokedOrInvalidHandle);
        }
        let cur = self.slots[h.slot];
        proof {
            assert(cur.active);
            assert(cur.generation < u64::MAX);
        }
        let updated = KernelCapSlot {
            active: false,
            generation: cur.generation + 1,
            realm: cur.realm,
            origin: cur.origin,
            kind: cur.kind,
            perms: cur.perms,
            resource_id: cur.resource_id,
        };
        self.slots.set(h.slot, updated);
        proof {
            assert forall|k: int| 0 <= k < self.slots@.len() implies (
                (#[trigger] self.slots@[k]).generation >= 1u64
                && (self.slots@[k].active ==> self.slots@[k].generation < u64::MAX)
            ) by {
                if k != h.slot as int {
                    assert(self.slots@[k] == old(self).slots@[k]);
                }
            }
            assert forall|other: CapHandle|
                spec_valid_handle(old(self).slots@, other) && other.slot != h.slot implies (
                    #[trigger] spec_valid_handle(self.slots@, other)
                    && spec_handle_origin(self.slots@, other)
                        == spec_handle_origin(old(self).slots@, other)
                ) by {
                assert(self.slots@[other.slot as int] == old(self).slots@[other.slot as int]);
            }
        }
        Ok(())
    }
}

} // verus!
