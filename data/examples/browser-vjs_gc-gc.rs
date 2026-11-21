//! Formally verified Mark-Sweep Garbage Collector (`vjs` J6, `docs/verified-browser-engine.md` §3.3).
//!
//! Proves in Verus with zero trusted items:
//! 1. **Termination**: Iterative worklist tricolor mark phase (`decreases` on unmarked slot count
//!    + worklist size) and linear sweep phase (`decreases` on remaining arena slots).
//! 2. **Heap Well-Formedness Preservation**: `heap.wf() && roots_valid(heap, roots) ==> new_heap.wf()`
//!    — zero dangling pointers in any surviving object, and exact recomputed per-realm live object
//!    and live byte usage bounded by each realm's configured quotas.
//! 3. **Soundness (Live Preservation)**: Every reachable slot (`spec_reachable(heap@, roots@, id)`)
//!    remains `Live` in `new_heap` with identical `GcObject` payload and outgoing edges
//!    (`new_heap@[id] == heap@[id]`), and reachability itself is preserved (`spec_reachable(new_heap@, ...)`).
//! 4. **Completeness (Garbage Reclamation)**: Every slot with `!spec_reachable(heap@, roots@, id)`
//!    is `Free` in `new_heap`, and `stats.freed_slots` / `stats.freed_bytes` equal the exact count
//!    and byte weight of reclaimed slots.
use vstd::prelude::*;

verus! {

use crate::types::JsError;

// -----------------------------------------------------------------------------------------------
// Heap Data Model & Abstract Views
// -----------------------------------------------------------------------------------------------

/// Tagged runtime object payload stored inside a `GcObject` slot.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GcPayload {
    OrdinaryObject { proto_tag: u32, prop_count: u32 },
    ProxyObject { revoked: bool },
    PromiseObject { promise_id: usize },
    GeneratorObject { gen_id: usize },
    AsyncFrameObject { async_id: usize },
    Closure { bytecode_id: u32, env_len: u32 },
    HostHandle { cap_id: u64 },
}

/// Abstract mathematical view of a `GcObject`.
pub struct GcObjectView {
    pub realm: u32,
    pub byte_weight: usize,
    pub payload: GcPayload,
    pub edges: Seq<usize>,
}

/// Concrete heap object stored in a `Live` arena slot.
pub struct GcObject {
    pub realm: u32,
    pub byte_weight: usize,
    pub payload: GcPayload,
    pub edges: Vec<usize>,
}

impl View for GcObject {
    type V = GcObjectView;

    open spec fn view(&self) -> GcObjectView {
        GcObjectView {
            realm: self.realm,
            byte_weight: self.byte_weight,
            payload: self.payload,
            edges: self.edges@,
        }
    }
}

/// Abstract mathematical view of an arena `Slot`.
pub enum SlotView {
    Free,
    Live(GcObjectView),
}

/// Concrete arena slot (`Free` | `Live(GcObject)`).
pub enum Slot {
    Free,
    Live(GcObject),
}

impl View for Slot {
    type V = SlotView;

    open spec fn view(&self) -> SlotView {
        match self {
            Slot::Free => SlotView::Free,
            Slot::Live(obj) => SlotView::Live(obj@),
        }
    }
}

/// Per-realm live memory & object count tracking + configured hard quotas.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RealmQuota {
    pub live_objects: usize,
    pub live_bytes: usize,
    pub max_objects: usize,
    pub max_bytes: usize,
}

/// Exact statistics produced by a `mark_sweep` collection cycle.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct GcStats {
    pub total_slots: usize,
    pub surviving_slots: usize,
    pub freed_slots: usize,
    pub surviving_bytes: usize,
    pub freed_bytes: usize,
}

/// Tricolor mark state used by Dijkstra's iterative worklist collector.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Color {
    /// Unvisited / unmarked candidate garbage.
    White,
    /// Discovered reachable live object currently queued on the worklist.
    Gray,
    /// Visited reachable live object whose outgoing edges have all been scanned.
    Black,
}

pub open spec fn spec_slots_view(slots: Seq<Slot>) -> Seq<SlotView> {
    Seq::new(slots.len(), |i: int| slots[i]@)
}

/// Arena heap with per-realm live memory / object quota accounting.
pub struct GcHeap {
    pub slots: Vec<Slot>,
    pub realms: Vec<RealmQuota>,
}

impl View for GcHeap {
    type V = Seq<SlotView>;

    open spec fn view(&self) -> Seq<SlotView> {
        spec_slots_view(self.slots@)
    }
}

// -----------------------------------------------------------------------------------------------
// Inductive Graph Reachability & Accounting Specifications
// -----------------------------------------------------------------------------------------------

pub open spec fn spec_is_live(heap: Seq<SlotView>, id: usize) -> bool {
    (id as int) < heap.len() && (heap[id as int] is Live)
}

pub open spec fn spec_has_edge(heap: Seq<SlotView>, u: usize, v: usize) -> bool {
    (u as int) < heap.len() && match heap[u as int] {
        SlotView::Free => false,
        SlotView::Live(obj) => exists|k: int| 0 <= k < obj.edges.len() && #[trigger] obj.edges[k] == v,
    }
}

pub open spec fn spec_in_roots(roots: Seq<usize>, id: usize) -> bool {
    exists|k: int| 0 <= k < roots.len() && #[trigger] roots[k] == id
}

/// Inductive `steps`-bounded reachability from `roots` in `heap`.
pub open spec fn spec_reachable_in(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    id: usize,
    steps: nat,
) -> bool
    decreases steps,
{
    if steps == 0 {
        spec_is_live(heap, id) && spec_in_roots(roots, id)
    } else {
        spec_reachable_in(heap, roots, id, (steps - 1) as nat)
        || (spec_is_live(heap, id)
            && exists|pred: usize|
                #[trigger] spec_has_edge(heap, pred, id)
                && spec_reachable_in(heap, roots, pred, (steps - 1) as nat))
    }
}

/// Existential multi-step reachability from `roots` in `heap`.
pub open spec fn spec_reachable(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    id: usize,
) -> bool {
    exists|steps: nat| #[trigger] spec_reachable_in(heap, roots, id, steps)
}

pub open spec fn spec_obj_edges_valid(heap: Seq<SlotView>, obj: GcObjectView) -> bool {
    forall|k: int| 0 <= k < obj.edges.len() ==> {
        let target = #[trigger] obj.edges[k];
        (target as int) < heap.len() && (heap[target as int] is Live)
    }
}

pub open spec fn spec_slot_valid(heap: Seq<SlotView>, num_realms: nat, slot: SlotView) -> bool {
    match slot {
        SlotView::Free => true,
        SlotView::Live(obj) => (obj.realm as nat) < num_realms && spec_obj_edges_valid(heap, obj),
    }
}

pub open spec fn spec_heap_graph_wf(heap: Seq<SlotView>, num_realms: nat) -> bool {
    forall|u: int| 0 <= u < heap.len() ==> spec_slot_valid(heap, num_realms, #[trigger] heap[u])
}

pub open spec fn spec_roots_valid(heap: Seq<SlotView>, roots: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < roots.len() ==> {
        let r = #[trigger] roots[i];
        (r as int) < heap.len() && (heap[r as int] is Live)
    }
}

pub open spec fn roots_valid(heap: &GcHeap, roots: &[usize]) -> bool {
    spec_roots_valid(heap@, roots@)
}

/// Prefix live object count for `realm` across `0..upto`.
pub open spec fn spec_realm_objects_upto(heap: Seq<SlotView>, realm: u32, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_realm_objects_upto(heap, realm, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < heap.len() {
            match heap[idx] {
                SlotView::Live(obj) => if obj.realm == realm { prev + 1 } else { prev },
                SlotView::Free => prev,
            }
        } else {
            prev
        }
    }
}

pub open spec fn spec_realm_live_objects(heap: Seq<SlotView>, realm: u32) -> nat {
    spec_realm_objects_upto(heap, realm, heap.len())
}

/// Prefix live byte sum for `realm` across `0..upto`.
pub open spec fn spec_realm_bytes_upto(heap: Seq<SlotView>, realm: u32, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_realm_bytes_upto(heap, realm, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < heap.len() {
            match heap[idx] {
                SlotView::Live(obj) => if obj.realm == realm { prev + (obj.byte_weight as nat) } else { prev },
                SlotView::Free => prev,
            }
        } else {
            prev
        }
    }
}

pub open spec fn spec_realm_live_bytes(heap: Seq<SlotView>, realm: u32) -> nat {
    spec_realm_bytes_upto(heap, realm, heap.len())
}

/// Total live byte weight across `0..upto` (all realms).
pub open spec fn spec_total_live_bytes_upto(heap: Seq<SlotView>, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_total_live_bytes_upto(heap, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < heap.len() {
            match heap[idx] {
                SlotView::Live(obj) => prev + (obj.byte_weight as nat),
                SlotView::Free => prev,
            }
        } else {
            prev
        }
    }
}

pub open spec fn spec_total_live_bytes(heap: Seq<SlotView>) -> nat {
    spec_total_live_bytes_upto(heap, heap.len())
}

/// Exact count of reachable slots in `0..upto`.
pub open spec fn spec_count_reachable_upto(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    upto: nat,
) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_count_reachable_upto(heap, roots, (upto - 1) as nat);
        let id = (upto - 1) as usize;
        if (upto - 1) < heap.len() && spec_reachable(heap, roots, id) {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn spec_count_reachable(heap: Seq<SlotView>, roots: Seq<usize>) -> nat {
    spec_count_reachable_upto(heap, roots, heap.len())
}

/// Exact count of reclaimed slots (previously `Live`, now unreachable) in `0..upto`.
pub open spec fn spec_count_reclaimed_upto(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    upto: nat,
) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_count_reclaimed_upto(heap, roots, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < heap.len() && (heap[idx] is Live) && !spec_reachable(heap, roots, idx as usize) {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn spec_count_reclaimed(heap: Seq<SlotView>, roots: Seq<usize>) -> nat {
    spec_count_reclaimed_upto(heap, roots, heap.len())
}

/// Exact sum of `byte_weight` of reclaimed slots in `0..upto`.
pub open spec fn spec_reclaimed_bytes_upto(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    upto: nat,
) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_reclaimed_bytes_upto(heap, roots, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < heap.len() && !spec_reachable(heap, roots, idx as usize) {
            match heap[idx] {
                SlotView::Live(obj) => prev + (obj.byte_weight as nat),
                SlotView::Free => prev,
            }
        } else {
            prev
        }
    }
}

pub open spec fn spec_reclaimed_bytes(heap: Seq<SlotView>, roots: Seq<usize>) -> nat {
    spec_reclaimed_bytes_upto(heap, roots, heap.len())
}

/// Count of unmarked (`Color::White`) slots in `0..upto` (used in worklist termination `decreases`).
pub open spec fn spec_count_unmarked_upto(colors: Seq<Color>, upto: nat) -> nat
    decreases upto,
{
    if upto == 0 {
        0
    } else {
        let prev = spec_count_unmarked_upto(colors, (upto - 1) as nat);
        let idx = (upto - 1) as int;
        if idx < colors.len() && colors[idx] == Color::White {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn spec_count_unmarked(colors: Seq<Color>) -> nat {
    spec_count_unmarked_upto(colors, colors.len())
}

pub open spec fn spec_no_dup_usize(s: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

pub open spec fn spec_seq_contains_usize(s: Seq<usize>, v: usize) -> bool {
    exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == v
}

impl GcHeap {
    /// Complete heap well-formedness predicate:
    /// - Arena size `< usize::MAX`, realm count `<= u32::MAX`.
    /// - Zero dangling pointers: every outgoing edge of every `Live` object points to an in-bounds `Live` slot,
    ///   and every `Live` object belongs to a valid realm.
    /// - Total live bytes `<= usize::MAX`.
    /// - Exact per-realm live object and byte usage matching the arena contents, within configured quotas.
    pub open spec fn wf(&self) -> bool {
        &&& self.slots@.len() < usize::MAX as int
        &&& self.realms@.len() <= u32::MAX as int
        &&& spec_heap_graph_wf(self@, self.realms@.len())
        &&& spec_total_live_bytes(self@) <= usize::MAX as nat
        &&& forall|r: int| 0 <= r < self.realms@.len() ==> {
            let rq = #[trigger] self.realms@[r];
            &&& rq.live_objects as nat == spec_realm_live_objects(self@, r as u32)
            &&& rq.live_bytes as nat == spec_realm_live_bytes(self@, r as u32)
            &&& rq.live_objects <= rq.max_objects
            &&& rq.live_bytes <= rq.max_bytes
        }
    }
}

// -----------------------------------------------------------------------------------------------
// Proof Lemmas for Tricolor Mark, Inductive Reachability, and Prefix Accounting
// -----------------------------------------------------------------------------------------------

proof fn lemma_root_is_reachable(heap: Seq<SlotView>, roots: Seq<usize>, ri: int)
    requires
        0 <= ri < roots.len(),
        spec_is_live(heap, roots[ri]),
    ensures
        spec_reachable(heap, roots, roots[ri]),
{
    let id = roots[ri];
    assert(roots[ri] == id);
    assert(spec_in_roots(roots, id));
    assert(spec_reachable_in(heap, roots, id, 0));
}

proof fn lemma_reachable_step(heap: Seq<SlotView>, roots: Seq<usize>, u: usize, v: usize)
    requires
        spec_reachable(heap, roots, u),
        spec_has_edge(heap, u, v),
        spec_is_live(heap, v),
    ensures
        spec_reachable(heap, roots, v),
{
    let s = choose|steps: nat| #[trigger] spec_reachable_in(heap, roots, u, steps);
    assert(spec_has_edge(heap, u, v));
    assert(spec_reachable_in(heap, roots, v, s + 1));
}

proof fn lemma_reachable_implies_live(heap: Seq<SlotView>, roots: Seq<usize>, id: usize)
    requires
        spec_reachable(heap, roots, id),
    ensures
        spec_is_live(heap, id),
{
    let s = choose|steps: nat| #[trigger] spec_reachable_in(heap, roots, id, steps);
    lemma_reachable_in_implies_live(heap, roots, id, s);
}

proof fn lemma_reachable_in_implies_live(heap: Seq<SlotView>, roots: Seq<usize>, id: usize, steps: nat)
    requires
        spec_reachable_in(heap, roots, id, steps),
    ensures
        spec_is_live(heap, id),
    decreases steps,
{
    if steps > 0 && spec_reachable_in(heap, roots, id, (steps - 1) as nat) {
        lemma_reachable_in_implies_live(heap, roots, id, (steps - 1) as nat);
    }
}

proof fn lemma_all_white_unmarked_upto(colors: Seq<Color>, upto: nat)
    requires
        upto <= colors.len(),
        forall|k: int| 0 <= k < upto as int ==> colors[k] == Color::White,
    ensures
        spec_count_unmarked_upto(colors, upto) == upto,
    decreases upto,
{
    if upto > 0 {
        lemma_all_white_unmarked_upto(colors, (upto - 1) as nat);
    }
}

proof fn lemma_white_to_gray_upto(colors: Seq<Color>, v: int, upto: nat)
    requires
        0 <= v < colors.len(),
        upto <= colors.len(),
        colors[v] == Color::White,
    ensures
        v < upto as int ==> spec_count_unmarked_upto(colors.update(v, Color::Gray), upto) + 1
            == spec_count_unmarked_upto(colors, upto),
        v >= upto as int ==> spec_count_unmarked_upto(colors.update(v, Color::Gray), upto)
            == spec_count_unmarked_upto(colors, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_white_to_gray_upto(colors, v, (upto - 1) as nat);
    }
}

proof fn lemma_gray_to_black_upto(colors: Seq<Color>, u: int, upto: nat)
    requires
        0 <= u < colors.len(),
        upto <= colors.len(),
        colors[u] == Color::Gray,
    ensures
        spec_count_unmarked_upto(colors.update(u, Color::Black), upto)
            == spec_count_unmarked_upto(colors, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_gray_to_black_upto(colors, u, (upto - 1) as nat);
    }
}

/// Dijkstra's Tricolor Completeness Lemma: once no `Gray` nodes exist (`worklist` is empty),
/// all roots are `Black`, and no `Black -> White` edge exists, every `steps`-reachable node is `Black`.
proof fn lemma_tricolor_reachable_in_is_black(
    heap: Seq<SlotView>,
    roots: Seq<usize>,
    colors: Seq<Color>,
    num_realms: nat,
    id: usize,
    steps: nat,
)
    requires
        colors.len() == heap.len(),
        spec_heap_graph_wf(heap, num_realms),
        forall|ri: int| 0 <= ri < roots.len() && spec_is_live(heap, roots[ri])
            ==> colors[roots[ri] as int] != Color::White,
        forall|k: int| 0 <= k < colors.len() ==> colors[k] != Color::Gray,
        forall|u: usize, v: usize|
            (u as int) < heap.len() && (v as int) < heap.len()
            && colors[u as int] == Color::Black
            && #[trigger] spec_has_edge(heap, u, v)
            ==> colors[v as int] != Color::White,
        spec_reachable_in(heap, roots, id, steps),
    ensures
        (id as int) < colors.len() && colors[id as int] == Color::Black,
    decreases steps,
{
    if steps == 0 {
        let ri = choose|k: int| 0 <= k < roots.len() && #[trigger] roots[k] == id;
        assert(colors[id as int] != Color::White);
        assert(colors[id as int] != Color::Gray);
    } else if spec_reachable_in(heap, roots, id, (steps - 1) as nat) {
        lemma_tricolor_reachable_in_is_black(heap, roots, colors, num_realms, id, (steps - 1) as nat);
    } else {
        let pred = choose|p: usize|
            #[trigger] spec_has_edge(heap, p, id)
            && spec_reachable_in(heap, roots, p, (steps - 1) as nat);
        lemma_tricolor_reachable_in_is_black(heap, roots, colors, num_realms, pred, (steps - 1) as nat);
        assert(spec_has_edge(heap, pred, id));
        assert(colors[id as int] != Color::White);
        assert(colors[id as int] != Color::Gray);
    }
}

proof fn lemma_realm_objects_prefix_ext(a: Seq<SlotView>, b: Seq<SlotView>, realm: u32, upto: nat)
    requires
        upto <= a.len(),
        upto <= b.len(),
        forall|k: int| 0 <= k < upto as int ==> a[k] == b[k],
    ensures
        spec_realm_objects_upto(a, realm, upto) == spec_realm_objects_upto(b, realm, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_realm_objects_prefix_ext(a, b, realm, (upto - 1) as nat);
    }
}

proof fn lemma_realm_bytes_prefix_ext(a: Seq<SlotView>, b: Seq<SlotView>, realm: u32, upto: nat)
    requires
        upto <= a.len(),
        upto <= b.len(),
        forall|k: int| 0 <= k < upto as int ==> a[k] == b[k],
    ensures
        spec_realm_bytes_upto(a, realm, upto) == spec_realm_bytes_upto(b, realm, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_realm_bytes_prefix_ext(a, b, realm, (upto - 1) as nat);
    }
}

proof fn lemma_total_bytes_prefix_ext(a: Seq<SlotView>, b: Seq<SlotView>, upto: nat)
    requires
        upto <= a.len(),
        upto <= b.len(),
        forall|k: int| 0 <= k < upto as int ==> a[k] == b[k],
    ensures
        spec_total_live_bytes_upto(a, upto) == spec_total_live_bytes_upto(b, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_total_bytes_prefix_ext(a, b, (upto - 1) as nat);
    }
}

proof fn lemma_realm_upto_monotonic(heap: Seq<SlotView>, realm: u32, u1: nat, u2: nat)
    requires
        u1 <= u2 <= heap.len(),
    ensures
        spec_realm_objects_upto(heap, realm, u1) <= spec_realm_objects_upto(heap, realm, u2),
        spec_realm_bytes_upto(heap, realm, u1) <= spec_realm_bytes_upto(heap, realm, u2),
    decreases u2 - u1,
{
    if u1 < u2 {
        lemma_realm_upto_monotonic(heap, realm, u1, (u2 - 1) as nat);
    }
}

proof fn lemma_total_bytes_upto_monotonic(heap: Seq<SlotView>, u1: nat, u2: nat)
    requires
        u1 <= u2 <= heap.len(),
    ensures
        spec_total_live_bytes_upto(heap, u1) <= spec_total_live_bytes_upto(heap, u2),
    decreases u2 - u1,
{
    if u1 < u2 {
        lemma_total_bytes_upto_monotonic(heap, u1, (u2 - 1) as nat);
    }
}

/// Reachability equivalence between `heap` and `new_heap` when `new_heap` preserves all reachable
/// slots identically and frees all unreachable slots.
proof fn lemma_reachable_in_preserved_forward(
    heap: Seq<SlotView>,
    new_heap: Seq<SlotView>,
    roots: Seq<usize>,
    id: usize,
    steps: nat,
)
    requires
        new_heap.len() == heap.len(),
        forall|x: usize| (x as int) < heap.len() && spec_reachable(heap, roots, x)
            ==> new_heap[x as int] == heap[x as int],
        spec_reachable_in(heap, roots, id, steps),
    ensures
        spec_reachable_in(new_heap, roots, id, steps),
    decreases steps,
{
    lemma_reachable_in_implies_live(heap, roots, id, steps);
    assert(spec_reachable(heap, roots, id));
    assert(new_heap[id as int] == heap[id as int]);
    if steps == 0 {
        let ri = choose|k: int| 0 <= k < roots.len() && #[trigger] roots[k] == id;
        assert(roots[ri] == id);
    } else if spec_reachable_in(heap, roots, id, (steps - 1) as nat) {
        lemma_reachable_in_preserved_forward(heap, new_heap, roots, id, (steps - 1) as nat);
    } else {
        let pred = choose|p: usize|
            #[trigger] spec_has_edge(heap, p, id)
            && spec_reachable_in(heap, roots, p, (steps - 1) as nat);
        lemma_reachable_in_preserved_forward(heap, new_heap, roots, pred, (steps - 1) as nat);
        lemma_reachable_in_implies_live(heap, roots, pred, (steps - 1) as nat);
        assert(spec_reachable(heap, roots, pred));
        assert(new_heap[pred as int] == heap[pred as int]);
        assert(spec_has_edge(new_heap, pred, id));
    }
}

proof fn lemma_reachable_in_preserved_backward(
    heap: Seq<SlotView>,
    new_heap: Seq<SlotView>,
    roots: Seq<usize>,
    id: usize,
    steps: nat,
)
    requires
        new_heap.len() == heap.len(),
        forall|x: usize| (x as int) < heap.len() && !spec_reachable(heap, roots, x)
            ==> new_heap[x as int] == SlotView::Free,
        spec_reachable_in(new_heap, roots, id, steps),
    ensures
        spec_reachable(heap, roots, id),
    decreases steps,
{
    lemma_reachable_in_implies_live(new_heap, roots, id, steps);
    if !spec_reachable(heap, roots, id) {
        assert(new_heap[id as int] == SlotView::Free);
        assert(false);
    }
}

// -----------------------------------------------------------------------------------------------
// Verified Helpers & Arena Operations
// -----------------------------------------------------------------------------------------------

fn clone_usize_vec(v: &Vec<usize>) -> (out: Vec<usize>)
    ensures
        out@ == v@,
{
    let n = v.len();
    let mut out: Vec<usize> = Vec::new();
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

fn clone_gc_object(obj: &GcObject) -> (out: GcObject)
    ensures
        out@ == obj@,
{
    GcObject {
        realm: obj.realm,
        byte_weight: obj.byte_weight,
        payload: obj.payload,
        edges: clone_usize_vec(&obj.edges),
    }
}

impl GcHeap {
    /// Construct an empty well-formed `GcHeap` with pre-configured realm quotas (`max_objects`, `max_bytes`).
    pub fn with_realms(quotas: &[(usize, usize)]) -> (res: Result<Self, JsError>)
        ensures
            match res {
                Ok(h) => {
                    &&& h.wf()
                    &&& h@.len() == 0
                    &&& h.realms@.len() == quotas@.len()
                    &&& forall|r: int| 0 <= r < quotas@.len() ==> {
                        let rq = #[trigger] h.realms@[r];
                        rq.live_objects == 0
                        && rq.live_bytes == 0
                        && rq.max_objects == quotas@[r].0
                        && rq.max_bytes == quotas@[r].1
                    }
                },
                Err(e) => e == JsError::QuotaExceeded && quotas@.len() > u32::MAX as int,
            },
    {
        if quotas.len() > u32::MAX as usize {
            return Err(JsError::QuotaExceeded);
        }
        let m = quotas.len();
        let mut realms: Vec<RealmQuota> = Vec::new();
        let mut r: usize = 0;
        while r < m
            invariant
                r <= m,
                m == quotas@.len(),
                realms@.len() == r as int,
                forall|k: int| 0 <= k < r as int ==> {
                    let rq = #[trigger] realms@[k];
                    rq.live_objects == 0
                    && rq.live_bytes == 0
                    && rq.max_objects == quotas@[k].0
                    && rq.max_bytes == quotas@[k].1
                },
            decreases m - r,
        {
            let (max_objects, max_bytes) = quotas[r];
            realms.push(RealmQuota {
                live_objects: 0,
                live_bytes: 0,
                max_objects,
                max_bytes,
            });
            r += 1;
        }
        let h = GcHeap { slots: Vec::new(), realms };
        proof {
            assert(h@.len() == 0);
        }
        Ok(h)
    }

    /// Total live bytes currently allocated across all slots in `self` (verified exec query).
    pub fn total_live_bytes(&self) -> (total: usize)
        requires
            self.wf(),
        ensures
            total as nat == spec_total_live_bytes(self@),
    {
        let n = self.slots.len();
        let mut total: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                self.wf(),
                total as nat == spec_total_live_bytes_upto(self@, i as nat),
            decreases n - i,
        {
            proof {
                lemma_total_bytes_upto_monotonic(self@, (i + 1) as nat, n as nat);
            }
            match &self.slots[i] {
                Slot::Live(obj) => {
                    total = total + obj.byte_weight;
                },
                Slot::Free => {},
            }
            i += 1;
        }
        total
    }

    /// Allocate a new `GcObject` into either the first `Free` slot or at the end of the arena,
    /// enforcing per-realm `max_objects` and `max_bytes` quotas and preserving `self.wf()`.
    pub fn alloc(
        &mut self,
        realm: u32,
        byte_weight: usize,
        payload: GcPayload,
        edges: Vec<usize>,
    ) -> (res: Result<usize, JsError>)
        requires
            old(self).wf(),
            forall|k: int| 0 <= k < edges@.len() ==> {
                let t = #[trigger] edges@[k];
                (t as int) < old(self)@.len() && (old(self)@[t as int] is Live)
            },
        ensures
            final(self).wf(),
            final(self).realms@.len() == old(self).realms@.len(),
            match res {
                Ok(id) => {
                    &&& (id as int) < final(self)@.len()
                    &&& final(self)@[id as int] == SlotView::Live(GcObjectView {
                        realm,
                        byte_weight,
                        payload,
                        edges: edges@,
                    })
                    &&& forall|other: int| 0 <= other < old(self)@.len() && other != id as int
                        ==> final(self)@[other] == old(self)@[other]
                    &&& forall|live_id: int| 0 <= live_id < old(self)@.len() && (old(self)@[live_id] is Live)
                        ==> final(self)@[live_id] == old(self)@[live_id]
                },
                Err(_) => final(self)@ == old(self)@ && final(self).realms@ == old(self).realms@,
            },
    {
        if (realm as usize) >= self.realms.len() {
            return Err(JsError::RangeError);
        }
        let r_idx = realm as usize;
        let rq = self.realms[r_idx];
        if rq.live_objects >= rq.max_objects {
            return Err(JsError::QuotaExceeded);
        }
        if byte_weight > rq.max_bytes - rq.live_bytes {
            return Err(JsError::QuotaExceeded);
        }
        let cur_total = self.total_live_bytes();
        if byte_weight > usize::MAX - cur_total {
            return Err(JsError::QuotaExceeded);
        }

        // Check if there is an existing Free slot to reuse; otherwise append if < usize::MAX - 1.
        let n = self.slots.len();
        let mut free_idx: Option<usize> = None;
        let mut scan: usize = 0;
        while scan < n
            invariant
                scan <= n,
                n == self@.len(),
                match free_idx {
                    None => true,
                    Some(fi) => (fi as int) < n as int && self@[fi as int] == SlotView::Free,
                },
            decreases n - scan,
        {
            if matches!(self.slots[scan], Slot::Free) {
                free_idx = Some(scan);
                break;
            }
            scan += 1;
        }

        let new_obj = GcObject { realm, byte_weight, payload, edges };
        let ghost new_view = new_obj@;

        match free_idx {
            Some(fi) => {
                let ghost old_view = self@;
                self.slots.set(fi, Slot::Live(new_obj));
                self.realms.set(r_idx, RealmQuota {
                    live_objects: rq.live_objects + 1,
                    live_bytes: rq.live_bytes + byte_weight,
                    max_objects: rq.max_objects,
                    max_bytes: rq.max_bytes,
                });
                proof {
                    lemma_update_free_slot_accounting(old_view, self@, fi as int, new_view, self.realms@.len());
                    assert forall|rr: int| 0 <= rr < self.realms@.len() implies {
                        let q = #[trigger] self.realms@[rr];
                        q.live_objects as nat == spec_realm_live_objects(self@, rr as u32)
                        && q.live_bytes as nat == spec_realm_live_bytes(self@, rr as u32)
                        && q.live_objects <= q.max_objects
                        && q.live_bytes <= q.max_bytes
                    } by {
                        lemma_update_free_slot_upto(old_view, self@, fi as int, new_view, rr as u32, old_view.len());
                        let _ = old(self).realms@[rr];
                    };
                }
                Ok(fi)
            },
            None => {
                if n >= usize::MAX - 1 {
                    return Err(JsError::QuotaExceeded);
                }
                let ghost old_view = self@;
                self.slots.push(Slot::Live(new_obj));
                self.realms.set(r_idx, RealmQuota {
                    live_objects: rq.live_objects + 1,
                    live_bytes: rq.live_bytes + byte_weight,
                    max_objects: rq.max_objects,
                    max_bytes: rq.max_bytes,
                });
                proof {
                    assert(forall|k: int| 0 <= k < n as int ==> self@[k] == old_view[k]);
                    lemma_total_bytes_prefix_ext(self@, old_view, n as nat);
                    assert(spec_total_live_bytes_upto(self@, (n + 1) as nat)
                        == spec_total_live_bytes_upto(self@, n as nat) + (byte_weight as nat));
                    assert forall|rr: int| 0 <= rr < self.realms@.len() implies {
                        let q = #[trigger] self.realms@[rr];
                        q.live_objects as nat == spec_realm_live_objects(self@, rr as u32)
                        && q.live_bytes as nat == spec_realm_live_bytes(self@, rr as u32)
                        && q.live_objects <= q.max_objects
                        && q.live_bytes <= q.max_bytes
                    } by {
                        lemma_realm_objects_prefix_ext(self@, old_view, rr as u32, n as nat);
                        lemma_realm_bytes_prefix_ext(self@, old_view, rr as u32, n as nat);
                        let _ = old(self).realms@[rr];
                    };
                    assert forall|u: int| 0 <= u < self@.len()
                        implies spec_slot_valid(self@, self.realms@.len(), #[trigger] self@[u])
                    by {
                        if u < n as int {
                            assert(old_view[u] == self@[u]);
                            assert(spec_slot_valid(old_view, self.realms@.len(), old_view[u]));
                            if let SlotView::Live(o) = self@[u] {
                                assert forall|k: int| 0 <= k < o.edges.len() implies {
                                    let t = #[trigger] o.edges[k];
                                    (t as int) < self@.len() && (self@[t as int] is Live)
                                } by {
                                    let t = o.edges[k];
                                    assert((t as int) < old_view.len());
                                    assert(self@[t as int] == old_view[t as int]);
                                };
                            }
                        } else {
                            assert forall|k: int| 0 <= k < new_view.edges.len() implies {
                                let t = #[trigger] new_view.edges[k];
                                (t as int) < self@.len() && (self@[t as int] is Live)
                            } by {
                                let t = new_view.edges[k];
                                assert(self@[t as int] == old_view[t as int]);
                            };
                        }
                    };
                }
                Ok(n)
            },
        }
    }

    /// Add an outgoing reference edge `from -> to` between two live objects (supporting cyclic graphs!).
    pub fn add_edge(&mut self, from: usize, to: usize) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.len() == old(self)@.len(),
            final(self).realms@ == old(self).realms@,
            match res {
                Ok(()) => {
                    &&& (from as int) < final(self)@.len()
                    &&& (to as int) < final(self)@.len()
                    &&& (old(self)@[from as int] is Live)
                    &&& (old(self)@[to as int] is Live)
                    &&& spec_has_edge(final(self)@, from, to)
                    &&& forall|other: int| 0 <= other < final(self)@.len() && other != from as int
                        ==> final(self)@[other] == old(self)@[other]
                },
                Err(_) => final(self)@ == old(self)@,
            },
    {
        if from >= self.slots.len() || to >= self.slots.len() {
            return Err(JsError::RangeError);
        }
        if matches!(self.slots[to], Slot::Free) {
            return Err(JsError::TypeError);
        }
        match &self.slots[from] {
            Slot::Free => Err(JsError::TypeError),
            Slot::Live(obj) => {
                let mut new_edges = clone_usize_vec(&obj.edges);
                let ghost old_len: int = new_edges@.len() as int;
                new_edges.push(to);
                let updated = GcObject {
                    realm: obj.realm,
                    byte_weight: obj.byte_weight,
                    payload: obj.payload,
                    edges: new_edges,
                };
                let ghost old_view = self@;
                self.slots.set(from, Slot::Live(updated));
                proof {
                    lemma_same_weights_preserve_accounting(old_view, self@, from as int, self.realms@.len());
                    if let SlotView::Live(u_view) = self@[from as int] {
                        assert(u_view.edges[old_len] == to);
                    }
                    assert forall|u: int| 0 <= u < self@.len()
                        implies spec_slot_valid(self@, self.realms@.len(), #[trigger] self@[u])
                    by {
                        assert(spec_slot_valid(old_view, self.realms@.len(), old_view[u]));
                        if let SlotView::Live(o) = self@[u] {
                            assert forall|k: int| 0 <= k < o.edges.len() implies {
                                let t = #[trigger] o.edges[k];
                                (t as int) < self@.len() && (self@[t as int] is Live)
                            } by {
                                let t = o.edges[k];
                                if u == from as int && k == old_len {
                                    assert(t == to);
                                } else {
                                    if let SlotView::Live(old_o) = old_view[u] {
                                        assert(old_o.edges[k] == t);
                                    }
                                }
                                if t != from {
                                    assert(self@[t as int] == old_view[t as int]);
                                }
                            };
                        }
                    };
                }
                Ok(())
            },
        }
    }
}

proof fn lemma_update_free_slot_upto(
    old_h: Seq<SlotView>,
    new_h: Seq<SlotView>,
    fi: int,
    new_obj: GcObjectView,
    realm: u32,
    upto: nat,
)
    requires
        new_h.len() == old_h.len(),
        0 <= fi < old_h.len(),
        upto <= old_h.len(),
        old_h[fi] == SlotView::Free,
        new_h[fi] == SlotView::Live(new_obj),
        forall|k: int| 0 <= k < old_h.len() && k != fi ==> new_h[k] == old_h[k],
    ensures
        fi < upto as int ==> (
            spec_realm_objects_upto(new_h, realm, upto)
                == spec_realm_objects_upto(old_h, realm, upto) + (if new_obj.realm == realm { 1nat } else { 0nat })
            && spec_realm_bytes_upto(new_h, realm, upto)
                == spec_realm_bytes_upto(old_h, realm, upto) + (if new_obj.realm == realm { new_obj.byte_weight as nat } else { 0nat })
            && spec_total_live_bytes_upto(new_h, upto)
                == spec_total_live_bytes_upto(old_h, upto) + (new_obj.byte_weight as nat)
        ),
        fi >= upto as int ==> (
            spec_realm_objects_upto(new_h, realm, upto) == spec_realm_objects_upto(old_h, realm, upto)
            && spec_realm_bytes_upto(new_h, realm, upto) == spec_realm_bytes_upto(old_h, realm, upto)
            && spec_total_live_bytes_upto(new_h, upto) == spec_total_live_bytes_upto(old_h, upto)
        ),
    decreases upto,
{
    if upto > 0 {
        lemma_update_free_slot_upto(old_h, new_h, fi, new_obj, realm, (upto - 1) as nat);
    }
}

proof fn lemma_update_free_slot_accounting(
    old_h: Seq<SlotView>,
    new_h: Seq<SlotView>,
    fi: int,
    new_obj: GcObjectView,
    num_realms: nat,
)
    requires
        new_h.len() == old_h.len(),
        0 <= fi < old_h.len(),
        old_h[fi] == SlotView::Free,
        new_h[fi] == SlotView::Live(new_obj),
        (new_obj.realm as nat) < num_realms,
        forall|k: int| 0 <= k < new_obj.edges.len() ==> {
            let t = #[trigger] new_obj.edges[k];
            (t as int) < old_h.len() && (old_h[t as int] is Live)
        },
        spec_heap_graph_wf(old_h, num_realms),
        forall|k: int| 0 <= k < old_h.len() && k != fi ==> new_h[k] == old_h[k],
    ensures
        spec_heap_graph_wf(new_h, num_realms),
        spec_total_live_bytes(new_h) == spec_total_live_bytes(old_h) + (new_obj.byte_weight as nat),
{
    lemma_update_free_slot_upto(old_h, new_h, fi, new_obj, 0u32, old_h.len());
    assert forall|u: int| 0 <= u < new_h.len()
        implies spec_slot_valid(new_h, num_realms, #[trigger] new_h[u])
    by {
        if u == fi {
            assert forall|k: int| 0 <= k < new_obj.edges.len() implies {
                let t = #[trigger] new_obj.edges[k];
                (t as int) < new_h.len() && (new_h[t as int] is Live)
            } by {
                let t = new_obj.edges[k];
                if t as int != fi {
                    assert(new_h[t as int] == old_h[t as int]);
                }
            };
        } else {
            assert(new_h[u] == old_h[u]);
            assert(spec_slot_valid(old_h, num_realms, old_h[u]));
            if let SlotView::Live(o) = new_h[u] {
                assert forall|k: int| 0 <= k < o.edges.len() implies {
                    let t = #[trigger] o.edges[k];
                    (t as int) < new_h.len() && (new_h[t as int] is Live)
                } by {
                    let t = o.edges[k];
                    if t as int != fi {
                        assert(new_h[t as int] == old_h[t as int]);
                    }
                };
            }
        }
    };
}

proof fn lemma_same_weights_upto(
    old_h: Seq<SlotView>,
    new_h: Seq<SlotView>,
    idx: int,
    realm: u32,
    upto: nat,
)
    requires
        new_h.len() == old_h.len(),
        0 <= idx < old_h.len(),
        upto <= old_h.len(),
        match (old_h[idx], new_h[idx]) {
            (SlotView::Live(a), SlotView::Live(b)) => a.realm == b.realm && a.byte_weight == b.byte_weight,
            _ => false,
        },
        forall|k: int| 0 <= k < old_h.len() && k != idx ==> new_h[k] == old_h[k],
    ensures
        spec_realm_objects_upto(new_h, realm, upto) == spec_realm_objects_upto(old_h, realm, upto),
        spec_realm_bytes_upto(new_h, realm, upto) == spec_realm_bytes_upto(old_h, realm, upto),
        spec_total_live_bytes_upto(new_h, upto) == spec_total_live_bytes_upto(old_h, upto),
    decreases upto,
{
    if upto > 0 {
        lemma_same_weights_upto(old_h, new_h, idx, realm, (upto - 1) as nat);
    }
}

proof fn lemma_same_weights_preserve_accounting(
    old_h: Seq<SlotView>,
    new_h: Seq<SlotView>,
    idx: int,
    num_realms: nat,
)
    requires
        new_h.len() == old_h.len(),
        0 <= idx < old_h.len(),
        match (old_h[idx], new_h[idx]) {
            (SlotView::Live(a), SlotView::Live(b)) => a.realm == b.realm && a.byte_weight == b.byte_weight,
            _ => false,
        },
        forall|k: int| 0 <= k < old_h.len() && k != idx ==> new_h[k] == old_h[k],
    ensures
        spec_total_live_bytes(new_h) == spec_total_live_bytes(old_h),
        forall|r: u32| (r as nat) < num_realms ==> (
            #[trigger] spec_realm_live_objects(new_h, r) == spec_realm_live_objects(old_h, r)
            && spec_realm_live_bytes(new_h, r) == spec_realm_live_bytes(old_h, r)
        ),
{
    lemma_same_weights_upto(old_h, new_h, idx, 0u32, old_h.len());
    assert forall|r: u32| (r as nat) < num_realms implies (
        #[trigger] spec_realm_live_objects(new_h, r) == spec_realm_live_objects(old_h, r)
        && spec_realm_live_bytes(new_h, r) == spec_realm_live_bytes(old_h, r)
    ) by {
        lemma_same_weights_upto(old_h, new_h, idx, r, old_h.len());
    };
}

// -----------------------------------------------------------------------------------------------
// Formally Verified Iterative Tricolor Mark-Sweep Collector
// -----------------------------------------------------------------------------------------------

/// Execute a full iterative tricolor Mark-Sweep collection over `heap` from `roots`,
/// returning `(new_heap, stats)` with machine-checked `wf` preservation, soundness, and completeness.
pub fn mark_sweep(heap: &GcHeap, roots: &[usize]) -> (res: (GcHeap, GcStats))
    requires
        heap.wf(),
        roots_valid(heap, roots),
    ensures
        ({
            let new_heap = res.0;
            let stats = res.1;
            // (a) Heap well-formedness preservation (zero dangling pointers + exact per-realm quotas)
            &&& new_heap.wf()
            &&& new_heap@.len() == heap@.len()
            &&& new_heap.realms@.len() == heap.realms@.len()
            &&& forall|r: int| 0 <= r < heap.realms@.len() ==> {
                let nrq = #[trigger] new_heap.realms@[r];
                let orq = heap.realms@[r];
                nrq.max_objects == orq.max_objects
                && nrq.max_bytes == orq.max_bytes
                && nrq.live_objects <= orq.live_objects
                && nrq.live_bytes <= orq.live_bytes
            }
            // (b) Soundness (Live Preservation + Subgraph Isomorphism)
            &&& forall|id: usize| (id as int) < heap@.len() && spec_reachable(heap@, roots@, id)
                ==> (new_heap@[id as int] is Live) && new_heap@[id as int] == heap@[id as int]
            &&& forall|id: usize| spec_reachable(new_heap@, roots@, id) <==> spec_reachable(heap@, roots@, id)
            // (c) Completeness (Garbage Reclamation + Exact Freed Statistics)
            &&& forall|id: usize| (id as int) < heap@.len() && !spec_reachable(heap@, roots@, id)
                ==> new_heap@[id as int] == SlotView::Free
            &&& stats.total_slots == heap@.len()
            &&& stats.surviving_slots as nat == spec_count_reachable(heap@, roots@)
            &&& stats.freed_slots as nat == spec_count_reclaimed(heap@, roots@)
            &&& stats.surviving_bytes as nat == spec_total_live_bytes(new_heap@)
            &&& stats.freed_bytes as nat == spec_reclaimed_bytes(heap@, roots@)
        }),
{
    let n = heap.slots.len();

    // -------------------------------------------------------------------
    // Phase 1a: Initialize tricolor array to all White (unmarked)
    // -------------------------------------------------------------------
    let mut colors: Vec<Color> = Vec::new();
    let mut init_i: usize = 0;
    while init_i < n
        invariant
            init_i <= n,
            colors@.len() == init_i as int,
            forall|k: int| 0 <= k < init_i as int ==> colors@[k] == Color::White,
        decreases n - init_i,
    {
        colors.push(Color::White);
        init_i += 1;
    }
    proof {
        lemma_all_white_unmarked_upto(colors@, n as nat);
    }

    // -------------------------------------------------------------------
    // Phase 1b: Seed Gray worklist from `roots`
    // -------------------------------------------------------------------
    let mut worklist: Vec<usize> = Vec::new();
    let r_len = roots.len();
    let mut ri: usize = 0;
    while ri < r_len
        invariant
            ri <= r_len,
            r_len == roots@.len(),
            n == heap@.len(),
            heap.wf(),
            roots_valid(heap, roots),
            colors@.len() == n as int,
            spec_count_unmarked(colors@) + (worklist@.len() as nat) == n as nat,
            forall|k: int| 0 <= k < ri as int ==> colors@[roots@[k] as int] != Color::White,
            forall|id: usize| (id as int) < n as int ==> colors@[id as int] != Color::Black,
            forall|id: usize| (id as int) < n as int && colors@[id as int] != Color::White
                ==> spec_is_live(heap@, id) && spec_reachable(heap@, roots@, id),
            forall|wi: int| 0 <= wi < worklist@.len() ==> {
                let w = #[trigger] worklist@[wi];
                (w as int) < n as int && colors@[w as int] == Color::Gray
            },
            spec_no_dup_usize(worklist@),
            forall|id: usize| (id as int) < n as int && colors@[id as int] == Color::Gray
                ==> spec_seq_contains_usize(worklist@, id),
        decreases r_len - ri,
    {
        let r = roots[ri];
        proof {
            assert(roots@[ri as int] == r);
            lemma_root_is_reachable(heap@, roots@, ri as int);
        }
        if matches!(colors[r], Color::White) {
            let ghost old_colors = colors@;
            let ghost old_wl = worklist@;
            proof {
                lemma_white_to_gray_upto(old_colors, r as int, n as nat);
                assert forall|wi: int| 0 <= wi < old_wl.len() implies #[trigger] old_wl[wi] != r by {
                    let w = old_wl[wi];
                    assert(old_colors[w as int] == Color::Gray);
                };
            }
            colors.set(r, Color::Gray);
            worklist.push(r);
            proof {
                assert(worklist@[old_wl.len() as int] == r);
                assert forall|id: usize| (id as int) < n as int && colors@[id as int] == Color::Gray
                    implies spec_seq_contains_usize(worklist@, id)
                by {
                    if id == r {
                        assert(worklist@[old_wl.len() as int] == r);
                    } else {
                        assert(old_colors[id as int] == Color::Gray);
                        let wi = choose|k: int| 0 <= k < old_wl.len() && #[trigger] old_wl[k] == id;
                        assert(worklist@[wi] == id);
                    }
                };
            }
        }
        ri += 1;
    }

    // -------------------------------------------------------------------
    // Phase 2: Iterative Tricolor Worklist Mark
    // (`decreases` on unmarked slot count + worklist size!)
    // -------------------------------------------------------------------
    while worklist.len() > 0
        invariant
            heap.wf(),
            roots_valid(heap, roots),
            n == heap@.len(),
            colors@.len() == n as int,
            spec_count_unmarked(colors@) + (worklist@.len() as nat) <= n as nat,
            // Inv 1: All roots are marked (non-White)
            forall|k: int| 0 <= k < roots@.len() ==> colors@[roots@[k] as int] != Color::White,
            // Inv 2: Soundness — every marked slot is Live and Reachable
            forall|id: usize| (id as int) < n as int && colors@[id as int] != Color::White
                ==> spec_is_live(heap@, id) && spec_reachable(heap@, roots@, id),
            // Inv 3: Worklist entries are valid, Gray, and duplicate-free
            forall|wi: int| 0 <= wi < worklist@.len() ==> {
                let w = #[trigger] worklist@[wi];
                (w as int) < n as int && colors@[w as int] == Color::Gray
            },
            spec_no_dup_usize(worklist@),
            // Inv 4: Every Gray slot is on the worklist
            forall|id: usize| (id as int) < n as int && colors@[id as int] == Color::Gray
                ==> spec_seq_contains_usize(worklist@, id),
            // Inv 5: Dijkstra's Tricolor Invariant — no Black-to-White edge
            forall|u: usize, v: usize|
                (u as int) < n as int && (v as int) < n as int
                && colors@[u as int] == Color::Black
                && #[trigger] spec_has_edge(heap@, u, v)
                ==> colors@[v as int] != Color::White,
        decreases spec_count_unmarked(colors@) + (worklist@.len() as nat),
    {
        let ghost measure_before: nat = spec_count_unmarked(colors@) + (worklist@.len() as nat);
        let ghost pre_pop_wl = worklist@;
        let u = worklist.pop().unwrap();
        proof {
            let last = pre_pop_wl.len() - 1;
            assert(pre_pop_wl[last] == u);
            assert((u as int) < n as int);
            assert(colors@[u as int] == Color::Gray);
            assert(spec_is_live(heap@, u));
            assert(spec_reachable(heap@, roots@, u));
            assert forall|wi: int| 0 <= wi < worklist@.len() implies {
                let w = #[trigger] worklist@[wi];
                (w as int) < n as int && colors@[w as int] == Color::Gray && w != u
            } by {
                assert(worklist@[wi] == pre_pop_wl[wi]);
                assert(pre_pop_wl[wi] != pre_pop_wl[last]);
            };
            assert forall|id: usize|
                (id as int) < n as int && colors@[id as int] == Color::Gray && id != u
                implies spec_seq_contains_usize(worklist@, id)
            by {
                let wi = choose|k: int| 0 <= k < pre_pop_wl.len() && #[trigger] pre_pop_wl[k] == id;
                assert(wi != last);
                assert(worklist@[wi] == id);
            };
        }

        match &heap.slots[u] {
            Slot::Free => {
                proof {
                    assert(heap@[u as int] == heap.slots@[u as int]@);
                    assert(false);
                }
            },
            Slot::Live(obj) => {
                let e_len = obj.edges.len();
                let mut j: usize = 0;
                while j < e_len
                    invariant
                        j <= e_len,
                        e_len == obj.edges@.len(),
                        heap@[u as int] == SlotView::Live(obj@),
                        heap.wf(),
                        roots_valid(heap, roots),
                        n == heap@.len(),
                        (u as int) < n as int,
                        colors@.len() == n as int,
                        colors@[u as int] == Color::Gray,
                        spec_reachable(heap@, roots@, u),
                        spec_count_unmarked(colors@) + (worklist@.len() as nat) + 1 == measure_before,
                        forall|k: int| 0 <= k < roots@.len() ==> colors@[roots@[k] as int] != Color::White,
                        forall|id: usize| (id as int) < n as int && colors@[id as int] != Color::White
                            ==> spec_is_live(heap@, id) && spec_reachable(heap@, roots@, id),
                        forall|wi: int| 0 <= wi < worklist@.len() ==> {
                            let w = #[trigger] worklist@[wi];
                            (w as int) < n as int && colors@[w as int] == Color::Gray && w != u
                        },
                        spec_no_dup_usize(worklist@),
                        forall|id: usize|
                            (id as int) < n as int && colors@[id as int] == Color::Gray && id != u
                            ==> spec_seq_contains_usize(worklist@, id),
                        forall|bu: usize, bv: usize|
                            (bu as int) < n as int && (bv as int) < n as int
                            && colors@[bu as int] == Color::Black
                            && #[trigger] spec_has_edge(heap@, bu, bv)
                            ==> colors@[bv as int] != Color::White,
                        forall|ek: int| 0 <= ek < j as int ==> colors@[obj.edges@[ek] as int] != Color::White,
                    decreases e_len - j,
                {
                    let v = obj.edges[j];
                    proof {
                        assert(spec_slot_valid(heap@, heap.realms@.len(), heap@[u as int]));
                        assert(obj.edges@[j as int] == v);
                        assert(spec_has_edge(heap@, u, v));
                        assert((v as int) < n as int);
                        assert(spec_is_live(heap@, v));
                        lemma_reachable_step(heap@, roots@, u, v);
                    }
                    if matches!(colors[v], Color::White) {
                        let ghost old_c = colors@;
                        let ghost old_w = worklist@;
                        proof {
                            assert(v != u);
                            lemma_white_to_gray_upto(old_c, v as int, n as nat);
                            assert forall|wi: int| 0 <= wi < old_w.len() implies #[trigger] old_w[wi] != v by {
                                let w = old_w[wi];
                                assert(old_c[w as int] == Color::Gray);
                            };
                        }
                        colors.set(v, Color::Gray);
                        worklist.push(v);
                        proof {
                            assert(worklist@[old_w.len() as int] == v);
                            assert forall|id: usize|
                                (id as int) < n as int && colors@[id as int] == Color::Gray && id != u
                                implies spec_seq_contains_usize(worklist@, id)
                            by {
                                if id == v {
                                    assert(worklist@[old_w.len() as int] == v);
                                } else {
                                    assert(old_c[id as int] == Color::Gray);
                                    let wi = choose|k: int| 0 <= k < old_w.len() && #[trigger] old_w[k] == id;
                                    assert(worklist@[wi] == id);
                                }
                            };
                        }
                    }
                    j += 1;
                }

                let ghost pre_black_c = colors@;
                proof {
                    lemma_gray_to_black_upto(pre_black_c, u as int, n as nat);
                }
                colors.set(u, Color::Black);
                proof {
                    assert forall|bu: usize, bv: usize|
                        (bu as int) < n as int && (bv as int) < n as int
                        && colors@[bu as int] == Color::Black
                        && #[trigger] spec_has_edge(heap@, bu, bv)
                        implies colors@[bv as int] != Color::White
                    by {
                        if bu == u {
                            let ek = choose|k: int| 0 <= k < obj.edges@.len() && #[trigger] obj.edges@[k] == bv;
                            assert(pre_black_c[bv as int] != Color::White);
                        } else {
                            assert(pre_black_c[bu as int] == Color::Black);
                            assert(pre_black_c[bv as int] != Color::White);
                        }
                    };
                    assert forall|id: usize|
                        (id as int) < n as int && colors@[id as int] == Color::Gray
                        implies spec_seq_contains_usize(worklist@, id)
                    by {
                        assert(id != u);
                        assert(pre_black_c[id as int] == Color::Gray);
                    };
                }
            },
        }
    }

    // Establish exact Mark Equivalence: `colors@[id] != White <==> spec_reachable(heap@, roots@, id)`
    proof {
        assert forall|k: int| 0 <= k < n as int implies colors@[k] != Color::Gray by {
            if colors@[k] == Color::Gray {
                assert(spec_seq_contains_usize(worklist@, k as usize));
                assert(false);
            }
        };
        assert forall|id: usize| (id as int) < n as int
            implies (colors@[id as int] != Color::White <==> spec_reachable(heap@, roots@, id))
        by {
            if spec_reachable(heap@, roots@, id) {
                let s = choose|steps: nat| #[trigger] spec_reachable_in(heap@, roots@, id, steps);
                lemma_tricolor_reachable_in_is_black(heap@, roots@, colors@, heap.realms@.len(), id, s);
            }
        };
    }

    // -------------------------------------------------------------------
    // Phase 3: Linear Sweep & Exact Per-Realm Quota Recomputation
    // -------------------------------------------------------------------
    let num_realms = heap.realms.len();
    let mut new_realms: Vec<RealmQuota> = Vec::new();
    let mut r_init: usize = 0;
    while r_init < num_realms
        invariant
            r_init <= num_realms,
            num_realms == heap.realms@.len(),
            new_realms@.len() == r_init as int,
            forall|r: int| 0 <= r < r_init as int ==> {
                let nrq = #[trigger] new_realms@[r];
                let orq = heap.realms@[r];
                nrq.live_objects == 0
                && nrq.live_bytes == 0
                && nrq.max_objects == orq.max_objects
                && nrq.max_bytes == orq.max_bytes
            },
        decreases num_realms - r_init,
    {
        let orq = heap.realms[r_init];
        new_realms.push(RealmQuota {
            live_objects: 0,
            live_bytes: 0,
            max_objects: orq.max_objects,
            max_bytes: orq.max_bytes,
        });
        r_init += 1;
    }

    let mut new_slots: Vec<Slot> = Vec::new();
    let mut surviving_slots: usize = 0;
    let mut freed_slots: usize = 0;
    let mut surviving_bytes: usize = 0;
    let mut freed_bytes: usize = 0;
    let mut sweep_i: usize = 0;

    while sweep_i < n
        invariant
            sweep_i <= n,
            n == heap@.len(),
            num_realms == heap.realms@.len(),
            heap.wf(),
            colors@.len() == n as int,
            forall|id: usize| (id as int) < n as int
                ==> (colors@[id as int] != Color::White <==> spec_reachable(heap@, roots@, id)),
            forall|id: usize| (id as int) < n as int && colors@[id as int] != Color::White
                ==> spec_is_live(heap@, id),
            new_slots@.len() == sweep_i as int,
            new_realms@.len() == num_realms as int,
            forall|k: int| 0 <= k < sweep_i as int && spec_reachable(heap@, roots@, k as usize)
                ==> spec_slots_view(new_slots@)[k] == heap@[k],
            forall|k: int| 0 <= k < sweep_i as int && !spec_reachable(heap@, roots@, k as usize)
                ==> spec_slots_view(new_slots@)[k] == SlotView::Free,
            surviving_slots as nat == spec_count_reachable_upto(heap@, roots@, sweep_i as nat),
            freed_slots as nat == spec_count_reclaimed_upto(heap@, roots@, sweep_i as nat),
            surviving_slots + freed_slots <= sweep_i,
            surviving_bytes as nat == spec_total_live_bytes_upto(spec_slots_view(new_slots@), sweep_i as nat),
            freed_bytes as nat == spec_reclaimed_bytes_upto(heap@, roots@, sweep_i as nat),
            (surviving_bytes as nat) + (freed_bytes as nat) == spec_total_live_bytes_upto(heap@, sweep_i as nat),
            forall|r: int| 0 <= r < num_realms as int ==> {
                let nrq = #[trigger] new_realms@[r];
                let orq = heap.realms@[r];
                &&& nrq.max_objects == orq.max_objects
                &&& nrq.max_bytes == orq.max_bytes
                &&& nrq.live_objects as nat == spec_realm_objects_upto(spec_slots_view(new_slots@), r as u32, sweep_i as nat)
                &&& nrq.live_bytes as nat == spec_realm_bytes_upto(spec_slots_view(new_slots@), r as u32, sweep_i as nat)
                &&& nrq.live_objects as nat <= spec_realm_objects_upto(heap@, r as u32, sweep_i as nat)
                &&& nrq.live_bytes as nat <= spec_realm_bytes_upto(heap@, r as u32, sweep_i as nat)
            },
        decreases n - sweep_i,
    {
        let ghost prev_views = spec_slots_view(new_slots@);
        proof {
            lemma_total_bytes_upto_monotonic(heap@, (sweep_i + 1) as nat, n as nat);
            assert(heap@[sweep_i as int] == heap.slots@[sweep_i as int]@);
        }

        if !matches!(colors[sweep_i], Color::White) {
            // Reachable live object: preserve identically and accumulate realm usage
            match &heap.slots[sweep_i] {
                Slot::Free => {
                    proof { assert(false); }
                },
                Slot::Live(obj) => {
                    let r_idx = obj.realm as usize;
                    let w = obj.byte_weight;
                    proof {
                        assert(spec_slot_valid(heap@, num_realms as nat, heap@[sweep_i as int]));
                        assert(r_idx < num_realms);
                        lemma_realm_upto_monotonic(heap@, obj.realm, (sweep_i + 1) as nat, n as nat);
                        let _ = heap.realms@[r_idx as int];
                    }
                    let nrq = new_realms[r_idx];
                    new_realms.set(r_idx, RealmQuota {
                        live_objects: nrq.live_objects + 1,
                        live_bytes: nrq.live_bytes + w,
                        max_objects: nrq.max_objects,
                        max_bytes: nrq.max_bytes,
                    });
                    let cloned = clone_gc_object(obj);
                    new_slots.push(Slot::Live(cloned));
                    surviving_slots += 1;
                    surviving_bytes += w;
                    proof {
                        let cur_views = spec_slots_view(new_slots@);
                        assert(forall|k: int| 0 <= k < sweep_i as int ==> cur_views[k] == prev_views[k]);
                        lemma_total_bytes_prefix_ext(cur_views, prev_views, sweep_i as nat);
                        assert forall|r: int| 0 <= r < num_realms as int implies {
                            let q = #[trigger] new_realms@[r];
                            let orq = heap.realms@[r];
                            &&& q.max_objects == orq.max_objects
                            &&& q.max_bytes == orq.max_bytes
                            &&& q.live_objects as nat == spec_realm_objects_upto(cur_views, r as u32, (sweep_i + 1) as nat)
                            &&& q.live_bytes as nat == spec_realm_bytes_upto(cur_views, r as u32, (sweep_i + 1) as nat)
                            &&& q.live_objects as nat <= spec_realm_objects_upto(heap@, r as u32, (sweep_i + 1) as nat)
                            &&& q.live_bytes as nat <= spec_realm_bytes_upto(heap@, r as u32, (sweep_i + 1) as nat)
                        } by {
                            lemma_realm_objects_prefix_ext(cur_views, prev_views, r as u32, sweep_i as nat);
                            lemma_realm_bytes_prefix_ext(cur_views, prev_views, r as u32, sweep_i as nat);
                        };
                    }
                },
            }
        } else {
            // Unreachable slot: reclaim if previously Live, leave Free if already Free
            match &heap.slots[sweep_i] {
                Slot::Live(obj) => {
                    let w = obj.byte_weight;
                    freed_slots += 1;
                    freed_bytes += w;
                },
                Slot::Free => {},
            }
            new_slots.push(Slot::Free);
            proof {
                let cur_views = spec_slots_view(new_slots@);
                assert(forall|k: int| 0 <= k < sweep_i as int ==> cur_views[k] == prev_views[k]);
                lemma_total_bytes_prefix_ext(cur_views, prev_views, sweep_i as nat);
                assert forall|r: int| 0 <= r < num_realms as int implies {
                    let q = #[trigger] new_realms@[r];
                    let orq = heap.realms@[r];
                    &&& q.max_objects == orq.max_objects
                    &&& q.max_bytes == orq.max_bytes
                    &&& q.live_objects as nat == spec_realm_objects_upto(cur_views, r as u32, (sweep_i + 1) as nat)
                    &&& q.live_bytes as nat == spec_realm_bytes_upto(cur_views, r as u32, (sweep_i + 1) as nat)
                    &&& q.live_objects as nat <= spec_realm_objects_upto(heap@, r as u32, (sweep_i + 1) as nat)
                    &&& q.live_bytes as nat <= spec_realm_bytes_upto(heap@, r as u32, (sweep_i + 1) as nat)
                } by {
                    lemma_realm_objects_prefix_ext(cur_views, prev_views, r as u32, sweep_i as nat);
                    lemma_realm_bytes_prefix_ext(cur_views, prev_views, r as u32, sweep_i as nat);
                };
            }
        }
        sweep_i += 1;
    }

    let new_heap = GcHeap {
        slots: new_slots,
        realms: new_realms,
    };
    let stats = GcStats {
        total_slots: n,
        surviving_slots,
        freed_slots,
        surviving_bytes,
        freed_bytes,
    };

    // Final proof of `new_heap.wf()` (zero dangling pointers + realm bounds) & reachability isomorphism
    proof {
        assert forall|r: int| 0 <= r < new_heap.realms@.len() implies {
            let nrq = #[trigger] new_heap.realms@[r];
            let orq = heap.realms@[r];
            &&& nrq.max_objects == orq.max_objects
            &&& nrq.max_bytes == orq.max_bytes
            &&& nrq.live_objects as nat == spec_realm_live_objects(new_heap@, r as u32)
            &&& nrq.live_bytes as nat == spec_realm_live_bytes(new_heap@, r as u32)
            &&& nrq.live_objects <= orq.live_objects
            &&& nrq.live_bytes <= orq.live_bytes
            &&& nrq.live_objects <= nrq.max_objects
            &&& nrq.live_bytes <= nrq.max_bytes
        } by {
            let _ = heap.realms@[r];
        };

        assert forall|id: usize| (id as int) < heap@.len() && spec_reachable(heap@, roots@, id)
            implies (new_heap@[id as int] is Live) && new_heap@[id as int] == heap@[id as int]
        by {
            lemma_reachable_implies_live(heap@, roots@, id);
            let k: int = id as int;
            assert(0 <= k < n as int && k as usize == id);
            assert(new_heap@[k] == heap@[k]);
        };

        assert forall|id: usize| (id as int) < heap@.len() && !spec_reachable(heap@, roots@, id)
            implies new_heap@[id as int] == SlotView::Free
        by {
            let k: int = id as int;
            assert(0 <= k < n as int && k as usize == id);
            assert(new_heap@[k] == SlotView::Free);
        };

        assert forall|u: int| 0 <= u < new_heap@.len()
            implies spec_slot_valid(new_heap@, new_heap.realms@.len(), #[trigger] new_heap@[u])
        by {
            if spec_reachable(heap@, roots@, u as usize) {
                assert(new_heap@[u] == heap@[u]);
                assert(spec_slot_valid(heap@, heap.realms@.len(), heap@[u]));
                if let SlotView::Live(obj) = new_heap@[u] {
                    assert forall|k: int| 0 <= k < obj.edges.len() implies {
                        let target = #[trigger] obj.edges[k];
                        (target as int) < new_heap@.len() && (new_heap@[target as int] is Live)
                    } by {
                        let target = obj.edges[k];
                        assert(spec_has_edge(heap@, u as usize, target));
                        assert((target as int) < heap@.len());
                        assert(spec_is_live(heap@, target));
                        lemma_reachable_step(heap@, roots@, u as usize, target);
                        assert(new_heap@[target as int] == heap@[target as int]);
                    };
                }
            } else {
                assert(new_heap@[u] == SlotView::Free);
            }
        };

        assert forall|id: usize|
            spec_reachable(new_heap@, roots@, id) <==> spec_reachable(heap@, roots@, id)
        by {
            if spec_reachable(heap@, roots@, id) {
                lemma_reachable_implies_live(heap@, roots@, id);
                let s = choose|steps: nat| #[trigger] spec_reachable_in(heap@, roots@, id, steps);
                lemma_reachable_in_preserved_forward(heap@, new_heap@, roots@, id, s);
            }
            if spec_reachable(new_heap@, roots@, id) {
                lemma_reachable_implies_live(new_heap@, roots@, id);
                let s = choose|steps: nat| #[trigger] spec_reachable_in(new_heap@, roots@, id, steps);
                lemma_reachable_in_preserved_backward(heap@, new_heap@, roots@, id, s);
            }
        };
    }

    (new_heap, stats)
}

impl GcHeap {
    /// Convenience in-place collection method replacing `*self` with `mark_sweep(self, roots)`.
    pub fn collect(&mut self, roots: &[usize]) -> (stats: GcStats)
        requires
            old(self).wf(),
            roots_valid(old(self), roots),
        ensures
            final(self).wf(),
            final(self)@.len() == old(self)@.len(),
            forall|id: usize| (id as int) < old(self)@.len() && spec_reachable(old(self)@, roots@, id)
                ==> (final(self)@[id as int] is Live) && final(self)@[id as int] == old(self)@[id as int],
            forall|id: usize| (id as int) < old(self)@.len() && !spec_reachable(old(self)@, roots@, id)
                ==> final(self)@[id as int] == SlotView::Free,
            stats.freed_slots as nat == spec_count_reclaimed(old(self)@, roots@),
            stats.surviving_slots as nat == spec_count_reachable(old(self)@, roots@),
    {
        let (next_heap, stats) = mark_sweep(self, roots);
        *self = next_heap;
        stats
    }
}

} // verus!
