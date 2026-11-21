//! ECMA-262 §9.1 Lexical Environment Records Arena (`EnvId`, `EnvArena`),
//! Temporal Dead Zone (`Uninitialized`) semantics, immutable `const` vs mutable `let`/`var`,
//! mark-sweep dead environment slot reclamation & reuse, and machine-checked well-formedness (`env_wf`) proofs.
use crate::value::{clone_js_str, clone_val, js_str_eq, JsStr, SpecVal, Val};
use vstd::prelude::*;

verus! {

/// Lexical environment identifier in `EnvArena`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct EnvId(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EnvKind {
    Global,
    Function,
    Block,
    Catch,
}

/// Binding initialization state (§9.1.1.1): `Uninitialized` models the Temporal Dead Zone (TDZ).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BindingStatus {
    Uninitialized,
    Initialized(Val),
}

pub enum SpecBindingStatus {
    Uninitialized,
    Initialized(SpecVal),
}

impl View for BindingStatus {
    type V = SpecBindingStatus;

    open spec fn view(&self) -> SpecBindingStatus {
        match self {
            BindingStatus::Uninitialized => SpecBindingStatus::Uninitialized,
            BindingStatus::Initialized(v) => SpecBindingStatus::Initialized(v@),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Binding {
    pub name: JsStr,
    pub mutable: bool,
    pub strict: bool,
    pub status: BindingStatus,
}

pub struct SpecBinding {
    pub name: Seq<u16>,
    pub mutable: bool,
    pub strict: bool,
    pub status: SpecBindingStatus,
}

impl View for Binding {
    type V = SpecBinding;

    open spec fn view(&self) -> SpecBinding {
        SpecBinding {
            name: self.name@,
            mutable: self.mutable,
            strict: self.strict,
            status: self.status@,
        }
    }
}

pub open spec fn spec_bindings_view(bs: Seq<Binding>) -> Seq<SpecBinding> {
    Seq::new(bs.len(), |i: int| bs[i]@)
}

pub open spec fn spec_opt_val_view(o: &Option<Val>) -> Option<SpecVal> {
    match o {
        None => None,
        Some(v) => Some(v@),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EnvRecord {
    pub kind: EnvKind,
    pub outer: Option<EnvId>,
    pub this_binding: Option<Val>,
    pub bindings: Vec<Binding>,
}

pub struct SpecEnvRecord {
    pub kind: EnvKind,
    pub outer: Option<EnvId>,
    pub this_binding: Option<SpecVal>,
    pub bindings: Seq<SpecBinding>,
}

impl View for EnvRecord {
    type V = SpecEnvRecord;

    open spec fn view(&self) -> SpecEnvRecord {
        SpecEnvRecord {
            kind: self.kind,
            outer: self.outer,
            this_binding: spec_opt_val_view(&self.this_binding),
            bindings: spec_bindings_view(self.bindings@),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum EnvSlot {
    Live(EnvRecord),
    Free,
}

pub enum SpecEnvSlot {
    Live(SpecEnvRecord),
    Free,
}

impl View for EnvSlot {
    type V = SpecEnvSlot;

    open spec fn view(&self) -> SpecEnvSlot {
        match self {
            EnvSlot::Live(rec) => SpecEnvSlot::Live(rec@),
            EnvSlot::Free => SpecEnvSlot::Free,
        }
    }
}

pub open spec fn spec_env_slots_view(es: Seq<EnvSlot>) -> Seq<SpecEnvSlot> {
    Seq::new(es.len(), |i: int| es[i]@)
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EnvArena {
    pub envs: Vec<EnvSlot>,
}

pub struct SpecEnvArena {
    pub envs: Seq<SpecEnvSlot>,
}

impl View for EnvArena {
    type V = SpecEnvArena;

    open spec fn view(&self) -> SpecEnvArena {
        SpecEnvArena { envs: spec_env_slots_view(self.envs@) }
    }
}

// ---------------------------------------------------------------------------
// Well-Formedness Specification (`env_wf`) & Structural Lemmas
// ---------------------------------------------------------------------------

pub open spec fn spec_bindings_unique(bs: Seq<SpecBinding>) -> bool {
    forall|i: int, j: int| 0 <= i < j < bs.len() ==> bs[i].name != bs[j].name
}

pub open spec fn spec_slot_is_live(s: SpecEnvSlot) -> bool {
    s is Live
}

/// Environment arena well-formedness:
/// 1. Slot 0 is a `Live` root `Global` environment with `outer == None` and unique binding names.
/// 2. Every `Live` environment at `i > 0` has `outer == Some(p)` where `p.0 < arena.envs.len()`,
///    `p.0 != i`, `arena.envs[p.0]` is `Live` (zero dangling `EnvId`s!), and unique binding names.
pub open spec fn env_wf(arena: SpecEnvArena) -> bool {
    arena.envs.len() >= 1
    && match arena.envs[0] {
        SpecEnvSlot::Live(rec) => rec.kind == EnvKind::Global && (rec.outer is None) && spec_bindings_unique(rec.bindings),
        SpecEnvSlot::Free => false,
    }
    && (forall|i: int| 1 <= i < arena.envs.len() ==> match #[trigger] arena.envs[i] {
        SpecEnvSlot::Free => true,
        SpecEnvSlot::Live(rec) => {
            spec_bindings_unique(rec.bindings)
            && match rec.outer {
                None => false,
                Some(p) => (p.0 as int) < arena.envs.len()
                    && (p.0 as int) != i
                    && (arena.envs[p.0 as int] is Live),
            }
        }
    })
}

/// Theorem: In any well-formed `EnvArena`, every `Live` `EnvId` either is `EnvId(0)` (`Global`)
/// or points to an in-bounds `Live` parent `p != id` (zero dangling environment pointers).
pub proof fn lemma_env_wf_outer_valid(arena: SpecEnvArena, id: EnvId)
    requires
        env_wf(arena),
        (id.0 as int) < arena.envs.len(),
        arena.envs[id.0 as int] is Live,
    ensures
        match arena.envs[id.0 as int] {
            SpecEnvSlot::Live(rec) => match rec.outer {
                None => id.0 == 0 && rec.kind == EnvKind::Global,
                Some(p) => (p.0 as int) < arena.envs.len() && p.0 != id.0 && (arena.envs[p.0 as int] is Live),
            },
            SpecEnvSlot::Free => false,
        },
{
    let _ = arena.envs[id.0 as int];
}

// ---------------------------------------------------------------------------
// Outcomes for Identifier Lookup & Mutation
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum IdentLookup {
    Found(Val),
    TdzUninitialized,
    Undeclared,
}

pub enum SpecIdentLookup {
    Found(SpecVal),
    TdzUninitialized,
    Undeclared,
}

impl View for IdentLookup {
    type V = SpecIdentLookup;

    open spec fn view(&self) -> SpecIdentLookup {
        match self {
            IdentLookup::Found(v) => SpecIdentLookup::Found(v@),
            IdentLookup::TdzUninitialized => SpecIdentLookup::TdzUninitialized,
            IdentLookup::Undeclared => SpecIdentLookup::Undeclared,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IdentAssignOutcome {
    Ok,
    TdzUninitialized,
    ImmutableConst,
    UndeclaredStrict,
}

// ---------------------------------------------------------------------------
// Spec Operations on `SpecEnvArena`
// ---------------------------------------------------------------------------

pub open spec fn spec_new_global_env(global_this: SpecVal) -> SpecEnvArena {
    SpecEnvArena {
        envs: seq![SpecEnvSlot::Live(SpecEnvRecord {
            kind: EnvKind::Global,
            outer: None,
            this_binding: Some(global_this),
            bindings: seq![],
        })],
    }
}

pub open spec fn spec_find_free_env_from(envs: Seq<SpecEnvSlot>, idx: nat) -> Option<nat>
    decreases envs.len() - idx,
{
    if idx >= envs.len() {
        None
    } else if envs[idx as int] is Free {
        Some(idx)
    } else {
        spec_find_free_env_from(envs, idx + 1)
    }
}

pub proof fn lemma_find_free_env_props(envs: Seq<SpecEnvSlot>, idx: nat)
    requires idx <= envs.len(),
    ensures
        match spec_find_free_env_from(envs, idx) {
            Some(found) => idx <= found < envs.len() && (envs[found as int] is Free),
            None => true,
        },
    decreases envs.len() - idx,
{
    if idx < envs.len() && !(envs[idx as int] is Free) {
        lemma_find_free_env_props(envs, idx + 1);
    }
}

pub open spec fn spec_alloc_env(
    arena: SpecEnvArena,
    kind: EnvKind,
    outer: EnvId,
    this_binding: Option<SpecVal>,
) -> (SpecEnvArena, EnvId) {
    if arena.envs.len() == 0 {
        let base = spec_new_global_env(SpecVal::Undefined);
        (base, EnvId(0))
    } else {
        let safe_outer = if (outer.0 as int) < arena.envs.len() && (arena.envs[outer.0 as int] is Live) {
            outer
        } else {
            EnvId(0)
        };
        let safe_kind = if kind == EnvKind::Global { EnvKind::Block } else { kind };
        let rec = SpecEnvRecord {
            kind: safe_kind,
            outer: Some(safe_outer),
            this_binding,
            bindings: seq![],
        };
        match spec_find_free_env_from(arena.envs, 1) {
            Some(idx) => (
                SpecEnvArena { envs: arena.envs.update(idx as int, SpecEnvSlot::Live(rec)) },
                EnvId(idx as usize),
            ),
            None => {
                let id = EnvId(arena.envs.len() as usize);
                (SpecEnvArena { envs: arena.envs.push(SpecEnvSlot::Live(rec)) }, id)
            }
        }
    }
}

pub open spec fn spec_sweep_envs(arena: SpecEnvArena, marks: Seq<bool>) -> SpecEnvArena {
    SpecEnvArena {
        envs: Seq::new(arena.envs.len(), |i: int| {
            if i == 0 || (i < marks.len() && marks[i]) {
                arena.envs[i]
            } else {
                SpecEnvSlot::Free
            }
        }),
    }
}

pub open spec fn spec_find_binding_from(bs: Seq<SpecBinding>, name: Seq<u16>, idx: nat) -> Option<nat>
    decreases bs.len() - idx,
{
    if idx >= bs.len() {
        None
    } else if bs[idx as int].name == name {
        Some(idx)
    } else {
        spec_find_binding_from(bs, name, idx + 1)
    }
}

pub open spec fn spec_find_binding(bs: Seq<SpecBinding>, name: Seq<u16>) -> Option<nat> {
    spec_find_binding_from(bs, name, 0)
}

pub proof fn lemma_find_binding_props(bs: Seq<SpecBinding>, name: Seq<u16>, idx: nat)
    requires idx <= bs.len(),
    ensures
        match spec_find_binding_from(bs, name, idx) {
            Some(found) => idx <= found < bs.len() && bs[found as int].name == name,
            None => forall|k: int| idx as int <= k < bs.len() ==> bs[k].name != name,
        },
    decreases bs.len() - idx,
{
    if idx < bs.len() && bs[idx as int].name != name {
        lemma_find_binding_props(bs, name, idx + 1);
    }
}

pub open spec fn spec_upsert_binding(bs: Seq<SpecBinding>, b: SpecBinding) -> Seq<SpecBinding> {
    match spec_find_binding(bs, b.name) {
        Some(idx) => bs.update(idx as int, b),
        None => bs.push(b),
    }
}

pub proof fn lemma_upsert_preserves_unique(bs: Seq<SpecBinding>, b: SpecBinding)
    requires spec_bindings_unique(bs),
    ensures spec_bindings_unique(spec_upsert_binding(bs, b)),
{
    lemma_find_binding_props(bs, b.name, 0);
    match spec_find_binding(bs, b.name) {
        Some(idx) => {
            let bs2 = bs.update(idx as int, b);
            assert forall|i: int, j: int| 0 <= i < j < bs2.len() implies bs2[i].name != bs2[j].name by {
                if i == idx as int {
                    assert(bs[idx as int].name == b.name);
                    assert(bs[idx as int].name != bs[j].name);
                } else if j == idx as int {
                    assert(bs[idx as int].name == b.name);
                    assert(bs[i].name != bs[idx as int].name);
                } else {
                    assert(bs2[i].name == bs[i].name);
                    assert(bs2[j].name == bs[j].name);
                }
            }
        }
        None => {
            let bs2 = bs.push(b);
            assert forall|i: int, j: int| 0 <= i < j < bs2.len() implies bs2[i].name != bs2[j].name by {
                if j == bs.len() {
                    assert(bs[i].name != b.name);
                }
            }
        }
    }
}

pub open spec fn spec_declare_tdz(
    arena: SpecEnvArena,
    env_id: EnvId,
    name: Seq<u16>,
    mutable: bool,
    strict: bool,
) -> SpecEnvArena {
    if (env_id.0 as int) >= arena.envs.len() {
        arena
    } else {
        match arena.envs[env_id.0 as int] {
            SpecEnvSlot::Free => arena,
            SpecEnvSlot::Live(rec) => {
                let new_b = SpecBinding {
                    name,
                    mutable,
                    strict,
                    status: SpecBindingStatus::Uninitialized,
                };
                let rec2 = SpecEnvRecord {
                    bindings: spec_upsert_binding(rec.bindings, new_b),
                    ..rec
                };
                SpecEnvArena { envs: arena.envs.update(env_id.0 as int, SpecEnvSlot::Live(rec2)) }
            }
        }
    }
}

pub open spec fn spec_bind_initialized(
    arena: SpecEnvArena,
    env_id: EnvId,
    name: Seq<u16>,
    val: SpecVal,
    mutable: bool,
    strict: bool,
) -> SpecEnvArena {
    if (env_id.0 as int) >= arena.envs.len() {
        arena
    } else {
        match arena.envs[env_id.0 as int] {
            SpecEnvSlot::Free => arena,
            SpecEnvSlot::Live(rec) => {
                let new_b = SpecBinding {
                    name,
                    mutable,
                    strict,
                    status: SpecBindingStatus::Initialized(val),
                };
                let rec2 = SpecEnvRecord {
                    bindings: spec_upsert_binding(rec.bindings, new_b),
                    ..rec
                };
                SpecEnvArena { envs: arena.envs.update(env_id.0 as int, SpecEnvSlot::Live(rec2)) }
            }
        }
    }
}

pub open spec fn spec_find_var_env_steps(arena: SpecEnvArena, cur: EnvId, steps: nat) -> EnvId
    decreases steps,
{
    if steps == 0 || (cur.0 as int) >= arena.envs.len() {
        EnvId(0)
    } else {
        match arena.envs[cur.0 as int] {
            SpecEnvSlot::Free => EnvId(0),
            SpecEnvSlot::Live(rec) => {
                if rec.kind == EnvKind::Global || rec.kind == EnvKind::Function {
                    cur
                } else {
                    match rec.outer {
                        Some(p) => spec_find_var_env_steps(arena, p, (steps - 1) as nat),
                        None => EnvId(0),
                    }
                }
            }
        }
    }
}

pub open spec fn spec_find_var_env(arena: SpecEnvArena, cur: EnvId) -> EnvId {
    spec_find_var_env_steps(arena, cur, arena.envs.len())
}

/// §10.2.11 / §16.1.7 `var` hoisting: creates mutable `Initialized(Undefined)` binding in nearest
/// var scope ONLY if `name` is not already bound there.
pub open spec fn spec_declare_var(
    arena: SpecEnvArena,
    start_env: EnvId,
    name: Seq<u16>,
    strict: bool,
) -> SpecEnvArena {
    let var_env = spec_find_var_env(arena, start_env);
    if (var_env.0 as int) >= arena.envs.len() {
        arena
    } else {
        match arena.envs[var_env.0 as int] {
            SpecEnvSlot::Free => arena,
            SpecEnvSlot::Live(rec) => {
                match spec_find_binding(rec.bindings, name) {
                    Some(_) => arena,
                    None => {
                        let new_b = SpecBinding {
                            name,
                            mutable: true,
                            strict,
                            status: SpecBindingStatus::Initialized(SpecVal::Undefined),
                        };
                        let rec2 = SpecEnvRecord {
                            bindings: rec.bindings.push(new_b),
                            ..rec
                        };
                        SpecEnvArena { envs: arena.envs.update(var_env.0 as int, SpecEnvSlot::Live(rec2)) }
                    }
                }
            }
        }
    }
}

pub open spec fn spec_initialize_lexical(
    arena: SpecEnvArena,
    env_id: EnvId,
    name: Seq<u16>,
    val: SpecVal,
) -> SpecEnvArena {
    if (env_id.0 as int) >= arena.envs.len() {
        arena
    } else {
        match arena.envs[env_id.0 as int] {
            SpecEnvSlot::Free => arena,
            SpecEnvSlot::Live(rec) => {
                match spec_find_binding(rec.bindings, name) {
                    Some(idx) => {
                        let old_b = rec.bindings[idx as int];
                        let new_b = SpecBinding {
                            status: SpecBindingStatus::Initialized(val),
                            ..old_b
                        };
                        let rec2 = SpecEnvRecord {
                            bindings: rec.bindings.update(idx as int, new_b),
                            ..rec
                        };
                        SpecEnvArena { envs: arena.envs.update(env_id.0 as int, SpecEnvSlot::Live(rec2)) }
                    }
                    None => spec_bind_initialized(arena, env_id, name, val, true, false),
                }
            }
        }
    }
}

pub open spec fn spec_resolve_binding_loc_steps(
    arena: SpecEnvArena,
    cur: EnvId,
    name: Seq<u16>,
    steps: nat,
) -> Option<(EnvId, nat)>
    decreases steps,
{
    if steps == 0 || (cur.0 as int) >= arena.envs.len() {
        None
    } else {
        match arena.envs[cur.0 as int] {
            SpecEnvSlot::Free => None,
            SpecEnvSlot::Live(rec) => {
                match spec_find_binding(rec.bindings, name) {
                    Some(idx) => Some((cur, idx)),
                    None => match rec.outer {
                        Some(p) => spec_resolve_binding_loc_steps(arena, p, name, (steps - 1) as nat),
                        None => None,
                    },
                }
            }
        }
    }
}

pub open spec fn spec_resolve_binding_loc(
    arena: SpecEnvArena,
    cur: EnvId,
    name: Seq<u16>,
) -> Option<(EnvId, nat)> {
    spec_resolve_binding_loc_steps(arena, cur, name, arena.envs.len())
}

pub proof fn lemma_resolve_binding_loc_steps_valid(
    arena: SpecEnvArena,
    cur: EnvId,
    name: Seq<u16>,
    steps: nat,
)
    ensures
        match spec_resolve_binding_loc_steps(arena, cur, name, steps) {
            Some((eid, idx)) => (eid.0 as int) < arena.envs.len() && match arena.envs[eid.0 as int] {
                SpecEnvSlot::Live(rec) => idx < rec.bindings.len(),
                SpecEnvSlot::Free => false,
            },
            None => true,
        },
    decreases steps,
{
    if steps > 0 && (cur.0 as int) < arena.envs.len() {
        if let SpecEnvSlot::Live(rec) = arena.envs[cur.0 as int] {
            lemma_find_binding_props(rec.bindings, name, 0);
            if spec_find_binding(rec.bindings, name) is None {
                if let Some(p) = rec.outer {
                    lemma_resolve_binding_loc_steps_valid(arena, p, name, (steps - 1) as nat);
                }
            }
        }
    }
}

pub open spec fn spec_get_identifier(
    arena: SpecEnvArena,
    start_env: EnvId,
    name: Seq<u16>,
) -> SpecIdentLookup {
    match spec_resolve_binding_loc(arena, start_env, name) {
        Some((eid, idx)) => {
            match arena.envs[eid.0 as int] {
                SpecEnvSlot::Live(rec) => match rec.bindings[idx as int].status {
                    SpecBindingStatus::Uninitialized => SpecIdentLookup::TdzUninitialized,
                    SpecBindingStatus::Initialized(v) => SpecIdentLookup::Found(v),
                },
                SpecEnvSlot::Free => SpecIdentLookup::Undeclared,
            }
        }
        None => SpecIdentLookup::Undeclared,
    }
}

pub open spec fn spec_set_identifier(
    arena: SpecEnvArena,
    start_env: EnvId,
    name: Seq<u16>,
    val: SpecVal,
    strict: bool,
) -> (SpecEnvArena, IdentAssignOutcome) {
    match spec_resolve_binding_loc(arena, start_env, name) {
        Some((eid, idx)) => {
            match arena.envs[eid.0 as int] {
                SpecEnvSlot::Free => (arena, IdentAssignOutcome::UndeclaredStrict),
                SpecEnvSlot::Live(rec) => {
                    let b = rec.bindings[idx as int];
                    match b.status {
                        SpecBindingStatus::Uninitialized => (arena, IdentAssignOutcome::TdzUninitialized),
                        SpecBindingStatus::Initialized(_) => {
                            if !b.mutable {
                                if b.strict || strict {
                                    (arena, IdentAssignOutcome::ImmutableConst)
                                } else {
                                    (arena, IdentAssignOutcome::Ok)
                                }
                            } else {
                                let b2 = SpecBinding { status: SpecBindingStatus::Initialized(val), ..b };
                                let rec2 = SpecEnvRecord { bindings: rec.bindings.update(idx as int, b2), ..rec };
                                (
                                    SpecEnvArena { envs: arena.envs.update(eid.0 as int, SpecEnvSlot::Live(rec2)) },
                                    IdentAssignOutcome::Ok,
                                )
                            }
                        }
                    }
                }
            }
        }
        None => {
            if strict {
                (arena, IdentAssignOutcome::UndeclaredStrict)
            } else {
                (spec_bind_initialized(arena, EnvId(0), name, val, true, false), IdentAssignOutcome::Ok)
            }
        }
    }
}

pub open spec fn spec_delete_identifier(
    arena: SpecEnvArena,
    start_env: EnvId,
    name: Seq<u16>,
) -> bool {
    match spec_resolve_binding_loc(arena, start_env, name) {
        Some(_) => false,
        None => true,
    }
}

pub open spec fn spec_resolve_this_steps(arena: SpecEnvArena, cur: EnvId, steps: nat) -> SpecVal
    decreases steps,
{
    if steps == 0 || (cur.0 as int) >= arena.envs.len() {
        SpecVal::Undefined
    } else {
        match arena.envs[cur.0 as int] {
            SpecEnvSlot::Free => SpecVal::Undefined,
            SpecEnvSlot::Live(rec) => match rec.this_binding {
                Some(v) => v,
                None => match rec.outer {
                    Some(p) => spec_resolve_this_steps(arena, p, (steps - 1) as nat),
                    None => SpecVal::Undefined,
                },
            },
        }
    }
}

pub open spec fn spec_resolve_this(arena: SpecEnvArena, cur: EnvId) -> SpecVal {
    spec_resolve_this_steps(arena, cur, arena.envs.len())
}

pub open spec fn spec_copy_per_iter_bindings(
    src_bs: Seq<SpecBinding>,
    names: Seq<Seq<u16>>,
    idx: nat,
    acc: Seq<SpecBinding>,
) -> Seq<SpecBinding>
    decreases names.len() - idx,
{
    if idx >= names.len() {
        acc
    } else {
        let nm = names[idx as int];
        let next_acc = match spec_find_binding(src_bs, nm) {
            Some(bidx) => spec_upsert_binding(acc, src_bs[bidx as int]),
            None => acc,
        };
        spec_copy_per_iter_bindings(src_bs, names, idx + 1, next_acc)
    }
}

pub open spec fn spec_clone_per_iter_env(
    arena: SpecEnvArena,
    env_id: EnvId,
    names: Seq<Seq<u16>>,
) -> (SpecEnvArena, EnvId) {
    if names.len() == 0 || (env_id.0 as int) >= arena.envs.len() {
        (arena, env_id)
    } else {
        match arena.envs[env_id.0 as int] {
            SpecEnvSlot::Free => (arena, env_id),
            SpecEnvSlot::Live(src) => {
                let outer = match src.outer {
                    Some(p) => if (p.0 as int) < arena.envs.len() && (arena.envs[p.0 as int] is Live) {
                        p
                    } else {
                        EnvId(0)
                    },
                    None => EnvId(0),
                };
                let (arena1, new_id) = spec_alloc_env(arena, EnvKind::Block, outer, None);
                let copied = spec_copy_per_iter_bindings(src.bindings, names, 0, seq![]);
                match arena1.envs[new_id.0 as int] {
                    SpecEnvSlot::Live(base_rec) => {
                        let rec = SpecEnvRecord { bindings: copied, ..base_rec };
                        (SpecEnvArena { envs: arena1.envs.update(new_id.0 as int, SpecEnvSlot::Live(rec)) }, new_id)
                    }
                    SpecEnvSlot::Free => (arena1, new_id),
                }
            }
        }
    }
}

/// Helper lemma: updating one `Live` slot at `upd_idx` while preserving its `kind` and `outer`
/// and keeping `spec_bindings_unique(new_rec.bindings)` preserves `env_wf`.
proof fn lemma_update_live_slot_preserves_wf(
    old_arena: SpecEnvArena,
    new_arena: SpecEnvArena,
    upd_idx: int,
    old_rec: SpecEnvRecord,
    new_rec: SpecEnvRecord,
)
    requires
        env_wf(old_arena),
        0 <= upd_idx < old_arena.envs.len(),
        old_arena.envs[upd_idx] == SpecEnvSlot::Live(old_rec),
        new_rec.kind == old_rec.kind,
        new_rec.outer == old_rec.outer,
        spec_bindings_unique(new_rec.bindings),
        new_arena.envs =~= old_arena.envs.update(upd_idx, SpecEnvSlot::Live(new_rec)),
    ensures
        env_wf(new_arena),
{
    assert(new_arena.envs.len() == old_arena.envs.len());
    if upd_idx == 0 {
        assert(new_arena.envs[0] == SpecEnvSlot::Live(new_rec));
    } else {
        assert(new_arena.envs[0] == old_arena.envs[0]);
    }
    assert forall|i: int| 1 <= i < new_arena.envs.len() implies match #[trigger] new_arena.envs[i] {
        SpecEnvSlot::Free => true,
        SpecEnvSlot::Live(rec) => {
            spec_bindings_unique(rec.bindings)
            && match rec.outer {
                None => false,
                Some(p) => (p.0 as int) < new_arena.envs.len()
                    && (p.0 as int) != i
                    && (new_arena.envs[p.0 as int] is Live),
            }
        }
    } by {
        let _ = old_arena.envs[i];
        if i == upd_idx {
            if let Some(p) = new_rec.outer {
                assert(old_arena.envs[p.0 as int] is Live);
                if p.0 as int == upd_idx {
                    assert(false);
                } else {
                    assert(new_arena.envs[p.0 as int] == old_arena.envs[p.0 as int]);
                }
            }
        } else {
            if let SpecEnvSlot::Live(rec) = new_arena.envs[i] {
                assert(old_arena.envs[i] == SpecEnvSlot::Live(rec));
                if let Some(p) = rec.outer {
                    if p.0 as int == upd_idx {
                        assert(new_arena.envs[p.0 as int] == SpecEnvSlot::Live(new_rec));
                    } else {
                        assert(new_arena.envs[p.0 as int] == old_arena.envs[p.0 as int]);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Executable `EnvArena` Implementation Proved Equal to Spec + `env_wf`
// ---------------------------------------------------------------------------

pub fn clone_binding_status(st: &BindingStatus) -> (r: BindingStatus)
    ensures r@ == st@,
{
    match st {
        BindingStatus::Uninitialized => BindingStatus::Uninitialized,
        BindingStatus::Initialized(v) => BindingStatus::Initialized(clone_val(v)),
    }
}

pub fn clone_binding(b: &Binding) -> (r: Binding)
    ensures r@ == b@,
{
    Binding {
        name: clone_js_str(&b.name),
        mutable: b.mutable,
        strict: b.strict,
        status: clone_binding_status(&b.status),
    }
}

pub fn clone_env_record(rec: &EnvRecord) -> (r: EnvRecord)
    ensures r@ == rec@,
{
    let n = rec.bindings.len();
    let mut bs: Vec<Binding> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == rec.bindings@.len(),
            bs@.len() == i,
            forall|k: int| 0 <= k < i as int ==> bs@[k]@ == rec.bindings@[k]@,
        decreases n - i,
    {
        bs.push(clone_binding(&rec.bindings[i]));
        i += 1;
    }
    let tb = match &rec.this_binding {
        None => None,
        Some(v) => Some(clone_val(v)),
    };
    let r = EnvRecord {
        kind: rec.kind,
        outer: rec.outer,
        this_binding: tb,
        bindings: bs,
    };
    proof {
        assert(r@.bindings =~= rec@.bindings);
    }
    r
}

fn find_binding_exec(bs: &Vec<Binding>, name: &JsStr) -> (r: Option<usize>)
    ensures
        match r {
            Some(idx) => spec_find_binding(spec_bindings_view(bs@), name@) == Some(idx as nat)
                && idx < bs@.len()
                && bs@[idx as int].name@ == name@,
            None => spec_find_binding(spec_bindings_view(bs@), name@) is None,
        },
{
    let n = bs.len();
    let mut i: usize = 0;
    let ghost sbs = spec_bindings_view(bs@);
    while i < n
        invariant
            i <= n == bs@.len(),
            sbs == spec_bindings_view(bs@),
            spec_find_binding_from(sbs, name@, 0) == spec_find_binding_from(sbs, name@, i as nat),
        decreases n - i,
    {
        if js_str_eq(&bs[i].name, name) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn upsert_binding_exec(bs: &mut Vec<Binding>, b: Binding)
    ensures
        spec_bindings_view(final(bs)@) =~= spec_upsert_binding(spec_bindings_view(old(bs)@), b@),
        spec_bindings_unique(spec_bindings_view(old(bs)@)) ==> spec_bindings_unique(spec_bindings_view(final(bs)@)),
{
    let ghost old_sbs = spec_bindings_view(old(bs)@);
    let ghost sb = b@;
    match find_binding_exec(bs, &b.name) {
        Some(idx) => {
            bs.set(idx, b);
            proof {
                assert(spec_bindings_view(bs@) =~= old_sbs.update(idx as int, sb));
                if spec_bindings_unique(old_sbs) {
                    lemma_upsert_preserves_unique(old_sbs, sb);
                }
            }
        }
        None => {
            bs.push(b);
            proof {
                assert(spec_bindings_view(bs@) =~= old_sbs.push(sb));
                if spec_bindings_unique(old_sbs) {
                    lemma_upsert_preserves_unique(old_sbs, sb);
                }
            }
        }
    }
}

fn find_free_env_exec(envs: &Vec<EnvSlot>) -> (r: Option<usize>)
    requires envs@.len() >= 1,
    ensures
        match r {
            Some(idx) => spec_find_free_env_from(spec_env_slots_view(envs@), 1) == Some(idx as nat)
                && 1 <= idx < envs@.len()
                && (spec_env_slots_view(envs@)[idx as int] is Free),
            None => spec_find_free_env_from(spec_env_slots_view(envs@), 1) is None,
        },
{
    let n = envs.len();
    let mut i: usize = 1;
    let ghost senvs = spec_env_slots_view(envs@);
    while i < n
        invariant
            1 <= i <= n == envs@.len(),
            senvs == spec_env_slots_view(envs@),
            spec_find_free_env_from(senvs, 1) == spec_find_free_env_from(senvs, i as nat),
        decreases n - i,
    {
        proof { assert(senvs[i as int] == envs@[i as int]@); }
        if matches!(&envs[i], EnvSlot::Free) {
            return Some(i);
        }
        i += 1;
    }
    None
}

impl EnvArena {
    pub fn new_global(global_this: Val) -> (r: Self)
        ensures
            r@ == spec_new_global_env(global_this@),
            env_wf(r@),
    {
        let mut envs: Vec<EnvSlot> = Vec::new();
        envs.push(EnvSlot::Live(EnvRecord {
            kind: EnvKind::Global,
            outer: None,
            this_binding: Some(global_this),
            bindings: Vec::new(),
        }));
        let r = EnvArena { envs };
        proof {
            if let SpecEnvSlot::Live(rec) = r@.envs[0] {
                assert(rec.bindings =~= seq![]);
            }
            assert(r@.envs =~= spec_new_global_env(global_this@).envs);
        }
        r
    }

    pub fn alloc_env(&mut self, kind: EnvKind, outer: EnvId, this_binding: Option<Val>) -> (id: EnvId)
        ensures
            (final(self)@, id) == spec_alloc_env(old(self)@, kind, outer, spec_opt_val_view(&this_binding)),
            (id.0 as int) < final(self)@.envs.len(),
            final(self)@.envs[id.0 as int] is Live,
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        if self.envs.len() == 0 {
            *self = EnvArena::new_global(Val::Undefined);
            return EnvId(0);
        }
        let ghost old_view = old(self)@;
        let outer_live = if outer.0 < self.envs.len() {
            proof { assert(old_view.envs[outer.0 as int] == self.envs@[outer.0 as int]@); }
            matches!(&self.envs[outer.0], EnvSlot::Live(_))
        } else {
            false
        };
        let safe_outer = if outer_live { outer } else { EnvId(0) };
        let safe_kind = match kind {
            EnvKind::Global => EnvKind::Block,
            other => other,
        };
        let ghost stb = spec_opt_val_view(&this_binding);
        let new_rec = EnvRecord {
            kind: safe_kind,
            outer: Some(safe_outer),
            this_binding,
            bindings: Vec::new(),
        };
        proof {
            assert(new_rec@.bindings =~= seq![]);
            assert(spec_bindings_unique(new_rec@.bindings));
        }
        match find_free_env_exec(&self.envs) {
            Some(idx) => {
                self.envs.set(idx, EnvSlot::Live(new_rec));
                let id = EnvId(idx);
                proof {
                    let (sarena, sid) = spec_alloc_env(old_view, kind, outer, stb);
                    assert(id == sid);
                    assert(self@.envs =~= sarena.envs);
                    if env_wf(old_view) {
                        assert(old_view.envs[safe_outer.0 as int] is Live);
                        assert(old_view.envs[idx as int] is Free);
                        assert(safe_outer.0 != idx);
                        assert(self@.envs[0] == old_view.envs[0]);
                        assert forall|i: int| 1 <= i < self@.envs.len() implies match #[trigger] self@.envs[i] {
                            SpecEnvSlot::Free => true,
                            SpecEnvSlot::Live(rec) => {
                                spec_bindings_unique(rec.bindings)
                                && match rec.outer {
                                    None => false,
                                    Some(p) => (p.0 as int) < self@.envs.len()
                                        && (p.0 as int) != i
                                        && (self@.envs[p.0 as int] is Live),
                                }
                            }
                        } by {
                            let _ = old_view.envs[i];
                            if i == idx as int {
                                assert(self@.envs[safe_outer.0 as int] == old_view.envs[safe_outer.0 as int]);
                            } else {
                                assert(self@.envs[i] == old_view.envs[i]);
                                if let SpecEnvSlot::Live(rec) = self@.envs[i] {
                                    if let Some(p) = rec.outer {
                                        if p.0 as int != idx as int {
                                            assert(self@.envs[p.0 as int] == old_view.envs[p.0 as int]);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                id
            }
            None => {
                let id = EnvId(self.envs.len());
                self.envs.push(EnvSlot::Live(new_rec));
                proof {
                    let (sarena, sid) = spec_alloc_env(old_view, kind, outer, stb);
                    assert(id == sid);
                    assert(self@.envs =~= sarena.envs);
                    if env_wf(old_view) {
                        assert(old_view.envs[safe_outer.0 as int] is Live);
                        assert((safe_outer.0 as int) < old_view.envs.len());
                        assert(self@.envs[0] == old_view.envs[0]);
                        assert forall|i: int| 1 <= i < self@.envs.len() implies match #[trigger] self@.envs[i] {
                            SpecEnvSlot::Free => true,
                            SpecEnvSlot::Live(rec) => {
                                spec_bindings_unique(rec.bindings)
                                && match rec.outer {
                                    None => false,
                                    Some(p) => (p.0 as int) < self@.envs.len()
                                        && (p.0 as int) != i
                                        && (self@.envs[p.0 as int] is Live),
                                }
                            }
                        } by {
                            if i < old_view.envs.len() {
                                assert(self@.envs[i] == old_view.envs[i]);
                                if let SpecEnvSlot::Live(rec) = self@.envs[i] {
                                    if let Some(p) = rec.outer {
                                        assert(self@.envs[p.0 as int] == old_view.envs[p.0 as int]);
                                    }
                                }
                            } else {
                                assert(self@.envs[safe_outer.0 as int] == old_view.envs[safe_outer.0 as int]);
                            }
                        }
                    }
                }
                id
            }
        }
    }

    /// Reclaim all unmarked environment records (`i >= 1` with `!marks[i]`) to `EnvSlot::Free`.
    pub fn sweep_unmarked(&mut self, marks: &Vec<bool>)
        requires
            marks@.len() == old(self)@.envs.len(),
            forall|i: int| 1 <= i < old(self)@.envs.len() && marks@[i] ==> match #[trigger] old(self)@.envs[i] {
                SpecEnvSlot::Live(rec) => match rec.outer {
                    Some(p) => (p.0 as int) == 0 || ((p.0 as int) < marks@.len() ==> marks@[p.0 as int]),
                    None => true,
                },
                SpecEnvSlot::Free => true,
            },
        ensures
            final(self)@ == spec_sweep_envs(old(self)@, marks@),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        let n = self.envs.len();
        if n <= 1 {
            proof {
                assert(self@.envs =~= spec_sweep_envs(old(self)@, marks@).envs);
            }
            return;
        }
        let ghost old_view = old(self)@;
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n == self.envs@.len(),
                n == old_view.envs.len() == marks@.len(),
                self@.envs[0] == old_view.envs[0],
                forall|k: int| 1 <= k < i as int ==> #[trigger] self@.envs[k] == (if marks@[k] { old_view.envs[k] } else { SpecEnvSlot::Free }),
                forall|k: int| i as int <= k < n as int ==> #[trigger] self@.envs[k] == old_view.envs[k],
            decreases n - i,
        {
            let ghost before_i = self@;
            if !marks[i] {
                self.envs.set(i, EnvSlot::Free);
            }
            proof {
                assert(self@.envs[0] == before_i.envs[0]);
                assert forall|k: int| 1 <= k <= i as int implies #[trigger] self@.envs[k] == (if marks@[k] { old_view.envs[k] } else { SpecEnvSlot::Free }) by {
                    if k < i as int {
                        assert(self@.envs[k] == before_i.envs[k]);
                    } else if marks@[i as int] {
                        assert(self@.envs[i as int] == before_i.envs[i as int]);
                    } else {
                        assert(self@.envs[i as int] == SpecEnvSlot::Free);
                    }
                }
                assert forall|k: int| (i + 1) as int <= k < n as int implies #[trigger] self@.envs[k] == old_view.envs[k] by {
                    assert(self@.envs[k] == before_i.envs[k]);
                }
            }
            i += 1;
        }
        proof {
            assert(self@.envs =~= spec_sweep_envs(old_view, marks@).envs);
            if env_wf(old_view) {
                assert forall|k: int| 1 <= k < self@.envs.len() implies match #[trigger] self@.envs[k] {
                    SpecEnvSlot::Free => true,
                    SpecEnvSlot::Live(rec) => {
                        spec_bindings_unique(rec.bindings)
                        && match rec.outer {
                            None => false,
                            Some(p) => (p.0 as int) < self@.envs.len()
                                && (p.0 as int) != k
                                && (self@.envs[p.0 as int] is Live),
                        }
                    }
                } by {
                    if marks@[k] {
                        assert(self@.envs[k] == old_view.envs[k]);
                        let _ = old_view.envs[k];
                        if let SpecEnvSlot::Live(rec) = old_view.envs[k] {
                            if let Some(p) = rec.outer {
                                assert(old_view.envs[p.0 as int] is Live);
                                if p.0 == 0 {
                                    assert(self@.envs[0] == old_view.envs[0]);
                                } else {
                                    assert(marks@[p.0 as int]);
                                    assert(self@.envs[p.0 as int] == old_view.envs[p.0 as int]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn declare_tdz(&mut self, env_id: EnvId, name: JsStr, mutable: bool, strict: bool)
        ensures
            final(self)@ == spec_declare_tdz(old(self)@, env_id, name@, mutable, strict),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        if env_id.0 >= self.envs.len() {
            return;
        }
        let ghost old_view = old(self)@;
        let ghost nm = name@;
        proof { assert(old_view.envs[env_id.0 as int] == self.envs@[env_id.0 as int]@); }
        let mut rec = match &self.envs[env_id.0] {
            EnvSlot::Free => return,
            EnvSlot::Live(r) => clone_env_record(r),
        };
        let ghost old_rec = rec@;
        let new_b = Binding {
            name,
            mutable,
            strict,
            status: BindingStatus::Uninitialized,
        };
        upsert_binding_exec(&mut rec.bindings, new_b);
        let ghost new_rec = rec@;
        self.envs.set(env_id.0, EnvSlot::Live(rec));
        proof {
            assert(self@.envs =~= spec_declare_tdz(old_view, env_id, nm, mutable, strict).envs);
            if env_wf(old_view) {
                assert(spec_bindings_unique(old_rec.bindings)) by {
                    if env_id.0 > 0 { let _ = old_view.envs[env_id.0 as int]; }
                };
                lemma_update_live_slot_preserves_wf(old_view, self@, env_id.0 as int, old_rec, new_rec);
            }
        }
    }

    pub fn bind_initialized(&mut self, env_id: EnvId, name: JsStr, val: Val, mutable: bool, strict: bool)
        ensures
            final(self)@ == spec_bind_initialized(old(self)@, env_id, name@, val@, mutable, strict),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        if env_id.0 >= self.envs.len() {
            return;
        }
        let ghost old_view = old(self)@;
        let ghost nm = name@;
        let ghost sv = val@;
        proof { assert(old_view.envs[env_id.0 as int] == self.envs@[env_id.0 as int]@); }
        let mut rec = match &self.envs[env_id.0] {
            EnvSlot::Free => return,
            EnvSlot::Live(r) => clone_env_record(r),
        };
        let ghost old_rec = rec@;
        let new_b = Binding {
            name,
            mutable,
            strict,
            status: BindingStatus::Initialized(val),
        };
        upsert_binding_exec(&mut rec.bindings, new_b);
        let ghost new_rec = rec@;
        self.envs.set(env_id.0, EnvSlot::Live(rec));
        proof {
            assert(self@.envs =~= spec_bind_initialized(old_view, env_id, nm, sv, mutable, strict).envs);
            if env_wf(old_view) {
                assert(spec_bindings_unique(old_rec.bindings)) by {
                    if env_id.0 > 0 { let _ = old_view.envs[env_id.0 as int]; }
                };
                lemma_update_live_slot_preserves_wf(old_view, self@, env_id.0 as int, old_rec, new_rec);
            }
        }
    }

    pub fn find_var_env(&self, cur: EnvId) -> (r: EnvId)
        ensures r == spec_find_var_env(self@, cur),
    {
        let mut steps = self.envs.len();
        let mut c = cur;
        let ghost sarena = self@;
        while steps > 0
            invariant
                steps <= self.envs@.len(),
                sarena == self@,
                spec_find_var_env(sarena, cur) == spec_find_var_env_steps(sarena, c, steps as nat),
            decreases steps,
        {
            if c.0 >= self.envs.len() {
                return EnvId(0);
            }
            proof { assert(sarena.envs[c.0 as int] == self.envs@[c.0 as int]@); }
            match &self.envs[c.0] {
                EnvSlot::Free => return EnvId(0),
                EnvSlot::Live(rec) => match rec.kind {
                    EnvKind::Global | EnvKind::Function => return c,
                    _ => match rec.outer {
                        Some(p) => {
                            c = p;
                            steps -= 1;
                        }
                        None => return EnvId(0),
                    },
                },
            }
        }
        EnvId(0)
    }

    pub fn declare_var(&mut self, start_env: EnvId, name: JsStr, strict: bool)
        ensures
            final(self)@ == spec_declare_var(old(self)@, start_env, name@, strict),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        let var_env = self.find_var_env(start_env);
        if var_env.0 >= self.envs.len() {
            return;
        }
        let ghost old_view = old(self)@;
        let ghost nm = name@;
        proof { assert(old_view.envs[var_env.0 as int] == self.envs@[var_env.0 as int]@); }
        let mut rec = match &self.envs[var_env.0] {
            EnvSlot::Free => return,
            EnvSlot::Live(r) => {
                if find_binding_exec(&r.bindings, &name).is_some() {
                    return;
                }
                clone_env_record(r)
            }
        };
        let ghost old_rec = rec@;
        proof {
            lemma_find_binding_props(old_rec.bindings, nm, 0);
        }
        rec.bindings.push(Binding {
            name,
            mutable: true,
            strict,
            status: BindingStatus::Initialized(Val::Undefined),
        });
        let ghost new_rec = rec@;
        proof {
            let old_bs = old_rec.bindings;
            let new_bs = new_rec.bindings;
            assert(new_bs =~= old_bs.push(SpecBinding {
                name: nm,
                mutable: true,
                strict,
                status: SpecBindingStatus::Initialized(SpecVal::Undefined),
            }));
            if env_wf(old_view) {
                assert(spec_bindings_unique(old_bs)) by {
                    if var_env.0 > 0 { let _ = old_view.envs[var_env.0 as int]; }
                };
                assert forall|a: int, b: int| 0 <= a < b < new_bs.len() implies new_bs[a].name != new_bs[b].name by {
                    if b == old_bs.len() {
                        assert(old_bs[a].name != nm);
                    }
                }
            }
        }
        self.envs.set(var_env.0, EnvSlot::Live(rec));
        proof {
            assert(self@.envs =~= spec_declare_var(old_view, start_env, nm, strict).envs);
            if env_wf(old_view) {
                lemma_update_live_slot_preserves_wf(old_view, self@, var_env.0 as int, old_rec, new_rec);
            }
        }
    }

    pub fn initialize_lexical(&mut self, env_id: EnvId, name: &JsStr, val: Val)
        ensures
            final(self)@ == spec_initialize_lexical(old(self)@, env_id, name@, val@),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        if env_id.0 >= self.envs.len() {
            return;
        }
        let ghost old_view = old(self)@;
        proof { assert(old_view.envs[env_id.0 as int] == self.envs@[env_id.0 as int]@); }
        let found_opt = match &self.envs[env_id.0] {
            EnvSlot::Free => return,
            EnvSlot::Live(r) => find_binding_exec(&r.bindings, name),
        };
        match found_opt {
            Some(idx) => {
                let ghost sv = val@;
                let mut rec = match &self.envs[env_id.0] {
                    EnvSlot::Live(r) => clone_env_record(r),
                    EnvSlot::Free => return,
                };
                let ghost old_rec = rec@;
                let old_b = clone_binding(&rec.bindings[idx]);
                let new_b = Binding {
                    name: old_b.name,
                    mutable: old_b.mutable,
                    strict: old_b.strict,
                    status: BindingStatus::Initialized(val),
                };
                rec.bindings.set(idx, new_b);
                let ghost new_rec = rec@;
                self.envs.set(env_id.0, EnvSlot::Live(rec));
                proof {
                    let old_bs = old_rec.bindings;
                    let new_bs = new_rec.bindings;
                    assert(new_bs =~= old_bs.update(idx as int, SpecBinding {
                        status: SpecBindingStatus::Initialized(sv),
                        ..old_bs[idx as int]
                    }));
                    assert(self@.envs =~= spec_initialize_lexical(old_view, env_id, name@, sv).envs);
                    if env_wf(old_view) {
                        assert(spec_bindings_unique(old_bs)) by {
                            if env_id.0 > 0 { let _ = old_view.envs[env_id.0 as int]; }
                        };
                        assert forall|a: int, b: int| 0 <= a < b < new_bs.len() implies new_bs[a].name != new_bs[b].name by {
                            assert(new_bs[a].name == old_bs[a].name);
                            assert(new_bs[b].name == old_bs[b].name);
                        }
                        lemma_update_live_slot_preserves_wf(old_view, self@, env_id.0 as int, old_rec, new_rec);
                    }
                }
            }
            None => {
                self.bind_initialized(env_id, clone_js_str(name), val, true, false);
            }
        }
    }

    pub fn resolve_binding_loc(&self, cur: EnvId, name: &JsStr) -> (r: Option<(EnvId, usize)>)
        ensures
            match r {
                Some((eid, idx)) =>
                    spec_resolve_binding_loc(self@, cur, name@) == Some((eid, idx as nat))
                    && (eid.0 as int) < self@.envs.len()
                    && match self@.envs[eid.0 as int] {
                        SpecEnvSlot::Live(rec) => (idx as int) < rec.bindings.len(),
                        SpecEnvSlot::Free => false,
                    },
                None => spec_resolve_binding_loc(self@, cur, name@) is None,
            },
    {
        let mut steps = self.envs.len();
        let mut c = cur;
        let ghost sarena = self@;
        while steps > 0
            invariant
                steps <= self.envs@.len(),
                sarena == self@,
                spec_resolve_binding_loc(sarena, cur, name@)
                    == spec_resolve_binding_loc_steps(sarena, c, name@, steps as nat),
            decreases steps,
        {
            if c.0 >= self.envs.len() {
                return None;
            }
            proof { assert(sarena.envs[c.0 as int] == self.envs@[c.0 as int]@); }
            match &self.envs[c.0] {
                EnvSlot::Free => return None,
                EnvSlot::Live(rec) => match find_binding_exec(&rec.bindings, name) {
                    Some(idx) => return Some((c, idx)),
                    None => match rec.outer {
                        Some(p) => {
                            c = p;
                            steps -= 1;
                        }
                        None => return None,
                    },
                },
            }
        }
        None
    }

    pub fn get_identifier(&self, start_env: EnvId, name: &JsStr) -> (r: IdentLookup)
        ensures r@ == spec_get_identifier(self@, start_env, name@),
    {
        match self.resolve_binding_loc(start_env, name) {
            Some((eid, idx)) => {
                proof { assert(self@.envs[eid.0 as int] == self.envs@[eid.0 as int]@); }
                match &self.envs[eid.0] {
                    EnvSlot::Live(rec) => match &rec.bindings[idx].status {
                        BindingStatus::Uninitialized => IdentLookup::TdzUninitialized,
                        BindingStatus::Initialized(v) => IdentLookup::Found(clone_val(v)),
                    },
                    EnvSlot::Free => IdentLookup::Undeclared,
                }
            }
            None => IdentLookup::Undeclared,
        }
    }

    pub fn set_identifier(
        &mut self,
        start_env: EnvId,
        name: &JsStr,
        val: Val,
        strict: bool,
    ) -> (out: IdentAssignOutcome)
        ensures
            (final(self)@, out) == spec_set_identifier(old(self)@, start_env, name@, val@, strict),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        match self.resolve_binding_loc(start_env, name) {
            Some((eid, idx)) => {
                let ghost old_view = old(self)@;
                proof { assert(old_view.envs[eid.0 as int] == self.envs@[eid.0 as int]@); }
                let (b_mutable, b_strict, is_uninit) = match &self.envs[eid.0] {
                    EnvSlot::Free => return IdentAssignOutcome::UndeclaredStrict,
                    EnvSlot::Live(r) => {
                        let iu = match r.bindings[idx].status {
                            BindingStatus::Uninitialized => true,
                            BindingStatus::Initialized(_) => false,
                        };
                        (r.bindings[idx].mutable, r.bindings[idx].strict, iu)
                    }
                };
                if is_uninit {
                    return IdentAssignOutcome::TdzUninitialized;
                }
                if !b_mutable {
                    if b_strict || strict {
                        return IdentAssignOutcome::ImmutableConst;
                    } else {
                        return IdentAssignOutcome::Ok;
                    }
                }
                let ghost sv = val@;
                let mut rec = match &self.envs[eid.0] {
                    EnvSlot::Live(r) => clone_env_record(r),
                    EnvSlot::Free => return IdentAssignOutcome::UndeclaredStrict,
                };
                let ghost old_rec = rec@;
                let old_b = clone_binding(&rec.bindings[idx]);
                rec.bindings.set(idx, Binding {
                    name: old_b.name,
                    mutable: old_b.mutable,
                    strict: old_b.strict,
                    status: BindingStatus::Initialized(val),
                });
                let ghost new_rec = rec@;
                self.envs.set(eid.0, EnvSlot::Live(rec));
                proof {
                    let old_bs = old_rec.bindings;
                    let new_bs = new_rec.bindings;
                    assert(new_bs =~= old_bs.update(idx as int, SpecBinding {
                        status: SpecBindingStatus::Initialized(sv),
                        ..old_bs[idx as int]
                    }));
                    assert(self@.envs =~= spec_set_identifier(old_view, start_env, name@, sv, strict).0.envs);
                    if env_wf(old_view) {
                        assert(spec_bindings_unique(old_bs)) by {
                            if eid.0 > 0 { let _ = old_view.envs[eid.0 as int]; }
                        };
                        assert forall|a: int, b: int| 0 <= a < b < new_bs.len() implies new_bs[a].name != new_bs[b].name by {
                            assert(new_bs[a].name == old_bs[a].name);
                            assert(new_bs[b].name == old_bs[b].name);
                        }
                        lemma_update_live_slot_preserves_wf(old_view, self@, eid.0 as int, old_rec, new_rec);
                    }
                }
                IdentAssignOutcome::Ok
            }
            None => {
                if strict {
                    IdentAssignOutcome::UndeclaredStrict
                } else {
                    self.bind_initialized(EnvId(0), clone_js_str(name), val, true, false);
                    IdentAssignOutcome::Ok
                }
            }
        }
    }

    pub fn delete_identifier(&self, start_env: EnvId, name: &JsStr) -> (r: bool)
        ensures r == spec_delete_identifier(self@, start_env, name@),
    {
        self.resolve_binding_loc(start_env, name).is_none()
    }

    pub fn resolve_this(&self, cur: EnvId) -> (r: Val)
        ensures r@ == spec_resolve_this(self@, cur),
    {
        let mut steps = self.envs.len();
        let mut c = cur;
        let ghost sarena = self@;
        while steps > 0
            invariant
                steps <= self.envs@.len(),
                sarena == self@,
                spec_resolve_this(sarena, cur) == spec_resolve_this_steps(sarena, c, steps as nat),
            decreases steps,
        {
            if c.0 >= self.envs.len() {
                return Val::Undefined;
            }
            proof { assert(sarena.envs[c.0 as int] == self.envs@[c.0 as int]@); }
            match &self.envs[c.0] {
                EnvSlot::Free => return Val::Undefined,
                EnvSlot::Live(rec) => match &rec.this_binding {
                    Some(v) => return clone_val(v),
                    None => match rec.outer {
                        Some(p) => {
                            c = p;
                            steps -= 1;
                        }
                        None => return Val::Undefined,
                    },
                },
            }
        }
        Val::Undefined
    }

    pub fn clone_per_iter_env(&mut self, env_id: EnvId, names: &Vec<JsStr>) -> (r: EnvId)
        ensures
            (final(self)@, r) == spec_clone_per_iter_env(old(self)@, env_id, crate::ast::spec_str_seq_view(names@)),
            env_wf(old(self)@) ==> env_wf(final(self)@),
    {
        if names.len() == 0 || env_id.0 >= self.envs.len() {
            return env_id;
        }
        let ghost old_view = old(self)@;
        let ghost snames = crate::ast::spec_str_seq_view(names@);
        proof { assert(old_view.envs[env_id.0 as int] == self.envs@[env_id.0 as int]@); }
        let src = match &self.envs[env_id.0] {
            EnvSlot::Free => return env_id,
            EnvSlot::Live(r) => clone_env_record(r),
        };
        let outer = match src.outer {
            Some(p) => {
                if p.0 < self.envs.len() {
                    proof { assert(old_view.envs[p.0 as int] == self.envs@[p.0 as int]@); }
                    if matches!(&self.envs[p.0], EnvSlot::Live(_)) { p } else { EnvId(0) }
                } else {
                    EnvId(0)
                }
            }
            None => EnvId(0),
        };
        let new_id = self.alloc_env(EnvKind::Block, outer, None);
        let mut copied: Vec<Binding> = Vec::new();
        let n = names.len();
        let mut i: usize = 0;
        proof {
            assert(spec_bindings_view(copied@) =~= Seq::<SpecBinding>::empty());
            assert(spec_bindings_unique(spec_bindings_view(copied@)));
        }
        while i < n
            invariant
                i <= n == names@.len(),
                snames == crate::ast::spec_str_seq_view(names@),
                (new_id.0 as int) < self@.envs.len(),
                self@.envs[new_id.0 as int] is Live,
                spec_bindings_unique(spec_bindings_view(copied@)),
                spec_copy_per_iter_bindings(src@.bindings, snames, 0, seq![])
                    == spec_copy_per_iter_bindings(src@.bindings, snames, i as nat, spec_bindings_view(copied@)),
            decreases n - i,
        {
            if let Some(bidx) = find_binding_exec(&src.bindings, &names[i]) {
                upsert_binding_exec(&mut copied, clone_binding(&src.bindings[bidx]));
            }
            i += 1;
        }
        let ghost after_alloc = self@;
        proof { assert(after_alloc.envs[new_id.0 as int] == self.envs@[new_id.0 as int]@); }
        let mut new_rec = match &self.envs[new_id.0] {
            EnvSlot::Live(r) => clone_env_record(r),
            EnvSlot::Free => return new_id,
        };
        let ghost base_rec = new_rec@;
        new_rec.bindings = copied;
        let ghost upd_rec = new_rec@;
        self.envs.set(new_id.0, EnvSlot::Live(new_rec));
        proof {
            assert(self@.envs =~= spec_clone_per_iter_env(old_view, env_id, snames).0.envs);
            if env_wf(old_view) {
                assert(env_wf(after_alloc));
                lemma_update_live_slot_preserves_wf(after_alloc, self@, new_id.0 as int, base_rec, upd_rec);
            }
        }
        new_id
    }
}

} // verus!
