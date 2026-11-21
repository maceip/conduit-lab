//! ECMA-262 Static Semantics: Early Errors (`spec_check_early_errors` + verified `check_early_errors`).
//!
//! Enforces:
//! - Duplicate `LexicallyDeclaredNames` in any Script, FunctionBody, Block, Switch, or For header;
//! - Collisions between `LexicallyDeclaredNames` and `VarDeclaredNames` (or FormalParameters / CatchParameter);
//! - Duplicate formal parameter names in strict mode, arrow functions, concise methods, and non-simple parameter lists;
//! - `"use strict"` directive inside functions with non-simple parameter lists (§15.2.1);
//! - Strict-mode reserved words (`implements`, `interface`, `let`, `package`, `private`, `protected`,
//!   `public`, `static`, `yield`), strict `eval`/`arguments` bindings & assignments, strict `with`,
//!   strict `delete <ident>`, and strict legacy octal numeric/string literals;
//! - Invalid `AssignmentTargetType` on LHS of `=`, compound assignments, `++`/`--`, and `for-in`/`for-of`;
//! - Unbound or duplicate labels, non-iteration `continue label`, `break`/`continue` outside iteration/switch,
//!   `return` and `new.target` outside functions, `await` outside async (or in formal params), and
//!   `yield` outside generators (or in formal params).
use crate::ast::*;
use crate::token::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Byte-Name Equality, Cloning, & Duplicate / Collision Set Primitives (Spec + Exec + Theorems)
// ---------------------------------------------------------------------------------------

pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
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
            n == a@.len() && n == b@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
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

pub fn clone_bytes(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == s@,
{
    let n = s.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(out@ =~= s@.subrange(0, 0));
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(s[i]);
        i = i + 1;
        proof {
            assert(out@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    out
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NameSpan {
    pub name: Vec<u8>,
    pub span: Span,
}

pub struct SpecNameSpan {
    pub name: Seq<u8>,
    pub span: Span,
}

impl View for NameSpan {
    type V = SpecNameSpan;

    open spec fn view(&self) -> SpecNameSpan {
        SpecNameSpan { name: self.name@, span: self.span }
    }
}

pub open spec fn spec_ns_view(s: Seq<NameSpan>) -> Seq<SpecNameSpan> {
    s.map_values(|x: NameSpan| x@)
}

pub proof fn lemma_ns_push_view(s: Seq<NameSpan>, x: NameSpan)
    ensures
        spec_ns_view(s.push(x)) == spec_ns_view(s).push(x@),
{
    assert(spec_ns_view(s.push(x)) =~= spec_ns_view(s).push(x@));
}

pub fn make_name_span(ident: &Ident) -> (ns: NameSpan)
    ensures
        ns@ == (SpecNameSpan { name: ident.name@, span: ident.span }),
{
    NameSpan { name: clone_bytes(ident.name.as_slice()), span: ident.span }
}

pub open spec fn spec_name_occurs_before(
    names: Seq<SpecNameSpan>,
    limit: nat,
    target: Seq<u8>,
) -> bool
    decreases limit,
{
    if limit == 0 || limit > names.len() {
        false
    } else {
        names[(limit - 1) as int].name == target
            || spec_name_occurs_before(names, (limit - 1) as nat, target)
    }
}

pub proof fn lemma_name_occurs_before_iff(
    names: Seq<SpecNameSpan>,
    limit: nat,
    target: Seq<u8>,
)
    requires
        limit <= names.len(),
    ensures
        spec_name_occurs_before(names, limit, target)
            <==> exists|i: int| 0 <= i < limit && (#[trigger] names[i]).name == target,
    decreases limit,
{
    if limit > 0 {
        lemma_name_occurs_before_iff(names, (limit - 1) as nat, target);
        if exists|i: int| 0 <= i < limit && (#[trigger] names[i]).name == target {
            let w = choose|i: int| 0 <= i < limit && (#[trigger] names[i]).name == target;
            if w < limit - 1 {
                assert(names[w].name == target);
            }
        }
    }
}

pub fn name_occurs_before(names: &[NameSpan], limit: usize, target: &[u8]) -> (r: bool)
    requires
        limit <= names@.len(),
    ensures
        r == spec_name_occurs_before(spec_ns_view(names@), limit as nat, target@),
{
    let mut k = limit;
    while k > 0
        invariant
            k <= limit && limit <= names@.len(),
            spec_name_occurs_before(spec_ns_view(names@), limit as nat, target@)
                == spec_name_occurs_before(spec_ns_view(names@), k as nat, target@),
        decreases k,
    {
        let idx = k - 1;
        if bytes_eq(names[idx].name.as_slice(), target) {
            return true;
        }
        k = idx;
    }
    false
}

pub open spec fn spec_find_duplicate_from(names: Seq<SpecNameSpan>, idx: nat) -> Option<Span>
    decreases names.len() - idx,
{
    if idx >= names.len() {
        None
    } else if spec_name_occurs_before(names, idx, names[idx as int].name) {
        Some(names[idx as int].span)
    } else {
        spec_find_duplicate_from(names, idx + 1)
    }
}

pub open spec fn spec_find_duplicate_name(names: Seq<SpecNameSpan>) -> Option<Span> {
    spec_find_duplicate_from(names, 0)
}

/// Soundness & completeness theorem for duplicate-name detection:
/// `spec_find_duplicate_name(names)` returns `None` iff all elements have pairwise distinct names.
pub proof fn lemma_no_duplicate_iff_pairwise_distinct(names: Seq<SpecNameSpan>)
    ensures
        spec_find_duplicate_name(names) is None
            <==> forall|i: int, j: int|
                0 <= i < j < names.len() ==> (#[trigger] names[i]).name != (#[trigger] names[j]).name,
{
    lemma_find_duplicate_from_iff(names, 0);
}

proof fn lemma_find_duplicate_from_iff(names: Seq<SpecNameSpan>, idx: nat)
    requires
        idx <= names.len(),
    ensures
        spec_find_duplicate_from(names, idx) is None
            <==> forall|i: int, j: int|
                idx <= j < names.len() && 0 <= i < j
                    ==> (#[trigger] names[i]).name != (#[trigger] names[j]).name,
    decreases names.len() - idx,
{
    if idx < names.len() {
        lemma_name_occurs_before_iff(names, idx, names[idx as int].name);
        lemma_find_duplicate_from_iff(names, idx + 1);
        if spec_find_duplicate_from(names, idx) is None {
            assert forall|i: int, j: int|
                idx <= j < names.len() && 0 <= i < j
                implies (#[trigger] names[i]).name != (#[trigger] names[j]).name by {
                if j == idx && names[i].name == names[idx as int].name {
                    assert(exists|w: int| 0 <= w < idx && (#[trigger] names[w]).name == names[idx as int].name);
                    assert(false);
                }
            }
        }
        if forall|i: int, j: int|
            idx <= j < names.len() && 0 <= i < j
                ==> (#[trigger] names[i]).name != (#[trigger] names[j]).name
        {
            if spec_name_occurs_before(names, idx, names[idx as int].name) {
                let w = choose|w: int| 0 <= w < idx && (#[trigger] names[w]).name == names[idx as int].name;
                assert(names[w].name != names[idx as int].name);
                assert(false);
            }
        }
    }
}

pub fn find_duplicate_name(names: &[NameSpan]) -> (r: Option<Span>)
    ensures
        r == spec_find_duplicate_name(spec_ns_view(names@)),
{
    let n = names.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == names@.len(),
            spec_find_duplicate_from(spec_ns_view(names@), idx as nat)
                == spec_find_duplicate_from(spec_ns_view(names@), 0),
        decreases n - idx,
    {
        if name_occurs_before(names, idx, names[idx].name.as_slice()) {
            return Some(names[idx].span);
        }
        idx = idx + 1;
    }
    None
}

pub open spec fn spec_find_collision_from(
    a: Seq<SpecNameSpan>,
    b: Seq<SpecNameSpan>,
    bi: nat,
) -> Option<Span>
    decreases b.len() - bi,
{
    if bi >= b.len() {
        None
    } else if spec_name_occurs_before(a, a.len(), b[bi as int].name) {
        Some(b[bi as int].span)
    } else {
        spec_find_collision_from(a, b, bi + 1)
    }
}

pub open spec fn spec_find_collision(a: Seq<SpecNameSpan>, b: Seq<SpecNameSpan>) -> Option<Span> {
    spec_find_collision_from(a, b, 0)
}

/// Soundness & completeness theorem for lexical/var collision detection:
/// `spec_find_collision(a, b)` returns `None` iff `a` and `b` are disjoint in binding names.
pub proof fn lemma_no_collision_iff_disjoint(a: Seq<SpecNameSpan>, b: Seq<SpecNameSpan>)
    ensures
        spec_find_collision(a, b) is None
            <==> forall|i: int, j: int|
                0 <= i < a.len() && 0 <= j < b.len()
                    ==> (#[trigger] a[i]).name != (#[trigger] b[j]).name,
{
    lemma_find_collision_from_iff(a, b, 0);
}

proof fn lemma_find_collision_from_iff(a: Seq<SpecNameSpan>, b: Seq<SpecNameSpan>, bi: nat)
    requires
        bi <= b.len(),
    ensures
        spec_find_collision_from(a, b, bi) is None
            <==> forall|i: int, j: int|
                0 <= i < a.len() && bi <= j < b.len()
                    ==> (#[trigger] a[i]).name != (#[trigger] b[j]).name,
    decreases b.len() - bi,
{
    if bi < b.len() {
        lemma_name_occurs_before_iff(a, a.len(), b[bi as int].name);
        lemma_find_collision_from_iff(a, b, bi + 1);
        if spec_find_collision_from(a, b, bi) is None {
            assert forall|i: int, j: int|
                0 <= i < a.len() && bi <= j < b.len()
                implies (#[trigger] a[i]).name != (#[trigger] b[j]).name by {
                if j == bi && a[i].name == b[bi as int].name {
                    assert(exists|w: int| 0 <= w < a.len() && (#[trigger] a[w]).name == b[bi as int].name);
                    assert(false);
                }
            }
        }
        if forall|i: int, j: int|
            0 <= i < a.len() && bi <= j < b.len()
                ==> (#[trigger] a[i]).name != (#[trigger] b[j]).name
        {
            if spec_name_occurs_before(a, a.len(), b[bi as int].name) {
                let w = choose|w: int| 0 <= w < a.len() && (#[trigger] a[w]).name == b[bi as int].name;
                assert(a[w].name != b[bi as int].name);
                assert(false);
            }
        }
    }
}

pub fn find_collision(a: &[NameSpan], b: &[NameSpan]) -> (r: Option<Span>)
    ensures
        r == spec_find_collision(spec_ns_view(a@), spec_ns_view(b@)),
{
    let nb = b.len();
    let na = a.len();
    let mut bi: usize = 0;
    while bi < nb
        invariant
            bi <= nb,
            nb == b@.len(),
            na == a@.len(),
            spec_find_collision_from(spec_ns_view(a@), spec_ns_view(b@), bi as nat)
                == spec_find_collision_from(spec_ns_view(a@), spec_ns_view(b@), 0),
        decreases nb - bi,
    {
        if name_occurs_before(a, na, b[bi].name.as_slice()) {
            return Some(b[bi].span);
        }
        bi = bi + 1;
    }
    None
}

// ---------------------------------------------------------------------------------------
// Identifier, BindingIdentifier, and AssignmentTargetType (§13.1, §13.2.10.2)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_check_ident_ref(
    ident: Ident,
    strict: bool,
    in_async: bool,
    in_generator: bool,
) -> Result<(), SyntaxDiagnostic> {
    match spec_classify_ident(ident.name@) {
        Some(kw) => {
            if spec_is_unconditional_reserved(kw) {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::UnexpectedToken, span: ident.span })
            } else if strict && spec_is_strict_reserved_word(kw) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictReservedWord,
                    span: ident.span,
                })
            } else if in_async && kw == Keyword::Await {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyAwaitOutsideAsync,
                    span: ident.span,
                })
            } else if in_generator && kw == Keyword::Yield {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyYieldOutsideGenerator,
                    span: ident.span,
                })
            } else {
                Ok(())
            }
        },
        None => Ok(()),
    }
}

pub fn check_ident_ref(
    ident: &Ident,
    strict: bool,
    in_async: bool,
    in_generator: bool,
) -> (r: Result<(), SyntaxDiagnostic>)
    ensures
        r == spec_check_ident_ref(*ident, strict, in_async, in_generator),
{
    match classify_ident(ident.name.as_slice()) {
        Some(kw) => {
            if is_unconditional_reserved(kw) {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::UnexpectedToken, span: ident.span })
            } else if strict && is_strict_reserved_word(kw) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictReservedWord,
                    span: ident.span,
                })
            } else if in_async && kw == Keyword::Await {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyAwaitOutsideAsync,
                    span: ident.span,
                })
            } else if in_generator && kw == Keyword::Yield {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyYieldOutsideGenerator,
                    span: ident.span,
                })
            } else {
                Ok(())
            }
        },
        None => Ok(()),
    }
}

pub open spec fn spec_check_binding_ident(
    ident: Ident,
    strict: bool,
    in_async: bool,
    in_generator: bool,
    is_let_or_const: bool,
) -> Result<(), SyntaxDiagnostic> {
    match spec_check_ident_ref(ident, strict, in_async, in_generator) {
        Err(e) => Err(e),
        Ok(()) => {
            if is_let_or_const && spec_is_let_name(ident.name@) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyLetBoundInLexicalDecl,
                    span: ident.span,
                })
            } else if strict && spec_is_eval_or_arguments(ident.name@) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictEvalOrArgumentsBinding,
                    span: ident.span,
                })
            } else {
                Ok(())
            }
        },
    }
}

pub fn check_binding_ident(
    ident: &Ident,
    strict: bool,
    in_async: bool,
    in_generator: bool,
    is_let_or_const: bool,
) -> (r: Result<(), SyntaxDiagnostic>)
    ensures
        r == spec_check_binding_ident(*ident, strict, in_async, in_generator, is_let_or_const),
{
    match check_ident_ref(ident, strict, in_async, in_generator) {
        Err(e) => Err(e),
        Ok(()) => {
            if is_let_or_const && is_let_name(ident.name.as_slice()) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyLetBoundInLexicalDecl,
                    span: ident.span,
                })
            } else if strict && is_eval_or_arguments(ident.name.as_slice()) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictEvalOrArgumentsBinding,
                    span: ident.span,
                })
            } else {
                Ok(())
            }
        },
    }
}

/// Quantifier-free parenthesized-expression unwrapper, terminating purely on scalar `rank`.
pub open spec fn spec_unwrap_parens(prog: SpecProgram, eid: ExprId) -> ExprId
    decreases
        if eid.0 < prog.exprs.len() { (prog.exprs[eid.0 as int].rank as int) + 1 } else { 0int },
{
    if eid.0 >= prog.exprs.len() {
        eid
    } else {
        let erank = prog.exprs[eid.0 as int].rank as nat;
        match prog.exprs[eid.0 as int].kind {
            ExprKind::Paren(inner) => {
                if inner.0 < prog.exprs.len() && (prog.exprs[inner.0 as int].rank as nat) < erank {
                    spec_unwrap_parens(prog, inner)
                } else {
                    eid
                }
            },
            _ => eid,
        }
    }
}

pub fn unwrap_parens(prog: &Program, eid0: ExprId) -> (r: ExprId)
    requires
        prog.wf(),
        eid0.0 < prog@.exprs.len(),
    ensures
        r == spec_unwrap_parens(prog@, eid0),
        r.0 < prog@.exprs.len(),
{
    let mut cur = eid0;
    loop
        invariant
            prog.wf(),
            cur.0 < prog@.exprs.len(),
            spec_unwrap_parens(prog@, cur) == spec_unwrap_parens(prog@, eid0),
        decreases prog@.exprs[cur.0 as int].rank,
    {
        match &prog.exprs[cur.0].kind {
            ExprKind::Paren(inner) => {
                cur = *inner;
            },
            _ => {
                return cur;
            },
        }
    }
}

pub open spec fn spec_is_logical_assign_op(op: AssignOp) -> bool {
    match op {
        AssignOp::LogicalAndAssign | AssignOp::LogicalOrAssign | AssignOp::CoalesceAssign => true,
        _ => false,
    }
}

pub fn is_logical_assign_op(op: AssignOp) -> (r: bool)
    ensures
        r == spec_is_logical_assign_op(op),
{
    match op {
        AssignOp::LogicalAndAssign | AssignOp::LogicalOrAssign | AssignOp::CoalesceAssign => true,
        _ => false,
    }
}

pub open spec fn spec_is_proto_bytes(b: Seq<u8>) -> bool {
    b.len() == 9
        && b[0] == 0x5F
        && b[1] == 0x5F
        && b[2] == 0x70
        && b[3] == 0x72
        && b[4] == 0x6F
        && b[5] == 0x74
        && b[6] == 0x6F
        && b[7] == 0x5F
        && b[8] == 0x5F
}

pub fn is_proto_bytes(b: &[u8]) -> (r: bool)
    ensures
        r == spec_is_proto_bytes(b@),
{
    b.len() == 9
        && b[0] == 0x5F
        && b[1] == 0x5F
        && b[2] == 0x70
        && b[3] == 0x72
        && b[4] == 0x6F
        && b[5] == 0x74
        && b[6] == 0x6F
        && b[7] == 0x5F
        && b[8] == 0x5F
}

pub open spec fn spec_is_proto_u16(u: Seq<u16>) -> bool {
    u.len() == 9
        && u[0] == 0x005F
        && u[1] == 0x005F
        && u[2] == 0x0070
        && u[3] == 0x0072
        && u[4] == 0x006F
        && u[5] == 0x0074
        && u[6] == 0x006F
        && u[7] == 0x005F
        && u[8] == 0x005F
}

pub fn is_proto_u16(u: &[u16]) -> (r: bool)
    ensures
        r == spec_is_proto_u16(u@),
{
    u.len() == 9
        && u[0] == 0x005F
        && u[1] == 0x005F
        && u[2] == 0x0070
        && u[3] == 0x0072
        && u[4] == 0x006F
        && u[5] == 0x0074
        && u[6] == 0x006F
        && u[7] == 0x005F
        && u[8] == 0x005F
}

/// ECMA-262 §13.2.5.1: whether `prop` is `PropertyDefinition : PropertyName : AssignmentExpression`
/// whose non-computed `PropName` is `"__proto__"`.
pub open spec fn spec_is_proto_init_prop(prop: ObjPropKind) -> bool {
    match prop {
        ObjPropKind::Init { key, is_shorthand: false, .. } => match key {
            PropKeyAst::Ident(id) => spec_is_proto_bytes(id@),
            PropKeyAst::StringLit { units, .. } => spec_is_proto_u16(units@),
            _ => false,
        },
        _ => false,
    }
}

pub fn is_proto_init_prop(prop: &ObjPropKind) -> (r: bool)
    ensures
        r == spec_is_proto_init_prop(*prop),
{
    match prop {
        ObjPropKind::Init { key, is_shorthand: false, .. } => match key {
            PropKeyAst::Ident(id) => is_proto_bytes(id.as_slice()),
            PropKeyAst::StringLit { units, .. } => is_proto_u16(units.as_slice()),
            _ => false,
        },
        _ => false,
    }
}

pub open spec fn spec_has_duplicate_proto_init(
    props: Seq<ObjPropKind>,
    idx: nat,
    seen: bool,
) -> bool
    decreases props.len() - idx,
{
    if idx >= props.len() {
        false
    } else if spec_is_proto_init_prop(props[idx as int]) {
        if seen {
            true
        } else {
            spec_has_duplicate_proto_init(props, idx + 1, true)
        }
    } else {
        spec_has_duplicate_proto_init(props, idx + 1, seen)
    }
}

pub fn has_duplicate_proto_init(props: &[ObjPropKind]) -> (r: bool)
    ensures
        r == spec_has_duplicate_proto_init(props@, 0, false),
{
    let n = props.len();
    let mut idx: usize = 0;
    let mut seen = false;
    while idx < n
        invariant
            idx <= n,
            n == props@.len(),
            spec_has_duplicate_proto_init(props@, 0, false)
                == spec_has_duplicate_proto_init(props@, idx as nat, seen),
        decreases n - idx,
    {
        if is_proto_init_prop(&props[idx]) {
            if seen {
                return true;
            }
            seen = true;
        }
        idx = idx + 1;
    }
    false
}

pub open spec fn spec_check_assignment_target(
    prog: SpecProgram,
    eid: ExprId,
    strict: bool,
    allow_web_compat: bool,
) -> Result<(), SyntaxDiagnostic> {
    let target_id = spec_unwrap_parens(prog, eid);
    if target_id.0 >= prog.exprs.len() {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
            span: Span { start: 0, end: 0 },
        })
    } else {
        let e = prog.exprs[target_id.0 as int];
        if e.in_optional_chain {
            Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
                span: e.span,
            })
        } else {
            match e.kind {
                ExprKind::Ident(ident) => {
                    if strict && spec_is_eval_or_arguments(ident.name@) {
                        Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyStrictEvalOrArgumentsAssign,
                            span: ident.span,
                        })
                    } else {
                        Ok(())
                    }
                },
                ExprKind::Member { optional: false, .. } => Ok(()),
                ExprKind::ComputedMember { optional: false, .. } => Ok(()),
                ExprKind::Call { optional: false, .. } => {
                    if allow_web_compat && !strict {
                        Ok(())
                    } else {
                        Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
                            span: e.span,
                        })
                    }
                },
                _ => Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
                    span: e.span,
                }),
            }
        }
    }
}

pub fn check_assignment_target(
    prog: &Program,
    eid: ExprId,
    strict: bool,
    allow_web_compat: bool,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        eid.0 < prog@.exprs.len(),
    ensures
        r == spec_check_assignment_target(prog@, eid, strict, allow_web_compat),
{
    let target_id = unwrap_parens(prog, eid);
    let e = &prog.exprs[target_id.0];
    if e.in_optional_chain {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
            span: e.span,
        })
    } else {
        match &e.kind {
            ExprKind::Ident(ident) => {
                if strict && is_eval_or_arguments(ident.name.as_slice()) {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyStrictEvalOrArgumentsAssign,
                        span: ident.span,
                    })
                } else {
                    Ok(())
                }
            },
            ExprKind::Member { optional: false, .. } => Ok(()),
            ExprKind::ComputedMember { optional: false, .. } => Ok(()),
            ExprKind::Call { optional: false, .. } => {
                if allow_web_compat && !strict {
                    Ok(())
                } else {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
                        span: e.span,
                    })
                }
            },
            _ => Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyInvalidAssignmentTarget,
                span: e.span,
            }),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Static Semantics: `VarDeclaredNames` (§8.2.6) — Quantifier-Free Spec Recursion
// ---------------------------------------------------------------------------------------

pub open spec fn spec_push_var_decls(
    decls: Seq<VarDeclarator>,
    idx: nat,
    acc: Seq<SpecNameSpan>,
) -> Seq<SpecNameSpan>
    decreases decls.len() - idx,
{
    if idx >= decls.len() {
        acc
    } else {
        let d = decls[idx as int];
        spec_push_var_decls(
            decls,
            idx + 1,
            acc.push(SpecNameSpan { name: d.name.name@, span: d.name.span }),
        )
    }
}

pub fn push_var_decls(decls: &[VarDeclarator], acc: &mut Vec<NameSpan>)
    ensures
        spec_ns_view(final(acc)@) == spec_push_var_decls(decls@, 0, spec_ns_view(old(acc)@)),
{
    let n = decls.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == decls@.len(),
            spec_push_var_decls(decls@, idx as nat, spec_ns_view(acc@))
                == spec_push_var_decls(decls@, 0, spec_ns_view(old(acc)@)),
        decreases n - idx,
    {
        let ns = make_name_span(&decls[idx].name);
        let ghost old_s = acc@;
        let ghost g_ns = ns;
        acc.push(ns);
        proof {
            lemma_ns_push_view(old_s, g_ns);
        }
        idx = idx + 1;
    }
}

pub open spec fn spec_collect_var_names_stmt(
    prog: SpecProgram,
    sid: StmtId,
    acc: Seq<SpecNameSpan>,
) -> Seq<SpecNameSpan>
    decreases
        if sid.0 < prog.stmts.len() { prog.stmts[sid.0 as int].rank as nat } else { 0nat },
        3nat,
        0nat,
{
    if sid.0 >= prog.stmts.len() {
        acc
    } else {
        let rank = prog.stmts[sid.0 as int].rank as nat;
        match prog.stmts[sid.0 as int].kind {
            StmtKind::VarDecl { kind: VarDeclKind::Var, decls } => {
                spec_push_var_decls(decls@, 0, acc)
            },
            StmtKind::Block(ids) => spec_collect_var_names_list(prog, ids@, 0, rank, acc),
            StmtKind::If { consequent, alternate, .. } => {
                let a1 = if consequent.0 < prog.stmts.len()
                    && (prog.stmts[consequent.0 as int].rank as nat) < rank
                {
                    spec_collect_var_names_stmt(prog, consequent, acc)
                } else {
                    acc
                };
                match alternate {
                    Some(alt) => {
                        if alt.0 < prog.stmts.len()
                            && (prog.stmts[alt.0 as int].rank as nat) < rank
                        {
                            spec_collect_var_names_stmt(prog, alt, a1)
                        } else {
                            a1
                        }
                    },
                    None => a1,
                }
            },
            StmtKind::While { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, acc)
                } else {
                    acc
                }
            },
            StmtKind::DoWhile { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, acc)
                } else {
                    acc
                }
            },
            StmtKind::With { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, acc)
                } else {
                    acc
                }
            },
            StmtKind::Labeled { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, acc)
                } else {
                    acc
                }
            },
            StmtKind::For { init, body, .. } => {
                let a1 = match init {
                    ForInit::VarDecl { kind: VarDeclKind::Var, decls } => {
                        spec_push_var_decls(decls@, 0, acc)
                    },
                    _ => acc,
                };
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, a1)
                } else {
                    a1
                }
            },
            StmtKind::ForIn { lhs, body, .. } => {
                let a1 = match lhs {
                    ForInOfLhs::VarDecl { kind: VarDeclKind::Var, name } => {
                        acc.push(SpecNameSpan { name: name.name@, span: name.span })
                    },
                    _ => acc,
                };
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, a1)
                } else {
                    a1
                }
            },
            StmtKind::ForOf { lhs, body, .. } => {
                let a1 = match lhs {
                    ForInOfLhs::VarDecl { kind: VarDeclKind::Var, name } => {
                        acc.push(SpecNameSpan { name: name.name@, span: name.span })
                    },
                    _ => acc,
                };
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < rank {
                    spec_collect_var_names_stmt(prog, body, a1)
                } else {
                    a1
                }
            },
            StmtKind::Switch { cases, .. } => {
                spec_collect_var_names_cases(prog, cases@, 0, rank, acc)
            },
            StmtKind::Try { block, catch_clause, finally_block } => {
                let a1 = spec_collect_var_names_list(prog, block@, 0, rank, acc);
                let a2 = match catch_clause {
                    Some(cc) => spec_collect_var_names_list(prog, cc.body@, 0, rank, a1),
                    None => a1,
                };
                match finally_block {
                    Some(fb) => spec_collect_var_names_list(prog, fb@, 0, rank, a2),
                    None => a2,
                }
            },
            _ => acc,
        }
    }
}

pub open spec fn spec_collect_var_names_list(
    prog: SpecProgram,
    ids: Seq<StmtId>,
    idx: nat,
    bound_rank: nat,
    acc: Seq<SpecNameSpan>,
) -> Seq<SpecNameSpan>
    decreases bound_rank, 1nat, ids.len() - idx + 1,
{
    if idx >= ids.len() {
        acc
    } else {
        let sid = ids[idx as int];
        let a1 = if sid.0 < prog.stmts.len() && (prog.stmts[sid.0 as int].rank as nat) < bound_rank {
            spec_collect_var_names_stmt(prog, sid, acc)
        } else {
            acc
        };
        spec_collect_var_names_list(prog, ids, idx + 1, bound_rank, a1)
    }
}

pub open spec fn spec_collect_var_names_cases(
    prog: SpecProgram,
    cases: Seq<SwitchCase>,
    idx: nat,
    bound_rank: nat,
    acc: Seq<SpecNameSpan>,
) -> Seq<SpecNameSpan>
    decreases bound_rank, 2nat, cases.len() - idx,
{
    if idx >= cases.len() {
        acc
    } else {
        let c = cases[idx as int];
        let a1 = spec_collect_var_names_list(prog, c.consequent@, 0, bound_rank, acc);
        spec_collect_var_names_cases(prog, cases, idx + 1, bound_rank, a1)
    }
}

pub fn collect_var_names_stmt(prog: &Program, sid: StmtId, acc: &mut Vec<NameSpan>)
    requires
        prog.wf(),
        sid.0 < prog@.stmts.len(),
    ensures
        spec_ns_view(final(acc)@) == spec_collect_var_names_stmt(prog@, sid, spec_ns_view(old(acc)@)),
    decreases prog@.stmts[sid.0 as int].rank as nat, 3nat, 0nat,
{
    let rank = prog.stmts[sid.0].rank;
    proof {
        assert(crate::ast::stmt_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.stmts[sid.0 as int].kind,
            rank as nat,
        ));
    }
    match &prog.stmts[sid.0].kind {
        StmtKind::VarDecl { kind: VarDeclKind::Var, decls } => {
            push_var_decls(decls.as_slice(), acc);
        },
        StmtKind::Block(ids) => {
            collect_var_names_list(prog, ids.as_slice(), rank, acc);
        },
        StmtKind::If { consequent, alternate, .. } => {
            collect_var_names_stmt(prog, *consequent, acc);
            if let Some(alt) = alternate {
                collect_var_names_stmt(prog, *alt, acc);
            }
        },
        StmtKind::While { body, .. } => collect_var_names_stmt(prog, *body, acc),
        StmtKind::DoWhile { body, .. } => collect_var_names_stmt(prog, *body, acc),
        StmtKind::With { body, .. } => collect_var_names_stmt(prog, *body, acc),
        StmtKind::Labeled { body, .. } => collect_var_names_stmt(prog, *body, acc),
        StmtKind::For { init, body, .. } => {
            if let ForInit::VarDecl { kind: VarDeclKind::Var, decls } = init {
                push_var_decls(decls.as_slice(), acc);
            }
            collect_var_names_stmt(prog, *body, acc);
        },
        StmtKind::ForIn { lhs, body, .. } => {
            if let ForInOfLhs::VarDecl { kind: VarDeclKind::Var, name } = lhs {
                let ns = make_name_span(name);
                let ghost old_s = acc@;
                let ghost g_ns = ns;
                acc.push(ns);
                proof {
                    lemma_ns_push_view(old_s, g_ns);
                }
            }
            collect_var_names_stmt(prog, *body, acc);
        },
        StmtKind::ForOf { lhs, body, .. } => {
            if let ForInOfLhs::VarDecl { kind: VarDeclKind::Var, name } = lhs {
                let ns = make_name_span(name);
                let ghost old_s = acc@;
                let ghost g_ns = ns;
                acc.push(ns);
                proof {
                    lemma_ns_push_view(old_s, g_ns);
                }
            }
            collect_var_names_stmt(prog, *body, acc);
        },
        StmtKind::Switch { cases, .. } => {
            proof {
                assert forall|k: int| 0 <= k < cases@.len() implies stmt_seq_bounded(
                    prog@.stmts,
                    (#[trigger] cases@[k]).consequent@,
                    rank as nat,
                ) by {
                    assert(opt_expr_bounded(prog@.exprs, cases@[k].test, rank as nat)
                        && stmt_seq_bounded(prog@.stmts, cases@[k].consequent@, rank as nat));
                }
            }
            collect_var_names_cases(prog, cases.as_slice(), rank, acc);
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            collect_var_names_list(prog, block.as_slice(), rank, acc);
            if let Some(cc) = catch_clause {
                collect_var_names_list(prog, cc.body.as_slice(), rank, acc);
            }
            if let Some(fb) = finally_block {
                collect_var_names_list(prog, fb.as_slice(), rank, acc);
            }
        },
        _ => {},
    }
}

pub fn collect_var_names_list(
    prog: &Program,
    ids: &[StmtId],
    bound_rank: usize,
    acc: &mut Vec<NameSpan>,
)
    requires
        prog.wf(),
        stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
    ensures
        spec_ns_view(final(acc)@)
            == spec_collect_var_names_list(prog@, ids@, 0, bound_rank as nat, spec_ns_view(old(acc)@)),
    decreases bound_rank as nat, 1nat, 0nat,
{
    let n = ids.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == ids@.len(),
            prog.wf(),
            stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
            spec_collect_var_names_list(prog@, ids@, idx as nat, bound_rank as nat, spec_ns_view(acc@))
                == spec_collect_var_names_list(
                    prog@,
                    ids@,
                    0,
                    bound_rank as nat,
                    spec_ns_view(old(acc)@),
                ),
        decreases n - idx,
    {
        let sid = ids[idx];
        proof {
            assert(stmt_id_bounded(prog@.stmts, ids@[idx as int], bound_rank as nat));
        }
        collect_var_names_stmt(prog, sid, acc);
        idx = idx + 1;
    }
}

pub fn collect_var_names_cases(
    prog: &Program,
    cases: &[SwitchCase],
    bound_rank: usize,
    acc: &mut Vec<NameSpan>,
)
    requires
        prog.wf(),
        forall|k: int|
            0 <= k < cases@.len()
                ==> stmt_seq_bounded(prog@.stmts, (#[trigger] cases@[k]).consequent@, bound_rank as nat),
    ensures
        spec_ns_view(final(acc)@)
            == spec_collect_var_names_cases(
                prog@,
                cases@,
                0,
                bound_rank as nat,
                spec_ns_view(old(acc)@),
            ),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = cases.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == cases@.len(),
            prog.wf(),
            forall|k: int|
                0 <= k < cases@.len()
                    ==> stmt_seq_bounded(prog@.stmts, (#[trigger] cases@[k]).consequent@, bound_rank as nat),
            spec_collect_var_names_cases(
                prog@,
                cases@,
                idx as nat,
                bound_rank as nat,
                spec_ns_view(acc@),
            ) == spec_collect_var_names_cases(
                prog@,
                cases@,
                0,
                bound_rank as nat,
                spec_ns_view(old(acc)@),
            ),
        decreases n - idx,
    {
        proof {
            assert(stmt_seq_bounded(prog@.stmts, cases@[idx as int].consequent@, bound_rank as nat));
        }
        collect_var_names_list(prog, cases[idx].consequent.as_slice(), bound_rank, acc);
        idx = idx + 1;
    }
}

// ---------------------------------------------------------------------------------------
// Scope Lexical / Var Redeclaration Checks (TopLevel, Block, Switch)
// ---------------------------------------------------------------------------------------

/// Unwraps arbitrarily nested `StmtKind::Labeled` chains (`l1: l2: function f() {}`),
/// returning `Some((SpecNameSpan, is_async, is_generator))` iff the innermost `LabelledItem`
/// is a `StmtKind::FunctionDecl` (ECMA-262 §8.2.5 / §8.2.6 / Annex B.3.2).
pub open spec fn spec_unwrap_labeled_fn_decl(
    prog: SpecProgram,
    sid: StmtId,
) -> Option<(SpecNameSpan, bool, bool)>
    decreases
        if sid.0 < prog.stmts.len() { (prog.stmts[sid.0 as int].rank as int) + 1 } else { 0int },
{
    if sid.0 >= prog.stmts.len() {
        None
    } else {
        let srank = prog.stmts[sid.0 as int].rank as nat;
        match prog.stmts[sid.0 as int].kind {
            StmtKind::FunctionDecl { name, is_async, is_generator, .. } => {
                Some((SpecNameSpan { name: name.name@, span: name.span }, is_async, is_generator))
            },
            StmtKind::Labeled { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < srank {
                    spec_unwrap_labeled_fn_decl(prog, body)
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

pub fn unwrap_labeled_fn_decl(prog: &Program, sid0: StmtId) -> (r: Option<(NameSpan, bool, bool)>)
    requires
        prog.wf(),
        sid0.0 < prog@.stmts.len(),
    ensures
        match r {
            Some((ns, ia, ig)) => {
                spec_unwrap_labeled_fn_decl(prog@, sid0) == Some((ns@, ia, ig))
            },
            None => spec_unwrap_labeled_fn_decl(prog@, sid0) is None,
        },
{
    let mut cur = sid0;
    loop
        invariant
            prog.wf(),
            cur.0 < prog@.stmts.len(),
            spec_unwrap_labeled_fn_decl(prog@, cur) == spec_unwrap_labeled_fn_decl(prog@, sid0),
        decreases prog@.stmts[cur.0 as int].rank,
    {
        match &prog.stmts[cur.0].kind {
            StmtKind::FunctionDecl { name, is_async, is_generator, .. } => {
                let ns = make_name_span(name);
                return Some((ns, *is_async, *is_generator));
            },
            StmtKind::Labeled { body, .. } => {
                cur = *body;
            },
            _ => {
                return None;
            },
        }
    }
}

pub open spec fn spec_collect_toplevel_decls(
    prog: SpecProgram,
    ids: Seq<StmtId>,
    idx: nat,
    bound_rank: nat,
    lex_acc: Seq<SpecNameSpan>,
    var_acc: Seq<SpecNameSpan>,
) -> (Seq<SpecNameSpan>, Seq<SpecNameSpan>)
    decreases ids.len() - idx,
{
    if idx >= ids.len() {
        (lex_acc, var_acc)
    } else {
        let sid = ids[idx as int];
        if sid.0 < prog.stmts.len() && (prog.stmts[sid.0 as int].rank as nat) < bound_rank {
            match prog.stmts[sid.0 as int].kind {
                StmtKind::VarDecl { kind: VarDeclKind::Let, decls } => {
                    let next_lex = spec_push_var_decls(decls@, 0, lex_acc);
                    spec_collect_toplevel_decls(prog, ids, idx + 1, bound_rank, next_lex, var_acc)
                },
                StmtKind::VarDecl { kind: VarDeclKind::Const, decls } => {
                    let next_lex = spec_push_var_decls(decls@, 0, lex_acc);
                    spec_collect_toplevel_decls(prog, ids, idx + 1, bound_rank, next_lex, var_acc)
                },
                _ => match spec_unwrap_labeled_fn_decl(prog, sid) {
                    Some((ns, _, _)) => {
                        let next_var = var_acc.push(ns);
                        spec_collect_toplevel_decls(prog, ids, idx + 1, bound_rank, lex_acc, next_var)
                    },
                    None => {
                        let next_var = spec_collect_var_names_stmt(prog, sid, var_acc);
                        spec_collect_toplevel_decls(prog, ids, idx + 1, bound_rank, lex_acc, next_var)
                    },
                },
            }
        } else {
            (lex_acc, var_acc)
        }
    }
}

pub fn collect_toplevel_decls(
    prog: &Program,
    ids: &[StmtId],
    bound_rank: usize,
) -> (r: (Vec<NameSpan>, Vec<NameSpan>))
    requires
        prog.wf(),
        stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
    ensures
        (spec_ns_view(r.0@), spec_ns_view(r.1@))
            == spec_collect_toplevel_decls(
                prog@,
                ids@,
                0,
                bound_rank as nat,
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
            ),
{
    let n = ids.len();
    let mut lex_acc: Vec<NameSpan> = Vec::new();
    let mut var_acc: Vec<NameSpan> = Vec::new();
    let mut idx: usize = 0;
    proof {
        assert(spec_ns_view(lex_acc@) =~= Seq::<SpecNameSpan>::empty());
        assert(spec_ns_view(var_acc@) =~= Seq::<SpecNameSpan>::empty());
    }
    while idx < n
        invariant
            idx <= n,
            n == ids@.len(),
            prog.wf(),
            stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
            spec_collect_toplevel_decls(
                prog@,
                ids@,
                idx as nat,
                bound_rank as nat,
                spec_ns_view(lex_acc@),
                spec_ns_view(var_acc@),
            ) == spec_collect_toplevel_decls(
                prog@,
                ids@,
                0,
                bound_rank as nat,
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
            ),
        decreases n - idx,
    {
        let sid = ids[idx];
        proof {
            assert(stmt_id_bounded(prog@.stmts, ids@[idx as int], bound_rank as nat));
        }
        match &prog.stmts[sid.0].kind {
            StmtKind::VarDecl { kind: VarDeclKind::Let, decls } => {
                push_var_decls(decls.as_slice(), &mut lex_acc);
            },
            StmtKind::VarDecl { kind: VarDeclKind::Const, decls } => {
                push_var_decls(decls.as_slice(), &mut lex_acc);
            },
            _ => match unwrap_labeled_fn_decl(prog, sid) {
                Some((ns, _, _)) => {
                    let ghost old_s = var_acc@;
                    let ghost g_ns = ns;
                    var_acc.push(ns);
                    proof {
                        lemma_ns_push_view(old_s, g_ns);
                    }
                },
                None => {
                    collect_var_names_stmt(prog, sid, &mut var_acc);
                },
            },
        }
        idx = idx + 1;
    }
    (lex_acc, var_acc)
}

pub open spec fn spec_collect_block_decls(
    prog: SpecProgram,
    ids: Seq<StmtId>,
    idx: nat,
    bound_rank: nat,
    strict: bool,
    lex_acc: Seq<SpecNameSpan>,
    sloppy_fn_acc: Seq<SpecNameSpan>,
    var_acc: Seq<SpecNameSpan>,
) -> (Seq<SpecNameSpan>, Seq<SpecNameSpan>, Seq<SpecNameSpan>)
    decreases ids.len() - idx,
{
    if idx >= ids.len() {
        (lex_acc, sloppy_fn_acc, var_acc)
    } else {
        let sid = ids[idx as int];
        if sid.0 < prog.stmts.len() && (prog.stmts[sid.0 as int].rank as nat) < bound_rank {
            match prog.stmts[sid.0 as int].kind {
                StmtKind::VarDecl { kind: VarDeclKind::Let, decls } => {
                    let next_lex = spec_push_var_decls(decls@, 0, lex_acc);
                    spec_collect_block_decls(
                        prog,
                        ids,
                        idx + 1,
                        bound_rank,
                        strict,
                        next_lex,
                        sloppy_fn_acc,
                        var_acc,
                    )
                },
                StmtKind::VarDecl { kind: VarDeclKind::Const, decls } => {
                    let next_lex = spec_push_var_decls(decls@, 0, lex_acc);
                    spec_collect_block_decls(
                        prog,
                        ids,
                        idx + 1,
                        bound_rank,
                        strict,
                        next_lex,
                        sloppy_fn_acc,
                        var_acc,
                    )
                },
                _ => match spec_unwrap_labeled_fn_decl(prog, sid) {
                    Some((ns, is_async, is_generator)) => {
                        if strict || is_async || is_generator {
                            spec_collect_block_decls(
                                prog,
                                ids,
                                idx + 1,
                                bound_rank,
                                strict,
                                lex_acc.push(ns),
                                sloppy_fn_acc,
                                var_acc,
                            )
                        } else {
                            spec_collect_block_decls(
                                prog,
                                ids,
                                idx + 1,
                                bound_rank,
                                strict,
                                lex_acc,
                                sloppy_fn_acc.push(ns),
                                var_acc,
                            )
                        }
                    },
                    None => {
                        let next_var = spec_collect_var_names_stmt(prog, sid, var_acc);
                        spec_collect_block_decls(
                            prog,
                            ids,
                            idx + 1,
                            bound_rank,
                            strict,
                            lex_acc,
                            sloppy_fn_acc,
                            next_var,
                        )
                    },
                },
            }
        } else {
            (lex_acc, sloppy_fn_acc, var_acc)
        }
    }
}

pub fn collect_block_decls_into(
    prog: &Program,
    ids: &[StmtId],
    bound_rank: usize,
    strict: bool,
    lex_acc: &mut Vec<NameSpan>,
    sloppy_fn_acc: &mut Vec<NameSpan>,
    var_acc: &mut Vec<NameSpan>,
)
    requires
        prog.wf(),
        stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
    ensures
        (spec_ns_view(final(lex_acc)@), spec_ns_view(final(sloppy_fn_acc)@), spec_ns_view(final(var_acc)@))
            == spec_collect_block_decls(
                prog@,
                ids@,
                0,
                bound_rank as nat,
                strict,
                spec_ns_view(old(lex_acc)@),
                spec_ns_view(old(sloppy_fn_acc)@),
                spec_ns_view(old(var_acc)@),
            ),
{
    let n = ids.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == ids@.len(),
            prog.wf(),
            stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
            spec_collect_block_decls(
                prog@,
                ids@,
                idx as nat,
                bound_rank as nat,
                strict,
                spec_ns_view(lex_acc@),
                spec_ns_view(sloppy_fn_acc@),
                spec_ns_view(var_acc@),
            ) == spec_collect_block_decls(
                prog@,
                ids@,
                0,
                bound_rank as nat,
                strict,
                spec_ns_view(old(lex_acc)@),
                spec_ns_view(old(sloppy_fn_acc)@),
                spec_ns_view(old(var_acc)@),
            ),
        decreases n - idx,
    {
        let sid = ids[idx];
        proof {
            assert(stmt_id_bounded(prog@.stmts, ids@[idx as int], bound_rank as nat));
        }
        match &prog.stmts[sid.0].kind {
            StmtKind::VarDecl { kind: VarDeclKind::Let, decls } => {
                push_var_decls(decls.as_slice(), lex_acc);
            },
            StmtKind::VarDecl { kind: VarDeclKind::Const, decls } => {
                push_var_decls(decls.as_slice(), lex_acc);
            },
            _ => match unwrap_labeled_fn_decl(prog, sid) {
                Some((ns, is_async, is_generator)) => {
                    let ghost g_ns = ns;
                    if strict || is_async || is_generator {
                        let ghost old_l = lex_acc@;
                        lex_acc.push(ns);
                        proof {
                            lemma_ns_push_view(old_l, g_ns);
                        }
                    } else {
                        let ghost old_sf = sloppy_fn_acc@;
                        sloppy_fn_acc.push(ns);
                        proof {
                            lemma_ns_push_view(old_sf, g_ns);
                        }
                    }
                },
                None => {
                    collect_var_names_stmt(prog, sid, var_acc);
                },
            },
        }
        idx = idx + 1;
    }
}

#[verifier::opaque]
pub open spec fn spec_validate_block_triple(
    lex: Seq<SpecNameSpan>,
    sloppy_fn: Seq<SpecNameSpan>,
    vars: Seq<SpecNameSpan>,
) -> Result<(), SyntaxDiagnostic> {
    match spec_find_duplicate_name(lex) {
        Some(span) => Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span,
        }),
        None => match spec_find_collision(lex, sloppy_fn) {
            Some(span) => Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                span,
            }),
            None => match spec_find_collision(lex, vars) {
                Some(span) => Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyLexicalVarCollision,
                    span,
                }),
                None => match spec_find_collision(sloppy_fn, vars) {
                    Some(span) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyLexicalVarCollision,
                        span,
                    }),
                    None => Ok(()),
                },
            },
        },
    }
}

pub fn validate_block_triple(
    lex: &[NameSpan],
    sloppy_fn: &[NameSpan],
    vars: &[NameSpan],
) -> (r: Result<(), SyntaxDiagnostic>)
    ensures
        r == spec_validate_block_triple(spec_ns_view(lex@), spec_ns_view(sloppy_fn@), spec_ns_view(vars@)),
{
    proof {
        reveal(spec_validate_block_triple);
    }
    match find_duplicate_name(lex) {
        Some(span) => Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span,
        }),
        None => match find_collision(lex, sloppy_fn) {
            Some(span) => Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                span,
            }),
            None => match find_collision(lex, vars) {
                Some(span) => Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyLexicalVarCollision,
                    span,
                }),
                None => match find_collision(sloppy_fn, vars) {
                    Some(span) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyLexicalVarCollision,
                        span,
                    }),
                    None => Ok(()),
                },
            },
        },
    }
}

pub open spec fn spec_collect_switch_decls(
    prog: SpecProgram,
    cases: Seq<SwitchCase>,
    idx: nat,
    bound_rank: nat,
    strict: bool,
    lex_acc: Seq<SpecNameSpan>,
    sloppy_fn_acc: Seq<SpecNameSpan>,
    var_acc: Seq<SpecNameSpan>,
) -> (Seq<SpecNameSpan>, Seq<SpecNameSpan>, Seq<SpecNameSpan>)
    decreases cases.len() - idx,
{
    if idx >= cases.len() {
        (lex_acc, sloppy_fn_acc, var_acc)
    } else {
        let c = cases[idx as int];
        let (l1, sf1, v1) = spec_collect_block_decls(
            prog,
            c.consequent@,
            0,
            bound_rank,
            strict,
            lex_acc,
            sloppy_fn_acc,
            var_acc,
        );
        spec_collect_switch_decls(prog, cases, idx + 1, bound_rank, strict, l1, sf1, v1)
    }
}

pub fn collect_switch_decls(
    prog: &Program,
    cases: &[SwitchCase],
    bound_rank: usize,
    strict: bool,
) -> (r: (Vec<NameSpan>, Vec<NameSpan>, Vec<NameSpan>))
    requires
        prog.wf(),
        forall|k: int|
            0 <= k < cases@.len()
                ==> stmt_seq_bounded(prog@.stmts, (#[trigger] cases@[k]).consequent@, bound_rank as nat),
    ensures
        (spec_ns_view(r.0@), spec_ns_view(r.1@), spec_ns_view(r.2@))
            == spec_collect_switch_decls(
                prog@,
                cases@,
                0,
                bound_rank as nat,
                strict,
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
            ),
{
    let n = cases.len();
    let mut lex_acc: Vec<NameSpan> = Vec::new();
    let mut sloppy_fn_acc: Vec<NameSpan> = Vec::new();
    let mut var_acc: Vec<NameSpan> = Vec::new();
    let mut idx: usize = 0;
    proof {
        assert(spec_ns_view(lex_acc@) =~= Seq::<SpecNameSpan>::empty());
        assert(spec_ns_view(sloppy_fn_acc@) =~= Seq::<SpecNameSpan>::empty());
        assert(spec_ns_view(var_acc@) =~= Seq::<SpecNameSpan>::empty());
    }
    while idx < n
        invariant
            idx <= n,
            n == cases@.len(),
            prog.wf(),
            forall|k: int|
                0 <= k < cases@.len()
                    ==> stmt_seq_bounded(prog@.stmts, (#[trigger] cases@[k]).consequent@, bound_rank as nat),
            spec_collect_switch_decls(
                prog@,
                cases@,
                idx as nat,
                bound_rank as nat,
                strict,
                spec_ns_view(lex_acc@),
                spec_ns_view(sloppy_fn_acc@),
                spec_ns_view(var_acc@),
            ) == spec_collect_switch_decls(
                prog@,
                cases@,
                0,
                bound_rank as nat,
                strict,
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
                Seq::<SpecNameSpan>::empty(),
            ),
        decreases n - idx,
    {
        proof {
            assert(stmt_seq_bounded(prog@.stmts, cases@[idx as int].consequent@, bound_rank as nat));
        }
        collect_block_decls_into(
            prog,
            cases[idx].consequent.as_slice(),
            bound_rank,
            strict,
            &mut lex_acc,
            &mut sloppy_fn_acc,
            &mut var_acc,
        );
        idx = idx + 1;
    }
    (lex_acc, sloppy_fn_acc, var_acc)
}

// ---------------------------------------------------------------------------------------
// Label & Context Tracking (`EarlyCtx`)
// ---------------------------------------------------------------------------------------

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct LabelEntry {
    pub labeled_stmt_id: StmtId,
    pub is_iteration: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EarlyCtx {
    pub strict: bool,
    pub in_function: bool,
    pub allow_new_target: bool,
    pub in_async: bool,
    pub in_generator: bool,
    pub in_formal_params: bool,
    pub in_iteration: bool,
    pub in_switch: bool,
    pub labels: Vec<LabelEntry>,
}

pub struct SpecEarlyCtx {
    pub strict: bool,
    pub in_function: bool,
    pub allow_new_target: bool,
    pub in_async: bool,
    pub in_generator: bool,
    pub in_formal_params: bool,
    pub in_iteration: bool,
    pub in_switch: bool,
    pub labels: Seq<LabelEntry>,
}

impl View for EarlyCtx {
    type V = SpecEarlyCtx;

    open spec fn view(&self) -> SpecEarlyCtx {
        SpecEarlyCtx {
            strict: self.strict,
            in_function: self.in_function,
            allow_new_target: self.allow_new_target,
            in_async: self.in_async,
            in_generator: self.in_generator,
            in_formal_params: self.in_formal_params,
            in_iteration: self.in_iteration,
            in_switch: self.in_switch,
            labels: self.labels@,
        }
    }
}

pub fn clone_labels(s: &[LabelEntry]) -> (v: Vec<LabelEntry>)
    ensures
        v@ == s@,
{
    let n = s.len();
    let mut out: Vec<LabelEntry> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(out@ =~= s@.subrange(0, 0));
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(s[i]);
        i = i + 1;
        proof {
            assert(out@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    out
}

impl EarlyCtx {
    pub fn with_iteration(&self) -> (c: EarlyCtx)
        ensures
            c@ == (SpecEarlyCtx { in_iteration: true, ..self@ }),
    {
        EarlyCtx {
            strict: self.strict,
            in_function: self.in_function,
            allow_new_target: self.allow_new_target,
            in_async: self.in_async,
            in_generator: self.in_generator,
            in_formal_params: self.in_formal_params,
            in_iteration: true,
            in_switch: self.in_switch,
            labels: clone_labels(self.labels.as_slice()),
        }
    }

    pub fn with_switch(&self) -> (c: EarlyCtx)
        ensures
            c@ == (SpecEarlyCtx { in_switch: true, ..self@ }),
    {
        EarlyCtx {
            strict: self.strict,
            in_function: self.in_function,
            allow_new_target: self.allow_new_target,
            in_async: self.in_async,
            in_generator: self.in_generator,
            in_formal_params: self.in_formal_params,
            in_iteration: self.in_iteration,
            in_switch: true,
            labels: clone_labels(self.labels.as_slice()),
        }
    }

    pub fn with_pushed_label(&self, entry: LabelEntry) -> (c: EarlyCtx)
        ensures
            c@ == (SpecEarlyCtx { labels: self@.labels.push(entry), ..self@ }),
    {
        let mut lbs = clone_labels(self.labels.as_slice());
        lbs.push(entry);
        EarlyCtx {
            strict: self.strict,
            in_function: self.in_function,
            allow_new_target: self.allow_new_target,
            in_async: self.in_async,
            in_generator: self.in_generator,
            in_formal_params: self.in_formal_params,
            in_iteration: self.in_iteration,
            in_switch: self.in_switch,
            labels: lbs,
        }
    }
}

pub open spec fn spec_labels_valid(prog: SpecProgram, labels: Seq<LabelEntry>) -> bool {
    forall|k: int| 0 <= k < labels.len() ==> (#[trigger] labels[k]).labeled_stmt_id.0 < prog.stmts.len()
}

pub open spec fn spec_label_entry_name(prog: SpecProgram, entry: LabelEntry) -> Seq<u8> {
    if entry.labeled_stmt_id.0 < prog.stmts.len() {
        match prog.stmts[entry.labeled_stmt_id.0 as int].kind {
            StmtKind::Labeled { label, .. } => label.name@,
            _ => Seq::<u8>::empty(),
        }
    } else {
        Seq::<u8>::empty()
    }
}

pub open spec fn spec_lookup_label_from(
    prog: SpecProgram,
    labels: Seq<LabelEntry>,
    idx: nat,
    target: Seq<u8>,
) -> Option<bool>
    decreases labels.len() - idx,
{
    if idx >= labels.len() {
        None
    } else if spec_label_entry_name(prog, labels[idx as int]) == target {
        Some(labels[idx as int].is_iteration)
    } else {
        spec_lookup_label_from(prog, labels, idx + 1, target)
    }
}

pub fn lookup_label(prog: &Program, labels: &[LabelEntry], target: &[u8]) -> (r: Option<bool>)
    requires
        spec_labels_valid(prog@, labels@),
    ensures
        r == spec_lookup_label_from(prog@, labels@, 0, target@),
{
    let n = labels.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == labels@.len(),
            spec_labels_valid(prog@, labels@),
            spec_lookup_label_from(prog@, labels@, idx as nat, target@)
                == spec_lookup_label_from(prog@, labels@, 0, target@),
        decreases n - idx,
    {
        let entry = labels[idx];
        proof {
            assert(labels@[idx as int].labeled_stmt_id.0 < prog@.stmts.len());
        }
        let matches_name = match &prog.stmts[entry.labeled_stmt_id.0].kind {
            StmtKind::Labeled { label, .. } => bytes_eq(label.name.as_slice(), target),
            _ => {
                let empty: [u8; 0] = [];
                proof {
                    assert(empty@ =~= Seq::<u8>::empty());
                }
                bytes_eq(&empty, target)
            },
        };
        if matches_name {
            return Some(entry.is_iteration);
        }
        idx = idx + 1;
    }
    None
}

pub open spec fn spec_is_iteration_target(prog: SpecProgram, sid: StmtId) -> bool
    decreases
        if sid.0 < prog.stmts.len() { (prog.stmts[sid.0 as int].rank as int) + 1 } else { 0int },
{
    if sid.0 >= prog.stmts.len() {
        false
    } else {
        let srank = prog.stmts[sid.0 as int].rank as nat;
        match prog.stmts[sid.0 as int].kind {
            StmtKind::While { .. }
            | StmtKind::DoWhile { .. }
            | StmtKind::For { .. }
            | StmtKind::ForIn { .. }
            | StmtKind::ForOf { .. } => true,
            StmtKind::Labeled { body, .. } => {
                if body.0 < prog.stmts.len() && (prog.stmts[body.0 as int].rank as nat) < srank {
                    spec_is_iteration_target(prog, body)
                } else {
                    false
                }
            },
            _ => false,
        }
    }
}

pub fn is_iteration_target(prog: &Program, sid0: StmtId) -> (r: bool)
    requires
        prog.wf(),
        sid0.0 < prog@.stmts.len(),
    ensures
        r == spec_is_iteration_target(prog@, sid0),
{
    let mut cur = sid0;
    loop
        invariant
            prog.wf(),
            cur.0 < prog@.stmts.len(),
            spec_is_iteration_target(prog@, cur) == spec_is_iteration_target(prog@, sid0),
        decreases prog@.stmts[cur.0 as int].rank,
    {
        match &prog.stmts[cur.0].kind {
            StmtKind::While { .. }
            | StmtKind::DoWhile { .. }
            | StmtKind::For { .. }
            | StmtKind::ForIn { .. }
            | StmtKind::ForOf { .. } => {
                return true;
            },
            StmtKind::Labeled { body, .. } => {
                cur = *body;
            },
            _ => {
                return false;
            },
        }
    }
}

// ---------------------------------------------------------------------------------------
// Formal Parameters Static Semantics (`IsSimpleParameterList`, Bindings & Duplicates)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_is_simple_params_from(params: Seq<Param>, idx: nat) -> bool
    decreases params.len() - idx,
{
    if idx >= params.len() {
        true
    } else {
        let p = params[idx as int];
        !p.is_rest && (p.default is None) && spec_is_simple_params_from(params, idx + 1)
    }
}

pub fn is_simple_params(params: &[Param]) -> (r: bool)
    ensures
        r == spec_is_simple_params_from(params@, 0),
{
    let n = params.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == params@.len(),
            spec_is_simple_params_from(params@, 0) == spec_is_simple_params_from(params@, idx as nat),
        decreases n - idx,
    {
        if params[idx].is_rest || params[idx].default.is_some() {
            return false;
        }
        idx = idx + 1;
    }
    true
}

pub open spec fn spec_collect_param_names(
    params: Seq<Param>,
    idx: nat,
    strict: bool,
    in_async: bool,
    in_generator: bool,
    acc: Seq<SpecNameSpan>,
) -> Result<Seq<SpecNameSpan>, SyntaxDiagnostic>
    decreases params.len() - idx,
{
    if idx >= params.len() {
        Ok(acc)
    } else {
        let p = params[idx as int];
        match spec_check_binding_ident(p.name, strict, in_async, in_generator, false) {
            Err(e) => Err(e),
            Ok(()) => spec_collect_param_names(
                params,
                idx + 1,
                strict,
                in_async,
                in_generator,
                acc.push(SpecNameSpan { name: p.name.name@, span: p.name.span }),
            ),
        }
    }
}

pub fn collect_param_names(
    params: &[Param],
    strict: bool,
    in_async: bool,
    in_generator: bool,
) -> (r: Result<Vec<NameSpan>, SyntaxDiagnostic>)
    ensures
        match r {
            Ok(v) => {
                spec_collect_param_names(
                    params@,
                    0,
                    strict,
                    in_async,
                    in_generator,
                    Seq::<SpecNameSpan>::empty(),
                ) == Ok::<Seq<SpecNameSpan>, SyntaxDiagnostic>(spec_ns_view(v@))
            },
            Err(e) => {
                spec_collect_param_names(
                    params@,
                    0,
                    strict,
                    in_async,
                    in_generator,
                    Seq::<SpecNameSpan>::empty(),
                ) == Err(e)
            },
        },
{
    let n = params.len();
    let mut acc: Vec<NameSpan> = Vec::new();
    let mut idx: usize = 0;
    proof {
        assert(spec_ns_view(acc@) =~= Seq::<SpecNameSpan>::empty());
    }
    while idx < n
        invariant
            idx <= n,
            n == params@.len(),
            spec_collect_param_names(
                params@,
                idx as nat,
                strict,
                in_async,
                in_generator,
                spec_ns_view(acc@),
            ) == spec_collect_param_names(
                params@,
                0,
                strict,
                in_async,
                in_generator,
                Seq::<SpecNameSpan>::empty(),
            ),
        decreases n - idx,
    {
        let p = &params[idx];
        match check_binding_ident(&p.name, strict, in_async, in_generator, false) {
            Err(e) => {
                return Err(e);
            },
            Ok(()) => {
                let ns = make_name_span(&p.name);
                let ghost old_s = acc@;
                let ghost g_ns = ns;
                acc.push(ns);
                proof {
                    lemma_ns_push_view(old_s, g_ns);
                }
                idx = idx + 1;
            },
        }
    }
    Ok(acc)
}

// ---------------------------------------------------------------------------------------
// Quantifier-Free Recursive AST Early-Error Spec (`decreases (rank, phase, remaining)`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_check_prop_key(
    prog: SpecProgram,
    key: PropKeyAst,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
    span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, 0nat,
{
    match key {
        PropKeyAst::Ident(_) => Ok(()),
        PropKeyAst::StringLit { has_legacy_octal_escape, .. } => {
            if ctx.strict && has_legacy_octal_escape {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::EarlyStrictLegacyOctal, span })
            } else {
                Ok(())
            }
        },
        PropKeyAst::NumberLit { has_legacy_octal_or_leading_zero, .. } => {
            if ctx.strict && has_legacy_octal_or_leading_zero {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::EarlyStrictLegacyOctal, span })
            } else {
                Ok(())
            }
        },
        PropKeyAst::Computed(cid) => {
            if cid.0 < prog.exprs.len() && (prog.exprs[cid.0 as int].rank as nat) < bound_rank {
                spec_check_expr(prog, cid, ctx)
            } else {
                Ok(())
            }
        },
    }
}

pub open spec fn spec_check_param_defaults(
    prog: SpecProgram,
    params: Seq<Param>,
    idx: nat,
    bound_rank: nat,
    param_ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, params.len() - idx + 1,
{
    if idx >= params.len() {
        Ok(())
    } else {
        match params[idx as int].default {
            Some(did) => {
                let d_res = if did.0 < prog.exprs.len()
                    && (prog.exprs[did.0 as int].rank as nat) < bound_rank
                {
                    spec_check_expr(prog, did, param_ctx)
                } else {
                    Ok(())
                };
                match d_res {
                    Err(e) => Err(e),
                    Ok(()) => spec_check_param_defaults(prog, params, idx + 1, bound_rank, param_ctx),
                }
            },
            None => spec_check_param_defaults(prog, params, idx + 1, bound_rank, param_ctx),
        }
    }
}

pub open spec fn spec_check_function_common(
    prog: SpecProgram,
    inner_name: Option<Ident>,
    params: Seq<Param>,
    body: Seq<StmtId>,
    bound_rank: nat,
    outer_strict: bool,
    body_has_use_strict: bool,
    has_directive_octal_escape: bool,
    is_async: bool,
    is_generator: bool,
    always_unique_params: bool,
    allow_new_target: bool,
    fn_span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 3nat, 0nat,
{
    let fn_strict = outer_strict || body_has_use_strict;
    let simple = spec_is_simple_params_from(params, 0);
    if body_has_use_strict && !simple {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyUseStrictWithNonSimpleParams,
            span: fn_span,
        })
    } else if fn_strict && has_directive_octal_escape {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: fn_span,
        })
    } else {
        let name_chk = match inner_name {
            Some(nm) => spec_check_binding_ident(nm, fn_strict, is_async, is_generator, false),
            None => Ok(()),
        };
        match name_chk {
            Err(e) => Err(e),
            Ok(()) => match spec_collect_param_names(
                params,
                0,
                fn_strict,
                is_async,
                is_generator,
                Seq::<SpecNameSpan>::empty(),
            ) {
                Err(e) => Err(e),
                Ok(param_names) => {
                    let dup_chk = if fn_strict || always_unique_params || !simple {
                        match spec_find_duplicate_name(param_names) {
                            Some(sp) => Err(SyntaxDiagnostic {
                                kind: DiagnosticKind::EarlyDuplicateParamName,
                                span: sp,
                            }),
                            None => Ok(()),
                        }
                    } else {
                        Ok(())
                    };
                    match dup_chk {
                        Err(e) => Err(e),
                        Ok(()) => {
                            let param_ctx = SpecEarlyCtx {
                                strict: fn_strict,
                                in_function: true,
                                allow_new_target,
                                in_async: is_async,
                                in_generator: is_generator,
                                in_formal_params: true,
                                in_iteration: false,
                                in_switch: false,
                                labels: Seq::<LabelEntry>::empty(),
                            };
                            match spec_check_param_defaults(prog, params, 0, bound_rank, param_ctx) {
                                Err(e) => Err(e),
                                Ok(()) => {
                                    let (lex_names, var_names) = spec_collect_toplevel_decls(
                                        prog,
                                        body,
                                        0,
                                        bound_rank,
                                        Seq::<SpecNameSpan>::empty(),
                                        Seq::<SpecNameSpan>::empty(),
                                    );
                                    match spec_find_duplicate_name(lex_names) {
                                        Some(sp) => Err(SyntaxDiagnostic {
                                            kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                            span: sp,
                                        }),
                                        None => match spec_find_collision(lex_names, var_names) {
                                            Some(sp) => Err(SyntaxDiagnostic {
                                                kind: DiagnosticKind::EarlyLexicalVarCollision,
                                                span: sp,
                                            }),
                                            None => match spec_find_collision(param_names, lex_names) {
                                                Some(sp) => Err(SyntaxDiagnostic {
                                                    kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                                    span: sp,
                                                }),
                                                None => {
                                                    let body_ctx = SpecEarlyCtx {
                                                        strict: fn_strict,
                                                        in_function: true,
                                                        allow_new_target,
                                                        in_async: is_async,
                                                        in_generator: is_generator,
                                                        in_formal_params: false,
                                                        in_iteration: false,
                                                        in_switch: false,
                                                        labels: Seq::<LabelEntry>::empty(),
                                                    };
                                                    spec_check_stmt_list(prog, body, 0, bound_rank, body_ctx)
                                                },
                                            },
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            },
        }
    }
}

pub open spec fn spec_check_setter_body(
    prog: SpecProgram,
    param: Param,
    body: Seq<StmtId>,
    bound_rank: nat,
    outer_strict: bool,
    body_has_use_strict: bool,
    has_directive_octal_escape: bool,
    fn_span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 3nat, 0nat,
{
    let fn_strict = outer_strict || body_has_use_strict;
    let simple = !param.is_rest && (param.default is None);
    if body_has_use_strict && !simple {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyUseStrictWithNonSimpleParams,
            span: fn_span,
        })
    } else if fn_strict && has_directive_octal_escape {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: fn_span,
        })
    } else {
        match spec_check_binding_ident(param.name, fn_strict, false, false, false) {
            Err(e) => Err(e),
            Ok(()) => {
                let def_chk = match param.default {
                    Some(did) => {
                        let param_ctx = SpecEarlyCtx {
                            strict: fn_strict,
                            in_function: true,
                            allow_new_target: true,
                            in_async: false,
                            in_generator: false,
                            in_formal_params: true,
                            in_iteration: false,
                            in_switch: false,
                            labels: Seq::<LabelEntry>::empty(),
                        };
                        if did.0 < prog.exprs.len()
                            && (prog.exprs[did.0 as int].rank as nat) < bound_rank
                        {
                            spec_check_expr(prog, did, param_ctx)
                        } else {
                            Ok(())
                        }
                    },
                    None => Ok(()),
                };
                match def_chk {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let (lex_names, var_names) = spec_collect_toplevel_decls(
                            prog,
                            body,
                            0,
                            bound_rank,
                            Seq::<SpecNameSpan>::empty(),
                            Seq::<SpecNameSpan>::empty(),
                        );
                        let p_seq = seq![SpecNameSpan {
                            name: param.name.name@,
                            span: param.name.span,
                        }];
                        match spec_find_duplicate_name(lex_names) {
                            Some(sp) => Err(SyntaxDiagnostic {
                                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                span: sp,
                            }),
                            None => match spec_find_collision(lex_names, var_names) {
                                Some(sp) => Err(SyntaxDiagnostic {
                                    kind: DiagnosticKind::EarlyLexicalVarCollision,
                                    span: sp,
                                }),
                                None => match spec_find_collision(p_seq, lex_names) {
                                    Some(sp) => Err(SyntaxDiagnostic {
                                        kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                        span: sp,
                                    }),
                                    None => {
                                        let body_ctx = SpecEarlyCtx {
                                            strict: fn_strict,
                                            in_function: true,
                                            allow_new_target: true,
                                            in_async: false,
                                            in_generator: false,
                                            in_formal_params: false,
                                            in_iteration: false,
                                            in_switch: false,
                                            labels: Seq::<LabelEntry>::empty(),
                                        };
                                        spec_check_stmt_list(prog, body, 0, bound_rank, body_ctx)
                                    },
                                },
                            },
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn spec_check_arrow_expr(
    prog: SpecProgram,
    params: Seq<Param>,
    body: ArrowBody,
    is_async: bool,
    erank: nat,
    ctx: SpecEarlyCtx,
    span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases erank, 4nat, 0nat,
{
    let p_async = ctx.in_async || is_async;
    let p_gen = ctx.in_generator;
    match body {
        ArrowBody::Block { stmts, has_use_strict, has_directive_octal_escape } => {
            let fn_strict = ctx.strict || has_use_strict;
            match spec_collect_param_names(
                params,
                0,
                fn_strict,
                p_async,
                p_gen,
                Seq::<SpecNameSpan>::empty(),
            ) {
                Err(err) => Err(err),
                Ok(_) => {
                    let outer_param_ctx = SpecEarlyCtx {
                        strict: fn_strict,
                        in_function: true,
                        allow_new_target: ctx.allow_new_target,
                        in_async: p_async,
                        in_generator: p_gen,
                        in_formal_params: true,
                        in_iteration: false,
                        in_switch: false,
                        labels: Seq::<LabelEntry>::empty(),
                    };
                    match spec_check_param_defaults(prog, params, 0, erank, outer_param_ctx) {
                        Err(err) => Err(err),
                        Ok(()) => spec_check_function_common(
                            prog,
                            None,
                            params,
                            stmts@,
                            erank,
                            ctx.strict,
                            has_use_strict,
                            has_directive_octal_escape,
                            is_async,
                            false,
                            true,
                            ctx.allow_new_target,
                            span,
                        ),
                    }
                },
            }
        },
        ArrowBody::Expr(body_expr) => {
            match spec_collect_param_names(
                params,
                0,
                ctx.strict,
                p_async,
                p_gen,
                Seq::<SpecNameSpan>::empty(),
            ) {
                Err(err) => Err(err),
                Ok(param_names) => match spec_find_duplicate_name(param_names) {
                    Some(sp) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyDuplicateParamName,
                        span: sp,
                    }),
                    None => {
                        let param_ctx = SpecEarlyCtx {
                            strict: ctx.strict,
                            in_function: true,
                            allow_new_target: ctx.allow_new_target,
                            in_async: p_async,
                            in_generator: p_gen,
                            in_formal_params: true,
                            in_iteration: false,
                            in_switch: false,
                            labels: Seq::<LabelEntry>::empty(),
                        };
                        match spec_check_param_defaults(prog, params, 0, erank, param_ctx) {
                            Err(err) => Err(err),
                            Ok(()) => {
                                let body_ctx = SpecEarlyCtx {
                                    strict: ctx.strict,
                                    in_function: true,
                                    allow_new_target: ctx.allow_new_target,
                                    in_async: is_async,
                                    in_generator: false,
                                    in_formal_params: false,
                                    in_iteration: false,
                                    in_switch: false,
                                    labels: Seq::<LabelEntry>::empty(),
                                };
                                if body_expr.0 < prog.exprs.len()
                                    && (prog.exprs[body_expr.0 as int].rank as nat) < erank
                                {
                                    spec_check_expr(prog, body_expr, body_ctx)
                                } else {
                                    Ok(())
                                }
                            },
                        }
                    },
                },
            }
        },
    }
}

pub open spec fn spec_check_array_elems(
    prog: SpecProgram,
    elems: Seq<ArrayElem>,
    idx: nat,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, elems.len() - idx + 1,
{
    if idx >= elems.len() {
        Ok(())
    } else {
        let step_res = match elems[idx as int] {
            ArrayElem::Hole => Ok(()),
            ArrayElem::Elem(id) => {
                if id.0 < prog.exprs.len() && (prog.exprs[id.0 as int].rank as nat) < bound_rank {
                    spec_check_expr(prog, id, ctx)
                } else {
                    Ok(())
                }
            },
            ArrayElem::Spread(id) => {
                if id.0 < prog.exprs.len() && (prog.exprs[id.0 as int].rank as nat) < bound_rank {
                    spec_check_expr(prog, id, ctx)
                } else {
                    Ok(())
                }
            },
        };
        match step_res {
            Err(e) => Err(e),
            Ok(()) => spec_check_array_elems(prog, elems, idx + 1, bound_rank, ctx),
        }
    }
}

pub open spec fn spec_check_call_args(
    prog: SpecProgram,
    args: Seq<CallArg>,
    idx: nat,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, args.len() - idx + 1,
{
    if idx >= args.len() {
        Ok(())
    } else {
        let step_res = match args[idx as int] {
            CallArg::Arg(id) => {
                if id.0 < prog.exprs.len() && (prog.exprs[id.0 as int].rank as nat) < bound_rank {
                    spec_check_expr(prog, id, ctx)
                } else {
                    Ok(())
                }
            },
            CallArg::Spread(id) => {
                if id.0 < prog.exprs.len() && (prog.exprs[id.0 as int].rank as nat) < bound_rank {
                    spec_check_expr(prog, id, ctx)
                } else {
                    Ok(())
                }
            },
        };
        match step_res {
            Err(e) => Err(e),
            Ok(()) => spec_check_call_args(prog, args, idx + 1, bound_rank, ctx),
        }
    }
}

pub open spec fn spec_check_one_obj_prop(
    prog: SpecProgram,
    prop: ObjPropKind,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
    obj_span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 4nat, 0nat,
{
    match prop {
        ObjPropKind::Init { key, value, is_shorthand, shorthand_ident } => {
            let sh_chk = if is_shorthand {
                match shorthand_ident {
                    Some(id) => spec_check_ident_ref(id, ctx.strict, ctx.in_async, ctx.in_generator),
                    None => Ok(()),
                }
            } else {
                Ok(())
            };
            match sh_chk {
                Err(e) => Err(e),
                Ok(()) => match spec_check_prop_key(prog, key, bound_rank, ctx, obj_span) {
                    Err(e) => Err(e),
                    Ok(()) => {
                        if value.0 < prog.exprs.len()
                            && (prog.exprs[value.0 as int].rank as nat) < bound_rank
                        {
                            spec_check_expr(prog, value, ctx)
                        } else {
                            Ok(())
                        }
                    },
                },
            }
        },
        ObjPropKind::Method {
            key,
            params,
            body,
            is_async,
            is_generator,
            body_has_use_strict,
            has_directive_octal_escape,
            span,
        } => match spec_check_prop_key(prog, key, bound_rank, ctx, span) {
            Err(e) => Err(e),
            Ok(()) => spec_check_function_common(
                prog,
                None,
                params@,
                body@,
                bound_rank,
                ctx.strict,
                body_has_use_strict,
                has_directive_octal_escape,
                is_async,
                is_generator,
                true,
                true,
                span,
            ),
        },
        ObjPropKind::Getter { key, body, body_has_use_strict, has_directive_octal_escape, span } => {
            match spec_check_prop_key(prog, key, bound_rank, ctx, span) {
                Err(e) => Err(e),
                Ok(()) => spec_check_function_common(
                    prog,
                    None,
                    Seq::<Param>::empty(),
                    body@,
                    bound_rank,
                    ctx.strict,
                    body_has_use_strict,
                    has_directive_octal_escape,
                    false,
                    false,
                    true,
                    true,
                    span,
                ),
            }
        },
        ObjPropKind::Setter {
            key,
            param,
            body,
            body_has_use_strict,
            has_directive_octal_escape,
            span,
        } => match spec_check_prop_key(prog, key, bound_rank, ctx, span) {
            Err(e) => Err(e),
            Ok(()) => spec_check_setter_body(
                prog,
                param,
                body@,
                bound_rank,
                ctx.strict,
                body_has_use_strict,
                has_directive_octal_escape,
                span,
            ),
        },
        ObjPropKind::Spread(id) => {
            if id.0 < prog.exprs.len() && (prog.exprs[id.0 as int].rank as nat) < bound_rank {
                spec_check_expr(prog, id, ctx)
            } else {
                Ok(())
            }
        },
    }
}

pub open spec fn spec_check_obj_props(
    prog: SpecProgram,
    props: Seq<ObjPropKind>,
    idx: nat,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
    obj_span: Span,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 4nat, props.len() - idx + 1,
{
    if idx >= props.len() {
        Ok(())
    } else {
        match spec_check_one_obj_prop(prog, props[idx as int], bound_rank, ctx, obj_span) {
            Err(e) => Err(e),
            Ok(()) => spec_check_obj_props(prog, props, idx + 1, bound_rank, ctx, obj_span),
        }
    }
}

pub open spec fn spec_check_var_declarators(
    prog: SpecProgram,
    decls: Seq<VarDeclarator>,
    idx: nat,
    bound_rank: nat,
    is_let_or_const: bool,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, decls.len() - idx + 1,
{
    if idx >= decls.len() {
        Ok(())
    } else {
        let d = decls[idx as int];
        match spec_check_binding_ident(d.name, ctx.strict, ctx.in_async, ctx.in_generator, is_let_or_const) {
            Err(e) => Err(e),
            Ok(()) => {
                let init_res = match d.init {
                    Some(eid) => {
                        if eid.0 < prog.exprs.len()
                            && (prog.exprs[eid.0 as int].rank as nat) < bound_rank
                        {
                            spec_check_expr(prog, eid, ctx)
                        } else {
                            Ok(())
                        }
                    },
                    None => Ok(()),
                };
                match init_res {
                    Err(e) => Err(e),
                    Ok(()) => spec_check_var_declarators(
                        prog,
                        decls,
                        idx + 1,
                        bound_rank,
                        is_let_or_const,
                        ctx,
                    ),
                }
            },
        }
    }
}

pub open spec fn spec_check_switch_cases(
    prog: SpecProgram,
    cases: Seq<SwitchCase>,
    idx: nat,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 3nat, cases.len() - idx,
{
    if idx >= cases.len() {
        Ok(())
    } else {
        let c = cases[idx as int];
        let test_res = match c.test {
            Some(tid) => {
                if tid.0 < prog.exprs.len()
                    && (prog.exprs[tid.0 as int].rank as nat) < bound_rank
                {
                    spec_check_expr(prog, tid, ctx)
                } else {
                    Ok(())
                }
            },
            None => Ok(()),
        };
        match test_res {
            Err(e) => Err(e),
            Ok(()) => match spec_check_stmt_list(prog, c.consequent@, 0, bound_rank, ctx) {
                Err(e) => Err(e),
                Ok(()) => spec_check_switch_cases(prog, cases, idx + 1, bound_rank, ctx),
            },
        }
    }
}

pub open spec fn spec_check_expr(
    prog: SpecProgram,
    eid: ExprId,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases
        if eid.0 < prog.exprs.len() { prog.exprs[eid.0 as int].rank as nat } else { 0nat },
        5nat,
        0nat,
{
    if eid.0 >= prog.exprs.len() {
        Ok(())
    } else {
        let e = prog.exprs[eid.0 as int];
        let erank = e.rank as nat;
        match e.kind {
            ExprKind::This | ExprKind::Null | ExprKind::Bool(_) => Ok(()),
            ExprKind::TemplateNoSub { has_invalid_escape, .. } => {
                if has_invalid_escape {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::InvalidUnicodeEscape,
                        span: e.span,
                    })
                } else {
                    Ok(())
                }
            },
            ExprKind::Number { has_legacy_octal_or_leading_zero, .. } => {
                if ctx.strict && has_legacy_octal_or_leading_zero {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyStrictLegacyOctal,
                        span: e.span,
                    })
                } else {
                    Ok(())
                }
            },
            ExprKind::StringLit { has_legacy_octal_escape, .. } => {
                if ctx.strict && has_legacy_octal_escape {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyStrictLegacyOctal,
                        span: e.span,
                    })
                } else {
                    Ok(())
                }
            },
            ExprKind::Ident(ident) => {
                spec_check_ident_ref(ident, ctx.strict, ctx.in_async, ctx.in_generator)
            },
            ExprKind::Paren(inner) => {
                if inner.0 < prog.exprs.len() && (prog.exprs[inner.0 as int].rank as nat) < erank {
                    spec_check_expr(prog, inner, ctx)
                } else {
                    Ok(())
                }
            },
            ExprKind::Array(elems) => spec_check_array_elems(prog, elems@, 0, erank, ctx),
            ExprKind::Object(props) => {
                if spec_has_duplicate_proto_init(props@, 0, false) {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyDuplicateProtoProperty,
                        span: e.span,
                    })
                } else {
                    spec_check_obj_props(prog, props@, 0, erank, ctx, e.span)
                }
            },
            ExprKind::Member { object, .. } => {
                if object.0 < prog.exprs.len() && (prog.exprs[object.0 as int].rank as nat) < erank {
                    spec_check_expr(prog, object, ctx)
                } else {
                    Ok(())
                }
            },
            ExprKind::ComputedMember { object, index, .. } => {
                let obj_res = if object.0 < prog.exprs.len()
                    && (prog.exprs[object.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, object, ctx)
                } else {
                    Ok(())
                };
                match obj_res {
                    Err(err) => Err(err),
                    Ok(()) => {
                        if index.0 < prog.exprs.len()
                            && (prog.exprs[index.0 as int].rank as nat) < erank
                        {
                            spec_check_expr(prog, index, ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            ExprKind::Call { callee, args, .. } => {
                let c_res = if callee.0 < prog.exprs.len()
                    && (prog.exprs[callee.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, callee, ctx)
                } else {
                    Ok(())
                };
                match c_res {
                    Err(err) => Err(err),
                    Ok(()) => spec_check_call_args(prog, args@, 0, erank, ctx),
                }
            },
            ExprKind::New { callee, args } => {
                let c_res = if callee.0 < prog.exprs.len()
                    && (prog.exprs[callee.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, callee, ctx)
                } else {
                    Ok(())
                };
                match c_res {
                    Err(err) => Err(err),
                    Ok(()) => spec_check_call_args(prog, args@, 0, erank, ctx),
                }
            },
            ExprKind::NewTarget => {
                if !ctx.allow_new_target {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyNewTargetOutsideFunction,
                        span: e.span,
                    })
                } else {
                    Ok(())
                }
            },
            ExprKind::Update { arg, .. } => {
                let a_res = if arg.0 < prog.exprs.len()
                    && (prog.exprs[arg.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, arg, ctx)
                } else {
                    Ok(())
                };
                match a_res {
                    Err(err) => Err(err),
                    Ok(()) => spec_check_assignment_target(prog, arg, ctx.strict, true),
                }
            },
            ExprKind::Unary { op, arg } => {
                let a_res = if arg.0 < prog.exprs.len()
                    && (prog.exprs[arg.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, arg, ctx)
                } else {
                    Ok(())
                };
                match a_res {
                    Err(err) => Err(err),
                    Ok(()) => {
                        if op == UnaryOp::Delete && ctx.strict {
                            let unwrapped = spec_unwrap_parens(prog, arg);
                            if unwrapped.0 < prog.exprs.len() {
                                match prog.exprs[unwrapped.0 as int].kind {
                                    ExprKind::Ident(_) => Err(SyntaxDiagnostic {
                                        kind: DiagnosticKind::EarlyStrictDeleteIdentifier,
                                        span: e.span,
                                    }),
                                    _ => Ok(()),
                                }
                            } else {
                                Ok(())
                            }
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            ExprKind::Await(arg) => {
                if !ctx.in_async {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyAwaitOutsideAsync,
                        span: e.span,
                    })
                } else if ctx.in_formal_params {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyAwaitInFormalParams,
                        span: e.span,
                    })
                } else if arg.0 < prog.exprs.len() && (prog.exprs[arg.0 as int].rank as nat) < erank {
                    spec_check_expr(prog, arg, ctx)
                } else {
                    Ok(())
                }
            },
            ExprKind::Yield { arg, .. } => {
                if !ctx.in_generator {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyYieldOutsideGenerator,
                        span: e.span,
                    })
                } else if ctx.in_formal_params {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyYieldInFormalParams,
                        span: e.span,
                    })
                } else {
                    match arg {
                        Some(aid) => {
                            if aid.0 < prog.exprs.len()
                                && (prog.exprs[aid.0 as int].rank as nat) < erank
                            {
                                spec_check_expr(prog, aid, ctx)
                            } else {
                                Ok(())
                            }
                        },
                        None => Ok(()),
                    }
                }
            },
            ExprKind::Binary { left, right, .. } => {
                let l_res = if left.0 < prog.exprs.len()
                    && (prog.exprs[left.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, left, ctx)
                } else {
                    Ok(())
                };
                match l_res {
                    Err(err) => Err(err),
                    Ok(()) => {
                        if right.0 < prog.exprs.len()
                            && (prog.exprs[right.0 as int].rank as nat) < erank
                        {
                            spec_check_expr(prog, right, ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            ExprKind::Sequence { left, right } => {
                let l_res = if left.0 < prog.exprs.len()
                    && (prog.exprs[left.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, left, ctx)
                } else {
                    Ok(())
                };
                match l_res {
                    Err(err) => Err(err),
                    Ok(()) => {
                        if right.0 < prog.exprs.len()
                            && (prog.exprs[right.0 as int].rank as nat) < erank
                        {
                            spec_check_expr(prog, right, ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            ExprKind::Conditional { cond, consequent, alternate } => {
                let c_res = if cond.0 < prog.exprs.len()
                    && (prog.exprs[cond.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, cond, ctx)
                } else {
                    Ok(())
                };
                match c_res {
                    Err(err) => Err(err),
                    Ok(()) => {
                        let q_res = if consequent.0 < prog.exprs.len()
                            && (prog.exprs[consequent.0 as int].rank as nat) < erank
                        {
                            spec_check_expr(prog, consequent, ctx)
                        } else {
                            Ok(())
                        };
                        match q_res {
                            Err(err) => Err(err),
                            Ok(()) => {
                                if alternate.0 < prog.exprs.len()
                                    && (prog.exprs[alternate.0 as int].rank as nat) < erank
                                {
                                    spec_check_expr(prog, alternate, ctx)
                                } else {
                                    Ok(())
                                }
                            },
                        }
                    },
                }
            },
            ExprKind::Assign { op, left, right } => {
                let l_res = if left.0 < prog.exprs.len()
                    && (prog.exprs[left.0 as int].rank as nat) < erank
                {
                    spec_check_expr(prog, left, ctx)
                } else {
                    Ok(())
                };
                match l_res {
                    Err(err) => Err(err),
                    Ok(()) => match spec_check_assignment_target(
                        prog,
                        left,
                        ctx.strict,
                        !spec_is_logical_assign_op(op),
                    ) {
                        Err(err) => Err(err),
                        Ok(()) => {
                            if right.0 < prog.exprs.len()
                                && (prog.exprs[right.0 as int].rank as nat) < erank
                            {
                                spec_check_expr(prog, right, ctx)
                            } else {
                                Ok(())
                            }
                        },
                    },
                }
            },
            ExprKind::FunctionExpr {
                name,
                params,
                body,
                is_async,
                is_generator,
                body_has_use_strict,
                has_directive_octal_escape,
            } => spec_check_function_common(
                prog,
                name,
                params@,
                body@,
                erank,
                ctx.strict,
                body_has_use_strict,
                has_directive_octal_escape,
                is_async,
                is_generator,
                false,
                true,
                e.span,
            ),
            ExprKind::ArrowFunction { params, body, is_async } => {
                spec_check_arrow_expr(prog, params@, body, is_async, erank, ctx, e.span)
            },
        }
    }
}

pub open spec fn spec_check_block_stmt_list(
    prog: SpecProgram,
    ids: Seq<StmtId>,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 3nat, 0nat,
{
    let (lex, sloppy_fn, vars) = spec_collect_block_decls(
        prog,
        ids,
        0,
        bound_rank,
        ctx.strict,
        Seq::<SpecNameSpan>::empty(),
        Seq::<SpecNameSpan>::empty(),
        Seq::<SpecNameSpan>::empty(),
    );
    match spec_validate_block_triple(lex, sloppy_fn, vars) {
        Err(e) => Err(e),
        Ok(()) => spec_check_stmt_list(prog, ids, 0, bound_rank, ctx),
    }
}

pub open spec fn spec_check_for_stmt(
    prog: SpecProgram,
    init: ForInit,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    srank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases srank, 4nat, 0nat,
{
    let init_chk = match init {
        ForInit::None => Ok(()),
        ForInit::Expr(e) => {
            if e.0 < prog.exprs.len() && (prog.exprs[e.0 as int].rank as nat) < srank {
                spec_check_expr(prog, e, ctx)
            } else {
                Ok(())
            }
        },
        ForInit::VarDecl { kind, decls } => {
            let is_lc = kind != VarDeclKind::Var;
            match spec_check_var_declarators(prog, decls@, 0, srank, is_lc, ctx) {
                Err(e) => Err(e),
                Ok(()) => {
                    if is_lc {
                        let head_lex = spec_push_var_decls(decls@, 0, Seq::<SpecNameSpan>::empty());
                        match spec_find_duplicate_name(head_lex) {
                            Some(sp) => Err(SyntaxDiagnostic {
                                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                span: sp,
                            }),
                            None => {
                                let body_vars = if body.0 < prog.stmts.len()
                                    && (prog.stmts[body.0 as int].rank as nat) < srank
                                {
                                    spec_collect_var_names_stmt(
                                        prog,
                                        body,
                                        Seq::<SpecNameSpan>::empty(),
                                    )
                                } else {
                                    Seq::<SpecNameSpan>::empty()
                                };
                                match spec_find_collision(head_lex, body_vars) {
                                    Some(sp) => Err(SyntaxDiagnostic {
                                        kind: DiagnosticKind::EarlyLexicalVarCollision,
                                        span: sp,
                                    }),
                                    None => Ok(()),
                                }
                            },
                        }
                    } else {
                        Ok(())
                    }
                },
            }
        },
    };
    match init_chk {
        Err(e) => Err(e),
        Ok(()) => {
            let cond_chk = match cond {
                Some(c) => {
                    if c.0 < prog.exprs.len() && (prog.exprs[c.0 as int].rank as nat) < srank {
                        spec_check_expr(prog, c, ctx)
                    } else {
                        Ok(())
                    }
                },
                None => Ok(()),
            };
            match cond_chk {
                Err(e) => Err(e),
                Ok(()) => {
                    let upd_chk = match update {
                        Some(u) => {
                            if u.0 < prog.exprs.len() && (prog.exprs[u.0 as int].rank as nat) < srank {
                                spec_check_expr(prog, u, ctx)
                            } else {
                                Ok(())
                            }
                        },
                        None => Ok(()),
                    };
                    match upd_chk {
                        Err(e) => Err(e),
                        Ok(()) => {
                            let iter_ctx = SpecEarlyCtx { in_iteration: true, ..ctx };
                            if body.0 < prog.stmts.len()
                                && (prog.stmts[body.0 as int].rank as nat) < srank
                            {
                                spec_check_stmt(prog, body, iter_ctx)
                            } else {
                                Ok(())
                            }
                        },
                    }
                },
            }
        },
    }
}

pub open spec fn spec_check_for_in_of_stmt(
    prog: SpecProgram,
    lhs: ForInOfLhs,
    rhs: ExprId,
    is_await: bool,
    body: StmtId,
    srank: nat,
    span: Span,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases srank, 4nat, 0nat,
{
    if is_await && !ctx.in_async {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyAwaitOutsideAsync,
            span,
        })
    } else {
        let lhs_chk = match lhs {
            ForInOfLhs::VarDecl { kind, name } => {
                let is_lc = kind != VarDeclKind::Var;
                match spec_check_binding_ident(name, ctx.strict, ctx.in_async, ctx.in_generator, is_lc) {
                    Err(e) => Err(e),
                    Ok(()) => {
                        if is_lc {
                            let head_lex = seq![SpecNameSpan { name: name.name@, span: name.span }];
                            let body_vars = if body.0 < prog.stmts.len()
                                && (prog.stmts[body.0 as int].rank as nat) < srank
                            {
                                spec_collect_var_names_stmt(
                                    prog,
                                    body,
                                    Seq::<SpecNameSpan>::empty(),
                                )
                            } else {
                                Seq::<SpecNameSpan>::empty()
                            };
                            match spec_find_collision(head_lex, body_vars) {
                                Some(sp) => Err(SyntaxDiagnostic {
                                    kind: DiagnosticKind::EarlyLexicalVarCollision,
                                    span: sp,
                                }),
                                None => Ok(()),
                            }
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            ForInOfLhs::Expr(e) => {
                let e_res = if e.0 < prog.exprs.len() && (prog.exprs[e.0 as int].rank as nat) < srank {
                    spec_check_expr(prog, e, ctx)
                } else {
                    Ok(())
                };
                match e_res {
                    Err(err) => Err(err),
                    Ok(()) => spec_check_assignment_target(prog, e, ctx.strict, true),
                }
            },
        };
        match lhs_chk {
            Err(e) => Err(e),
            Ok(()) => {
                let rhs_res = if rhs.0 < prog.exprs.len()
                    && (prog.exprs[rhs.0 as int].rank as nat) < srank
                {
                    spec_check_expr(prog, rhs, ctx)
                } else {
                    Ok(())
                };
                match rhs_res {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let iter_ctx = SpecEarlyCtx { in_iteration: true, ..ctx };
                        if body.0 < prog.stmts.len()
                            && (prog.stmts[body.0 as int].rank as nat) < srank
                        {
                            spec_check_stmt(prog, body, iter_ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn spec_check_try_stmt(
    prog: SpecProgram,
    block: Seq<StmtId>,
    catch_clause: Option<CatchClause>,
    finally_block: Option<Vec<StmtId>>,
    srank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases srank, 4nat, 0nat,
{
    match spec_check_block_stmt_list(prog, block, srank, ctx) {
        Err(e) => Err(e),
        Ok(()) => {
            let catch_chk = match catch_clause {
                None => Ok(()),
                Some(cc) => {
                    let param_chk = match cc.param {
                        None => Ok(()),
                        Some(p) => {
                            match spec_check_binding_ident(
                                p,
                                ctx.strict,
                                ctx.in_async,
                                ctx.in_generator,
                                false,
                            ) {
                                Err(e) => Err(e),
                                Ok(()) => {
                                    let (c_lex, c_sloppy, _) = spec_collect_block_decls(
                                        prog,
                                        cc.body@,
                                        0,
                                        srank,
                                        ctx.strict,
                                        Seq::<SpecNameSpan>::empty(),
                                        Seq::<SpecNameSpan>::empty(),
                                        Seq::<SpecNameSpan>::empty(),
                                    );
                                    let p_seq = seq![SpecNameSpan { name: p.name@, span: p.span }];
                                    match spec_find_collision(p_seq, c_lex) {
                                        Some(sp) => Err(SyntaxDiagnostic {
                                            kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                            span: sp,
                                        }),
                                        None => match spec_find_collision(p_seq, c_sloppy) {
                                            Some(sp) => Err(SyntaxDiagnostic {
                                                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                                                span: sp,
                                            }),
                                            None => Ok(()),
                                        },
                                    }
                                },
                            }
                        },
                    };
                    match param_chk {
                        Err(e) => Err(e),
                        Ok(()) => spec_check_block_stmt_list(prog, cc.body@, srank, ctx),
                    }
                },
            };
            match catch_chk {
                Err(e) => Err(e),
                Ok(()) => match finally_block {
                    None => Ok(()),
                    Some(fb) => spec_check_block_stmt_list(prog, fb@, srank, ctx),
                },
            }
        },
    }
}

pub open spec fn spec_check_stmt(
    prog: SpecProgram,
    sid: StmtId,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases
        if sid.0 < prog.stmts.len() { prog.stmts[sid.0 as int].rank as nat } else { 0nat },
        5nat,
        0nat,
{
    if sid.0 >= prog.stmts.len() {
        Ok(())
    } else {
        let s = prog.stmts[sid.0 as int];
        let srank = s.rank as nat;
        match s.kind {
            StmtKind::Empty | StmtKind::Debugger => Ok(()),
            StmtKind::Block(ids) => spec_check_block_stmt_list(prog, ids@, srank, ctx),
            StmtKind::VarDecl { kind, decls } => {
                let is_lc = kind != VarDeclKind::Var;
                spec_check_var_declarators(prog, decls@, 0, srank, is_lc, ctx)
            },
            StmtKind::ExprStmt(eid) => {
                if eid.0 < prog.exprs.len() && (prog.exprs[eid.0 as int].rank as nat) < srank {
                    spec_check_expr(prog, eid, ctx)
                } else {
                    Ok(())
                }
            },
            StmtKind::Throw(eid) => {
                if eid.0 < prog.exprs.len() && (prog.exprs[eid.0 as int].rank as nat) < srank {
                    spec_check_expr(prog, eid, ctx)
                } else {
                    Ok(())
                }
            },
            StmtKind::Return(opt_e) => {
                if !ctx.in_function {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyReturnOutsideFunction,
                        span: s.span,
                    })
                } else {
                    match opt_e {
                        Some(eid) => {
                            if eid.0 < prog.exprs.len()
                                && (prog.exprs[eid.0 as int].rank as nat) < srank
                            {
                                spec_check_expr(prog, eid, ctx)
                            } else {
                                Ok(())
                            }
                        },
                        None => Ok(()),
                    }
                }
            },
            StmtKind::Break(opt_lbl) => match opt_lbl {
                None => {
                    if !ctx.in_iteration && !ctx.in_switch {
                        Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyInvalidBreak,
                            span: s.span,
                        })
                    } else {
                        Ok(())
                    }
                },
                Some(lbl) => match spec_check_ident_ref(lbl, ctx.strict, ctx.in_async, ctx.in_generator) {
                    Err(e) => Err(e),
                    Ok(()) => match spec_lookup_label_from(prog, ctx.labels, 0, lbl.name@) {
                        Some(_) => Ok(()),
                        None => Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyUndefinedLabel,
                            span: lbl.span,
                        }),
                    },
                },
            },
            StmtKind::Continue(opt_lbl) => match opt_lbl {
                None => {
                    if !ctx.in_iteration {
                        Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyInvalidContinue,
                            span: s.span,
                        })
                    } else {
                        Ok(())
                    }
                },
                Some(lbl) => match spec_check_ident_ref(lbl, ctx.strict, ctx.in_async, ctx.in_generator) {
                    Err(e) => Err(e),
                    Ok(()) => match spec_lookup_label_from(prog, ctx.labels, 0, lbl.name@) {
                        Some(true) => Ok(()),
                        Some(false) => Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyNonIterationContinueLabel,
                            span: lbl.span,
                        }),
                        None => Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyUndefinedLabel,
                            span: lbl.span,
                        }),
                    },
                },
            },
            StmtKind::If { cond, consequent, alternate } => {
                let c_res = if cond.0 < prog.exprs.len()
                    && (prog.exprs[cond.0 as int].rank as nat) < srank
                {
                    spec_check_expr(prog, cond, ctx)
                } else {
                    Ok(())
                };
                match c_res {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let q_res = if consequent.0 < prog.stmts.len()
                            && (prog.stmts[consequent.0 as int].rank as nat) < srank
                        {
                            spec_check_stmt(prog, consequent, ctx)
                        } else {
                            Ok(())
                        };
                        match q_res {
                            Err(e) => Err(e),
                            Ok(()) => match alternate {
                                Some(alt) => {
                                    if alt.0 < prog.stmts.len()
                                        && (prog.stmts[alt.0 as int].rank as nat) < srank
                                    {
                                        spec_check_stmt(prog, alt, ctx)
                                    } else {
                                        Ok(())
                                    }
                                },
                                None => Ok(()),
                            },
                        }
                    },
                }
            },
            StmtKind::While { cond, body } => {
                let c_res = if cond.0 < prog.exprs.len()
                    && (prog.exprs[cond.0 as int].rank as nat) < srank
                {
                    spec_check_expr(prog, cond, ctx)
                } else {
                    Ok(())
                };
                match c_res {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let iter_ctx = SpecEarlyCtx { in_iteration: true, ..ctx };
                        if body.0 < prog.stmts.len()
                            && (prog.stmts[body.0 as int].rank as nat) < srank
                        {
                            spec_check_stmt(prog, body, iter_ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            StmtKind::DoWhile { body, cond } => {
                let iter_ctx = SpecEarlyCtx { in_iteration: true, ..ctx };
                let b_res = if body.0 < prog.stmts.len()
                    && (prog.stmts[body.0 as int].rank as nat) < srank
                {
                    spec_check_stmt(prog, body, iter_ctx)
                } else {
                    Ok(())
                };
                match b_res {
                    Err(e) => Err(e),
                    Ok(()) => {
                        if cond.0 < prog.exprs.len()
                            && (prog.exprs[cond.0 as int].rank as nat) < srank
                        {
                            spec_check_expr(prog, cond, ctx)
                        } else {
                            Ok(())
                        }
                    },
                }
            },
            StmtKind::For { init, cond, update, body } => {
                spec_check_for_stmt(prog, init, cond, update, body, srank, ctx)
            },
            StmtKind::ForIn { lhs, rhs, body } => {
                spec_check_for_in_of_stmt(prog, lhs, rhs, false, body, srank, s.span, ctx)
            },
            StmtKind::ForOf { lhs, rhs, is_await, body } => {
                spec_check_for_in_of_stmt(prog, lhs, rhs, is_await, body, srank, s.span, ctx)
            },
            StmtKind::Switch { discriminant, cases } => {
                let d_res = if discriminant.0 < prog.exprs.len()
                    && (prog.exprs[discriminant.0 as int].rank as nat) < srank
                {
                    spec_check_expr(prog, discriminant, ctx)
                } else {
                    Ok(())
                };
                match d_res {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let (lex, sloppy_fn, vars) = spec_collect_switch_decls(
                            prog,
                            cases@,
                            0,
                            srank,
                            ctx.strict,
                            Seq::<SpecNameSpan>::empty(),
                            Seq::<SpecNameSpan>::empty(),
                            Seq::<SpecNameSpan>::empty(),
                        );
                        match spec_validate_block_triple(lex, sloppy_fn, vars) {
                            Err(e) => Err(e),
                            Ok(()) => {
                                let sw_ctx = SpecEarlyCtx { in_switch: true, ..ctx };
                                spec_check_switch_cases(prog, cases@, 0, srank, sw_ctx)
                            },
                        }
                    },
                }
            },
            StmtKind::Try { block, catch_clause, finally_block } => {
                spec_check_try_stmt(prog, block@, catch_clause, finally_block, srank, ctx)
            },
            StmtKind::With { object, body } => {
                if ctx.strict {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyStrictWithStatement,
                        span: s.span,
                    })
                } else {
                    let o_res = if object.0 < prog.exprs.len()
                        && (prog.exprs[object.0 as int].rank as nat) < srank
                    {
                        spec_check_expr(prog, object, ctx)
                    } else {
                        Ok(())
                    };
                    match o_res {
                        Err(e) => Err(e),
                        Ok(()) => {
                            if body.0 < prog.stmts.len()
                                && (prog.stmts[body.0 as int].rank as nat) < srank
                            {
                                spec_check_stmt(prog, body, ctx)
                            } else {
                                Ok(())
                            }
                        },
                    }
                }
            },
            StmtKind::Labeled { label, body } => {
                match spec_check_ident_ref(label, ctx.strict, ctx.in_async, ctx.in_generator) {
                    Err(e) => Err(e),
                    Ok(()) => match spec_lookup_label_from(prog, ctx.labels, 0, label.name@) {
                        Some(_) => Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyDuplicateLabel,
                            span: label.span,
                        }),
                        None => {
                            if ctx.strict && (spec_unwrap_labeled_fn_decl(prog, body) is Some) {
                                Err(SyntaxDiagnostic {
                                    kind: DiagnosticKind::SingleStmtLexicalDecl,
                                    span: s.span,
                                })
                            } else {
                                let is_iter = spec_is_iteration_target(prog, body);
                                let entry = LabelEntry { labeled_stmt_id: sid, is_iteration: is_iter };
                                let next_ctx = SpecEarlyCtx {
                                    labels: ctx.labels.push(entry),
                                    ..ctx
                                };
                                if body.0 < prog.stmts.len()
                                    && (prog.stmts[body.0 as int].rank as nat) < srank
                                {
                                    spec_check_stmt(prog, body, next_ctx)
                                } else {
                                    Ok(())
                                }
                            }
                        },
                    },
                }
            },
            StmtKind::FunctionDecl {
                name,
                params,
                body,
                is_async,
                is_generator,
                body_has_use_strict,
                has_directive_octal_escape,
            } => match spec_check_binding_ident(
                name,
                ctx.strict || body_has_use_strict,
                ctx.in_async,
                ctx.in_generator,
                false,
            ) {
                Err(e) => Err(e),
                Ok(()) => spec_check_function_common(
                    prog,
                    None,
                    params@,
                    body@,
                    srank,
                    ctx.strict,
                    body_has_use_strict,
                    has_directive_octal_escape,
                    is_async,
                    is_generator,
                    false,
                    true,
                    s.span,
                ),
            },
        }
    }
}

pub open spec fn spec_check_stmt_list(
    prog: SpecProgram,
    ids: Seq<StmtId>,
    idx: nat,
    bound_rank: nat,
    ctx: SpecEarlyCtx,
) -> Result<(), SyntaxDiagnostic>
    decreases bound_rank, 2nat, ids.len() - idx + 1,
{
    if idx >= ids.len() {
        Ok(())
    } else {
        let sid = ids[idx as int];
        let s_res = if sid.0 < prog.stmts.len() && (prog.stmts[sid.0 as int].rank as nat) < bound_rank {
            spec_check_stmt(prog, sid, ctx)
        } else {
            Ok(())
        };
        match s_res {
            Err(e) => Err(e),
            Ok(()) => spec_check_stmt_list(prog, ids, idx + 1, bound_rank, ctx),
        }
    }
}

/// Top-level ECMA-262 §16.1.1 Script Static Semantics: Early Errors specification.
pub open spec fn spec_check_early_errors(prog: SpecProgram) -> Result<(), SyntaxDiagnostic> {
    if prog.has_use_strict && prog.has_directive_octal_escape {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: Span { start: 0, end: 0 },
        })
    } else {
        let top_bound = prog.exprs.len() + prog.stmts.len();
        let (lex_names, var_names) = spec_collect_toplevel_decls(
            prog,
            prog.body,
            0,
            top_bound,
            Seq::<SpecNameSpan>::empty(),
            Seq::<SpecNameSpan>::empty(),
        );
        match spec_find_duplicate_name(lex_names) {
            Some(sp) => Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyDuplicateLexicalName,
                span: sp,
            }),
            None => match spec_find_collision(lex_names, var_names) {
                Some(sp) => Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyLexicalVarCollision,
                    span: sp,
                }),
                None => {
                    let root_ctx = SpecEarlyCtx {
                        strict: prog.has_use_strict,
                        in_function: false,
                        allow_new_target: false,
                        in_async: false,
                        in_generator: false,
                        in_formal_params: false,
                        in_iteration: false,
                        in_switch: false,
                        labels: Seq::<LabelEntry>::empty(),
                    };
                    spec_check_stmt_list(prog, prog.body, 0, top_bound, root_ctx)
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------------------
// Executable Early-Error Checker (Proved `r == spec_check_early_errors(prog@)`)
// ---------------------------------------------------------------------------------------

pub fn check_prop_key(
    prog: &Program,
    key: &PropKeyAst,
    bound_rank: usize,
    ctx: &EarlyCtx,
    span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::prop_key_bounded(prog@.exprs, *key, bound_rank as nat),
    ensures
        r == spec_check_prop_key(prog@, *key, bound_rank as nat, ctx@, span),
    decreases bound_rank as nat, 2nat, 0nat,
{
    match key {
        PropKeyAst::Ident(_) => Ok(()),
        PropKeyAst::StringLit { has_legacy_octal_escape, .. } => {
            if ctx.strict && *has_legacy_octal_escape {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::EarlyStrictLegacyOctal, span })
            } else {
                Ok(())
            }
        },
        PropKeyAst::NumberLit { has_legacy_octal_or_leading_zero, .. } => {
            if ctx.strict && *has_legacy_octal_or_leading_zero {
                Err(SyntaxDiagnostic { kind: DiagnosticKind::EarlyStrictLegacyOctal, span })
            } else {
                Ok(())
            }
        },
        PropKeyAst::Computed(cid) => check_expr(prog, *cid, ctx),
    }
}

pub fn check_param_defaults(
    prog: &Program,
    params: &[Param],
    bound_rank: usize,
    param_ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, param_ctx@.labels),
        crate::ast::params_bounded(prog@.exprs, params@, bound_rank as nat),
    ensures
        r == spec_check_param_defaults(prog@, params@, 0, bound_rank as nat, param_ctx@),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = params.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == params@.len(),
            prog.wf(),
            spec_labels_valid(prog@, param_ctx@.labels),
            crate::ast::params_bounded(prog@.exprs, params@, bound_rank as nat),
            spec_check_param_defaults(prog@, params@, 0, bound_rank as nat, param_ctx@)
                == spec_check_param_defaults(prog@, params@, idx as nat, bound_rank as nat, param_ctx@),
        decreases n - idx,
    {
        proof {
            assert(opt_expr_bounded(
                prog@.exprs,
                params@[idx as int].default,
                bound_rank as nat,
            ));
        }
        if let Some(did) = params[idx].default {
            if let Err(e) = check_expr(prog, did, param_ctx) {
                return Err(e);
            }
        }
        idx = idx + 1;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn check_function_common(
    prog: &Program,
    inner_name: &Option<Ident>,
    params: &[Param],
    body: &[StmtId],
    bound_rank: usize,
    outer_strict: bool,
    body_has_use_strict: bool,
    has_directive_octal_escape: bool,
    is_async: bool,
    is_generator: bool,
    always_unique_params: bool,
    allow_new_target: bool,
    fn_span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        crate::ast::params_bounded(prog@.exprs, params@, bound_rank as nat),
        stmt_seq_bounded(prog@.stmts, body@, bound_rank as nat),
    ensures
        r == spec_check_function_common(
            prog@,
            *inner_name,
            params@,
            body@,
            bound_rank as nat,
            outer_strict,
            body_has_use_strict,
            has_directive_octal_escape,
            is_async,
            is_generator,
            always_unique_params,
            allow_new_target,
            fn_span,
        ),
    decreases bound_rank as nat, 3nat, 0nat,
{
    let fn_strict = outer_strict || body_has_use_strict;
    let simple = is_simple_params(params);
    if body_has_use_strict && !simple {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyUseStrictWithNonSimpleParams,
            span: fn_span,
        });
    }
    if fn_strict && has_directive_octal_escape {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: fn_span,
        });
    }
    if let Some(nm) = inner_name {
        if let Err(e) = check_binding_ident(nm, fn_strict, is_async, is_generator, false) {
            return Err(e);
        }
    }
    let param_names = match collect_param_names(params, fn_strict, is_async, is_generator) {
        Err(e) => {
            return Err(e);
        },
        Ok(v) => v,
    };
    if fn_strict || always_unique_params || !simple {
        if let Some(sp) = find_duplicate_name(param_names.as_slice()) {
            return Err(SyntaxDiagnostic {
                kind: DiagnosticKind::EarlyDuplicateParamName,
                span: sp,
            });
        }
    }
    let param_ctx = EarlyCtx {
        strict: fn_strict,
        in_function: true,
        allow_new_target,
        in_async: is_async,
        in_generator: is_generator,
        in_formal_params: true,
        in_iteration: false,
        in_switch: false,
        labels: Vec::new(),
    };
    proof {
        assert(param_ctx.labels@ =~= Seq::<LabelEntry>::empty());
    }
    if let Err(e) = check_param_defaults(prog, params, bound_rank, &param_ctx) {
        return Err(e);
    }
    let (lex_names, var_names) = collect_toplevel_decls(prog, body, bound_rank);
    if let Some(sp) = find_duplicate_name(lex_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span: sp,
        });
    }
    if let Some(sp) = find_collision(lex_names.as_slice(), var_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyLexicalVarCollision,
            span: sp,
        });
    }
    if let Some(sp) = find_collision(param_names.as_slice(), lex_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span: sp,
        });
    }
    let body_ctx = EarlyCtx {
        strict: fn_strict,
        in_function: true,
        allow_new_target,
        in_async: is_async,
        in_generator: is_generator,
        in_formal_params: false,
        in_iteration: false,
        in_switch: false,
        labels: Vec::new(),
    };
    proof {
        assert(body_ctx.labels@ =~= Seq::<LabelEntry>::empty());
    }
    check_stmt_list(prog, body, bound_rank, &body_ctx)
}

#[allow(clippy::too_many_arguments)]
pub fn check_setter_body(
    prog: &Program,
    param: &Param,
    body: &[StmtId],
    bound_rank: usize,
    outer_strict: bool,
    body_has_use_strict: bool,
    has_directive_octal_escape: bool,
    fn_span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        opt_expr_bounded(prog@.exprs, param.default, bound_rank as nat),
        stmt_seq_bounded(prog@.stmts, body@, bound_rank as nat),
    ensures
        r == spec_check_setter_body(
            prog@,
            *param,
            body@,
            bound_rank as nat,
            outer_strict,
            body_has_use_strict,
            has_directive_octal_escape,
            fn_span,
        ),
    decreases bound_rank as nat, 3nat, 0nat,
{
    let fn_strict = outer_strict || body_has_use_strict;
    let simple = !param.is_rest && param.default.is_none();
    if body_has_use_strict && !simple {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyUseStrictWithNonSimpleParams,
            span: fn_span,
        });
    }
    if fn_strict && has_directive_octal_escape {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: fn_span,
        });
    }
    if let Err(e) = check_binding_ident(&param.name, fn_strict, false, false, false) {
        return Err(e);
    }
    if let Some(did) = param.default {
        let param_ctx = EarlyCtx {
            strict: fn_strict,
            in_function: true,
            allow_new_target: true,
            in_async: false,
            in_generator: false,
            in_formal_params: true,
            in_iteration: false,
            in_switch: false,
            labels: Vec::new(),
        };
        proof {
            assert(param_ctx.labels@ =~= Seq::<LabelEntry>::empty());
        }
        if let Err(e) = check_expr(prog, did, &param_ctx) {
            return Err(e);
        }
    }
    let (lex_names, var_names) = collect_toplevel_decls(prog, body, bound_rank);
    let mut p_vec: Vec<NameSpan> = Vec::new();
    let ns = make_name_span(&param.name);
    let ghost old_p = p_vec@;
    let ghost g_ns = ns;
    p_vec.push(ns);
    proof {
        assert(spec_ns_view(old_p) =~= Seq::<SpecNameSpan>::empty());
        lemma_ns_push_view(old_p, g_ns);
        assert(spec_ns_view(p_vec@) =~= seq![SpecNameSpan {
            name: param.name.name@,
            span: param.name.span,
        }]);
    }
    if let Some(sp) = find_duplicate_name(lex_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span: sp,
        });
    }
    if let Some(sp) = find_collision(lex_names.as_slice(), var_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyLexicalVarCollision,
            span: sp,
        });
    }
    if let Some(sp) = find_collision(p_vec.as_slice(), lex_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span: sp,
        });
    }
    let body_ctx = EarlyCtx {
        strict: fn_strict,
        in_function: true,
        allow_new_target: true,
        in_async: false,
        in_generator: false,
        in_formal_params: false,
        in_iteration: false,
        in_switch: false,
        labels: Vec::new(),
    };
    proof {
        assert(body_ctx.labels@ =~= Seq::<LabelEntry>::empty());
    }
    check_stmt_list(prog, body, bound_rank, &body_ctx)
}

pub fn check_arrow_expr(
    prog: &Program,
    params: &[Param],
    body: &ArrowBody,
    is_async: bool,
    erank: usize,
    ctx: &EarlyCtx,
    span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        crate::ast::params_bounded(prog@.exprs, params@, erank as nat),
        (match *body {
            ArrowBody::Expr(e) => expr_id_bounded(prog@.exprs, e, erank as nat),
            ArrowBody::Block { stmts: b, .. } => stmt_seq_bounded(prog@.stmts, b@, erank as nat),
        }),
    ensures
        r == spec_check_arrow_expr(prog@, params@, *body, is_async, erank as nat, ctx@, span),
    decreases erank as nat, 4nat, 0nat,
{
    let p_async = ctx.in_async || is_async;
    let p_gen = ctx.in_generator;
    match body {
        ArrowBody::Block { stmts, has_use_strict, has_directive_octal_escape } => {
            let fn_strict = ctx.strict || *has_use_strict;
            match collect_param_names(params, fn_strict, p_async, p_gen) {
                Err(err) => Err(err),
                Ok(_) => {
                    let outer_param_ctx = EarlyCtx {
                        strict: fn_strict,
                        in_function: true,
                        allow_new_target: ctx.allow_new_target,
                        in_async: p_async,
                        in_generator: p_gen,
                        in_formal_params: true,
                        in_iteration: false,
                        in_switch: false,
                        labels: Vec::new(),
                    };
                    proof {
                        assert(outer_param_ctx.labels@ =~= Seq::<LabelEntry>::empty());
                    }
                    match check_param_defaults(prog, params, erank, &outer_param_ctx) {
                        Err(err) => Err(err),
                        Ok(()) => check_function_common(
                            prog,
                            &None,
                            params,
                            stmts.as_slice(),
                            erank,
                            ctx.strict,
                            *has_use_strict,
                            *has_directive_octal_escape,
                            is_async,
                            false,
                            true,
                            ctx.allow_new_target,
                            span,
                        ),
                    }
                },
            }
        },
        ArrowBody::Expr(body_expr) => {
            match collect_param_names(params, ctx.strict, p_async, p_gen) {
                Err(err) => Err(err),
                Ok(param_names) => match find_duplicate_name(param_names.as_slice()) {
                    Some(sp) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyDuplicateParamName,
                        span: sp,
                    }),
                    None => {
                        let param_ctx = EarlyCtx {
                            strict: ctx.strict,
                            in_function: true,
                            allow_new_target: ctx.allow_new_target,
                            in_async: p_async,
                            in_generator: p_gen,
                            in_formal_params: true,
                            in_iteration: false,
                            in_switch: false,
                            labels: Vec::new(),
                        };
                        proof {
                            assert(param_ctx.labels@ =~= Seq::<LabelEntry>::empty());
                        }
                        match check_param_defaults(prog, params, erank, &param_ctx) {
                            Err(err) => Err(err),
                            Ok(()) => {
                                let body_ctx = EarlyCtx {
                                    strict: ctx.strict,
                                    in_function: true,
                                    allow_new_target: ctx.allow_new_target,
                                    in_async: is_async,
                                    in_generator: false,
                                    in_formal_params: false,
                                    in_iteration: false,
                                    in_switch: false,
                                    labels: Vec::new(),
                                };
                                proof {
                                    assert(body_ctx.labels@ =~= Seq::<LabelEntry>::empty());
                                }
                                check_expr(prog, *body_expr, &body_ctx)
                            },
                        }
                    },
                },
            }
        },
    }
}

pub fn check_array_elems(
    prog: &Program,
    elems: &[ArrayElem],
    bound_rank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::array_elems_bounded(prog@.exprs, elems@, bound_rank as nat),
    ensures
        r == spec_check_array_elems(prog@, elems@, 0, bound_rank as nat, ctx@),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = elems.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == elems@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            crate::ast::array_elems_bounded(prog@.exprs, elems@, bound_rank as nat),
            spec_check_array_elems(prog@, elems@, 0, bound_rank as nat, ctx@)
                == spec_check_array_elems(prog@, elems@, idx as nat, bound_rank as nat, ctx@),
        decreases n - idx,
    {
        proof {
            let ek = elems@[idx as int];
            assert(match ek {
                ArrayElem::Hole => true,
                ArrayElem::Elem(id) => expr_id_bounded(prog@.exprs, id, bound_rank as nat),
                ArrayElem::Spread(id) => expr_id_bounded(prog@.exprs, id, bound_rank as nat),
            });
        }
        let step_res = match &elems[idx] {
            ArrayElem::Hole => Ok(()),
            ArrayElem::Elem(id) => check_expr(prog, *id, ctx),
            ArrayElem::Spread(id) => check_expr(prog, *id, ctx),
        };
        if let Err(e) = step_res {
            return Err(e);
        }
        idx = idx + 1;
    }
    Ok(())
}

pub fn check_call_args(
    prog: &Program,
    args: &[CallArg],
    bound_rank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::call_args_bounded(prog@.exprs, args@, bound_rank as nat),
    ensures
        r == spec_check_call_args(prog@, args@, 0, bound_rank as nat, ctx@),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = args.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == args@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            crate::ast::call_args_bounded(prog@.exprs, args@, bound_rank as nat),
            spec_check_call_args(prog@, args@, 0, bound_rank as nat, ctx@)
                == spec_check_call_args(prog@, args@, idx as nat, bound_rank as nat, ctx@),
        decreases n - idx,
    {
        proof {
            let ak = args@[idx as int];
            assert(match ak {
                CallArg::Arg(id) => expr_id_bounded(prog@.exprs, id, bound_rank as nat),
                CallArg::Spread(id) => expr_id_bounded(prog@.exprs, id, bound_rank as nat),
            });
        }
        let step_res = match &args[idx] {
            CallArg::Arg(id) => check_expr(prog, *id, ctx),
            CallArg::Spread(id) => check_expr(prog, *id, ctx),
        };
        if let Err(e) = step_res {
            return Err(e);
        }
        idx = idx + 1;
    }
    Ok(())
}

pub fn check_one_obj_prop(
    prog: &Program,
    prop: &ObjPropKind,
    bound_rank: usize,
    ctx: &EarlyCtx,
    obj_span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::obj_prop_bounded(prog@.exprs, prog@.stmts, *prop, bound_rank as nat),
    ensures
        r == spec_check_one_obj_prop(prog@, *prop, bound_rank as nat, ctx@, obj_span),
    decreases bound_rank as nat, 4nat, 0nat,
{
    match prop {
        ObjPropKind::Init { key, value, is_shorthand, shorthand_ident } => {
            let sh_chk = if *is_shorthand {
                match shorthand_ident {
                    Some(id) => check_ident_ref(id, ctx.strict, ctx.in_async, ctx.in_generator),
                    None => Ok(()),
                }
            } else {
                Ok(())
            };
            match sh_chk {
                Err(e) => Err(e),
                Ok(()) => match check_prop_key(prog, key, bound_rank, ctx, obj_span) {
                    Err(e) => Err(e),
                    Ok(()) => check_expr(prog, *value, ctx),
                },
            }
        },
        ObjPropKind::Method {
            key,
            params,
            body,
            is_async,
            is_generator,
            body_has_use_strict,
            has_directive_octal_escape,
            span,
        } => match check_prop_key(prog, key, bound_rank, ctx, *span) {
            Err(e) => Err(e),
            Ok(()) => check_function_common(
                prog,
                &None,
                params.as_slice(),
                body.as_slice(),
                bound_rank,
                ctx.strict,
                *body_has_use_strict,
                *has_directive_octal_escape,
                *is_async,
                *is_generator,
                true,
                true,
                *span,
            ),
        },
        ObjPropKind::Getter { key, body, body_has_use_strict, has_directive_octal_escape, span } => {
            match check_prop_key(prog, key, bound_rank, ctx, *span) {
                Err(e) => Err(e),
                Ok(()) => {
                    let empty_params: [Param; 0] = [];
                    proof {
                        assert(empty_params@ =~= Seq::<Param>::empty());
                    }
                    check_function_common(
                        prog,
                        &None,
                        &empty_params,
                        body.as_slice(),
                        bound_rank,
                        ctx.strict,
                        *body_has_use_strict,
                        *has_directive_octal_escape,
                        false,
                        false,
                        true,
                        true,
                        *span,
                    )
                },
            }
        },
        ObjPropKind::Setter {
            key,
            param,
            body,
            body_has_use_strict,
            has_directive_octal_escape,
            span,
        } => match check_prop_key(prog, key, bound_rank, ctx, *span) {
            Err(e) => Err(e),
            Ok(()) => check_setter_body(
                prog,
                param,
                body.as_slice(),
                bound_rank,
                ctx.strict,
                *body_has_use_strict,
                *has_directive_octal_escape,
                *span,
            ),
        },
        ObjPropKind::Spread(id) => check_expr(prog, *id, ctx),
    }
}

pub fn check_obj_props(
    prog: &Program,
    props: &[ObjPropKind],
    bound_rank: usize,
    ctx: &EarlyCtx,
    obj_span: Span,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::obj_props_bounded(prog@.exprs, prog@.stmts, props@, bound_rank as nat),
    ensures
        r == spec_check_obj_props(prog@, props@, 0, bound_rank as nat, ctx@, obj_span),
    decreases bound_rank as nat, 4nat, 1nat,
{
    let n = props.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == props@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            crate::ast::obj_props_bounded(prog@.exprs, prog@.stmts, props@, bound_rank as nat),
            spec_check_obj_props(prog@, props@, 0, bound_rank as nat, ctx@, obj_span)
                == spec_check_obj_props(prog@, props@, idx as nat, bound_rank as nat, ctx@, obj_span),
        decreases n - idx,
    {
        proof {
            assert(crate::ast::obj_prop_bounded(
                prog@.exprs,
                prog@.stmts,
                props@[idx as int],
                bound_rank as nat,
            ));
        }
        if let Err(e) = check_one_obj_prop(prog, &props[idx], bound_rank, ctx, obj_span) {
            return Err(e);
        }
        idx = idx + 1;
    }
    Ok(())
}

pub fn check_var_declarators(
    prog: &Program,
    decls: &[VarDeclarator],
    bound_rank: usize,
    is_let_or_const: bool,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::var_decls_bounded(prog@.exprs, decls@, bound_rank as nat),
    ensures
        r == spec_check_var_declarators(
            prog@,
            decls@,
            0,
            bound_rank as nat,
            is_let_or_const,
            ctx@,
        ),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = decls.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == decls@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            crate::ast::var_decls_bounded(prog@.exprs, decls@, bound_rank as nat),
            spec_check_var_declarators(prog@, decls@, 0, bound_rank as nat, is_let_or_const, ctx@)
                == spec_check_var_declarators(
                    prog@,
                    decls@,
                    idx as nat,
                    bound_rank as nat,
                    is_let_or_const,
                    ctx@,
                ),
        decreases n - idx,
    {
        let d = &decls[idx];
        if let Err(e) =
            check_binding_ident(&d.name, ctx.strict, ctx.in_async, ctx.in_generator, is_let_or_const)
        {
            return Err(e);
        }
        proof {
            assert(opt_expr_bounded(
                prog@.exprs,
                decls@[idx as int].init,
                bound_rank as nat,
            ));
        }
        if let Some(eid) = d.init {
            if let Err(e) = check_expr(prog, eid, ctx) {
                return Err(e);
            }
        }
        idx = idx + 1;
    }
    Ok(())
}

pub fn check_switch_cases(
    prog: &Program,
    cases: &[SwitchCase],
    bound_rank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        crate::ast::switch_cases_bounded(prog@.exprs, prog@.stmts, cases@, bound_rank as nat),
    ensures
        r == spec_check_switch_cases(prog@, cases@, 0, bound_rank as nat, ctx@),
    decreases bound_rank as nat, 3nat, 0nat,
{
    let n = cases.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == cases@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            crate::ast::switch_cases_bounded(prog@.exprs, prog@.stmts, cases@, bound_rank as nat),
            spec_check_switch_cases(prog@, cases@, 0, bound_rank as nat, ctx@)
                == spec_check_switch_cases(prog@, cases@, idx as nat, bound_rank as nat, ctx@),
        decreases n - idx,
    {
        proof {
            assert(opt_expr_bounded(
                prog@.exprs,
                cases@[idx as int].test,
                bound_rank as nat,
            ));
            assert(stmt_seq_bounded(
                prog@.stmts,
                cases@[idx as int].consequent@,
                bound_rank as nat,
            ));
        }
        if let Some(tid) = cases[idx].test {
            if let Err(e) = check_expr(prog, tid, ctx) {
                return Err(e);
            }
        }
        if let Err(e) = check_stmt_list(prog, cases[idx].consequent.as_slice(), bound_rank, ctx) {
            return Err(e);
        }
        idx = idx + 1;
    }
    Ok(())
}

#[verifier::spinoff_prover]
fn check_expr_unary_ops(
    prog: &Program,
    eid: ExprId,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        eid.0 < prog@.exprs.len(),
        spec_labels_valid(prog@, ctx@.labels),
        match prog@.exprs[eid.0 as int].kind {
            ExprKind::Update { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Await(_)
            | ExprKind::Yield { .. } => true,
            _ => false,
        },
    ensures
        r == spec_check_expr(prog@, eid, ctx@),
    decreases prog@.exprs[eid.0 as int].rank as nat, 4nat, 1nat,
{
    let e = &prog.exprs[eid.0];
    let erank = e.rank;
    proof {
        assert(crate::ast::expr_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.exprs[eid.0 as int].kind,
            erank as nat,
        ));
    }
    match &e.kind {
        ExprKind::Update { arg, .. } => match check_expr(prog, *arg, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_assignment_target(prog, *arg, ctx.strict, true),
        },
        ExprKind::Unary { op, arg } => match check_expr(prog, *arg, ctx) {
            Err(err) => Err(err),
            Ok(()) => {
                if *op == UnaryOp::Delete && ctx.strict {
                    let unwrapped = unwrap_parens(prog, *arg);
                    match &prog.exprs[unwrapped.0].kind {
                        ExprKind::Ident(_) => Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::EarlyStrictDeleteIdentifier,
                            span: e.span,
                        }),
                        _ => Ok(()),
                    }
                } else {
                    Ok(())
                }
            },
        },
        ExprKind::Await(arg) => {
            if !ctx.in_async {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyAwaitOutsideAsync,
                    span: e.span,
                })
            } else if ctx.in_formal_params {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyAwaitInFormalParams,
                    span: e.span,
                })
            } else {
                check_expr(prog, *arg, ctx)
            }
        },
        ExprKind::Yield { arg, .. } => {
            if !ctx.in_generator {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyYieldOutsideGenerator,
                    span: e.span,
                })
            } else if ctx.in_formal_params {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyYieldInFormalParams,
                    span: e.span,
                })
            } else {
                match arg {
                    Some(aid) => check_expr(prog, *aid, ctx),
                    None => Ok(()),
                }
            }
        },
        _ => Ok(()),
    }
}

#[verifier::spinoff_prover]
fn check_expr_binary_ops(
    prog: &Program,
    eid: ExprId,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        eid.0 < prog@.exprs.len(),
        spec_labels_valid(prog@, ctx@.labels),
        match prog@.exprs[eid.0 as int].kind {
            ExprKind::Binary { .. }
            | ExprKind::Sequence { .. }
            | ExprKind::Conditional { .. }
            | ExprKind::Assign { .. }
            | ExprKind::FunctionExpr { .. }
            | ExprKind::ArrowFunction { .. } => true,
            _ => false,
        },
    ensures
        r == spec_check_expr(prog@, eid, ctx@),
    decreases prog@.exprs[eid.0 as int].rank as nat, 4nat, 1nat,
{
    let e = &prog.exprs[eid.0];
    let erank = e.rank;
    proof {
        assert(crate::ast::expr_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.exprs[eid.0 as int].kind,
            erank as nat,
        ));
    }
    match &e.kind {
        ExprKind::Binary { left, right, .. } => match check_expr(prog, *left, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_expr(prog, *right, ctx),
        },
        ExprKind::Sequence { left, right } => match check_expr(prog, *left, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_expr(prog, *right, ctx),
        },
        ExprKind::Conditional { cond, consequent, alternate } => match check_expr(prog, *cond, ctx) {
            Err(err) => Err(err),
            Ok(()) => match check_expr(prog, *consequent, ctx) {
                Err(err) => Err(err),
                Ok(()) => check_expr(prog, *alternate, ctx),
            },
        },
        ExprKind::Assign { op, left, right } => match check_expr(prog, *left, ctx) {
            Err(err) => Err(err),
            Ok(()) => match check_assignment_target(
                prog,
                *left,
                ctx.strict,
                !is_logical_assign_op(*op),
            ) {
                Err(err) => Err(err),
                Ok(()) => check_expr(prog, *right, ctx),
            },
        },
        ExprKind::FunctionExpr {
            name,
            params,
            body,
            is_async,
            is_generator,
            body_has_use_strict,
            has_directive_octal_escape,
        } => check_function_common(
            prog,
            name,
            params.as_slice(),
            body.as_slice(),
            erank,
            ctx.strict,
            *body_has_use_strict,
            *has_directive_octal_escape,
            *is_async,
            *is_generator,
            false,
            true,
            e.span,
        ),
        ExprKind::ArrowFunction { params, body, is_async } => {
            check_arrow_expr(prog, params.as_slice(), body, *is_async, erank, ctx, e.span)
        },
        _ => Ok(()),
    }
}

#[verifier::spinoff_prover]
pub fn check_expr(
    prog: &Program,
    eid: ExprId,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        eid.0 < prog@.exprs.len(),
        spec_labels_valid(prog@, ctx@.labels),
    ensures
        r == spec_check_expr(prog@, eid, ctx@),
    decreases prog@.exprs[eid.0 as int].rank as nat, 5nat, 0nat,
{
    let e = &prog.exprs[eid.0];
    let erank = e.rank;
    proof {
        assert(crate::ast::expr_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.exprs[eid.0 as int].kind,
            erank as nat,
        ));
    }
    match &e.kind {
        ExprKind::This | ExprKind::Null | ExprKind::Bool(_) => Ok(()),
        ExprKind::TemplateNoSub { has_invalid_escape, .. } => {
            if *has_invalid_escape {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::InvalidUnicodeEscape,
                    span: e.span,
                })
            } else {
                Ok(())
            }
        },
        ExprKind::Number { has_legacy_octal_or_leading_zero, .. } => {
            if ctx.strict && *has_legacy_octal_or_leading_zero {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictLegacyOctal,
                    span: e.span,
                })
            } else {
                Ok(())
            }
        },
        ExprKind::StringLit { has_legacy_octal_escape, .. } => {
            if ctx.strict && *has_legacy_octal_escape {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictLegacyOctal,
                    span: e.span,
                })
            } else {
                Ok(())
            }
        },
        ExprKind::Ident(ident) => check_ident_ref(ident, ctx.strict, ctx.in_async, ctx.in_generator),
        ExprKind::Paren(inner) => check_expr(prog, *inner, ctx),
        ExprKind::Array(elems) => check_array_elems(prog, elems.as_slice(), erank, ctx),
        ExprKind::Object(props) => {
            if has_duplicate_proto_init(props.as_slice()) {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyDuplicateProtoProperty,
                    span: e.span,
                })
            } else {
                check_obj_props(prog, props.as_slice(), erank, ctx, e.span)
            }
        },
        ExprKind::Member { object, .. } => check_expr(prog, *object, ctx),
        ExprKind::ComputedMember { object, index, .. } => match check_expr(prog, *object, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_expr(prog, *index, ctx),
        },
        ExprKind::Call { callee, args, .. } => match check_expr(prog, *callee, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_call_args(prog, args.as_slice(), erank, ctx),
        },
        ExprKind::New { callee, args } => match check_expr(prog, *callee, ctx) {
            Err(err) => Err(err),
            Ok(()) => check_call_args(prog, args.as_slice(), erank, ctx),
        },
        ExprKind::NewTarget => {
            if !ctx.allow_new_target {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyNewTargetOutsideFunction,
                    span: e.span,
                })
            } else {
                Ok(())
            }
        },
        ExprKind::Update { .. }
        | ExprKind::Unary { .. }
        | ExprKind::Await(_)
        | ExprKind::Yield { .. } => check_expr_unary_ops(prog, eid, ctx),
        ExprKind::Binary { .. }
        | ExprKind::Sequence { .. }
        | ExprKind::Conditional { .. }
        | ExprKind::Assign { .. }
        | ExprKind::FunctionExpr { .. }
        | ExprKind::ArrowFunction { .. } => check_expr_binary_ops(prog, eid, ctx),
    }
}

pub fn check_block_stmt_list(
    prog: &Program,
    ids: &[StmtId],
    bound_rank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
    ensures
        r == spec_check_block_stmt_list(prog@, ids@, bound_rank as nat, ctx@),
    decreases bound_rank as nat, 3nat, 0nat,
{
    let mut lex: Vec<NameSpan> = Vec::new();
    let mut sloppy_fn: Vec<NameSpan> = Vec::new();
    let mut vars: Vec<NameSpan> = Vec::new();
    proof {
        assert(spec_ns_view(lex@) =~= Seq::<SpecNameSpan>::empty());
        assert(spec_ns_view(sloppy_fn@) =~= Seq::<SpecNameSpan>::empty());
        assert(spec_ns_view(vars@) =~= Seq::<SpecNameSpan>::empty());
    }
    collect_block_decls_into(prog, ids, bound_rank, ctx.strict, &mut lex, &mut sloppy_fn, &mut vars);
    match validate_block_triple(lex.as_slice(), sloppy_fn.as_slice(), vars.as_slice()) {
        Err(e) => Err(e),
        Ok(()) => check_stmt_list(prog, ids, bound_rank, ctx),
    }
}

pub fn check_for_stmt(
    prog: &Program,
    init: &ForInit,
    cond: &Option<ExprId>,
    update: &Option<ExprId>,
    body: StmtId,
    srank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        (match *init {
            ForInit::None => true,
            ForInit::VarDecl { decls, .. } => crate::ast::var_decls_bounded(prog@.exprs, decls@, srank as nat),
            ForInit::Expr(e) => expr_id_bounded(prog@.exprs, e, srank as nat),
        }),
        opt_expr_bounded(prog@.exprs, *cond, srank as nat),
        opt_expr_bounded(prog@.exprs, *update, srank as nat),
        stmt_id_bounded(prog@.stmts, body, srank as nat),
    ensures
        r == spec_check_for_stmt(prog@, *init, *cond, *update, body, srank as nat, ctx@),
    decreases srank as nat, 4nat, 0nat,
{
    match init {
        ForInit::None => {},
        ForInit::Expr(e) => {
            if let Err(err) = check_expr(prog, *e, ctx) {
                return Err(err);
            }
        },
        ForInit::VarDecl { kind, decls } => {
            let is_lc = *kind != VarDeclKind::Var;
            if let Err(err) = check_var_declarators(prog, decls.as_slice(), srank, is_lc, ctx) {
                return Err(err);
            }
            if is_lc {
                let mut head_lex: Vec<NameSpan> = Vec::new();
                proof {
                    assert(spec_ns_view(head_lex@) =~= Seq::<SpecNameSpan>::empty());
                }
                push_var_decls(decls.as_slice(), &mut head_lex);
                if let Some(sp) = find_duplicate_name(head_lex.as_slice()) {
                    return Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyDuplicateLexicalName,
                        span: sp,
                    });
                }
                let mut body_vars: Vec<NameSpan> = Vec::new();
                proof {
                    assert(spec_ns_view(body_vars@) =~= Seq::<SpecNameSpan>::empty());
                }
                collect_var_names_stmt(prog, body, &mut body_vars);
                if let Some(sp) = find_collision(head_lex.as_slice(), body_vars.as_slice()) {
                    return Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyLexicalVarCollision,
                        span: sp,
                    });
                }
            }
        },
    }
    if let Some(c) = cond {
        if let Err(err) = check_expr(prog, *c, ctx) {
            return Err(err);
        }
    }
    if let Some(u) = update {
        if let Err(err) = check_expr(prog, *u, ctx) {
            return Err(err);
        }
    }
    let iter_ctx = ctx.with_iteration();
    check_stmt(prog, body, &iter_ctx)
}

#[allow(clippy::too_many_arguments)]
pub fn check_for_in_of_stmt(
    prog: &Program,
    lhs: &ForInOfLhs,
    rhs: ExprId,
    is_await: bool,
    body: StmtId,
    srank: usize,
    span: Span,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        (match *lhs {
            ForInOfLhs::VarDecl { .. } => true,
            ForInOfLhs::Expr(e) => expr_id_bounded(prog@.exprs, e, srank as nat),
        }),
        expr_id_bounded(prog@.exprs, rhs, srank as nat),
        stmt_id_bounded(prog@.stmts, body, srank as nat),
    ensures
        r == spec_check_for_in_of_stmt(prog@, *lhs, rhs, is_await, body, srank as nat, span, ctx@),
    decreases srank as nat, 4nat, 0nat,
{
    if is_await && !ctx.in_async {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyAwaitOutsideAsync,
            span,
        });
    }
    match lhs {
        ForInOfLhs::VarDecl { kind, name } => {
            let is_lc = *kind != VarDeclKind::Var;
            if let Err(err) = check_binding_ident(name, ctx.strict, ctx.in_async, ctx.in_generator, is_lc) {
                return Err(err);
            }
            if is_lc {
                let mut head_lex: Vec<NameSpan> = Vec::new();
                let ns = make_name_span(name);
                let ghost old_h = head_lex@;
                let ghost g_ns = ns;
                head_lex.push(ns);
                let mut body_vars: Vec<NameSpan> = Vec::new();
                proof {
                    assert(spec_ns_view(old_h) =~= Seq::<SpecNameSpan>::empty());
                    lemma_ns_push_view(old_h, g_ns);
                    assert(spec_ns_view(head_lex@) =~= seq![SpecNameSpan {
                        name: name.name@,
                        span: name.span,
                    }]);
                    assert(spec_ns_view(body_vars@) =~= Seq::<SpecNameSpan>::empty());
                }
                collect_var_names_stmt(prog, body, &mut body_vars);
                if let Some(sp) = find_collision(head_lex.as_slice(), body_vars.as_slice()) {
                    return Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyLexicalVarCollision,
                        span: sp,
                    });
                }
            }
        },
        ForInOfLhs::Expr(e) => {
            if let Err(err) = check_expr(prog, *e, ctx) {
                return Err(err);
            }
            if let Err(err) = check_assignment_target(prog, *e, ctx.strict, true) {
                return Err(err);
            }
        },
    }
    if let Err(err) = check_expr(prog, rhs, ctx) {
        return Err(err);
    }
    let iter_ctx = ctx.with_iteration();
    check_stmt(prog, body, &iter_ctx)
}

pub fn check_try_stmt(
    prog: &Program,
    block: &[StmtId],
    catch_clause: &Option<CatchClause>,
    finally_block: &Option<Vec<StmtId>>,
    srank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        stmt_seq_bounded(prog@.stmts, block@, srank as nat),
        (match *catch_clause {
            Some(cc) => stmt_seq_bounded(prog@.stmts, cc.body@, srank as nat),
            None => true,
        }),
        (match *finally_block {
            Some(fb) => stmt_seq_bounded(prog@.stmts, fb@, srank as nat),
            None => true,
        }),
    ensures
        r == spec_check_try_stmt(prog@, block@, *catch_clause, *finally_block, srank as nat, ctx@),
    decreases srank as nat, 4nat, 0nat,
{
    match check_block_stmt_list(prog, block, srank, ctx) {
        Err(e) => {
            return Err(e);
        },
        Ok(()) => {},
    }
    if let Some(cc) = catch_clause {
        if let Some(p) = &cc.param {
            match check_binding_ident(p, ctx.strict, ctx.in_async, ctx.in_generator, false) {
                Err(e) => {
                    return Err(e);
                },
                Ok(()) => {},
            }
            let mut c_lex: Vec<NameSpan> = Vec::new();
            let mut c_sloppy: Vec<NameSpan> = Vec::new();
            let mut c_vars: Vec<NameSpan> = Vec::new();
            let mut p_vec: Vec<NameSpan> = Vec::new();
            let ns = make_name_span(p);
            let ghost old_p = p_vec@;
            let ghost g_ns = ns;
            p_vec.push(ns);
            proof {
                assert(spec_ns_view(c_lex@) =~= Seq::<SpecNameSpan>::empty());
                assert(spec_ns_view(c_sloppy@) =~= Seq::<SpecNameSpan>::empty());
                assert(spec_ns_view(c_vars@) =~= Seq::<SpecNameSpan>::empty());
                assert(spec_ns_view(old_p) =~= Seq::<SpecNameSpan>::empty());
                lemma_ns_push_view(old_p, g_ns);
                assert(spec_ns_view(p_vec@) =~= seq![SpecNameSpan { name: p.name@, span: p.span }]);
            }
            collect_block_decls_into(
                prog,
                cc.body.as_slice(),
                srank,
                ctx.strict,
                &mut c_lex,
                &mut c_sloppy,
                &mut c_vars,
            );
            if let Some(sp) = find_collision(p_vec.as_slice(), c_lex.as_slice()) {
                return Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyDuplicateLexicalName,
                    span: sp,
                });
            }
            if let Some(sp) = find_collision(p_vec.as_slice(), c_sloppy.as_slice()) {
                return Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyDuplicateLexicalName,
                    span: sp,
                });
            }
        }
        match check_block_stmt_list(prog, cc.body.as_slice(), srank, ctx) {
            Err(e) => {
                return Err(e);
            },
            Ok(()) => {},
        }
    }
    match finally_block {
        None => Ok(()),
        Some(fb) => check_block_stmt_list(prog, fb.as_slice(), srank, ctx),
    }
}

#[verifier::spinoff_prover]
fn check_stmt_compound(
    prog: &Program,
    sid: StmtId,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        sid.0 < prog@.stmts.len(),
        spec_labels_valid(prog@, ctx@.labels),
        match prog@.stmts[sid.0 as int].kind {
            StmtKind::For { .. }
            | StmtKind::ForIn { .. }
            | StmtKind::ForOf { .. }
            | StmtKind::Switch { .. }
            | StmtKind::Try { .. }
            | StmtKind::With { .. }
            | StmtKind::Labeled { .. }
            | StmtKind::FunctionDecl { .. } => true,
            _ => false,
        },
    ensures
        r == spec_check_stmt(prog@, sid, ctx@),
    decreases prog@.stmts[sid.0 as int].rank as nat, 4nat, 1nat,
{
    let s = &prog.stmts[sid.0];
    let srank = s.rank;
    proof {
        assert(crate::ast::stmt_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.stmts[sid.0 as int].kind,
            srank as nat,
        ));
    }
    match &s.kind {
        StmtKind::For { init, cond, update, body } => {
            check_for_stmt(prog, init, cond, update, *body, srank, ctx)
        },
        StmtKind::ForIn { lhs, rhs, body } => {
            check_for_in_of_stmt(prog, lhs, *rhs, false, *body, srank, s.span, ctx)
        },
        StmtKind::ForOf { lhs, rhs, is_await, body } => {
            check_for_in_of_stmt(prog, lhs, *rhs, *is_await, *body, srank, s.span, ctx)
        },
        StmtKind::Switch { discriminant, cases } => match check_expr(prog, *discriminant, ctx) {
            Err(e) => Err(e),
            Ok(()) => {
                proof {
                    assert forall|k: int| 0 <= k < cases@.len() implies stmt_seq_bounded(
                        prog@.stmts,
                        (#[trigger] cases@[k]).consequent@,
                        srank as nat,
                    ) by {
                        assert(opt_expr_bounded(prog@.exprs, cases@[k].test, srank as nat)
                            && stmt_seq_bounded(prog@.stmts, cases@[k].consequent@, srank as nat));
                    }
                }
                let (lex, sloppy_fn, vars) =
                    collect_switch_decls(prog, cases.as_slice(), srank, ctx.strict);
                match validate_block_triple(lex.as_slice(), sloppy_fn.as_slice(), vars.as_slice()) {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let sw_ctx = ctx.with_switch();
                        check_switch_cases(prog, cases.as_slice(), srank, &sw_ctx)
                    },
                }
            },
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            check_try_stmt(prog, block.as_slice(), catch_clause, finally_block, srank, ctx)
        },
        StmtKind::With { object, body } => {
            if ctx.strict {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyStrictWithStatement,
                    span: s.span,
                })
            } else {
                match check_expr(prog, *object, ctx) {
                    Err(e) => Err(e),
                    Ok(()) => check_stmt(prog, *body, ctx),
                }
            }
        },
        StmtKind::Labeled { label, body } => {
            match check_ident_ref(label, ctx.strict, ctx.in_async, ctx.in_generator) {
                Err(e) => Err(e),
                Ok(()) => match lookup_label(prog, ctx.labels.as_slice(), label.name.as_slice()) {
                    Some(_) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyDuplicateLabel,
                        span: label.span,
                    }),
                    None => {
                        if ctx.strict && unwrap_labeled_fn_decl(prog, *body).is_some() {
                            Err(SyntaxDiagnostic {
                                kind: DiagnosticKind::SingleStmtLexicalDecl,
                                span: s.span,
                            })
                        } else {
                            let is_iter = is_iteration_target(prog, *body);
                            let entry = LabelEntry { labeled_stmt_id: sid, is_iteration: is_iter };
                            let next_ctx = ctx.with_pushed_label(entry);
                            proof {
                                assert forall|k: int| 0 <= k < next_ctx@.labels.len() implies (
                                    #[trigger] next_ctx@.labels[k]
                                ).labeled_stmt_id.0 < prog@.stmts.len() by {
                                    if k < ctx@.labels.len() {
                                        assert(next_ctx@.labels[k] == ctx@.labels[k]);
                                    }
                                }
                            }
                            check_stmt(prog, *body, &next_ctx)
                        }
                    },
                },
            }
        },
        StmtKind::FunctionDecl {
            name,
            params,
            body,
            is_async,
            is_generator,
            body_has_use_strict,
            has_directive_octal_escape,
        } => match check_binding_ident(
            name,
            ctx.strict || *body_has_use_strict,
            ctx.in_async,
            ctx.in_generator,
            false,
        ) {
            Err(e) => Err(e),
            Ok(()) => check_function_common(
                prog,
                &None,
                params.as_slice(),
                body.as_slice(),
                srank,
                ctx.strict,
                *body_has_use_strict,
                *has_directive_octal_escape,
                *is_async,
                *is_generator,
                false,
                true,
                s.span,
            ),
        },
        _ => Ok(()),
    }
}

#[verifier::spinoff_prover]
pub fn check_stmt(
    prog: &Program,
    sid: StmtId,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        sid.0 < prog@.stmts.len(),
        spec_labels_valid(prog@, ctx@.labels),
    ensures
        r == spec_check_stmt(prog@, sid, ctx@),
    decreases prog@.stmts[sid.0 as int].rank as nat, 5nat, 0nat,
{
    let s = &prog.stmts[sid.0];
    let srank = s.rank;
    proof {
        assert(crate::ast::stmt_children_bounded(
            prog@.exprs,
            prog@.stmts,
            prog@.stmts[sid.0 as int].kind,
            srank as nat,
        ));
    }
    match &s.kind {
        StmtKind::Empty | StmtKind::Debugger => Ok(()),
        StmtKind::Block(ids) => check_block_stmt_list(prog, ids.as_slice(), srank, ctx),
        StmtKind::VarDecl { kind, decls } => {
            let is_lc = *kind != VarDeclKind::Var;
            check_var_declarators(prog, decls.as_slice(), srank, is_lc, ctx)
        },
        StmtKind::ExprStmt(eid) => check_expr(prog, *eid, ctx),
        StmtKind::Throw(eid) => check_expr(prog, *eid, ctx),
        StmtKind::Return(opt_e) => {
            if !ctx.in_function {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::EarlyReturnOutsideFunction,
                    span: s.span,
                })
            } else {
                match opt_e {
                    Some(eid) => check_expr(prog, *eid, ctx),
                    None => Ok(()),
                }
            }
        },
        StmtKind::Break(opt_lbl) => match opt_lbl {
            None => {
                if !ctx.in_iteration && !ctx.in_switch {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyInvalidBreak,
                        span: s.span,
                    })
                } else {
                    Ok(())
                }
            },
            Some(lbl) => match check_ident_ref(lbl, ctx.strict, ctx.in_async, ctx.in_generator) {
                Err(e) => Err(e),
                Ok(()) => match lookup_label(prog, ctx.labels.as_slice(), lbl.name.as_slice()) {
                    Some(_) => Ok(()),
                    None => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyUndefinedLabel,
                        span: lbl.span,
                    }),
                },
            },
        },
        StmtKind::Continue(opt_lbl) => match opt_lbl {
            None => {
                if !ctx.in_iteration {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyInvalidContinue,
                        span: s.span,
                    })
                } else {
                    Ok(())
                }
            },
            Some(lbl) => match check_ident_ref(lbl, ctx.strict, ctx.in_async, ctx.in_generator) {
                Err(e) => Err(e),
                Ok(()) => match lookup_label(prog, ctx.labels.as_slice(), lbl.name.as_slice()) {
                    Some(true) => Ok(()),
                    Some(false) => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyNonIterationContinueLabel,
                        span: lbl.span,
                    }),
                    None => Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::EarlyUndefinedLabel,
                        span: lbl.span,
                    }),
                },
            },
        },
        StmtKind::If { cond, consequent, alternate } => match check_expr(prog, *cond, ctx) {
            Err(e) => Err(e),
            Ok(()) => match check_stmt(prog, *consequent, ctx) {
                Err(e) => Err(e),
                Ok(()) => match alternate {
                    Some(alt) => check_stmt(prog, *alt, ctx),
                    None => Ok(()),
                },
            },
        },
        StmtKind::While { cond, body } => match check_expr(prog, *cond, ctx) {
            Err(e) => Err(e),
            Ok(()) => {
                let iter_ctx = ctx.with_iteration();
                check_stmt(prog, *body, &iter_ctx)
            },
        },
        StmtKind::DoWhile { body, cond } => {
            let iter_ctx = ctx.with_iteration();
            match check_stmt(prog, *body, &iter_ctx) {
                Err(e) => Err(e),
                Ok(()) => check_expr(prog, *cond, ctx),
            }
        },
        StmtKind::For { .. }
        | StmtKind::ForIn { .. }
        | StmtKind::ForOf { .. }
        | StmtKind::Switch { .. }
        | StmtKind::Try { .. }
        | StmtKind::With { .. }
        | StmtKind::Labeled { .. }
        | StmtKind::FunctionDecl { .. } => check_stmt_compound(prog, sid, ctx),
    }
}

pub fn check_stmt_list(
    prog: &Program,
    ids: &[StmtId],
    bound_rank: usize,
    ctx: &EarlyCtx,
) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
        spec_labels_valid(prog@, ctx@.labels),
        stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
    ensures
        r == spec_check_stmt_list(prog@, ids@, 0, bound_rank as nat, ctx@),
    decreases bound_rank as nat, 2nat, 0nat,
{
    let n = ids.len();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            n == ids@.len(),
            prog.wf(),
            spec_labels_valid(prog@, ctx@.labels),
            stmt_seq_bounded(prog@.stmts, ids@, bound_rank as nat),
            spec_check_stmt_list(prog@, ids@, 0, bound_rank as nat, ctx@)
                == spec_check_stmt_list(prog@, ids@, idx as nat, bound_rank as nat, ctx@),
        decreases n - idx,
    {
        let sid = ids[idx];
        proof {
            assert(stmt_id_bounded(prog@.stmts, ids@[idx as int], bound_rank as nat));
        }
        if let Err(e) = check_stmt(prog, sid, ctx) {
            return Err(e);
        }
        idx = idx + 1;
    }
    Ok(())
}

/// Verified ECMA-262 Static Semantics: Early Errors pass, proved equal to `spec_check_early_errors`.
pub fn check_early_errors(prog: &Program) -> (r: Result<(), SyntaxDiagnostic>)
    requires
        prog.wf(),
    ensures
        r == spec_check_early_errors(prog@),
{
    if prog.has_use_strict && prog.has_directive_octal_escape {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyStrictLegacyOctal,
            span: Span { start: 0, end: 0 },
        });
    }
    let top_bound = prog.exprs.len() + prog.stmts.len();
    proof {
        assert forall|k: int| 0 <= k < prog@.body.len() implies stmt_id_bounded(
            prog@.stmts,
            #[trigger] prog@.body[k],
            top_bound as nat,
        ) by {
            let sid = prog@.body[k];
            assert(sid.0 < prog@.stmts.len());
            assert((prog@.stmts[sid.0 as int].rank as nat) < top_bound as nat);
        }
    }
    let (lex_names, var_names) = collect_toplevel_decls(prog, prog.body.as_slice(), top_bound);
    if let Some(sp) = find_duplicate_name(lex_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyDuplicateLexicalName,
            span: sp,
        });
    }
    if let Some(sp) = find_collision(lex_names.as_slice(), var_names.as_slice()) {
        return Err(SyntaxDiagnostic {
            kind: DiagnosticKind::EarlyLexicalVarCollision,
            span: sp,
        });
    }
    let root_ctx = EarlyCtx {
        strict: prog.has_use_strict,
        in_function: false,
        allow_new_target: false,
        in_async: false,
        in_generator: false,
        in_formal_params: false,
        in_iteration: false,
        in_switch: false,
        labels: Vec::new(),
    };
    proof {
        assert(root_ctx.labels@ =~= Seq::<LabelEntry>::empty());
    }
    check_stmt_list(prog, prog.body.as_slice(), top_bound, &root_ctx)
}

} // verus!
