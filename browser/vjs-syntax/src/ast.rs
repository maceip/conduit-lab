//! ECMA-262 §13–16 Abstract Syntax Tree (Arena-backed DAG/Tree with machine-checked
//! topological `rank` acyclicity `wf` and syntactic grammar well-formedness `grammar_wf`).
use crate::token::{DiagnosticKind, Span, SyntaxDiagnostic, UnsupportedSyntax};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Arena Node Identifiers
// ---------------------------------------------------------------------------------------

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExprId(pub usize);

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub struct StmtId(pub usize);

// ---------------------------------------------------------------------------------------
// AST Operators & Leaf Structures
// ---------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ident {
    pub name: Vec<u8>,
    pub has_escape: bool,
    pub span: Span,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Param {
    pub name: Ident,
    pub default: Option<ExprId>,
    pub is_rest: bool,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    Delete,
    Void,
    Typeof,
    Plus,
    Minus,
    BitNot,
    Not,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum UpdateOp {
    Inc,
    Dec,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Mul,
    Div,
    Rem,
    Exp,
    Add,
    Sub,
    Shl,
    Shr,
    UShr,
    Lt,
    Gt,
    Le,
    Ge,
    Instanceof,
    In,
    EqEq,
    Ne,
    EqEqEq,
    NeEq,
    BitAnd,
    BitXor,
    BitOr,
    LogicalAnd,
    LogicalOr,
    Coalesce,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum AssignOp {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    ExpAssign,
    ShlAssign,
    ShrAssign,
    UShrAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    LogicalAndAssign,
    LogicalOrAssign,
    CoalesceAssign,
}

#[derive(Structural, Clone, Copy, PartialEq, Eq, Debug)]
pub enum VarDeclKind {
    Var,
    Let,
    Const,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ArrayElem {
    Hole,
    Elem(ExprId),
    Spread(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CallArg {
    Arg(ExprId),
    Spread(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PropKeyAst {
    Ident(Vec<u8>),
    StringLit {
        units: Vec<u16>,
        has_legacy_octal_escape: bool,
    },
    NumberLit {
        raw: Vec<u8>,
        is_bigint: bool,
        has_legacy_octal_or_leading_zero: bool,
    },
    Computed(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ObjPropKind {
    Init {
        key: PropKeyAst,
        value: ExprId,
        is_shorthand: bool,
        shorthand_ident: Option<Ident>,
    },
    Method {
        key: PropKeyAst,
        params: Vec<Param>,
        body: Vec<StmtId>,
        is_async: bool,
        is_generator: bool,
        body_has_use_strict: bool,
        has_directive_octal_escape: bool,
        span: Span,
    },
    Getter {
        key: PropKeyAst,
        body: Vec<StmtId>,
        body_has_use_strict: bool,
        has_directive_octal_escape: bool,
        span: Span,
    },
    Setter {
        key: PropKeyAst,
        param: Param,
        body: Vec<StmtId>,
        body_has_use_strict: bool,
        has_directive_octal_escape: bool,
        span: Span,
    },
    Spread(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ArrowBody {
    Expr(ExprId),
    Block {
        stmts: Vec<StmtId>,
        has_use_strict: bool,
        has_directive_octal_escape: bool,
    },
}

// ---------------------------------------------------------------------------------------
// Expressions (§13) & Statements (§14–15)
// ---------------------------------------------------------------------------------------

#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprKind {
    This,
    Null,
    Bool(bool),
    Number {
        raw: Vec<u8>,
        is_bigint: bool,
        has_legacy_octal_or_leading_zero: bool,
    },
    StringLit {
        units: Vec<u16>,
        has_legacy_octal_escape: bool,
    },
    TemplateNoSub {
        units: Vec<u16>,
        has_invalid_escape: bool,
    },
    Ident(Ident),
    Paren(ExprId),
    Array(Vec<ArrayElem>),
    Object(Vec<ObjPropKind>),
    Member {
        object: ExprId,
        property: Vec<u8>,
        optional: bool,
    },
    ComputedMember {
        object: ExprId,
        index: ExprId,
        optional: bool,
    },
    Call {
        callee: ExprId,
        args: Vec<CallArg>,
        optional: bool,
    },
    New {
        callee: ExprId,
        args: Vec<CallArg>,
    },
    NewTarget,
    Update {
        op: UpdateOp,
        prefix: bool,
        arg: ExprId,
    },
    Unary {
        op: UnaryOp,
        arg: ExprId,
    },
    Await(ExprId),
    Yield {
        delegate: bool,
        arg: Option<ExprId>,
    },
    Binary {
        op: BinOp,
        left: ExprId,
        right: ExprId,
    },
    Conditional {
        cond: ExprId,
        consequent: ExprId,
        alternate: ExprId,
    },
    Assign {
        op: AssignOp,
        left: ExprId,
        right: ExprId,
    },
    Sequence {
        left: ExprId,
        right: ExprId,
    },
    FunctionExpr {
        name: Option<Ident>,
        params: Vec<Param>,
        body: Vec<StmtId>,
        is_async: bool,
        is_generator: bool,
        body_has_use_strict: bool,
        has_directive_octal_escape: bool,
    },
    ArrowFunction {
        params: Vec<Param>,
        body: ArrowBody,
        is_async: bool,
    },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub rank: usize,
    pub in_optional_chain: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VarDeclarator {
    pub name: Ident,
    pub init: Option<ExprId>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ForInit {
    None,
    VarDecl {
        kind: VarDeclKind,
        decls: Vec<VarDeclarator>,
    },
    Expr(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ForInOfLhs {
    VarDecl {
        kind: VarDeclKind,
        name: Ident,
    },
    Expr(ExprId),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SwitchCase {
    pub test: Option<ExprId>,
    pub consequent: Vec<StmtId>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CatchClause {
    pub param: Option<Ident>,
    pub body: Vec<StmtId>,
}

#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StmtKind {
    Empty,
    Block(Vec<StmtId>),
    VarDecl {
        kind: VarDeclKind,
        decls: Vec<VarDeclarator>,
    },
    ExprStmt(ExprId),
    If {
        cond: ExprId,
        consequent: StmtId,
        alternate: Option<StmtId>,
    },
    While {
        cond: ExprId,
        body: StmtId,
    },
    DoWhile {
        body: StmtId,
        cond: ExprId,
    },
    For {
        init: ForInit,
        cond: Option<ExprId>,
        update: Option<ExprId>,
        body: StmtId,
    },
    ForIn {
        lhs: ForInOfLhs,
        rhs: ExprId,
        body: StmtId,
    },
    ForOf {
        lhs: ForInOfLhs,
        rhs: ExprId,
        is_await: bool,
        body: StmtId,
    },
    Switch {
        discriminant: ExprId,
        cases: Vec<SwitchCase>,
    },
    Return(Option<ExprId>),
    Break(Option<Ident>),
    Continue(Option<Ident>),
    Throw(ExprId),
    Try {
        block: Vec<StmtId>,
        catch_clause: Option<CatchClause>,
        finally_block: Option<Vec<StmtId>>,
    },
    With {
        object: ExprId,
        body: StmtId,
    },
    Labeled {
        label: Ident,
        body: StmtId,
    },
    Debugger,
    FunctionDecl {
        name: Ident,
        params: Vec<Param>,
        body: Vec<StmtId>,
        is_async: bool,
        is_generator: bool,
        body_has_use_strict: bool,
        has_directive_octal_escape: bool,
    },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub rank: usize,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Program {
    pub exprs: Vec<Expr>,
    pub stmts: Vec<Stmt>,
    pub body: Vec<StmtId>,
    pub has_use_strict: bool,
    pub has_directive_octal_escape: bool,
}

/// Spec-level view of `Program`.
pub struct SpecProgram {
    pub exprs: Seq<Expr>,
    pub stmts: Seq<Stmt>,
    pub body: Seq<StmtId>,
    pub has_use_strict: bool,
    pub has_directive_octal_escape: bool,
}

impl View for Program {
    type V = SpecProgram;

    open spec fn view(&self) -> SpecProgram {
        SpecProgram {
            exprs: self.exprs@,
            stmts: self.stmts@,
            body: self.body@,
            has_use_strict: self.has_use_strict,
            has_directive_octal_escape: self.has_directive_octal_escape,
        }
    }
}

/// Top-level result of parsing an ECMAScript program: `Ok` | `SyntaxError` | `Unsupported`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParseOutcome {
    Ok(Program),
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

pub enum SpecParseOutcome {
    Ok(SpecProgram),
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

impl View for ParseOutcome {
    type V = SpecParseOutcome;

    open spec fn view(&self) -> SpecParseOutcome {
        match self {
            ParseOutcome::Ok(p) => SpecParseOutcome::Ok(p@),
            ParseOutcome::SyntaxError(e) => SpecParseOutcome::SyntaxError(*e),
            ParseOutcome::Unsupported(u) => SpecParseOutcome::Unsupported(*u),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Structural Acyclicity (`wf`) & Syntactic Grammar Well-Formedness (`grammar_wf`) Specs
// ---------------------------------------------------------------------------------------

pub open spec fn expr_id_bounded(exprs: Seq<Expr>, id: ExprId, bound_rank: nat) -> bool {
    id.0 < exprs.len() && (exprs[id.0 as int].rank as nat) < bound_rank
}

pub open spec fn stmt_id_bounded(stmts: Seq<Stmt>, id: StmtId, bound_rank: nat) -> bool {
    id.0 < stmts.len() && (stmts[id.0 as int].rank as nat) < bound_rank
}

pub open spec fn opt_expr_bounded(exprs: Seq<Expr>, id_opt: Option<ExprId>, bound_rank: nat) -> bool {
    match id_opt {
        Some(id) => expr_id_bounded(exprs, id, bound_rank),
        None => true,
    }
}

pub open spec fn opt_stmt_bounded(stmts: Seq<Stmt>, id_opt: Option<StmtId>, bound_rank: nat) -> bool {
    match id_opt {
        Some(id) => stmt_id_bounded(stmts, id, bound_rank),
        None => true,
    }
}

pub open spec fn stmt_seq_bounded(stmts: Seq<Stmt>, ids: Seq<StmtId>, bound_rank: nat) -> bool {
    forall|k: int| 0 <= k < ids.len() ==> stmt_id_bounded(stmts, #[trigger] ids[k], bound_rank)
}

pub open spec fn params_bounded(exprs: Seq<Expr>, params: Seq<Param>, bound_rank: nat) -> bool {
    forall|k: int| 0 <= k < params.len() ==> opt_expr_bounded(exprs, (#[trigger] params[k]).default, bound_rank)
}

pub open spec fn array_elems_bounded(exprs: Seq<Expr>, elems: Seq<ArrayElem>, bound_rank: nat) -> bool {
    forall|k: int|
        0 <= k < elems.len() ==> match #[trigger] elems[k] {
            ArrayElem::Hole => true,
            ArrayElem::Elem(id) => expr_id_bounded(exprs, id, bound_rank),
            ArrayElem::Spread(id) => expr_id_bounded(exprs, id, bound_rank),
        }
}

pub open spec fn call_args_bounded(exprs: Seq<Expr>, args: Seq<CallArg>, bound_rank: nat) -> bool {
    forall|k: int|
        0 <= k < args.len() ==> match #[trigger] args[k] {
            CallArg::Arg(id) => expr_id_bounded(exprs, id, bound_rank),
            CallArg::Spread(id) => expr_id_bounded(exprs, id, bound_rank),
        }
}

pub open spec fn prop_key_bounded(exprs: Seq<Expr>, key: PropKeyAst, bound_rank: nat) -> bool {
    match key {
        PropKeyAst::Computed(id) => expr_id_bounded(exprs, id, bound_rank),
        _ => true,
    }
}

pub open spec fn obj_prop_bounded(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    prop: ObjPropKind,
    bound_rank: nat,
) -> bool {
    match prop {
        ObjPropKind::Init { key, value, .. } => {
            prop_key_bounded(exprs, key, bound_rank) && expr_id_bounded(exprs, value, bound_rank)
        },
        ObjPropKind::Method { key, params, body, .. } => {
            prop_key_bounded(exprs, key, bound_rank)
                && params_bounded(exprs, params@, bound_rank)
                && stmt_seq_bounded(stmts, body@, bound_rank)
        },
        ObjPropKind::Getter { key, body, .. } => {
            prop_key_bounded(exprs, key, bound_rank) && stmt_seq_bounded(stmts, body@, bound_rank)
        },
        ObjPropKind::Setter { key, param, body, .. } => {
            prop_key_bounded(exprs, key, bound_rank)
                && opt_expr_bounded(exprs, param.default, bound_rank)
                && stmt_seq_bounded(stmts, body@, bound_rank)
        },
        ObjPropKind::Spread(id) => expr_id_bounded(exprs, id, bound_rank),
    }
}

pub open spec fn obj_props_bounded(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    props: Seq<ObjPropKind>,
    bound_rank: nat,
) -> bool {
    forall|k: int| 0 <= k < props.len() ==> obj_prop_bounded(exprs, stmts, #[trigger] props[k], bound_rank)
}

pub open spec fn var_decls_bounded(
    exprs: Seq<Expr>,
    decls: Seq<VarDeclarator>,
    bound_rank: nat,
) -> bool {
    forall|k: int| 0 <= k < decls.len() ==> opt_expr_bounded(exprs, (#[trigger] decls[k]).init, bound_rank)
}

pub open spec fn switch_cases_bounded(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    cases: Seq<SwitchCase>,
    bound_rank: nat,
) -> bool {
    forall|k: int|
        0 <= k < cases.len() ==> (opt_expr_bounded(exprs, (#[trigger] cases[k]).test, bound_rank)
            && stmt_seq_bounded(stmts, cases[k].consequent@, bound_rank))
}

pub open spec fn expr_children_bounded(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    kind: ExprKind,
    bound_rank: nat,
) -> bool {
    match kind {
        ExprKind::This
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Number { .. }
        | ExprKind::StringLit { .. }
        | ExprKind::TemplateNoSub { .. }
        | ExprKind::Ident(_)
        | ExprKind::NewTarget => true,
        ExprKind::Paren(inner) | ExprKind::Await(inner) => expr_id_bounded(exprs, inner, bound_rank),
        ExprKind::Array(elems) => array_elems_bounded(exprs, elems@, bound_rank),
        ExprKind::Object(props) => obj_props_bounded(exprs, stmts, props@, bound_rank),
        ExprKind::Member { object, .. } => expr_id_bounded(exprs, object, bound_rank),
        ExprKind::ComputedMember { object, index, .. } => {
            expr_id_bounded(exprs, object, bound_rank) && expr_id_bounded(exprs, index, bound_rank)
        },
        ExprKind::Call { callee, args, .. } | ExprKind::New { callee, args } => {
            expr_id_bounded(exprs, callee, bound_rank) && call_args_bounded(exprs, args@, bound_rank)
        },
        ExprKind::Update { arg, .. } | ExprKind::Unary { arg, .. } => {
            expr_id_bounded(exprs, arg, bound_rank)
        },
        ExprKind::Yield { arg, .. } => opt_expr_bounded(exprs, arg, bound_rank),
        ExprKind::Binary { left, right, .. }
        | ExprKind::Assign { left, right, .. }
        | ExprKind::Sequence { left, right } => {
            expr_id_bounded(exprs, left, bound_rank) && expr_id_bounded(exprs, right, bound_rank)
        },
        ExprKind::Conditional { cond, consequent, alternate } => {
            expr_id_bounded(exprs, cond, bound_rank)
                && expr_id_bounded(exprs, consequent, bound_rank)
                && expr_id_bounded(exprs, alternate, bound_rank)
        },
        ExprKind::FunctionExpr { params, body, .. } => {
            params_bounded(exprs, params@, bound_rank) && stmt_seq_bounded(stmts, body@, bound_rank)
        },
        ExprKind::ArrowFunction { params, body, .. } => {
            params_bounded(exprs, params@, bound_rank)
                && match body {
                    ArrowBody::Expr(e) => expr_id_bounded(exprs, e, bound_rank),
                    ArrowBody::Block { stmts: b, .. } => stmt_seq_bounded(stmts, b@, bound_rank),
                }
        },
    }
}

pub open spec fn stmt_children_bounded(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    kind: StmtKind,
    bound_rank: nat,
) -> bool {
    match kind {
        StmtKind::Empty | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Debugger => true,
        StmtKind::Block(ids) => stmt_seq_bounded(stmts, ids@, bound_rank),
        StmtKind::VarDecl { decls, .. } => var_decls_bounded(exprs, decls@, bound_rank),
        StmtKind::ExprStmt(e) | StmtKind::Throw(e) => expr_id_bounded(exprs, e, bound_rank),
        StmtKind::Return(opt_e) => opt_expr_bounded(exprs, opt_e, bound_rank),
        StmtKind::If { cond, consequent, alternate } => {
            expr_id_bounded(exprs, cond, bound_rank)
                && stmt_id_bounded(stmts, consequent, bound_rank)
                && opt_stmt_bounded(stmts, alternate, bound_rank)
        },
        StmtKind::While { cond, body } | StmtKind::DoWhile { body, cond } => {
            expr_id_bounded(exprs, cond, bound_rank) && stmt_id_bounded(stmts, body, bound_rank)
        },
        StmtKind::For { init, cond, update, body } => {
            let init_ok = match init {
                ForInit::None => true,
                ForInit::VarDecl { decls, .. } => var_decls_bounded(exprs, decls@, bound_rank),
                ForInit::Expr(e) => expr_id_bounded(exprs, e, bound_rank),
            };
            init_ok
                && opt_expr_bounded(exprs, cond, bound_rank)
                && opt_expr_bounded(exprs, update, bound_rank)
                && stmt_id_bounded(stmts, body, bound_rank)
        },
        StmtKind::ForIn { lhs, rhs, body } | StmtKind::ForOf { lhs, rhs, body, .. } => {
            let lhs_ok = match lhs {
                ForInOfLhs::VarDecl { .. } => true,
                ForInOfLhs::Expr(e) => expr_id_bounded(exprs, e, bound_rank),
            };
            lhs_ok && expr_id_bounded(exprs, rhs, bound_rank) && stmt_id_bounded(stmts, body, bound_rank)
        },
        StmtKind::Switch { discriminant, cases } => {
            expr_id_bounded(exprs, discriminant, bound_rank)
                && switch_cases_bounded(exprs, stmts, cases@, bound_rank)
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            stmt_seq_bounded(stmts, block@, bound_rank)
                && (match catch_clause {
                    Some(cc) => stmt_seq_bounded(stmts, cc.body@, bound_rank),
                    None => true,
                })
                && (match finally_block {
                    Some(fb) => stmt_seq_bounded(stmts, fb@, bound_rank),
                    None => true,
                })
        },
        StmtKind::With { object, body } => {
            expr_id_bounded(exprs, object, bound_rank) && stmt_id_bounded(stmts, body, bound_rank)
        },
        StmtKind::Labeled { body, .. } => stmt_id_bounded(stmts, body, bound_rank),
        StmtKind::FunctionDecl { params, body, .. } => {
            params_bounded(exprs, params@, bound_rank) && stmt_seq_bounded(stmts, body@, bound_rank)
        },
    }
}

// Local index-only validity (used at parser call sites before `alloc_expr` / `alloc_stmt` assigns `rank`)
pub open spec fn expr_refs_in_bounds(exprs_len: nat, stmts_len: nat, kind: ExprKind) -> bool {
    match kind {
        ExprKind::This
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Number { .. }
        | ExprKind::StringLit { .. }
        | ExprKind::TemplateNoSub { .. }
        | ExprKind::Ident(_)
        | ExprKind::NewTarget => true,
        ExprKind::Paren(inner) | ExprKind::Await(inner) => inner.0 < exprs_len,
        ExprKind::Array(elems) => forall|k: int|
            0 <= k < elems@.len() ==> match #[trigger] elems@[k] {
                ArrayElem::Hole => true,
                ArrayElem::Elem(id) => id.0 < exprs_len,
                ArrayElem::Spread(id) => id.0 < exprs_len,
            },
        ExprKind::Object(props) => forall|k: int|
            0 <= k < props@.len() ==> match #[trigger] props@[k] {
                ObjPropKind::Init { key, value, .. } => {
                    (match key {
                        PropKeyAst::Computed(id) => id.0 < exprs_len,
                        _ => true,
                    }) && value.0 < exprs_len
                },
                ObjPropKind::Method { key, params, body, .. } => {
                    (match key {
                        PropKeyAst::Computed(id) => id.0 < exprs_len,
                        _ => true,
                    }) && (forall|p: int|
                        0 <= p < params@.len() ==> match (#[trigger] params@[p]).default {
                            Some(id) => id.0 < exprs_len,
                            None => true,
                        })
                        && (forall|s: int| 0 <= s < body@.len() ==> (#[trigger] body@[s]).0 < stmts_len)
                },
                ObjPropKind::Getter { key, body, .. } => {
                    (match key {
                        PropKeyAst::Computed(id) => id.0 < exprs_len,
                        _ => true,
                    }) && (forall|s: int| 0 <= s < body@.len() ==> (#[trigger] body@[s]).0 < stmts_len)
                },
                ObjPropKind::Setter { key, param, body, .. } => {
                    (match key {
                        PropKeyAst::Computed(id) => id.0 < exprs_len,
                        _ => true,
                    }) && (match param.default {
                        Some(id) => id.0 < exprs_len,
                        None => true,
                    }) && (forall|s: int| 0 <= s < body@.len() ==> (#[trigger] body@[s]).0 < stmts_len)
                },
                ObjPropKind::Spread(id) => id.0 < exprs_len,
            },
        ExprKind::Member { object, .. } => object.0 < exprs_len,
        ExprKind::ComputedMember { object, index, .. } => object.0 < exprs_len && index.0 < exprs_len,
        ExprKind::Call { callee, args, .. } => {
            callee.0 < exprs_len
                && forall|k: int|
                    0 <= k < args@.len() ==> match #[trigger] args@[k] {
                        CallArg::Arg(id) => id.0 < exprs_len,
                        CallArg::Spread(id) => id.0 < exprs_len,
                    }
        },
        ExprKind::New { callee, args } => {
            callee.0 < exprs_len
                && forall|k: int|
                    0 <= k < args@.len() ==> match #[trigger] args@[k] {
                        CallArg::Arg(id) => id.0 < exprs_len,
                        CallArg::Spread(id) => id.0 < exprs_len,
                    }
        },
        ExprKind::Update { arg, .. } | ExprKind::Unary { arg, .. } => arg.0 < exprs_len,
        ExprKind::Yield { arg, .. } => match arg {
            Some(id) => id.0 < exprs_len,
            None => true,
        },
        ExprKind::Binary { left, right, .. }
        | ExprKind::Assign { left, right, .. }
        | ExprKind::Sequence { left, right } => left.0 < exprs_len && right.0 < exprs_len,
        ExprKind::Conditional { cond, consequent, alternate } => {
            cond.0 < exprs_len && consequent.0 < exprs_len && alternate.0 < exprs_len
        },
        ExprKind::FunctionExpr { params, body, .. } => {
            (forall|p: int|
                0 <= p < params@.len() ==> match (#[trigger] params@[p]).default {
                    Some(id) => id.0 < exprs_len,
                    None => true,
                }) && (forall|s: int| 0 <= s < body@.len() ==> (#[trigger] body@[s]).0 < stmts_len)
        },
        ExprKind::ArrowFunction { params, body, .. } => {
            (forall|p: int|
                0 <= p < params@.len() ==> match (#[trigger] params@[p]).default {
                    Some(id) => id.0 < exprs_len,
                    None => true,
                })
                && match body {
                    ArrowBody::Expr(e) => e.0 < exprs_len,
                    ArrowBody::Block { stmts: b, .. } => {
                        forall|s: int| 0 <= s < b@.len() ==> (#[trigger] b@[s]).0 < stmts_len
                    },
                }
        },
    }
}

pub open spec fn stmt_refs_in_bounds(exprs_len: nat, stmts_len: nat, kind: StmtKind) -> bool {
    match kind {
        StmtKind::Empty | StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Debugger => true,
        StmtKind::Block(ids) => forall|s: int| 0 <= s < ids@.len() ==> (#[trigger] ids@[s]).0 < stmts_len,
        StmtKind::VarDecl { decls, .. } => forall|k: int|
            0 <= k < decls@.len() ==> match (#[trigger] decls@[k]).init {
                Some(id) => id.0 < exprs_len,
                None => true,
            },
        StmtKind::ExprStmt(e) | StmtKind::Throw(e) => e.0 < exprs_len,
        StmtKind::Return(opt_e) => match opt_e {
            Some(id) => id.0 < exprs_len,
            None => true,
        },
        StmtKind::If { cond, consequent, alternate } => {
            cond.0 < exprs_len
                && consequent.0 < stmts_len
                && match alternate {
                    Some(alt) => alt.0 < stmts_len,
                    None => true,
                }
        },
        StmtKind::While { cond, body } | StmtKind::DoWhile { body, cond } => {
            cond.0 < exprs_len && body.0 < stmts_len
        },
        StmtKind::For { init, cond, update, body } => {
            let init_ok = match init {
                ForInit::None => true,
                ForInit::VarDecl { decls, .. } => forall|k: int|
                    0 <= k < decls@.len() ==> match (#[trigger] decls@[k]).init {
                        Some(id) => id.0 < exprs_len,
                        None => true,
                    },
                ForInit::Expr(e) => e.0 < exprs_len,
            };
            init_ok
                && (match cond {
                    Some(id) => id.0 < exprs_len,
                    None => true,
                })
                && (match update {
                    Some(id) => id.0 < exprs_len,
                    None => true,
                })
                && body.0 < stmts_len
        },
        StmtKind::ForIn { lhs, rhs, body } | StmtKind::ForOf { lhs, rhs, body, .. } => {
            (match lhs {
                ForInOfLhs::VarDecl { .. } => true,
                ForInOfLhs::Expr(e) => e.0 < exprs_len,
            }) && rhs.0 < exprs_len && body.0 < stmts_len
        },
        StmtKind::Switch { discriminant, cases } => {
            discriminant.0 < exprs_len
                && forall|k: int|
                    0 <= k < cases@.len() ==> ((match (#[trigger] cases@[k]).test {
                        Some(id) => id.0 < exprs_len,
                        None => true,
                    }) && forall|s: int|
                        0 <= s < cases@[k].consequent@.len()
                            ==> (#[trigger] cases@[k].consequent@[s]).0 < stmts_len)
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            (forall|s: int| 0 <= s < block@.len() ==> (#[trigger] block@[s]).0 < stmts_len)
                && (match catch_clause {
                    Some(cc) => forall|s: int| 0 <= s < cc.body@.len() ==> (#[trigger] cc.body@[s]).0 < stmts_len,
                    None => true,
                })
                && (match finally_block {
                    Some(fb) => forall|s: int| 0 <= s < fb@.len() ==> (#[trigger] fb@[s]).0 < stmts_len,
                    None => true,
                })
        },
        StmtKind::With { object, body } => object.0 < exprs_len && body.0 < stmts_len,
        StmtKind::Labeled { body, .. } => body.0 < stmts_len,
        StmtKind::FunctionDecl { params, body, .. } => {
            (forall|p: int|
                0 <= p < params@.len() ==> match (#[trigger] params@[p]).default {
                    Some(id) => id.0 < exprs_len,
                    None => true,
                }) && (forall|s: int| 0 <= s < body@.len() ==> (#[trigger] body@[s]).0 < stmts_len)
        },
    }
}

// ---------------------------------------------------------------------------------------
// Syntactic Grammar Well-Formedness Predicates (`grammar_wf`)
// ---------------------------------------------------------------------------------------

/// Whether `e` is an unparenthesized `LogicalAnd` or `LogicalOr` expression (§13.13).
pub open spec fn spec_is_unparen_logical_and_or(e: Expr) -> bool {
    match e.kind {
        ExprKind::Binary { op: BinOp::LogicalAnd, .. } => true,
        ExprKind::Binary { op: BinOp::LogicalOr, .. } => true,
        _ => false,
    }
}

/// Whether `e` is an unparenthesized `Coalesce` (`??`) expression (§13.13).
pub open spec fn spec_is_unparen_coalesce(e: Expr) -> bool {
    match e.kind {
        ExprKind::Binary { op: BinOp::Coalesce, .. } => true,
        _ => false,
    }
}

/// Whether `e` is an unparenthesized `Unary` or `Await` expression (forbidden on LHS of `**` per §13.6).
pub open spec fn spec_is_unparen_unary_or_await(e: Expr) -> bool {
    match e.kind {
        ExprKind::Unary { .. } | ExprKind::Await(_) => true,
        _ => false,
    }
}

/// Rest parameter finality & no-default invariant (§15.1).
pub open spec fn spec_params_grammar_wf(params: Seq<Param>) -> bool {
    forall|k: int|
        0 <= k < params.len() ==> ((#[trigger] params[k]).is_rest ==> (params[k].default is None
            && k == params.len() - 1))
}

/// Local syntactic grammar well-formedness for a single `ExprKind`.
pub open spec fn expr_grammar_local_wf(exprs: Seq<Expr>, kind: ExprKind) -> bool {
    match kind {
        ExprKind::Binary { op: BinOp::Coalesce, left, right } => {
            left.0 < exprs.len()
                && right.0 < exprs.len()
                && !spec_is_unparen_logical_and_or(exprs[left.0 as int])
                && !spec_is_unparen_logical_and_or(exprs[right.0 as int])
        },
        ExprKind::Binary { op: BinOp::LogicalAnd, left, right } => {
            left.0 < exprs.len()
                && right.0 < exprs.len()
                && !spec_is_unparen_coalesce(exprs[left.0 as int])
                && !spec_is_unparen_coalesce(exprs[right.0 as int])
        },
        ExprKind::Binary { op: BinOp::LogicalOr, left, right } => {
            left.0 < exprs.len()
                && right.0 < exprs.len()
                && !spec_is_unparen_coalesce(exprs[left.0 as int])
                && !spec_is_unparen_coalesce(exprs[right.0 as int])
        },
        ExprKind::Binary { op: BinOp::Exp, left, .. } => {
            left.0 < exprs.len() && !spec_is_unparen_unary_or_await(exprs[left.0 as int])
        },
        ExprKind::New { callee, .. } => {
            callee.0 < exprs.len() && !exprs[callee.0 as int].in_optional_chain
        },
        ExprKind::FunctionExpr { params, .. } => {
            spec_params_grammar_wf(params@)
        },
        ExprKind::ArrowFunction { params, .. } => {
            spec_params_grammar_wf(params@)
        },
        ExprKind::Object(props) => forall|k: int|
            0 <= k < props@.len() ==> match #[trigger] props@[k] {
                ObjPropKind::Method { params, .. } => spec_params_grammar_wf(params@),
                ObjPropKind::Setter { param, .. } => !param.is_rest,
                _ => true,
            },
        _ => true,
    }
}

pub open spec fn spec_count_default_cases(cases: Seq<SwitchCase>) -> nat
    decreases cases.len(),
{
    if cases.len() == 0 {
        0
    } else {
        let rest = spec_count_default_cases(cases.drop_last());
        if cases.last().test is None {
            rest + 1
        } else {
            rest
        }
    }
}

/// Local syntactic grammar well-formedness for a single `StmtKind`.
pub open spec fn stmt_grammar_local_wf(kind: StmtKind) -> bool {
    match kind {
        StmtKind::VarDecl { kind: vk, decls } => {
            decls@.len() >= 1
                && (vk == VarDeclKind::Const ==> forall|k: int|
                    0 <= k < decls@.len() ==> (#[trigger] decls@[k]).init is Some)
        },
        StmtKind::For { init: ForInit::VarDecl { kind: vk, decls }, .. } => {
            decls@.len() >= 1
                && (vk == VarDeclKind::Const ==> forall|k: int|
                    0 <= k < decls@.len() ==> (#[trigger] decls@[k]).init is Some)
        },
        StmtKind::Try { catch_clause, finally_block, .. } => {
            catch_clause is Some || finally_block is Some
        },
        StmtKind::Switch { cases, .. } => spec_count_default_cases(cases@) <= 1,
        StmtKind::FunctionDecl { params, .. } => spec_params_grammar_wf(params@),
        _ => true,
    }
}

impl SpecProgram {
    /// Complete structural & topological DAG acyclicity invariant:
    /// every `ExprId`/`StmtId` is in bounds and has strictly smaller `rank` than its parent.
    pub open spec fn wf(self) -> bool {
        self.exprs.len() + self.stmts.len() <= usize::MAX
            && (forall|i: int|
                0 <= i < self.exprs.len() ==> (
                    ((#[trigger] self.exprs[i]).rank as nat) < self.exprs.len() + self.stmts.len()
                        && expr_children_bounded(
                            self.exprs,
                            self.stmts,
                            self.exprs[i].kind,
                            self.exprs[i].rank as nat,
                        )
                ))
            && (forall|j: int|
                0 <= j < self.stmts.len() ==> (
                    ((#[trigger] self.stmts[j]).rank as nat) < self.exprs.len() + self.stmts.len()
                        && stmt_children_bounded(
                            self.exprs,
                            self.stmts,
                            self.stmts[j].kind,
                            self.stmts[j].rank as nat,
                        )
                ))
            && (forall|k: int| 0 <= k < self.body.len() ==> (#[trigger] self.body[k]).0 < self.stmts.len())
    }

    /// Syntactic grammar well-formedness across every expression and statement node in the AST.
    pub open spec fn grammar_wf(self) -> bool {
        self.wf()
            && (forall|i: int|
                0 <= i < self.exprs.len() ==> expr_grammar_local_wf(self.exprs, (#[trigger] self.exprs[i]).kind))
            && (forall|j: int|
                0 <= j < self.stmts.len() ==> stmt_grammar_local_wf((#[trigger] self.stmts[j]).kind))
    }
}

impl Program {
    pub open spec fn wf(&self) -> bool {
        self@.wf()
    }

    pub open spec fn grammar_wf(&self) -> bool {
        self@.grammar_wf()
    }
}

// ---------------------------------------------------------------------------------------
// Framing Lemmas & Verified Bottom-Up Arena Allocation (`AstArena`)
// ---------------------------------------------------------------------------------------

pub proof fn lemma_expr_children_frame_push_expr(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    new_e: Expr,
    kind: ExprKind,
    bound_rank: nat,
)
    requires
        expr_children_bounded(exprs, stmts, kind, bound_rank),
    ensures
        expr_children_bounded(exprs.push(new_e), stmts, kind, bound_rank),
{
    let exprs2 = exprs.push(new_e);
    match kind {
        ExprKind::Array(elems) => {
            assert forall|k: int| 0 <= k < elems@.len() implies match #[trigger] elems@[k] {
                ArrayElem::Hole => true,
                ArrayElem::Elem(id) => expr_id_bounded(exprs2, id, bound_rank),
                ArrayElem::Spread(id) => expr_id_bounded(exprs2, id, bound_rank),
            } by {
                match elems@[k] {
                    ArrayElem::Hole => {},
                    ArrayElem::Elem(id) | ArrayElem::Spread(id) => {
                        assert(exprs2[id.0 as int] == exprs[id.0 as int]);
                    },
                }
            }
        },
        ExprKind::Object(props) => {
            assert forall|k: int| 0 <= k < props@.len() implies obj_prop_bounded(
                exprs2,
                stmts,
                #[trigger] props@[k],
                bound_rank,
            ) by {
                assert(obj_prop_bounded(exprs, stmts, props@[k], bound_rank));
                match props@[k] {
                    ObjPropKind::Init { key, value, .. } => {
                        assert(exprs2[value.0 as int] == exprs[value.0 as int]);
                        if let PropKeyAst::Computed(cid) = key {
                            assert(exprs2[cid.0 as int] == exprs[cid.0 as int]);
                        }
                    },
                    ObjPropKind::Method { key, params, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert(exprs2[cid.0 as int] == exprs[cid.0 as int]);
                        }
                        assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                            exprs2,
                            (#[trigger] params@[p]).default,
                            bound_rank,
                        ) by {
                            assert(opt_expr_bounded(exprs, params@[p].default, bound_rank));
                        }
                    },
                    ObjPropKind::Getter { key, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert(exprs2[cid.0 as int] == exprs[cid.0 as int]);
                        }
                    },
                    ObjPropKind::Setter { key, param, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert(exprs2[cid.0 as int] == exprs[cid.0 as int]);
                        }
                        if let Some(did) = param.default {
                            assert(exprs2[did.0 as int] == exprs[did.0 as int]);
                        }
                    },
                    ObjPropKind::Spread(id) => {
                        assert(exprs2[id.0 as int] == exprs[id.0 as int]);
                    },
                }
            }
        },
        ExprKind::Call { callee, args, .. } | ExprKind::New { callee, args } => {
            assert(exprs2[callee.0 as int] == exprs[callee.0 as int]);
            assert forall|k: int| 0 <= k < args@.len() implies match #[trigger] args@[k] {
                CallArg::Arg(id) => expr_id_bounded(exprs2, id, bound_rank),
                CallArg::Spread(id) => expr_id_bounded(exprs2, id, bound_rank),
            } by {
                match args@[k] {
                    CallArg::Arg(id) | CallArg::Spread(id) => {
                        assert(exprs2[id.0 as int] == exprs[id.0 as int]);
                    },
                }
            }
        },
        ExprKind::FunctionExpr { params, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                exprs2,
                (#[trigger] params@[p]).default,
                bound_rank,
            ) by {
                assert(opt_expr_bounded(exprs, params@[p].default, bound_rank));
            }
        },
        ExprKind::ArrowFunction { params, body, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                exprs2,
                (#[trigger] params@[p]).default,
                bound_rank,
            ) by {
                assert(opt_expr_bounded(exprs, params@[p].default, bound_rank));
            }
            if let ArrowBody::Expr(e) = body {
                assert(exprs2[e.0 as int] == exprs[e.0 as int]);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_stmt_children_frame_push_expr(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    new_e: Expr,
    kind: StmtKind,
    bound_rank: nat,
)
    requires
        stmt_children_bounded(exprs, stmts, kind, bound_rank),
    ensures
        stmt_children_bounded(exprs.push(new_e), stmts, kind, bound_rank),
{
    let exprs2 = exprs.push(new_e);
    match kind {
        StmtKind::VarDecl { decls, .. } => {
            assert forall|k: int| 0 <= k < decls@.len() implies opt_expr_bounded(
                exprs2,
                (#[trigger] decls@[k]).init,
                bound_rank,
            ) by {
                assert(opt_expr_bounded(exprs, decls@[k].init, bound_rank));
            }
        },
        StmtKind::For { init, .. } => {
            if let ForInit::VarDecl { decls, .. } = init {
                assert forall|k: int| 0 <= k < decls@.len() implies opt_expr_bounded(
                    exprs2,
                    (#[trigger] decls@[k]).init,
                    bound_rank,
                ) by {
                    assert(opt_expr_bounded(exprs, decls@[k].init, bound_rank));
                }
            }
        },
        StmtKind::Switch { discriminant, cases } => {
            assert(exprs2[discriminant.0 as int] == exprs[discriminant.0 as int]);
            assert forall|k: int| 0 <= k < cases@.len() implies (opt_expr_bounded(
                exprs2,
                (#[trigger] cases@[k]).test,
                bound_rank,
            ) && stmt_seq_bounded(stmts, cases@[k].consequent@, bound_rank)) by {
                assert(opt_expr_bounded(exprs, cases@[k].test, bound_rank));
            }
        },
        StmtKind::FunctionDecl { params, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                exprs2,
                (#[trigger] params@[p]).default,
                bound_rank,
            ) by {
                assert(opt_expr_bounded(exprs, params@[p].default, bound_rank));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_expr_children_frame_push_stmt(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    new_s: Stmt,
    kind: ExprKind,
    bound_rank: nat,
)
    requires
        expr_children_bounded(exprs, stmts, kind, bound_rank),
    ensures
        expr_children_bounded(exprs, stmts.push(new_s), kind, bound_rank),
{
    let stmts2 = stmts.push(new_s);
    match kind {
        ExprKind::Object(props) => {
            assert forall|k: int| 0 <= k < props@.len() implies obj_prop_bounded(
                exprs,
                stmts2,
                #[trigger] props@[k],
                bound_rank,
            ) by {
                assert(obj_prop_bounded(exprs, stmts, props@[k], bound_rank));
                match props@[k] {
                    ObjPropKind::Method { body, .. }
                    | ObjPropKind::Getter { body, .. }
                    | ObjPropKind::Setter { body, .. } => {
                        assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                            stmts2,
                            #[trigger] body@[s],
                            bound_rank,
                        ) by {
                            assert(stmt_id_bounded(stmts, body@[s], bound_rank));
                        }
                    },
                    _ => {},
                }
            }
        },
        ExprKind::FunctionExpr { body, .. } => {
            assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                stmts2,
                #[trigger] body@[s],
                bound_rank,
            ) by {
                assert(stmt_id_bounded(stmts, body@[s], bound_rank));
            }
        },
        ExprKind::ArrowFunction { body: ArrowBody::Block { stmts: b, .. }, .. } => {
            assert forall|s: int| 0 <= s < b@.len() implies stmt_id_bounded(
                stmts2,
                #[trigger] b@[s],
                bound_rank,
            ) by {
                assert(stmt_id_bounded(stmts, b@[s], bound_rank));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_stmt_children_frame_push_stmt(
    exprs: Seq<Expr>,
    stmts: Seq<Stmt>,
    new_s: Stmt,
    kind: StmtKind,
    bound_rank: nat,
)
    requires
        stmt_children_bounded(exprs, stmts, kind, bound_rank),
    ensures
        stmt_children_bounded(exprs, stmts.push(new_s), kind, bound_rank),
{
    let stmts2 = stmts.push(new_s);
    match kind {
        StmtKind::Block(ids) => {
            assert forall|s: int| 0 <= s < ids@.len() implies stmt_id_bounded(
                stmts2,
                #[trigger] ids@[s],
                bound_rank,
            ) by {
                assert(stmt_id_bounded(stmts, ids@[s], bound_rank));
            }
        },
        StmtKind::Switch { cases, .. } => {
            assert forall|k: int| 0 <= k < cases@.len() implies (opt_expr_bounded(
                exprs,
                (#[trigger] cases@[k]).test,
                bound_rank,
            ) && stmt_seq_bounded(stmts2, cases@[k].consequent@, bound_rank)) by {
                assert(opt_expr_bounded(exprs, cases@[k].test, bound_rank));
                assert(stmt_seq_bounded(stmts, cases@[k].consequent@, bound_rank));
                assert forall|s: int| 0 <= s < cases@[k].consequent@.len() implies stmt_id_bounded(
                    stmts2,
                    #[trigger] cases@[k].consequent@[s],
                    bound_rank,
                ) by {
                    assert(stmt_id_bounded(stmts, cases@[k].consequent@[s], bound_rank));
                }
            }
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            assert forall|s: int| 0 <= s < block@.len() implies stmt_id_bounded(
                stmts2,
                #[trigger] block@[s],
                bound_rank,
            ) by {
                assert(stmt_id_bounded(stmts, block@[s], bound_rank));
            }
            if let Some(cc) = catch_clause {
                assert forall|s: int| 0 <= s < cc.body@.len() implies stmt_id_bounded(
                    stmts2,
                    #[trigger] cc.body@[s],
                    bound_rank,
                ) by {
                    assert(stmt_id_bounded(stmts, cc.body@[s], bound_rank));
                }
            }
            if let Some(fb) = finally_block {
                assert forall|s: int| 0 <= s < fb@.len() implies stmt_id_bounded(
                    stmts2,
                    #[trigger] fb@[s],
                    bound_rank,
                ) by {
                    assert(stmt_id_bounded(stmts, fb@[s], bound_rank));
                }
            }
        },
        StmtKind::FunctionDecl { body, .. } => {
            assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                stmts2,
                #[trigger] body@[s],
                bound_rank,
            ) by {
                assert(stmt_id_bounded(stmts, body@[s], bound_rank));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_refs_to_bounded_expr(
    prog: SpecProgram,
    kind: ExprKind,
)
    requires
        prog.wf(),
        expr_refs_in_bounds(prog.exprs.len(), prog.stmts.len(), kind),
    ensures
        expr_children_bounded(prog.exprs, prog.stmts, kind, prog.exprs.len() + prog.stmts.len()),
{
    let r = prog.exprs.len() + prog.stmts.len();
    match kind {
        ExprKind::Array(elems) => {
            assert forall|k: int| 0 <= k < elems@.len() implies match #[trigger] elems@[k] {
                ArrayElem::Hole => true,
                ArrayElem::Elem(id) => expr_id_bounded(prog.exprs, id, r),
                ArrayElem::Spread(id) => expr_id_bounded(prog.exprs, id, r),
            } by {
                match elems@[k] {
                    ArrayElem::Hole => {},
                    ArrayElem::Elem(id) | ArrayElem::Spread(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                }
            }
        },
        ExprKind::Object(props) => {
            assert forall|k: int| 0 <= k < props@.len() implies obj_prop_bounded(
                prog.exprs,
                prog.stmts,
                #[trigger] props@[k],
                r,
            ) by {
                match props@[k] {
                    ObjPropKind::Init { key, value, .. } => {
                        assert((prog.exprs[value.0 as int].rank as nat) < r);
                        if let PropKeyAst::Computed(cid) = key {
                            assert((prog.exprs[cid.0 as int].rank as nat) < r);
                        }
                    },
                    ObjPropKind::Method { key, params, body, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert((prog.exprs[cid.0 as int].rank as nat) < r);
                        }
                        assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                            prog.exprs,
                            (#[trigger] params@[p]).default,
                            r,
                        ) by {
                            if let Some(did) = params@[p].default {
                                assert((prog.exprs[did.0 as int].rank as nat) < r);
                            }
                        }
                        assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                            prog.stmts,
                            #[trigger] body@[s],
                            r,
                        ) by {
                            let sid = body@[s];
                            assert((prog.stmts[sid.0 as int].rank as nat) < r);
                        }
                    },
                    ObjPropKind::Getter { key, body, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert((prog.exprs[cid.0 as int].rank as nat) < r);
                        }
                        assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                            prog.stmts,
                            #[trigger] body@[s],
                            r,
                        ) by {
                            let sid = body@[s];
                            assert((prog.stmts[sid.0 as int].rank as nat) < r);
                        }
                    },
                    ObjPropKind::Setter { key, param, body, .. } => {
                        if let PropKeyAst::Computed(cid) = key {
                            assert((prog.exprs[cid.0 as int].rank as nat) < r);
                        }
                        if let Some(did) = param.default {
                            assert((prog.exprs[did.0 as int].rank as nat) < r);
                        }
                        assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                            prog.stmts,
                            #[trigger] body@[s],
                            r,
                        ) by {
                            let sid = body@[s];
                            assert((prog.stmts[sid.0 as int].rank as nat) < r);
                        }
                    },
                    ObjPropKind::Spread(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                }
            }
        },
        ExprKind::Call { callee, args, .. } => {
            assert((prog.exprs[callee.0 as int].rank as nat) < r);
            assert forall|k: int| 0 <= k < args@.len() implies match #[trigger] args@[k] {
                CallArg::Arg(id) => expr_id_bounded(prog.exprs, id, r),
                CallArg::Spread(id) => expr_id_bounded(prog.exprs, id, r),
            } by {
                match args@[k] {
                    CallArg::Arg(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                    CallArg::Spread(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                }
            }
        },
        ExprKind::New { callee, args } => {
            assert((prog.exprs[callee.0 as int].rank as nat) < r);
            assert forall|k: int| 0 <= k < args@.len() implies match #[trigger] args@[k] {
                CallArg::Arg(id) => expr_id_bounded(prog.exprs, id, r),
                CallArg::Spread(id) => expr_id_bounded(prog.exprs, id, r),
            } by {
                match args@[k] {
                    CallArg::Arg(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                    CallArg::Spread(id) => {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    },
                }
            }
        },
        ExprKind::FunctionExpr { params, body, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                prog.exprs,
                (#[trigger] params@[p]).default,
                r,
            ) by {
                if let Some(did) = params@[p].default {
                    assert((prog.exprs[did.0 as int].rank as nat) < r);
                }
            }
            assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                prog.stmts,
                #[trigger] body@[s],
                r,
            ) by {
                let sid = body@[s];
                assert((prog.stmts[sid.0 as int].rank as nat) < r);
            }
        },
        ExprKind::ArrowFunction { params, body, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                prog.exprs,
                (#[trigger] params@[p]).default,
                r,
            ) by {
                if let Some(did) = params@[p].default {
                    assert((prog.exprs[did.0 as int].rank as nat) < r);
                }
            }
            match body {
                ArrowBody::Expr(e) => {
                    assert((prog.exprs[e.0 as int].rank as nat) < r);
                },
                ArrowBody::Block { stmts: b, .. } => {
                    assert forall|s: int| 0 <= s < b@.len() implies stmt_id_bounded(
                        prog.stmts,
                        #[trigger] b@[s],
                        r,
                    ) by {
                        let sid = b@[s];
                        assert((prog.stmts[sid.0 as int].rank as nat) < r);
                    }
                },
            }
        },
        _ => {},
    }
}

pub proof fn lemma_refs_to_bounded_stmt(
    prog: SpecProgram,
    kind: StmtKind,
)
    requires
        prog.wf(),
        stmt_refs_in_bounds(prog.exprs.len(), prog.stmts.len(), kind),
    ensures
        stmt_children_bounded(prog.exprs, prog.stmts, kind, prog.exprs.len() + prog.stmts.len()),
{
    let r = prog.exprs.len() + prog.stmts.len();
    match kind {
        StmtKind::Block(ids) => {
            assert forall|s: int| 0 <= s < ids@.len() implies stmt_id_bounded(
                prog.stmts,
                #[trigger] ids@[s],
                r,
            ) by {
                let sid = ids@[s];
                assert((prog.stmts[sid.0 as int].rank as nat) < r);
            }
        },
        StmtKind::VarDecl { decls, .. } => {
            assert forall|k: int| 0 <= k < decls@.len() implies opt_expr_bounded(
                prog.exprs,
                (#[trigger] decls@[k]).init,
                r,
            ) by {
                if let Some(id) = decls@[k].init {
                    assert((prog.exprs[id.0 as int].rank as nat) < r);
                }
            }
        },
        StmtKind::For { init, cond, update, body } => {
            if let ForInit::VarDecl { decls, .. } = init {
                assert forall|k: int| 0 <= k < decls@.len() implies opt_expr_bounded(
                    prog.exprs,
                    (#[trigger] decls@[k]).init,
                    r,
                ) by {
                    if let Some(id) = decls@[k].init {
                        assert((prog.exprs[id.0 as int].rank as nat) < r);
                    }
                }
            }
            if let Some(c) = cond {
                assert((prog.exprs[c.0 as int].rank as nat) < r);
            }
            if let Some(u) = update {
                assert((prog.exprs[u.0 as int].rank as nat) < r);
            }
            assert((prog.stmts[body.0 as int].rank as nat) < r);
        },
        StmtKind::Switch { discriminant, cases } => {
            assert((prog.exprs[discriminant.0 as int].rank as nat) < r);
            assert forall|k: int| 0 <= k < cases@.len() implies (opt_expr_bounded(
                prog.exprs,
                (#[trigger] cases@[k]).test,
                r,
            ) && stmt_seq_bounded(prog.stmts, cases@[k].consequent@, r)) by {
                if let Some(tid) = cases@[k].test {
                    assert((prog.exprs[tid.0 as int].rank as nat) < r);
                }
                assert forall|s: int| 0 <= s < cases@[k].consequent@.len() implies stmt_id_bounded(
                    prog.stmts,
                    #[trigger] cases@[k].consequent@[s],
                    r,
                ) by {
                    let sid = cases@[k].consequent@[s];
                    assert((prog.stmts[sid.0 as int].rank as nat) < r);
                }
            }
        },
        StmtKind::Try { block, catch_clause, finally_block } => {
            assert forall|s: int| 0 <= s < block@.len() implies stmt_id_bounded(
                prog.stmts,
                #[trigger] block@[s],
                r,
            ) by {
                let sid = block@[s];
                assert((prog.stmts[sid.0 as int].rank as nat) < r);
            }
            if let Some(cc) = catch_clause {
                assert forall|s: int| 0 <= s < cc.body@.len() implies stmt_id_bounded(
                    prog.stmts,
                    #[trigger] cc.body@[s],
                    r,
                ) by {
                    let sid = cc.body@[s];
                    assert((prog.stmts[sid.0 as int].rank as nat) < r);
                }
            }
            if let Some(fb) = finally_block {
                assert forall|s: int| 0 <= s < fb@.len() implies stmt_id_bounded(
                    prog.stmts,
                    #[trigger] fb@[s],
                    r,
                ) by {
                    let sid = fb@[s];
                    assert((prog.stmts[sid.0 as int].rank as nat) < r);
                }
            }
        },
        StmtKind::FunctionDecl { params, body, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies opt_expr_bounded(
                prog.exprs,
                (#[trigger] params@[p]).default,
                r,
            ) by {
                if let Some(did) = params@[p].default {
                    assert((prog.exprs[did.0 as int].rank as nat) < r);
                }
            }
            assert forall|s: int| 0 <= s < body@.len() implies stmt_id_bounded(
                prog.stmts,
                #[trigger] body@[s],
                r,
            ) by {
                let sid = body@[s];
                assert((prog.stmts[sid.0 as int].rank as nat) < r);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_expr_grammar_frame_push_expr(
    exprs: Seq<Expr>,
    new_e: Expr,
    kind: ExprKind,
)
    requires
        expr_grammar_local_wf(exprs, kind),
    ensures
        expr_grammar_local_wf(exprs.push(new_e), kind),
{
    let exprs2 = exprs.push(new_e);
    match kind {
        ExprKind::Binary { op: BinOp::Coalesce, left, right }
        | ExprKind::Binary { op: BinOp::LogicalAnd, left, right }
        | ExprKind::Binary { op: BinOp::LogicalOr, left, right } => {
            assert(exprs2[left.0 as int] == exprs[left.0 as int]);
            assert(exprs2[right.0 as int] == exprs[right.0 as int]);
        },
        ExprKind::Binary { op: BinOp::Exp, left, .. } => {
            assert(exprs2[left.0 as int] == exprs[left.0 as int]);
        },
        ExprKind::New { callee, .. } => {
            assert(exprs2[callee.0 as int] == exprs[callee.0 as int]);
        },
        _ => {},
    }
}

impl Program {
    /// Construct an empty well-formed `Program` arena.
    pub fn new() -> (p: Program)
        ensures
            p.wf(),
            p.grammar_wf(),
            p.exprs@.len() == 0,
            p.stmts@.len() == 0,
            p.body@.len() == 0,
    {
        Program {
            exprs: Vec::new(),
            stmts: Vec::new(),
            body: Vec::new(),
            has_use_strict: false,
            has_directive_octal_escape: false,
        }
    }

    /// Allocate a new bottom-up `Expr` node, preserving `wf` and `grammar_wf` by construction.
    pub fn alloc_expr(
        &mut self,
        kind: ExprKind,
        span: Span,
        in_optional_chain: bool,
    ) -> (res: Result<ExprId, SyntaxDiagnostic>)
        requires
            old(self).grammar_wf(),
            expr_refs_in_bounds(old(self).exprs@.len(), old(self).stmts@.len(), kind),
            expr_grammar_local_wf(old(self).exprs@, kind),
        ensures
            final(self).grammar_wf(),
            old(self).exprs@.len() <= final(self).exprs@.len(),
            old(self).stmts@ == final(self).stmts@,
            old(self).body@ == final(self).body@,
            forall|i: int| 0 <= i < old(self).exprs@.len() ==> #[trigger] final(self).exprs@[i] == old(self).exprs@[i],
            match res {
                Ok(id) => {
                    id.0 == old(self).exprs@.len()
                        && final(self).exprs@.len() == old(self).exprs@.len() + 1
                        && final(self).exprs@[id.0 as int].kind == kind
                        && final(self).exprs@[id.0 as int].span == span
                        && final(self).exprs@[id.0 as int].in_optional_chain == in_optional_chain
                },
                Err(_) => final(self)@ == old(self)@,
            },
    {
        let elen = self.exprs.len();
        let slen = self.stmts.len();
        if elen >= usize::MAX - slen {
            return Err(SyntaxDiagnostic {
                kind: DiagnosticKind::AstArenaOverflow,
                span,
            });
        }
        let rank = elen + slen;
        let ghost old_prog = self@;
        let node = Expr { kind, span, rank, in_optional_chain };
        let ghost g_node = node;
        proof {
            lemma_refs_to_bounded_expr(old_prog, g_node.kind);
            lemma_expr_children_frame_push_expr(
                old_prog.exprs,
                old_prog.stmts,
                g_node,
                g_node.kind,
                rank as nat,
            );
        }
        self.exprs.push(node);
        proof {
            let new_exprs = self.exprs@;
            assert forall|i: int| 0 <= i < new_exprs.len() implies (
                ((#[trigger] new_exprs[i]).rank as nat) < new_exprs.len() + self.stmts@.len()
                    && expr_children_bounded(
                        new_exprs,
                        self.stmts@,
                        new_exprs[i].kind,
                        new_exprs[i].rank as nat,
                    )
                    && expr_grammar_local_wf(new_exprs, new_exprs[i].kind)
            ) by {
                if i < old_prog.exprs.len() {
                    assert(new_exprs[i] == old_prog.exprs[i]);
                    lemma_expr_children_frame_push_expr(
                        old_prog.exprs,
                        old_prog.stmts,
                        g_node,
                        old_prog.exprs[i].kind,
                        old_prog.exprs[i].rank as nat,
                    );
                    lemma_expr_grammar_frame_push_expr(
                        old_prog.exprs,
                        g_node,
                        old_prog.exprs[i].kind,
                    );
                } else {
                    assert(new_exprs[i] == g_node);
                    lemma_expr_grammar_frame_push_expr(
                        old_prog.exprs,
                        g_node,
                        g_node.kind,
                    );
                }
            }
            assert forall|j: int| 0 <= j < self.stmts@.len() implies (
                ((#[trigger] self.stmts@[j]).rank as nat) < new_exprs.len() + self.stmts@.len()
                    && stmt_children_bounded(
                        new_exprs,
                        self.stmts@,
                        self.stmts@[j].kind,
                        self.stmts@[j].rank as nat,
                    )
                    && stmt_grammar_local_wf(self.stmts@[j].kind)
            ) by {
                assert(self.stmts@[j] == old_prog.stmts[j]);
                lemma_stmt_children_frame_push_expr(
                    old_prog.exprs,
                    old_prog.stmts,
                    g_node,
                    old_prog.stmts[j].kind,
                    old_prog.stmts[j].rank as nat,
                );
            }
            assert forall|k: int| 0 <= k < self.body@.len() implies (#[trigger] self.body@[k]).0 < self.stmts@.len() by {
                assert(self.body@[k] == old_prog.body[k]);
            }
        }
        Ok(ExprId(elen))
    }

    /// Allocate a new bottom-up `Stmt` node, preserving `wf` and `grammar_wf` by construction.
    pub fn alloc_stmt(
        &mut self,
        kind: StmtKind,
        span: Span,
    ) -> (res: Result<StmtId, SyntaxDiagnostic>)
        requires
            old(self).grammar_wf(),
            stmt_refs_in_bounds(old(self).exprs@.len(), old(self).stmts@.len(), kind),
            stmt_grammar_local_wf(kind),
        ensures
            final(self).grammar_wf(),
            old(self).exprs@ == final(self).exprs@,
            old(self).stmts@.len() <= final(self).stmts@.len(),
            old(self).body@ == final(self).body@,
            forall|j: int| 0 <= j < old(self).stmts@.len() ==> #[trigger] final(self).stmts@[j] == old(self).stmts@[j],
            match res {
                Ok(id) => {
                    id.0 == old(self).stmts@.len()
                        && final(self).stmts@.len() == old(self).stmts@.len() + 1
                        && final(self).stmts@[id.0 as int].kind == kind
                        && final(self).stmts@[id.0 as int].span == span
                },
                Err(_) => final(self)@ == old(self)@,
            },
    {
        let elen = self.exprs.len();
        let slen = self.stmts.len();
        if slen >= usize::MAX - elen {
            return Err(SyntaxDiagnostic {
                kind: DiagnosticKind::AstArenaOverflow,
                span,
            });
        }
        let rank = elen + slen;
        let ghost old_prog = self@;
        let node = Stmt { kind, span, rank };
        let ghost g_node = node;
        proof {
            lemma_refs_to_bounded_stmt(old_prog, g_node.kind);
            lemma_stmt_children_frame_push_stmt(
                old_prog.exprs,
                old_prog.stmts,
                g_node,
                g_node.kind,
                rank as nat,
            );
        }
        self.stmts.push(node);
        proof {
            let new_stmts = self.stmts@;
            assert forall|i: int| 0 <= i < self.exprs@.len() implies (
                ((#[trigger] self.exprs@[i]).rank as nat) < self.exprs@.len() + new_stmts.len()
                    && expr_children_bounded(
                        self.exprs@,
                        new_stmts,
                        self.exprs@[i].kind,
                        self.exprs@[i].rank as nat,
                    )
                    && expr_grammar_local_wf(self.exprs@, self.exprs@[i].kind)
            ) by {
                assert(self.exprs@[i] == old_prog.exprs[i]);
                lemma_expr_children_frame_push_stmt(
                    old_prog.exprs,
                    old_prog.stmts,
                    g_node,
                    old_prog.exprs[i].kind,
                    old_prog.exprs[i].rank as nat,
                );
            }
            assert forall|j: int| 0 <= j < new_stmts.len() implies (
                ((#[trigger] new_stmts[j]).rank as nat) < self.exprs@.len() + new_stmts.len()
                    && stmt_children_bounded(
                        self.exprs@,
                        new_stmts,
                        new_stmts[j].kind,
                        new_stmts[j].rank as nat,
                    )
                    && stmt_grammar_local_wf(new_stmts[j].kind)
            ) by {
                if j < old_prog.stmts.len() {
                    assert(new_stmts[j] == old_prog.stmts[j]);
                    lemma_stmt_children_frame_push_stmt(
                        old_prog.exprs,
                        old_prog.stmts,
                        g_node,
                        old_prog.stmts[j].kind,
                        old_prog.stmts[j].rank as nat,
                    );
                    assert(stmt_grammar_local_wf(old_prog.stmts[j].kind));
                } else {
                    assert(new_stmts[j] == g_node);
                }
            }
            assert forall|k: int| 0 <= k < self.body@.len() implies (#[trigger] self.body@[k]).0 < new_stmts.len() by {
                assert(self.body@[k] == old_prog.body[k]);
                assert(old_prog.body[k].0 < old_prog.stmts.len());
            }
        }
        Ok(StmtId(slen))
    }
}

pub fn count_default_cases(cases: &[SwitchCase]) -> (cnt: usize)
    ensures
        cnt as nat == spec_count_default_cases(cases@),
{
    let n = cases.len();
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    proof {
        assert(cases@.subrange(0, 0) =~= Seq::<SwitchCase>::empty());
    }
    while i < n
        invariant
            i <= n && cnt <= i,
            n == cases@.len(),
            cnt as nat == spec_count_default_cases(cases@.subrange(0, i as int)),
        decreases n - i,
    {
        proof {
            assert(cases@.subrange(0, (i + 1) as int).drop_last() =~= cases@.subrange(0, i as int));
        }
        if cases[i].test.is_none() {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    proof {
        assert(cases@.subrange(0, n as int) =~= cases@);
    }
    cnt
}

} // verus!
