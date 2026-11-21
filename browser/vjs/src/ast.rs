//! Arena-indexed ECMAScript Abstract Syntax Tree (`Program`, `StmtNode`, `ExprNode`, `FuncDef`),
//! structural well-formedness (`spec_prog_wf`), and explicit `UnsupportedFeature` taxonomy
//! (`docs/verified-browser-engine.md` §3.3).
use crate::value::{JsNum, JsStr};
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ExprId(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct StmtId(pub usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct FuncId(pub usize);

/// Explicit refusal taxonomy when a script uses a language feature outside J4's verified subset.
/// Per `docs/verified-browser-engine.md` §3.3, unsupported features are always reported explicitly,
/// never silently approximated.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum UnsupportedFeature {
    WithStatement,
    EvalDirectCall,
    GeneratorFunction,
    AsyncFunction,
    AwaitExpression,
    YieldExpression,
    ClassSyntax,
    ModuleSyntax,
    RegExpLiteral,
    BigIntLiteral,
    TaggedTemplate,
    SuperKeyword,
    DestructuringPattern,
    ForAwaitOf,
    NonIntegerExponentiation,
    SymbolPrimitive,
    InvalidAstReference,
    ParserDepthLimit,
}

impl View for UnsupportedFeature {
    type V = UnsupportedFeature;

    open spec fn view(&self) -> UnsupportedFeature {
        *self
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOp {
    Void,
    Typeof,
    LogicalNot,
    BitNot,
    Plus,
    Minus,
    Delete,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Exp,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Ushr,
    Lt,
    Le,
    Gt,
    Ge,
    EqLoose,
    NeLoose,
    EqStrict,
    NeStrict,
    In,
    Instanceof,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LogicalOp {
    And,
    Or,
    Nullish,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
    UshrAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    AndAssign,
    OrAssign,
    NullishAssign,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UpdateOp {
    Inc,
    Dec,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum VarKind {
    Var,
    Let,
    Const,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PropKeyInit {
    Static(JsStr),
    Computed(ExprId),
}

pub enum SpecPropKeyInit {
    Static(Seq<u16>),
    Computed(ExprId),
}

impl View for PropKeyInit {
    type V = SpecPropKeyInit;

    open spec fn view(&self) -> SpecPropKeyInit {
        match self {
            PropKeyInit::Static(s) => SpecPropKeyInit::Static(s@),
            PropKeyInit::Computed(e) => SpecPropKeyInit::Computed(*e),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropInit {
    pub key: PropKeyInit,
    pub val: ExprId,
}

pub struct SpecPropInit {
    pub key: SpecPropKeyInit,
    pub val: ExprId,
}

impl View for PropInit {
    type V = SpecPropInit;

    open spec fn view(&self) -> SpecPropInit {
        SpecPropInit { key: self.key@, val: self.val }
    }
}

/// Suffix step inside an ECMA-262 §13.3.9 `OptionalExpression` (`?.` chain).
#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ChainStep {
    Member { prop: ExprId, optional: bool },
    Call { args: Vec<ExprId>, optional: bool },
}

#[allow(inconsistent_fields)]
pub enum SpecChainStep {
    Member { prop: ExprId, optional: bool },
    Call { args: Seq<ExprId>, optional: bool },
}

impl View for ChainStep {
    type V = SpecChainStep;

    open spec fn view(&self) -> SpecChainStep {
        match self {
            ChainStep::Member { prop, optional } => SpecChainStep::Member { prop: *prop, optional: *optional },
            ChainStep::Call { args, optional } => SpecChainStep::Call { args: args@, optional: *optional },
        }
    }
}

pub open spec fn spec_chain_steps_view(steps: Seq<ChainStep>) -> Seq<SpecChainStep> {
    Seq::new(steps.len(), |i: int| steps[i]@)
}

#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprNode {
    LitUndefined,
    LitNull,
    LitBool(bool),
    LitNum(JsNum),
    LitStr(JsStr),
    This,
    Ident(JsStr),
    Unary { op: UnaryOp, arg: ExprId },
    TypeofIdent(JsStr),
    DeleteMember { obj: ExprId, prop: ExprId },
    DeleteIdent(JsStr),
    Binary { op: BinOp, lhs: ExprId, rhs: ExprId },
    Logical { op: LogicalOp, lhs: ExprId, rhs: ExprId },
    Conditional { cond: ExprId, then_expr: ExprId, else_expr: ExprId },
    Sequence { exprs: Vec<ExprId> },
    AssignIdent { op: AssignOp, name: JsStr, rhs: ExprId },
    AssignMember { op: AssignOp, obj: ExprId, prop: ExprId, rhs: ExprId },
    UpdateIdent { op: UpdateOp, prefix: bool, name: JsStr },
    UpdateMember { op: UpdateOp, prefix: bool, obj: ExprId, prop: ExprId },
    Member { obj: ExprId, prop: ExprId, optional: bool },
    Call { callee: ExprId, optional: bool, args: Vec<ExprId> },
    CallMethod { obj: ExprId, prop: ExprId, optional: bool, optional_call: bool, args: Vec<ExprId> },
    OptChain { head: ExprId, steps: Vec<ChainStep>, is_delete: bool },
    New { callee: ExprId, args: Vec<ExprId> },
    ArrayLit { elements: Vec<Option<ExprId>> },
    ObjectLit { props: Vec<PropInit> },
    FuncExpr { func: FuncId },
    UnsupportedExpr(UnsupportedFeature),
}

#[allow(inconsistent_fields)]
pub enum SpecExprNode {
    LitUndefined,
    LitNull,
    LitBool(bool),
    LitNum(JsNum),
    LitStr(Seq<u16>),
    This,
    Ident(Seq<u16>),
    Unary { op: UnaryOp, arg: ExprId },
    TypeofIdent(Seq<u16>),
    DeleteMember { obj: ExprId, prop: ExprId },
    DeleteIdent(Seq<u16>),
    Binary { op: BinOp, lhs: ExprId, rhs: ExprId },
    Logical { op: LogicalOp, lhs: ExprId, rhs: ExprId },
    Conditional { cond: ExprId, then_expr: ExprId, else_expr: ExprId },
    Sequence { exprs: Seq<ExprId> },
    AssignIdent { op: AssignOp, name: Seq<u16>, rhs: ExprId },
    AssignMember { op: AssignOp, obj: ExprId, prop: ExprId, rhs: ExprId },
    UpdateIdent { op: UpdateOp, prefix: bool, name: Seq<u16> },
    UpdateMember { op: UpdateOp, prefix: bool, obj: ExprId, prop: ExprId },
    Member { obj: ExprId, prop: ExprId, optional: bool },
    Call { callee: ExprId, optional: bool, args: Seq<ExprId> },
    CallMethod { obj: ExprId, prop: ExprId, optional: bool, optional_call: bool, args: Seq<ExprId> },
    OptChain { head: ExprId, steps: Seq<SpecChainStep>, is_delete: bool },
    New { callee: ExprId, args: Seq<ExprId> },
    ArrayLit { elements: Seq<Option<ExprId>> },
    ObjectLit { props: Seq<SpecPropInit> },
    FuncExpr { func: FuncId },
    UnsupportedExpr(UnsupportedFeature),
}

pub open spec fn spec_prop_inits_view(props: Seq<PropInit>) -> Seq<SpecPropInit> {
    Seq::new(props.len(), |i: int| props[i]@)
}

impl View for ExprNode {
    type V = SpecExprNode;

    open spec fn view(&self) -> SpecExprNode {
        match self {
            ExprNode::LitUndefined => SpecExprNode::LitUndefined,
            ExprNode::LitNull => SpecExprNode::LitNull,
            ExprNode::LitBool(b) => SpecExprNode::LitBool(*b),
            ExprNode::LitNum(n) => SpecExprNode::LitNum(*n),
            ExprNode::LitStr(s) => SpecExprNode::LitStr(s@),
            ExprNode::This => SpecExprNode::This,
            ExprNode::Ident(s) => SpecExprNode::Ident(s@),
            ExprNode::Unary { op, arg } => SpecExprNode::Unary { op: *op, arg: *arg },
            ExprNode::TypeofIdent(s) => SpecExprNode::TypeofIdent(s@),
            ExprNode::DeleteMember { obj, prop } => SpecExprNode::DeleteMember { obj: *obj, prop: *prop },
            ExprNode::DeleteIdent(s) => SpecExprNode::DeleteIdent(s@),
            ExprNode::Binary { op, lhs, rhs } => SpecExprNode::Binary { op: *op, lhs: *lhs, rhs: *rhs },
            ExprNode::Logical { op, lhs, rhs } => SpecExprNode::Logical { op: *op, lhs: *lhs, rhs: *rhs },
            ExprNode::Conditional { cond, then_expr, else_expr } =>
                SpecExprNode::Conditional { cond: *cond, then_expr: *then_expr, else_expr: *else_expr },
            ExprNode::Sequence { exprs } => SpecExprNode::Sequence { exprs: exprs@ },
            ExprNode::AssignIdent { op, name, rhs } =>
                SpecExprNode::AssignIdent { op: *op, name: name@, rhs: *rhs },
            ExprNode::AssignMember { op, obj, prop, rhs } =>
                SpecExprNode::AssignMember { op: *op, obj: *obj, prop: *prop, rhs: *rhs },
            ExprNode::UpdateIdent { op, prefix, name } =>
                SpecExprNode::UpdateIdent { op: *op, prefix: *prefix, name: name@ },
            ExprNode::UpdateMember { op, prefix, obj, prop } =>
                SpecExprNode::UpdateMember { op: *op, prefix: *prefix, obj: *obj, prop: *prop },
            ExprNode::Member { obj, prop, optional } =>
                SpecExprNode::Member { obj: *obj, prop: *prop, optional: *optional },
            ExprNode::Call { callee, optional, args } =>
                SpecExprNode::Call { callee: *callee, optional: *optional, args: args@ },
            ExprNode::CallMethod { obj, prop, optional, optional_call, args } =>
                SpecExprNode::CallMethod {
                    obj: *obj,
                    prop: *prop,
                    optional: *optional,
                    optional_call: *optional_call,
                    args: args@,
                },
            ExprNode::OptChain { head, steps, is_delete } =>
                SpecExprNode::OptChain {
                    head: *head,
                    steps: spec_chain_steps_view(steps@),
                    is_delete: *is_delete,
                },
            ExprNode::New { callee, args } =>
                SpecExprNode::New { callee: *callee, args: args@ },
            ExprNode::ArrayLit { elements } =>
                SpecExprNode::ArrayLit { elements: elements@ },
            ExprNode::ObjectLit { props } =>
                SpecExprNode::ObjectLit { props: spec_prop_inits_view(props@) },
            ExprNode::FuncExpr { func } => SpecExprNode::FuncExpr { func: *func },
            ExprNode::UnsupportedExpr(f) => SpecExprNode::UnsupportedExpr(*f),
        }
    }
}

/// Left-hand side target of `for-in` / `for-of` (§14.7.5).
#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ForEachLhs {
    Decl { kind: VarKind, name: JsStr },
    Ident(JsStr),
    Member { obj: ExprId, prop: ExprId },
}

#[allow(inconsistent_fields)]
pub enum SpecForEachLhs {
    Decl { kind: VarKind, name: Seq<u16> },
    Ident(Seq<u16>),
    Member { obj: ExprId, prop: ExprId },
}

impl View for ForEachLhs {
    type V = SpecForEachLhs;

    open spec fn view(&self) -> SpecForEachLhs {
        match self {
            ForEachLhs::Decl { kind, name } => SpecForEachLhs::Decl { kind: *kind, name: name@ },
            ForEachLhs::Ident(name) => SpecForEachLhs::Ident(name@),
            ForEachLhs::Member { obj, prop } => SpecForEachLhs::Member { obj: *obj, prop: *prop },
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VarDeclarator {
    pub name: JsStr,
    pub init: Option<ExprId>,
}

pub struct SpecVarDeclarator {
    pub name: Seq<u16>,
    pub init: Option<ExprId>,
}

impl View for VarDeclarator {
    type V = SpecVarDeclarator;

    open spec fn view(&self) -> SpecVarDeclarator {
        SpecVarDeclarator { name: self.name@, init: self.init }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SwitchCase {
    pub test: Option<ExprId>,
    pub consequent: Vec<StmtId>,
}

pub struct SpecSwitchCase {
    pub test: Option<ExprId>,
    pub consequent: Seq<StmtId>,
}

impl View for SwitchCase {
    type V = SpecSwitchCase;

    open spec fn view(&self) -> SpecSwitchCase {
        SpecSwitchCase { test: self.test, consequent: self.consequent@ }
    }
}

#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StmtNode {
    Empty,
    ExprStmt(ExprId),
    Block { stmts: Vec<StmtId> },
    VarDecl { kind: VarKind, decls: Vec<VarDeclarator> },
    FuncDecl { func: FuncId },
    If { cond: ExprId, then_branch: StmtId, else_branch: Option<StmtId> },
    While { labels: Vec<JsStr>, cond: ExprId, body: StmtId },
    DoWhile { labels: Vec<JsStr>, body: StmtId, cond: ExprId },
    For {
        labels: Vec<JsStr>,
        init: Option<StmtId>,
        per_iter_lets: Vec<JsStr>,
        cond: Option<ExprId>,
        update: Option<ExprId>,
        body: StmtId,
    },
    ForIn {
        labels: Vec<JsStr>,
        lhs: ForEachLhs,
        object: ExprId,
        body: StmtId,
    },
    ForOf {
        labels: Vec<JsStr>,
        lhs: ForEachLhs,
        iterable: ExprId,
        body: StmtId,
    },
    Switch {
        label: Option<JsStr>,
        discriminant: ExprId,
        cases: Vec<SwitchCase>,
    },
    Return(Option<ExprId>),
    Break(Option<JsStr>),
    Continue(Option<JsStr>),
    Throw(ExprId),
    Try {
        block: StmtId,
        catch_param: Option<JsStr>,
        catch_body: Option<StmtId>,
        finally_body: Option<StmtId>,
    },
    Labeled { label: JsStr, body: StmtId },
    UnsupportedStmt(UnsupportedFeature),
}

pub open spec fn spec_opt_str_view(o: &Option<JsStr>) -> Option<Seq<u16>> {
    match o {
        None => None,
        Some(s) => Some(s@),
    }
}

pub open spec fn spec_str_seq_view(v: Seq<JsStr>) -> Seq<Seq<u16>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

pub open spec fn spec_var_decls_view(v: Seq<VarDeclarator>) -> Seq<SpecVarDeclarator> {
    Seq::new(v.len(), |i: int| v[i]@)
}

pub open spec fn spec_switch_cases_view(v: Seq<SwitchCase>) -> Seq<SpecSwitchCase> {
    Seq::new(v.len(), |i: int| v[i]@)
}

#[allow(inconsistent_fields)]
pub enum SpecStmtNode {
    Empty,
    ExprStmt(ExprId),
    Block { stmts: Seq<StmtId> },
    VarDecl { kind: VarKind, decls: Seq<SpecVarDeclarator> },
    FuncDecl { func: FuncId },
    If { cond: ExprId, then_branch: StmtId, else_branch: Option<StmtId> },
    While { labels: Seq<Seq<u16>>, cond: ExprId, body: StmtId },
    DoWhile { labels: Seq<Seq<u16>>, body: StmtId, cond: ExprId },
    For {
        labels: Seq<Seq<u16>>,
        init: Option<StmtId>,
        per_iter_lets: Seq<Seq<u16>>,
        cond: Option<ExprId>,
        update: Option<ExprId>,
        body: StmtId,
    },
    ForIn {
        labels: Seq<Seq<u16>>,
        lhs: SpecForEachLhs,
        object: ExprId,
        body: StmtId,
    },
    ForOf {
        labels: Seq<Seq<u16>>,
        lhs: SpecForEachLhs,
        iterable: ExprId,
        body: StmtId,
    },
    Switch {
        label: Option<Seq<u16>>,
        discriminant: ExprId,
        cases: Seq<SpecSwitchCase>,
    },
    Return(Option<ExprId>),
    Break(Option<Seq<u16>>),
    Continue(Option<Seq<u16>>),
    Throw(ExprId),
    Try {
        block: StmtId,
        catch_param: Option<Seq<u16>>,
        catch_body: Option<StmtId>,
        finally_body: Option<StmtId>,
    },
    Labeled { label: Seq<u16>, body: StmtId },
    UnsupportedStmt(UnsupportedFeature),
}

impl View for StmtNode {
    type V = SpecStmtNode;

    open spec fn view(&self) -> SpecStmtNode {
        match self {
            StmtNode::Empty => SpecStmtNode::Empty,
            StmtNode::ExprStmt(e) => SpecStmtNode::ExprStmt(*e),
            StmtNode::Block { stmts } => SpecStmtNode::Block { stmts: stmts@ },
            StmtNode::VarDecl { kind, decls } =>
                SpecStmtNode::VarDecl { kind: *kind, decls: spec_var_decls_view(decls@) },
            StmtNode::FuncDecl { func } => SpecStmtNode::FuncDecl { func: *func },
            StmtNode::If { cond, then_branch, else_branch } =>
                SpecStmtNode::If { cond: *cond, then_branch: *then_branch, else_branch: *else_branch },
            StmtNode::While { labels, cond, body } =>
                SpecStmtNode::While { labels: spec_str_seq_view(labels@), cond: *cond, body: *body },
            StmtNode::DoWhile { labels, body, cond } =>
                SpecStmtNode::DoWhile { labels: spec_str_seq_view(labels@), body: *body, cond: *cond },
            StmtNode::For { labels, init, per_iter_lets, cond, update, body } =>
                SpecStmtNode::For {
                    labels: spec_str_seq_view(labels@),
                    init: *init,
                    per_iter_lets: spec_str_seq_view(per_iter_lets@),
                    cond: *cond,
                    update: *update,
                    body: *body,
                },
            StmtNode::ForIn { labels, lhs, object, body } =>
                SpecStmtNode::ForIn {
                    labels: spec_str_seq_view(labels@),
                    lhs: lhs@,
                    object: *object,
                    body: *body,
                },
            StmtNode::ForOf { labels, lhs, iterable, body } =>
                SpecStmtNode::ForOf {
                    labels: spec_str_seq_view(labels@),
                    lhs: lhs@,
                    iterable: *iterable,
                    body: *body,
                },
            StmtNode::Switch { label, discriminant, cases } =>
                SpecStmtNode::Switch {
                    label: spec_opt_str_view(label),
                    discriminant: *discriminant,
                    cases: spec_switch_cases_view(cases@),
                },
            StmtNode::Return(e) => SpecStmtNode::Return(*e),
            StmtNode::Break(l) => SpecStmtNode::Break(spec_opt_str_view(l)),
            StmtNode::Continue(l) => SpecStmtNode::Continue(spec_opt_str_view(l)),
            StmtNode::Throw(e) => SpecStmtNode::Throw(*e),
            StmtNode::Try { block, catch_param, catch_body, finally_body } =>
                SpecStmtNode::Try {
                    block: *block,
                    catch_param: spec_opt_str_view(catch_param),
                    catch_body: *catch_body,
                    finally_body: *finally_body,
                },
            StmtNode::Labeled { label, body } =>
                SpecStmtNode::Labeled { label: label@, body: *body },
            StmtNode::UnsupportedStmt(f) => SpecStmtNode::UnsupportedStmt(*f),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FuncDef {
    pub name: Option<JsStr>,
    pub params: Vec<JsStr>,
    pub body: Vec<StmtId>,
    pub strict: bool,
    pub is_arrow: bool,
    pub hoisted_vars: Vec<JsStr>,
}

pub struct SpecFuncDef {
    pub name: Option<Seq<u16>>,
    pub params: Seq<Seq<u16>>,
    pub body: Seq<StmtId>,
    pub strict: bool,
    pub is_arrow: bool,
    pub hoisted_vars: Seq<Seq<u16>>,
}

impl View for FuncDef {
    type V = SpecFuncDef;

    open spec fn view(&self) -> SpecFuncDef {
        SpecFuncDef {
            name: spec_opt_str_view(&self.name),
            params: spec_str_seq_view(self.params@),
            body: self.body@,
            strict: self.strict,
            is_arrow: self.is_arrow,
            hoisted_vars: spec_str_seq_view(self.hoisted_vars@),
        }
    }
}

/// Top-level ECMAScript Script program AST.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Program {
    pub strict: bool,
    pub exprs: Vec<ExprNode>,
    pub stmts: Vec<StmtNode>,
    pub funcs: Vec<FuncDef>,
    pub hoisted_vars: Vec<JsStr>,
    pub body: Vec<StmtId>,
}

pub open spec fn spec_exprs_view(v: Seq<ExprNode>) -> Seq<SpecExprNode> {
    Seq::new(v.len(), |i: int| v[i]@)
}

pub open spec fn spec_stmts_view(v: Seq<StmtNode>) -> Seq<SpecStmtNode> {
    Seq::new(v.len(), |i: int| v[i]@)
}

pub open spec fn spec_funcs_view(v: Seq<FuncDef>) -> Seq<SpecFuncDef> {
    Seq::new(v.len(), |i: int| v[i]@)
}

pub struct SpecProgram {
    pub strict: bool,
    pub exprs: Seq<SpecExprNode>,
    pub stmts: Seq<SpecStmtNode>,
    pub funcs: Seq<SpecFuncDef>,
    pub hoisted_vars: Seq<Seq<u16>>,
    pub body: Seq<StmtId>,
}

impl View for Program {
    type V = SpecProgram;

    open spec fn view(&self) -> SpecProgram {
        SpecProgram {
            strict: self.strict,
            exprs: spec_exprs_view(self.exprs@),
            stmts: spec_stmts_view(self.stmts@),
            funcs: spec_funcs_view(self.funcs@),
            hoisted_vars: spec_str_seq_view(self.hoisted_vars@),
            body: self.body@,
        }
    }
}

/// Arena well-formedness of a parsed `SpecProgram`: all top-level and function body `StmtId`s
/// point to valid entries in `stmts`.
pub open spec fn spec_stmt_ids_in_bounds(ids: Seq<StmtId>, n_stmts: nat) -> bool {
    forall|k: int| 0 <= k < ids.len() ==> ((#[trigger] ids[k]).0 as nat) < n_stmts
}

pub open spec fn spec_prog_wf(p: SpecProgram) -> bool {
    spec_stmt_ids_in_bounds(p.body, p.stmts.len())
    && (forall|f: int| 0 <= f < p.funcs.len() ==>
        spec_stmt_ids_in_bounds((#[trigger] p.funcs[f]).body, p.stmts.len()))
}

fn check_stmt_ids_in_bounds(ids: &Vec<StmtId>, n_stmts: usize) -> (ok: bool)
    ensures ok == spec_stmt_ids_in_bounds(ids@, n_stmts as nat),
{
    let n = ids.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == ids@.len(),
            forall|k: int| 0 <= k < i as int ==> ((#[trigger] ids@[k]).0 as nat) < (n_stmts as nat),
        decreases n - i,
    {
        if ids[i].0 >= n_stmts {
            return false;
        }
        i += 1;
    }
    true
}

impl Program {
    pub fn check_wf(&self) -> (ok: bool)
        ensures ok == spec_prog_wf(self@),
    {
        let ns = self.stmts.len();
        if !check_stmt_ids_in_bounds(&self.body, ns) {
            return false;
        }
        let nf = self.funcs.len();
        let mut f: usize = 0;
        let ghost sfuncs = self@.funcs;
        while f < nf
            invariant
                f <= nf == self.funcs@.len(),
                ns == self@.stmts.len(),
                sfuncs == self@.funcs,
                spec_stmt_ids_in_bounds(self@.body, ns as nat),
                forall|k: int| 0 <= k < f as int ==>
                    spec_stmt_ids_in_bounds((#[trigger] sfuncs[k]).body, ns as nat),
            decreases nf - f,
        {
            proof { assert(sfuncs[f as int] == self.funcs@[f as int]@); }
            if !check_stmt_ids_in_bounds(&self.funcs[f].body, ns) {
                return false;
            }
            f += 1;
        }
        true
    }

    pub fn new(strict: bool) -> (p: Self)
        ensures
            p@.strict == strict,
            p@.exprs.len() == 0,
            p@.stmts.len() == 0,
            p@.funcs.len() == 0,
            p@.hoisted_vars.len() == 0,
            p@.body.len() == 0,
    {
        let p = Program {
            strict,
            exprs: Vec::new(),
            stmts: Vec::new(),
            funcs: Vec::new(),
            hoisted_vars: Vec::new(),
            body: Vec::new(),
        };
        proof {
            assert(p@.exprs =~= Seq::<SpecExprNode>::empty());
            assert(p@.stmts =~= Seq::<SpecStmtNode>::empty());
            assert(p@.funcs =~= Seq::<SpecFuncDef>::empty());
            assert(p@.hoisted_vars =~= Seq::<Seq<u16>>::empty());
        }
        p
    }

    pub fn push_expr(&mut self, node: ExprNode) -> (id: ExprId)
        ensures
            id.0 == old(self)@.exprs.len(),
            final(self)@.exprs.len() == old(self)@.exprs.len() + 1,
            final(self)@.exprs[id.0 as int] == node@,
            final(self)@.stmts == old(self)@.stmts,
            final(self)@.funcs == old(self)@.funcs,
    {
        let idx = self.exprs.len();
        self.exprs.push(node);
        proof {
            assert(self@.stmts =~= old(self)@.stmts);
            assert(self@.funcs =~= old(self)@.funcs);
        }
        ExprId(idx)
    }

    pub fn push_stmt(&mut self, node: StmtNode) -> (id: StmtId)
        ensures
            id.0 == old(self)@.stmts.len(),
            final(self)@.stmts.len() == old(self)@.stmts.len() + 1,
            final(self)@.stmts[id.0 as int] == node@,
            final(self)@.exprs == old(self)@.exprs,
            final(self)@.funcs == old(self)@.funcs,
    {
        let idx = self.stmts.len();
        self.stmts.push(node);
        proof {
            assert(self@.exprs =~= old(self)@.exprs);
            assert(self@.funcs =~= old(self)@.funcs);
        }
        StmtId(idx)
    }

    pub fn push_func(&mut self, func: FuncDef) -> (id: FuncId)
        ensures
            id.0 == old(self)@.funcs.len(),
            final(self)@.funcs.len() == old(self)@.funcs.len() + 1,
            final(self)@.funcs[id.0 as int] == func@,
            final(self)@.exprs == old(self)@.exprs,
            final(self)@.stmts == old(self)@.stmts,
    {
        let idx = self.funcs.len();
        self.funcs.push(func);
        proof {
            assert(self@.exprs =~= old(self)@.exprs);
            assert(self@.stmts =~= old(self)@.stmts);
        }
        FuncId(idx)
    }
}

} // verus!
