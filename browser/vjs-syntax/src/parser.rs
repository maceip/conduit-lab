//! ECMA-262 §13–16 Verified Recursive-Descent + Pratt AST Parser.
//!
//! Proves in Verus:
//! 1. Total termination (`decreases`) and panic-freedom over arbitrary token streams ending in `Eof`.
//! 2. Monotonic token-consumption progress (`old(p).pos < final(p).pos` on every `Ok` expression and statement),
//!    and full-stream consumption up to `TokenKind::Eof` at top level (never silently dropping tokens).
//! 3. Preservation of arena structural acyclicity (`Program::wf`) and all 8 syntactic grammar
//!    well-formedness invariants (`Program::grammar_wf`).
use crate::ast::*;
use crate::early_errors::check_early_errors;
use crate::token::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Step Result & Small Verified Cloning Helpers
// ---------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParseStep<T> {
    Ok(T),
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

fn clone_u8_slice(b: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == b@,
{
    let n = b.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == b@.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> out@[k] == b@[k],
        decreases n - i,
    {
        out.push(b[i]);
        i = i + 1;
    }
    proof {
        assert(out@ =~= b@);
    }
    out
}

fn clone_u16_slice(u: &[u16]) -> (v: Vec<u16>)
    ensures
        v@ == u@,
{
    let n = u.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == u@.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> out@[k] == u@[k],
        decreases n - i,
    {
        out.push(u[i]);
        i = i + 1;
    }
    proof {
        assert(out@ =~= u@);
    }
    out
}

fn eq_ascii_3(b: &[u8], c0: u8, c1: u8, c2: u8) -> (r: bool)
    ensures
        r == (b@.len() == 3 && b@[0] == c0 && b@[1] == c1 && b@[2] == c2),
{
    b.len() == 3 && b[0] == c0 && b[1] == c1 && b[2] == c2
}

fn eq_ascii_6(b: &[u8], c0: u8, c1: u8, c2: u8, c3: u8, c4: u8, c5: u8) -> (r: bool)
    ensures
        r == (b@.len() == 6
            && b@[0] == c0
            && b@[1] == c1
            && b@[2] == c2
            && b@[3] == c3
            && b@[4] == c4
            && b@[5] == c5),
{
    b.len() == 6
        && b[0] == c0
        && b[1] == c1
        && b[2] == c2
        && b[3] == c3
        && b[4] == c4
        && b[5] == c5
}

// ---------------------------------------------------------------------------------------
// Opaque Arena Invariants & Transitive Monotonicity Framing
// ---------------------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn prog_grammar_wf(p: SpecProgram) -> bool {
    p.grammar_wf()
}

#[verifier::opaque]
pub open spec fn arena_prefix_preserved(old_p: SpecProgram, new_p: SpecProgram) -> bool {
    old_p.exprs.len() <= new_p.exprs.len()
        && old_p.stmts.len() <= new_p.stmts.len()
        && (forall|i: int| 0 <= i < old_p.exprs.len() ==> #[trigger] new_p.exprs[i] == old_p.exprs[i])
        && (forall|j: int| 0 <= j < old_p.stmts.len() ==> #[trigger] new_p.stmts[j] == old_p.stmts[j])
}

pub open spec fn arena_grew(old_p: SpecProgram, new_p: SpecProgram) -> bool {
    old_p.exprs.len() <= new_p.exprs.len()
        && old_p.stmts.len() <= new_p.stmts.len()
        && arena_prefix_preserved(old_p, new_p)
}

pub proof fn lemma_arena_refl(p: SpecProgram)
    ensures
        arena_grew(p, p),
{
    reveal(arena_prefix_preserved);
}

pub proof fn lemma_arena_trans(p0: SpecProgram, p1: SpecProgram, p2: SpecProgram)
    requires
        arena_grew(p0, p1),
        arena_grew(p1, p2),
    ensures
        arena_grew(p0, p2),
{
    reveal(arena_prefix_preserved);
    assert forall|i: int| 0 <= i < p0.exprs.len() implies #[trigger] p2.exprs[i] == p0.exprs[i] by {
        assert(p1.exprs[i] == p0.exprs[i]);
        assert(p2.exprs[i] == p1.exprs[i]);
    }
    assert forall|j: int| 0 <= j < p0.stmts.len() implies #[trigger] p2.stmts[j] == p0.stmts[j] by {
        assert(p1.stmts[j] == p0.stmts[j]);
        assert(p2.stmts[j] == p1.stmts[j]);
    }
}

pub proof fn lemma_arena_expr_preserved(p0: SpecProgram, p1: SpecProgram, id: ExprId)
    requires
        arena_grew(p0, p1),
        id.0 < p0.exprs.len(),
    ensures
        id.0 < p1.exprs.len(),
        p1.exprs[id.0 as int] == p0.exprs[id.0 as int],
{
    reveal(arena_prefix_preserved);
}

pub proof fn lemma_arena_stmt_preserved(p0: SpecProgram, p1: SpecProgram, id: StmtId)
    requires
        arena_grew(p0, p1),
        id.0 < p0.stmts.len(),
    ensures
        id.0 < p1.stmts.len(),
        p1.stmts[id.0 as int] == p0.stmts[id.0 as int],
{
    reveal(arena_prefix_preserved);
}

// ---------------------------------------------------------------------------------------
// Parser State & Token Stream Invariants
// ---------------------------------------------------------------------------------------

pub open spec fn spec_tokens_wf(tokens: Seq<Token>) -> bool {
    tokens.len() >= 1 && (tokens.last().kind is Eof)
}

pub struct Parser<'a> {
    pub tokens: &'a [Token],
    pub pos: usize,
    pub prog: Program,
    pub strict: bool,
    pub in_async: bool,
    pub in_generator: bool,
}

pub open spec fn parser_step_post<'a>(old_p: Parser<'a>, new_p: Parser<'a>) -> bool {
    new_p.wf()
        && new_p.tokens@ == old_p.tokens@
        && old_p.pos <= new_p.pos
        && arena_grew(old_p.prog@, new_p.prog@)
}

impl<'a> Parser<'a> {
    pub open spec fn wf(&self) -> bool {
        self.pos < self.tokens@.len()
            && spec_tokens_wf(self.tokens@)
            && prog_grammar_wf(self.prog@)
    }

    pub fn new(tokens: &'a [Token]) -> (p: Parser<'a>)
        requires
            spec_tokens_wf(tokens@),
        ensures
            p.wf(),
            p.tokens@ == tokens@,
            p.pos == 0,
            p.prog.exprs@.len() == 0,
            p.prog.stmts@.len() == 0,
            p.prog.body@.len() == 0,
    {
        let prog = Program::new();
        proof {
            reveal(prog_grammar_wf);
        }
        Parser {
            tokens,
            pos: 0,
            prog,
            strict: false,
            in_async: false,
            in_generator: false,
        }
    }

    pub fn cur(&self) -> (t: &'a Token)
        requires
            self.wf(),
        ensures
            *t == self.tokens@[self.pos as int],
    {
        &self.tokens[self.pos]
    }

    pub fn cur_span(&self) -> (sp: Span)
        requires
            self.wf(),
        ensures
            sp == self.tokens@[self.pos as int].span,
    {
        self.tokens[self.pos].span
    }

    pub fn is_eof(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == (self.tokens@[self.pos as int].kind is Eof),
            !r ==> self.pos + 1 < self.tokens@.len(),
    {
        match &self.tokens[self.pos].kind {
            TokenKind::Eof => true,
            _ => {
                proof {
                    if self.pos + 1 >= self.tokens@.len() {
                        assert(self.pos as int == self.tokens@.len() - 1);
                        assert(self.tokens@[self.pos as int] == self.tokens@.last());
                        assert(false);
                    }
                }
                false
            },
        }
    }

    pub fn advance(&mut self)
        requires
            old(self).wf(),
            !(old(self).tokens@[old(self).pos as int].kind is Eof),
        ensures
            parser_step_post(*old(self), *final(self)),
            final(self).pos == old(self).pos + 1,
            final(self).prog@ == old(self).prog@,
            final(self).strict == old(self).strict,
            final(self).in_async == old(self).in_async,
            final(self).in_generator == old(self).in_generator,
    {
        let tlen = self.tokens.len();
        proof {
            assert(tlen == self.tokens@.len());
            if self.pos + 1 >= tlen {
                assert(self.pos as int == self.tokens@.len() - 1);
                assert(self.tokens@[self.pos as int] == self.tokens@.last());
                assert(false);
            }
            lemma_arena_refl(self.prog@);
        }
        self.pos = self.pos + 1;
    }

    pub fn emit_expr(
        &mut self,
        kind: ExprKind,
        span: Span,
        in_optional_chain: bool,
    ) -> (res: ParseStep<ExprId>)
        requires
            old(self).wf(),
            expr_refs_in_bounds(old(self).prog.exprs@.len(), old(self).prog.stmts@.len(), kind),
            expr_grammar_local_wf(old(self).prog.exprs@, kind),
        ensures
            parser_step_post(*old(self), *final(self)),
            final(self).pos == old(self).pos,
            final(self).strict == old(self).strict,
            final(self).in_async == old(self).in_async,
            final(self).in_generator == old(self).in_generator,
            match res {
                ParseStep::Ok(id) => {
                    id.0 < final(self).prog.exprs@.len()
                        && final(self).prog.exprs@[id.0 as int].kind == kind
                        && final(self).prog.exprs@[id.0 as int].span == span
                        && final(self).prog.exprs@[id.0 as int].in_optional_chain == in_optional_chain
                },
                _ => final(self).prog@ == old(self).prog@,
            },
    {
        let ghost p0 = self.prog@;
        proof {
            reveal(prog_grammar_wf);
        }
        match self.prog.alloc_expr(kind, span, in_optional_chain) {
            Ok(id) => {
                proof {
                    reveal(prog_grammar_wf);
                    reveal(arena_prefix_preserved);
                    assert(arena_grew(p0, self.prog@));
                }
                ParseStep::Ok(id)
            },
            Err(e) => {
                proof {
                    reveal(prog_grammar_wf);
                    lemma_arena_refl(self.prog@);
                }
                ParseStep::SyntaxError(e)
            },
        }
    }

    pub fn emit_stmt(&mut self, kind: StmtKind, span: Span) -> (res: ParseStep<StmtId>)
        requires
            old(self).wf(),
            stmt_refs_in_bounds(old(self).prog.exprs@.len(), old(self).prog.stmts@.len(), kind),
            stmt_grammar_local_wf(kind),
        ensures
            parser_step_post(*old(self), *final(self)),
            final(self).pos == old(self).pos,
            final(self).strict == old(self).strict,
            final(self).in_async == old(self).in_async,
            final(self).in_generator == old(self).in_generator,
            match res {
                ParseStep::Ok(id) => {
                    id.0 < final(self).prog.stmts@.len()
                        && final(self).prog.stmts@[id.0 as int].kind == kind
                        && final(self).prog.stmts@[id.0 as int].span == span
                },
                _ => final(self).prog@ == old(self).prog@,
            },
    {
        let ghost p0 = self.prog@;
        proof {
            reveal(prog_grammar_wf);
        }
        match self.prog.alloc_stmt(kind, span) {
            Ok(id) => {
                proof {
                    reveal(prog_grammar_wf);
                    reveal(arena_prefix_preserved);
                    assert(arena_grew(p0, self.prog@));
                }
                ParseStep::Ok(id)
            },
            Err(e) => {
                proof {
                    reveal(prog_grammar_wf);
                    lemma_arena_refl(self.prog@);
                }
                ParseStep::SyntaxError(e)
            },
        }
    }

    pub fn expect_punct(&mut self, expected: Punctuator) -> (res: ParseStep<Span>)
        requires
            old(self).wf(),
        ensures
            parser_step_post(*old(self), *final(self)),
            final(self).prog@ == old(self).prog@,
            final(self).strict == old(self).strict,
            final(self).in_async == old(self).in_async,
            final(self).in_generator == old(self).in_generator,
            match res {
                ParseStep::Ok(_) => final(self).pos == old(self).pos + 1,
                _ => final(self).pos == old(self).pos,
            },
    {
        let sp = self.cur_span();
        match &self.tokens[self.pos].kind {
            TokenKind::Punct(p) if *p == expected => {
                self.advance();
                ParseStep::Ok(sp)
            },
            TokenKind::Eof => {
                proof {
                    lemma_arena_refl(self.prog@);
                }
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedEof,
                    span: sp,
                })
            },
            _ => {
                proof {
                    lemma_arena_refl(self.prog@);
                }
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedToken,
                    span: sp,
                })
            },
        }
    }

    /// ECMA-262 §12.9.1 Automatic Semicolon Insertion (ASI).
    pub fn consume_semicolon(&mut self) -> (res: ParseStep<()>)
        requires
            old(self).wf(),
        ensures
            parser_step_post(*old(self), *final(self)),
            final(self).prog@ == old(self).prog@,
            final(self).strict == old(self).strict,
            final(self).in_async == old(self).in_async,
            final(self).in_generator == old(self).in_generator,
    {
        let tok = &self.tokens[self.pos];
        match &tok.kind {
            TokenKind::Punct(Punctuator::Semicolon) => {
                self.advance();
                ParseStep::Ok(())
            },
            TokenKind::Punct(Punctuator::RBrace) | TokenKind::Eof => {
                proof {
                    lemma_arena_refl(self.prog@);
                }
                ParseStep::Ok(())
            },
            _ => {
                if tok.preceded_by_line_terminator {
                    proof {
                        lemma_arena_refl(self.prog@);
                    }
                    ParseStep::Ok(())
                } else {
                    let sp = tok.span;
                    proof {
                        lemma_arena_refl(self.prog@);
                    }
                    ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::MissingSemicolon,
                        span: sp,
                    })
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------------------
// Grammar Well-Formedness Runtime Checkers & Lookahead Predicates
// ---------------------------------------------------------------------------------------

fn is_punct(tok: &Token, expected: Punctuator) -> (r: bool)
    ensures
        r == (tok.kind == TokenKind::Punct(expected)),
        r ==> !(tok.kind is Eof),
{
    match &tok.kind {
        TokenKind::Punct(pt) => *pt == expected,
        _ => false,
    }
}

fn is_kw(tok: &Token, expected: Keyword) -> (r: bool)
    ensures
        r == (tok.kind == TokenKind::Keyword(expected)),
        r ==> !(tok.kind is Eof),
{
    match &tok.kind {
        TokenKind::Keyword(kw) => *kw == expected,
        _ => false,
    }
}

fn is_unparen_logical_and_or_exec(e: &Expr) -> (r: bool)
    ensures
        r == spec_is_unparen_logical_and_or(*e),
{
    match &e.kind {
        ExprKind::Binary { op: BinOp::LogicalAnd, .. } => true,
        ExprKind::Binary { op: BinOp::LogicalOr, .. } => true,
        _ => false,
    }
}

fn is_unparen_coalesce_exec(e: &Expr) -> (r: bool)
    ensures
        r == spec_is_unparen_coalesce(*e),
{
    match &e.kind {
        ExprKind::Binary { op: BinOp::Coalesce, .. } => true,
        _ => false,
    }
}

fn is_unparen_unary_or_await_exec(e: &Expr) -> (r: bool)
    ensures
        r == spec_is_unparen_unary_or_await(*e),
{
    match &e.kind {
        ExprKind::Unary { .. } | ExprKind::Await(_) => true,
        _ => false,
    }
}

fn is_destructuring_expr_lhs(prog: &Program, eid: ExprId) -> (r: bool)
    requires
        eid.0 < prog.exprs@.len(),
{
    let mut cur = eid;
    let mut steps: usize = 0;
    let max_steps = prog.exprs.len();
    while steps < max_steps
        invariant
            cur.0 < prog.exprs@.len(),
            max_steps == prog.exprs@.len(),
            steps <= max_steps,
        decreases max_steps - steps,
    {
        match &prog.exprs[cur.0].kind {
            ExprKind::Paren(inner) => {
                if inner.0 < prog.exprs.len() {
                    cur = *inner;
                    steps = steps + 1;
                } else {
                    return false;
                }
            },
            ExprKind::Array(_) | ExprKind::Object(_) => {
                return true;
            },
            _ => {
                return false;
            },
        }
    }
    false
}

/// Whether `tok` can be parsed as a syntactic `Identifier` under `(in_async, in_generator)`.
/// Note: strict-mode reserved words (`implements`, `let`, `static`, `yield`, etc.) and escaped
/// keywords are checked in `early_errors.rs` so strictness from inner `"use strict"` prologues
/// applies uniformly!
fn token_can_be_ident(tok: &Token, in_async: bool, in_generator: bool) -> (r: bool)
    ensures
        r ==> !(tok.kind is Eof),
{
    match &tok.kind {
        TokenKind::Ident { .. } => true,
        TokenKind::Keyword(kw) => {
            if is_unconditional_reserved(*kw) {
                false
            } else if in_async && *kw == Keyword::Await {
                false
            } else if in_generator && *kw == Keyword::Yield {
                false
            } else {
                true
            }
        },
        _ => false,
    }
}

/// Whether `Keyword::Let` at `pos` starts a `LexicalDeclaration` (`let x`, `let [`, `let {`).
fn is_let_lexical_decl_at(tokens: &[Token], pos: usize) -> (r: bool)
    requires
        pos < tokens@.len(),
        spec_tokens_wf(tokens@),
{
    match &tokens[pos].kind {
        TokenKind::Keyword(Keyword::Let) => {
            proof {
                if pos + 1 >= tokens@.len() {
                    assert(pos as int == tokens@.len() - 1);
                    assert(tokens@[pos as int] == tokens@.last());
                    assert(false);
                }
            }
            if is_punct(&tokens[pos + 1], Punctuator::LBracket)
                || is_punct(&tokens[pos + 1], Punctuator::LBrace)
            {
                true
            } else {
                match &tokens[pos + 1].kind {
                    TokenKind::Ident { .. } => true,
                    TokenKind::Keyword(kw) => !is_unconditional_reserved(*kw),
                    _ => false,
                }
            }
        },
        _ => false,
    }
}

/// Whether `Keyword::Let` at `pos` is followed by `[` (`[lookahead ∉ { ..., let [ }]` in §14.5).
fn is_let_bracket_at(tokens: &[Token], pos: usize) -> (r: bool)
    requires
        pos < tokens@.len(),
        spec_tokens_wf(tokens@),
{
    match &tokens[pos].kind {
        TokenKind::Keyword(Keyword::Let) => {
            proof {
                if pos + 1 >= tokens@.len() {
                    assert(pos as int == tokens@.len() - 1);
                    assert(tokens@[pos as int] == tokens@.last());
                    assert(false);
                }
            }
            is_punct(&tokens[pos + 1], Punctuator::LBracket)
        },
        _ => false,
    }
}

/// Checks if a `/` or `/=` at `start_pos` has a closing `/` on the same line (before `Eof` or newline),
/// distinguishing valid `RegExpLiteral` syntax (`Unsupported(RegExpLiteral)`) from stray `/` (`SyntaxError`).
fn has_closing_slash_on_same_line(tokens: &[Token], start_pos: usize) -> (r: bool)
    requires
        start_pos < tokens@.len(),
        spec_tokens_wf(tokens@),
{
    let n = tokens.len();
    if n - start_pos <= 1 {
        return false;
    }
    let mut idx: usize = start_pos + 1;
    while idx < n
        invariant
            start_pos < idx && idx <= n,
            n == tokens@.len(),
        decreases n - idx,
    {
        if tokens[idx].preceded_by_line_terminator {
            return false;
        }
        match &tokens[idx].kind {
            TokenKind::Eof => {
                return false;
            },
            TokenKind::Punct(Punctuator::Slash) | TokenKind::Punct(Punctuator::SlashEq) => {
                return true;
            },
            _ => {},
        }
        idx = idx + 1;
    }
    false
}

/// Balanced `(` ... `)` scanner starting at `lparen_pos` (where `tokens[lparen_pos]` is `(`).
/// Returns `Some(rparen_pos)` with `lparen_pos < rparen_pos < tokens.len()`.
fn find_matching_rparen(tokens: &[Token], lparen_pos: usize) -> (res: Option<usize>)
    requires
        lparen_pos < tokens@.len(),
        tokens@[lparen_pos as int].kind == TokenKind::Punct(Punctuator::LParen),
        spec_tokens_wf(tokens@),
    ensures
        match res {
            Some(rp) => lparen_pos < rp && rp + 1 < tokens@.len(),
            None => true,
        },
{
    let n = tokens.len();
    proof {
        if lparen_pos + 1 >= n {
            assert(lparen_pos as int == tokens@.len() - 1);
            assert(tokens@[lparen_pos as int] == tokens@.last());
            assert(false);
        }
    }
    let mut idx: usize = lparen_pos + 1;
    let mut depth: usize = 1;
    while idx < n
        invariant
            lparen_pos < idx && idx <= n,
            n == tokens@.len(),
            spec_tokens_wf(tokens@),
            depth >= 1,
            depth <= idx - lparen_pos,
        decreases n - idx,
    {
        match &tokens[idx].kind {
            TokenKind::Punct(Punctuator::LParen) => {
                depth = depth + 1;
            },
            TokenKind::Punct(Punctuator::RParen) => {
                depth = depth - 1;
                if depth == 0 {
                    proof {
                        if idx + 1 >= tokens@.len() {
                            assert(idx as int == tokens@.len() - 1);
                            assert(tokens@[idx as int] == tokens@.last());
                            assert(false);
                        }
                    }
                    return Some(idx);
                }
            },
            TokenKind::Eof => {
                return None;
            },
            _ => {},
        }
        idx = idx + 1;
    }
    None
}

// ---------------------------------------------------------------------------------------
// Identifier & Property Name Parsers
// ---------------------------------------------------------------------------------------

fn parse_ident<'a>(p: &mut Parser<'a>) -> (res: ParseStep<Ident>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).prog@ == old(p).prog@,
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(_) => final(p).pos == old(p).pos + 1,
            _ => final(p).pos == old(p).pos,
        },
{
    let tok = &p.tokens[p.pos];
    let sp = tok.span;
    match &tok.kind {
        TokenKind::Ident { name, has_escape } => {
            let nm = clone_u8_slice(name.as_slice());
            let esc = *has_escape;
            p.advance();
            ParseStep::Ok(Ident { name: nm, has_escape: esc, span: sp })
        },
        TokenKind::Keyword(kw) => {
            let k = *kw;
            if token_can_be_ident(tok, p.in_async, p.in_generator) {
                let nm = keyword_bytes(k);
                p.advance();
                ParseStep::Ok(Ident { name: nm, has_escape: false, span: sp })
            } else {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedToken,
                    span: sp,
                })
            }
        },
        TokenKind::Punct(Punctuator::LBracket) | TokenKind::Punct(Punctuator::LBrace) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::DestructuringPattern,
                span: sp,
            })
        },
        TokenKind::Eof => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedEof,
                span: sp,
            })
        },
        _ => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: sp,
            })
        },
    }
}

/// Parse an `Identifier` with custom `(allow_await_ident, allow_yield_ident)` flags
/// (needed when parsing `async (params) => ...` or `function* name(...)` before toggling context).
fn parse_ident_with_flags<'a>(
    p: &mut Parser<'a>,
    in_async_ctx: bool,
    in_gen_ctx: bool,
) -> (res: ParseStep<Ident>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).prog@ == old(p).prog@,
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(_) => final(p).pos == old(p).pos + 1,
            _ => final(p).pos == old(p).pos,
        },
{
    let tok = &p.tokens[p.pos];
    let sp = tok.span;
    match &tok.kind {
        TokenKind::Ident { name, has_escape } => {
            let nm = clone_u8_slice(name.as_slice());
            let esc = *has_escape;
            p.advance();
            ParseStep::Ok(Ident { name: nm, has_escape: esc, span: sp })
        },
        TokenKind::Keyword(kw) => {
            let k = *kw;
            if token_can_be_ident(tok, in_async_ctx, in_gen_ctx) {
                let nm = keyword_bytes(k);
                p.advance();
                ParseStep::Ok(Ident { name: nm, has_escape: false, span: sp })
            } else {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedToken,
                    span: sp,
                })
            }
        },
        TokenKind::Punct(Punctuator::LBracket) | TokenKind::Punct(Punctuator::LBrace) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::DestructuringPattern,
                span: sp,
            })
        },
        TokenKind::Eof => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedEof,
                span: sp,
            })
        },
        _ => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: sp,
            })
        },
    }
}

/// ECMA-262 §12.7 `IdentifierName` (allows ALL keywords as property names after `.` or `?.`).
fn parse_identifier_name<'a>(p: &mut Parser<'a>) -> (res: ParseStep<(Vec<u8>, Span)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).prog@ == old(p).prog@,
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(_) => final(p).pos == old(p).pos + 1,
            _ => final(p).pos == old(p).pos,
        },
{
    let tok = &p.tokens[p.pos];
    let sp = tok.span;
    match &tok.kind {
        TokenKind::Ident { name, .. } => {
            let nm = clone_u8_slice(name.as_slice());
            p.advance();
            ParseStep::Ok((nm, sp))
        },
        TokenKind::Keyword(kw) => {
            let nm = keyword_bytes(*kw);
            p.advance();
            ParseStep::Ok((nm, sp))
        },
        TokenKind::Eof => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedEof,
                span: sp,
            })
        },
        _ => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: sp,
            })
        },
    }
}

// ---------------------------------------------------------------------------------------
// Operator Mapping Tables (Pratt Binding Powers & Assignment Operators)
// ---------------------------------------------------------------------------------------

fn match_binary_op(tok: &Token, allow_in: bool) -> (res: Option<(BinOp, u8, u8)>)
    ensures
        match res {
            Some((op, l_bp, r_bp)) => {
                op != BinOp::Exp && l_bp < r_bp && r_bp <= 23 && !(tok.kind is Eof)
            },
            None => true,
        },
{
    match &tok.kind {
        TokenKind::Punct(p) => match p {
            Punctuator::QuestionQuestion => Some((BinOp::Coalesce, 2, 3)),
            Punctuator::PipePipe => Some((BinOp::LogicalOr, 4, 5)),
            Punctuator::AmpAmp => Some((BinOp::LogicalAnd, 6, 7)),
            Punctuator::Pipe => Some((BinOp::BitOr, 8, 9)),
            Punctuator::Caret => Some((BinOp::BitXor, 10, 11)),
            Punctuator::Amp => Some((BinOp::BitAnd, 12, 13)),
            Punctuator::EqEq => Some((BinOp::EqEq, 14, 15)),
            Punctuator::Ne => Some((BinOp::Ne, 14, 15)),
            Punctuator::EqEqEq => Some((BinOp::EqEqEq, 14, 15)),
            Punctuator::NeEq => Some((BinOp::NeEq, 14, 15)),
            Punctuator::Lt => Some((BinOp::Lt, 16, 17)),
            Punctuator::Gt => Some((BinOp::Gt, 16, 17)),
            Punctuator::Le => Some((BinOp::Le, 16, 17)),
            Punctuator::Ge => Some((BinOp::Ge, 16, 17)),
            Punctuator::Shl => Some((BinOp::Shl, 18, 19)),
            Punctuator::Shr => Some((BinOp::Shr, 18, 19)),
            Punctuator::UShr => Some((BinOp::UShr, 18, 19)),
            Punctuator::Plus => Some((BinOp::Add, 20, 21)),
            Punctuator::Minus => Some((BinOp::Sub, 20, 21)),
            Punctuator::Star => Some((BinOp::Mul, 22, 23)),
            Punctuator::Slash => Some((BinOp::Div, 22, 23)),
            Punctuator::Percent => Some((BinOp::Rem, 22, 23)),
            _ => None,
        },
        TokenKind::Keyword(Keyword::Instanceof) => Some((BinOp::Instanceof, 16, 17)),
        TokenKind::Keyword(Keyword::In) => {
            if allow_in {
                Some((BinOp::In, 16, 17))
            } else {
                None
            }
        },
        _ => None,
    }
}

fn match_assign_op(tok: &Token) -> (res: Option<AssignOp>)
    ensures
        res is Some ==> !(tok.kind is Eof),
{
    match &tok.kind {
        TokenKind::Punct(p) => match p {
            Punctuator::Eq => Some(AssignOp::Assign),
            Punctuator::PlusEq => Some(AssignOp::AddAssign),
            Punctuator::MinusEq => Some(AssignOp::SubAssign),
            Punctuator::StarEq => Some(AssignOp::MulAssign),
            Punctuator::SlashEq => Some(AssignOp::DivAssign),
            Punctuator::PercentEq => Some(AssignOp::RemAssign),
            Punctuator::StarStarEq => Some(AssignOp::ExpAssign),
            Punctuator::ShlEq => Some(AssignOp::ShlAssign),
            Punctuator::ShrEq => Some(AssignOp::ShrAssign),
            Punctuator::UShrEq => Some(AssignOp::UShrAssign),
            Punctuator::AmpEq => Some(AssignOp::BitAndAssign),
            Punctuator::PipeEq => Some(AssignOp::BitOrAssign),
            Punctuator::CaretEq => Some(AssignOp::BitXorAssign),
            Punctuator::AmpAmpEq => Some(AssignOp::LogicalAndAssign),
            Punctuator::PipePipeEq => Some(AssignOp::LogicalOrAssign),
            Punctuator::QuestionQuestionEq => Some(AssignOp::CoalesceAssign),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------------------
// Formal Parameters & Function / Method / Arrow Body Helpers
// ---------------------------------------------------------------------------------------

/// Parses `( FormalParameters )` starting AT `(` and consuming the closing `)`.
/// Proves `spec_params_grammar_wf(params@)` and `forall p: p.default < exprs.len()`.
fn parse_formal_params<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    fn_is_async: bool,
    fn_is_generator: bool,
) -> (res: ParseStep<Vec<Param>>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(params) => {
                old(p).pos < final(p).pos
                    && spec_params_grammar_wf(params@)
                    && forall|k: int|
                        0 <= k < params@.len() ==> match (#[trigger] params@[k]).default {
                            Some(id) => id.0 < final(p).prog.exprs@.len(),
                            None => true,
                        }
            },
            _ => true,
        },
    decreases fuel, 20nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match p.expect_punct(Punctuator::LParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let saved_async = p.in_async;
    let saved_gen = p.in_generator;
    p.in_async = fn_is_async;
    p.in_generator = fn_is_generator;

    let mut params: Vec<Param> = Vec::new();
    while !is_punct(&p.tokens[p.pos], Punctuator::RParen)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            saved_async == old(p).in_async,
            saved_gen == old(p).in_generator,
            p.in_async == fn_is_async,
            p.in_generator == fn_is_generator,
            forall|k: int|
                0 <= k < params@.len() ==> !(#[trigger] params@[k]).is_rest
                    && match params@[k].default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    },
        decreases p.tokens@.len() - p.pos,
    {
        if is_punct(&p.tokens[p.pos], Punctuator::Ellipsis) {
            let ghost prog_before_rest = p.prog@;
            p.advance();
            let rest_name = match parse_ident(p) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_rest, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_rest, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            if is_punct(&p.tokens[p.pos], Punctuator::Eq) {
                let sp = p.cur_span();
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::RestParamWithDefault,
                    span: sp,
                });
            }
            if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
                let sp = p.cur_span();
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::RestParamNotLast,
                    span: sp,
                });
            }
            let ghost prev_params = params@;
            params.push(Param { name: rest_name, default: None, is_rest: true });
            match p.expect_punct(Punctuator::RParen) {
                ParseStep::Ok(_) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    proof {
                        assert forall|k: int| 0 <= k < params@.len() implies (
                            ((#[trigger] params@[k]).is_rest ==> (params@[k].default is None
                                && k == params@.len() - 1))
                                && match params@[k].default {
                                    Some(id) => id.0 < p.prog.exprs@.len(),
                                    None => true,
                                }
                        ) by {
                            if k < prev_params.len() {
                                assert(params@[k] == prev_params[k]);
                            }
                        }
                    }
                    return ParseStep::Ok(params);
                },
                ParseStep::SyntaxError(e) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    return ParseStep::Unsupported(u);
                },
            }
        }

        let ghost prog_loop_start = p.prog@;
        let param_name = match parse_ident(p) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                proof {
                    lemma_arena_trans(old(p).prog@, prog_loop_start, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                proof {
                    lemma_arena_trans(old(p).prog@, prog_loop_start, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };

        let def_opt = if is_punct(&p.tokens[p.pos], Punctuator::Eq) {
            p.advance();
            let ghost prog_before_def = p.prog@;
            match parse_assignment_expr(p, fuel - 1, true) {
                ParseStep::Ok(eid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                        assert forall|k: int| 0 <= k < params@.len() implies (
                            !(#[trigger] params@[k]).is_rest
                                && match params@[k].default {
                                    Some(id) => id.0 < p.prog.exprs@.len(),
                                    None => true,
                                }
                        ) by {
                            if let Some(id) = params@[k].default {
                                assert(id.0 < prog_before_def.exprs.len());
                            }
                        }
                    }
                    Some(eid)
                },
                ParseStep::SyntaxError(e) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    p.in_async = saved_async;
                    p.in_generator = saved_gen;
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            None
        };

        let ghost prev_params = params@;
        params.push(Param { name: param_name, default: def_opt, is_rest: false });
        proof {
            assert forall|k: int| 0 <= k < params@.len() implies (
                !(#[trigger] params@[k]).is_rest
                    && match params@[k].default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    }
            ) by {
                if k < prev_params.len() {
                    assert(params@[k] == prev_params[k]);
                }
            }
        }

        if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
            p.advance();
        } else if !is_punct(&p.tokens[p.pos], Punctuator::RParen) {
            let sp = p.cur_span();
            let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
        }
    }

    p.advance(); // consume `)`
    p.in_async = saved_async;
    p.in_generator = saved_gen;
    ParseStep::Ok(params)
}

/// Parses `{ FunctionBody }` starting AT `{` and consuming `}`.
/// Returns `(stmts, body_has_use_strict, has_directive_octal_escape, end_span)`.
fn parse_function_body<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    fn_is_async: bool,
    fn_is_generator: bool,
) -> (res: ParseStep<(Vec<StmtId>, bool, bool, Span)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok((stmts, _, _, _)) => {
                old(p).pos < final(p).pos
                    && forall|s: int| 0 <= s < stmts@.len() ==> (#[trigger] stmts@[s]).0 < final(p).prog.stmts@.len()
            },
            _ => true,
        },
    decreases fuel, 20nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match p.expect_punct(Punctuator::LBrace) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let saved_strict = p.strict;
    let saved_async = p.in_async;
    let saved_gen = p.in_generator;
    p.in_async = fn_is_async;
    p.in_generator = fn_is_generator;

    let ghost prog_after_lbrace = p.prog@;
    let (stmts, has_use_strict, has_octal) = match parse_stmt_list_with_prologue(p, fuel - 1, true) {
        ParseStep::Ok(t) => t,
        ParseStep::SyntaxError(e) => {
            p.strict = saved_strict;
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_lbrace, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            p.strict = saved_strict;
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_lbrace, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_lbrace, p.prog@);
    }

    match p.expect_punct(Punctuator::RBrace) {
        ParseStep::Ok(end_sp) => {
            p.strict = saved_strict;
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::Ok((stmts, has_use_strict, has_octal, end_sp))
        },
        ParseStep::SyntaxError(e) => {
            p.strict = saved_strict;
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::SyntaxError(e)
        },
        ParseStep::Unsupported(u) => {
            p.strict = saved_strict;
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::Unsupported(u)
        },
    }
}

// ---------------------------------------------------------------------------------------
// Array, Object, Function Expression, and Call Argument Parsers
// ---------------------------------------------------------------------------------------

fn parse_call_args<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<(Vec<CallArg>, Span)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok((args, _)) => {
                old(p).pos < final(p).pos
                    && forall|k: int|
                        0 <= k < args@.len() ==> match #[trigger] args@[k] {
                            CallArg::Arg(id) => id.0 < final(p).prog.exprs@.len(),
                            CallArg::Spread(id) => id.0 < final(p).prog.exprs@.len(),
                        }
            },
            _ => true,
        },
    decreases fuel, 19nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match p.expect_punct(Punctuator::LParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let mut args: Vec<CallArg> = Vec::new();
    while !is_punct(&p.tokens[p.pos], Punctuator::RParen)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            forall|k: int|
                0 <= k < args@.len() ==> match #[trigger] args@[k] {
                    CallArg::Arg(id) => id.0 < p.prog.exprs@.len(),
                    CallArg::Spread(id) => id.0 < p.prog.exprs@.len(),
                },
        decreases p.tokens@.len() - p.pos,
    {
        let is_spread = if is_punct(&p.tokens[p.pos], Punctuator::Ellipsis) {
            p.advance();
            true
        } else {
            false
        };
        let ghost prog_before_arg = p.prog@;
        let eid = match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let item = if is_spread { CallArg::Spread(eid) } else { CallArg::Arg(eid) };
        let ghost prev_args = args@;
        args.push(item);
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
            assert forall|k: int| 0 <= k < args@.len() implies match #[trigger] args@[k] {
                CallArg::Arg(id) => id.0 < p.prog.exprs@.len(),
                CallArg::Spread(id) => id.0 < p.prog.exprs@.len(),
            } by {
                if k < prev_args.len() {
                    assert(args@[k] == prev_args[k]);
                    match prev_args[k] {
                        CallArg::Arg(id) => {
                            assert(id.0 < prog_before_arg.exprs.len());
                        },
                        CallArg::Spread(id) => {
                            assert(id.0 < prog_before_arg.exprs.len());
                        },
                    }
                }
            }
        }
        if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
            p.advance();
        } else if !is_punct(&p.tokens[p.pos], Punctuator::RParen) {
            let sp = p.cur_span();
            let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
            return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
        }
    }
    let end_sp = p.cur_span();
    p.advance();
    ParseStep::Ok((args, end_sp))
}

fn parse_array_literal<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind == TokenKind::Punct(Punctuator::LBracket),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 19nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }
    p.advance(); // consume `[`
    let mut elems: Vec<ArrayElem> = Vec::new();
    while !is_punct(&p.tokens[p.pos], Punctuator::RBracket)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            forall|k: int|
                0 <= k < elems@.len() ==> match #[trigger] elems@[k] {
                    ArrayElem::Hole => true,
                    ArrayElem::Elem(id) => id.0 < p.prog.exprs@.len(),
                    ArrayElem::Spread(id) => id.0 < p.prog.exprs@.len(),
                },
        decreases p.tokens@.len() - p.pos,
    {
        if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
            let ghost prev_elems = elems@;
            elems.push(ArrayElem::Hole);
            p.advance();
            proof {
                assert forall|k: int| 0 <= k < elems@.len() implies match #[trigger] elems@[k] {
                    ArrayElem::Hole => true,
                    ArrayElem::Elem(id) => id.0 < p.prog.exprs@.len(),
                    ArrayElem::Spread(id) => id.0 < p.prog.exprs@.len(),
                } by {
                    if k < prev_elems.len() {
                        assert(elems@[k] == prev_elems[k]);
                    }
                }
            }
        } else {
            let is_spread = if is_punct(&p.tokens[p.pos], Punctuator::Ellipsis) {
                p.advance();
                true
            } else {
                false
            };
            let ghost prog_before_elem = p.prog@;
            let eid = match parse_assignment_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_elem, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_elem, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let item = if is_spread { ArrayElem::Spread(eid) } else { ArrayElem::Elem(eid) };
            let ghost prev_elems = elems@;
            elems.push(item);
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_elem, p.prog@);
                assert forall|k: int| 0 <= k < elems@.len() implies match #[trigger] elems@[k] {
                    ArrayElem::Hole => true,
                    ArrayElem::Elem(id) => id.0 < p.prog.exprs@.len(),
                    ArrayElem::Spread(id) => id.0 < p.prog.exprs@.len(),
                } by {
                    if k < prev_elems.len() {
                        assert(elems@[k] == prev_elems[k]);
                        match prev_elems[k] {
                            ArrayElem::Hole => {},
                            ArrayElem::Elem(id) => {
                                assert(id.0 < prog_before_elem.exprs.len());
                            },
                            ArrayElem::Spread(id) => {
                                assert(id.0 < prog_before_elem.exprs.len());
                            },
                        }
                    }
                }
            }
            if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
                p.advance();
            } else if !is_punct(&p.tokens[p.pos], Punctuator::RBracket) {
                let sp = p.cur_span();
                let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
                return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
            }
        }
    }
    let end_sp = p.cur_span();
    p.advance(); // consume `]`
    let ghost prog_before_emit = p.prog@;
    let res = p.emit_expr(
        ExprKind::Array(elems),
        Span { start: start_sp.start, end: end_sp.end },
        false,
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

fn parse_prop_key<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<PropKeyAst>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(k) => {
                old(p).pos < final(p).pos
                    && match k {
                        PropKeyAst::Computed(id) => id.0 < final(p).prog.exprs@.len(),
                        _ => true,
                    }
            },
            _ => true,
        },
    decreases fuel, 18nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match &p.tokens[p.pos].kind {
        TokenKind::Punct(Punctuator::LBracket) => {
            p.advance();
            let ghost prog_before_comp = p.prog@;
            let cid = match parse_assignment_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_comp, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_comp, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_comp, p.prog@);
            }
            match p.expect_punct(Punctuator::RBracket) {
                ParseStep::Ok(_) => ParseStep::Ok(PropKeyAst::Computed(cid)),
                ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
                ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
            }
        },
        TokenKind::StringLit { units, has_legacy_octal_escape, .. } => {
            let u = clone_u16_slice(units.as_slice());
            let oct = *has_legacy_octal_escape;
            p.advance();
            ParseStep::Ok(PropKeyAst::StringLit { units: u, has_legacy_octal_escape: oct })
        },
        TokenKind::Number { raw, is_bigint, has_legacy_octal_or_leading_zero } => {
            let r = clone_u8_slice(raw.as_slice());
            let bi = *is_bigint;
            let oct = *has_legacy_octal_or_leading_zero;
            p.advance();
            ParseStep::Ok(PropKeyAst::NumberLit {
                raw: r,
                is_bigint: bi,
                has_legacy_octal_or_leading_zero: oct,
            })
        },
        _ => match parse_identifier_name(p) {
            ParseStep::Ok((nm, _)) => ParseStep::Ok(PropKeyAst::Ident(nm)),
            ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
            ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
        },
    }
}

/// Parses `( PropertySetParameterList )` — exactly one non-rest parameter with optional default.
fn parse_setter_param<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<Param>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(param) => {
                old(p).pos < final(p).pos
                    && !param.is_rest
                    && match param.default {
                        Some(id) => id.0 < final(p).prog.exprs@.len(),
                        None => true,
                    }
            },
            _ => true,
        },
    decreases fuel, 18nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match p.expect_punct(Punctuator::LParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let saved_async = p.in_async;
    let saved_gen = p.in_generator;
    p.in_async = false;
    p.in_generator = false;

    if is_punct(&p.tokens[p.pos], Punctuator::Ellipsis) {
        let sp = p.cur_span();
        p.in_async = saved_async;
        p.in_generator = saved_gen;
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedToken,
            span: sp,
        });
    }
    let name = match parse_ident(p) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            return ParseStep::Unsupported(u);
        },
    };
    let def_opt = if is_punct(&p.tokens[p.pos], Punctuator::Eq) {
        p.advance();
        let ghost prog_before_def = p.prog@;
        match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                }
                Some(id)
            },
            ParseStep::SyntaxError(e) => {
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                p.in_async = saved_async;
                p.in_generator = saved_gen;
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_def, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        }
    } else {
        None
    };
    // Optional trailing comma is NOT allowed in Setter `( x )` in ECMA-262 `PropertySetParameterList : FormalParameter`
    match p.expect_punct(Punctuator::RParen) {
        ParseStep::Ok(_) => {
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::Ok(Param { name, default: def_opt, is_rest: false })
        },
        ParseStep::SyntaxError(e) => {
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::SyntaxError(e)
        },
        ParseStep::Unsupported(u) => {
            p.in_async = saved_async;
            p.in_generator = saved_gen;
            ParseStep::Unsupported(u)
        },
    }
}

pub open spec fn spec_one_prop_valid(
    exprs_len: nat,
    stmts_len: nat,
    prop: ObjPropKind,
) -> bool {
    (match prop {
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
                && spec_params_grammar_wf(params@)
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
                && !param.is_rest
        },
        ObjPropKind::Spread(id) => id.0 < exprs_len,
    })
}

proof fn lemma_one_prop_frame(
    e0: nat,
    s0: nat,
    e1: nat,
    s1: nat,
    prop: ObjPropKind,
)
    requires
        e0 <= e1,
        s0 <= s1,
        spec_one_prop_valid(e0, s0, prop),
    ensures
        spec_one_prop_valid(e1, s1, prop),
{
    match prop {
        ObjPropKind::Method { params, body, .. } => {
            assert forall|p: int| 0 <= p < params@.len() implies match (#[trigger] params@[p]).default {
                Some(id) => id.0 < e1,
                None => true,
            } by {
                assert(match params@[p].default {
                    Some(id) => id.0 < e0,
                    None => true,
                });
            }
            assert forall|s: int| 0 <= s < body@.len() implies (#[trigger] body@[s]).0 < s1 by {
                assert(body@[s].0 < s0);
            }
        },
        ObjPropKind::Getter { body, .. } => {
            assert forall|s: int| 0 <= s < body@.len() implies (#[trigger] body@[s]).0 < s1 by {
                assert(body@[s].0 < s0);
            }
        },
        ObjPropKind::Setter { body, .. } => {
            assert forall|s: int| 0 <= s < body@.len() implies (#[trigger] body@[s]).0 < s1 by {
                assert(body@[s].0 < s0);
            }
        },
        _ => {},
    }
}

fn is_prop_self_delimiter(tok: &Token) -> (r: bool) {
    match &tok.kind {
        TokenKind::Punct(Punctuator::Colon)
        | TokenKind::Punct(Punctuator::Comma)
        | TokenKind::Punct(Punctuator::RBrace)
        | TokenKind::Punct(Punctuator::LParen)
        | TokenKind::Punct(Punctuator::Eq) => true,
        _ => false,
    }
}

#[verifier::spinoff_prover]
fn parse_one_object_prop<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ObjPropKind>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind != TokenKind::Punct(Punctuator::RBrace),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(prop) => {
                old(p).pos < final(p).pos
                    && spec_one_prop_valid(
                        final(p).prog.exprs@.len(),
                        final(p).prog.stmts@.len(),
                        prop,
                    )
            },
            _ => true,
        },
    decreases fuel, 19nat, 0nat,
{
    let prop_start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: prop_start_sp,
        });
    }
    if p.is_eof() {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedEof,
            span: prop_start_sp,
        });
    }
    proof {
        lemma_arena_refl(p.prog@);
    }

    // 1. Spread property `...AssignmentExpression`
    if is_punct(&p.tokens[p.pos], Punctuator::Ellipsis) {
        p.advance();
        let ghost prog_before = p.prog@;
        return match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before, p.prog@);
                }
                ParseStep::Ok(ObjPropKind::Spread(id))
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    // 2. Generator method `* PropertyName ( params ) { body }`
    if is_punct(&p.tokens[p.pos], Punctuator::Star) {
        p.advance();
        let ghost prog_after_star = p.prog@;
        let key = match parse_prop_key(p, fuel - 1) {
            ParseStep::Ok(k) => k,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_star, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_star, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_key = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_star, prog_after_key);
        }
        let params = match parse_formal_params(p, fuel - 1, false, true) {
            ParseStep::Ok(ps) => ps,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_params = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_key, prog_after_params);
        }
        return match parse_function_body(p, fuel - 1, false, true) {
            ParseStep::Ok((body, has_strict, has_octal, end_sp)) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                    assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    } by {
                        assert(match params@[i].default {
                            Some(id) => id.0 < prog_after_params.exprs.len(),
                            None => true,
                        });
                    }
                }
                ParseStep::Ok(ObjPropKind::Method {
                    key,
                    params,
                    body,
                    is_async: false,
                    is_generator: true,
                    body_has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                    span: Span { start: prop_start_sp.start, end: end_sp.end },
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    // 3. Async method `async [no LineTerminator here] *? PropertyName ( params ) { body }`
    if is_kw(&p.tokens[p.pos], Keyword::Async)
        && !is_prop_self_delimiter(&p.tokens[p.pos + 1])
        && !p.tokens[p.pos + 1].preceded_by_line_terminator
    {
        p.advance(); // consume `async`
        let is_gen = if is_punct(&p.tokens[p.pos], Punctuator::Star) {
            p.advance();
            true
        } else {
            false
        };
        let ghost prog_after_pfx = p.prog@;
        let key = match parse_prop_key(p, fuel - 1) {
            ParseStep::Ok(k) => k,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_pfx, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_pfx, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_key = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_pfx, prog_after_key);
        }
        let params = match parse_formal_params(p, fuel - 1, true, is_gen) {
            ParseStep::Ok(ps) => ps,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_params = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_key, prog_after_params);
        }
        return match parse_function_body(p, fuel - 1, true, is_gen) {
            ParseStep::Ok((body, has_strict, has_octal, end_sp)) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                    assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    } by {
                        assert(match params@[i].default {
                            Some(id) => id.0 < prog_after_params.exprs.len(),
                            None => true,
                        });
                    }
                }
                ParseStep::Ok(ObjPropKind::Method {
                    key,
                    params,
                    body,
                    is_async: true,
                    is_generator: is_gen,
                    body_has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                    span: Span { start: prop_start_sp.start, end: end_sp.end },
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    // 4. Contextual unescaped `get` / `set` accessor properties
    let accessor_mode: u8 = match &p.tokens[p.pos].kind {
        TokenKind::Ident { name, has_escape: false } => {
            if !is_prop_self_delimiter(&p.tokens[p.pos + 1]) {
                if eq_ascii_3(name.as_slice(), 0x67, 0x65, 0x74) {
                    1
                } else if eq_ascii_3(name.as_slice(), 0x73, 0x65, 0x74) {
                    2
                } else {
                    0
                }
            } else {
                0
            }
        },
        _ => 0,
    };

    if accessor_mode == 1 {
        p.advance(); // consume `get`
        let ghost prog_after_get = p.prog@;
        let key = match parse_prop_key(p, fuel - 1) {
            ParseStep::Ok(k) => k,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_get, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_get, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_key = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_get, prog_after_key);
        }
        match p.expect_punct(Punctuator::LParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        return match parse_function_body(p, fuel - 1, false, false) {
            ParseStep::Ok((body, has_strict, has_octal, end_sp)) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                ParseStep::Ok(ObjPropKind::Getter {
                    key,
                    body,
                    body_has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                    span: Span { start: prop_start_sp.start, end: end_sp.end },
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    if accessor_mode == 2 {
        p.advance(); // consume `set`
        let ghost prog_after_set = p.prog@;
        let key = match parse_prop_key(p, fuel - 1) {
            ParseStep::Ok(k) => k,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_set, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_set, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_key = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_set, prog_after_key);
        }
        let param = match parse_setter_param(p, fuel - 1) {
            ParseStep::Ok(pr) => pr,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_param = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_key, prog_after_param);
        }
        return match parse_function_body(p, fuel - 1, false, false) {
            ParseStep::Ok((body, has_strict, has_octal, end_sp)) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_param, p.prog@);
                }
                ParseStep::Ok(ObjPropKind::Setter {
                    key,
                    param,
                    body,
                    body_has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                    span: Span { start: prop_start_sp.start, end: end_sp.end },
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_param, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_param, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    // 5. Shorthand `{ ident }` or CoverInitializedName `{ ident = expr }` (early SyntaxError in ObjectLiteral)
    let next_kind_is_comma_or_rbrace = is_punct(&p.tokens[p.pos + 1], Punctuator::Comma)
        || is_punct(&p.tokens[p.pos + 1], Punctuator::RBrace);
    let next_kind_is_eq = is_punct(&p.tokens[p.pos + 1], Punctuator::Eq);

    if next_kind_is_eq && token_can_be_ident(&p.tokens[p.pos], p.in_async, p.in_generator) {
        let eq_sp = p.tokens[p.pos + 1].span;
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::CoverInitializedNameInObject,
            span: eq_sp,
        });
    }

    if next_kind_is_comma_or_rbrace {
        let ident = match parse_ident(p) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
        };
        let key_bytes = clone_u8_slice(ident.name.as_slice());
        let ident_for_prop = Ident {
            name: clone_u8_slice(ident.name.as_slice()),
            has_escape: ident.has_escape,
            span: ident.span,
        };
        let id_sp = ident.span;
        let ghost prog_before_emit = p.prog@;
        return match p.emit_expr(ExprKind::Ident(ident), id_sp, false) {
            ParseStep::Ok(val_id) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                ParseStep::Ok(ObjPropKind::Init {
                    key: PropKeyAst::Ident(key_bytes),
                    value: val_id,
                    is_shorthand: true,
                    shorthand_ident: Some(ident_for_prop),
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    // 6. Regular `PropertyName : AssignmentExpression` or Concise Method `PropertyName ( params ) { body }`
    let ghost prog_before_key = p.prog@;
    let key = match parse_prop_key(p, fuel - 1) {
        ParseStep::Ok(k) => k,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_key, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_key, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_after_key = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_key, prog_after_key);
    }

    if is_punct(&p.tokens[p.pos], Punctuator::LParen) {
        let params = match parse_formal_params(p, fuel - 1, false, false) {
            ParseStep::Ok(ps) => ps,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_key, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_params = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_key, prog_after_params);
        }
        return match parse_function_body(p, fuel - 1, false, false) {
            ParseStep::Ok((body, has_strict, has_octal, end_sp)) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                    assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    } by {
                        assert(match params@[i].default {
                            Some(id) => id.0 < prog_after_params.exprs.len(),
                            None => true,
                        });
                    }
                }
                ParseStep::Ok(ObjPropKind::Method {
                    key,
                    params,
                    body,
                    is_async: false,
                    is_generator: false,
                    body_has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                    span: Span { start: prop_start_sp.start, end: end_sp.end },
                })
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::SyntaxError(e)
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                }
                ParseStep::Unsupported(u)
            },
        };
    }

    match p.expect_punct(Punctuator::Colon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let ghost prog_before_val = p.prog@;
    match parse_assignment_expr(p, fuel - 1, true) {
        ParseStep::Ok(val_id) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_val, p.prog@);
            }
            ParseStep::Ok(ObjPropKind::Init {
                key,
                value: val_id,
                is_shorthand: false,
                shorthand_ident: None,
            })
        },
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_val, p.prog@);
            }
            ParseStep::SyntaxError(e)
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_val, p.prog@);
            }
            ParseStep::Unsupported(u)
        },
    }
}

fn parse_object_literal<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind == TokenKind::Punct(Punctuator::LBrace),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 20nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }
    p.advance(); // consume `{`
    let mut props: Vec<ObjPropKind> = Vec::new();
    while !is_punct(&p.tokens[p.pos], Punctuator::RBrace)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            forall|k: int|
                0 <= k < props@.len() ==> spec_one_prop_valid(
                    p.prog.exprs@.len(),
                    p.prog.stmts@.len(),
                    #[trigger] props@[k],
                ),
        decreases p.tokens@.len() - p.pos,
    {
        let ghost prog_before_prop = p.prog@;
        let prop = match parse_one_object_prop(p, fuel) {
            ParseStep::Ok(pr) => pr,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_prop, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_prop, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prev_props = props@;
        props.push(prop);
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_prop, p.prog@);
            assert forall|k: int| 0 <= k < props@.len() implies spec_one_prop_valid(
                p.prog.exprs@.len(),
                p.prog.stmts@.len(),
                #[trigger] props@[k],
            ) by {
                if k < prev_props.len() {
                    assert(props@[k] == prev_props[k]);
                    lemma_one_prop_frame(
                        prog_before_prop.exprs.len(),
                        prog_before_prop.stmts.len(),
                        p.prog.exprs@.len(),
                        p.prog.stmts@.len(),
                        prev_props[k],
                    );
                }
            }
        }
        if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
            p.advance();
        } else if !is_punct(&p.tokens[p.pos], Punctuator::RBrace) {
            let sp = p.cur_span();
            let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
            return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
        }
    }
    let end_sp = p.cur_span();
    p.advance(); // consume `}`
    proof {
        assert forall|k: int| 0 <= k < props@.len() implies match #[trigger] props@[k] {
            ObjPropKind::Method { params, .. } => spec_params_grammar_wf(params@),
            ObjPropKind::Setter { param, .. } => !param.is_rest,
            _ => true,
        } by {
            assert(spec_one_prop_valid(p.prog.exprs@.len(), p.prog.stmts@.len(), props@[k]));
        }
    }
    let ghost prog_before_emit = p.prog@;
    let res = p.emit_expr(
        ExprKind::Object(props),
        Span { start: start_sp.start, end: end_sp.end },
        false,
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

/// Parses `function *? BindingIdentifier? ( FormalParameters ) { FunctionBody }`
/// after `function` (and optional leading `async`) has already been consumed!
fn parse_function_expr_after_kw<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    start_sp: Span,
    is_async: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 21nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    proof {
        lemma_arena_refl(p.prog@);
    }
    let is_gen = if is_punct(&p.tokens[p.pos], Punctuator::Star) {
        p.advance();
        true
    } else {
        false
    };
    // Optional inner binding name uses the function's own `(is_async, is_gen)` context per §15.2 / §15.5 / §15.8!
    let inner_name = if !is_punct(&p.tokens[p.pos], Punctuator::LParen) {
        match parse_ident_with_flags(p, is_async, is_gen) {
            ParseStep::Ok(nm) => Some(nm),
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
        }
    } else {
        None
    };

    let ghost prog_before_params = p.prog@;
    let params = match parse_formal_params(p, fuel - 1, is_async, is_gen) {
        ParseStep::Ok(ps) => ps,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_params, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_params, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_after_params = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_params, prog_after_params);
    }

    let (body, has_strict, has_octal, end_sp) = match parse_function_body(p, fuel - 1, is_async, is_gen) {
        ParseStep::Ok(t) => t,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_emit = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_params, prog_before_emit);
        assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
            Some(id) => id.0 < p.prog.exprs@.len(),
            None => true,
        } by {
            assert(match params@[i].default {
                Some(id) => id.0 < prog_after_params.exprs.len(),
                None => true,
            });
        }
    }
    let res = p.emit_expr(
        ExprKind::FunctionExpr {
            name: inner_name,
            params,
            body,
            is_async,
            is_generator: is_gen,
            body_has_use_strict: has_strict,
            has_directive_octal_escape: has_octal,
        },
        Span { start: start_sp.start, end: end_sp.end },
        false,
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

// ---------------------------------------------------------------------------------------
// Primary, Member, LeftHandSide, Update, Unary, Exponentiation, and Binary Expressions
// ---------------------------------------------------------------------------------------

#[verifier::spinoff_prover]
fn parse_primary_expr<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 1nat, 0nat,
{
    let sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }

    match &p.tokens[p.pos].kind {
        TokenKind::Keyword(Keyword::This) => {
            p.advance();
            p.emit_expr(ExprKind::This, sp, false)
        },
        TokenKind::Keyword(Keyword::Null) => {
            p.advance();
            p.emit_expr(ExprKind::Null, sp, false)
        },
        TokenKind::Keyword(Keyword::True) => {
            p.advance();
            p.emit_expr(ExprKind::Bool(true), sp, false)
        },
        TokenKind::Keyword(Keyword::False) => {
            p.advance();
            p.emit_expr(ExprKind::Bool(false), sp, false)
        },
        TokenKind::Number { raw, is_bigint, has_legacy_octal_or_leading_zero } => {
            let r = clone_u8_slice(raw.as_slice());
            let bi = *is_bigint;
            let oct = *has_legacy_octal_or_leading_zero;
            p.advance();
            p.emit_expr(
                ExprKind::Number {
                    raw: r,
                    is_bigint: bi,
                    has_legacy_octal_or_leading_zero: oct,
                },
                sp,
                false,
            )
        },
        TokenKind::StringLit { units, has_legacy_octal_escape, .. } => {
            let u = clone_u16_slice(units.as_slice());
            let oct = *has_legacy_octal_escape;
            p.advance();
            p.emit_expr(
                ExprKind::StringLit { units: u, has_legacy_octal_escape: oct },
                sp,
                false,
            )
        },
        TokenKind::NoSubTemplate { units, has_invalid_escape } => {
            let u = clone_u16_slice(units.as_slice());
            let inv = *has_invalid_escape;
            p.advance();
            p.emit_expr(
                ExprKind::TemplateNoSub { units: u, has_invalid_escape: inv },
                sp,
                false,
            )
        },
        TokenKind::Punct(Punctuator::LParen) => {
            p.advance();
            let ghost prog_after_lp = p.prog@;
            let inner = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_lp, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_lp, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_lp, p.prog@);
            }
            let end_sp = match p.expect_punct(Punctuator::RParen) {
                ParseStep::Ok(s) => s,
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_expr(
                ExprKind::Paren(inner),
                Span { start: sp.start, end: end_sp.end },
                false,
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Punct(Punctuator::LBracket) => parse_array_literal(p, fuel - 1),
        TokenKind::Punct(Punctuator::LBrace) => parse_object_literal(p, fuel - 1),
        TokenKind::Keyword(Keyword::Function) => {
            p.advance();
            let ghost prog_after_fn = p.prog@;
            let res = parse_function_expr_after_kw(p, fuel - 1, sp, false);
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_fn, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Async) => {
            proof {
                if p.pos + 1 >= p.tokens@.len() {
                    assert(p.pos as int == p.tokens@.len() - 1);
                    assert(p.tokens@[p.pos as int] == p.tokens@.last());
                    assert(false);
                }
            }
            if is_kw(&p.tokens[p.pos + 1], Keyword::Function)
                && !p.tokens[p.pos + 1].preceded_by_line_terminator
            {
                p.advance(); // consume `async`
                p.advance(); // consume `function`
                let ghost prog_after_kw = p.prog@;
                let res = parse_function_expr_after_kw(p, fuel - 1, sp, true);
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                }
                res
            } else {
                match parse_ident(p) {
                    ParseStep::Ok(id) => p.emit_expr(ExprKind::Ident(id), sp, false),
                    ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
                    ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
                }
            }
        },
        TokenKind::Keyword(Keyword::Class) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::ClassSyntax,
                span: sp,
            })
        },
        TokenKind::Keyword(Keyword::Super) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::SuperExpression,
                span: sp,
            })
        },
        TokenKind::Keyword(Keyword::Import) => {
            proof {
                if p.pos + 1 >= p.tokens@.len() {
                    assert(p.pos as int == p.tokens@.len() - 1);
                    assert(p.tokens@[p.pos as int] == p.tokens@.last());
                    assert(false);
                }
                lemma_arena_refl(p.prog@);
            }
            if is_punct(&p.tokens[p.pos + 1], Punctuator::LParen) {
                ParseStep::Unsupported(UnsupportedSyntax {
                    kind: UnsupportedSyntaxKind::DynamicImport,
                    span: sp,
                })
            } else {
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::ModuleDeclarationInScript,
                    span: sp,
                })
            }
        },
        TokenKind::Punct(Punctuator::Slash) | TokenKind::Punct(Punctuator::SlashEq) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            if has_closing_slash_on_same_line(p.tokens, p.pos) {
                ParseStep::Unsupported(UnsupportedSyntax {
                    kind: UnsupportedSyntaxKind::RegExpLiteral,
                    span: sp,
                })
            } else {
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedToken,
                    span: sp,
                })
            }
        },
        TokenKind::Eof => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedEof,
                span: sp,
            })
        },
        _ => match parse_ident(p) {
            ParseStep::Ok(id) => p.emit_expr(ExprKind::Ident(id), sp, false),
            ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
            ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
        },
    }
}

/// Parses `MemberExpression` / `NewExpression` (`new.target`, `new MemberExpression Arguments?`,
/// `PrimaryExpression (. ident | [ expr ])*`).
/// Used both as the base of `LeftHandSideExpression` and inside `new <callee>` (where `?.` is forbidden!).
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_member_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    inside_new_callee: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => {
                old(p).pos < final(p).pos
                    && id.0 < final(p).prog.exprs@.len()
                    && (inside_new_callee ==> !final(p).prog.exprs@[id.0 as int].in_optional_chain)
            },
            _ => true,
        },
    decreases fuel, 2nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }

    let mut cur_id: ExprId = if is_kw(&p.tokens[p.pos], Keyword::New) {
        p.advance(); // consume `new`
        if is_punct(&p.tokens[p.pos], Punctuator::Dot) {
            p.advance(); // consume `.`
            let is_unescaped_target = match &p.tokens[p.pos].kind {
                TokenKind::Ident { name, has_escape: false } => {
                    eq_ascii_6(name.as_slice(), 0x74, 0x61, 0x72, 0x67, 0x65, 0x74)
                },
                _ => false,
            };
            if !is_unescaped_target {
                let err_sp = p.cur_span();
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedToken,
                    span: err_sp,
                });
            }
            let tgt_sp = p.cur_span();
            p.advance(); // consume `target`
            match p.emit_expr(
                ExprKind::NewTarget,
                Span { start: start_sp.start, end: tgt_sp.end },
                false,
            ) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            let ghost prog_after_new = p.prog@;
            let callee = match parse_member_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_new, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_new, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_callee = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_new, prog_after_callee);
            }
            if is_punct(&p.tokens[p.pos], Punctuator::OptionalChain) {
                let oc_sp = p.cur_span();
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::NewOnOptionalChain,
                    span: oc_sp,
                });
            }
            let (args, end_sp) = if is_punct(&p.tokens[p.pos], Punctuator::LParen) {
                match parse_call_args(p, fuel - 1) {
                    ParseStep::Ok(t) => {
                        proof {
                            lemma_arena_expr_preserved(prog_after_callee, p.prog@, callee);
                            lemma_arena_trans(old(p).prog@, prog_after_callee, p.prog@);
                        }
                        t
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_callee, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_callee, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                }
            } else {
                let c_sp = p.prog.exprs[callee.0].span;
                let empty: Vec<CallArg> = Vec::new();
                (empty, c_sp)
            };
            let ghost prog_before_emit = p.prog@;
            match p.emit_expr(
                ExprKind::New { callee, args },
                Span { start: start_sp.start, end: end_sp.end },
                false,
            ) {
                ParseStep::Ok(id) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                    }
                    id
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        }
    } else {
        let base = match parse_primary_expr(p, fuel) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
        };
        if inside_new_callee && p.prog.exprs[base.0].in_optional_chain {
            let err_sp = p.prog.exprs[base.0].span;
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::NewOnOptionalChain,
                span: err_sp,
            });
        }
        base
    };

    // Suffix loop for `.ident` and `[expr]` (and rejecting tagged templates; `(` is handled by `new` or outer `parse_lhs_expr`)
    loop
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            cur_id.0 < p.prog.exprs@.len(),
            inside_new_callee ==> !p.prog.exprs@[cur_id.0 as int].in_optional_chain,
        decreases p.tokens@.len() - p.pos,
    {
        match &p.tokens[p.pos].kind {
            TokenKind::Punct(Punctuator::Dot) => {
                p.advance();
                let (prop_name, end_sp) = match parse_identifier_name(p) {
                    ParseStep::Ok(t) => t,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let obj_sp = p.prog.exprs[cur_id.0].span;
                let obj_opt = p.prog.exprs[cur_id.0].in_optional_chain;
                let ghost prog_before_emit = p.prog@;
                cur_id = match p.emit_expr(
                    ExprKind::Member {
                        object: cur_id,
                        property: prop_name,
                        optional: false,
                    },
                    Span { start: obj_sp.start, end: end_sp.end },
                    obj_opt,
                ) {
                    ParseStep::Ok(id) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        id
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
            },
            TokenKind::Punct(Punctuator::LBracket) => {
                p.advance();
                let ghost prog_before_idx = p.prog@;
                let idx_id = match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                proof {
                    lemma_arena_expr_preserved(prog_before_idx, p.prog@, cur_id);
                    lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                }
                let end_sp = match p.expect_punct(Punctuator::RBracket) {
                    ParseStep::Ok(s) => s,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let obj_sp = p.prog.exprs[cur_id.0].span;
                let obj_opt = p.prog.exprs[cur_id.0].in_optional_chain;
                let ghost prog_before_emit = p.prog@;
                cur_id = match p.emit_expr(
                    ExprKind::ComputedMember {
                        object: cur_id,
                        index: idx_id,
                        optional: false,
                    },
                    Span { start: obj_sp.start, end: end_sp.end },
                    obj_opt,
                ) {
                    ParseStep::Ok(id) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        id
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
            },
            TokenKind::NoSubTemplate { .. } => {
                let tsp = p.cur_span();
                if p.prog.exprs[cur_id.0].in_optional_chain {
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnexpectedToken,
                        span: tsp,
                    });
                }
                return ParseStep::Unsupported(UnsupportedSyntax {
                    kind: UnsupportedSyntaxKind::TaggedTemplate,
                    span: tsp,
                });
            },
            TokenKind::Punct(Punctuator::OptionalChain) if inside_new_callee => {
                let oc_sp = p.cur_span();
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::NewOnOptionalChain,
                    span: oc_sp,
                });
            },
            _ => {
                return ParseStep::Ok(cur_id);
            },
        }
    }
}

/// Parses `LeftHandSideExpression` (`MemberExpression` + call `(args)`, `.ident`, `[expr]`,
/// and optional chaining `?.ident`, `?.[expr]`, `?.(args)`).
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_lhs_expr<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 3nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    let mut cur_id = match parse_member_expr(p, fuel, false) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    loop
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            cur_id.0 < p.prog.exprs@.len(),
        decreases p.tokens@.len() - p.pos,
    {
        match &p.tokens[p.pos].kind {
            TokenKind::Punct(Punctuator::LParen) => {
                let ghost prog_before_args = p.prog@;
                let (args, end_sp) = match parse_call_args(p, fuel - 1) {
                    ParseStep::Ok(t) => t,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                proof {
                    lemma_arena_expr_preserved(prog_before_args, p.prog@, cur_id);
                    lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                }
                let obj_sp = p.prog.exprs[cur_id.0].span;
                let obj_opt = p.prog.exprs[cur_id.0].in_optional_chain;
                let ghost prog_before_emit = p.prog@;
                cur_id = match p.emit_expr(
                    ExprKind::Call { callee: cur_id, args, optional: false },
                    Span { start: obj_sp.start, end: end_sp.end },
                    obj_opt,
                ) {
                    ParseStep::Ok(id) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        id
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
            },
            TokenKind::Punct(Punctuator::Dot) => {
                p.advance();
                let (prop_name, end_sp) = match parse_identifier_name(p) {
                    ParseStep::Ok(t) => t,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let obj_sp = p.prog.exprs[cur_id.0].span;
                let obj_opt = p.prog.exprs[cur_id.0].in_optional_chain;
                let ghost prog_before_emit = p.prog@;
                cur_id = match p.emit_expr(
                    ExprKind::Member {
                        object: cur_id,
                        property: prop_name,
                        optional: false,
                    },
                    Span { start: obj_sp.start, end: end_sp.end },
                    obj_opt,
                ) {
                    ParseStep::Ok(id) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        id
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
            },
            TokenKind::Punct(Punctuator::LBracket) => {
                p.advance();
                let ghost prog_before_idx = p.prog@;
                let idx_id = match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                proof {
                    lemma_arena_expr_preserved(prog_before_idx, p.prog@, cur_id);
                    lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                }
                let end_sp = match p.expect_punct(Punctuator::RBracket) {
                    ParseStep::Ok(s) => s,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let obj_sp = p.prog.exprs[cur_id.0].span;
                let obj_opt = p.prog.exprs[cur_id.0].in_optional_chain;
                let ghost prog_before_emit = p.prog@;
                cur_id = match p.emit_expr(
                    ExprKind::ComputedMember {
                        object: cur_id,
                        index: idx_id,
                        optional: false,
                    },
                    Span { start: obj_sp.start, end: end_sp.end },
                    obj_opt,
                ) {
                    ParseStep::Ok(id) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        id
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
            },
            TokenKind::Punct(Punctuator::OptionalChain) => {
                p.advance(); // consume `?.`
                let obj_sp = p.prog.exprs[cur_id.0].span;
                if is_punct(&p.tokens[p.pos], Punctuator::LParen) {
                    let ghost prog_before_args = p.prog@;
                    let (args, end_sp) = match parse_call_args(p, fuel - 1) {
                        ParseStep::Ok(t) => t,
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                    proof {
                        lemma_arena_expr_preserved(prog_before_args, p.prog@, cur_id);
                        lemma_arena_trans(old(p).prog@, prog_before_args, p.prog@);
                    }
                    let ghost prog_before_emit = p.prog@;
                    cur_id = match p.emit_expr(
                        ExprKind::Call { callee: cur_id, args, optional: true },
                        Span { start: obj_sp.start, end: end_sp.end },
                        true,
                    ) {
                        ParseStep::Ok(id) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            id
                        },
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                } else if is_punct(&p.tokens[p.pos], Punctuator::LBracket) {
                    p.advance();
                    let ghost prog_before_idx = p.prog@;
                    let idx_id = match parse_expr(p, fuel - 1, true) {
                        ParseStep::Ok(id) => id,
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                    proof {
                        lemma_arena_expr_preserved(prog_before_idx, p.prog@, cur_id);
                        lemma_arena_trans(old(p).prog@, prog_before_idx, p.prog@);
                    }
                    let end_sp = match p.expect_punct(Punctuator::RBracket) {
                        ParseStep::Ok(s) => s,
                        ParseStep::SyntaxError(e) => {
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            return ParseStep::Unsupported(u);
                        },
                    };
                    let ghost prog_before_emit = p.prog@;
                    cur_id = match p.emit_expr(
                        ExprKind::ComputedMember {
                            object: cur_id,
                            index: idx_id,
                            optional: true,
                        },
                        Span { start: obj_sp.start, end: end_sp.end },
                        true,
                    ) {
                        ParseStep::Ok(id) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            id
                        },
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                } else if let TokenKind::NoSubTemplate { .. } = &p.tokens[p.pos].kind {
                    // Tagged template inside optional chain is early SyntaxError in ECMA-262 §13.3.11
                    let tsp = p.cur_span();
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnexpectedToken,
                        span: tsp,
                    });
                } else {
                    let (prop_name, end_sp) = match parse_identifier_name(p) {
                        ParseStep::Ok(t) => t,
                        ParseStep::SyntaxError(e) => {
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            return ParseStep::Unsupported(u);
                        },
                    };
                    let ghost prog_before_emit = p.prog@;
                    cur_id = match p.emit_expr(
                        ExprKind::Member {
                            object: cur_id,
                            property: prop_name,
                            optional: true,
                        },
                        Span { start: obj_sp.start, end: end_sp.end },
                        true,
                    ) {
                        ParseStep::Ok(id) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            id
                        },
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                }
            },
            TokenKind::NoSubTemplate { .. } => {
                let tsp = p.cur_span();
                if p.prog.exprs[cur_id.0].in_optional_chain {
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnexpectedToken,
                        span: tsp,
                    });
                }
                return ParseStep::Unsupported(UnsupportedSyntax {
                    kind: UnsupportedSyntaxKind::TaggedTemplate,
                    span: tsp,
                });
            },
            _ => {
                return ParseStep::Ok(cur_id);
            },
        }
    }
}

/// Parses `UpdateExpression` (`++UnaryExpression`, `--UnaryExpression`,
/// `LeftHandSideExpression [no LineTerminator here] ++/--`).
fn parse_update_expr<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 4nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }

    let prefix_op = match &p.tokens[p.pos].kind {
        TokenKind::Punct(Punctuator::PlusPlus) => Some(UpdateOp::Inc),
        TokenKind::Punct(Punctuator::MinusMinus) => Some(UpdateOp::Dec),
        _ => None,
    };

    if let Some(op) = prefix_op {
        p.advance();
        let ghost prog_after_op = p.prog@;
        let arg = match parse_unary_expr(p, fuel - 1) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
        }
        let arg_sp = p.prog.exprs[arg.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Update { op, prefix: true, arg },
            Span { start: start_sp.start, end: arg_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    let lhs = match parse_lhs_expr(p, fuel) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    // Restricted production: `LeftHandSideExpression [no LineTerminator here] ++ / --`
    if !p.tokens[p.pos].preceded_by_line_terminator {
        let post_op = match &p.tokens[p.pos].kind {
            TokenKind::Punct(Punctuator::PlusPlus) => Some(UpdateOp::Inc),
            TokenKind::Punct(Punctuator::MinusMinus) => Some(UpdateOp::Dec),
            _ => None,
        };
        if let Some(op) = post_op {
            let op_sp = p.cur_span();
            p.advance();
            let lhs_sp = p.prog.exprs[lhs.0].span;
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_expr(
                ExprKind::Update { op, prefix: false, arg: lhs },
                Span { start: lhs_sp.start, end: op_sp.end },
                false,
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            return res;
        }
    }

    ParseStep::Ok(lhs)
}

/// Parses `UnaryExpression` (`delete`, `void`, `typeof`, `+`, `-`, `~`, `!`, `await` when `in_async`,
/// or `UpdateExpression`).
fn parse_unary_expr<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 5nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }

    let unary_op = match &p.tokens[p.pos].kind {
        TokenKind::Keyword(Keyword::Delete) => Some(UnaryOp::Delete),
        TokenKind::Keyword(Keyword::Void) => Some(UnaryOp::Void),
        TokenKind::Keyword(Keyword::Typeof) => Some(UnaryOp::Typeof),
        TokenKind::Punct(Punctuator::Plus) => Some(UnaryOp::Plus),
        TokenKind::Punct(Punctuator::Minus) => Some(UnaryOp::Minus),
        TokenKind::Punct(Punctuator::Tilde) => Some(UnaryOp::BitNot),
        TokenKind::Punct(Punctuator::Bang) => Some(UnaryOp::Not),
        _ => None,
    };

    if let Some(op) = unary_op {
        p.advance();
        let ghost prog_after_op = p.prog@;
        let arg = match parse_unary_expr(p, fuel - 1) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_op, p.prog@);
        }
        let arg_sp = p.prog.exprs[arg.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Unary { op, arg },
            Span { start: start_sp.start, end: arg_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    if p.in_async && is_kw(&p.tokens[p.pos], Keyword::Await) {
        p.advance();
        let ghost prog_after_aw = p.prog@;
        let arg = match parse_unary_expr(p, fuel - 1) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_aw, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_aw, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_aw, p.prog@);
        }
        let arg_sp = p.prog.exprs[arg.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Await(arg),
            Span { start: start_sp.start, end: arg_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    parse_update_expr(p, fuel)
}

/// Parses `ExponentiationExpression : UnaryExpression | UpdateExpression ** ExponentiationExpression` (§13.6).
/// Proves `!spec_is_unparen_unary_or_await(exprs[left.0])` whenever `BinOp::Exp` is constructed!
fn parse_exp_expr<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 6nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }

    let left = match parse_unary_expr(p, fuel) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    if is_punct(&p.tokens[p.pos], Punctuator::StarStar) {
        if is_unparen_unary_or_await_exec(&p.prog.exprs[left.0]) {
            let err_sp = p.prog.exprs[left.0].span;
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnaryBeforeExponentiation,
                span: err_sp,
            });
        }
        let ghost prog_after_left = p.prog@;
        p.advance(); // consume `**`
        let right = match parse_exp_expr(p, fuel - 1) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_expr_preserved(prog_after_left, p.prog@, left);
            lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
        }
        let l_sp = p.prog.exprs[left.0].span;
        let r_sp = p.prog.exprs[right.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Binary { op: BinOp::Exp, left, right },
            Span { start: l_sp.start, end: r_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    ParseStep::Ok(left)
}

/// Verified Pratt binary expression parser across all 24 left-associative binary operators,
/// enforcing ECMA-262 §13.13 unparenthesized `??` + `&&`/`||` disambiguation (`grammar_wf`).
#[verifier::spinoff_prover]
fn parse_binary_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    min_bp: u8,
    allow_in: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
        min_bp <= 24,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 7nat, (25nat - (min_bp as nat)),
{
    let mut left = match parse_exp_expr(p, fuel) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    loop
        invariant
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            left.0 < p.prog.exprs@.len(),
            min_bp <= 24,
        decreases p.tokens@.len() - p.pos,
    {
        let op_info = match_binary_op(&p.tokens[p.pos], allow_in);
        let (op, l_bp, r_bp) = match op_info {
            Some(t) => t,
            None => {
                return ParseStep::Ok(left);
            },
        };
        if l_bp < min_bp {
            return ParseStep::Ok(left);
        }
        let op_sp = p.cur_span();
        p.advance(); // consume binary operator
        let ghost prog_before_rhs = p.prog@;
        let right = match parse_binary_expr(p, fuel, r_bp, allow_in) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_expr_preserved(prog_before_rhs, p.prog@, left);
            lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
        }

        // Enforce §13.13 early syntax error: unparenthesized `??` mixed with `&&` or `||`!
        if op == BinOp::Coalesce {
            if is_unparen_logical_and_or_exec(&p.prog.exprs[left.0])
                || is_unparen_logical_and_or_exec(&p.prog.exprs[right.0])
            {
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnparenthesizedNullishAndLogicalMix,
                    span: op_sp,
                });
            }
        } else if op == BinOp::LogicalAnd || op == BinOp::LogicalOr {
            if is_unparen_coalesce_exec(&p.prog.exprs[left.0])
                || is_unparen_coalesce_exec(&p.prog.exprs[right.0])
            {
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnparenthesizedNullishAndLogicalMix,
                    span: op_sp,
                });
            }
        }

        let l_sp = p.prog.exprs[left.0].span;
        let r_sp = p.prog.exprs[right.0].span;
        let ghost prog_before_emit = p.prog@;
        left = match p.emit_expr(
            ExprKind::Binary { op, left, right },
            Span { start: l_sp.start, end: r_sp.end },
            false,
        ) {
            ParseStep::Ok(id) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                id
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
    }
}

/// Parses `ConditionalExpression : ShortCircuitExpression (? AssignmentExpression[+In] : AssignmentExpression[?In])?`.
fn parse_conditional_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_in: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 8nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }

    let cond = match parse_binary_expr(p, fuel, 0, allow_in) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    if is_punct(&p.tokens[p.pos], Punctuator::Question) {
        let ghost prog_after_cond = p.prog@;
        p.advance(); // consume `?`
        let consequent = match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_cond, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_cond, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_cons = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_cond, prog_after_cons);
        }
        match p.expect_punct(Punctuator::Colon) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let alternate = match parse_assignment_expr(p, fuel - 1, allow_in) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_cons, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_cons, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_expr_preserved(prog_after_cond, prog_after_cons, cond);
            lemma_arena_expr_preserved(prog_after_cons, p.prog@, cond);
            lemma_arena_expr_preserved(prog_after_cons, p.prog@, consequent);
            lemma_arena_trans(old(p).prog@, prog_after_cons, p.prog@);
        }
        let c_sp = p.prog.exprs[cond.0].span;
        let a_sp = p.prog.exprs[alternate.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Conditional { cond, consequent, alternate },
            Span { start: c_sp.start, end: a_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    ParseStep::Ok(cond)
}

/// Parses `ConciseBody` of an ArrowFunction after `=>` has already been consumed.
fn parse_arrow_concise_body<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    is_async: bool,
    allow_in: bool,
) -> (res: ParseStep<(ArrowBody, Span)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok((body, _)) => {
                old(p).pos < final(p).pos
                    && match body {
                        ArrowBody::Expr(e) => e.0 < final(p).prog.exprs@.len(),
                        ArrowBody::Block { stmts: b, .. } => {
                            forall|s: int| 0 <= s < b@.len() ==> (#[trigger] b@[s]).0 < final(p).prog.stmts@.len()
                        },
                    }
            },
            _ => true,
        },
    decreases fuel, 8nat, 1nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    if is_punct(&p.tokens[p.pos], Punctuator::LBrace) {
        match parse_function_body(p, fuel - 1, is_async, false) {
            ParseStep::Ok((stmts, has_strict, has_octal, end_sp)) => ParseStep::Ok((
                ArrowBody::Block {
                    stmts,
                    has_use_strict: has_strict,
                    has_directive_octal_escape: has_octal,
                },
                end_sp,
            )),
            ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
            ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
        }
    } else {
        let saved_async = p.in_async;
        let saved_gen = p.in_generator;
        p.in_async = is_async;
        p.in_generator = false;
        let res = parse_assignment_expr(p, fuel - 1, allow_in);
        p.in_async = saved_async;
        p.in_generator = saved_gen;
        match res {
            ParseStep::Ok(eid) => {
                let esp = p.prog.exprs[eid.0].span;
                ParseStep::Ok((ArrowBody::Expr(eid), esp))
            },
            ParseStep::SyntaxError(e) => ParseStep::SyntaxError(e),
            ParseStep::Unsupported(u) => ParseStep::Unsupported(u),
        }
    }
}

fn is_yield_terminator(tok: &Token) -> (r: bool) {
    if tok.preceded_by_line_terminator {
        true
    } else {
        match &tok.kind {
            TokenKind::Punct(Punctuator::Semicolon)
            | TokenKind::Punct(Punctuator::RBrace)
            | TokenKind::Punct(Punctuator::RParen)
            | TokenKind::Punct(Punctuator::RBracket)
            | TokenKind::Punct(Punctuator::Comma)
            | TokenKind::Punct(Punctuator::Colon)
            | TokenKind::Eof => true,
            _ => false,
        }
    }
}

/// Parses `AssignmentExpression` (`YieldExpression`, `ArrowFunction`, `AsyncArrowFunction`,
/// `ConditionalExpression`, or `LeftHandSideExpression AssignmentOp AssignmentExpression`).
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_assignment_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_in: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 9nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }

    // 1. `YieldExpression` inside Generator contexts (§15.5)
    if p.in_generator && is_kw(&p.tokens[p.pos], Keyword::Yield) {
        p.advance(); // consume `yield`
        if is_yield_terminator(&p.tokens[p.pos]) {
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_expr(
                ExprKind::Yield { delegate: false, arg: None },
                start_sp,
                false,
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            return res;
        }
        let delegate = if is_punct(&p.tokens[p.pos], Punctuator::Star) {
            p.advance();
            true
        } else {
            false
        };
        let ghost prog_before_arg = p.prog@;
        let arg = match parse_assignment_expr(p, fuel - 1, allow_in) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_arg, p.prog@);
        }
        let arg_sp = p.prog.exprs[arg.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Yield { delegate, arg: Some(arg) },
            Span { start: start_sp.start, end: arg_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    // 2. Async Arrow Function lookahead:
    //    (a) `async [no LineTerminator here] BindingIdentifier [no LineTerminator here] => ConciseBody`
    //    (b) `async [no LineTerminator here] ( FormalParameters ) [no LineTerminator here] => ConciseBody`
    if is_kw(&p.tokens[p.pos], Keyword::Async) {
        proof {
            if p.pos + 1 >= p.tokens@.len() {
                assert(p.pos as int == p.tokens@.len() - 1);
                assert(p.tokens@[p.pos as int] == p.tokens@.last());
                assert(false);
            }
        }
        if !p.tokens[p.pos + 1].preceded_by_line_terminator {
            if is_punct(&p.tokens[p.pos + 1], Punctuator::LParen) {
                if let Some(rp_idx) = find_matching_rparen(p.tokens, p.pos + 1) {
                    if is_punct(&p.tokens[rp_idx + 1], Punctuator::Arrow) {
                        if p.tokens[rp_idx + 1].preceded_by_line_terminator {
                            let err_sp = p.tokens[rp_idx + 1].span;
                            proof {
                                lemma_arena_refl(p.prog@);
                            }
                            return ParseStep::SyntaxError(SyntaxDiagnostic {
                                kind: DiagnosticKind::LineTerminatorBeforeArrow,
                                span: err_sp,
                            });
                        }
                        p.advance(); // consume `async`
                        let ghost prog_after_async = p.prog@;
                        let cur_gen = p.in_generator;
                        let params = match parse_formal_params(p, fuel - 1, true, cur_gen) {
                            ParseStep::Ok(ps) => ps,
                            ParseStep::SyntaxError(e) => {
                                proof {
                                    lemma_arena_trans(old(p).prog@, prog_after_async, p.prog@);
                                }
                                return ParseStep::SyntaxError(e);
                            },
                            ParseStep::Unsupported(u) => {
                                proof {
                                    lemma_arena_trans(old(p).prog@, prog_after_async, p.prog@);
                                }
                                return ParseStep::Unsupported(u);
                            },
                        };
                        let ghost prog_after_params = p.prog@;
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_async, prog_after_params);
                        }
                        match p.expect_punct(Punctuator::Arrow) {
                            ParseStep::SyntaxError(e) => {
                                return ParseStep::SyntaxError(e);
                            },
                            ParseStep::Unsupported(u) => {
                                return ParseStep::Unsupported(u);
                            },
                            ParseStep::Ok(_) => {},
                        }
                        let (body, end_sp) = match parse_arrow_concise_body(p, fuel, true, allow_in) {
                            ParseStep::Ok(t) => t,
                            ParseStep::SyntaxError(e) => {
                                proof {
                                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                                }
                                return ParseStep::SyntaxError(e);
                            },
                            ParseStep::Unsupported(u) => {
                                proof {
                                    lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                                }
                                return ParseStep::Unsupported(u);
                            },
                        };
                        let ghost prog_before_emit = p.prog@;
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_params, prog_before_emit);
                            assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
                                Some(id) => id.0 < p.prog.exprs@.len(),
                                None => true,
                            } by {
                                assert(match params@[i].default {
                                    Some(id) => id.0 < prog_after_params.exprs.len(),
                                    None => true,
                                });
                            }
                        }
                        let res = p.emit_expr(
                            ExprKind::ArrowFunction { params, body, is_async: true },
                            Span { start: start_sp.start, end: end_sp.end },
                            false,
                        );
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                        }
                        return res;
                    }
                }
            } else if token_can_be_ident(&p.tokens[p.pos + 1], true, p.in_generator) {
                proof {
                    if p.pos + 2 >= p.tokens@.len() {
                        assert((p.pos + 1) as int == p.tokens@.len() - 1);
                        assert(p.tokens@[(p.pos + 1) as int] == p.tokens@.last());
                        assert(false);
                    }
                }
                if is_punct(&p.tokens[p.pos + 2], Punctuator::Arrow) {
                    if p.tokens[p.pos + 2].preceded_by_line_terminator {
                        let err_sp = p.tokens[p.pos + 2].span;
                        proof {
                            lemma_arena_refl(p.prog@);
                        }
                        return ParseStep::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::LineTerminatorBeforeArrow,
                            span: err_sp,
                        });
                    }
                    p.advance(); // consume `async`
                    let single_ident = match parse_ident_with_flags(p, true, p.in_generator) {
                        ParseStep::Ok(id) => id,
                        ParseStep::SyntaxError(e) => {
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            return ParseStep::Unsupported(u);
                        },
                    };
                    p.advance(); // consume `=>`
                    let mut params: Vec<Param> = Vec::new();
                    params.push(Param { name: single_ident, default: None, is_rest: false });
                    let ghost prog_before_body = p.prog@;
                    let (body, end_sp) = match parse_arrow_concise_body(p, fuel, true, allow_in) {
                        ParseStep::Ok(t) => t,
                        ParseStep::SyntaxError(e) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_body, p.prog@);
                            }
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            proof {
                                lemma_arena_trans(old(p).prog@, prog_before_body, p.prog@);
                            }
                            return ParseStep::Unsupported(u);
                        },
                    };
                    let ghost prog_before_emit = p.prog@;
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_body, prog_before_emit);
                        assert(params@.len() == 1);
                        assert(!params@[0].is_rest && params@[0].default is None);
                    }
                    let res = p.emit_expr(
                        ExprKind::ArrowFunction { params, body, is_async: true },
                        Span { start: start_sp.start, end: end_sp.end },
                        false,
                    );
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                    }
                    return res;
                }
            }
        }
    }

    // 3. Sync Arrow Function lookahead:
    //    (a) `BindingIdentifier [no LineTerminator here] => ConciseBody`
    if token_can_be_ident(&p.tokens[p.pos], p.in_async, p.in_generator) {
        proof {
            if p.pos + 1 >= p.tokens@.len() {
                assert(p.pos as int == p.tokens@.len() - 1);
                assert(p.tokens@[p.pos as int] == p.tokens@.last());
                assert(false);
            }
        }
        if is_punct(&p.tokens[p.pos + 1], Punctuator::Arrow) {
            if p.tokens[p.pos + 1].preceded_by_line_terminator {
                let err_sp = p.tokens[p.pos + 1].span;
                proof {
                    lemma_arena_refl(p.prog@);
                }
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::LineTerminatorBeforeArrow,
                    span: err_sp,
                });
            }
            let single_ident = match parse_ident(p) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
            };
            p.advance(); // consume `=>`
            let mut params: Vec<Param> = Vec::new();
            params.push(Param { name: single_ident, default: None, is_rest: false });
            let ghost prog_before_body = p.prog@;
            let (body, end_sp) = match parse_arrow_concise_body(p, fuel, false, allow_in) {
                ParseStep::Ok(t) => t,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_body, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_body, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_before_emit = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_body, prog_before_emit);
                assert(params@.len() == 1);
                assert(!params@[0].is_rest && params@[0].default is None);
            }
            let res = p.emit_expr(
                ExprKind::ArrowFunction { params, body, is_async: false },
                Span { start: start_sp.start, end: end_sp.end },
                false,
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            return res;
        }
    }

    //    (b) `( FormalParameters ) [no LineTerminator here] => ConciseBody`
    if is_punct(&p.tokens[p.pos], Punctuator::LParen) {
        if let Some(rp_idx) = find_matching_rparen(p.tokens, p.pos) {
            if is_punct(&p.tokens[rp_idx + 1], Punctuator::Arrow) {
                if p.tokens[rp_idx + 1].preceded_by_line_terminator {
                    let err_sp = p.tokens[rp_idx + 1].span;
                    proof {
                        lemma_arena_refl(p.prog@);
                    }
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::LineTerminatorBeforeArrow,
                        span: err_sp,
                    });
                }
                let cur_async = p.in_async;
                let cur_gen = p.in_generator;
                let params = match parse_formal_params(p, fuel - 1, cur_async, cur_gen) {
                    ParseStep::Ok(ps) => ps,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let ghost prog_after_params = p.prog@;
                match p.expect_punct(Punctuator::Arrow) {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(_) => {},
                }
                let (body, end_sp) = match parse_arrow_concise_body(p, fuel, false, allow_in) {
                    ParseStep::Ok(t) => t,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                let ghost prog_before_emit = p.prog@;
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_params, prog_before_emit);
                    assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    } by {
                        assert(match params@[i].default {
                            Some(id) => id.0 < prog_after_params.exprs.len(),
                            None => true,
                        });
                    }
                }
                let res = p.emit_expr(
                    ExprKind::ArrowFunction { params, body, is_async: false },
                    Span { start: start_sp.start, end: end_sp.end },
                    false,
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                return res;
            }
        }
    }

    // 4. Conditional or Assignment (`lhs = rhs`, `lhs += rhs`, ...)
    parse_assignment_or_cond_expr(p, fuel, allow_in)
}

#[verifier::spinoff_prover]
fn parse_assignment_or_cond_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_in: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
        fuel >= 1,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 8nat, 2nat,
{
    let left = match parse_conditional_expr(p, fuel, allow_in) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    if let Some(aop) = match_assign_op(&p.tokens[p.pos]) {
        if aop == AssignOp::Assign && is_destructuring_expr_lhs(&p.prog, left) {
            let l_sp = p.prog.exprs[left.0].span;
            return ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::DestructuringPattern,
                span: l_sp,
            });
        }
        let ghost prog_after_left = p.prog@;
        p.advance(); // consume assignment operator
        let right = match parse_assignment_expr(p, fuel - 1, allow_in) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_expr_preserved(prog_after_left, p.prog@, left);
            lemma_arena_trans(old(p).prog@, prog_after_left, p.prog@);
        }
        let l_sp = p.prog.exprs[left.0].span;
        let r_sp = p.prog.exprs[right.0].span;
        let ghost prog_before_emit = p.prog@;
        let res = p.emit_expr(
            ExprKind::Assign { op: aop, left, right },
            Span { start: l_sp.start, end: r_sp.end },
            false,
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    // Check stray `=>` (e.g., `(1) => 2` or `a + b => c` where LHS wasn't valid formal params!)
    if is_punct(&p.tokens[p.pos], Punctuator::Arrow) {
        let sp = p.cur_span();
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedToken,
            span: sp,
        });
    }

    ParseStep::Ok(left)
}

/// Parses `Expression` (comma-separated `Sequence` of `AssignmentExpression`s).
pub fn parse_expr<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_in: bool,
) -> (res: ParseStep<ExprId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.exprs@.len(),
            _ => true,
        },
    decreases fuel, 10nat, 0nat,
{
    let mut left = match parse_assignment_expr(p, fuel, allow_in) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    while is_punct(&p.tokens[p.pos], Punctuator::Comma)
        invariant
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            left.0 < p.prog.exprs@.len(),
        decreases p.tokens@.len() - p.pos,
    {
        p.advance(); // consume `,`
        let ghost prog_before_rhs = p.prog@;
        let right = match parse_assignment_expr(p, fuel, allow_in) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_expr_preserved(prog_before_rhs, p.prog@, left);
            lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
        }
        let l_sp = p.prog.exprs[left.0].span;
        let r_sp = p.prog.exprs[right.0].span;
        let ghost prog_before_emit = p.prog@;
        left = match p.emit_expr(
            ExprKind::Sequence { left, right },
            Span { start: l_sp.start, end: r_sp.end },
            false,
        ) {
            ParseStep::Ok(id) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                id
            },
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
    }

    ParseStep::Ok(left)
}

// ---------------------------------------------------------------------------------------
// Statement & Declaration Parsers (§14–15)
// ---------------------------------------------------------------------------------------

fn parse_var_decl_list<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    vk: VarDeclKind,
    allow_in: bool,
) -> (res: ParseStep<Vec<VarDeclarator>>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(decls) => {
                old(p).pos < final(p).pos
                    && decls@.len() >= 1
                    && (vk == VarDeclKind::Const ==> forall|k: int|
                        0 <= k < decls@.len() ==> (#[trigger] decls@[k]).init is Some)
                    && (forall|k: int|
                        0 <= k < decls@.len() ==> match (#[trigger] decls@[k]).init {
                            Some(id) => id.0 < final(p).prog.exprs@.len(),
                            None => true,
                        })
            },
            _ => true,
        },
    decreases fuel, 11nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }

    proof {
        lemma_arena_refl(p.prog@);
    }
    let mut decls: Vec<VarDeclarator> = Vec::new();
    loop
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos <= p.pos,
            decls@.len() > 0 ==> old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            vk == VarDeclKind::Const ==> forall|k: int|
                0 <= k < decls@.len() ==> (#[trigger] decls@[k]).init is Some,
            forall|k: int|
                0 <= k < decls@.len() ==> match (#[trigger] decls@[k]).init {
                    Some(id) => id.0 < p.prog.exprs@.len(),
                    None => true,
                },
        decreases p.tokens@.len() - p.pos,
    {
        let ghost prog_before_name = p.prog@;
        let name = match parse_ident(p) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_name, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_name, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };

        let init_opt: Option<ExprId> = if is_punct(&p.tokens[p.pos], Punctuator::Eq) {
            p.advance();
            let ghost prog_before_init = p.prog@;
            match parse_assignment_expr(p, fuel - 1, allow_in) {
                ParseStep::Ok(eid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_init, p.prog@);
                        assert forall|k: int| 0 <= k < decls@.len() implies match (#[trigger] decls@[k]).init {
                            Some(id) => id.0 < p.prog.exprs@.len(),
                            None => true,
                        } by {
                            if let Some(id) = decls@[k].init {
                                assert(id.0 < prog_before_init.exprs.len());
                            }
                        }
                    }
                    Some(eid)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_init, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_init, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            if vk == VarDeclKind::Const {
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::ConstWithoutInitializer,
                    span: name.span,
                });
            }
            None
        };

        let ghost prev_decls = decls@;
        decls.push(VarDeclarator { name, init: init_opt });
        proof {
            if vk == VarDeclKind::Const {
                assert forall|k: int| 0 <= k < decls@.len() implies (#[trigger] decls@[k]).init is Some by {
                    if k < prev_decls.len() {
                        assert(decls@[k] == prev_decls[k]);
                    }
                }
            }
            assert forall|k: int| 0 <= k < decls@.len() implies match (#[trigger] decls@[k]).init {
                Some(id) => id.0 < p.prog.exprs@.len(),
                None => true,
            } by {
                if k < prev_decls.len() {
                    assert(decls@[k] == prev_decls[k]);
                }
            }
        }

        if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
            p.advance();
        } else {
            return ParseStep::Ok(decls);
        }
    }
}

/// Parses `{ StatementList? }` block (without Directive Prologue) starting AT `{`.
fn parse_block_stmts<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
) -> (res: ParseStep<(Vec<StmtId>, Span)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok((stmts, _)) => {
                old(p).pos < final(p).pos
                    && forall|s: int| 0 <= s < stmts@.len() ==> (#[trigger] stmts@[s]).0 < final(p).prog.stmts@.len()
            },
            _ => true,
        },
    decreases fuel, 12nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    match p.expect_punct(Punctuator::LBrace) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let mut stmts: Vec<StmtId> = Vec::new();
    while !is_punct(&p.tokens[p.pos], Punctuator::RBrace)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            forall|s: int| 0 <= s < stmts@.len() ==> (#[trigger] stmts@[s]).0 < p.prog.stmts@.len(),
        decreases p.tokens@.len() - p.pos,
    {
        if p.is_eof() {
            let sp = p.cur_span();
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedEof,
                span: sp,
            });
        }
        let ghost prog_before_s = p.prog@;
        let sid = match parse_stmt_or_decl(p, fuel - 1, true, false) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prev_stmts = stmts@;
        stmts.push(sid);
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
            assert forall|s: int| 0 <= s < stmts@.len() implies (#[trigger] stmts@[s]).0 < p.prog.stmts@.len() by {
                if s < prev_stmts.len() {
                    assert(stmts@[s] == prev_stmts[s]);
                    assert(prev_stmts[s].0 < prog_before_s.stmts.len());
                }
            }
        }
    }
    let end_sp = p.cur_span();
    p.advance(); // consume `}`
    ParseStep::Ok((stmts, end_sp))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_for_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind == TokenKind::Keyword(Keyword::For),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 13nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }
    p.advance(); // consume `for`
    let is_await = if is_kw(&p.tokens[p.pos], Keyword::Await) {
        p.advance();
        true
    } else {
        false
    };
    match p.expect_punct(Punctuator::LParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }

    // Case 1: `for ( ; cond? ; update? ) body`
    if is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
        if is_await {
            let sp = p.cur_span();
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: sp,
            });
        }
        p.advance(); // consume `;`
        let cond_opt: Option<ExprId> =
            if !is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
                let ghost prog_c = p.prog@;
                match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(cid) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                        }
                        Some(cid)
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                }
            } else {
                None
            };
        let ghost prog_after_cond = p.prog@;
        match p.expect_punct(Punctuator::Semicolon) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let upd_opt: Option<ExprId> =
            if !is_punct(&p.tokens[p.pos], Punctuator::RParen) {
                let ghost prog_u = p.prog@;
                match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(uid) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                            if let Some(cid) = cond_opt {
                                assert(cid.0 < prog_after_cond.exprs.len());
                            }
                        }
                        Some(uid)
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                }
            } else {
                None
            };
        let ghost prog_after_upd = p.prog@;
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
            ParseStep::Ok(bid) => bid,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_before_emit = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_upd, prog_before_emit);
            if let Some(cid) = cond_opt {
                assert(cid.0 < prog_after_cond.exprs.len());
            }
            if let Some(uid) = upd_opt {
                assert(uid.0 < prog_after_upd.exprs.len());
            }
        }
        let body_sp = p.prog.stmts[body.0].span;
        let res = p.emit_stmt(
            StmtKind::For {
                init: ForInit::None,
                cond: cond_opt,
                update: upd_opt,
                body,
            },
            Span { start: start_sp.start, end: body_sp.end },
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    // Case 2: `for ( var / let / const ... )`
    let decl_kind_opt: Option<VarDeclKind> = match &p.tokens[p.pos].kind {
        TokenKind::Keyword(Keyword::Var) => Some(VarDeclKind::Var),
        TokenKind::Keyword(Keyword::Const) => Some(VarDeclKind::Const),
        TokenKind::Keyword(Keyword::Let) => {
            if is_let_lexical_decl_at(p.tokens, p.pos) {
                Some(VarDeclKind::Let)
            } else {
                None
            }
        },
        _ => None,
    };

    if let Some(vk) = decl_kind_opt {
        p.advance(); // consume `var` / `let` / `const`
        let ghost prog_c2 = p.prog@;
        let res = parse_for_var_decl_head(p, fuel, start_sp, is_await, vk);
        proof {
            lemma_arena_trans(old(p).prog@, prog_c2, p.prog@);
        }
        return res;
    }

    // Case 3: `for ( Expression[~In] ... )`
    let ghost prog_c3 = p.prog@;
    let res = parse_for_expr_head(p, fuel, start_sp, is_await);
    proof {
        lemma_arena_trans(old(p).prog@, prog_c3, p.prog@);
    }
    res
}


#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_for_var_decl_head<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    start_sp: Span,
    is_await: bool,
    vk: VarDeclKind,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 12nat, 1nat,
{
    proof {
        lemma_arena_refl(p.prog@);
    }
    let first_name = match parse_ident(p) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };

    // `for (var/let/const x in rhs) body`
    if !is_await && is_kw(&p.tokens[p.pos], Keyword::In) {
        p.advance(); // consume `in`
        let ghost prog_before_rhs = p.prog@;
        let rhs = match parse_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_rhs = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_rhs, prog_after_rhs);
        }
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
            ParseStep::Ok(bid) => bid,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_before_emit = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_rhs, prog_before_emit);
        }
        let body_sp = p.prog.stmts[body.0].span;
        let res = p.emit_stmt(
            StmtKind::ForIn {
                lhs: ForInOfLhs::VarDecl { kind: vk, name: first_name },
                rhs,
                body,
            },
            Span { start: start_sp.start, end: body_sp.end },
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    // `for await? (var/let/const x of rhs) body`
    if is_kw(&p.tokens[p.pos], Keyword::Of) {
        p.advance(); // consume `of`
        let ghost prog_before_rhs = p.prog@;
        let rhs = match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_rhs = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_rhs, prog_after_rhs);
        }
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
            ParseStep::Ok(bid) => bid,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_before_emit = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_rhs, prog_before_emit);
        }
        let body_sp = p.prog.stmts[body.0].span;
        let res = p.emit_stmt(
            StmtKind::ForOf {
                lhs: ForInOfLhs::VarDecl { kind: vk, name: first_name },
                rhs,
                is_await,
                body,
            },
            Span { start: start_sp.start, end: body_sp.end },
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    // Standard C-style `for (var/let/const x = init, ... ; cond? ; update?) body`
    if is_await {
        let sp = p.cur_span();
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedToken,
            span: sp,
        });
    }

    let first_init: Option<ExprId> =
        if is_punct(&p.tokens[p.pos], Punctuator::Eq) {
            p.advance();
            let ghost prog_fi = p.prog@;
            match parse_assignment_expr(p, fuel - 1, false) {
                ParseStep::Ok(id) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_fi, p.prog@);
                    }
                    Some(id)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_fi, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_fi, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            if vk == VarDeclKind::Const {
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::ConstWithoutInitializer,
                    span: first_name.span,
                });
            }
            None
        };

    let mut decls: Vec<VarDeclarator> = Vec::new();
    decls.push(VarDeclarator { name: first_name, init: first_init });
    proof {
        assert(decls@.len() == 1);
        if vk == VarDeclKind::Const {
            assert(decls@[0].init is Some);
        }
    }

    if is_punct(&p.tokens[p.pos], Punctuator::Comma) {
        p.advance();
        let ghost prog_before_rest = p.prog@;
        let more = match parse_var_decl_list(p, fuel - 1, vk, false) {
            ParseStep::Ok(m) => m,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rest, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rest, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_rest, p.prog@);
        }
        let mut mi: usize = 0;
        let mn = more.len();
        while mi < mn
            invariant
                mi <= mn,
                mn == more@.len(),
                decls@.len() >= 1,
                vk == VarDeclKind::Const ==> forall|k: int|
                    0 <= k < decls@.len() ==> (#[trigger] decls@[k]).init is Some,
                vk == VarDeclKind::Const ==> forall|k: int|
                    0 <= k < more@.len() ==> (#[trigger] more@[k]).init is Some,
                forall|k: int|
                    0 <= k < decls@.len() ==> match (#[trigger] decls@[k]).init {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    },
                forall|k: int|
                    0 <= k < more@.len() ==> match (#[trigger] more@[k]).init {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    },
            decreases mn - mi,
        {
            let item = VarDeclarator {
                name: Ident {
                    name: clone_u8_slice(more[mi].name.name.as_slice()),
                    has_escape: more[mi].name.has_escape,
                    span: more[mi].name.span,
                },
                init: more[mi].init,
            };
            let ghost prev_d = decls@;
            decls.push(item);
            proof {
                if vk == VarDeclKind::Const {
                    assert forall|k: int| 0 <= k < decls@.len() implies (#[trigger] decls@[k]).init is Some by {
                        if k < prev_d.len() {
                            assert(decls@[k] == prev_d[k]);
                        } else {
                            assert(more@[mi as int].init is Some);
                        }
                    }
                }
                assert forall|k: int| 0 <= k < decls@.len() implies match (#[trigger] decls@[k]).init {
                    Some(id) => id.0 < p.prog.exprs@.len(),
                    None => true,
                } by {
                    if k < prev_d.len() {
                        assert(decls@[k] == prev_d[k]);
                    } else {
                        assert(match more@[mi as int].init {
                            Some(id) => id.0 < p.prog.exprs@.len(),
                            None => true,
                        });
                    }
                }
            }
            mi = mi + 1;
        }
    }

    let ghost prog_after_decls = p.prog@;
    match p.expect_punct(Punctuator::Semicolon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let cond_opt: Option<ExprId> =
        if !is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
            let ghost prog_c = p.prog@;
            match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(cid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    Some(cid)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            None
        };
    let ghost prog_after_cond = p.prog@;
    match p.expect_punct(Punctuator::Semicolon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let upd_opt: Option<ExprId> =
        if !is_punct(&p.tokens[p.pos], Punctuator::RParen) {
            let ghost prog_u = p.prog@;
            match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(uid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    Some(uid)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            None
        };
    let ghost prog_after_upd = p.prog@;
    match p.expect_punct(Punctuator::RParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
        ParseStep::Ok(bid) => bid,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_emit = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_upd, prog_before_emit);
        assert forall|k: int| 0 <= k < decls@.len() implies match (#[trigger] decls@[k]).init {
            Some(id) => id.0 < p.prog.exprs@.len(),
            None => true,
        } by {
            assert(match decls@[k].init {
                Some(id) => id.0 < prog_after_decls.exprs.len(),
                None => true,
            });
            assert(prog_after_decls.exprs.len() <= prog_after_cond.exprs.len());
            assert(prog_after_cond.exprs.len() <= prog_after_upd.exprs.len());
        }
        if let Some(cid) = cond_opt {
            assert(cid.0 < prog_after_cond.exprs.len());
            assert(prog_after_cond.exprs.len() <= prog_after_upd.exprs.len());
        }
        if let Some(uid) = upd_opt {
            assert(uid.0 < prog_after_upd.exprs.len());
        }
    }
    let body_sp = p.prog.stmts[body.0].span;
    let res = p.emit_stmt(
        StmtKind::For {
            init: ForInit::VarDecl { kind: vk, decls },
            cond: cond_opt,
            update: upd_opt,
            body,
        },
        Span { start: start_sp.start, end: body_sp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    return res;
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_for_expr_head<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    start_sp: Span,
    is_await: bool,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 12nat, 2nat,
{
    proof {
        lemma_arena_refl(p.prog@);
    }
    let started_with_let = is_kw(&p.tokens[p.pos], Keyword::Let);
    let started_with_unescaped_async = is_kw(&p.tokens[p.pos], Keyword::Async);
    let expr_start_pos = p.pos;
    let ghost prog_before_lhs = p.prog@;
    let lhs_expr = match parse_expr(p, fuel - 1, false) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_lhs, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_lhs, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let is_bare_async = started_with_unescaped_async && p.pos == expr_start_pos + 1;
    let ghost prog_after_lhs = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_lhs, prog_after_lhs);
    }

    if !is_await && is_kw(&p.tokens[p.pos], Keyword::In) {
        if is_destructuring_expr_lhs(&p.prog, lhs_expr) {
            let l_sp = p.prog.exprs[lhs_expr.0].span;
            return ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::DestructuringPattern,
                span: l_sp,
            });
        }
        p.advance(); // consume `in`
        let ghost prog_before_rhs = p.prog@;
        let rhs = match parse_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_rhs = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_rhs, prog_after_rhs);
        }
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
            ParseStep::Ok(bid) => bid,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_before_emit = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_rhs, prog_before_emit);
            assert(lhs_expr.0 < prog_after_lhs.exprs.len());
            assert(prog_after_lhs.exprs.len() <= prog_after_rhs.exprs.len());
        }
        let body_sp = p.prog.stmts[body.0].span;
        let res = p.emit_stmt(
            StmtKind::ForIn {
                lhs: ForInOfLhs::Expr(lhs_expr),
                rhs,
                body,
            },
            Span { start: start_sp.start, end: body_sp.end },
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    if is_kw(&p.tokens[p.pos], Keyword::Of) {
        if started_with_let || is_bare_async {
            let l_sp = p.prog.exprs[lhs_expr.0].span;
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: l_sp,
            });
        }
        if is_destructuring_expr_lhs(&p.prog, lhs_expr) {
            let l_sp = p.prog.exprs[lhs_expr.0].span;
            return ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::DestructuringPattern,
                span: l_sp,
            });
        }
        p.advance(); // consume `of`
        let ghost prog_before_rhs = p.prog@;
        let rhs = match parse_assignment_expr(p, fuel - 1, true) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_after_rhs = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_rhs, prog_after_rhs);
        }
        match p.expect_punct(Punctuator::RParen) {
            ParseStep::SyntaxError(e) => {
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseStep::Unsupported(u);
            },
            ParseStep::Ok(_) => {},
        }
        let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
            ParseStep::Ok(bid) => bid,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_rhs, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };
        let ghost prog_before_emit = p.prog@;
        proof {
            lemma_arena_trans(old(p).prog@, prog_after_rhs, prog_before_emit);
            assert(lhs_expr.0 < prog_after_lhs.exprs.len());
            assert(prog_after_lhs.exprs.len() <= prog_after_rhs.exprs.len());
        }
        let body_sp = p.prog.stmts[body.0].span;
        let res = p.emit_stmt(
            StmtKind::ForOf {
                lhs: ForInOfLhs::Expr(lhs_expr),
                rhs,
                is_await,
                body,
            },
            Span { start: start_sp.start, end: body_sp.end },
        );
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
        }
        return res;
    }

    if is_await {
        let sp = p.cur_span();
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedToken,
            span: sp,
        });
    }

    match p.expect_punct(Punctuator::Semicolon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let cond_opt: Option<ExprId> =
        if !is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
            let ghost prog_c = p.prog@;
            match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(cid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    Some(cid)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            None
        };
    let ghost prog_after_cond = p.prog@;
    match p.expect_punct(Punctuator::Semicolon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let upd_opt: Option<ExprId> =
        if !is_punct(&p.tokens[p.pos], Punctuator::RParen) {
            let ghost prog_u = p.prog@;
            match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(uid) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    Some(uid)
                },
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_u, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            }
        } else {
            None
        };
    let ghost prog_after_upd = p.prog@;
    match p.expect_punct(Punctuator::RParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
        ParseStep::Ok(bid) => bid,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_upd, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_emit = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_upd, prog_before_emit);
        assert(lhs_expr.0 < prog_after_lhs.exprs.len());
        assert(prog_after_lhs.exprs.len() <= prog_after_cond.exprs.len());
        assert(prog_after_cond.exprs.len() <= prog_after_upd.exprs.len());
        if let Some(cid) = cond_opt {
            assert(cid.0 < prog_after_cond.exprs.len());
        }
        if let Some(uid) = upd_opt {
            assert(uid.0 < prog_after_upd.exprs.len());
        }
    }
    let body_sp = p.prog.stmts[body.0].span;
    let res = p.emit_stmt(
        StmtKind::For {
            init: ForInit::Expr(lhs_expr),
            cond: cond_opt,
            update: upd_opt,
            body,
        },
        Span { start: start_sp.start, end: body_sp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

#[verifier::spinoff_prover]
fn parse_switch_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind == TokenKind::Keyword(Keyword::Switch),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 13nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }
    p.advance(); // consume `switch`
    match p.expect_punct(Punctuator::LParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let ghost prog_before_disc = p.prog@;
    let discriminant = match parse_expr(p, fuel - 1, true) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_disc, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_disc, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_disc, p.prog@);
    }
    match p.expect_punct(Punctuator::RParen) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    match p.expect_punct(Punctuator::LBrace) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }

    let mut cases: Vec<SwitchCase> = Vec::new();
    let mut seen_default = false;
    while !is_punct(&p.tokens[p.pos], Punctuator::RBrace)
        invariant
            fuel >= 1,
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos < p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.strict == old(p).strict,
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            discriminant.0 < p.prog.exprs@.len(),
            spec_count_default_cases(cases@) == (if seen_default { 1nat } else { 0nat }),
            forall|k: int|
                0 <= k < cases@.len() ==> ((match (#[trigger] cases@[k]).test {
                    Some(id) => id.0 < p.prog.exprs@.len(),
                    None => true,
                }) && forall|s: int|
                    0 <= s < cases@[k].consequent@.len()
                        ==> (#[trigger] cases@[k].consequent@[s]).0 < p.prog.stmts@.len()),
        decreases p.tokens@.len() - p.pos,
    {
        let ghost iter_start_pos = p.pos;
        let test_opt: Option<ExprId> =
            if is_kw(&p.tokens[p.pos], Keyword::Case) {
                p.advance(); // consume `case`
                let ghost prog_before_t = p.prog@;
                let tid = match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_t, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_t, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_t, p.prog@);
                    assert forall|k: int| 0 <= k < cases@.len() implies ((match (#[trigger] cases@[k]).test {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    }) && forall|s: int|
                        0 <= s < cases@[k].consequent@.len()
                            ==> (#[trigger] cases@[k].consequent@[s]).0 < p.prog.stmts@.len()) by {
                        if let Some(id) = cases@[k].test {
                            assert(id.0 < prog_before_t.exprs.len());
                        }
                        assert forall|s: int| 0 <= s < cases@[k].consequent@.len() implies (
                            #[trigger] cases@[k].consequent@[s]
                        ).0 < p.prog.stmts@.len() by {
                            assert(cases@[k].consequent@[s].0 < prog_before_t.stmts.len());
                        }
                    }
                }
                match p.expect_punct(Punctuator::Colon) {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(_) => {},
                }
                Some(tid)
            } else if is_kw(&p.tokens[p.pos], Keyword::Default) {
                let def_sp = p.cur_span();
                if seen_default {
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::MultipleDefaultInSwitch,
                        span: def_sp,
                    });
                }
                p.advance(); // consume `default`
                match p.expect_punct(Punctuator::Colon) {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(_) => {},
                }
                seen_default = true;
                None
            } else {
                let sp = p.cur_span();
                let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
                return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
            };

        let mut cons: Vec<StmtId> = Vec::new();
        while !is_punct(&p.tokens[p.pos], Punctuator::RBrace)
            && !is_kw(&p.tokens[p.pos], Keyword::Case)
            && !is_kw(&p.tokens[p.pos], Keyword::Default)
            invariant
                fuel >= 1,
                p.wf(),
                p.tokens@ == old(p).tokens@,
                old(p).pos < iter_start_pos,
                iter_start_pos < p.pos,
                arena_grew(old(p).prog@, p.prog@),
                p.strict == old(p).strict,
                p.in_async == old(p).in_async,
                p.in_generator == old(p).in_generator,
                discriminant.0 < p.prog.exprs@.len(),
                match test_opt {
                    Some(id) => id.0 < p.prog.exprs@.len(),
                    None => true,
                },
                forall|s: int| 0 <= s < cons@.len() ==> (#[trigger] cons@[s]).0 < p.prog.stmts@.len(),
                forall|k: int|
                    0 <= k < cases@.len() ==> ((match (#[trigger] cases@[k]).test {
                        Some(id) => id.0 < p.prog.exprs@.len(),
                        None => true,
                    }) && forall|s: int|
                        0 <= s < cases@[k].consequent@.len()
                            ==> (#[trigger] cases@[k].consequent@[s]).0 < p.prog.stmts@.len()),
            decreases p.tokens@.len() - p.pos,
        {
            if p.is_eof() {
                let sp = p.cur_span();
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::UnexpectedEof,
                    span: sp,
                });
            }
            let ghost prog_before_cs = p.prog@;
            let sid = match parse_stmt_or_decl(p, fuel - 1, true, false) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_cs, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_cs, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prev_cons = cons@;
            cons.push(sid);
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_cs, p.prog@);
                assert forall|s: int| 0 <= s < cons@.len() implies (#[trigger] cons@[s]).0 < p.prog.stmts@.len() by {
                    if s < prev_cons.len() {
                        assert(cons@[s] == prev_cons[s]);
                        assert(prev_cons[s].0 < prog_before_cs.stmts.len());
                    }
                }
                assert forall|k: int| 0 <= k < cases@.len() implies ((match (#[trigger] cases@[k]).test {
                    Some(id) => id.0 < p.prog.exprs@.len(),
                    None => true,
                }) && forall|s: int|
                    0 <= s < cases@[k].consequent@.len()
                        ==> (#[trigger] cases@[k].consequent@[s]).0 < p.prog.stmts@.len()) by {
                    if let Some(id) = cases@[k].test {
                        assert(id.0 < prog_before_cs.exprs.len());
                    }
                    assert forall|s: int| 0 <= s < cases@[k].consequent@.len() implies (
                        #[trigger] cases@[k].consequent@[s]
                    ).0 < p.prog.stmts@.len() by {
                        assert(cases@[k].consequent@[s].0 < prog_before_cs.stmts.len());
                    }
                }
            }
        }

        let new_case = SwitchCase { test: test_opt, consequent: cons };
        let ghost prev_cases = cases@;
        let ghost g_case = new_case;
        cases.push(new_case);
        proof {
            assert(cases@.drop_last() =~= prev_cases);
            assert(cases@.last() == g_case);
            assert forall|k: int| 0 <= k < cases@.len() implies ((match (#[trigger] cases@[k]).test {
                Some(id) => id.0 < p.prog.exprs@.len(),
                None => true,
            }) && forall|s: int|
                0 <= s < cases@[k].consequent@.len()
                    ==> (#[trigger] cases@[k].consequent@[s]).0 < p.prog.stmts@.len()) by {
                if k < prev_cases.len() {
                    assert(cases@[k] == prev_cases[k]);
                }
            }
        }
    }

    let end_sp = p.cur_span();
    p.advance(); // consume `}`
    let ghost prog_before_emit = p.prog@;
    let res = p.emit_stmt(
        StmtKind::Switch { discriminant, cases },
        Span { start: start_sp.start, end: end_sp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

fn parse_try_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        old(p).tokens@[old(p).pos as int].kind == TokenKind::Keyword(Keyword::Try),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 13nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }
    p.advance(); // consume `try`
    let ghost prog_before_blk = p.prog@;
    let (block, mut last_sp) = match parse_block_stmts(p, fuel - 1) {
        ParseStep::Ok(t) => t,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_blk, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_blk, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_after_blk = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_blk, prog_after_blk);
    }

    let catch_clause: Option<CatchClause> =
        if is_kw(&p.tokens[p.pos], Keyword::Catch) {
            p.advance(); // consume `catch`
            let param_opt: Option<Ident> =
                if is_punct(&p.tokens[p.pos], Punctuator::LParen) {
                    p.advance();
                    let pid = match parse_ident(p) {
                        ParseStep::Ok(id) => id,
                        ParseStep::SyntaxError(e) => {
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            return ParseStep::Unsupported(u);
                        },
                    };
                    match p.expect_punct(Punctuator::RParen) {
                        ParseStep::SyntaxError(e) => {
                            return ParseStep::SyntaxError(e);
                        },
                        ParseStep::Unsupported(u) => {
                            return ParseStep::Unsupported(u);
                        },
                        ParseStep::Ok(_) => {},
                    }
                    Some(pid)
                } else {
                    None
                };
            let ghost prog_before_cb = p.prog@;
            let (cbody, csp) = match parse_block_stmts(p, fuel - 1) {
                ParseStep::Ok(t) => t,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_cb, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_cb, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_cb, p.prog@);
            }
            last_sp = csp;
            Some(CatchClause { param: param_opt, body: cbody })
        } else {
            None
        };
    let ghost prog_after_catch = p.prog@;

    let finally_block: Option<Vec<StmtId>> =
        if is_kw(&p.tokens[p.pos], Keyword::Finally) {
            p.advance();
            let ghost prog_before_fb = p.prog@;
            let (fbody, fsp) = match parse_block_stmts(p, fuel - 1) {
                ParseStep::Ok(t) => t,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_fb, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_fb, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_fb, p.prog@);
            }
            last_sp = fsp;
            Some(fbody)
        } else {
            None
        };

    if catch_clause.is_none() && finally_block.is_none() {
        let sp = p.cur_span();
        return ParseStep::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::TryWithoutCatchOrFinally,
            span: sp,
        });
    }

    let ghost prog_before_emit = p.prog@;
    proof {
        assert(prog_after_blk.stmts.len() <= prog_after_catch.stmts.len());
        assert(prog_after_catch.stmts.len() <= prog_before_emit.stmts.len());
        assert forall|s: int| 0 <= s < block@.len() implies (#[trigger] block@[s]).0 < p.prog.stmts@.len() by {
            assert(block@[s].0 < prog_after_blk.stmts.len());
        }
        if let Some(cc) = &catch_clause {
            assert forall|s: int| 0 <= s < cc.body@.len() implies (#[trigger] cc.body@[s]).0 < p.prog.stmts@.len() by {
                assert(cc.body@[s].0 < prog_after_catch.stmts.len());
            }
        }
    }
    let res = p.emit_stmt(
        StmtKind::Try { block, catch_clause, finally_block },
        Span { start: start_sp.start, end: last_sp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

fn parse_function_decl_after_kw<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    start_sp: Span,
    is_async: bool,
    allow_gen: bool,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 21nat, 0nat,
{
    if fuel == 0 {
        let sp = p.cur_span();
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: sp,
        });
    }
    proof {
        lemma_arena_refl(p.prog@);
    }
    let is_gen = if is_punct(&p.tokens[p.pos], Punctuator::Star) {
        if !allow_gen {
            let sp = p.cur_span();
            proof {
                lemma_arena_refl(p.prog@);
            }
            return ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::SingleStmtLexicalDecl,
                span: sp,
            });
        }
        p.advance();
        true
    } else {
        false
    };
    let name = match parse_ident(p) {
        ParseStep::Ok(nm) => nm,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_params = p.prog@;
    let params = match parse_formal_params(p, fuel - 1, is_async, is_gen) {
        ParseStep::Ok(ps) => ps,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_params, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_params, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_after_params = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_params, prog_after_params);
    }
    let (body, has_strict, has_octal, end_sp) = match parse_function_body(p, fuel - 1, is_async, is_gen) {
        ParseStep::Ok(t) => t,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_params, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_emit = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_params, prog_before_emit);
        assert forall|i: int| 0 <= i < params@.len() implies match (#[trigger] params@[i]).default {
            Some(id) => id.0 < p.prog.exprs@.len(),
            None => true,
        } by {
            assert(match params@[i].default {
                Some(id) => id.0 < prog_after_params.exprs.len(),
                None => true,
            });
        }
    }
    let res = p.emit_stmt(
        StmtKind::FunctionDecl {
            name,
            params,
            body,
            is_async,
            is_generator: is_gen,
            body_has_use_strict: has_strict,
            has_directive_octal_escape: has_octal,
        },
        Span { start: start_sp.start, end: end_sp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

/// Parses a `StatementListItem` (when `allow_decl == true`) or a sub-`Statement`
/// (when `allow_decl == false`, with `allow_annex_b_fn == true` for `IfStatement` clauses in sloppy mode).
/// Proves strict token-cursor progress (`old(p).pos < final(p).pos`) on every `ParseStep::Ok`!
pub fn parse_stmt_or_decl<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_decl: bool,
    allow_annex_b_fn: bool,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 15nat, 1nat,
{
    parse_stmt_or_decl_inner(p, fuel, allow_decl, allow_annex_b_fn, allow_decl)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn parse_stmt_or_decl_inner<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_decl: bool,
    allow_if_fn: bool,
    allow_labeled_fn: bool,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 15nat, 0nat,
{
    let start_sp = p.cur_span();
    if fuel == 0 {
        proof {
            lemma_arena_refl(p.prog@);
        }
        return ParseStep::Unsupported(UnsupportedSyntax {
            kind: UnsupportedSyntaxKind::MaxNestingDepthExceeded,
            span: start_sp,
        });
    }

    match &p.tokens[p.pos].kind {
        TokenKind::Punct(Punctuator::Semicolon) => {
            p.advance();
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(StmtKind::Empty, start_sp);
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Punct(Punctuator::LBrace) => {
            let (stmts, end_sp) = match parse_block_stmts(p, fuel - 1) {
                ParseStep::Ok(t) => t,
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(
                StmtKind::Block(stmts),
                Span { start: start_sp.start, end: end_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Var) => {
            p.advance();
            let ghost prog_after_kw = p.prog@;
            let decls = match parse_var_decl_list(p, fuel - 1, VarDeclKind::Var, true) {
                ParseStep::Ok(d) => d,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
            }
            match p.consume_semicolon() {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(()) => {},
            }
            let end_pos_sp = if p.pos > 0 { p.tokens[p.pos - 1].span } else { start_sp };
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(
                StmtKind::VarDecl { kind: VarDeclKind::Var, decls },
                Span { start: start_sp.start, end: end_pos_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Const) => {
            if !allow_decl {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::SingleStmtLexicalDecl,
                    span: start_sp,
                });
            }
            p.advance();
            let ghost prog_after_kw = p.prog@;
            let decls = match parse_var_decl_list(p, fuel - 1, VarDeclKind::Const, true) {
                ParseStep::Ok(d) => d,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
            }
            match p.consume_semicolon() {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(()) => {},
            }
            let end_pos_sp = if p.pos > 0 { p.tokens[p.pos - 1].span } else { start_sp };
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(
                StmtKind::VarDecl { kind: VarDeclKind::Const, decls },
                Span { start: start_sp.start, end: end_pos_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Let) if allow_decl && is_let_lexical_decl_at(p.tokens, p.pos) => {
            p.advance();
            let ghost prog_after_kw = p.prog@;
            let decls = match parse_var_decl_list(p, fuel - 1, VarDeclKind::Let, true) {
                ParseStep::Ok(d) => d,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
            }
            match p.consume_semicolon() {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(()) => {},
            }
            let end_pos_sp = if p.pos > 0 { p.tokens[p.pos - 1].span } else { start_sp };
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(
                StmtKind::VarDecl { kind: VarDeclKind::Let, decls },
                Span { start: start_sp.start, end: end_pos_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Let) if !allow_decl && is_let_bracket_at(p.tokens, p.pos) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::SingleStmtLexicalDecl,
                span: start_sp,
            })
        },
        TokenKind::Keyword(Keyword::Function) => {
            if !allow_decl && !((allow_if_fn || allow_labeled_fn) && !p.strict) {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::SingleStmtLexicalDecl,
                    span: start_sp,
                });
            }
            p.advance(); // consume `function`
            let ghost prog_after_fn = p.prog@;
            let res = parse_function_decl_after_kw(p, fuel - 1, start_sp, false, allow_decl);
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_fn, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Async) => {
            proof {
                if p.pos + 1 >= p.tokens@.len() {
                    assert(p.pos as int == p.tokens@.len() - 1);
                    assert(p.tokens@[p.pos as int] == p.tokens@.last());
                    assert(false);
                }
            }
            if is_kw(&p.tokens[p.pos + 1], Keyword::Function)
                && !p.tokens[p.pos + 1].preceded_by_line_terminator
            {
                if !allow_decl {
                    proof {
                        lemma_arena_refl(p.prog@);
                    }
                    return ParseStep::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::SingleStmtLexicalDecl,
                        span: start_sp,
                    });
                }
                p.advance(); // consume `async`
                p.advance(); // consume `function`
                let ghost prog_after_kw = p.prog@;
                let res = parse_function_decl_after_kw(p, fuel - 1, start_sp, true, true);
                proof {
                    lemma_arena_trans(old(p).prog@, prog_after_kw, p.prog@);
                }
                res
            } else if is_punct(&p.tokens[p.pos + 1], Punctuator::Colon) {
                parse_labeled_stmt(p, fuel, allow_decl || allow_labeled_fn)
            } else {
                parse_expr_stmt(p, fuel)
            }
        },
        TokenKind::Keyword(Keyword::If)
        | TokenKind::Keyword(Keyword::While)
        | TokenKind::Keyword(Keyword::Do) => parse_if_while_do_stmt(p, fuel),
        TokenKind::Keyword(Keyword::For) => parse_for_stmt(p, fuel),
        TokenKind::Keyword(Keyword::Switch) => parse_switch_stmt(p, fuel),
        TokenKind::Keyword(Keyword::Try) => parse_try_stmt(p, fuel),
        TokenKind::Keyword(Keyword::Return)
        | TokenKind::Keyword(Keyword::Break)
        | TokenKind::Keyword(Keyword::Continue)
        | TokenKind::Keyword(Keyword::Throw)
        | TokenKind::Keyword(Keyword::With)
        | TokenKind::Keyword(Keyword::Debugger) => parse_jump_or_with_stmt(p, fuel),
        TokenKind::Keyword(Keyword::Class) => {
            if !allow_decl {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::SingleStmtLexicalDecl,
                    span: start_sp,
                });
            }
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::ClassSyntax,
                span: start_sp,
            })
        },
        TokenKind::Keyword(Keyword::Export) => {
            proof {
                lemma_arena_refl(p.prog@);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::ModuleDeclarationInScript,
                span: start_sp,
            })
        },
        TokenKind::Keyword(Keyword::Import) => {
            proof {
                if p.pos + 1 >= p.tokens@.len() {
                    assert(p.pos as int == p.tokens@.len() - 1);
                    assert(p.tokens@[p.pos as int] == p.tokens@.last());
                    assert(false);
                }
            }
            if is_punct(&p.tokens[p.pos + 1], Punctuator::LParen) {
                parse_expr_stmt(p, fuel)
            } else {
                proof {
                    lemma_arena_refl(p.prog@);
                }
                ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::ModuleDeclarationInScript,
                    span: start_sp,
                })
            }
        },
        _ => {
            if token_can_be_ident(&p.tokens[p.pos], p.in_async, p.in_generator) {
                proof {
                    if p.pos + 1 >= p.tokens@.len() {
                        assert(p.pos as int == p.tokens@.len() - 1);
                        assert(p.tokens@[p.pos as int] == p.tokens@.last());
                        assert(false);
                    }
                }
                if is_punct(&p.tokens[p.pos + 1], Punctuator::Colon) {
                    return parse_labeled_stmt(p, fuel, allow_decl || allow_labeled_fn);
                }
            }
            parse_expr_stmt(p, fuel)
        },
    }
}


#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_if_while_do_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
        match old(p).tokens@[old(p).pos as int].kind {
            TokenKind::Keyword(Keyword::If)
            | TokenKind::Keyword(Keyword::While)
            | TokenKind::Keyword(Keyword::Do) => true,
            _ => false,
        },
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 14nat, 1nat,
{
    let start_sp = p.cur_span();
    match &p.tokens[p.pos].kind {
        TokenKind::Keyword(Keyword::If) => {
            p.advance();
            match p.expect_punct(Punctuator::LParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let ghost prog_before_c = p.prog@;
            let cond = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_c = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_c, prog_after_c);
            }
            match p.expect_punct(Punctuator::RParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let consequent = match parse_stmt_or_decl(p, fuel - 1, false, true) {
                ParseStep::Ok(sid) => sid,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_cons = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_c, prog_after_cons);
            }
            let (alternate, end_sp) = if is_kw(&p.tokens[p.pos], Keyword::Else) {
                p.advance();
                let ghost prog_before_alt = p.prog@;
                match parse_stmt_or_decl(p, fuel - 1, false, true) {
                    ParseStep::Ok(asid) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_alt, p.prog@);
                        }
                        let asp = p.prog.stmts[asid.0].span;
                        (Some(asid), asp)
                    },
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_alt, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_alt, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                }
            } else {
                let csp = p.prog.stmts[consequent.0].span;
                (None, csp)
            };
            let ghost prog_before_emit = p.prog@;
            proof {
                assert(cond.0 < prog_after_c.exprs.len());
                assert(prog_after_c.exprs.len() <= prog_after_cons.exprs.len());
                assert(prog_after_cons.exprs.len() <= prog_before_emit.exprs.len());
                assert(consequent.0 < prog_after_cons.stmts.len());
                assert(prog_after_cons.stmts.len() <= prog_before_emit.stmts.len());
            }
            let res = p.emit_stmt(
                StmtKind::If { cond, consequent, alternate },
                Span { start: start_sp.start, end: end_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::While) => {
            p.advance();
            match p.expect_punct(Punctuator::LParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let ghost prog_before_c = p.prog@;
            let cond = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_c = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_c, prog_after_c);
            }
            match p.expect_punct(Punctuator::RParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
                ParseStep::Ok(sid) => sid,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_before_emit = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_c, prog_before_emit);
                assert(cond.0 < prog_after_c.exprs.len());
            }
            let bsp = p.prog.stmts[body.0].span;
            let res = p.emit_stmt(
                StmtKind::While { cond, body },
                Span { start: start_sp.start, end: bsp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Do) => {
            p.advance();
            let ghost prog_before_b = p.prog@;
            let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
                ParseStep::Ok(sid) => sid,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_b, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_b, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_b = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_b, prog_after_b);
            }
            if !is_kw(&p.tokens[p.pos], Keyword::While) {
                let sp = p.cur_span();
                let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
                return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: sp });
            }
            p.advance(); // consume `while`
            match p.expect_punct(Punctuator::LParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let ghost prog_before_c = p.prog@;
            let cond = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_c, p.prog@);
            }
            let mut end_sp = match p.expect_punct(Punctuator::RParen) {
                ParseStep::Ok(s) => s,
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
            };
            // ES6+ §12.9.1 special ASI rule: `;` after `do ... while (...)` is ALWAYS optional!
            if is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
                end_sp = p.cur_span();
                p.advance();
            }
            let ghost prog_before_emit = p.prog@;
            proof {
                assert(body.0 < prog_after_b.stmts.len());
                assert(prog_after_b.stmts.len() <= prog_before_emit.stmts.len());
            }
            let res = p.emit_stmt(
                StmtKind::DoWhile { body, cond },
                Span { start: start_sp.start, end: end_sp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        _ => {
            proof {
                assert(false);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: start_sp,
            })
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn parse_jump_or_with_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
        match old(p).tokens@[old(p).pos as int].kind {
            TokenKind::Keyword(Keyword::Return)
            | TokenKind::Keyword(Keyword::Break)
            | TokenKind::Keyword(Keyword::Continue)
            | TokenKind::Keyword(Keyword::Throw)
            | TokenKind::Keyword(Keyword::With)
            | TokenKind::Keyword(Keyword::Debugger) => true,
            _ => false,
        },
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 14nat, 2nat,
{
    let start_sp = p.cur_span();
    match &p.tokens[p.pos].kind {
        TokenKind::Keyword(Keyword::Return) => {
            p.advance();
            if is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
                let semi_sp = p.cur_span();
                p.advance();
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Return(None),
                    Span { start: start_sp.start, end: semi_sp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else if is_punct(&p.tokens[p.pos], Punctuator::RBrace)
                || p.is_eof()
                || p.tokens[p.pos].preceded_by_line_terminator
            {
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(StmtKind::Return(None), start_sp);
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else {
                let ghost prog_before_e = p.prog@;
                let eid = match parse_expr(p, fuel - 1, true) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
                        }
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        proof {
                            lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
                        }
                        return ParseStep::Unsupported(u);
                    },
                };
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
                }
                let esp = p.prog.exprs[eid.0].span;
                match p.consume_semicolon() {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(()) => {},
                }
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Return(Some(eid)),
                    Span { start: start_sp.start, end: esp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            }
        },
        TokenKind::Keyword(Keyword::Break) => {
            p.advance();
            if is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
                let semi_sp = p.cur_span();
                p.advance();
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Break(None),
                    Span { start: start_sp.start, end: semi_sp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else if is_punct(&p.tokens[p.pos], Punctuator::RBrace)
                || p.is_eof()
                || p.tokens[p.pos].preceded_by_line_terminator
            {
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(StmtKind::Break(None), start_sp);
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else {
                let lbl = match parse_ident(p) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let lsp = lbl.span;
                match p.consume_semicolon() {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(()) => {},
                }
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Break(Some(lbl)),
                    Span { start: start_sp.start, end: lsp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            }
        },
        TokenKind::Keyword(Keyword::Continue) => {
            p.advance();
            if is_punct(&p.tokens[p.pos], Punctuator::Semicolon) {
                let semi_sp = p.cur_span();
                p.advance();
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Continue(None),
                    Span { start: start_sp.start, end: semi_sp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else if is_punct(&p.tokens[p.pos], Punctuator::RBrace)
                || p.is_eof()
                || p.tokens[p.pos].preceded_by_line_terminator
            {
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(StmtKind::Continue(None), start_sp);
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            } else {
                let lbl = match parse_ident(p) {
                    ParseStep::Ok(id) => id,
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                };
                let lsp = lbl.span;
                match p.consume_semicolon() {
                    ParseStep::SyntaxError(e) => {
                        return ParseStep::SyntaxError(e);
                    },
                    ParseStep::Unsupported(u) => {
                        return ParseStep::Unsupported(u);
                    },
                    ParseStep::Ok(()) => {},
                }
                let ghost prog_before_emit = p.prog@;
                let res = p.emit_stmt(
                    StmtKind::Continue(Some(lbl)),
                    Span { start: start_sp.start, end: lsp.end },
                );
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
                }
                res
            }
        },
        TokenKind::Keyword(Keyword::Throw) => {
            p.advance();
            if is_punct(&p.tokens[p.pos], Punctuator::Semicolon)
                || is_punct(&p.tokens[p.pos], Punctuator::RBrace)
                || p.is_eof()
            {
                let err_sp = p.cur_span();
                let dk = if p.is_eof() { DiagnosticKind::UnexpectedEof } else { DiagnosticKind::UnexpectedToken };
                return ParseStep::SyntaxError(SyntaxDiagnostic { kind: dk, span: err_sp });
            }
            if p.tokens[p.pos].preceded_by_line_terminator {
                let err_sp = p.cur_span();
                return ParseStep::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::LineTerminatorInThrow,
                    span: err_sp,
                });
            }
            let ghost prog_before_e = p.prog@;
            let eid = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_e, p.prog@);
            }
            let esp = p.prog.exprs[eid.0].span;
            match p.consume_semicolon() {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(()) => {},
            }
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(
                StmtKind::Throw(eid),
                Span { start: start_sp.start, end: esp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::With) => {
            p.advance();
            match p.expect_punct(Punctuator::LParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let ghost prog_before_o = p.prog@;
            let obj = match parse_expr(p, fuel - 1, true) {
                ParseStep::Ok(id) => id,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_o, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_before_o, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_after_o = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_o, prog_after_o);
            }
            match p.expect_punct(Punctuator::RParen) {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(_) => {},
            }
            let body = match parse_stmt_or_decl(p, fuel - 1, false, false) {
                ParseStep::Ok(sid) => sid,
                ParseStep::SyntaxError(e) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_o, p.prog@);
                    }
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    proof {
                        lemma_arena_trans(old(p).prog@, prog_after_o, p.prog@);
                    }
                    return ParseStep::Unsupported(u);
                },
            };
            let ghost prog_before_emit = p.prog@;
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_o, prog_before_emit);
                assert(obj.0 < prog_after_o.exprs.len());
            }
            let bsp = p.prog.stmts[body.0].span;
            let res = p.emit_stmt(
                StmtKind::With { object: obj, body },
                Span { start: start_sp.start, end: bsp.end },
            );
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        TokenKind::Keyword(Keyword::Debugger) => {
            p.advance();
            match p.consume_semicolon() {
                ParseStep::SyntaxError(e) => {
                    return ParseStep::SyntaxError(e);
                },
                ParseStep::Unsupported(u) => {
                    return ParseStep::Unsupported(u);
                },
                ParseStep::Ok(()) => {},
            }
            let ghost prog_before_emit = p.prog@;
            let res = p.emit_stmt(StmtKind::Debugger, start_sp);
            proof {
                lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
            }
            res
        },
        _ => {
            proof {
                assert(false);
            }
            ParseStep::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedToken,
                span: start_sp,
            })
        },
    }
}

fn parse_labeled_stmt<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    allow_labeled_fn: bool,
) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 14nat, 0nat,
{
    let start_sp = p.cur_span();
    let label = match parse_ident(p) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };
    match p.expect_punct(Punctuator::Colon) {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(_) => {},
    }
    let ghost prog_after_colon = p.prog@;
    let body = match parse_stmt_or_decl_inner(p, fuel - 1, false, false, allow_labeled_fn) {
        ParseStep::Ok(sid) => sid,
        ParseStep::SyntaxError(e) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_colon, p.prog@);
            }
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            proof {
                lemma_arena_trans(old(p).prog@, prog_after_colon, p.prog@);
            }
            return ParseStep::Unsupported(u);
        },
    };
    let ghost prog_before_emit = p.prog@;
    proof {
        lemma_arena_trans(old(p).prog@, prog_after_colon, prog_before_emit);
    }
    let bsp = p.prog.stmts[body.0].span;
    let res = p.emit_stmt(
        StmtKind::Labeled { label, body },
        Span { start: start_sp.start, end: bsp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

fn parse_expr_stmt<'a>(p: &mut Parser<'a>, fuel: usize) -> (res: ParseStep<StmtId>)
    requires
        old(p).wf(),
        fuel >= 1,
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).strict == old(p).strict,
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok(id) => old(p).pos < final(p).pos && id.0 < final(p).prog.stmts@.len(),
            _ => true,
        },
    decreases fuel, 14nat, 0nat,
{
    let start_sp = p.cur_span();
    let eid = match parse_expr(p, fuel, true) {
        ParseStep::Ok(id) => id,
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
    };
    let esp = p.prog.exprs[eid.0].span;
    match p.consume_semicolon() {
        ParseStep::SyntaxError(e) => {
            return ParseStep::SyntaxError(e);
        },
        ParseStep::Unsupported(u) => {
            return ParseStep::Unsupported(u);
        },
        ParseStep::Ok(()) => {},
    }
    let ghost prog_before_emit = p.prog@;
    let res = p.emit_stmt(
        StmtKind::ExprStmt(eid),
        Span { start: start_sp.start, end: esp.end },
    );
    proof {
        lemma_arena_trans(old(p).prog@, prog_before_emit, p.prog@);
    }
    res
}

/// Parses a `StatementList` with Directive Prologue tracking (`"use strict"` and legacy octal
/// escapes inside the Directive Prologue per §11.2.1).
/// Note: updates `p.strict |= has_use_strict` dynamically as directives are scanned!
pub fn parse_stmt_list_with_prologue<'a>(
    p: &mut Parser<'a>,
    fuel: usize,
    stop_at_rbrace: bool,
) -> (res: ParseStep<(Vec<StmtId>, bool, bool)>)
    requires
        old(p).wf(),
    ensures
        parser_step_post(*old(p), *final(p)),
        final(p).in_async == old(p).in_async,
        final(p).in_generator == old(p).in_generator,
        match res {
            ParseStep::Ok((stmts, _, _)) => {
                (!stop_at_rbrace ==> (final(p).tokens@[final(p).pos as int].kind is Eof))
                    && forall|s: int| 0 <= s < stmts@.len() ==> (#[trigger] stmts@[s]).0 < final(p).prog.stmts@.len()
            },
            _ => true,
        },
    decreases fuel, 16nat, 0nat,
{
    let mut stmts: Vec<StmtId> = Vec::new();
    let mut in_prologue = true;
    let mut has_use_strict = false;
    proof {
        lemma_arena_refl(p.prog@);
    }
    let mut has_directive_octal_escape = false;

    loop
        invariant
            p.wf(),
            p.tokens@ == old(p).tokens@,
            old(p).pos <= p.pos,
            arena_grew(old(p).prog@, p.prog@),
            p.in_async == old(p).in_async,
            p.in_generator == old(p).in_generator,
            forall|s: int| 0 <= s < stmts@.len() ==> (#[trigger] stmts@[s]).0 < p.prog.stmts@.len(),
        decreases p.tokens@.len() - p.pos,
    {
        if p.is_eof() {
            return ParseStep::Ok((stmts, has_use_strict, has_directive_octal_escape));
        }
        if stop_at_rbrace && is_punct(&p.tokens[p.pos], Punctuator::RBrace) {
            return ParseStep::Ok((stmts, has_use_strict, has_directive_octal_escape));
        }

        let (lead_is_str, lead_octal, lead_use_strict) = match &p.tokens[p.pos].kind {
            TokenKind::StringLit { has_legacy_octal_escape: oct, is_exact_use_strict: us, .. } => {
                (true, *oct, *us)
            },
            _ => (false, false, false),
        };

        let ghost prog_before_s = p.prog@;
        let sid = match parse_stmt_or_decl(p, fuel, true, false) {
            ParseStep::Ok(id) => id,
            ParseStep::SyntaxError(e) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
                }
                return ParseStep::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                proof {
                    lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
                }
                return ParseStep::Unsupported(u);
            },
        };

        if in_prologue {
            let is_directive = if lead_is_str {
                match &p.prog.stmts[sid.0].kind {
                    StmtKind::ExprStmt(eid) => {
                        if eid.0 < p.prog.exprs.len() {
                            match &p.prog.exprs[eid.0].kind {
                                ExprKind::StringLit { .. } => true,
                                _ => false,
                            }
                        } else {
                            false
                        }
                    },
                    _ => false,
                }
            } else {
                false
            };

            if is_directive {
                if lead_octal {
                    has_directive_octal_escape = true;
                }
                if lead_use_strict {
                    has_use_strict = true;
                    p.strict = true;
                }
            } else {
                in_prologue = false;
            }
        }

        let ghost prev_stmts = stmts@;
        stmts.push(sid);
        proof {
            lemma_arena_trans(old(p).prog@, prog_before_s, p.prog@);
            assert forall|s: int| 0 <= s < stmts@.len() implies (#[trigger] stmts@[s]).0 < p.prog.stmts@.len() by {
                if s < prev_stmts.len() {
                    assert(stmts@[s] == prev_stmts[s]);
                    assert(prev_stmts[s].0 < prog_before_s.stmts.len());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------
// Top-Level Verified Parser + Early-Errors Pipeline & Metatheorems
// ---------------------------------------------------------------------------------------

/// Theorem: Every successful statement/declaration parse strictly advances the token cursor (`p0.pos < p1.pos`).
pub proof fn lemma_parse_stmt_strict_progress<'a>(p0: Parser<'a>, p1: Parser<'a>, id: StmtId)
    requires
        parser_step_post(p0, p1),
        p0.pos < p1.pos,
        id.0 < p1.prog.stmts@.len(),
    ensures
        p1.tokens@.len() - p1.pos < p0.tokens@.len() - p0.pos,
{
}

/// Verified token-stream to validated `Program` parser (including Static Semantics: Early Errors).
///
/// Proves:
/// 1. Every `ParseOutcome::Ok(prog)` satisfies `prog.wf()`, `prog.grammar_wf()`, AND
///    `spec_check_early_errors(prog@) == Ok(())`!
/// 2. The parser consumes the entire token stream up to `TokenKind::Eof` (never silently dropping tokens).
pub fn parse_tokens_verified(tokens: &[Token]) -> (out: ParseOutcome)
    requires
        spec_tokens_wf(tokens@),
    ensures
        match out {
            ParseOutcome::Ok(prog) => {
                prog.wf()
                    && prog.grammar_wf()
                    && (crate::early_errors::spec_check_early_errors(prog@) is Ok)
            },
            _ => true,
        },
{
    let tlen = tokens.len();
    let initial_fuel: usize = if tlen <= (usize::MAX - 64) / 4 {
        tlen * 4 + 64
    } else {
        usize::MAX
    };

    let mut parser = Parser::new(tokens);
    let (body, has_use_strict, has_directive_octal_escape) =
        match parse_stmt_list_with_prologue(&mut parser, initial_fuel, false) {
            ParseStep::Ok(t) => t,
            ParseStep::SyntaxError(e) => {
                return ParseOutcome::SyntaxError(e);
            },
            ParseStep::Unsupported(u) => {
                return ParseOutcome::Unsupported(u);
            },
        };

    // Assert full-stream consumption (`parser.tokens[parser.pos]` is `Eof`)!
    if !parser.is_eof() {
        let sp = parser.cur_span();
        return ParseOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnexpectedToken,
            span: sp,
        });
    }

    let mut prog = parser.prog;
    let ghost old_prog = prog@;
    let ghost body_seq = body@;
    proof {
        reveal(prog_grammar_wf);
        assert(old_prog.grammar_wf());
        assert(old_prog.wf());
    }
    prog.body = body;
    prog.has_use_strict = has_use_strict;
    prog.has_directive_octal_escape = has_directive_octal_escape;
    proof {
        assert(prog@.exprs == old_prog.exprs);
        assert(prog@.stmts == old_prog.stmts);
        assert(prog@.body == body_seq);
        assert forall|i: int| 0 <= i < prog@.exprs.len() implies (
            ((#[trigger] prog@.exprs[i]).rank as nat) < prog@.exprs.len() + prog@.stmts.len()
                && crate::ast::expr_children_bounded(
                    prog@.exprs,
                    prog@.stmts,
                    prog@.exprs[i].kind,
                    prog@.exprs[i].rank as nat,
                )
                && expr_grammar_local_wf(prog@.exprs, prog@.exprs[i].kind)
        ) by {
            assert(prog@.exprs[i] == old_prog.exprs[i]);
        }
        assert forall|j: int| 0 <= j < prog@.stmts.len() implies (
            ((#[trigger] prog@.stmts[j]).rank as nat) < prog@.exprs.len() + prog@.stmts.len()
                && crate::ast::stmt_children_bounded(
                    prog@.exprs,
                    prog@.stmts,
                    prog@.stmts[j].kind,
                    prog@.stmts[j].rank as nat,
                )
                && stmt_grammar_local_wf(prog@.stmts[j].kind)
        ) by {
            assert(prog@.stmts[j] == old_prog.stmts[j]);
        }
        assert forall|k: int| 0 <= k < prog@.body.len() implies (#[trigger] prog@.body[k]).0 < prog@.stmts.len() by {
            assert(prog@.body[k] == body_seq[k]);
        }
        assert(prog.wf());
        assert(prog.grammar_wf());
    }

    match check_early_errors(&prog) {
        Ok(()) => ParseOutcome::Ok(prog),
        Err(diag) => ParseOutcome::SyntaxError(diag),
    }
}

} // verus!
