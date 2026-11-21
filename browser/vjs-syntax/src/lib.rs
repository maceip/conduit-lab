//! `vjs_syntax` (Step J3 of `vjs`, `docs/verified-browser-engine.md` §3.3):
//! Formally verified ECMAScript lexer, recursive-descent + Pratt AST parser,
//! and Static Semantics: Early Errors checker.
//!
//! Every public entry point (`parse_script`, `parse_script_str`, `parse_script_utf16`,
//! `tokenize`, `tokenize_utf16`, `parse_tokens_verified`, `check_early_errors`) is
//! machine-verified in Verus with zero trusted escape hatches (`#![forbid(unsafe_code)]`).
#![forbid(unsafe_code)]
#![allow(unused_imports, unused_variables)]

pub mod ast;
pub mod early_errors;
pub mod lexer;
pub mod parser;
pub mod token;

use vstd::prelude::*;

pub use ast::{
    ArrayElem, ArrowBody, AssignOp, BinOp, CallArg, CatchClause, Expr, ExprId, ExprKind,
    ForInOfLhs, ForInit, Ident, ObjPropKind, Param, ParseOutcome, Program, PropKeyAst, Stmt,
    StmtId, StmtKind, SwitchCase, UnaryOp, UpdateOp, VarDeclKind, VarDeclarator,
};
pub use early_errors::check_early_errors;
pub use lexer::{tokenize, tokenize_utf16, LexOutcome};
pub use parser::parse_tokens_verified;
pub use token::{
    DiagnosticKind, Keyword, Punctuator, Span, SyntaxDiagnostic, Token, TokenKind,
    UnsupportedSyntax, UnsupportedSyntaxKind,
};

verus! {

proof fn lemma_lex_ok_tokens_wf(tokens: Seq<Token>)
    requires
        token::spec_tokens_view(tokens).len() >= 1,
        token::spec_tokens_view(tokens).last().kind == token::SpecTokenKind::Eof,
    ensures
        parser::spec_tokens_wf(tokens),
{
    let v = token::spec_tokens_view(tokens);
    assert(tokens.len() == v.len());
    let last_idx = (tokens.len() - 1) as int;
    assert(v[last_idx] == tokens[last_idx]@);
    assert(v.last() == v[last_idx]);
    assert(tokens.last() == tokens[last_idx]);
    assert(tokens.last()@.kind == token::SpecTokenKind::Eof);
    match tokens.last().kind {
        TokenKind::Eof => {},
        _ => {
            assert(false);
        },
    }
}

/// Verified end-to-end ECMAScript Script parser over arbitrary `&[u8]` UTF-8 source bytes.
///
/// Total and panic-free on ALL byte inputs; guarantees that every `ParseOutcome::Ok(prog)`
/// satisfies arena acyclicity (`prog.wf()`), syntactic grammar invariants (`prog.grammar_wf()`),
/// and ECMA-262 Static Semantics: Early Errors (`spec_check_early_errors(prog@) == Ok(())`).
pub fn parse_script(input: &[u8]) -> (out: ParseOutcome)
    ensures
        match out {
            ParseOutcome::Ok(prog) => {
                prog.wf()
                    && prog.grammar_wf()
                    && (early_errors::spec_check_early_errors(prog@) is Ok)
            },
            _ => true,
        },
{
    match tokenize(input) {
        LexOutcome::Ok(tokens) => {
            proof {
                lexer::lemma_tokenize_ends_with_eof(input@);
                lemma_lex_ok_tokens_wf(tokens@);
            }
            parse_tokens_verified(tokens.as_slice())
        },
        LexOutcome::SyntaxError(e) => ParseOutcome::SyntaxError(e),
        LexOutcome::Unsupported(u) => ParseOutcome::Unsupported(u),
    }
}

/// Verified end-to-end ECMAScript Script parser over `&str`.
pub fn parse_script_str(src: &str) -> (out: ParseOutcome)
    ensures
        match out {
            ParseOutcome::Ok(prog) => {
                prog.wf()
                    && prog.grammar_wf()
                    && (early_errors::spec_check_early_errors(prog@) is Ok)
            },
            _ => true,
        },
{
    parse_script(src.as_bytes())
}

/// Verified end-to-end ECMAScript Script parser over UTF-16 code units `&[u16]` (§11.1.4).
pub fn parse_script_utf16(units: &[u16]) -> (out: ParseOutcome)
    ensures
        match out {
            ParseOutcome::Ok(prog) => {
                prog.wf()
                    && prog.grammar_wf()
                    && (early_errors::spec_check_early_errors(prog@) is Ok)
            },
            _ => true,
        },
{
    match lexer::utf16_units_to_utf8(units) {
        Ok(bytes) => parse_script(bytes.as_slice()),
        Err(e) => ParseOutcome::SyntaxError(e),
    }
}

} // verus!
