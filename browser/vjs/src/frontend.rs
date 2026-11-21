//! Verified Self-Contained ECMAScript Lexer, Recursive-Descent + Precedence-Climbing Parser,
//! ASI (§12.9), and Early Error Checker (`parse_script`), proved total and terminating in Verus.
use crate::ast::{
    AssignOp, BinOp, ChainStep, ExprId, ExprNode, ForEachLhs, FuncDef, FuncId, LogicalOp, Program,
    PropInit, PropKeyInit, StmtId, StmtNode, SwitchCase, UnaryOp, UnsupportedFeature, UpdateOp,
    VarDeclarator, VarKind,
};
#[cfg(verus_keep_ghost)]
use crate::ast::spec_prog_wf;
use crate::value::{
    clone_js_str, js_str_eq, string_to_js_num, JsNum, JsStr, POS_ZERO_BITS,
};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kw {
    Var,
    Let,
    Const,
    Function,
    Return,
    If,
    Else,
    While,
    Do,
    For,
    In,
    Of,
    Switch,
    Case,
    Default,
    Break,
    Continue,
    Try,
    Catch,
    Finally,
    Throw,
    New,
    Typeof,
    Void,
    Delete,
    Instanceof,
    This,
    True,
    False,
    Null,
    With,
    Async,
    Await,
    Yield,
    Class,
    Super,
    Import,
    Export,
    Debugger,
}

#[allow(inconsistent_fields)]
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TokKind {
    Ident(JsStr),
    Keyword { kw: Kw, raw: JsStr },
    Num { val: JsNum, legacy_octal: bool },
    Str { val: JsStr, has_escape: bool, has_legacy_octal_escape: bool },
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Semi,
    Comma,
    Dot,
    QuestionDot,
    Ellipsis,
    Colon,
    Question,
    Arrow,
    Plus,
    Minus,
    Star,
    StarStar,
    Slash,
    Percent,
    PlusPlus,
    MinusMinus,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Bang,
    AmpAmp,
    PipePipe,
    QuestionQuestion,
    Shl,
    Shr,
    Ushr,
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    BangEq,
    EqEqEq,
    BangEqEq,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    StarStarEq,
    SlashEq,
    PercentEq,
    ShlEq,
    ShrEq,
    UshrEq,
    AmpEq,
    PipeEq,
    CaretEq,
    AmpAmpEq,
    PipePipeEq,
    QuestionQuestionEq,
    Unsupported(UnsupportedFeature),
    Eof,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: TokKind,
    pub had_newline: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParseOutcome {
    Ok(Program),
    SyntaxError(JsStr),
    Unsupported(UnsupportedFeature),
}

fn clone_tok_kind(k: &TokKind) -> (r: TokKind) {
    match k {
        TokKind::Ident(s) => TokKind::Ident(clone_js_str(s)),
        TokKind::Keyword { kw, raw } => TokKind::Keyword { kw: *kw, raw: clone_js_str(raw) },
        TokKind::Num { val, legacy_octal } => TokKind::Num { val: *val, legacy_octal: *legacy_octal },
        TokKind::Str { val, has_escape, has_legacy_octal_escape } => TokKind::Str {
            val: clone_js_str(val),
            has_escape: *has_escape,
            has_legacy_octal_escape: *has_legacy_octal_escape,
        },
        TokKind::LParen => TokKind::LParen,
        TokKind::RParen => TokKind::RParen,
        TokKind::LBrace => TokKind::LBrace,
        TokKind::RBrace => TokKind::RBrace,
        TokKind::LBracket => TokKind::LBracket,
        TokKind::RBracket => TokKind::RBracket,
        TokKind::Semi => TokKind::Semi,
        TokKind::Comma => TokKind::Comma,
        TokKind::Dot => TokKind::Dot,
        TokKind::QuestionDot => TokKind::QuestionDot,
        TokKind::Ellipsis => TokKind::Ellipsis,
        TokKind::Colon => TokKind::Colon,
        TokKind::Question => TokKind::Question,
        TokKind::Arrow => TokKind::Arrow,
        TokKind::Plus => TokKind::Plus,
        TokKind::Minus => TokKind::Minus,
        TokKind::Star => TokKind::Star,
        TokKind::StarStar => TokKind::StarStar,
        TokKind::Slash => TokKind::Slash,
        TokKind::Percent => TokKind::Percent,
        TokKind::PlusPlus => TokKind::PlusPlus,
        TokKind::MinusMinus => TokKind::MinusMinus,
        TokKind::Amp => TokKind::Amp,
        TokKind::Pipe => TokKind::Pipe,
        TokKind::Caret => TokKind::Caret,
        TokKind::Tilde => TokKind::Tilde,
        TokKind::Bang => TokKind::Bang,
        TokKind::AmpAmp => TokKind::AmpAmp,
        TokKind::PipePipe => TokKind::PipePipe,
        TokKind::QuestionQuestion => TokKind::QuestionQuestion,
        TokKind::Shl => TokKind::Shl,
        TokKind::Shr => TokKind::Shr,
        TokKind::Ushr => TokKind::Ushr,
        TokKind::Lt => TokKind::Lt,
        TokKind::Le => TokKind::Le,
        TokKind::Gt => TokKind::Gt,
        TokKind::Ge => TokKind::Ge,
        TokKind::EqEq => TokKind::EqEq,
        TokKind::BangEq => TokKind::BangEq,
        TokKind::EqEqEq => TokKind::EqEqEq,
        TokKind::BangEqEq => TokKind::BangEqEq,
        TokKind::Eq => TokKind::Eq,
        TokKind::PlusEq => TokKind::PlusEq,
        TokKind::MinusEq => TokKind::MinusEq,
        TokKind::StarEq => TokKind::StarEq,
        TokKind::StarStarEq => TokKind::StarStarEq,
        TokKind::SlashEq => TokKind::SlashEq,
        TokKind::PercentEq => TokKind::PercentEq,
        TokKind::ShlEq => TokKind::ShlEq,
        TokKind::ShrEq => TokKind::ShrEq,
        TokKind::UshrEq => TokKind::UshrEq,
        TokKind::AmpEq => TokKind::AmpEq,
        TokKind::PipeEq => TokKind::PipeEq,
        TokKind::CaretEq => TokKind::CaretEq,
        TokKind::AmpAmpEq => TokKind::AmpAmpEq,
        TokKind::PipePipeEq => TokKind::PipePipeEq,
        TokKind::QuestionQuestionEq => TokKind::QuestionQuestionEq,
        TokKind::Unsupported(f) => TokKind::Unsupported(*f),
        TokKind::Eof => TokKind::Eof,
    }
}

fn syntax_err_msg(ascii: &[u8]) -> JsStr {
    let n = ascii.len();
    let mut v: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == ascii@.len(),
        decreases n - i,
    {
        v.push(ascii[i] as u16);
        i += 1;
    }
    JsStr(v)
}

fn clone_str_vec(src: &Vec<JsStr>) -> Vec<JsStr> {
    let n = src.len();
    let mut out: Vec<JsStr> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == src@.len(),
        decreases n - i,
    {
        out.push(clone_js_str(&src[i]));
        i += 1;
    }
    out
}

fn clone_expr_id_vec(src: &Vec<ExprId>) -> Vec<ExprId> {
    let n = src.len();
    let mut out: Vec<ExprId> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == src@.len(),
        decreases n - i,
    {
        out.push(src[i]);
        i += 1;
    }
    out
}

fn clone_chain_steps(src: &Vec<ChainStep>) -> Vec<ChainStep> {
    let n = src.len();
    let mut out: Vec<ChainStep> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == src@.len(),
        decreases n - i,
    {
        let step = match &src[i] {
            ChainStep::Member { prop, optional } => ChainStep::Member { prop: *prop, optional: *optional },
            ChainStep::Call { args, optional } => ChainStep::Call { args: clone_expr_id_vec(args), optional: *optional },
        };
        out.push(step);
        i += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// UTF-16 Lexer (§12: `<USP>` Whitespace, Legacy Octals, `_` Separators, Escapes)
// ---------------------------------------------------------------------------

fn is_ident_start_u16(u: u16) -> bool {
    (u >= 0x61 && u <= 0x7A)
        || (u >= 0x41 && u <= 0x5A)
        || u == 0x5F
        || u == 0x24
        || (u >= 0x80 && !crate::utf16::is_white_space(u) && !crate::utf16::is_line_terminator(u))
}

fn is_ident_part_u16(u: u16) -> bool {
    is_ident_start_u16(u) || (u >= 0x30 && u <= 0x39)
}

fn hex_nibble_u16(u: u16) -> (r: Option<u32>)
    ensures
        match r {
            Some(v) => v < 16,
            None => true,
        },
{
    if u >= 0x30 && u <= 0x39 {
        Some((u - 0x30) as u32)
    } else if u >= 0x61 && u <= 0x66 {
        Some((u - 0x61 + 10) as u32)
    } else if u >= 0x41 && u <= 0x46 {
        Some((u - 0x41 + 10) as u32)
    } else {
        None
    }
}

fn eq_ascii(s: &JsStr, lit: &[u8]) -> bool {
    if s.0.len() != lit.len() {
        return false;
    }
    let n = lit.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == lit@.len() && n == s.0@.len(),
        decreases n - i,
    {
        if s.0[i] != (lit[i] as u16) {
            return false;
        }
        i += 1;
    }
    true
}

fn classify_ident(s: JsStr) -> TokKind {
    if eq_ascii(&s, b"var") { TokKind::Keyword { kw: Kw::Var, raw: s } }
    else if eq_ascii(&s, b"let") { TokKind::Keyword { kw: Kw::Let, raw: s } }
    else if eq_ascii(&s, b"const") { TokKind::Keyword { kw: Kw::Const, raw: s } }
    else if eq_ascii(&s, b"function") { TokKind::Keyword { kw: Kw::Function, raw: s } }
    else if eq_ascii(&s, b"return") { TokKind::Keyword { kw: Kw::Return, raw: s } }
    else if eq_ascii(&s, b"if") { TokKind::Keyword { kw: Kw::If, raw: s } }
    else if eq_ascii(&s, b"else") { TokKind::Keyword { kw: Kw::Else, raw: s } }
    else if eq_ascii(&s, b"while") { TokKind::Keyword { kw: Kw::While, raw: s } }
    else if eq_ascii(&s, b"do") { TokKind::Keyword { kw: Kw::Do, raw: s } }
    else if eq_ascii(&s, b"for") { TokKind::Keyword { kw: Kw::For, raw: s } }
    else if eq_ascii(&s, b"in") { TokKind::Keyword { kw: Kw::In, raw: s } }
    else if eq_ascii(&s, b"of") { TokKind::Ident(s) }
    else if eq_ascii(&s, b"switch") { TokKind::Keyword { kw: Kw::Switch, raw: s } }
    else if eq_ascii(&s, b"case") { TokKind::Keyword { kw: Kw::Case, raw: s } }
    else if eq_ascii(&s, b"default") { TokKind::Keyword { kw: Kw::Default, raw: s } }
    else if eq_ascii(&s, b"break") { TokKind::Keyword { kw: Kw::Break, raw: s } }
    else if eq_ascii(&s, b"continue") { TokKind::Keyword { kw: Kw::Continue, raw: s } }
    else if eq_ascii(&s, b"try") { TokKind::Keyword { kw: Kw::Try, raw: s } }
    else if eq_ascii(&s, b"catch") { TokKind::Keyword { kw: Kw::Catch, raw: s } }
    else if eq_ascii(&s, b"finally") { TokKind::Keyword { kw: Kw::Finally, raw: s } }
    else if eq_ascii(&s, b"throw") { TokKind::Keyword { kw: Kw::Throw, raw: s } }
    else if eq_ascii(&s, b"new") { TokKind::Keyword { kw: Kw::New, raw: s } }
    else if eq_ascii(&s, b"typeof") { TokKind::Keyword { kw: Kw::Typeof, raw: s } }
    else if eq_ascii(&s, b"void") { TokKind::Keyword { kw: Kw::Void, raw: s } }
    else if eq_ascii(&s, b"delete") { TokKind::Keyword { kw: Kw::Delete, raw: s } }
    else if eq_ascii(&s, b"instanceof") { TokKind::Keyword { kw: Kw::Instanceof, raw: s } }
    else if eq_ascii(&s, b"this") { TokKind::Keyword { kw: Kw::This, raw: s } }
    else if eq_ascii(&s, b"true") { TokKind::Keyword { kw: Kw::True, raw: s } }
    else if eq_ascii(&s, b"false") { TokKind::Keyword { kw: Kw::False, raw: s } }
    else if eq_ascii(&s, b"null") { TokKind::Keyword { kw: Kw::Null, raw: s } }
    else if eq_ascii(&s, b"with") { TokKind::Keyword { kw: Kw::With, raw: s } }
    else if eq_ascii(&s, b"async") { TokKind::Keyword { kw: Kw::Async, raw: s } }
    else if eq_ascii(&s, b"await") { TokKind::Keyword { kw: Kw::Await, raw: s } }
    else if eq_ascii(&s, b"yield") { TokKind::Keyword { kw: Kw::Yield, raw: s } }
    else if eq_ascii(&s, b"class") { TokKind::Keyword { kw: Kw::Class, raw: s } }
    else if eq_ascii(&s, b"super") { TokKind::Keyword { kw: Kw::Super, raw: s } }
    else if eq_ascii(&s, b"import") { TokKind::Keyword { kw: Kw::Import, raw: s } }
    else if eq_ascii(&s, b"export") { TokKind::Keyword { kw: Kw::Export, raw: s } }
    else if eq_ascii(&s, b"debugger") { TokKind::Keyword { kw: Kw::Debugger, raw: s } }
    else { TokKind::Ident(s) }
}

fn tok_can_end_expr(k: &TokKind) -> bool {
    match k {
        TokKind::Ident(_)
        | TokKind::Num { .. }
        | TokKind::Str { .. }
        | TokKind::RParen
        | TokKind::RBracket
        | TokKind::RBrace
        | TokKind::PlusPlus
        | TokKind::MinusMinus => true,
        TokKind::Keyword { kw, .. } => matches!(kw, Kw::This | Kw::True | Kw::False | Kw::Null),
        _ => false,
    }
}

fn push_codepoint_utf16(out: &mut Vec<u16>, cp: u32) {
    if cp <= 0xFFFF {
        out.push(cp as u16);
    } else if cp <= 0x10FFFF {
        let off = cp - 0x10000;
        out.push((0xD800 + (off / 1024)) as u16);
        out.push((0xDC00 + (off % 1024)) as u16);
    } else {
        out.push(0xFFFD);
    }
}

fn lex_string_lit(us: &[u16], start: usize, quote: u16) -> (r: Result<(usize, TokKind, bool), JsStr>)
    requires start < us@.len(),
    ensures
        match r {
            Ok((next_pos, _, _)) => start < next_pos <= us@.len(),
            Err(_) => true,
        },
{
    let n = us.len();
    let mut i: usize = start + 1;
    let mut out: Vec<u16> = Vec::new();
    let mut has_escape = false;
    let mut has_legacy_octal_escape = false;
    let mut spanned_newline = false;
    while i < n
        invariant start < i <= n == us@.len(),
        decreases n - i,
    {
        let u = us[i];
        if u == quote {
            return Ok((
                i + 1,
                TokKind::Str { val: JsStr(out), has_escape, has_legacy_octal_escape },
                spanned_newline,
            ));
        }
        if (u == 0x0A || u == 0x0D) && quote != 0x60 {
            return Err(syntax_err_msg(b"Unterminated string literal"));
        }
        if quote == 0x60 && u == 0x24 && n - i >= 2 && us[i + 1] == 0x7B {
            return Ok((i + 2, TokKind::Unsupported(UnsupportedFeature::TaggedTemplate), spanned_newline));
        }
        if u == 0x5C {
            has_escape = true;
            if i + 1 >= n {
                return Err(syntax_err_msg(b"Unterminated escape sequence"));
            }
            let esc = us[i + 1];
            if esc == 0x6E { out.push(0x0A); i += 2; }
            else if esc == 0x72 { out.push(0x0D); i += 2; }
            else if esc == 0x74 { out.push(0x09); i += 2; }
            else if esc == 0x62 { out.push(0x08); i += 2; }
            else if esc == 0x66 { out.push(0x0C); i += 2; }
            else if esc == 0x76 { out.push(0x0B); i += 2; }
            else if esc == 0x5C { out.push(0x5C); i += 2; }
            else if esc == 0x27 { out.push(0x27); i += 2; }
            else if esc == 0x22 { out.push(0x22); i += 2; }
            else if esc == 0x60 { out.push(0x60); i += 2; }
            else if esc == 0x0A || esc == 0x2028 || esc == 0x2029 {
                spanned_newline = true;
                i += 2;
            } else if esc == 0x0D {
                spanned_newline = true;
                if n - i >= 3 && us[i + 2] == 0x0A { i += 3; } else { i += 2; }
            } else if esc >= 0x30 && esc <= 0x39 {
                let next_is_dec = n - i >= 3 && us[i + 2] >= 0x30 && us[i + 2] <= 0x39;
                if esc == 0x30 && !next_is_dec {
                    out.push(0x00);
                    i += 2;
                } else if quote == 0x60 {
                    return Err(syntax_err_msg(b"Octal escape sequences are not allowed in template strings"));
                } else if esc >= 0x38 {
                    has_legacy_octal_escape = true;
                    out.push(esc);
                    i += 2;
                } else if esc == 0x30 && n - i >= 3 && (us[i + 2] == 0x38 || us[i + 2] == 0x39) {
                    has_legacy_octal_escape = true;
                    out.push(0x00);
                    i += 2;
                } else {
                    has_legacy_octal_escape = true;
                    let mut val_oct: u16 = esc - 0x30;
                    let mut step_oct: usize = 2;
                    if n - i >= 3 && us[i + 2] >= 0x30 && us[i + 2] <= 0x37 {
                        val_oct = val_oct * 8 + (us[i + 2] - 0x30);
                        step_oct = 3;
                        if esc <= 0x33 && n - i >= 4 && us[i + 3] >= 0x30 && us[i + 3] <= 0x37 {
                            val_oct = val_oct * 8 + (us[i + 3] - 0x30);
                            step_oct = 4;
                        }
                    }
                    out.push(val_oct);
                    i += step_oct;
                }
            } else if esc == 0x78 {
                if n - i < 4 {
                    return Err(syntax_err_msg(b"Invalid hex escape"));
                }
                match (hex_nibble_u16(us[i + 2]), hex_nibble_u16(us[i + 3])) {
                    (Some(h1), Some(h2)) => {
                        out.push((h1 * 16 + h2) as u16);
                        i += 4;
                    }
                    _ => return Err(syntax_err_msg(b"Invalid hex escape")),
                }
            } else if esc == 0x75 {
                if n - i >= 3 && us[i + 2] == 0x7B {
                    let mut j: usize = i + 3;
                    let mut cp: u32 = 0;
                    let mut any_hex = false;
                    while j < n && us[j] != 0x7D
                        invariant i + 3 <= j <= n == us@.len(),
                        decreases n - j,
                    {
                        match hex_nibble_u16(us[j]) {
                            Some(d) => {
                                if cp > 0x10FFFF {
                                    return Err(syntax_err_msg(b"CodePoint escape out of range"));
                                }
                                cp = cp * 16 + d;
                                any_hex = true;
                                j += 1;
                            }
                            None => return Err(syntax_err_msg(b"Invalid unicode escape")),
                        }
                    }
                    if !any_hex || j >= n || cp > 0x10FFFF {
                        return Err(syntax_err_msg(b"Invalid unicode code point escape"));
                    }
                    push_codepoint_utf16(&mut out, cp);
                    i = j + 1;
                } else {
                    if n - i < 6 {
                        return Err(syntax_err_msg(b"Invalid unicode escape"));
                    }
                    match (
                        hex_nibble_u16(us[i + 2]),
                        hex_nibble_u16(us[i + 3]),
                        hex_nibble_u16(us[i + 4]),
                        hex_nibble_u16(us[i + 5]),
                    ) {
                        (Some(a), Some(b1), Some(c), Some(d)) => {
                            out.push((a * 4096 + b1 * 256 + c * 16 + d) as u16);
                            i += 6;
                        }
                        _ => return Err(syntax_err_msg(b"Invalid unicode escape")),
                    }
                }
            } else {
                out.push(esc);
                i += 2;
            }
        } else if quote == 0x60 && u == 0x0D {
            spanned_newline = true;
            out.push(0x0A);
            if n - i >= 2 && us[i + 1] == 0x0A {
                i += 2;
            } else {
                i += 1;
            }
        } else {
            if u == 0x0A || u == 0x2028 || u == 0x2029 {
                spanned_newline = true;
            }
            out.push(u);
            i += 1;
        }
    }
    Err(syntax_err_msg(b"Unterminated string literal"))
}

fn is_radix_digit_u16(u: u16, radix: u32) -> bool {
    if radix == 2 {
        u == 0x30 || u == 0x31
    } else if radix == 8 {
        u >= 0x30 && u <= 0x37
    } else if radix == 16 {
        (u >= 0x30 && u <= 0x39) || (u >= 0x41 && u <= 0x46) || (u >= 0x61 && u <= 0x66)
    } else {
        u >= 0x30 && u <= 0x39
    }
}

fn scan_digits_with_sep(
    us: &[u16],
    start: usize,
    radix: u32,
    out: &mut Vec<u16>,
) -> (r: Result<usize, JsStr>)
    requires start < us@.len(),
    ensures
        match r {
            Ok(end_pos) => start < end_pos <= us@.len(),
            Err(_) => true,
        },
{
    let n = us.len();
    if !is_radix_digit_u16(us[start], radix) {
        return Err(syntax_err_msg(b"Invalid numeric literal or leading separator"));
    }
    out.push(us[start]);
    let mut i: usize = start + 1;
    let mut prev_sep = false;
    while i < n && (is_radix_digit_u16(us[i], radix) || us[i] == 0x5F)
        invariant start < i <= n == us@.len(),
        decreases n - i,
    {
        if us[i] == 0x5F {
            if prev_sep {
                return Err(syntax_err_msg(b"Multiple consecutive numeric separators are not permitted"));
            }
            prev_sep = true;
        } else {
            out.push(us[i]);
            prev_sep = false;
        }
        i += 1;
    }
    if prev_sep {
        return Err(syntax_err_msg(b"Numeric separator is not allowed at the end of a numeric literal"));
    }
    Ok(i)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn lex_number_lit(us: &[u16], start: usize) -> (r: Result<(usize, TokKind), JsStr>)
    requires start < us@.len(),
    ensures
        match r {
            Ok((next_pos, _)) => start < next_pos <= us@.len(),
            Err(_) => true,
        },
{
    let n = us.len();
    let mut chars: Vec<u16> = Vec::new();

    // 1. Explicit binary / octal / hex prefix (`0b`/`0B`, `0o`/`0O`, `0x`/`0X`)
    if us[start] == 0x30 && n - start >= 2
        && (us[start + 1] == 0x78 || us[start + 1] == 0x58
            || us[start + 1] == 0x62 || us[start + 1] == 0x42
            || us[start + 1] == 0x6F || us[start + 1] == 0x4F)
    {
        let pfx = us[start + 1];
        let radix: u32 = if pfx == 0x78 || pfx == 0x58 {
            16
        } else if pfx == 0x62 || pfx == 0x42 {
            2
        } else {
            8
        };
        if start + 2 >= n {
            return Err(syntax_err_msg(b"Missing digits after numeric prefix"));
        }
        chars.push(0x30);
        chars.push(pfx);
        let i = match scan_digits_with_sep(us, start + 2, radix, &mut chars) {
            Ok(end_p) => end_p,
            Err(m) => return Err(m),
        };
        if i < n && us[i] == 0x6E {
            if i + 1 < n && is_ident_part_u16(us[i + 1]) {
                return Err(syntax_err_msg(b"Identifier immediately after BigInt literal"));
            }
            return Ok((i + 1, TokKind::Unsupported(UnsupportedFeature::BigIntLiteral)));
        }
        if i < n && (is_ident_start_u16(us[i]) || (us[i] >= 0x30 && us[i] <= 0x39)) {
            return Err(syntax_err_msg(b"Invalid digit or identifier immediately after numeric literal"));
        }
        let num = string_to_js_num(&JsStr(chars));
        if crate::value::num_is_nan(num) {
            return Err(syntax_err_msg(b"Invalid numeric literal"));
        }
        return Ok((i, TokKind::Num { val: num, legacy_octal: false }));
    }

    // 2. Leading `0` followed by digit or `_`: LegacyOctalIntegerLiteral (`010`) or NonOctalDecimal (`08`, `09`)
    if us[start] == 0x30 && n - start >= 2
        && ((us[start + 1] >= 0x30 && us[start + 1] <= 0x39) || us[start + 1] == 0x5F)
    {
        if us[start + 1] == 0x5F {
            return Err(syntax_err_msg(b"Numeric separator not allowed after leading 0"));
        }
        let mut i: usize = start + 1;
        let mut all_octal = true;
        let mut raw_digits: Vec<u16> = Vec::new();
        while i < n && ((us[i] >= 0x30 && us[i] <= 0x39) || us[i] == 0x5F)
            invariant start < i <= n == us@.len(),
            decreases n - i,
        {
            if us[i] == 0x5F {
                return Err(syntax_err_msg(b"Numeric separator not allowed in leading-zero literal"));
            }
            if us[i] >= 0x38 {
                all_octal = false;
            }
            raw_digits.push(us[i]);
            i += 1;
        }
        if i < n && us[i] == 0x6E {
            return Err(syntax_err_msg(b"Invalid BigInt literal with leading zero"));
        }
        if all_octal {
            if i < n && (us[i] == 0x2E || us[i] == 0x65 || us[i] == 0x45 || is_ident_start_u16(us[i])) {
                return Err(syntax_err_msg(b"Unexpected character after legacy octal literal"));
            }
            chars.push(0x30);
            chars.push(0x6F);
            let mut k: usize = 0;
            while k < raw_digits.len()
                invariant k <= raw_digits@.len(),
                decreases raw_digits@.len() - k,
            {
                chars.push(raw_digits[k]);
                k += 1;
            }
            let num = string_to_js_num(&JsStr(chars));
            return Ok((i, TokKind::Num { val: num, legacy_octal: true }));
        }
        // NonOctalDecimalIntegerLiteral (`08`, `09`, `08.5` in sloppy mode; SyntaxError in strict mode)
        chars.push(0x30);
        let mut k: usize = 0;
        while k < raw_digits.len()
            invariant k <= raw_digits@.len(),
            decreases raw_digits@.len() - k,
        {
            chars.push(raw_digits[k]);
            k += 1;
        }
        if i < n && us[i] == 0x2E {
            chars.push(0x2E);
            i += 1;
            if i < n && ((us[i] >= 0x30 && us[i] <= 0x39) || us[i] == 0x5F) {
                i = match scan_digits_with_sep(us, i, 10, &mut chars) {
                    Ok(end_p) => end_p,
                    Err(m) => return Err(m),
                };
            }
        }
        if i < n && (us[i] == 0x65 || us[i] == 0x45) {
            chars.push(us[i]);
            i += 1;
            if i < n && (us[i] == 0x2B || us[i] == 0x2D) {
                chars.push(us[i]);
                i += 1;
            }
            if i >= n {
                return Err(syntax_err_msg(b"Exponent requires digits"));
            }
            i = match scan_digits_with_sep(us, i, 10, &mut chars) {
                Ok(end_p) => end_p,
                Err(m) => return Err(m),
            };
        }
        if i < n && is_ident_start_u16(us[i]) {
            return Err(syntax_err_msg(b"Identifier immediately after numeric literal"));
        }
        let num = string_to_js_num(&JsStr(chars));
        return Ok((i, TokKind::Num { val: num, legacy_octal: true }));
    }

    // 3. Standard DecimalLiteral / DecimalBigIntegerLiteral
    let mut i: usize = start;
    if us[start] != 0x2E {
        i = match scan_digits_with_sep(us, start, 10, &mut chars) {
            Ok(end_p) => end_p,
            Err(m) => return Err(m),
        };
        if i < n && us[i] == 0x6E {
            if i + 1 < n && is_ident_part_u16(us[i + 1]) {
                return Err(syntax_err_msg(b"Identifier immediately after BigInt literal"));
            }
            return Ok((i + 1, TokKind::Unsupported(UnsupportedFeature::BigIntLiteral)));
        }
    }
    if i < n && us[i] == 0x2E {
        chars.push(0x2E);
        i += 1;
        if i < n && ((us[i] >= 0x30 && us[i] <= 0x39) || us[i] == 0x5F) {
            i = match scan_digits_with_sep(us, i, 10, &mut chars) {
                Ok(end_p) => end_p,
                Err(m) => return Err(m),
            };
        }
    }
    if i < n && (us[i] == 0x65 || us[i] == 0x45) {
        chars.push(us[i]);
        i += 1;
        if i < n && (us[i] == 0x2B || us[i] == 0x2D) {
            chars.push(us[i]);
            i += 1;
        }
        if i >= n {
            return Err(syntax_err_msg(b"Exponent requires digits"));
        }
        i = match scan_digits_with_sep(us, i, 10, &mut chars) {
            Ok(end_p) => end_p,
            Err(m) => return Err(m),
        };
    }
    if i == start {
        return Ok((start + 1, TokKind::Num { val: JsNum(POS_ZERO_BITS), legacy_octal: false }));
    }
    if i < n && is_ident_start_u16(us[i]) {
        return Err(syntax_err_msg(b"Identifier immediately after numeric literal"));
    }
    let num = string_to_js_num(&JsStr(chars));
    Ok((i, TokKind::Num { val: num, legacy_octal: false }))
}

fn skip_regex_literal_u16(us: &[u16], start: usize) -> (r: Result<usize, JsStr>)
    requires start < us@.len(),
    ensures
        match r {
            Ok(next_pos) => start < next_pos <= us@.len(),
            Err(_) => true,
        },
{
    let n = us.len();
    let mut i: usize = start + 1;
    let mut in_class = false;
    while i < n
        invariant start < i <= n == us@.len(),
        decreases n - i,
    {
        let u = us[i];
        if crate::utf16::is_line_terminator(u) {
            return Err(syntax_err_msg(b"Unterminated regular expression literal"));
        }
        if u == 0x5C {
            if i + 1 >= n || crate::utf16::is_line_terminator(us[i + 1]) {
                return Err(syntax_err_msg(b"Unterminated regular expression escape"));
            }
            i += 2;
        } else if u == 0x5B {
            in_class = true;
            i += 1;
        } else if u == 0x5D {
            in_class = false;
            i += 1;
        } else if u == 0x2F && !in_class {
            i += 1;
            while i < n && is_ident_part_u16(us[i])
                invariant start < i <= n == us@.len(),
                decreases n - i,
            {
                i += 1;
            }
            return Ok(i);
        } else {
            i += 1;
        }
    }
    Err(syntax_err_msg(b"Unterminated regular expression literal"))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn tokenize_utf16(us: &[u16]) -> (res: Result<Vec<Token>, JsStr>) {
    let n = us.len();
    let mut pos: usize = 0;
    let mut tokens: Vec<Token> = Vec::new();
    let mut had_newline = false;
    let mut prev_can_end = false;

    // Optional hashbang `#!...` at start of script (§12.5)
    if n >= 2 && us[0] == 0x23 && us[1] == 0x21 {
        pos = 2;
        while pos < n && !crate::utf16::is_line_terminator(us[pos])
            invariant 2 <= pos <= n == us@.len(),
            decreases n - pos,
        {
            pos += 1;
        }
    }

    while pos < n
        invariant pos <= n == us@.len(),
        decreases n - pos,
    {
        #[allow(unused_variables)]
        let iter_start = pos;
        let u = us[pos];
        if crate::utf16::is_white_space(u) {
            pos += 1;
        } else if crate::utf16::is_line_terminator(u) {
            had_newline = true;
            pos += 1;
        } else if u == 0x2F && n - pos >= 2 && us[pos + 1] == 0x2F {
            pos += 2;
            while pos < n && !crate::utf16::is_line_terminator(us[pos])
                invariant iter_start < pos <= n == us@.len(),
                decreases n - pos,
            {
                pos += 1;
            }
        } else if u == 0x2F && n - pos >= 2 && us[pos + 1] == 0x2A {
            pos += 2;
            let mut closed = false;
            while pos < n
                invariant iter_start < pos <= n == us@.len(),
                decreases n - pos,
            {
                if us[pos] == 0x2A && n - pos >= 2 && us[pos + 1] == 0x2F {
                    pos += 2;
                    closed = true;
                    break;
                }
                if crate::utf16::is_line_terminator(us[pos]) {
                    had_newline = true;
                }
                pos += 1;
            }
            if !closed {
                return Err(syntax_err_msg(b"Unterminated multi-line comment"));
            }
        } else if u == 0x27 || u == 0x22 || u == 0x60 {
            if u == 0x60 && prev_can_end {
                tokens.push(Token {
                    kind: TokKind::Unsupported(UnsupportedFeature::TaggedTemplate),
                    had_newline,
                });
                return Ok(tokens);
            }
            match lex_string_lit(us, pos, u) {
                Ok((next_pos, kind, spanned_nl)) => {
                    prev_can_end = tok_can_end_expr(&kind);
                    tokens.push(Token { kind, had_newline });
                    had_newline = spanned_nl;
                    pos = next_pos;
                }
                Err(msg) => return Err(msg),
            }
        } else if (u >= 0x30 && u <= 0x39)
            || (u == 0x2E && n - pos >= 2 && us[pos + 1] >= 0x30 && us[pos + 1] <= 0x39)
        {
            match lex_number_lit(us, pos) {
                Ok((next_pos, kind)) => {
                    prev_can_end = tok_can_end_expr(&kind);
                    tokens.push(Token { kind, had_newline });
                    had_newline = false;
                    pos = next_pos;
                }
                Err(msg) => return Err(msg),
            }
        } else if is_ident_start_u16(u) {
            let mut chars: Vec<u16> = Vec::new();
            #[allow(unused_variables)]
            let start = pos;
            chars.push(u);
            pos += 1;
            while pos < n && is_ident_part_u16(us[pos])
                invariant start < pos <= n == us@.len(),
                decreases n - pos,
            {
                chars.push(us[pos]);
                pos += 1;
            }
            let kind = classify_ident(JsStr(chars));
            prev_can_end = tok_can_end_expr(&kind);
            tokens.push(Token { kind, had_newline });
            had_newline = false;
        } else if u == 0x2F && !prev_can_end {
            match skip_regex_literal_u16(us, pos) {
                Ok(next_pos) => {
                    let kind = TokKind::Unsupported(UnsupportedFeature::RegExpLiteral);
                    prev_can_end = true;
                    tokens.push(Token { kind, had_newline });
                    had_newline = false;
                    pos = next_pos;
                }
                Err(msg) => return Err(msg),
            }
        } else {
            let (step, kind): (usize, TokKind) = if u == 0x28 {
                (1, TokKind::LParen)
            } else if u == 0x29 {
                (1, TokKind::RParen)
            } else if u == 0x7B {
                (1, TokKind::LBrace)
            } else if u == 0x7D {
                (1, TokKind::RBrace)
            } else if u == 0x5B {
                (1, TokKind::LBracket)
            } else if u == 0x5D {
                (1, TokKind::RBracket)
            } else if u == 0x3B {
                (1, TokKind::Semi)
            } else if u == 0x2C {
                (1, TokKind::Comma)
            } else if u == 0x7E {
                (1, TokKind::Tilde)
            } else if u == 0x3A {
                (1, TokKind::Colon)
            } else if u == 0x2E {
                if n - pos >= 3 && us[pos + 1] == 0x2E && us[pos + 2] == 0x2E {
                    (3, TokKind::Ellipsis)
                } else {
                    (1, TokKind::Dot)
                }
            } else if u == 0x3F {
                if n - pos >= 3 && us[pos + 1] == 0x3F && us[pos + 2] == 0x3D {
                    (3, TokKind::QuestionQuestionEq)
                } else if n - pos >= 2 && us[pos + 1] == 0x3F {
                    (2, TokKind::QuestionQuestion)
                } else if n - pos >= 2 && us[pos + 1] == 0x2E
                    && !(n - pos >= 3 && us[pos + 2] >= 0x30 && us[pos + 2] <= 0x39)
                {
                    (2, TokKind::QuestionDot)
                } else {
                    (1, TokKind::Question)
                }
            } else if u == 0x2B {
                if n - pos >= 2 && us[pos + 1] == 0x2B { (2, TokKind::PlusPlus) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::PlusEq) }
                else { (1, TokKind::Plus) }
            } else if u == 0x2D {
                if n - pos >= 2 && us[pos + 1] == 0x2D { (2, TokKind::MinusMinus) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::MinusEq) }
                else { (1, TokKind::Minus) }
            } else if u == 0x2A {
                if n - pos >= 3 && us[pos + 1] == 0x2A && us[pos + 2] == 0x3D { (3, TokKind::StarStarEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x2A { (2, TokKind::StarStar) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::StarEq) }
                else { (1, TokKind::Star) }
            } else if u == 0x2F {
                if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::SlashEq) }
                else { (1, TokKind::Slash) }
            } else if u == 0x25 {
                if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::PercentEq) }
                else { (1, TokKind::Percent) }
            } else if u == 0x26 {
                if n - pos >= 3 && us[pos + 1] == 0x26 && us[pos + 2] == 0x3D { (3, TokKind::AmpAmpEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x26 { (2, TokKind::AmpAmp) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::AmpEq) }
                else { (1, TokKind::Amp) }
            } else if u == 0x7C {
                if n - pos >= 3 && us[pos + 1] == 0x7C && us[pos + 2] == 0x3D { (3, TokKind::PipePipeEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x7C { (2, TokKind::PipePipe) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::PipeEq) }
                else { (1, TokKind::Pipe) }
            } else if u == 0x5E {
                if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::CaretEq) }
                else { (1, TokKind::Caret) }
            } else if u == 0x21 {
                if n - pos >= 3 && us[pos + 1] == 0x3D && us[pos + 2] == 0x3D { (3, TokKind::BangEqEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::BangEq) }
                else { (1, TokKind::Bang) }
            } else if u == 0x3D {
                if n - pos >= 3 && us[pos + 1] == 0x3D && us[pos + 2] == 0x3D { (3, TokKind::EqEqEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::EqEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x3E { (2, TokKind::Arrow) }
                else { (1, TokKind::Eq) }
            } else if u == 0x3C {
                if n - pos >= 3 && us[pos + 1] == 0x3C && us[pos + 2] == 0x3D { (3, TokKind::ShlEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x3C { (2, TokKind::Shl) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::Le) }
                else { (1, TokKind::Lt) }
            } else if u == 0x3E {
                if n - pos >= 4 && us[pos + 1] == 0x3E && us[pos + 2] == 0x3E && us[pos + 3] == 0x3D { (4, TokKind::UshrEq) }
                else if n - pos >= 3 && us[pos + 1] == 0x3E && us[pos + 2] == 0x3E { (3, TokKind::Ushr) }
                else if n - pos >= 3 && us[pos + 1] == 0x3E && us[pos + 2] == 0x3D { (3, TokKind::ShrEq) }
                else if n - pos >= 2 && us[pos + 1] == 0x3E { (2, TokKind::Shr) }
                else if n - pos >= 2 && us[pos + 1] == 0x3D { (2, TokKind::Ge) }
                else { (1, TokKind::Gt) }
            } else {
                return Err(syntax_err_msg(b"Unexpected character in input"));
            };
            prev_can_end = tok_can_end_expr(&kind);
            tokens.push(Token { kind, had_newline });
            had_newline = false;
            pos += step;
        }
    }

    tokens.push(Token { kind: TokKind::Eof, had_newline });
    Ok(tokens)
}

pub fn tokenize(bs: &[u8]) -> (res: Result<Vec<Token>, JsStr>)
    ensures (crate::utf16::spec_utf8_to_utf16(bs@) is None) ==> (res is Err),
{
    match crate::utf16::utf8_to_utf16(bs) {
        Some(u16s) => tokenize_utf16(u16s.units.as_slice()),
        None => Err(syntax_err_msg(b"Invalid UTF-8 source bytes")),
    }
}

// ---------------------------------------------------------------------------
// Recursive-Descent + Precedence-Climbing Parser & Early Error Validation
// ---------------------------------------------------------------------------

enum PRes<T> {
    Ok(T),
    SyntaxErr(JsStr),
    Unsup(UnsupportedFeature),
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    prog: Program,
    strict: bool,
    in_function: bool,
    loop_depth: usize,
    switch_depth: usize,
    labels: Vec<(JsStr, bool)>,
    var_scopes: Vec<Vec<JsStr>>,
}

fn vec_contains_str(list: &Vec<JsStr>, target: &JsStr) -> bool {
    let n = list.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == list@.len(),
        decreases n - i,
    {
        if js_str_eq(&list[i], target) {
            return true;
        }
        i += 1;
    }
    false
}

fn push_unique_str(list: &mut Vec<JsStr>, s: JsStr) {
    if !vec_contains_str(list, &s) {
        list.push(s);
    }
}

fn is_strict_restricted_ident(s: &JsStr) -> bool {
    eq_ascii(s, b"eval") || eq_ascii(s, b"arguments")
}

/// Deterministic lookahead from `LParen` at `lparen_pos` to check for `(p1, p2, ...) =>`
/// with no LineTerminator before `=>`.
fn scan_arrow_params(tokens: &Vec<Token>, lparen_pos: usize, strict: bool) -> PRes<Option<(usize, Vec<JsStr>)>> {
    let n = tokens.len();
    if lparen_pos >= n || !matches!(tokens[lparen_pos].kind, TokKind::LParen) {
        return PRes::Ok(None);
    }
    let mut i: usize = lparen_pos + 1;
    let mut params: Vec<JsStr> = Vec::new();
    if i < n && matches!(tokens[i].kind, TokKind::RParen) {
        let after_rparen = i + 1;
        if after_rparen < n && matches!(tokens[after_rparen].kind, TokKind::Arrow) && !tokens[after_rparen].had_newline {
            return PRes::Ok(Some((after_rparen + 1, params)));
        }
        return PRes::Ok(None);
    }
    while i < n
        invariant lparen_pos < i <= n == tokens@.len(),
        decreases n - i,
    {
        if matches!(tokens[i].kind, TokKind::Ellipsis | TokKind::LBracket | TokKind::LBrace) {
            // Check if this parenthesized group is actually followed by `=>` before rejecting as destructuring:
            let mut depth: usize = 1;
            let mut k: usize = i;
            while k < n && depth > 0
                invariant i <= k <= n == tokens@.len(),
                decreases n - k,
            {
                match tokens[k].kind {
                    TokKind::LParen => { if depth < usize::MAX { depth += 1; } }
                    TokKind::RParen => { depth -= 1; }
                    _ => {}
                }
                k += 1;
            }
            if depth == 0 && k < n && matches!(tokens[k].kind, TokKind::Arrow) && !tokens[k].had_newline {
                return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
            }
            return PRes::Ok(None);
        }
        let pname = match &tokens[i].kind {
            TokKind::Ident(s) => clone_js_str(s),
            _ => return PRes::Ok(None),
        };
        i += 1;
        if i >= n {
            return PRes::Ok(None);
        }
        if matches!(tokens[i].kind, TokKind::Comma) {
            params.push(pname);
            i += 1;
            if i < n && matches!(tokens[i].kind, TokKind::RParen) {
                let after = i + 1;
                if after < n && matches!(tokens[after].kind, TokKind::Arrow) && !tokens[after].had_newline {
                    return check_arrow_dups(params, after + 1, strict);
                }
                return PRes::Ok(None);
            }
        } else if matches!(tokens[i].kind, TokKind::RParen) {
            params.push(pname);
            let after = i + 1;
            if after < n && matches!(tokens[after].kind, TokKind::Arrow) && !tokens[after].had_newline {
                return check_arrow_dups(params, after + 1, strict);
            }
            return PRes::Ok(None);
        } else {
            return PRes::Ok(None);
        }
    }
    PRes::Ok(None)
}

fn check_arrow_dups(params: Vec<JsStr>, next_pos: usize, strict: bool) -> PRes<Option<(usize, Vec<JsStr>)>> {
    // Arrow functions ALWAYS forbid duplicate parameter names (§15.3.1)!
    let n = params.len();
    let mut seen: Vec<JsStr> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n == params@.len(),
        decreases n - i,
    {
        if strict && is_strict_restricted_ident(&params[i]) {
            return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict mode arrow parameter name"));
        }
        if vec_contains_str(&seen, &params[i]) {
            return PRes::SyntaxErr(syntax_err_msg(b"Duplicate parameter name in arrow function"));
        }
        seen.push(clone_js_str(&params[i]));
        i += 1;
    }
    PRes::Ok(Some((next_pos, params)))
}

fn binop_info(k: &TokKind, allow_in: bool) -> (r: Option<(u8, bool, Option<BinOp>, Option<LogicalOp>)>)
    ensures
        match r {
            Some((prec, _, _, _)) => prec <= 11,
            None => true,
        },
{
    match k {
        TokKind::PipePipe => Some((1, false, None, Some(LogicalOp::Or))),
        TokKind::QuestionQuestion => Some((1, false, None, Some(LogicalOp::Nullish))),
        TokKind::AmpAmp => Some((2, false, None, Some(LogicalOp::And))),
        TokKind::Pipe => Some((3, false, Some(BinOp::BitOr), None)),
        TokKind::Caret => Some((4, false, Some(BinOp::BitXor), None)),
        TokKind::Amp => Some((5, false, Some(BinOp::BitAnd), None)),
        TokKind::EqEq => Some((6, false, Some(BinOp::EqLoose), None)),
        TokKind::BangEq => Some((6, false, Some(BinOp::NeLoose), None)),
        TokKind::EqEqEq => Some((6, false, Some(BinOp::EqStrict), None)),
        TokKind::BangEqEq => Some((6, false, Some(BinOp::NeStrict), None)),
        TokKind::Lt => Some((7, false, Some(BinOp::Lt), None)),
        TokKind::Le => Some((7, false, Some(BinOp::Le), None)),
        TokKind::Gt => Some((7, false, Some(BinOp::Gt), None)),
        TokKind::Ge => Some((7, false, Some(BinOp::Ge), None)),
        TokKind::Keyword { kw: Kw::Instanceof, .. } => Some((7, false, Some(BinOp::Instanceof), None)),
        TokKind::Keyword { kw: Kw::In, .. } => if allow_in {
            Some((7, false, Some(BinOp::In), None))
        } else {
            None
        },
        TokKind::Shl => Some((8, false, Some(BinOp::Shl), None)),
        TokKind::Shr => Some((8, false, Some(BinOp::Shr), None)),
        TokKind::Ushr => Some((8, false, Some(BinOp::Ushr), None)),
        TokKind::Plus => Some((9, false, Some(BinOp::Add), None)),
        TokKind::Minus => Some((9, false, Some(BinOp::Sub), None)),
        TokKind::Star => Some((10, false, Some(BinOp::Mul), None)),
        TokKind::Slash => Some((10, false, Some(BinOp::Div), None)),
        TokKind::Percent => Some((10, false, Some(BinOp::Rem), None)),
        TokKind::StarStar => Some((11, true, Some(BinOp::Exp), None)),
        _ => None,
    }
}

fn assign_op_of(k: &TokKind) -> Option<AssignOp> {
    match k {
        TokKind::Eq => Some(AssignOp::Assign),
        TokKind::PlusEq => Some(AssignOp::AddAssign),
        TokKind::MinusEq => Some(AssignOp::SubAssign),
        TokKind::StarEq => Some(AssignOp::MulAssign),
        TokKind::StarStarEq => Some(AssignOp::ExpAssign),
        TokKind::SlashEq => Some(AssignOp::DivAssign),
        TokKind::PercentEq => Some(AssignOp::RemAssign),
        TokKind::ShlEq => Some(AssignOp::ShlAssign),
        TokKind::ShrEq => Some(AssignOp::ShrAssign),
        TokKind::UshrEq => Some(AssignOp::UshrAssign),
        TokKind::AmpEq => Some(AssignOp::BitAndAssign),
        TokKind::PipeEq => Some(AssignOp::BitOrAssign),
        TokKind::CaretEq => Some(AssignOp::BitXorAssign),
        TokKind::AmpAmpEq => Some(AssignOp::AndAssign),
        TokKind::PipePipeEq => Some(AssignOp::OrAssign),
        TokKind::QuestionQuestionEq => Some(AssignOp::NullishAssign),
        _ => None,
    }
}

impl Parser {
    fn cur_kind(&self) -> TokKind {
        if self.pos < self.tokens.len() {
            clone_tok_kind(&self.tokens[self.pos].kind)
        } else {
            TokKind::Eof
        }
    }

    fn cur_had_nl(&self) -> bool {
        if self.pos < self.tokens.len() {
            self.tokens[self.pos].had_newline
        } else {
            true
        }
    }

    fn peek_kind_at(&self, offset: usize) -> TokKind {
        if offset <= self.tokens.len() && self.pos < self.tokens.len() - offset {
            clone_tok_kind(&self.tokens[self.pos + offset].kind)
        } else {
            TokKind::Eof
        }
    }

    fn peek_nl_at(&self, offset: usize) -> bool {
        if offset <= self.tokens.len() && self.pos < self.tokens.len() - offset {
            self.tokens[self.pos + offset].had_newline
        } else {
            true
        }
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    fn record_var(&mut self, name: &JsStr) {
        if let Some(mut top) = self.var_scopes.pop() {
            push_unique_str(&mut top, clone_js_str(name));
            self.var_scopes.push(top);
        }
    }

    fn eat_semi(&mut self) -> Result<(), JsStr> {
        let k = self.cur_kind();
        if matches!(k, TokKind::Semi) {
            self.advance();
            Ok(())
        } else if self.cur_had_nl() || matches!(k, TokKind::RBrace | TokKind::Eof) {
            Ok(())
        } else {
            Err(syntax_err_msg(b"Automatic semicolon insertion failed: expected ';'"))
        }
    }

    fn parse_binding_ident(&mut self) -> PRes<JsStr> {
        let k = self.cur_kind();
        match k {
            TokKind::Ident(s) => {
                if self.strict && is_strict_restricted_ident(&s) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Cannot bind eval or arguments in strict mode"));
                }
                self.advance();
                PRes::Ok(s)
            }
            TokKind::Keyword { kw: Kw::Let, raw } => {
                if self.strict {
                    return PRes::SyntaxErr(syntax_err_msg(b"'let' is reserved in strict mode"));
                }
                self.advance();
                PRes::Ok(raw)
            }
            TokKind::LBracket | TokKind::LBrace => PRes::Unsup(UnsupportedFeature::DestructuringPattern),
            TokKind::Unsupported(f) => PRes::Unsup(f),
            _ => PRes::SyntaxErr(syntax_err_msg(b"Expected identifier")),
        }
    }

    fn parse_ident_name(&mut self) -> PRes<JsStr> {
        let k = self.cur_kind();
        match k {
            TokKind::Ident(s) => {
                self.advance();
                PRes::Ok(s)
            }
            TokKind::Keyword { raw, .. } => {
                self.advance();
                PRes::Ok(raw)
            }
            TokKind::Unsupported(f) => PRes::Unsup(f),
            _ => PRes::SyntaxErr(syntax_err_msg(b"Expected property identifier name")),
        }
    }

    fn find_label(&self, target: &JsStr) -> Option<bool> {
        let n = self.labels.len();
        let mut i = n;
        while i > 0
            invariant i <= n == self.labels@.len(),
            decreases i,
        {
            i -= 1;
            if js_str_eq(&self.labels[i].0, target) {
                return Some(self.labels[i].1);
            }
        }
        None
    }

    fn detect_directive_prologue_strict(&self, start_pos: usize) -> bool {
        let n = self.tokens.len();
        if start_pos >= n {
            return false;
        }
        let mut idx = start_pos;
        while idx < n
            invariant start_pos <= idx <= n == self.tokens@.len(),
            decreases n - idx,
        {
            match &self.tokens[idx].kind {
                TokKind::Str { val, has_escape, .. } => {
                    // Must be followed by `;`, newline, or `}` to be an ExpressionStatement directive!
                    let next_ok = if idx + 1 >= n {
                        true
                    } else {
                        matches!(self.tokens[idx + 1].kind, TokKind::Semi | TokKind::RBrace | TokKind::Eof)
                            || self.tokens[idx + 1].had_newline
                    };
                    if !next_ok {
                        return false;
                    }
                    if !*has_escape && eq_ascii(val, b"use strict") {
                        return true;
                    }
                    idx += 1;
                    if idx < n && matches!(self.tokens[idx].kind, TokKind::Semi) {
                        idx += 1;
                    }
                }
                _ => return false,
            }
        }
        false
    }

    // -----------------------------------------------------------------------
    // Expression Parsing (`decreases p_fuel`)
    // -----------------------------------------------------------------------

    fn parse_expr(&mut self, allow_in: bool, p_fuel: usize) -> (r: PRes<ExprId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let first = match self.parse_assign_expr(allow_in, p_fuel - 1) {
            PRes::Ok(e) => e,
            other => return other,
        };
        if !matches!(self.cur_kind(), TokKind::Comma) {
            return PRes::Ok(first);
        }
        let mut exprs: Vec<ExprId> = Vec::new();
        exprs.push(first);
        let mut rem_fuel = p_fuel - 1;
        while matches!(self.cur_kind(), TokKind::Comma)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            self.advance();
            match self.parse_assign_expr(allow_in, rem_fuel - 1) {
                PRes::Ok(e) => exprs.push(e),
                other => return other,
            }
            rem_fuel -= 1;
        }
        PRes::Ok(self.prog.push_expr(ExprNode::Sequence { exprs }))
    }

    fn parse_assign_expr(&mut self, allow_in: bool, p_fuel: usize) -> (r: PRes<ExprId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        // Check single-identifier arrow `x => ...`
        if let TokKind::Ident(param) = self.cur_kind() {
            if matches!(self.peek_kind_at(1), TokKind::Arrow) && !self.peek_nl_at(1) {
                if self.strict && is_strict_restricted_ident(&param) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict arrow parameter"));
                }
                self.advance(); // ident
                self.advance(); // =>
                let mut params: Vec<JsStr> = Vec::new();
                params.push(param);
                return self.parse_arrow_body(params, allow_in, p_fuel - 1);
            }
        }
        // Check parenthesized arrow `(a, b) => ...` or `() => ...`
        if matches!(self.cur_kind(), TokKind::LParen) {
            match scan_arrow_params(&self.tokens, self.pos, self.strict) {
                PRes::Unsup(f) => return PRes::Unsup(f),
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Ok(Some((body_pos, params))) => {
                    self.pos = body_pos;
                    return self.parse_arrow_body(params, allow_in, p_fuel - 1);
                }
                PRes::Ok(None) => {}
            }
        }

        let (lhs, lhs_parenthesized) = match self.parse_cond_expr(allow_in, p_fuel - 1) {
            PRes::Ok(pair) => pair,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };

        let ck = self.cur_kind();
        if let Some(op) = assign_op_of(&ck) {
            self.advance();
            let rhs = match self.parse_assign_expr(allow_in, p_fuel - 1) {
                PRes::Ok(r) => r,
                other => return other,
            };
            if lhs.0 >= self.prog.exprs.len() {
                return PRes::SyntaxErr(syntax_err_msg(b"Invalid assignment target"));
            }
            match &self.prog.exprs[lhs.0] {
                ExprNode::Ident(nm) => {
                    let name = clone_js_str(nm);
                    if self.strict && is_strict_restricted_ident(&name) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Cannot assign to eval or arguments in strict mode"));
                    }
                    PRes::Ok(self.prog.push_expr(ExprNode::AssignIdent { op, name, rhs }))
                }
                ExprNode::Member { obj, prop, optional } => {
                    if *optional || lhs_parenthesized && *optional {
                        return PRes::SyntaxErr(syntax_err_msg(b"Optional chain cannot be assignment target"));
                    }
                    let o = *obj;
                    let p = *prop;
                    PRes::Ok(self.prog.push_expr(ExprNode::AssignMember { op, obj: o, prop: p, rhs }))
                }
                _ => PRes::SyntaxErr(syntax_err_msg(b"Invalid left-hand side in assignment")),
            }
        } else {
            PRes::Ok(lhs)
        }
    }

    fn parse_arrow_body(&mut self, params: Vec<JsStr>, allow_in: bool, p_fuel: usize) -> (r: PRes<ExprId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let saved_in_fn = self.in_function;
        let saved_strict = self.strict;
        let saved_loop = self.loop_depth;
        let saved_switch = self.switch_depth;
        let saved_labels_len = self.labels.len();

        self.in_function = true;
        self.loop_depth = 0;
        self.switch_depth = 0;
        self.var_scopes.push(Vec::new());

        let (body_stmts, fn_strict) = if matches!(self.cur_kind(), TokKind::LBrace) {
            self.advance(); // {
            let dir_strict = self.strict || self.detect_directive_prologue_strict(self.pos);
            self.strict = dir_strict;
            match self.parse_stmt_list_checked(&params, true, p_fuel - 1) {
                PRes::Ok(stmts) => {
                    if !matches!(self.cur_kind(), TokKind::RBrace) {
                        self.var_scopes.pop();
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected '}' after arrow body"));
                    }
                    self.advance();
                    (stmts, dir_strict)
                }
                PRes::SyntaxErr(m) => {
                    self.var_scopes.pop();
                    return PRes::SyntaxErr(m);
                }
                PRes::Unsup(f) => {
                    self.var_scopes.pop();
                    return PRes::Unsup(f);
                }
            }
        } else {
            let expr = match self.parse_assign_expr(allow_in, p_fuel - 1) {
                PRes::Ok(e) => e,
                PRes::SyntaxErr(m) => {
                    self.var_scopes.pop();
                    return PRes::SyntaxErr(m);
                }
                PRes::Unsup(f) => {
                    self.var_scopes.pop();
                    return PRes::Unsup(f);
                }
            };
            let ret_stmt = self.prog.push_stmt(StmtNode::Return(Some(expr)));
            let mut stmts: Vec<StmtId> = Vec::new();
            stmts.push(ret_stmt);
            (stmts, saved_strict)
        };

        let hoisted_vars = match self.var_scopes.pop() {
            Some(v) => v,
            None => Vec::new(),
        };
        while self.labels.len() > saved_labels_len
            decreases self.labels@.len(),
        {
            self.labels.pop();
        }
        self.in_function = saved_in_fn;
        self.strict = saved_strict;
        self.loop_depth = saved_loop;
        self.switch_depth = saved_switch;

        let fid = self.prog.push_func(FuncDef {
            name: None,
            params,
            body: body_stmts,
            strict: fn_strict,
            is_arrow: true,
            hoisted_vars,
        });
        PRes::Ok(self.prog.push_expr(ExprNode::FuncExpr { func: fid }))
    }

    fn parse_cond_expr(&mut self, allow_in: bool, p_fuel: usize) -> (r: PRes<(ExprId, bool)>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let (cond, paren, _) = match self.parse_bin_expr(1, allow_in, p_fuel - 1) {
            PRes::Ok(t) => t,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        if matches!(self.cur_kind(), TokKind::Question) {
            self.advance();
            let then_expr = match self.parse_assign_expr(true, p_fuel - 1) {
                PRes::Ok(e) => e,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if !matches!(self.cur_kind(), TokKind::Colon) {
                return PRes::SyntaxErr(syntax_err_msg(b"Expected ':' in conditional expression"));
            }
            self.advance();
            let else_expr = match self.parse_assign_expr(allow_in, p_fuel - 1) {
                PRes::Ok(e) => e,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            let id = self.prog.push_expr(ExprNode::Conditional { cond, then_expr, else_expr });
            PRes::Ok((id, false))
        } else {
            PRes::Ok((cond, paren))
        }
    }

    /// Returns `(expr_id, is_parenthesized, top_logical_kind)` where `top_logical_kind`:
    /// `0 = none`, `1 = && or ||`, `2 = ??` (to enforce ECMA-262 unparenthesized `??` mixing early error!).
    fn parse_bin_expr(&mut self, min_prec: u8, allow_in: bool, p_fuel: usize) -> (r: PRes<(ExprId, bool, u8)>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let (mut lhs, mut lhs_paren, mut lhs_is_unary) = match self.parse_unary_expr(p_fuel - 1) {
            PRes::Ok(t) => t,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        let mut lhs_log_kind: u8 = 0;
        let mut rem_fuel = p_fuel - 1;

        while rem_fuel > 0
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            let ck = self.cur_kind();
            let Some((prec, right_assoc, bin_opt, log_opt)) = binop_info(&ck, allow_in) else {
                break;
            };
            if prec < min_prec {
                break;
            }
            // Early error: unparenthesized unary operand on LHS of `**` (`-x ** y`)!
            if matches!(bin_opt, Some(BinOp::Exp)) && lhs_is_unary && !lhs_paren {
                return PRes::SyntaxErr(syntax_err_msg(b"Unary operator used immediately before exponentiation expression"));
            }
            self.advance();
            let next_min = if right_assoc { prec } else { prec + 1 };
            let (rhs, rhs_paren, _) = match self.parse_bin_expr(next_min, allow_in, rem_fuel - 1) {
                PRes::Ok(t) => t,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if let Some(lop) = log_opt {
                let cur_kind: u8 = match lop {
                    LogicalOp::Nullish => 2,
                    _ => 1,
                };
                if !lhs_paren && lhs_log_kind != 0 && lhs_log_kind != cur_kind {
                    return PRes::SyntaxErr(syntax_err_msg(b"Cannot mix '??' with '&&' or '||' without parentheses"));
                }
                if !rhs_paren && rhs.0 < self.prog.exprs.len() {
                    if let ExprNode::Logical { op: rop, .. } = &self.prog.exprs[rhs.0] {
                        let rkind: u8 = match rop {
                            LogicalOp::Nullish => 2,
                            _ => 1,
                        };
                        if rkind != cur_kind {
                            return PRes::SyntaxErr(syntax_err_msg(b"Cannot mix '??' with '&&' or '||' without parentheses"));
                        }
                    }
                }
                lhs = self.prog.push_expr(ExprNode::Logical { op: lop, lhs, rhs });
                lhs_log_kind = cur_kind;
            } else if let Some(bop) = bin_opt {
                // Note: `BinOp::Minus` vs `BinOp::Sub`:
                lhs = self.prog.push_expr(ExprNode::Binary { op: bop, lhs, rhs });
                lhs_log_kind = 0;
            }
            lhs_paren = false;
            lhs_is_unary = false;
            rem_fuel -= 1;
        }
        PRes::Ok((lhs, lhs_paren, lhs_log_kind))
    }

    fn parse_unary_expr(&mut self, p_fuel: usize) -> (r: PRes<(ExprId, bool, bool)>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let ck = self.cur_kind();
        match ck {
            TokKind::Keyword { kw: Kw::Delete, .. } => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                if arg.0 < self.prog.exprs.len() {
                    match &self.prog.exprs[arg.0] {
                        ExprNode::Ident(nm) => {
                            if self.strict {
                                return PRes::SyntaxErr(syntax_err_msg(b"Delete of an unqualified identifier in strict mode"));
                            }
                            let name = clone_js_str(nm);
                            let id = self.prog.push_expr(ExprNode::DeleteIdent(name));
                            return PRes::Ok((id, false, true));
                        }
                        ExprNode::Member { obj, prop, .. } => {
                            let o = *obj;
                            let p = *prop;
                            let id = self.prog.push_expr(ExprNode::DeleteMember { obj: o, prop: p });
                            return PRes::Ok((id, false, true));
                        }
                        ExprNode::OptChain { head, steps, .. } => {
                            let h = *head;
                            let cs = clone_chain_steps(steps);
                            let id = self.prog.push_expr(ExprNode::OptChain { head: h, steps: cs, is_delete: true });
                            return PRes::Ok((id, false, true));
                        }
                        _ => {}
                    }
                }
                let id = self.prog.push_expr(ExprNode::Unary { op: UnaryOp::Delete, arg });
                PRes::Ok((id, false, true))
            }
            TokKind::Keyword { kw: Kw::Typeof, .. } => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                if arg.0 < self.prog.exprs.len() {
                    if let ExprNode::Ident(nm) = &self.prog.exprs[arg.0] {
                        let name = clone_js_str(nm);
                        let id = self.prog.push_expr(ExprNode::TypeofIdent(name));
                        return PRes::Ok((id, false, true));
                    }
                }
                let id = self.prog.push_expr(ExprNode::Unary { op: UnaryOp::Typeof, arg });
                PRes::Ok((id, false, true))
            }
            TokKind::Keyword { kw: Kw::Void, .. } => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                PRes::Ok((self.prog.push_expr(ExprNode::Unary { op: UnaryOp::Void, arg }), false, true))
            }
            TokKind::Bang => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                PRes::Ok((self.prog.push_expr(ExprNode::Unary { op: UnaryOp::LogicalNot, arg }), false, true))
            }
            TokKind::Tilde => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                PRes::Ok((self.prog.push_expr(ExprNode::Unary { op: UnaryOp::BitNot, arg }), false, true))
            }
            TokKind::Plus => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                PRes::Ok((self.prog.push_expr(ExprNode::Unary { op: UnaryOp::Plus, arg }), false, true))
            }
            TokKind::Minus => {
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                PRes::Ok((self.prog.push_expr(ExprNode::Unary { op: UnaryOp::Minus, arg }), false, true))
            }
            TokKind::PlusPlus | TokKind::MinusMinus => {
                let uop = if matches!(ck, TokKind::PlusPlus) { UpdateOp::Inc } else { UpdateOp::Dec };
                self.advance();
                let (arg, _, _) = match self.parse_unary_expr(p_fuel - 1) {
                    PRes::Ok(t) => t,
                    other => return other,
                };
                match self.make_update_node(uop, true, arg) {
                    PRes::Ok(id) => PRes::Ok((id, false, false)),
                    PRes::SyntaxErr(m) => PRes::SyntaxErr(m),
                    PRes::Unsup(f) => PRes::Unsup(f),
                }
            }
            TokKind::Keyword { kw: Kw::Await, .. } => PRes::Unsup(UnsupportedFeature::AwaitExpression),
            TokKind::Keyword { kw: Kw::Yield, .. } => PRes::Unsup(UnsupportedFeature::YieldExpression),
            _ => {
                let (expr, paren) = match self.parse_lhs_expr(true, p_fuel - 1) {
                    PRes::Ok(t) => t,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                // Postfix `[no LineTerminator here] ++` / `--`
                if !self.cur_had_nl() && matches!(self.cur_kind(), TokKind::PlusPlus | TokKind::MinusMinus) {
                    let uop = if matches!(self.cur_kind(), TokKind::PlusPlus) { UpdateOp::Inc } else { UpdateOp::Dec };
                    self.advance();
                    match self.make_update_node(uop, false, expr) {
                        PRes::Ok(id) => PRes::Ok((id, false, false)),
                        PRes::SyntaxErr(m) => PRes::SyntaxErr(m),
                        PRes::Unsup(f) => PRes::Unsup(f),
                    }
                } else {
                    PRes::Ok((expr, paren, false))
                }
            }
        }
    }

    fn make_update_node(&mut self, op: UpdateOp, prefix: bool, target: ExprId) -> PRes<ExprId> {
        if target.0 >= self.prog.exprs.len() {
            return PRes::SyntaxErr(syntax_err_msg(b"Invalid update expression operand"));
        }
        match &self.prog.exprs[target.0] {
            ExprNode::Ident(nm) => {
                let name = clone_js_str(nm);
                if self.strict && is_strict_restricted_ident(&name) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict mode update target"));
                }
                PRes::Ok(self.prog.push_expr(ExprNode::UpdateIdent { op, prefix, name }))
            }
            ExprNode::Member { obj, prop, optional } => {
                if *optional {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid optional chain in update expression"));
                }
                let o = *obj;
                let p = *prop;
                PRes::Ok(self.prog.push_expr(ExprNode::UpdateMember { op, prefix, obj: o, prop: p }))
            }
            _ => PRes::SyntaxErr(syntax_err_msg(b"Invalid left-hand side expression in prefix/postfix operation")),
        }
    }

    fn parse_lhs_expr(&mut self, allow_calls: bool, p_fuel: usize) -> (r: PRes<(ExprId, bool)>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let (mut base, mut paren) = if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::New, .. }) {
            self.advance();
            let (callee, _) = match self.parse_lhs_expr(false, p_fuel - 1) {
                PRes::Ok(t) => t,
                other => return other,
            };
            let args = if matches!(self.cur_kind(), TokKind::LParen) {
                match self.parse_arg_list(p_fuel - 1) {
                    PRes::Ok(a) => a,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                }
            } else {
                Vec::new()
            };
            (self.prog.push_expr(ExprNode::New { callee, args }), false)
        } else {
            match self.parse_primary_expr(p_fuel - 1) {
                PRes::Ok(t) => t,
                other => return other,
            }
        };

        let mut opt_head: Option<ExprId> = None;
        let mut opt_steps: Vec<ChainStep> = Vec::new();
        let mut rem_fuel = p_fuel - 1;
        while rem_fuel > 0
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            let ck = self.cur_kind();
            if matches!(ck, TokKind::QuestionDot) {
                if !allow_calls {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid optional chain in new expression"));
                }
                if opt_head.is_none() {
                    if !paren && base.0 < self.prog.exprs.len() {
                        if let ExprNode::Member { obj, prop, optional: false } = &self.prog.exprs[base.0] {
                            let o = *obj;
                            let p = *prop;
                            opt_head = Some(o);
                            opt_steps.push(ChainStep::Member { prop: p, optional: false });
                        } else {
                            opt_head = Some(base);
                        }
                    } else {
                        opt_head = Some(base);
                    }
                }
                self.advance();
                if matches!(self.cur_kind(), TokKind::LBracket) {
                    self.advance();
                    let prop = match self.parse_expr(true, rem_fuel - 1) {
                        PRes::Ok(e) => e,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if !matches!(self.cur_kind(), TokKind::RBracket) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected ']'"));
                    }
                    self.advance();
                    opt_steps.push(ChainStep::Member { prop, optional: true });
                } else if matches!(self.cur_kind(), TokKind::LParen) {
                    let is_direct_opt_eval = if !paren && opt_steps.len() == 0 {
                        match opt_head {
                            Some(h) => if h.0 < self.prog.exprs.len() {
                                match &self.prog.exprs[h.0] {
                                    ExprNode::Ident(nm) => eq_ascii(nm, b"eval"),
                                    _ => false,
                                }
                            } else { false },
                            None => false,
                        }
                    } else {
                        false
                    };
                    let args = match self.parse_arg_list(rem_fuel - 1) {
                        PRes::Ok(a) => a,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if is_direct_opt_eval {
                        return PRes::Unsup(UnsupportedFeature::EvalDirectCall);
                    }
                    opt_steps.push(ChainStep::Call { args, optional: true });
                } else {
                    let pname = match self.parse_ident_name() {
                        PRes::Ok(s) => s,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    let prop = self.prog.push_expr(ExprNode::LitStr(pname));
                    opt_steps.push(ChainStep::Member { prop, optional: true });
                }
                paren = false;
                rem_fuel -= 1;
            } else if matches!(ck, TokKind::Dot) {
                self.advance();
                let pname = match self.parse_ident_name() {
                    PRes::Ok(s) => s,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                let prop = self.prog.push_expr(ExprNode::LitStr(pname));
                if opt_head.is_some() {
                    opt_steps.push(ChainStep::Member { prop, optional: false });
                } else if allow_calls && matches!(self.cur_kind(), TokKind::LParen) {
                    let args = match self.parse_arg_list(rem_fuel - 1) {
                        PRes::Ok(a) => a,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    base = self.prog.push_expr(ExprNode::CallMethod { obj: base, prop, optional: false, optional_call: false, args });
                } else {
                    base = self.prog.push_expr(ExprNode::Member { obj: base, prop, optional: false });
                }
                paren = false;
                rem_fuel -= 1;
            } else if matches!(ck, TokKind::LBracket) {
                self.advance();
                let prop = match self.parse_expr(true, rem_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if !matches!(self.cur_kind(), TokKind::RBracket) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected ']' in computed member expression"));
                }
                self.advance();
                if opt_head.is_some() {
                    opt_steps.push(ChainStep::Member { prop, optional: false });
                } else if allow_calls && matches!(self.cur_kind(), TokKind::LParen) {
                    let args = match self.parse_arg_list(rem_fuel - 1) {
                        PRes::Ok(a) => a,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    base = self.prog.push_expr(ExprNode::CallMethod { obj: base, prop, optional: false, optional_call: false, args });
                } else {
                    base = self.prog.push_expr(ExprNode::Member { obj: base, prop, optional: false });
                }
                paren = false;
                rem_fuel -= 1;
            } else if allow_calls && matches!(ck, TokKind::LParen) {
                if opt_head.is_some() {
                    let args = match self.parse_arg_list(rem_fuel - 1) {
                        PRes::Ok(a) => a,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    opt_steps.push(ChainStep::Call { args, optional: false });
                } else {
                    let is_direct_eval = if !paren && base.0 < self.prog.exprs.len() {
                        match &self.prog.exprs[base.0] {
                            ExprNode::Ident(nm) => eq_ascii(nm, b"eval"),
                            _ => false,
                        }
                    } else {
                        false
                    };
                    let args = match self.parse_arg_list(rem_fuel - 1) {
                        PRes::Ok(a) => a,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if is_direct_eval {
                        base = self.prog.push_expr(ExprNode::UnsupportedExpr(UnsupportedFeature::EvalDirectCall));
                    } else if !paren && base.0 < self.prog.exprs.len() {
                        if let ExprNode::Member { obj, prop, optional } = &self.prog.exprs[base.0] {
                            let o = *obj;
                            let p = *prop;
                            let opt = *optional;
                            base = self.prog.push_expr(ExprNode::CallMethod { obj: o, prop: p, optional: opt, optional_call: false, args });
                        } else {
                            base = self.prog.push_expr(ExprNode::Call { callee: base, optional: false, args });
                        }
                    } else {
                        base = self.prog.push_expr(ExprNode::Call { callee: base, optional: false, args });
                    }
                }
                paren = false;
                rem_fuel -= 1;
            } else {
                break;
            }
        }
        if let Some(head) = opt_head {
            base = self.prog.push_expr(ExprNode::OptChain { head, steps: opt_steps, is_delete: false });
            paren = false;
        }
        PRes::Ok((base, paren))
    }

    fn parse_arg_list(&mut self, p_fuel: usize) -> (r: PRes<Vec<ExprId>>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        self.advance(); // consume `(`
        let mut args: Vec<ExprId> = Vec::new();
        let mut rem_fuel = p_fuel - 1;
        while !matches!(self.cur_kind(), TokKind::RParen | TokKind::Eof)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            if matches!(self.cur_kind(), TokKind::Ellipsis) {
                return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
            }
            match self.parse_assign_expr(true, rem_fuel - 1) {
                PRes::Ok(e) => args.push(e),
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            }
            rem_fuel -= 1;
            if matches!(self.cur_kind(), TokKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after argument list"));
        }
        self.advance();
        PRes::Ok(args)
    }

    fn parse_primary_expr(&mut self, p_fuel: usize) -> (r: PRes<(ExprId, bool)>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let ck = self.cur_kind();
        match ck {
            TokKind::Num { val, legacy_octal } => {
                if self.strict && legacy_octal {
                    return PRes::SyntaxErr(syntax_err_msg(b"Octal numeric literals are not allowed in strict mode"));
                }
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::LitNum(val)), false))
            }
            TokKind::Str { val, has_legacy_octal_escape, .. } => {
                if self.strict && has_legacy_octal_escape {
                    return PRes::SyntaxErr(syntax_err_msg(b"Octal escape sequences are not allowed in strict mode"));
                }
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::LitStr(val)), false))
            }
            TokKind::Keyword { kw: Kw::True, .. } => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::LitBool(true)), false))
            }
            TokKind::Keyword { kw: Kw::False, .. } => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::LitBool(false)), false))
            }
            TokKind::Keyword { kw: Kw::Null, .. } => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::LitNull), false))
            }
            TokKind::Keyword { kw: Kw::This, .. } => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::This), false))
            }
            TokKind::Ident(s) => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::Ident(s)), false))
            }
            TokKind::Keyword { kw: Kw::Let, raw } => {
                if self.strict {
                    return PRes::SyntaxErr(syntax_err_msg(b"Unexpected strict mode reserved word 'let'"));
                }
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::Ident(raw)), false))
            }
            TokKind::LParen => {
                self.advance();
                let inner = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if !matches!(self.cur_kind(), TokKind::RParen) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected ')'"));
                }
                self.advance();
                PRes::Ok((inner, true))
            }
            TokKind::LBracket => {
                self.advance();
                let mut elements: Vec<Option<ExprId>> = Vec::new();
                let mut rem_fuel = p_fuel - 1;
                while !matches!(self.cur_kind(), TokKind::RBracket | TokKind::Eof)
                    invariant rem_fuel < p_fuel,
                    decreases rem_fuel,
                {
                    if rem_fuel == 0 {
                        return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
                    }
                    if matches!(self.cur_kind(), TokKind::Comma) {
                        elements.push(None);
                        self.advance();
                        rem_fuel -= 1;
                    } else if matches!(self.cur_kind(), TokKind::Ellipsis) {
                        return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
                    } else {
                        match self.parse_assign_expr(true, rem_fuel - 1) {
                            PRes::Ok(e) => elements.push(Some(e)),
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        }
                        rem_fuel -= 1;
                        if matches!(self.cur_kind(), TokKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                if !matches!(self.cur_kind(), TokKind::RBracket) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected ']' in array literal"));
                }
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::ArrayLit { elements }), false))
            }
            TokKind::LBrace => {
                self.advance();
                let mut props: Vec<PropInit> = Vec::new();
                let mut rem_fuel = p_fuel - 1;
                while !matches!(self.cur_kind(), TokKind::RBrace | TokKind::Eof)
                    invariant rem_fuel < p_fuel,
                    decreases rem_fuel,
                {
                    if rem_fuel == 0 {
                        return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
                    }
                    if matches!(self.cur_kind(), TokKind::Ellipsis) {
                        return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
                    }
                    let (key, shorthand_ident): (PropKeyInit, Option<JsStr>) = if matches!(self.cur_kind(), TokKind::LBracket) {
                        self.advance();
                        let ce = match self.parse_assign_expr(true, rem_fuel - 1) {
                            PRes::Ok(e) => e,
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        };
                        if !matches!(self.cur_kind(), TokKind::RBracket) {
                            return PRes::SyntaxErr(syntax_err_msg(b"Expected ']' in computed property key"));
                        }
                        self.advance();
                        (PropKeyInit::Computed(ce), None)
                    } else if let TokKind::Str { val, has_legacy_octal_escape, .. } = self.cur_kind() {
                        if self.strict && has_legacy_octal_escape {
                            return PRes::SyntaxErr(syntax_err_msg(b"Octal escape sequences are not allowed in strict mode"));
                        }
                        self.advance();
                        (PropKeyInit::Static(val), None)
                    } else if let TokKind::Num { val: num, legacy_octal } = self.cur_kind() {
                        if self.strict && legacy_octal {
                            return PRes::SyntaxErr(syntax_err_msg(b"Octal numeric literals are not allowed in strict mode"));
                        }
                        self.advance();
                        (PropKeyInit::Static(crate::value::number_to_js_str(num)), None)
                    } else if let TokKind::Ident(s) = self.cur_kind() {
                        self.advance();
                        let s2 = clone_js_str(&s);
                        (PropKeyInit::Static(s), Some(s2))
                    } else {
                        match self.parse_ident_name() {
                            PRes::Ok(s) => (PropKeyInit::Static(s), None),
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        }
                    };

                    if matches!(self.cur_kind(), TokKind::Colon) {
                        self.advance();
                        let val = match self.parse_assign_expr(true, rem_fuel - 1) {
                            PRes::Ok(e) => e,
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        };
                        props.push(PropInit { key, val });
                    } else if matches!(self.cur_kind(), TokKind::LParen) {
                        // Concise object method `{ m(a, b) { ... } }`
                        let fid = match self.parse_function_common(None, rem_fuel - 1) {
                            PRes::Ok(f) => f,
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(u) => return PRes::Unsup(u),
                        };
                        let val = self.prog.push_expr(ExprNode::FuncExpr { func: fid });
                        props.push(PropInit { key, val });
                    } else if let Some(id_name) = shorthand_ident {
                        if self.strict && is_strict_restricted_ident(&id_name) && false {
                            // Reading `eval`/`arguments` in `{ eval }` is valid; only binding is restricted
                        }
                        let val = self.prog.push_expr(ExprNode::Ident(id_name));
                        props.push(PropInit { key, val });
                    } else {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected ':' in object literal"));
                    }
                    rem_fuel -= 1;
                    if matches!(self.cur_kind(), TokKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                if !matches!(self.cur_kind(), TokKind::RBrace) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected '}' in object literal"));
                }
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::ObjectLit { props }), false))
            }
            TokKind::Keyword { kw: Kw::Function, .. } => {
                self.advance();
                if matches!(self.cur_kind(), TokKind::Star) {
                    return PRes::Unsup(UnsupportedFeature::GeneratorFunction);
                }
                let opt_name = if !matches!(self.cur_kind(), TokKind::LParen) {
                    match self.parse_binding_ident() {
                        PRes::Ok(nm) => Some(nm),
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    }
                } else {
                    None
                };
                match self.parse_function_common(opt_name, p_fuel - 1) {
                    PRes::Ok(fid) => PRes::Ok((self.prog.push_expr(ExprNode::FuncExpr { func: fid }), false)),
                    PRes::SyntaxErr(m) => PRes::SyntaxErr(m),
                    PRes::Unsup(f) => PRes::Unsup(f),
                }
            }
            TokKind::Keyword { kw: Kw::Async, .. } => PRes::Unsup(UnsupportedFeature::AsyncFunction),
            TokKind::Keyword { kw: Kw::Class, .. } => PRes::Unsup(UnsupportedFeature::ClassSyntax),
            TokKind::Keyword { kw: Kw::Super, .. } => PRes::Unsup(UnsupportedFeature::SuperKeyword),
            TokKind::Unsupported(f) => {
                self.advance();
                PRes::Ok((self.prog.push_expr(ExprNode::UnsupportedExpr(f)), false))
            }
            _ => PRes::SyntaxErr(syntax_err_msg(b"Unexpected token in primary expression")),
        }
    }

    fn parse_function_common(&mut self, name: Option<JsStr>, p_fuel: usize) -> (r: PRes<FuncId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        if !matches!(self.cur_kind(), TokKind::LParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' in function declaration/expression"));
        }
        self.advance();
        let mut params: Vec<JsStr> = Vec::new();
        let mut rem_fuel = p_fuel - 1;
        while !matches!(self.cur_kind(), TokKind::RParen | TokKind::Eof)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            if matches!(self.cur_kind(), TokKind::Ellipsis | TokKind::LBracket | TokKind::LBrace) {
                return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
            }
            let p = match self.parse_binding_ident() {
                PRes::Ok(nm) => nm,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if matches!(self.cur_kind(), TokKind::Eq) {
                return PRes::Unsup(UnsupportedFeature::DestructuringPattern);
            }
            params.push(p);
            rem_fuel -= 1;
            if matches!(self.cur_kind(), TokKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after formal parameters"));
        }
        self.advance();
        if !matches!(self.cur_kind(), TokKind::LBrace) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '{' before function body"));
        }
        self.advance();

        let fn_strict = self.strict || self.detect_directive_prologue_strict(self.pos);
        if fn_strict {
            if let Some(ref fnm) = name {
                if is_strict_restricted_ident(fnm) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict mode function name"));
                }
            }
            let mut seen: Vec<JsStr> = Vec::new();
            let mut pi: usize = 0;
            while pi < params.len()
                invariant pi <= params@.len(),
                decreases params@.len() - pi,
            {
                if is_strict_restricted_ident(&params[pi]) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict mode formal parameter name"));
                }
                if vec_contains_str(&seen, &params[pi]) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Duplicate parameter name not allowed in strict mode"));
                }
                seen.push(clone_js_str(&params[pi]));
                pi += 1;
            }
        }

        let saved_in_fn = self.in_function;
        let saved_strict = self.strict;
        let saved_loop = self.loop_depth;
        let saved_switch = self.switch_depth;
        let saved_labels_len = self.labels.len();

        self.in_function = true;
        self.strict = fn_strict;
        self.loop_depth = 0;
        self.switch_depth = 0;
        self.var_scopes.push(Vec::new());

        let body = match self.parse_stmt_list_checked(&params, true, p_fuel - 1) {
            PRes::Ok(stmts) => stmts,
            PRes::SyntaxErr(m) => {
                self.var_scopes.pop();
                return PRes::SyntaxErr(m);
            }
            PRes::Unsup(f) => {
                self.var_scopes.pop();
                return PRes::Unsup(f);
            }
        };

        if !matches!(self.cur_kind(), TokKind::RBrace) {
            self.var_scopes.pop();
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '}' after function body"));
        }
        self.advance();

        let hoisted_vars = match self.var_scopes.pop() {
            Some(v) => v,
            None => Vec::new(),
        };
        while self.labels.len() > saved_labels_len
            decreases self.labels@.len(),
        {
            self.labels.pop();
        }
        self.in_function = saved_in_fn;
        self.strict = saved_strict;
        self.loop_depth = saved_loop;
        self.switch_depth = saved_switch;

        PRes::Ok(self.prog.push_func(FuncDef {
            name,
            params,
            body,
            strict: fn_strict,
            is_arrow: false,
            hoisted_vars,
        }))
    }

    // -----------------------------------------------------------------------
    // Statement List & Early Error Scope Validation (`decreases p_fuel`)
    // -----------------------------------------------------------------------

    /// Parses a sequence of statements until `}` / `case` / `default` / `EOF`, enforcing:
    /// - Duplicate `LexicallyDeclaredNames` (`let`/`const`, and block-level `function` in strict mode)
    /// - `LexicallyDeclaredNames` colliding with `BoundNames(params)` (if `is_fn_top`) or `VarDeclaredNames`!
    fn parse_stmt_list_checked(
        &mut self,
        fn_params: &Vec<JsStr>,
        stop_at_rbrace: bool,
        p_fuel: usize,
    ) -> (r: PRes<Vec<StmtId>>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let mut stmts: Vec<StmtId> = Vec::new();
        let mut lex_names: Vec<JsStr> = Vec::new();
        let vars_before: usize = if self.var_scopes.len() > 0 {
            self.var_scopes[self.var_scopes.len() - 1].len()
        } else {
            0
        };

        let mut rem_fuel = p_fuel - 1;
        while !matches!(self.cur_kind(), TokKind::Eof)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            let ck = self.cur_kind();
            if stop_at_rbrace && matches!(ck, TokKind::RBrace) {
                break;
            }
            if matches!(ck, TokKind::Keyword { kw: Kw::Case | Kw::Default, .. }) {
                break;
            }
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            let sid = match self.parse_stmt(&mut lex_names, fn_params, rem_fuel - 1) {
                PRes::Ok(s) => s,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            stmts.push(sid);
            rem_fuel -= 1;
        }

        // Early Error (§14.2.1 / §15.2.1 / §16.1.1):
        // Check `LexicallyDeclaredNames` vs `VarDeclaredNames` collected within this block/script/function!
        if self.var_scopes.len() > 0 {
            let vlist = &self.var_scopes[self.var_scopes.len() - 1];
            let start_idx = if stop_at_rbrace && fn_params.len() == 0 && vars_before <= vlist.len() {
                vars_before
            } else {
                0
            };
            let mut vi = start_idx;
            while vi < vlist.len()
                invariant vi <= vlist@.len(),
                decreases vlist@.len() - vi,
            {
                if vec_contains_str(&lex_names, &vlist[vi]) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Identifier has already been lexically declared"));
                }
                vi += 1;
            }
        }

        PRes::Ok(stmts)
    }

    fn parse_var_decl_list(
        &mut self,
        kind: VarKind,
        allow_in: bool,
        lex_names: &mut Vec<JsStr>,
        fn_params: &Vec<JsStr>,
        p_fuel: usize,
    ) -> (r: PRes<Vec<VarDeclarator>>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let mut decls: Vec<VarDeclarator> = Vec::new();
        let mut rem_fuel = p_fuel - 1;
        loop
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            let name = match self.parse_binding_ident() {
                PRes::Ok(nm) => nm,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if matches!(kind, VarKind::Let | VarKind::Const) && eq_ascii(&name, b"let") {
                return PRes::SyntaxErr(syntax_err_msg(b"'let' is disallowed as a lexically bound name"));
            }
            match kind {
                VarKind::Var => {
                    if vec_contains_str(lex_names, &name) {
                        return PRes::SyntaxErr(syntax_err_msg(b"var declaration collides with lexical declaration"));
                    }
                    self.record_var(&name);
                }
                VarKind::Let | VarKind::Const => {
                    if vec_contains_str(lex_names, &name) || vec_contains_str(fn_params, &name) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Duplicate lexical binding in scope"));
                    }
                    lex_names.push(clone_js_str(&name));
                }
            }
            let init = if matches!(self.cur_kind(), TokKind::Eq) {
                self.advance();
                match self.parse_assign_expr(allow_in, rem_fuel - 1) {
                    PRes::Ok(e) => Some(e),
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                }
            } else {
                None
            };
            decls.push(VarDeclarator { name, init });
            rem_fuel -= 1;
            if matches!(self.cur_kind(), TokKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        PRes::Ok(decls)
    }

    fn parse_stmt(
        &mut self,
        lex_names: &mut Vec<JsStr>,
        fn_params: &Vec<JsStr>,
        p_fuel: usize,
    ) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let ck = self.cur_kind();
        match ck {
            TokKind::Semi => {
                self.advance();
                PRes::Ok(self.prog.push_stmt(StmtNode::Empty))
            }
            TokKind::LBrace => {
                self.advance();
                let empty_params: Vec<JsStr> = Vec::new();
                let stmts = match self.parse_stmt_list_checked(&empty_params, true, p_fuel - 1) {
                    PRes::Ok(s) => s,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if !matches!(self.cur_kind(), TokKind::RBrace) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected '}'"));
                }
                self.advance();
                PRes::Ok(self.prog.push_stmt(StmtNode::Block { stmts }))
            }
            TokKind::Keyword { kw: Kw::Var, .. } => {
                self.advance();
                let decls = match self.parse_var_decl_list(VarKind::Var, true, lex_names, fn_params, p_fuel - 1) {
                    PRes::Ok(d) => d,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::VarDecl { kind: VarKind::Var, decls }))
            }
            TokKind::Keyword { kw: Kw::Const, .. } => {
                self.advance();
                let decls = match self.parse_var_decl_list(VarKind::Const, true, lex_names, fn_params, p_fuel - 1) {
                    PRes::Ok(d) => d,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                // Early Error (§14.3.1.1): `const` declarations MUST have an initializer!
                let mut di: usize = 0;
                while di < decls.len()
                    invariant di <= decls@.len(),
                    decreases decls@.len() - di,
                {
                    if decls[di].init.is_none() {
                        return PRes::SyntaxErr(syntax_err_msg(b"Missing initializer in const declaration"));
                    }
                    di += 1;
                }
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::VarDecl { kind: VarKind::Const, decls }))
            }
            TokKind::Keyword { kw: Kw::Let, .. } => {
                // In sloppy mode, `let` starts a lexical declaration only when followed by Ident / `[` / `{`!
                let next_k = self.peek_kind_at(1);
                let is_lex_let = matches!(next_k, TokKind::Ident(_) | TokKind::LBracket | TokKind::LBrace)
                    || matches!(next_k, TokKind::Keyword { kw: Kw::Let, .. })
                    || self.strict;
                if is_lex_let {
                    self.advance();
                    let decls = match self.parse_var_decl_list(VarKind::Let, true, lex_names, fn_params, p_fuel - 1) {
                        PRes::Ok(d) => d,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if let Err(msg) = self.eat_semi() {
                        return PRes::SyntaxErr(msg);
                    }
                    return PRes::Ok(self.prog.push_stmt(StmtNode::VarDecl { kind: VarKind::Let, decls }));
                }
                let expr = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::ExprStmt(expr)))
            }
            TokKind::Keyword { kw: Kw::Function, .. } => {
                self.advance();
                if matches!(self.cur_kind(), TokKind::Star) {
                    return PRes::Unsup(UnsupportedFeature::GeneratorFunction);
                }
                let fname = match self.parse_binding_ident() {
                    PRes::Ok(nm) => nm,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if vec_contains_str(lex_names, &fname) {
                    if self.strict {
                        return PRes::SyntaxErr(syntax_err_msg(b"Duplicate function declaration in strict block"));
                    }
                }
                let fid = match self.parse_function_common(Some(fname), p_fuel - 1) {
                    PRes::Ok(f) => f,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(u) => return PRes::Unsup(u),
                };
                PRes::Ok(self.prog.push_stmt(StmtNode::FuncDecl { func: fid }))
            }
            TokKind::Keyword { kw: Kw::If, .. } => {
                self.advance();
                if !matches!(self.cur_kind(), TokKind::LParen) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' after 'if'"));
                }
                self.advance();
                let cond = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if !matches!(self.cur_kind(), TokKind::RParen) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after 'if' condition"));
                }
                self.advance();
                let allow_fn = !self.strict;
                let then_branch = match self.parse_sub_stmt(allow_fn, p_fuel - 1) {
                    PRes::Ok(s) => s,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                let else_branch = if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Else, .. }) {
                    self.advance();
                    match self.parse_sub_stmt(allow_fn, p_fuel - 1) {
                        PRes::Ok(s) => Some(s),
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    }
                } else {
                    None
                };
                PRes::Ok(self.prog.push_stmt(StmtNode::If { cond, then_branch, else_branch }))
            }
            TokKind::Keyword { kw: Kw::While, .. } => {
                self.parse_while_stmt(Vec::new(), p_fuel - 1)
            }
            TokKind::Keyword { kw: Kw::Do, .. } => {
                self.parse_do_while_stmt(Vec::new(), p_fuel - 1)
            }
            TokKind::Keyword { kw: Kw::For, .. } => {
                self.parse_for_stmt(Vec::new(), p_fuel - 1)
            }
            TokKind::Keyword { kw: Kw::Switch, .. } => {
                self.parse_switch_stmt(None, p_fuel - 1)
            }
            TokKind::Keyword { kw: Kw::Return, .. } => {
                if !self.in_function {
                    return PRes::SyntaxErr(syntax_err_msg(b"Illegal return statement outside function"));
                }
                self.advance();
                if self.cur_had_nl() || matches!(self.cur_kind(), TokKind::Semi | TokKind::RBrace | TokKind::Eof) {
                    let _ = self.eat_semi();
                    return PRes::Ok(self.prog.push_stmt(StmtNode::Return(None)));
                }
                let val = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Return(Some(val))))
            }
            TokKind::Keyword { kw: Kw::Break, .. } => {
                self.advance();
                if self.cur_had_nl() || matches!(self.cur_kind(), TokKind::Semi | TokKind::RBrace | TokKind::Eof) {
                    if self.loop_depth == 0 && self.switch_depth == 0 {
                        return PRes::SyntaxErr(syntax_err_msg(b"Illegal unlabeled break statement"));
                    }
                    let _ = self.eat_semi();
                    return PRes::Ok(self.prog.push_stmt(StmtNode::Break(None)));
                }
                let lbl = match self.parse_binding_ident() {
                    PRes::Ok(nm) => nm,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if self.find_label(&lbl).is_none() {
                    return PRes::SyntaxErr(syntax_err_msg(b"Undefined break target label"));
                }
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Break(Some(lbl))))
            }
            TokKind::Keyword { kw: Kw::Continue, .. } => {
                self.advance();
                if self.cur_had_nl() || matches!(self.cur_kind(), TokKind::Semi | TokKind::RBrace | TokKind::Eof) {
                    if self.loop_depth == 0 {
                        return PRes::SyntaxErr(syntax_err_msg(b"Illegal unlabeled continue statement"));
                    }
                    let _ = self.eat_semi();
                    return PRes::Ok(self.prog.push_stmt(StmtNode::Continue(None)));
                }
                let lbl = match self.parse_binding_ident() {
                    PRes::Ok(nm) => nm,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                match self.find_label(&lbl) {
                    Some(true) => {}
                    _ => return PRes::SyntaxErr(syntax_err_msg(b"Illegal continue target label")),
                }
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Continue(Some(lbl))))
            }
            TokKind::Keyword { kw: Kw::Throw, .. } => {
                self.advance();
                if self.cur_had_nl() || matches!(self.cur_kind(), TokKind::Semi | TokKind::RBrace | TokKind::Eof) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Illegal newline or missing expression after throw"));
                }
                let expr = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Throw(expr)))
            }
            TokKind::Keyword { kw: Kw::Try, .. } => {
                self.advance();
                if !matches!(self.cur_kind(), TokKind::LBrace) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected '{' after 'try'"));
                }
                let mut sub_lex: Vec<JsStr> = Vec::new();
                let empty_p: Vec<JsStr> = Vec::new();
                let block = match self.parse_stmt(&mut sub_lex, &empty_p, p_fuel - 1) {
                    PRes::Ok(s) => s,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                let mut catch_param: Option<JsStr> = None;
                let mut catch_body: Option<StmtId> = None;
                let mut finally_body: Option<StmtId> = None;

                if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Catch, .. }) {
                    self.advance();
                    let mut c_params: Vec<JsStr> = Vec::new();
                    if matches!(self.cur_kind(), TokKind::LParen) {
                        self.advance();
                        let cp = match self.parse_binding_ident() {
                            PRes::Ok(nm) => nm,
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        };
                        if !matches!(self.cur_kind(), TokKind::RParen) {
                            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after catch parameter"));
                        }
                        self.advance();
                        c_params.push(clone_js_str(&cp));
                        catch_param = Some(cp);
                    }
                    if !matches!(self.cur_kind(), TokKind::LBrace) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected '{' for catch block"));
                    }
                    self.advance();
                    let c_stmts = match self.parse_stmt_list_checked(&c_params, true, p_fuel - 1) {
                        PRes::Ok(s) => s,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if !matches!(self.cur_kind(), TokKind::RBrace) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected '}' after catch block"));
                    }
                    self.advance();
                    catch_body = Some(self.prog.push_stmt(StmtNode::Block { stmts: c_stmts }));
                }
                if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Finally, .. }) {
                    self.advance();
                    if !matches!(self.cur_kind(), TokKind::LBrace) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected '{' after 'finally'"));
                    }
                    let mut sub_lex3: Vec<JsStr> = Vec::new();
                    let f_blk = match self.parse_stmt(&mut sub_lex3, &empty_p, p_fuel - 1) {
                        PRes::Ok(s) => s,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    finally_body = Some(f_blk);
                }
                if catch_body.is_none() && finally_body.is_none() {
                    return PRes::SyntaxErr(syntax_err_msg(b"Missing catch or finally after try"));
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Try { block, catch_param, catch_body, finally_body }))
            }
            TokKind::Keyword { kw: Kw::Debugger, .. } => {
                self.advance();
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::Empty))
            }
            TokKind::Keyword { kw: Kw::With, .. } => PRes::Unsup(UnsupportedFeature::WithStatement),
            TokKind::Keyword { kw: Kw::Class, .. } => PRes::Unsup(UnsupportedFeature::ClassSyntax),
            TokKind::Keyword { kw: Kw::Async, .. } => PRes::Unsup(UnsupportedFeature::AsyncFunction),
            TokKind::Keyword { kw: Kw::Import | Kw::Export, .. } => PRes::Unsup(UnsupportedFeature::ModuleSyntax),
            TokKind::Ident(_) => {
                if matches!(self.peek_kind_at(1), TokKind::Colon) {
                    self.parse_labeled_chain(p_fuel - 1)
                } else {
                    let expr = match self.parse_expr(true, p_fuel - 1) {
                        PRes::Ok(e) => e,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if let Err(msg) = self.eat_semi() {
                        return PRes::SyntaxErr(msg);
                    }
                    PRes::Ok(self.prog.push_stmt(StmtNode::ExprStmt(expr)))
                }
            }
            _ => {
                let expr = match self.parse_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if let Err(msg) = self.eat_semi() {
                    return PRes::SyntaxErr(msg);
                }
                PRes::Ok(self.prog.push_stmt(StmtNode::ExprStmt(expr)))
            }
        }
    }

    /// Enforce ECMA-262 §14.6.1 / §14.7 / §14.13.1 single-statement context early errors:
    /// Rejects `let` (lexical), `const`, `class`, `async function`, `function*`, and (unless
    /// `allow_sloppy_func && !self.strict`) `function` declarations!
    fn check_single_stmt_context(&self, allow_sloppy_func: bool) -> Result<(), JsStr> {
        let ck = self.cur_kind();
        match ck {
            TokKind::Keyword { kw: Kw::Const, .. } =>
                Err(syntax_err_msg(b"Lexical declaration cannot appear in a single-statement context")),
            TokKind::Keyword { kw: Kw::Let, .. } => {
                let nk = self.peek_kind_at(1);
                let is_lex = matches!(nk, TokKind::Ident(_) | TokKind::LBracket | TokKind::LBrace)
                    || matches!(nk, TokKind::Keyword { kw: Kw::Let, .. })
                    || self.strict;
                if is_lex {
                    Err(syntax_err_msg(b"Lexical declaration cannot appear in a single-statement context"))
                } else {
                    Ok(())
                }
            }
            TokKind::Keyword { kw: Kw::Class, .. } =>
                Err(syntax_err_msg(b"Class declaration cannot appear in a single-statement context")),
            TokKind::Keyword { kw: Kw::Function, .. } => {
                if matches!(self.peek_kind_at(1), TokKind::Star) {
                    Err(syntax_err_msg(b"Generator declaration cannot appear in a single-statement context"))
                } else if self.strict || !allow_sloppy_func {
                    Err(syntax_err_msg(b"Function declarations are not allowed in single-statement positions"))
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    fn parse_sub_stmt(&mut self, allow_sloppy_func: bool, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        if let Err(msg) = self.check_single_stmt_context(allow_sloppy_func) {
            return PRes::SyntaxErr(msg);
        }
        if allow_sloppy_func && !self.strict && matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Function, .. }) {
            // Annex B §B.3.2 / §B.3.4 sloppy-mode `if (...) function f() {}` / `lbl: function f() {}`
            if matches!(self.peek_kind_at(1), TokKind::Ident(_)) {
                if let TokKind::Ident(fnm) = self.peek_kind_at(1) {
                    self.record_var(&fnm);
                }
            }
        }
        let mut sub_lex: Vec<JsStr> = Vec::new();
        let empty_p: Vec<JsStr> = Vec::new();
        self.parse_stmt(&mut sub_lex, &empty_p, p_fuel - 1)
    }

    /// Parse one or more chained labels `l1: l2: ... stmt`, marking ALL labels in the chain
    /// with `is_iter = true` when the target statement is `while`, `do`, or `for` (§14.13).
    fn parse_labeled_chain(&mut self, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let mut chain: Vec<JsStr> = Vec::new();
        let mut rem_fuel = p_fuel - 1;
        while self.pos < self.tokens.len() && matches!(self.peek_kind_at(1), TokKind::Colon)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            let lbl = match self.cur_kind() {
                TokKind::Ident(s) => {
                    if self.strict && (eq_ascii(&s, b"let") || eq_ascii(&s, b"yield") || eq_ascii(&s, b"await")) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict-mode label identifier"));
                    }
                    s
                }
                TokKind::Keyword { kw: Kw::Let, raw } => {
                    if self.strict {
                        return PRes::SyntaxErr(syntax_err_msg(b"'let' is disallowed as a label in strict mode"));
                    }
                    raw
                }
                _ => break,
            };
            if self.find_label(&lbl).is_some() || vec_contains_str(&chain, &lbl) {
                return PRes::SyntaxErr(syntax_err_msg(b"Duplicate label"));
            }
            self.advance(); // label ident
            self.advance(); // :
            chain.push(lbl);
            rem_fuel -= 1;
        }
        if chain.len() == 0 {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected label identifier"));
        }

        let target_ck = self.cur_kind();
        let is_iter = matches!(target_ck, TokKind::Keyword { kw: Kw::While | Kw::Do | Kw::For, .. });
        let saved_labels_len = self.labels.len();
        let mut ci: usize = 0;
        while ci < chain.len()
            invariant ci <= chain@.len(),
            decreases chain@.len() - ci,
        {
            self.labels.push((clone_js_str(&chain[ci]), is_iter));
            ci += 1;
        }

        let inner_res = match target_ck {
            TokKind::Keyword { kw: Kw::While, .. } =>
                self.parse_while_stmt(clone_str_vec(&chain), p_fuel - 1),
            TokKind::Keyword { kw: Kw::Do, .. } =>
                self.parse_do_while_stmt(clone_str_vec(&chain), p_fuel - 1),
            TokKind::Keyword { kw: Kw::For, .. } =>
                self.parse_for_stmt(clone_str_vec(&chain), p_fuel - 1),
            TokKind::Keyword { kw: Kw::Switch, .. } => {
                let last_lbl = clone_js_str(&chain[chain.len() - 1]);
                self.parse_switch_stmt(Some(last_lbl), p_fuel - 1)
            }
            _ => self.parse_sub_stmt(!self.strict, p_fuel - 1),
        };

        while self.labels.len() > saved_labels_len
            decreases self.labels@.len(),
        {
            self.labels.pop();
        }

        match inner_res {
            PRes::Ok(mut body) => {
                if !is_iter {
                    let mut ri = chain.len();
                    while ri > 0
                        invariant ri <= chain@.len(),
                        decreases ri,
                    {
                        ri -= 1;
                        body = self.prog.push_stmt(StmtNode::Labeled {
                            label: clone_js_str(&chain[ri]),
                            body,
                        });
                    }
                }
                PRes::Ok(body)
            }
            other => other,
        }
    }

    fn parse_while_stmt(&mut self, labels: Vec<JsStr>, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        self.advance(); // while
        if !matches!(self.cur_kind(), TokKind::LParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' after 'while'"));
        }
        self.advance();
        let cond = match self.parse_expr(true, p_fuel - 1) {
            PRes::Ok(e) => e,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after 'while' condition"));
        }
        self.advance();
        if self.loop_depth < usize::MAX { self.loop_depth += 1; }
        let body_res = self.parse_sub_stmt(false, p_fuel - 1);
        if self.loop_depth > 0 { self.loop_depth -= 1; }
        match body_res {
            PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::While { labels, cond, body })),
            other => other,
        }
    }

    fn parse_do_while_stmt(&mut self, labels: Vec<JsStr>, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        self.advance(); // do
        if self.loop_depth < usize::MAX { self.loop_depth += 1; }
        let body = match self.parse_sub_stmt(false, p_fuel - 1) {
            PRes::Ok(b) => b,
            other => {
                if self.loop_depth > 0 { self.loop_depth -= 1; }
                return other;
            }
        };
        if self.loop_depth > 0 { self.loop_depth -= 1; }
        if !matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::While, .. }) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected 'while' after 'do' body"));
        }
        self.advance();
        if !matches!(self.cur_kind(), TokKind::LParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' after 'do ... while'"));
        }
        self.advance();
        let cond = match self.parse_expr(true, p_fuel - 1) {
            PRes::Ok(e) => e,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after 'do ... while' condition"));
        }
        self.advance();
        if matches!(self.cur_kind(), TokKind::Semi) {
            self.advance();
        }
        PRes::Ok(self.prog.push_stmt(StmtNode::DoWhile { labels, body, cond }))
    }

    fn expr_to_foreach_lhs(&self, expr_id: ExprId) -> PRes<ForEachLhs> {
        if expr_id.0 >= self.prog.exprs.len() {
            return PRes::SyntaxErr(syntax_err_msg(b"Invalid left-hand side in for-in/of"));
        }
        match &self.prog.exprs[expr_id.0] {
            ExprNode::Ident(nm) => {
                if self.strict && is_strict_restricted_ident(nm) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Invalid strict-mode assignment target in for-in/of"));
                }
                PRes::Ok(ForEachLhs::Ident(clone_js_str(nm)))
            }
            ExprNode::Member { obj, prop, optional } => {
                if *optional {
                    return PRes::SyntaxErr(syntax_err_msg(b"Optional chain is invalid left-hand side in for-in/of"));
                }
                PRes::Ok(ForEachLhs::Member { obj: *obj, prop: *prop })
            }
            ExprNode::ArrayLit { .. } | ExprNode::ObjectLit { .. } => {
                PRes::Unsup(UnsupportedFeature::DestructuringPattern)
            }
            _ => PRes::SyntaxErr(syntax_err_msg(b"Invalid left-hand side in for-in/of")),
        }
    }

    fn parse_for_stmt(&mut self, labels: Vec<JsStr>, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        self.advance(); // for
        if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Await, .. }) {
            return PRes::Unsup(UnsupportedFeature::ForAwaitOf);
        }
        if !matches!(self.cur_kind(), TokKind::LParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' after 'for'"));
        }
        self.advance();

        let mut per_iter_lets: Vec<JsStr> = Vec::new();
        let mut head_lex: Vec<JsStr> = Vec::new();
        let empty_p: Vec<JsStr> = Vec::new();

        if matches!(self.cur_kind(), TokKind::Semi) {
            self.advance();
            return self.finish_c_for(labels, None, per_iter_lets, p_fuel - 1);
        }

        let ck = self.cur_kind();
        let vkind_opt: Option<VarKind> = match ck {
            TokKind::Keyword { kw: Kw::Var, .. } => Some(VarKind::Var),
            TokKind::Keyword { kw: Kw::Const, .. } => Some(VarKind::Const),
            TokKind::Keyword { kw: Kw::Let, .. } => {
                let nk = self.peek_kind_at(1);
                if matches!(nk, TokKind::Ident(_) | TokKind::LBracket | TokKind::LBrace)
                    || matches!(nk, TokKind::Keyword { kw: Kw::Let, .. })
                    || self.strict
                {
                    Some(VarKind::Let)
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(vk) = vkind_opt {
            self.advance();
            let decls = match self.parse_var_decl_list(vk, false, &mut head_lex, &empty_p, p_fuel - 1) {
                PRes::Ok(d) => d,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if decls.len() == 1 && decls[0].init.is_none() {
                if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::In, .. }) {
                    self.advance();
                    let object = match self.parse_expr(true, p_fuel - 1) {
                        PRes::Ok(e) => e,
                        PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                        PRes::Unsup(f) => return PRes::Unsup(f),
                    };
                    if !matches!(self.cur_kind(), TokKind::RParen) {
                        return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' in for-in"));
                    }
                    self.advance();
                    if self.loop_depth < usize::MAX { self.loop_depth += 1; }
                    let bres = self.parse_sub_stmt(false, p_fuel - 1);
                    if self.loop_depth > 0 { self.loop_depth -= 1; }
                    return match bres {
                        PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::ForIn {
                            labels,
                            lhs: ForEachLhs::Decl { kind: vk, name: clone_js_str(&decls[0].name) },
                            object,
                            body,
                        })),
                        other => other,
                    };
                }
                if let TokKind::Ident(ref kw_of) = self.cur_kind() {
                    if eq_ascii(kw_of, b"of") {
                        self.advance();
                        let iterable = match self.parse_assign_expr(true, p_fuel - 1) {
                            PRes::Ok(e) => e,
                            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                            PRes::Unsup(f) => return PRes::Unsup(f),
                        };
                        if !matches!(self.cur_kind(), TokKind::RParen) {
                            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' in for-of"));
                        }
                        self.advance();
                        if self.loop_depth < usize::MAX { self.loop_depth += 1; }
                        let bres = self.parse_sub_stmt(false, p_fuel - 1);
                        if self.loop_depth > 0 { self.loop_depth -= 1; }
                        return match bres {
                            PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::ForOf {
                                labels,
                                lhs: ForEachLhs::Decl { kind: vk, name: clone_js_str(&decls[0].name) },
                                iterable,
                                body,
                            })),
                            other => other,
                        };
                    }
                }
            }
            if matches!(vk, VarKind::Const) {
                let mut di: usize = 0;
                while di < decls.len()
                    invariant di <= decls@.len(),
                    decreases decls@.len() - di,
                {
                    if decls[di].init.is_none() {
                        return PRes::SyntaxErr(syntax_err_msg(b"Missing initializer in const declaration"));
                    }
                    di += 1;
                }
            }
            if matches!(vk, VarKind::Let) {
                let mut di: usize = 0;
                while di < decls.len()
                    invariant di <= decls@.len(),
                    decreases decls@.len() - di,
                {
                    per_iter_lets.push(clone_js_str(&decls[di].name));
                    di += 1;
                }
            }
            if !matches!(self.cur_kind(), TokKind::Semi) {
                return PRes::SyntaxErr(syntax_err_msg(b"Expected ';' in 'for' header"));
            }
            self.advance();
            let init_sid = self.prog.push_stmt(StmtNode::VarDecl { kind: vk, decls });
            return self.finish_c_for(labels, Some(init_sid), per_iter_lets, p_fuel - 1);
        }

        let init_expr = match self.parse_expr(false, p_fuel - 1) {
            PRes::Ok(e) => e,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::In, .. }) {
            let lhs = match self.expr_to_foreach_lhs(init_expr) {
                PRes::Ok(l) => l,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            self.advance();
            let object = match self.parse_expr(true, p_fuel - 1) {
                PRes::Ok(e) => e,
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            };
            if !matches!(self.cur_kind(), TokKind::RParen) {
                return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' in for-in"));
            }
            self.advance();
            if self.loop_depth < usize::MAX { self.loop_depth += 1; }
            let bres = self.parse_sub_stmt(false, p_fuel - 1);
            if self.loop_depth > 0 { self.loop_depth -= 1; }
            return match bres {
                PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::ForIn {
                    labels,
                    lhs,
                    object,
                    body,
                })),
                other => other,
            };
        }
        if let TokKind::Ident(ref kw_of) = self.cur_kind() {
            if eq_ascii(kw_of, b"of") {
                let lhs = match self.expr_to_foreach_lhs(init_expr) {
                    PRes::Ok(l) => l,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                self.advance();
                let iterable = match self.parse_assign_expr(true, p_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                    PRes::Unsup(f) => return PRes::Unsup(f),
                };
                if !matches!(self.cur_kind(), TokKind::RParen) {
                    return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' in for-of"));
                }
                self.advance();
                if self.loop_depth < usize::MAX { self.loop_depth += 1; }
                let bres = self.parse_sub_stmt(false, p_fuel - 1);
                if self.loop_depth > 0 { self.loop_depth -= 1; }
                return match bres {
                    PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::ForOf {
                        labels,
                        lhs,
                        iterable,
                        body,
                    })),
                    other => other,
                };
            }
        }
        if !matches!(self.cur_kind(), TokKind::Semi) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ';' after 'for' init expression"));
        }
        self.advance();
        let init_sid = self.prog.push_stmt(StmtNode::ExprStmt(init_expr));
        self.finish_c_for(labels, Some(init_sid), per_iter_lets, p_fuel - 1)
    }

    fn finish_c_for(
        &mut self,
        labels: Vec<JsStr>,
        init: Option<StmtId>,
        per_iter_lets: Vec<JsStr>,
        p_fuel: usize,
    ) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        let cond = if matches!(self.cur_kind(), TokKind::Semi) {
            None
        } else {
            match self.parse_expr(true, p_fuel - 1) {
                PRes::Ok(e) => Some(e),
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            }
        };
        if !matches!(self.cur_kind(), TokKind::Semi) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ';' after 'for' condition"));
        }
        self.advance();
        let update = if matches!(self.cur_kind(), TokKind::RParen) {
            None
        } else {
            match self.parse_expr(true, p_fuel - 1) {
                PRes::Ok(e) => Some(e),
                PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
                PRes::Unsup(f) => return PRes::Unsup(f),
            }
        };
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after 'for' header"));
        }
        self.advance();
        if self.loop_depth < usize::MAX { self.loop_depth += 1; }
        let body_res = self.parse_sub_stmt(false, p_fuel - 1);
        if self.loop_depth > 0 { self.loop_depth -= 1; }
        match body_res {
            PRes::Ok(body) => PRes::Ok(self.prog.push_stmt(StmtNode::For {
                labels,
                init,
                per_iter_lets,
                cond,
                update,
                body,
            })),
            other => other,
        }
    }

    fn parse_switch_stmt(&mut self, label: Option<JsStr>, p_fuel: usize) -> (r: PRes<StmtId>)
        decreases p_fuel,
    {
        if p_fuel == 0 {
            return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
        }
        self.advance(); // switch
        if !matches!(self.cur_kind(), TokKind::LParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '(' after 'switch'"));
        }
        self.advance();
        let discriminant = match self.parse_expr(true, p_fuel - 1) {
            PRes::Ok(e) => e,
            PRes::SyntaxErr(m) => return PRes::SyntaxErr(m),
            PRes::Unsup(f) => return PRes::Unsup(f),
        };
        if !matches!(self.cur_kind(), TokKind::RParen) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected ')' after 'switch' discriminant"));
        }
        self.advance();
        if !matches!(self.cur_kind(), TokKind::LBrace) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '{' in 'switch' statement"));
        }
        self.advance();

        if self.switch_depth < usize::MAX { self.switch_depth += 1; }
        let mut cases: Vec<SwitchCase> = Vec::new();
        let mut saw_default = false;
        let mut switch_lex: Vec<JsStr> = Vec::new();
        let empty_p: Vec<JsStr> = Vec::new();
        let mut rem_fuel = p_fuel - 1;

        while !matches!(self.cur_kind(), TokKind::RBrace | TokKind::Eof)
            invariant rem_fuel < p_fuel,
            decreases rem_fuel,
        {
            if rem_fuel == 0 {
                if self.switch_depth > 0 { self.switch_depth -= 1; }
                return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
            }
            let test: Option<ExprId> = if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Case, .. }) {
                self.advance();
                let te = match self.parse_expr(true, rem_fuel - 1) {
                    PRes::Ok(e) => e,
                    PRes::SyntaxErr(m) => {
                        if self.switch_depth > 0 { self.switch_depth -= 1; }
                        return PRes::SyntaxErr(m);
                    }
                    PRes::Unsup(f) => {
                        if self.switch_depth > 0 { self.switch_depth -= 1; }
                        return PRes::Unsup(f);
                    }
                };
                Some(te)
            } else if matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Default, .. }) {
                if saw_default {
                    if self.switch_depth > 0 { self.switch_depth -= 1; }
                    return PRes::SyntaxErr(syntax_err_msg(b"Multiple default clauses in switch"));
                }
                saw_default = true;
                self.advance();
                None
            } else {
                if self.switch_depth > 0 { self.switch_depth -= 1; }
                return PRes::SyntaxErr(syntax_err_msg(b"Expected 'case' or 'default' in switch"));
            };
            if !matches!(self.cur_kind(), TokKind::Colon) {
                if self.switch_depth > 0 { self.switch_depth -= 1; }
                return PRes::SyntaxErr(syntax_err_msg(b"Expected ':' after case/default"));
            }
            self.advance();

            let mut consequent: Vec<StmtId> = Vec::new();
            let mut inner_fuel = rem_fuel - 1;
            while !matches!(self.cur_kind(), TokKind::RBrace | TokKind::Eof)
                && !matches!(self.cur_kind(), TokKind::Keyword { kw: Kw::Case | Kw::Default, .. })
                invariant inner_fuel < rem_fuel < p_fuel,
                decreases inner_fuel,
            {
                if inner_fuel == 0 {
                    if self.switch_depth > 0 { self.switch_depth -= 1; }
                    return PRes::Unsup(UnsupportedFeature::ParserDepthLimit);
                }
                match self.parse_stmt(&mut switch_lex, &empty_p, inner_fuel - 1) {
                    PRes::Ok(s) => consequent.push(s),
                    PRes::SyntaxErr(m) => {
                        if self.switch_depth > 0 { self.switch_depth -= 1; }
                        return PRes::SyntaxErr(m);
                    }
                    PRes::Unsup(f) => {
                        if self.switch_depth > 0 { self.switch_depth -= 1; }
                        return PRes::Unsup(f);
                    }
                }
                inner_fuel -= 1;
            }
            cases.push(SwitchCase { test, consequent });
            rem_fuel -= 1;
        }

        if self.switch_depth > 0 { self.switch_depth -= 1; }
        if !matches!(self.cur_kind(), TokKind::RBrace) {
            return PRes::SyntaxErr(syntax_err_msg(b"Expected '}' after switch cases"));
        }
        self.advance();
        PRes::Ok(self.prog.push_stmt(StmtNode::Switch { label, discriminant, cases }))
    }
}

/// Parse UTF-16 code units into a verified `Program` AST (`Ok`), `SyntaxError`, or explicit `Unsupported`.
pub fn parse_script_utf16(units: &[u16]) -> (res: ParseOutcome)
    ensures
        match res {
            ParseOutcome::Ok(ref prog) => spec_prog_wf(prog@),
            _ => true,
        },
{
    let tokens = match tokenize_utf16(units) {
        Ok(t) => t,
        Err(msg) => return ParseOutcome::SyntaxError(msg),
    };
    let n_toks = tokens.len();
    let p_fuel: usize = if n_toks <= 1_000_000 { n_toks * 32 + 256 } else { 32_000_256 };

    let mut parser = Parser {
        tokens,
        pos: 0,
        prog: Program::new(false),
        strict: false,
        in_function: false,
        loop_depth: 0,
        switch_depth: 0,
        labels: Vec::new(),
        var_scopes: Vec::new(),
    };
    let is_strict = parser.detect_directive_prologue_strict(0);
    parser.strict = is_strict;
    parser.prog.strict = is_strict;
    parser.var_scopes.push(Vec::new());

    let empty_params: Vec<JsStr> = Vec::new();
    match parser.parse_stmt_list_checked(&empty_params, false, p_fuel) {
        PRes::Ok(body) => {
            if !matches!(parser.cur_kind(), TokKind::Eof) {
                return ParseOutcome::SyntaxError(syntax_err_msg(b"Unexpected token at top level"));
            }
            let hoisted_vars = match parser.var_scopes.pop() {
                Some(v) => v,
                None => Vec::new(),
            };
            parser.prog.hoisted_vars = hoisted_vars;
            parser.prog.body = body;
            if !parser.prog.check_wf() {
                return ParseOutcome::Unsupported(UnsupportedFeature::InvalidAstReference);
            }
            ParseOutcome::Ok(parser.prog)
        }
        PRes::SyntaxErr(msg) => ParseOutcome::SyntaxError(msg),
        PRes::Unsup(f) => ParseOutcome::Unsupported(f),
    }
}

/// Parse UTF-8 source bytes via verified UTF-8 -> UTF-16 decoding into a `Program` AST.
pub fn parse_script_bytes(bs: &[u8]) -> (res: ParseOutcome)
    ensures
        (crate::utf16::spec_utf8_to_utf16(bs@) is None) ==> matches!(res, ParseOutcome::SyntaxError(_)),
        match res {
            ParseOutcome::Ok(ref prog) => spec_prog_wf(prog@),
            _ => true,
        },
{
    match crate::utf16::utf8_to_utf16(bs) {
        Some(u16s) => parse_script_utf16(u16s.units.as_slice()),
        None => ParseOutcome::SyntaxError(syntax_err_msg(b"Invalid UTF-8 source bytes")),
    }
}

/// Parse an ECMAScript source `&str` via verified UTF-8 -> UTF-16 decoding into a `Program` AST.
pub fn parse_script(js_source: &str) -> (res: ParseOutcome)
    ensures
        (crate::utf16::spec_utf8_to_utf16(js_source.spec_bytes()) is None) ==> matches!(res, ParseOutcome::SyntaxError(_)),
        match res {
            ParseOutcome::Ok(ref prog) => spec_prog_wf(prog@),
            _ => true,
        },
{
    parse_script_bytes(js_source.as_bytes())
}

} // verus!
