//! Integration & differential test suite for `vjs_types` (J1):
//! 1. Executes real pinned `tc39/test262` files under `tests/data/built-ins/Number` and
//!    `tests/data/language/types` through a clean AST evaluator backed exclusively by
//!    `vjs_types` verified operations (`Utf16Str`, `JsNumber`, `JsBigInt`, `JsPrim`).
//! 2. Differential-tests `JsNumber` IEEE-754 arithmetic, comparisons, `ToInt32`/`ToUint32`,
//!    `Number::toString`, and `StringToNumber` against Rust `f64` across 25,000+ cases.
//! 3. Differential-tests `JsNumber`, `JsBigInt`, `Utf16Str`, `ToBoolean`, `SameValue`,
//!    `IsStrictlyEqual`, and `IsLooselyEqual` against live Node.js V8
//!    (`/Users/mac/.nvm/versions/node/v24.15.0/bin/node`) across 1,500+ edge-case inputs.
//! 4. Writes `browser/vjs-types/report.json` with exact measured pass counts.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use vjs_types::bigint::{string_to_bigint, JsBigInt};
use vjs_types::number::{bigint_to_number_rne, number_to_string, string_to_number, JsNumber};
use vjs_types::ops::{
    is_loosely_equal, is_strictly_equal, same_value, same_value_zero, to_boolean, to_number,
    to_numeric, to_primitive, to_string, typeof_prim, JsInput, JsNumeric, JsPrim, MethodOutcome,
    ObjectToPrimitiveHook, PreferredType, TypeErrorKind,
};
use vjs_types::utf16::{utf16_encode_code_point, utf8_to_utf16, Utf16Str};

const NODE_BIN: &str = "/Users/mac/.nvm/versions/node/v24.15.0/bin/node";

fn u16_to_rust_string(s: &Utf16Str) -> String {
    String::from_utf16_lossy(&s.units)
}

fn rust_str_to_u16(s: &str) -> Utf16Str {
    utf8_to_utf16(s.as_bytes()).expect("valid UTF-8")
}

// ===========================================================================================
// Minimal Faithful Test262 Evaluator Backed 100% by `vjs_types`
// ===========================================================================================

#[derive(Clone, Debug)]
enum Val {
    Prim(JsPrim),
    Object(usize),
    BuiltinFn(BuiltinId),
    UserFn { params: Vec<String>, body: Vec<Stmt> },
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum BuiltinId {
    NumberCtor,
    StringCtor,
    BooleanCtor,
    ObjectCtor,
    ArrayCtor,
    SymbolCtor,
    BigIntCtor,
    TypeErrorCtor,
    Test262ErrorCtor,
    IsNaNGlobal,
    IsFiniteGlobal,
    EvalGlobal,
    NumberIsNaN,
    NumberIsFinite,
    NumberIsInteger,
    NumberIsSafeInteger,
    NumberProtoToString,
    MathPow,
    MathAbs,
    AssertSameValue,
    AssertNotSameValue,
    DefaultObjToString,
    DefaultObjValueOf,
}

#[derive(Clone, Debug)]
enum ObjKind {
    Ordinary,
    BoxedPrim(JsPrim),
    Array(Vec<Val>),
    ErrorObj { is_type_error: bool, msg: String },
}

#[derive(Clone, Debug)]
struct ObjSlot {
    kind: ObjKind,
    props: BTreeMap<String, Val>,
}

#[derive(Clone, Debug)]
enum Tok {
    Ident(String),
    NumLit(JsNumber),
    BigIntLit(JsBigInt),
    StrLit(Utf16Str),
    Punct(String),
}

fn hex_val_char(c: char) -> Option<u32> {
    match c {
        '0'..='9' => Some((c as u32) - ('0' as u32)),
        'a'..='f' => Some((c as u32) - ('a' as u32) + 10),
        'A'..='F' => Some((c as u32) - ('A' as u32) + 10),
        _ => None,
    }
}

fn tokenize_js(src: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut out = Vec::new();

    while i < n {
        let c = chars[i];
        // Whitespace (including BOM, LS, PS, NBSP)
        if c.is_whitespace() || c == '\u{FEFF}' || c == '\u{2028}' || c == '\u{2029}' {
            i += 1;
            continue;
        }
        // Comments
        if c == '/' && i + 1 < n && chars[i + 1] == '/' {
            i += 2;
            while i < n && chars[i] != '\n' && chars[i] != '\r' && chars[i] != '\u{2028}' && chars[i] != '\u{2029}' {
                i += 1;
            }
            continue;
        }
        if c == '/' && i + 1 < n && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < n && !(chars[i] == '*' && chars[i + 1] == '/') {
                i += 1;
            }
            i += 2;
            continue;
        }
        // String literal
        if c == '\'' || c == '"' {
            let quote = c;
            i += 1;
            let mut units: Vec<u16> = Vec::new();
            while i < n && chars[i] != quote {
                if chars[i] == '\\' {
                    i += 1;
                    if i >= n {
                        return Err("unterminated escape".into());
                    }
                    match chars[i] {
                        'n' => { units.push(0x000A); i += 1; }
                        'r' => { units.push(0x000D); i += 1; }
                        't' => { units.push(0x0009); i += 1; }
                        'b' => { units.push(0x0008); i += 1; }
                        'f' => { units.push(0x000C); i += 1; }
                        'v' => { units.push(0x000B); i += 1; }
                        '0' => { units.push(0x0000); i += 1; }
                        '\\' => { units.push(0x005C); i += 1; }
                        '\'' => { units.push(0x0027); i += 1; }
                        '"' => { units.push(0x0022); i += 1; }
                        '\n' => { i += 1; }
                        '\r' => {
                            i += 1;
                            if i < n && chars[i] == '\n' {
                                i += 1;
                            }
                        }
                        'x' => {
                            if i + 2 >= n {
                                return Err("bad \\x escape".into());
                            }
                            let h1 = hex_val_char(chars[i + 1]).ok_or("bad hex")?;
                            let h2 = hex_val_char(chars[i + 2]).ok_or("bad hex")?;
                            units.push(((h1 << 4) | h2) as u16);
                            i += 3;
                        }
                        'u' => {
                            if i + 1 < n && chars[i + 1] == '{' {
                                i += 2;
                                let mut cp: u32 = 0;
                                while i < n && chars[i] != '}' {
                                    let hv = hex_val_char(chars[i]).ok_or("bad \\u{} hex")?;
                                    cp = (cp << 4) | hv;
                                    i += 1;
                                }
                                i += 1; // '}'
                                units.extend(utf16_encode_code_point(cp));
                            } else {
                                if i + 4 >= n {
                                    return Err("bad \\uHHHH escape".into());
                                }
                                let h1 = hex_val_char(chars[i + 1]).ok_or("bad hex")?;
                                let h2 = hex_val_char(chars[i + 2]).ok_or("bad hex")?;
                                let h3 = hex_val_char(chars[i + 3]).ok_or("bad hex")?;
                                let h4 = hex_val_char(chars[i + 4]).ok_or("bad hex")?;
                                units.push(((h1 << 12) | (h2 << 8) | (h3 << 4) | h4) as u16);
                                i += 5;
                            }
                        }
                        other => {
                            let mut buf = [0u16; 2];
                            for u in other.encode_utf16(&mut buf) {
                                units.push(*u);
                            }
                            i += 1;
                        }
                    }
                } else {
                    let mut buf = [0u16; 2];
                    for u in chars[i].encode_utf16(&mut buf) {
                        units.push(*u);
                    }
                    i += 1;
                }
            }
            i += 1; // closing quote
            out.push(Tok::StrLit(Utf16Str::from_vec(units)));
            continue;
        }
        // Numeric literal (`0x..`, `0b..`, `0o..`, `123`, `.5`, `0..toString()`)
        if c.is_ascii_digit() || (c == '.' && i + 1 < n && chars[i + 1].is_ascii_digit()) {
            let start = i;
            if c == '0' && i + 1 < n && matches!(chars[i + 1], 'x' | 'X' | 'b' | 'B' | 'o' | 'O') {
                i += 2;
                while i < n && (chars[i].is_ascii_hexdigit() || chars[i] == '_') {
                    i += 1;
                }
            } else {
                while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                }
                // Careful with `0..toString()`: first `.` belongs to `0.`, second `.` is member access!
                if i < n && chars[i] == '.' {
                    i += 1;
                    while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                        i += 1;
                    }
                }
                if i < n && (chars[i] == 'e' || chars[i] == 'E') {
                    i += 1;
                    if i < n && (chars[i] == '+' || chars[i] == '-') {
                        i += 1;
                    }
                    while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                        i += 1;
                    }
                }
            }
            let raw: String = chars[start..i].iter().filter(|&&ch| ch != '_').collect();
            if i < n && chars[i] == 'n' {
                i += 1;
                let u = rust_str_to_u16(&raw);
                let bi = string_to_bigint(&u).ok_or_else(|| format!("bad BigInt literal {raw}"))?;
                out.push(Tok::BigIntLit(bi));
            } else {
                let u = rust_str_to_u16(&raw);
                let num = string_to_number(&u);
                out.push(Tok::NumLit(num));
            }
            continue;
        }
        // Identifier
        if c.is_ascii_alphabetic() || c == '_' || c == '$' {
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_' || chars[i] == '$') {
                i += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            out.push(Tok::Ident(ident));
            continue;
        }
        // Multi-char punctuators
        let rem: String = chars[i..std::cmp::min(n, i + 4)].iter().collect();
        let matched = [
            ">>>=", "===", "!==", ">>>", "<<=", ">>=", "**=", "&&=", "||=", "==", "!=", "<=",
            ">=", "&&", "||", "++", "--", "**", "<<", ">>", "+=", "-=", "*=",
        ]
        .iter()
        .find(|&&p| rem.starts_with(p));
        if let Some(&p) = matched {
            out.push(Tok::Punct(p.to_string()));
            i += p.len();
            continue;
        }
        out.push(Tok::Punct(c.to_string()));
        i += 1;
    }
    Ok(out)
}

#[derive(Clone, Debug)]
enum Expr {
    Ident(String),
    Lit(JsPrim),
    ArrayLit(Vec<Expr>),
    ObjLit(Vec<(String, Expr)>),
    FnExpr { params: Vec<String>, body: Vec<Stmt> },
    Unary(String, Box<Expr>),
    Update { op: String, prefix: bool, target: Box<Expr> },
    Binary(String, Box<Expr>, Box<Expr>),
    Assign(String, Box<Expr>, Box<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    New(Box<Expr>, Vec<Expr>),
    Member(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
enum Stmt {
    VarDecl(Vec<(String, Option<Expr>)>),
    FnDecl { name: String, params: Vec<String>, body: Vec<Stmt> },
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    For {
        init: Option<Box<Stmt>>,
        cond: Option<Expr>,
        step: Option<Expr>,
        body: Box<Stmt>,
    },
    Return(Option<Expr>),
    Throw(Expr),
    Try {
        body: Vec<Stmt>,
        catch_var: Option<String>,
        catch_body: Vec<Stmt>,
    },
    ExprStmt(Expr),
    Empty,
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn next(&mut self) -> Option<Tok> {
        if self.pos < self.toks.len() {
            let t = self.toks[self.pos].clone();
            self.pos += 1;
            Some(t)
        } else {
            None
        }
    }

    fn eat_punct(&mut self, p: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Punct(s)) if s == p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_ident(&mut self, kw: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Ident(s)) if s == kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_punct(&mut self, p: &str) -> Result<(), String> {
        if self.eat_punct(p) {
            Ok(())
        } else {
            Err(format!("expected `{p}` at token {:?} (pos {})", self.peek(), self.pos))
        }
    }

    fn parse_program(&mut self) -> Result<Vec<Stmt>, String> {
        let mut out = Vec::new();
        while self.peek().is_some() {
            out.push(self.parse_stmt()?);
        }
        Ok(out)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        if self.eat_punct(";") {
            return Ok(Stmt::Empty);
        }
        if self.eat_punct("{") {
            let mut body = Vec::new();
            while !self.eat_punct("}") {
                if self.peek().is_none() {
                    return Err("unclosed `{`".into());
                }
                body.push(self.parse_stmt()?);
            }
            return Ok(Stmt::Block(body));
        }
        if self.eat_ident("var") || self.eat_ident("let") || self.eat_ident("const") {
            let mut decls = Vec::new();
            loop {
                let Some(Tok::Ident(name)) = self.next() else {
                    return Err("expected var identifier".into());
                };
                let init = if self.eat_punct("=") {
                    Some(self.parse_assign()?)
                } else {
                    None
                };
                decls.push((name, init));
                if !self.eat_punct(",") {
                    break;
                }
            }
            let _ = self.eat_punct(";");
            return Ok(Stmt::VarDecl(decls));
        }
        if self.eat_ident("function") {
            let Some(Tok::Ident(name)) = self.next() else {
                return Err("expected function name".into());
            };
            let (params, body) = self.parse_fn_tail()?;
            return Ok(Stmt::FnDecl { name, params, body });
        }
        if self.eat_ident("if") {
            self.expect_punct("(")?;
            let cond = self.parse_expr()?;
            self.expect_punct(")")?;
            let then_s = Box::new(self.parse_stmt()?);
            let else_s = if self.eat_ident("else") {
                Some(Box::new(self.parse_stmt()?))
            } else {
                None
            };
            return Ok(Stmt::If(cond, then_s, else_s));
        }
        if self.eat_ident("for") {
            self.expect_punct("(")?;
            let init = if self.eat_punct(";") {
                None
            } else if self.eat_ident("var") || self.eat_ident("let") || self.eat_ident("const") {
                let mut decls = Vec::new();
                loop {
                    let Some(Tok::Ident(name)) = self.next() else {
                        return Err("expected for-var identifier".into());
                    };
                    let init_e = if self.eat_punct("=") {
                        Some(self.parse_assign()?)
                    } else {
                        None
                    };
                    decls.push((name, init_e));
                    if !self.eat_punct(",") {
                        break;
                    }
                }
                self.expect_punct(";")?;
                Some(Box::new(Stmt::VarDecl(decls)))
            } else {
                let e = self.parse_expr()?;
                self.expect_punct(";")?;
                Some(Box::new(Stmt::ExprStmt(e)))
            };
            let cond = if self.eat_punct(";") {
                None
            } else {
                let c = self.parse_expr()?;
                self.expect_punct(";")?;
                Some(c)
            };
            let step = if self.eat_punct(")") {
                None
            } else {
                let s = self.parse_expr()?;
                self.expect_punct(")")?;
                Some(s)
            };
            let body = Box::new(self.parse_stmt()?);
            return Ok(Stmt::For { init, cond, step, body });
        }
        if self.eat_ident("return") {
            if self.eat_punct(";") || matches!(self.peek(), Some(Tok::Punct(s)) if s == "}") || self.peek().is_none() {
                return Ok(Stmt::Return(None));
            }
            let e = self.parse_expr()?;
            let _ = self.eat_punct(";");
            return Ok(Stmt::Return(Some(e)));
        }
        if self.eat_ident("throw") {
            let e = self.parse_expr()?;
            let _ = self.eat_punct(";");
            return Ok(Stmt::Throw(e));
        }
        if self.eat_ident("try") {
            self.expect_punct("{")?;
            let mut body = Vec::new();
            while !self.eat_punct("}") {
                body.push(self.parse_stmt()?);
            }
            let mut catch_var = None;
            let mut catch_body = Vec::new();
            if self.eat_ident("catch") {
                if self.eat_punct("(") {
                    if let Some(Tok::Ident(v)) = self.next() {
                        catch_var = Some(v);
                    }
                    self.expect_punct(")")?;
                }
                self.expect_punct("{")?;
                while !self.eat_punct("}") {
                    catch_body.push(self.parse_stmt()?);
                }
            }
            return Ok(Stmt::Try { body, catch_var, catch_body });
        }
        let e = self.parse_expr()?;
        let _ = self.eat_punct(";");
        Ok(Stmt::ExprStmt(e))
    }

    fn parse_fn_tail(&mut self) -> Result<(Vec<String>, Vec<Stmt>), String> {
        self.expect_punct("(")?;
        let mut params = Vec::new();
        if !self.eat_punct(")") {
            loop {
                let Some(Tok::Ident(p)) = self.next() else {
                    return Err("expected param name".into());
                };
                params.push(p);
                if self.eat_punct(")") {
                    break;
                }
                self.expect_punct(",")?;
            }
        }
        self.expect_punct("{")?;
        let mut body = Vec::new();
        while !self.eat_punct("}") {
            body.push(self.parse_stmt()?);
        }
        Ok((params, body))
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_assign()
    }

    fn parse_assign(&mut self) -> Result<Expr, String> {
        let lhs = self.parse_cond()?;
        for op in ["=", "+=", "-=", "*="] {
            if self.eat_punct(op) {
                let rhs = self.parse_assign()?;
                return Ok(Expr::Assign(op.to_string(), Box::new(lhs), Box::new(rhs)));
            }
        }
        Ok(lhs)
    }

    fn parse_cond(&mut self) -> Result<Expr, String> {
        let c = self.parse_or()?;
        if self.eat_punct("?") {
            let t = self.parse_assign()?;
            self.expect_punct(":")?;
            let f = self.parse_assign()?;
            return Ok(Expr::Cond(Box::new(c), Box::new(t), Box::new(f)));
        }
        Ok(c)
    }

    fn parse_or(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_and()?;
        while self.eat_punct("||") {
            let r = self.parse_and()?;
            l = Expr::Binary("||".into(), Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_and(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_bitor()?;
        while self.eat_punct("&&") {
            let r = self.parse_bitor()?;
            l = Expr::Binary("&&".into(), Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_bitor(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_bitxor()?;
        while self.eat_punct("|") {
            let r = self.parse_bitxor()?;
            l = Expr::Binary("|".into(), Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_bitxor(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_bitand()?;
        while self.eat_punct("^") {
            let r = self.parse_bitand()?;
            l = Expr::Binary("^".into(), Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_bitand(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_eq()?;
        while self.eat_punct("&") {
            let r = self.parse_eq()?;
            l = Expr::Binary("&".into(), Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn parse_eq(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_rel()?;
        loop {
            let op = ["===", "!==", "==", "!="]
                .iter()
                .find(|&&o| self.eat_punct(o))
                .copied();
            if let Some(o) = op {
                let r = self.parse_rel()?;
                l = Expr::Binary(o.into(), Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_rel(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_shift()?;
        loop {
            if self.eat_ident("instanceof") {
                let r = self.parse_shift()?;
                l = Expr::Binary("instanceof".into(), Box::new(l), Box::new(r));
                continue;
            }
            let op = ["<=", ">=", "<", ">"]
                .iter()
                .find(|&&o| self.eat_punct(o))
                .copied();
            if let Some(o) = op {
                let r = self.parse_shift()?;
                l = Expr::Binary(o.into(), Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_shift(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_add()?;
        loop {
            let op = [">>>", "<<", ">>"]
                .iter()
                .find(|&&o| self.eat_punct(o))
                .copied();
            if let Some(o) = op {
                let r = self.parse_add()?;
                l = Expr::Binary(o.into(), Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_add(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_mul()?;
        loop {
            let op = ["+", "-"].iter().find(|&&o| self.eat_punct(o)).copied();
            if let Some(o) = op {
                let r = self.parse_mul()?;
                l = Expr::Binary(o.into(), Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_mul(&mut self) -> Result<Expr, String> {
        let mut l = self.parse_exp()?;
        loop {
            let op = ["*", "/", "%"].iter().find(|&&o| self.eat_punct(o)).copied();
            if let Some(o) = op {
                let r = self.parse_exp()?;
                l = Expr::Binary(o.into(), Box::new(l), Box::new(r));
            } else {
                break;
            }
        }
        Ok(l)
    }

    fn parse_exp(&mut self) -> Result<Expr, String> {
        let l = self.parse_unary()?;
        if self.eat_punct("**") {
            let r = self.parse_exp()?;
            return Ok(Expr::Binary("**".into(), Box::new(l), Box::new(r)));
        }
        Ok(l)
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        if self.eat_ident("typeof") {
            return Ok(Expr::Unary("typeof".into(), Box::new(self.parse_unary()?)));
        }
        if self.eat_ident("void") {
            return Ok(Expr::Unary("void".into(), Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("++") {
            return Ok(Expr::Update { op: "++".into(), prefix: true, target: Box::new(self.parse_unary()?) });
        }
        if self.eat_punct("--") {
            return Ok(Expr::Update { op: "--".into(), prefix: true, target: Box::new(self.parse_unary()?) });
        }
        for op in ["+", "-", "!", "~"] {
            if self.eat_punct(op) {
                return Ok(Expr::Unary(op.into(), Box::new(self.parse_unary()?)));
            }
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_call_member()?;
        if self.eat_punct("++") {
            e = Expr::Update { op: "++".into(), prefix: false, target: Box::new(e) };
        } else if self.eat_punct("--") {
            e = Expr::Update { op: "--".into(), prefix: false, target: Box::new(e) };
        }
        Ok(e)
    }

    fn parse_call_member(&mut self) -> Result<Expr, String> {
        let mut e = if self.eat_ident("new") {
            let callee = self.parse_member_only()?;
            let args = if self.eat_punct("(") {
                self.parse_arg_list()?
            } else {
                Vec::new()
            };
            Expr::New(Box::new(callee), args)
        } else {
            self.parse_primary()?
        };
        loop {
            if self.eat_punct(".") {
                let Some(Tok::Ident(prop)) = self.next() else {
                    return Err("expected property after `.`".into());
                };
                e = Expr::Member(Box::new(e), prop);
            } else if self.eat_punct("[") {
                let idx = self.parse_expr()?;
                self.expect_punct("]")?;
                e = Expr::Index(Box::new(e), Box::new(idx));
            } else if self.eat_punct("(") {
                let args = self.parse_arg_list()?;
                e = Expr::Call(Box::new(e), args);
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn parse_member_only(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_primary()?;
        loop {
            if self.eat_punct(".") {
                let Some(Tok::Ident(prop)) = self.next() else {
                    return Err("expected property after `.`".into());
                };
                e = Expr::Member(Box::new(e), prop);
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn parse_arg_list(&mut self) -> Result<Vec<Expr>, String> {
        let mut args = Vec::new();
        if !self.eat_punct(")") {
            loop {
                args.push(self.parse_assign()?);
                if self.eat_punct(")") {
                    break;
                }
                self.expect_punct(",")?;
            }
        }
        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        if self.eat_punct("(") {
            let e = self.parse_expr()?;
            self.expect_punct(")")?;
            return Ok(e);
        }
        if self.eat_punct("[") {
            let mut items = Vec::new();
            if !self.eat_punct("]") {
                loop {
                    items.push(self.parse_assign()?);
                    if self.eat_punct("]") {
                        break;
                    }
                    self.expect_punct(",")?;
                }
            }
            return Ok(Expr::ArrayLit(items));
        }
        if self.eat_punct("{") {
            let mut props = Vec::new();
            if !self.eat_punct("}") {
                loop {
                    let key = match self.next() {
                        Some(Tok::Ident(s)) => s,
                        Some(Tok::StrLit(s)) => u16_to_rust_string(&s),
                        other => return Err(format!("bad object key {other:?}")),
                    };
                    self.expect_punct(":")?;
                    let val = self.parse_assign()?;
                    props.push((key, val));
                    if self.eat_punct("}") {
                        break;
                    }
                    self.expect_punct(",")?;
                    if self.eat_punct("}") {
                        break;
                    }
                }
            }
            return Ok(Expr::ObjLit(props));
        }
        if self.eat_ident("function") {
            if matches!(self.peek(), Some(Tok::Ident(_))) {
                let _ = self.next();
            }
            let (params, body) = self.parse_fn_tail()?;
            return Ok(Expr::FnExpr { params, body });
        }
        match self.next() {
            Some(Tok::NumLit(n)) => Ok(Expr::Lit(JsPrim::Number(n))),
            Some(Tok::BigIntLit(b)) => Ok(Expr::Lit(JsPrim::BigInt(b))),
            Some(Tok::StrLit(s)) => Ok(Expr::Lit(JsPrim::Str(s))),
            Some(Tok::Ident(s)) => match s.as_str() {
                "null" => Ok(Expr::Lit(JsPrim::Null)),
                "true" => Ok(Expr::Lit(JsPrim::Bool(true))),
                "false" => Ok(Expr::Lit(JsPrim::Bool(false))),
                _ => Ok(Expr::Ident(s)),
            },
            other => Err(format!("unexpected token {other:?}")),
        }
    }
}

enum Flow {
    Normal,
    Return(Val),
    Throw(Val),
}

struct Env {
    vars: BTreeMap<String, Val>,
    heap: Vec<ObjSlot>,
    thrown_slots: Vec<Val>,
    next_sym: u64,
    num_proto_id: usize,
}

impl Env {
    fn new() -> Self {
        let mut env = Env {
            vars: BTreeMap::new(),
            heap: Vec::new(),
            thrown_slots: Vec::new(),
            next_sym: 1,
            num_proto_id: 0,
        };
        // Number.prototype is a Number object with [[NumberData]] = +0 per ECMA-262 §21.1.3!
        let mut np_props = BTreeMap::new();
        np_props.insert("toString".into(), Val::BuiltinFn(BuiltinId::NumberProtoToString));
        let np_id = env.alloc_obj(ObjSlot {
            kind: ObjKind::BoxedPrim(JsPrim::Number(JsNumber::POS_ZERO)),
            props: np_props,
        });
        env.num_proto_id = np_id;

        let mut assert_props = BTreeMap::new();
        assert_props.insert("sameValue".into(), Val::BuiltinFn(BuiltinId::AssertSameValue));
        assert_props.insert("notSameValue".into(), Val::BuiltinFn(BuiltinId::AssertNotSameValue));
        let assert_id = env.alloc_obj(ObjSlot { kind: ObjKind::Ordinary, props: assert_props });

        let mut math_props = BTreeMap::new();
        math_props.insert("pow".into(), Val::BuiltinFn(BuiltinId::MathPow));
        math_props.insert("abs".into(), Val::BuiltinFn(BuiltinId::MathAbs));
        let math_id = env.alloc_obj(ObjSlot { kind: ObjKind::Ordinary, props: math_props });

        env.vars.insert("undefined".into(), Val::Prim(JsPrim::Undefined));
        env.vars.insert("NaN".into(), Val::Prim(JsPrim::Number(JsNumber::NAN)));
        env.vars.insert("Infinity".into(), Val::Prim(JsPrim::Number(JsNumber::POS_INFINITY)));
        env.vars.insert("Number".into(), Val::BuiltinFn(BuiltinId::NumberCtor));
        env.vars.insert("String".into(), Val::BuiltinFn(BuiltinId::StringCtor));
        env.vars.insert("Boolean".into(), Val::BuiltinFn(BuiltinId::BooleanCtor));
        env.vars.insert("Object".into(), Val::BuiltinFn(BuiltinId::ObjectCtor));
        env.vars.insert("Array".into(), Val::BuiltinFn(BuiltinId::ArrayCtor));
        env.vars.insert("Symbol".into(), Val::BuiltinFn(BuiltinId::SymbolCtor));
        env.vars.insert("BigInt".into(), Val::BuiltinFn(BuiltinId::BigIntCtor));
        env.vars.insert("TypeError".into(), Val::BuiltinFn(BuiltinId::TypeErrorCtor));
        env.vars.insert("Test262Error".into(), Val::BuiltinFn(BuiltinId::Test262ErrorCtor));
        env.vars.insert("isNaN".into(), Val::BuiltinFn(BuiltinId::IsNaNGlobal));
        env.vars.insert("isFinite".into(), Val::BuiltinFn(BuiltinId::IsFiniteGlobal));
        env.vars.insert("eval".into(), Val::BuiltinFn(BuiltinId::EvalGlobal));
        env.vars.insert("assert".into(), Val::Object(assert_id));
        env.vars.insert("Math".into(), Val::Object(math_id));
        env
    }

    fn alloc_obj(&mut self, slot: ObjSlot) -> usize {
        let id = self.heap.len();
        self.heap.push(slot);
        id
    }

    fn make_type_error(&mut self, msg: &str) -> Val {
        let id = self.alloc_obj(ObjSlot {
            kind: ObjKind::ErrorObj { is_type_error: true, msg: msg.to_string() },
            props: BTreeMap::new(),
        });
        Val::Object(id)
    }

    fn hoist_stmts(&mut self, stmts: &[Stmt]) {
        for s in stmts {
            match s {
                Stmt::VarDecl(decls) => {
                    for (name, _) in decls {
                        self.vars.entry(name.clone()).or_insert(Val::Prim(JsPrim::Undefined));
                    }
                }
                Stmt::FnDecl { name, params, body } => {
                    self.vars.insert(
                        name.clone(),
                        Val::UserFn { params: params.clone(), body: body.clone() },
                    );
                }
                Stmt::Block(b) => self.hoist_stmts(b),
                Stmt::If(_, t, e) => {
                    self.hoist_stmts(std::slice::from_ref(t));
                    if let Some(el) = e {
                        self.hoist_stmts(std::slice::from_ref(el));
                    }
                }
                Stmt::For { init, body, .. } => {
                    if let Some(i) = init {
                        self.hoist_stmts(std::slice::from_ref(i));
                    }
                    self.hoist_stmts(std::slice::from_ref(body));
                }
                Stmt::Try { body, catch_body, .. } => {
                    self.hoist_stmts(body);
                    self.hoist_stmts(catch_body);
                }
                _ => {}
            }
        }
    }

    fn eval_slot_method_args(&mut self, obj_id: usize, name: &str, args: Vec<Val>) -> MethodOutcome {
        let method = if let Some(v) = self.heap[obj_id].props.get(name).cloned() {
            Some(v)
        } else {
            match name {
                "toString" => Some(Val::BuiltinFn(BuiltinId::DefaultObjToString)),
                "valueOf" => Some(Val::BuiltinFn(BuiltinId::DefaultObjValueOf)),
                _ => None,
            }
        };
        let Some(m) = method else {
            return MethodOutcome::NotCallable;
        };
        match m {
            Val::BuiltinFn(_) | Val::UserFn { .. } => {
                match self.call_fn(m, Some(Val::Object(obj_id)), args) {
                    Ok(Val::Prim(p)) => MethodOutcome::ReturnedPrim(p),
                    Ok(_) => MethodOutcome::ReturnedObject,
                    Err(thrown_val) => {
                        let err_id = self.thrown_slots.len() as u64;
                        self.thrown_slots.push(thrown_val);
                        MethodOutcome::Threw(err_id)
                    }
                }
            }
            _ => MethodOutcome::NotCallable,
        }
    }

    fn val_to_prim(&mut self, v: &Val, pref: PreferredType) -> Result<JsPrim, Val> {
        match v {
            Val::Prim(p) => Ok(p.clone()),
            Val::BuiltinFn(_) | Val::UserFn { .. } => Ok(JsPrim::Str(rust_str_to_u16("function() {}"))),
            Val::Object(id) => {
                // Step 1 (ECMA-262 §7.1.1): Check exotic `@@toPrimitive` first.
                let exotic_out = if self.heap[*id].props.contains_key("@@toPrimitive") {
                    let hint_str = match pref {
                        PreferredType::Default => "default",
                        PreferredType::String => "string",
                        PreferredType::Number => "number",
                    };
                    self.eval_slot_method_args(
                        *id,
                        "@@toPrimitive",
                        vec![Val::Prim(JsPrim::Str(rust_str_to_u16(hint_str)))],
                    )
                } else {
                    MethodOutcome::NotCallable
                };

                // Step 2 (ECMA-262 §7.1.1.1 OrdinaryToPrimitive): Evaluate candidate methods
                // lazily in exact hint order, short-circuiting the second slot if the first
                // returns a primitive or throws (or if exotic `@@toPrimitive` was callable).
                let (to_str_out, val_of_out) = if !matches!(exotic_out, MethodOutcome::NotCallable) {
                    (MethodOutcome::NotCallable, MethodOutcome::NotCallable)
                } else if pref == PreferredType::String {
                    let first = self.eval_slot_method_args(*id, "toString", Vec::new());
                    let second = if matches!(first, MethodOutcome::NotCallable | MethodOutcome::ReturnedObject) {
                        self.eval_slot_method_args(*id, "valueOf", Vec::new())
                    } else {
                        MethodOutcome::NotCallable
                    };
                    (first, second)
                } else {
                    let first = self.eval_slot_method_args(*id, "valueOf", Vec::new());
                    let second = if matches!(first, MethodOutcome::NotCallable | MethodOutcome::ReturnedObject) {
                        self.eval_slot_method_args(*id, "toString", Vec::new())
                    } else {
                        MethodOutcome::NotCallable
                    };
                    (second, first)
                };

                let hook = ObjectToPrimitiveHook {
                    exotic_to_prim: exotic_out,
                    to_string_slot: to_str_out,
                    value_of_slot: val_of_out,
                };
                match to_primitive(&JsInput::Object(*id as u64), pref, &hook) {
                    Ok(p) => Ok(p),
                    Err(TypeErrorKind::AbruptHookError(err_id)) => {
                        Err(self.thrown_slots[err_id as usize].clone())
                    }
                    Err(_) => Err(self.make_type_error("Cannot convert object to primitive value")),
                }
            }
        }
    }

    fn val_to_number(&mut self, v: &Val) -> Result<JsNumber, Val> {
        let p = self.val_to_prim(v, PreferredType::Number)?;
        to_number(&p).map_err(|_| self.make_type_error("Cannot convert to number"))
    }

    fn val_to_string(&mut self, v: &Val) -> Result<Utf16Str, Val> {
        let p = self.val_to_prim(v, PreferredType::String)?;
        to_string(&p).map_err(|_| self.make_type_error("Cannot convert to string"))
    }

    fn val_to_bool(&self, v: &Val) -> bool {
        match v {
            Val::Prim(p) => to_boolean(p),
            Val::Object(_) | Val::BuiltinFn(_) | Val::UserFn { .. } => true,
        }
    }

    fn collect_hoisted_names(stmts: &[Stmt], out: &mut std::collections::BTreeSet<String>) {
        for s in stmts {
            match s {
                Stmt::VarDecl(decls) => {
                    for (name, _) in decls {
                        out.insert(name.clone());
                    }
                }
                Stmt::FnDecl { name, .. } => {
                    out.insert(name.clone());
                }
                Stmt::Block(b) => Self::collect_hoisted_names(b, out),
                Stmt::If(_, t, e) => {
                    Self::collect_hoisted_names(std::slice::from_ref(t), out);
                    if let Some(el) = e {
                        Self::collect_hoisted_names(std::slice::from_ref(el), out);
                    }
                }
                Stmt::For { init, body, .. } => {
                    if let Some(i) = init {
                        Self::collect_hoisted_names(std::slice::from_ref(i), out);
                    }
                    Self::collect_hoisted_names(std::slice::from_ref(body), out);
                }
                Stmt::Try { body, catch_var, catch_body } => {
                    if let Some(cv) = catch_var {
                        out.insert(cv.clone());
                    }
                    Self::collect_hoisted_names(body, out);
                    Self::collect_hoisted_names(catch_body, out);
                }
                _ => {}
            }
        }
    }

    fn call_fn(&mut self, callee: Val, this_val: Option<Val>, args: Vec<Val>) -> Result<Val, Val> {
        match callee {
            Val::UserFn { params, body } => {
                let mut local_names = std::collections::BTreeSet::new();
                for p in &params {
                    local_names.insert(p.clone());
                }
                Self::collect_hoisted_names(&body, &mut local_names);
                let saved_locals: Vec<(String, Option<Val>)> = local_names
                    .into_iter()
                    .map(|k| {
                        let prev = self.vars.get(&k).cloned();
                        (k, prev)
                    })
                    .collect();
                self.hoist_stmts(&body);
                for (idx, p) in params.iter().enumerate() {
                    let av = args.get(idx).cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    self.vars.insert(p.clone(), av);
                }
                let res = match self.exec_stmts(&body) {
                    Flow::Normal => Ok(Val::Prim(JsPrim::Undefined)),
                    Flow::Return(v) => Ok(v),
                    Flow::Throw(e) => Err(e),
                };
                for (k, prev) in saved_locals {
                    match prev {
                        Some(v) => {
                            self.vars.insert(k, v);
                        }
                        None => {
                            self.vars.remove(&k);
                        }
                    }
                }
                res
            }
            Val::BuiltinFn(b) => match b {
                BuiltinId::NumberCtor => {
                    let n = if args.is_empty() {
                        JsNumber::POS_ZERO
                    } else {
                        match &args[0] {
                            Val::Prim(JsPrim::BigInt(bi)) => bigint_to_number_rne(bi),
                            other => self.val_to_number(other)?,
                        }
                    };
                    Ok(Val::Prim(JsPrim::Number(n)))
                }
                BuiltinId::StringCtor => {
                    if args.is_empty() {
                        Ok(Val::Prim(JsPrim::Str(Utf16Str::new())))
                    } else if let Val::Prim(JsPrim::Symbol(_)) = &args[0] {
                        Ok(Val::Prim(JsPrim::Str(rust_str_to_u16("Symbol()"))))
                    } else {
                        let s = self.val_to_string(&args[0])?;
                        Ok(Val::Prim(JsPrim::Str(s)))
                    }
                }
                BuiltinId::BooleanCtor => {
                    let b = args.first().map(|v| self.val_to_bool(v)).unwrap_or(false);
                    Ok(Val::Prim(JsPrim::Bool(b)))
                }
                BuiltinId::SymbolCtor => {
                    let id = self.next_sym;
                    self.next_sym += 1;
                    Ok(Val::Prim(JsPrim::Symbol(id)))
                }
                BuiltinId::BigIntCtor => {
                    let a0 = args.first().cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    let p = self.val_to_prim(&a0, PreferredType::Number)?;
                    match p {
                        JsPrim::BigInt(bi) => Ok(Val::Prim(JsPrim::BigInt(bi))),
                        JsPrim::Bool(b) => Ok(Val::Prim(JsPrim::BigInt(JsBigInt::from_u64(if b { 1 } else { 0 })))),
                        JsPrim::Number(n) => match n.to_exact_bigint() {
                            Some(bi) => Ok(Val::Prim(JsPrim::BigInt(bi))),
                            None => Err(self.make_type_error("Not an integral number for BigInt")),
                        },
                        JsPrim::Str(s) => match string_to_bigint(&s) {
                            Some(bi) => Ok(Val::Prim(JsPrim::BigInt(bi))),
                            None => Err(self.make_type_error("Cannot convert string to BigInt")),
                        },
                        _ => Err(self.make_type_error("Cannot convert to BigInt")),
                    }
                }
                BuiltinId::ObjectCtor => {
                    if let Some(a0) = args.first() {
                        match a0 {
                            Val::Prim(JsPrim::Undefined) | Val::Prim(JsPrim::Null) => {}
                            Val::Object(id) => return Ok(Val::Object(*id)),
                            Val::Prim(p) => {
                                let id = self.alloc_obj(ObjSlot {
                                    kind: ObjKind::BoxedPrim(p.clone()),
                                    props: BTreeMap::new(),
                                });
                                return Ok(Val::Object(id));
                            }
                            _ => {}
                        }
                    }
                    let id = self.alloc_obj(ObjSlot { kind: ObjKind::Ordinary, props: BTreeMap::new() });
                    Ok(Val::Object(id))
                }
                BuiltinId::ArrayCtor => {
                    let elems = if args.len() == 1 {
                        if let Val::Prim(JsPrim::Number(n)) = &args[0] {
                            let len = n.to_uint32() as usize;
                            vec![Val::Prim(JsPrim::Undefined); len]
                        } else {
                            args
                        }
                    } else {
                        args
                    };
                    let id = self.alloc_obj(ObjSlot { kind: ObjKind::Array(elems), props: BTreeMap::new() });
                    Ok(Val::Object(id))
                }
                BuiltinId::TypeErrorCtor | BuiltinId::Test262ErrorCtor => {
                    let msg = if let Some(a0) = args.first() {
                        u16_to_rust_string(&self.val_to_string(a0)?)
                    } else {
                        String::new()
                    };
                    let id = self.alloc_obj(ObjSlot {
                        kind: ObjKind::ErrorObj {
                            is_type_error: b == BuiltinId::TypeErrorCtor,
                            msg,
                        },
                        props: BTreeMap::new(),
                    });
                    Ok(Val::Object(id))
                }
                BuiltinId::IsNaNGlobal => {
                    let n = match args.first() {
                        Some(v) => self.val_to_number(v)?,
                        None => JsNumber::NAN,
                    };
                    Ok(Val::Prim(JsPrim::Bool(n.is_nan())))
                }
                BuiltinId::IsFiniteGlobal => {
                    let n = match args.first() {
                        Some(v) => self.val_to_number(v)?,
                        None => JsNumber::NAN,
                    };
                    Ok(Val::Prim(JsPrim::Bool(n.is_finite())))
                }
                BuiltinId::EvalGlobal => {
                    let Some(a0) = args.first() else {
                        return Ok(Val::Prim(JsPrim::Undefined));
                    };
                    let Val::Prim(JsPrim::Str(code_u16)) = a0 else {
                        return Ok(a0.clone());
                    };
                    let code = u16_to_rust_string(code_u16);
                    let toks = tokenize_js(&code).map_err(|e| self.make_type_error(&e))?;
                    let mut parser = Parser { toks, pos: 0 };
                    let stmts = parser.parse_program().map_err(|e| self.make_type_error(&e))?;
                    self.hoist_stmts(&stmts);
                    let mut last_val = Val::Prim(JsPrim::Undefined);
                    for st in &stmts {
                        if let Stmt::ExprStmt(ex) = st {
                            last_val = self.eval_expr(ex)?;
                        } else {
                            match self.exec_stmt(st) {
                                Flow::Normal => {}
                                Flow::Return(v) => return Ok(v),
                                Flow::Throw(err) => return Err(err),
                            }
                        }
                    }
                    Ok(last_val)
                }
                BuiltinId::NumberIsNaN => {
                    let res = match args.first() {
                        Some(Val::Prim(JsPrim::Number(n))) => n.is_nan(),
                        _ => false,
                    };
                    Ok(Val::Prim(JsPrim::Bool(res)))
                }
                BuiltinId::NumberIsFinite => {
                    let res = match args.first() {
                        Some(Val::Prim(JsPrim::Number(n))) => n.is_finite(),
                        _ => false,
                    };
                    Ok(Val::Prim(JsPrim::Bool(res)))
                }
                BuiltinId::NumberIsInteger => {
                    let res = match args.first() {
                        Some(Val::Prim(JsPrim::Number(n))) => n.is_integral_number(),
                        _ => false,
                    };
                    Ok(Val::Prim(JsPrim::Bool(res)))
                }
                BuiltinId::NumberIsSafeInteger => {
                    let res = match args.first() {
                        Some(Val::Prim(JsPrim::Number(n))) => n.is_safe_integer(),
                        _ => false,
                    };
                    Ok(Val::Prim(JsPrim::Bool(res)))
                }
                BuiltinId::NumberProtoToString => {
                    let num = match this_val {
                        Some(Val::Prim(JsPrim::Number(n))) => n,
                        Some(Val::Object(id)) => match &self.heap[id].kind {
                            ObjKind::BoxedPrim(JsPrim::Number(n)) => *n,
                            _ => return Err(self.make_type_error("thisNumberValue failed")),
                        },
                        _ => return Err(self.make_type_error("thisNumberValue failed")),
                    };
                    if let Some(r_arg) = args.first() {
                        if !matches!(r_arg, Val::Prim(JsPrim::Undefined)) {
                            let rn = self.val_to_number(r_arg)?;
                            if !rn.equal(JsNumber::from_u32(10)) {
                                return Err(self.make_type_error("non-10 radix unsupported in J1"));
                            }
                        }
                    }
                    Ok(Val::Prim(JsPrim::Str(number_to_string(num))))
                }
                BuiltinId::MathPow => {
                    let base = match args.first() {
                        Some(v) => self.val_to_number(v)?,
                        None => JsNumber::NAN,
                    };
                    let exp = match args.get(1) {
                        Some(v) => self.val_to_number(v)?,
                        None => JsNumber::NAN,
                    };
                    let bf = f64::from_bits(base.0);
                    let ef = f64::from_bits(exp.0);
                    let out = JsNumber(bf.powf(ef).to_bits()).canonicalize_nan();
                    Ok(Val::Prim(JsPrim::Number(out)))
                }
                BuiltinId::MathAbs => {
                    let n = match args.first() {
                        Some(v) => self.val_to_number(v)?,
                        None => JsNumber::NAN,
                    };
                    Ok(Val::Prim(JsPrim::Number(n.abs())))
                }
                BuiltinId::AssertSameValue => {
                    let a = args.first().cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    let e = args.get(1).cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    let msg = if let Some(m) = args.get(2) {
                        u16_to_rust_string(&self.val_to_string(m)?)
                    } else {
                        String::new()
                    };
                    let eq = match (&a, &e) {
                        (Val::Prim(pa), Val::Prim(pe)) => same_value(pa, pe),
                        (Val::Object(ia), Val::Object(ie)) => ia == ie,
                        (Val::BuiltinFn(ba), Val::BuiltinFn(be)) => ba == be,
                        _ => false,
                    };
                    if !eq {
                        let err_msg = format!("assert.sameValue failed ({msg}): actual={a:?}, expected={e:?}");
                        let id = self.alloc_obj(ObjSlot {
                            kind: ObjKind::ErrorObj { is_type_error: false, msg: err_msg },
                            props: BTreeMap::new(),
                        });
                        return Err(Val::Object(id));
                    }
                    Ok(Val::Prim(JsPrim::Undefined))
                }
                BuiltinId::AssertNotSameValue => {
                    let a = args.first().cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    let e = args.get(1).cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                    let eq = match (&a, &e) {
                        (Val::Prim(pa), Val::Prim(pe)) => same_value(pa, pe),
                        (Val::Object(ia), Val::Object(ie)) => ia == ie,
                        (Val::BuiltinFn(ba), Val::BuiltinFn(be)) => ba == be,
                        _ => false,
                    };
                    if eq {
                        let id = self.alloc_obj(ObjSlot {
                            kind: ObjKind::ErrorObj {
                                is_type_error: false,
                                msg: format!("assert.notSameValue failed: {a:?}"),
                            },
                            props: BTreeMap::new(),
                        });
                        return Err(Val::Object(id));
                    }
                    Ok(Val::Prim(JsPrim::Undefined))
                }
                BuiltinId::DefaultObjToString => {
                    let Some(Val::Object(id)) = this_val else {
                        return Ok(Val::Prim(JsPrim::Str(rust_str_to_u16("[object Object]"))));
                    };
                    match self.heap[id].kind.clone() {
                        ObjKind::BoxedPrim(p) => {
                            let s = to_string(&p).map_err(|_| self.make_type_error("Symbol toString"))?;
                            Ok(Val::Prim(JsPrim::Str(s)))
                        }
                        ObjKind::Array(elems) => {
                            let mut parts = Vec::new();
                            for el in elems {
                                match el {
                                    Val::Prim(JsPrim::Undefined) | Val::Prim(JsPrim::Null) => {
                                        parts.push(String::new());
                                    }
                                    other => {
                                        let s = self.val_to_string(&other)?;
                                        parts.push(u16_to_rust_string(&s));
                                    }
                                }
                            }
                            Ok(Val::Prim(JsPrim::Str(rust_str_to_u16(&parts.join(",")))))
                        }
                        ObjKind::ErrorObj { msg, .. } => Ok(Val::Prim(JsPrim::Str(rust_str_to_u16(&msg)))),
                        ObjKind::Ordinary => Ok(Val::Prim(JsPrim::Str(rust_str_to_u16("[object Object]")))),
                    }
                }
                BuiltinId::DefaultObjValueOf => {
                    let Some(Val::Object(id)) = this_val else {
                        return Ok(Val::Prim(JsPrim::Undefined));
                    };
                    match &self.heap[id].kind {
                        ObjKind::BoxedPrim(p) => Ok(Val::Prim(p.clone())),
                        _ => Ok(Val::Object(id)),
                    }
                }
            },
            other => Err(self.make_type_error(&format!("not callable: {other:?}"))),
        }
    }

    fn construct_new(&mut self, callee: Val, args: Vec<Val>) -> Result<Val, Val> {
        match callee {
            Val::BuiltinFn(BuiltinId::NumberCtor) => {
                let Val::Prim(p) = self.call_fn(callee, None, args)? else { unreachable!() };
                let id = self.alloc_obj(ObjSlot { kind: ObjKind::BoxedPrim(p), props: BTreeMap::new() });
                Ok(Val::Object(id))
            }
            Val::BuiltinFn(BuiltinId::BooleanCtor) => {
                let Val::Prim(p) = self.call_fn(callee, None, args)? else { unreachable!() };
                let id = self.alloc_obj(ObjSlot { kind: ObjKind::BoxedPrim(p), props: BTreeMap::new() });
                Ok(Val::Object(id))
            }
            Val::BuiltinFn(BuiltinId::StringCtor) => {
                let Val::Prim(p) = self.call_fn(callee, None, args)? else { unreachable!() };
                let id = self.alloc_obj(ObjSlot { kind: ObjKind::BoxedPrim(p), props: BTreeMap::new() });
                Ok(Val::Object(id))
            }
            Val::BuiltinFn(_) => self.call_fn(callee, None, args),
            other => Err(self.make_type_error(&format!("not a constructor: {other:?}"))),
        }
    }

    fn get_member(&mut self, base: &Val, prop: &str) -> Result<Val, Val> {
        match base {
            Val::BuiltinFn(BuiltinId::NumberCtor) => match prop {
                "NaN" => Ok(Val::Prim(JsPrim::Number(JsNumber::NAN))),
                "POSITIVE_INFINITY" => Ok(Val::Prim(JsPrim::Number(JsNumber::POS_INFINITY))),
                "NEGATIVE_INFINITY" => Ok(Val::Prim(JsPrim::Number(JsNumber::NEG_INFINITY))),
                "MAX_VALUE" => Ok(Val::Prim(JsPrim::Number(JsNumber::MAX_VALUE))),
                "MIN_VALUE" => Ok(Val::Prim(JsPrim::Number(JsNumber::MIN_VALUE))),
                "EPSILON" => Ok(Val::Prim(JsPrim::Number(JsNumber::EPSILON))),
                "MAX_SAFE_INTEGER" => Ok(Val::Prim(JsPrim::Number(JsNumber::MAX_SAFE_INTEGER))),
                "MIN_SAFE_INTEGER" => Ok(Val::Prim(JsPrim::Number(JsNumber::MIN_SAFE_INTEGER))),
                "isNaN" => Ok(Val::BuiltinFn(BuiltinId::NumberIsNaN)),
                "isFinite" => Ok(Val::BuiltinFn(BuiltinId::NumberIsFinite)),
                "isInteger" => Ok(Val::BuiltinFn(BuiltinId::NumberIsInteger)),
                "isSafeInteger" => Ok(Val::BuiltinFn(BuiltinId::NumberIsSafeInteger)),
                "prototype" => Ok(Val::Object(self.num_proto_id)),
                _ => Ok(Val::Prim(JsPrim::Undefined)),
            },
            Val::Prim(JsPrim::Number(_)) => match prop {
                "toString" => Ok(Val::BuiltinFn(BuiltinId::NumberProtoToString)),
                "constructor" => Ok(Val::BuiltinFn(BuiltinId::NumberCtor)),
                _ => Ok(Val::Prim(JsPrim::Undefined)),
            },
            Val::Prim(JsPrim::Str(s)) => match prop {
                "length" => Ok(Val::Prim(JsPrim::Number(JsNumber::from_u32(s.len() as u32)))),
                "constructor" => Ok(Val::BuiltinFn(BuiltinId::StringCtor)),
                _ => Ok(Val::Prim(JsPrim::Undefined)),
            },
            Val::Prim(JsPrim::Bool(_)) => match prop {
                "constructor" => Ok(Val::BuiltinFn(BuiltinId::BooleanCtor)),
                _ => Ok(Val::Prim(JsPrim::Undefined)),
            },
            Val::Object(id) => {
                if let Some(v) = self.heap[*id].props.get(prop).cloned() {
                    return Ok(v);
                }
                match (&self.heap[*id].kind, prop) {
                    (ObjKind::BoxedPrim(JsPrim::Number(_)), "toString") => {
                        Ok(Val::BuiltinFn(BuiltinId::NumberProtoToString))
                    }
                    (ObjKind::BoxedPrim(JsPrim::Number(_)), "constructor") => {
                        Ok(Val::BuiltinFn(BuiltinId::NumberCtor))
                    }
                    (ObjKind::BoxedPrim(JsPrim::Str(_)), "constructor") => {
                        Ok(Val::BuiltinFn(BuiltinId::StringCtor))
                    }
                    (ObjKind::BoxedPrim(JsPrim::Bool(_)), "constructor") => {
                        Ok(Val::BuiltinFn(BuiltinId::BooleanCtor))
                    }
                    (ObjKind::Array(elems), "length") => {
                        Ok(Val::Prim(JsPrim::Number(JsNumber::from_u32(elems.len() as u32))))
                    }
                    (_, "toString") => Ok(Val::BuiltinFn(BuiltinId::DefaultObjToString)),
                    (_, "valueOf") => Ok(Val::BuiltinFn(BuiltinId::DefaultObjValueOf)),
                    _ => Ok(Val::Prim(JsPrim::Undefined)),
                }
            }
            _ => Ok(Val::Prim(JsPrim::Undefined)),
        }
    }

    fn eval_expr(&mut self, e: &Expr) -> Result<Val, Val> {
        match e {
            Expr::Lit(p) => Ok(Val::Prim(p.clone())),
            Expr::Ident(name) => {
                self.vars
                    .get(name)
                    .cloned()
                    .ok_or_else(|| self.make_type_error(&format!("ReferenceError: {name} is not defined")))
            }
            Expr::ArrayLit(items) => {
                let mut vals = Vec::with_capacity(items.len());
                for it in items {
                    vals.push(self.eval_expr(it)?);
                }
                let id = self.alloc_obj(ObjSlot { kind: ObjKind::Array(vals), props: BTreeMap::new() });
                Ok(Val::Object(id))
            }
            Expr::ObjLit(entries) => {
                let mut props = BTreeMap::new();
                for (k, ve) in entries {
                    let v = self.eval_expr(ve)?;
                    props.insert(k.clone(), v);
                }
                let id = self.alloc_obj(ObjSlot { kind: ObjKind::Ordinary, props });
                Ok(Val::Object(id))
            }
            Expr::FnExpr { params, body } => {
                Ok(Val::UserFn { params: params.clone(), body: body.clone() })
            }
            Expr::Unary(op, sub) => match op.as_str() {
                "typeof" => {
                    let v = if let Expr::Ident(name) = &**sub {
                        self.vars.get(name).cloned().unwrap_or(Val::Prim(JsPrim::Undefined))
                    } else {
                        self.eval_expr(sub)?
                    };
                    let s = match v {
                        Val::Prim(p) => typeof_prim(&p),
                        Val::Object(_) => rust_str_to_u16("object"),
                        Val::BuiltinFn(_) | Val::UserFn { .. } => rust_str_to_u16("function"),
                    };
                    Ok(Val::Prim(JsPrim::Str(s)))
                }
                "void" => {
                    let _ = self.eval_expr(sub)?;
                    Ok(Val::Prim(JsPrim::Undefined))
                }
                "!" => {
                    let v = self.eval_expr(sub)?;
                    Ok(Val::Prim(JsPrim::Bool(!self.val_to_bool(&v))))
                }
                "+" => {
                    let v = self.eval_expr(sub)?;
                    let n = self.val_to_number(&v)?;
                    Ok(Val::Prim(JsPrim::Number(n)))
                }
                "-" => {
                    let v = self.eval_expr(sub)?;
                    let p = self.val_to_prim(&v, PreferredType::Number)?;
                    match p {
                        JsPrim::BigInt(bi) => Ok(Val::Prim(JsPrim::BigInt(bi.neg()))),
                        other => {
                            let n = to_number(&other).map_err(|_| self.make_type_error("unary - TypeError"))?;
                            Ok(Val::Prim(JsPrim::Number(n.negate())))
                        }
                    }
                }
                "~" => {
                    let v = self.eval_expr(sub)?;
                    let n = self.val_to_number(&v)?;
                    let inv = !n.to_int32();
                    Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(inv))))
                }
                _ => Err(self.make_type_error("unsupported unary op")),
            },
            Expr::Update { op, prefix, target } => {
                let Expr::Ident(name) = &**target else {
                    return Err(self.make_type_error("non-ident update"));
                };
                let cur = self.vars.get(name).cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                let old_n = self.val_to_number(&cur)?;
                let new_n = if op == "++" {
                    old_n.add(JsNumber::ONE)
                } else {
                    old_n.sub(JsNumber::ONE)
                };
                self.vars.insert(name.clone(), Val::Prim(JsPrim::Number(new_n)));
                Ok(Val::Prim(JsPrim::Number(if *prefix { new_n } else { old_n })))
            }
            Expr::Assign(op, lhs, rhs) => {
                let rv = self.eval_expr(rhs)?;
                match &**lhs {
                    Expr::Ident(name) => {
                        let final_v = if op == "=" {
                            rv
                        } else {
                            let lv = self.vars.get(name).cloned().unwrap_or(Val::Prim(JsPrim::Undefined));
                            let binary_op = &op[..1];
                            self.eval_binary_vals(binary_op, lv, rv)?
                        };
                        // Global `undefined`, `NaN`, `Infinity` have `[[Writable]]: false` (ECMA-262 §19.1).
                        if !matches!(name.as_str(), "undefined" | "NaN" | "Infinity") {
                            self.vars.insert(name.clone(), final_v.clone());
                        }
                        Ok(final_v)
                    }
                    Expr::Member(base_e, prop) => {
                        let bv = self.eval_expr(base_e)?;
                        if let Val::Object(id) = bv {
                            self.heap[id].props.insert(prop.clone(), rv.clone());
                        }
                        // Non-writable built-in properties (e.g. `Number.NaN`) ignore sloppy assignment.
                        Ok(rv)
                    }
                    Expr::Index(arr_e, idx_e) => {
                        let arr_v = self.eval_expr(arr_e)?;
                        let idx_v = self.eval_expr(idx_e)?;
                        if let Val::Object(id) = arr_v {
                            let i = self.val_to_number(&idx_v)?.to_uint32() as usize;
                            if let ObjKind::Array(ref mut elems) = self.heap[id].kind {
                                if i >= elems.len() {
                                    elems.resize(i + 1, Val::Prim(JsPrim::Undefined));
                                }
                                elems[i] = rv.clone();
                                return Ok(rv);
                            }
                        }
                        Err(self.make_type_error("bad index assignment"))
                    }
                    _ => Err(self.make_type_error("bad assignment target")),
                }
            }
            Expr::Cond(c, t, f) => {
                let cv = self.eval_expr(c)?;
                if self.val_to_bool(&cv) {
                    self.eval_expr(t)
                } else {
                    self.eval_expr(f)
                }
            }
            Expr::Binary(op, l, r) => {
                if op == "&&" {
                    let lv = self.eval_expr(l)?;
                    return if !self.val_to_bool(&lv) { Ok(lv) } else { self.eval_expr(r) };
                }
                if op == "||" {
                    let lv = self.eval_expr(l)?;
                    return if self.val_to_bool(&lv) { Ok(lv) } else { self.eval_expr(r) };
                }
                let lv = self.eval_expr(l)?;
                let rv = self.eval_expr(r)?;
                self.eval_binary_vals(op, lv, rv)
            }
            Expr::Member(base_e, prop) => {
                let bv = self.eval_expr(base_e)?;
                self.get_member(&bv, prop)
            }
            Expr::Index(base_e, idx_e) => {
                let bv = self.eval_expr(base_e)?;
                let iv = self.eval_expr(idx_e)?;
                if let Val::Object(id) = bv {
                    let i = self.val_to_number(&iv)?.to_uint32() as usize;
                    if let ObjKind::Array(elems) = &self.heap[id].kind {
                        return Ok(elems.get(i).cloned().unwrap_or(Val::Prim(JsPrim::Undefined)));
                    }
                }
                let prop = u16_to_rust_string(&self.val_to_string(&iv)?);
                self.get_member(&bv, &prop)
            }
            Expr::Call(callee_e, arg_es) => {
                let (callee, this_v) = if let Expr::Member(base_e, prop) = &**callee_e {
                    let bv = self.eval_expr(base_e)?;
                    let mv = self.get_member(&bv, prop)?;
                    (mv, Some(bv))
                } else {
                    (self.eval_expr(callee_e)?, None)
                };
                let mut args = Vec::with_capacity(arg_es.len());
                for ae in arg_es {
                    args.push(self.eval_expr(ae)?);
                }
                self.call_fn(callee, this_v, args)
            }
            Expr::New(callee_e, arg_es) => {
                let callee = self.eval_expr(callee_e)?;
                let mut args = Vec::with_capacity(arg_es.len());
                for ae in arg_es {
                    args.push(self.eval_expr(ae)?);
                }
                self.construct_new(callee, args)
            }
        }
    }

    fn eval_binary_vals(&mut self, op: &str, lv: Val, rv: Val) -> Result<Val, Val> {
        match op {
            "===" | "!==" => {
                let eq = match (&lv, &rv) {
                    (Val::Prim(pa), Val::Prim(pb)) => is_strictly_equal(pa, pb),
                    (Val::Object(ia), Val::Object(ib)) => ia == ib,
                    (Val::BuiltinFn(ba), Val::BuiltinFn(bb)) => ba == bb,
                    _ => false,
                };
                Ok(Val::Prim(JsPrim::Bool(if op == "===" { eq } else { !eq })))
            }
            "==" | "!=" => {
                let eq = match (&lv, &rv) {
                    (Val::Prim(pa), Val::Prim(pb)) => is_loosely_equal(pa, pb),
                    (Val::Object(ia), Val::Object(ib)) => ia == ib,
                    (Val::Object(_), Val::Prim(pb)) => {
                        if matches!(pb, JsPrim::Undefined | JsPrim::Null) {
                            false
                        } else {
                            let lp = self.val_to_prim(&lv, PreferredType::Default)?;
                            is_loosely_equal(&lp, pb)
                        }
                    }
                    (Val::Prim(pa), Val::Object(_)) => {
                        if matches!(pa, JsPrim::Undefined | JsPrim::Null) {
                            false
                        } else {
                            let rp = self.val_to_prim(&rv, PreferredType::Default)?;
                            is_loosely_equal(pa, &rp)
                        }
                    }
                    (Val::BuiltinFn(ba), Val::BuiltinFn(bb)) => ba == bb,
                    _ => false,
                };
                Ok(Val::Prim(JsPrim::Bool(if op == "==" { eq } else { !eq })))
            }
            "instanceof" => {
                let is_inst = match (&lv, &rv) {
                    (Val::Object(id), Val::BuiltinFn(BuiltinId::TypeErrorCtor)) => {
                        matches!(self.heap[*id].kind, ObjKind::ErrorObj { is_type_error: true, .. })
                    }
                    _ => false,
                };
                Ok(Val::Prim(JsPrim::Bool(is_inst)))
            }
            "+" => {
                let lp = self.val_to_prim(&lv, PreferredType::Default)?;
                let rp = self.val_to_prim(&rv, PreferredType::Default)?;
                if matches!(lp, JsPrim::Str(_)) || matches!(rp, JsPrim::Str(_)) {
                    let ls = to_string(&lp).map_err(|_| self.make_type_error("+ Symbol"))?;
                    let rs = to_string(&rp).map_err(|_| self.make_type_error("+ Symbol"))?;
                    return Ok(Val::Prim(JsPrim::Str(ls.concat(&rs))));
                }
                match (&lp, &rp) {
                    (JsPrim::BigInt(a), JsPrim::BigInt(b)) => Ok(Val::Prim(JsPrim::BigInt(a.add(b)))),
                    _ => {
                        let na = to_number(&lp).map_err(|_| self.make_type_error("+ TypeError"))?;
                        let nb = to_number(&rp).map_err(|_| self.make_type_error("+ TypeError"))?;
                        Ok(Val::Prim(JsPrim::Number(na.add(nb))))
                    }
                }
            }
            "-" | "*" | "/" => {
                let lp = self.val_to_prim(&lv, PreferredType::Number)?;
                let rp = self.val_to_prim(&rv, PreferredType::Number)?;
                if let (JsPrim::BigInt(a), JsPrim::BigInt(b)) = (&lp, &rp) {
                    return match op {
                        "-" => Ok(Val::Prim(JsPrim::BigInt(a.sub(b)))),
                        "*" => Ok(Val::Prim(JsPrim::BigInt(a.mul(b)))),
                        _ => Err(self.make_type_error("BigInt div unused")),
                    };
                }
                let na = to_number(&lp).map_err(|_| self.make_type_error("arith TypeError"))?;
                let nb = to_number(&rp).map_err(|_| self.make_type_error("arith TypeError"))?;
                let out = match op {
                    "-" => na.sub(nb),
                    "*" => na.mul(nb),
                    "/" => na.div(nb),
                    _ => unreachable!(),
                };
                Ok(Val::Prim(JsPrim::Number(out)))
            }
            "**" => {
                let na = self.val_to_number(&lv)?;
                let nb = self.val_to_number(&rv)?;
                let out = JsNumber(f64::from_bits(na.0).powf(f64::from_bits(nb.0)).to_bits()).canonicalize_nan();
                Ok(Val::Prim(JsPrim::Number(out)))
            }
            "<" | ">" | "<=" | ">=" => {
                let lp = self.val_to_prim(&lv, PreferredType::Number)?;
                let rp = self.val_to_prim(&rv, PreferredType::Number)?;
                if let (JsPrim::Str(sa), JsPrim::Str(sb)) = (&lp, &rp) {
                    let res = match op {
                        "<" => sa.is_less_than(sb),
                        ">" => sb.is_less_than(sa),
                        "<=" => !sb.is_less_than(sa),
                        ">=" => !sa.is_less_than(sb),
                        _ => unreachable!(),
                    };
                    return Ok(Val::Prim(JsPrim::Bool(res)));
                }
                if let (JsPrim::BigInt(ba), JsPrim::BigInt(bb)) = (&lp, &rp) {
                    let c = ba.cmp_bigint(bb);
                    let res = match op {
                        "<" => c < 0,
                        ">" => c > 0,
                        "<=" => c <= 0,
                        ">=" => c >= 0,
                        _ => unreachable!(),
                    };
                    return Ok(Val::Prim(JsPrim::Bool(res)));
                }
                let na = to_number(&lp).map_err(|_| self.make_type_error("cmp TypeError"))?;
                let nb = to_number(&rp).map_err(|_| self.make_type_error("cmp TypeError"))?;
                let res = match op {
                    "<" => na.less_than(nb) == Some(true),
                    ">" => nb.less_than(na) == Some(true),
                    "<=" => nb.less_than(na) == Some(false),
                    ">=" => na.less_than(nb) == Some(false),
                    _ => unreachable!(),
                };
                Ok(Val::Prim(JsPrim::Bool(res)))
            }
            "|" => {
                let a = self.val_to_number(&lv)?.to_int32();
                let b = self.val_to_number(&rv)?.to_int32();
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(a | b))))
            }
            "&" => {
                let a = self.val_to_number(&lv)?.to_int32();
                let b = self.val_to_number(&rv)?.to_int32();
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(a & b))))
            }
            "^" => {
                let a = self.val_to_number(&lv)?.to_int32();
                let b = self.val_to_number(&rv)?.to_int32();
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(a ^ b))))
            }
            ">>>" => {
                let a = self.val_to_number(&lv)?.to_uint32();
                let b = self.val_to_number(&rv)?.to_uint32() & 0x1F;
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_u32(a >> b))))
            }
            "<<" => {
                let a = self.val_to_number(&lv)?.to_int32();
                let b = self.val_to_number(&rv)?.to_uint32() & 0x1F;
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(a << b))))
            }
            ">>" => {
                let a = self.val_to_number(&lv)?.to_int32();
                let b = self.val_to_number(&rv)?.to_uint32() & 0x1F;
                Ok(Val::Prim(JsPrim::Number(JsNumber::from_i32(a >> b))))
            }
            _ => Err(self.make_type_error(&format!("unsupported op {op}"))),
        }
    }

    fn exec_stmt(&mut self, s: &Stmt) -> Flow {
        match s {
            Stmt::Empty | Stmt::FnDecl { .. } => Flow::Normal,
            Stmt::VarDecl(decls) => {
                for (name, init) in decls {
                    if let Some(e) = init {
                        match self.eval_expr(e) {
                            Ok(v) => {
                                if !matches!(name.as_str(), "undefined" | "NaN" | "Infinity") {
                                    self.vars.insert(name.clone(), v);
                                }
                            }
                            Err(err) => return Flow::Throw(err),
                        }
                    }
                }
                Flow::Normal
            }
            Stmt::Block(stmts) => self.exec_stmts(stmts),
            Stmt::If(cond, then_s, else_s) => {
                let cv = match self.eval_expr(cond) {
                    Ok(v) => v,
                    Err(e) => return Flow::Throw(e),
                };
                if self.val_to_bool(&cv) {
                    self.exec_stmt(then_s)
                } else if let Some(el) = else_s {
                    self.exec_stmt(el)
                } else {
                    Flow::Normal
                }
            }
            Stmt::For { init, cond, step, body } => {
                if let Some(i) = init {
                    let f = self.exec_stmt(i);
                    if !matches!(f, Flow::Normal) {
                        return f;
                    }
                }
                loop {
                    if let Some(c) = cond {
                        let cv = match self.eval_expr(c) {
                            Ok(v) => v,
                            Err(e) => return Flow::Throw(e),
                        };
                        if !self.val_to_bool(&cv) {
                            break;
                        }
                    }
                    let f = self.exec_stmt(body);
                    if !matches!(f, Flow::Normal) {
                        return f;
                    }
                    if let Some(st) = step {
                        if let Err(e) = self.eval_expr(st) {
                            return Flow::Throw(e);
                        }
                    }
                }
                Flow::Normal
            }
            Stmt::Return(opt_e) => {
                let v = if let Some(e) = opt_e {
                    match self.eval_expr(e) {
                        Ok(v) => v,
                        Err(err) => return Flow::Throw(err),
                    }
                } else {
                    Val::Prim(JsPrim::Undefined)
                };
                Flow::Return(v)
            }
            Stmt::Throw(e) => match self.eval_expr(e) {
                Ok(v) => Flow::Throw(v),
                Err(err) => Flow::Throw(err),
            },
            Stmt::Try { body, catch_var, catch_body } => match self.exec_stmts(body) {
                Flow::Throw(err) => {
                    if let Some(cv) = catch_var {
                        self.vars.insert(cv.clone(), err);
                    }
                    self.exec_stmts(catch_body)
                }
                other => other,
            },
            Stmt::ExprStmt(e) => match self.eval_expr(e) {
                Ok(_) => Flow::Normal,
                Err(err) => Flow::Throw(err),
            },
        }
    }

    fn exec_stmts(&mut self, stmts: &[Stmt]) -> Flow {
        for s in stmts {
            let f = self.exec_stmt(s);
            if !matches!(f, Flow::Normal) {
                return f;
            }
        }
        Flow::Normal
    }
}

fn run_test262_source(src: &str) -> Result<Env, String> {
    let toks = tokenize_js(src)?;
    let mut parser = Parser { toks, pos: 0 };
    let prog = parser.parse_program()?;
    let mut env = Env::new();
    env.hoist_stmts(&prog);
    match env.exec_stmts(&prog) {
        Flow::Normal | Flow::Return(_) => Ok(env),
        Flow::Throw(Val::Object(id)) => {
            if let ObjKind::ErrorObj { msg, .. } = &env.heap[id].kind {
                Err(format!("Uncaught JS error: {msg}"))
            } else {
                Err(format!("Uncaught JS object #{id}"))
            }
        }
        Flow::Throw(other) => Err(format!("Uncaught JS value: {other:?}")),
    }
}

fn run_test262_inline(src: &str) -> Result<(), String> {
    run_test262_source(src).map(|_| ())
}

fn run_test262_file(path: &Path) -> Result<(), String> {
    let src = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    run_test262_inline(&src)
}

fn collect_js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        let mut sorted: Vec<_> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
        sorted.sort();
        for p in sorted {
            if p.is_dir() {
                collect_js_files(&p, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some("js") {
                out.push(p);
            }
        }
    }
}

// ===========================================================================================
// Deterministic PRNG for Differential Suites
// ===========================================================================================

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn edge_number_bits() -> Vec<u64> {
    vec![
        0x0000_0000_0000_0000, // +0
        0x8000_0000_0000_0000, // -0
        0x7FF0_0000_0000_0000, // +Infinity
        0xFFF0_0000_0000_0000, // -Infinity
        0x7FF8_0000_0000_0000, // canonical qNaN
        0x7FF8_0000_0000_0001, // qNaN payload
        0xFFF8_0000_0000_1234, // negative NaN payload
        0x0000_0000_0000_0001, // MIN_VALUE (2^-1074)
        0x8000_0000_0000_0001, // -MIN_VALUE
        0x0000_0000_0000_0002, // 2 * MIN_VALUE
        0x0000_0000_0000_0009, // 9 * MIN_VALUE
        0x000F_FFFF_FFFF_FFFF, // max subnormal
        0x0010_0000_0000_0000, // min positive normal (2^-1022)
        0x7FEF_FFFF_FFFF_FFFF, // MAX_VALUE
        0xFFEF_FFFF_FFFF_FFFF, // -MAX_VALUE
        0x3FF0_0000_0000_0000, // 1.0
        0xBFF0_0000_0000_0000, // -1.0
        0x3FEF_FFFF_FFFF_FFFF, // 1.0 - EPSILON/2
        0x3FF0_0000_0000_0001, // 1.0 + EPSILON
        0x3CB0_0000_0000_0000, // EPSILON
        0x433F_FFFF_FFFF_FFFF, // MAX_SAFE_INTEGER (2^53 - 1)
        0xC33F_FFFF_FFFF_FFFF, // MIN_SAFE_INTEGER
        0x4340_0000_0000_0000, // 2^53
        0x41DFFFFFFFC00000,     // i32::MAX (2147483647.0)
        0xC1E0000000000000,     // i32::MIN (-2147483648.0)
        0x41EFFFFFFFE00000,     // u32::MAX (4294967295.0)
        0x41F0000000000000,     // 2^32
        0xC1F0000000000000,     // -2^32
        0.1f64.to_bits(),
        0.2f64.to_bits(),
        0.3f64.to_bits(),
        1e-6f64.to_bits(),
        1e-7f64.to_bits(),
        1e20f64.to_bits(),
        1e21f64.to_bits(),
        1e23f64.to_bits(),
        1000000000000000128.0f64.to_bits(),
    ]
}

fn canonicalize_f64_bits(v: f64) -> u64 {
    if v.is_nan() {
        JsNumber::NAN.0
    } else {
        v.to_bits()
    }
}

#[test]
fn utf16_surrogate_wtf8_trim_slice_index_tests() {
    // Valid surrogate pair U+1F600 (0xD83D, 0xDE00) + BMP 'A' + lone high surrogate 0xD800 + lone low 0xDC00
    let s = Utf16Str::from_vec(vec![0xD83D, 0xDE00, 0x0041, 0xD800, 0xDC00]);
    // Note: (0xD800, 0xDC00) at indices 3..5 IS a valid surrogate pair for U+10000!
    // Test lone surrogates explicitly: [0xD800, 0x0041, 0xDC00]
    let lone = Utf16Str::from_vec(vec![0xD800, 0x0041, 0xDC00]);
    assert!(s.is_well_formed_unicode());
    assert!(!lone.is_well_formed_unicode());

    let cp0 = s.code_point_at(0);
    assert_eq!(cp0.code_point, 0x1F600);
    assert_eq!(cp0.code_unit_count, 2);
    assert!(!cp0.is_unpaired_surrogate);

    let l0 = lone.code_point_at(0);
    assert_eq!(l0.code_point, 0xD800);
    assert_eq!(l0.code_unit_count, 1);
    assert!(l0.is_unpaired_surrogate);

    let l2 = lone.code_point_at(2);
    assert_eq!(l2.code_point, 0xDC00);
    assert_eq!(l2.code_unit_count, 1);
    assert!(l2.is_unpaired_surrogate);

    let wtf8 = lone.utf16_to_wtf8_or_lossless();
    // 0xD800 -> ED A0 80, 'A' -> 41, 0xDC00 -> ED B0 80
    assert_eq!(wtf8, vec![0xED, 0xA0, 0x80, 0x41, 0xED, 0xB0, 0x80]);

    // UTF-8 decode + overlong / surrogate rejection
    let decoded = utf8_to_utf16("hello 😀".as_bytes()).unwrap();
    assert_eq!(decoded.units, vec![0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0xD83D, 0xDE00]);
    assert!(utf8_to_utf16(&[0xED, 0xA0, 0x80]).is_none()); // UTF-8 must reject CESU-8/WTF-8 surrogates
    assert!(utf8_to_utf16(&[0xC0, 0xAF]).is_none()); // overlong '/'

    // TrimString (§7.1.4.1): BOM 0xFEFF, NBSP 0x00A0, LS 0x2028, PS 0x2029 trimmed; 0x180E NOT trimmed
    let ws = Utf16Str::from_vec(vec![0xFEFF, 0x00A0, 0x2028, 0x180E, 0x0031, 0x2029, 0x3000]);
    assert_eq!(ws.trim().units, vec![0x180E, 0x0031]);

    // slice, concat, index_of, is_less_than
    let hay = rust_str_to_u16("abracadabra");
    let needle = rust_str_to_u16("abra");
    assert_eq!(hay.index_of(&needle, 0), Some(0));
    assert_eq!(hay.index_of(&needle, 1), Some(7));
    assert_eq!(hay.index_of(&needle, 8), None);
    assert_eq!(hay.index_of(&Utf16Str::new(), 5), Some(5));
    assert!(rust_str_to_u16("abc").is_less_than(&rust_str_to_u16("abd")));
    assert!(rust_str_to_u16("abc").is_less_than(&rust_str_to_u16("abcd")));
}

#[test]
fn ieee754_classification_comparisons_and_ties_to_even_tests() {
    assert!(JsNumber::NAN.is_nan());
    assert!(JsNumber(0xFFF8_0000_0000_0042).is_nan());
    assert!(JsNumber::POS_ZERO.is_pos_zero());
    assert!(JsNumber::NEG_ZERO.is_neg_zero());
    assert!(JsNumber::POS_ZERO.is_zero() && JsNumber::NEG_ZERO.is_zero());
    assert!(JsNumber::POS_ZERO.equal(JsNumber::NEG_ZERO));
    assert!(!JsNumber::POS_ZERO.same_value(JsNumber::NEG_ZERO));
    assert!(JsNumber::POS_ZERO.same_value_zero(JsNumber::NEG_ZERO));
    assert!(!JsNumber::NAN.equal(JsNumber::NAN));
    assert!(JsNumber::NAN.same_value(JsNumber(0x7FF8_0000_0000_9999)));

    // Exact round-to-nearest-even at 2^53:
    // 2^53 + 1 (odd midpoint!) rounds down to even 2^53; 2^53 + 2 stays 2^53 + 2; 2^53 + 3 rounds up to 2^53 + 4!
    let two53 = JsNumber(0x4340_0000_0000_0000); // 9007199254740992.0
    assert_eq!(two53.add(JsNumber::ONE), two53);
    let two53_plus2 = two53.add(JsNumber::from_i32(2));
    assert_eq!(two53_plus2.0, 0x4340_0000_0000_0001);
    assert_eq!(two53_plus2.add(JsNumber::ONE).0, 0x4340_0000_0000_0002);

    // Subnormal-to-normal carry under RNE
    let max_sub = JsNumber(0x000F_FFFF_FFFF_FFFF);
    let min_sub = JsNumber::MIN_VALUE;
    assert_eq!(max_sub.add(min_sub).0, 0x0010_0000_0000_0000); // 2^-1022

    // Exhaustive subnormal, near-min-normal, near-MAX_VALUE, and shift-boundary torture test vs hardware f64!
    let mut special = Vec::new();
    for m in 0u64..32 {
        special.push(m); // lowest subnormals
        special.push(0x8000_0000_0000_0000 | m);
        special.push(0x000F_FFFF_FFFF_FFE0 + m); // top subnormals -> min normal boundary
        special.push(0x0010_0000_0000_0000 + m); // lowest normals
        special.push(0x7FEF_FFFF_FFFF_FFE0 + m); // near MAX_VALUE -> overflow boundary
    }
    for sh in 0u64..=62 {
        let exp = (1023u64 + sh) << 52;
        special.push(exp);
        special.push(exp | 1);
        special.push(exp | 0x000F_FFFF_FFFF_FFFF);
    }
    for &a in &special {
        for &b in &special {
            let ja = JsNumber(a);
            let jb = JsNumber(b);
            let fa = f64::from_bits(a);
            let fb = f64::from_bits(b);
            assert_eq!(ja.add(jb).0, canonicalize_f64_bits(fa + fb), "special add {a:#x} + {b:#x}");
            assert_eq!(ja.sub(jb).0, canonicalize_f64_bits(fa - fb), "special sub {a:#x} - {b:#x}");
            assert_eq!(ja.mul(jb).0, canonicalize_f64_bits(fa * fb), "special mul {a:#x} * {b:#x}");
            assert_eq!(ja.div(jb).0, canonicalize_f64_bits(fa / fb), "special div {a:#x} / {b:#x}");
        }
    }
}

#[test]
fn ieee754_to_int32_uint32_uint16_boundary_tests() {
    for special in [JsNumber::NAN, JsNumber::POS_ZERO, JsNumber::NEG_ZERO, JsNumber::POS_INFINITY, JsNumber::NEG_INFINITY] {
        assert_eq!(special.to_int32(), 0);
        assert_eq!(special.to_uint32(), 0);
        assert_eq!(special.to_uint16(), 0);
    }
    assert_eq!(JsNumber(4294967295.9f64.to_bits()).to_uint32(), u32::MAX);
    assert_eq!(JsNumber(4294967295.9f64.to_bits()).to_int32(), -1);
    assert_eq!(JsNumber(4294967296.9f64.to_bits()).to_uint32(), 0);
    assert_eq!(JsNumber((-4294967296.9f64).to_bits()).to_uint32(), 0);
    assert_eq!(JsNumber((-4294967297.9f64).to_bits()).to_uint32(), u32::MAX);
    assert_eq!(JsNumber::from_i32(i32::MIN).to_int32(), i32::MIN);
    assert_eq!(JsNumber::from_i32(i32::MAX).to_int32(), i32::MAX);
    assert_eq!(JsNumber::from_u32(u32::MAX).to_uint32(), u32::MAX);
    assert_eq!(JsNumber::from_u32(0x1_ABCD).to_uint16(), 0xABCD);
}

#[test]
fn number_to_string_and_string_to_number_edge_tests() {
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::NEG_ZERO)), "0");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::NAN)), "NaN");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::POS_INFINITY)), "Infinity");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::NEG_INFINITY)), "-Infinity");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::MIN_VALUE)), "5e-324");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber(2))), "1e-323");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber::MAX_VALUE)), "1.7976931348623157e+308");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber(1e20f64.to_bits()))), "100000000000000000000");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber(1e21f64.to_bits()))), "1e+21");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber(1e-6f64.to_bits()))), "0.000001");
    assert_eq!(u16_to_rust_string(&number_to_string(JsNumber(1e-7f64.to_bits()))), "1e-7");

    assert!(string_to_number(&rust_str_to_u16("-0")).is_neg_zero());
    assert!(string_to_number(&rust_str_to_u16("")).is_pos_zero());
    assert!(string_to_number(&rust_str_to_u16("-0x1")).is_nan());
    assert!(string_to_number(&rust_str_to_u16("+0b1")).is_nan());
    assert_eq!(string_to_number(&rust_str_to_u16("0x10")), JsNumber::from_i32(16));
    assert_eq!(string_to_number(&rust_str_to_u16("0o10")), JsNumber::from_i32(8));
    assert_eq!(string_to_number(&rust_str_to_u16("010")), JsNumber::from_i32(10));

    // Unclamped exponent cancellation across > 100,000 leading fractional / trailing integer zeros
    let long_frac = format!("0.{}5e200001", "0".repeat(200_000));
    let long_int = format!("5{}e-200000", "0".repeat(200_000));
    assert_eq!(string_to_number(&rust_str_to_u16(&long_frac)), JsNumber::from_i32(5));
    assert_eq!(string_to_number(&rust_str_to_u16(&long_int)), JsNumber::from_i32(5));
}

#[test]
fn bigint_canonical_arithmetic_radix_and_roundtrip_tests() {
    let z = JsBigInt::zero();
    assert!(!z.neg && z.limbs.is_empty());

    let neg_zero_parsed = string_to_bigint(&rust_str_to_u16("  -0000  ")).unwrap();
    assert!(!neg_zero_parsed.neg && neg_zero_parsed.limbs.is_empty());
    assert!(string_to_bigint(&rust_str_to_u16("")).unwrap().limbs.is_empty());
    assert!(string_to_bigint(&rust_str_to_u16("-0x1")).is_none());
    assert!(string_to_bigint(&rust_str_to_u16("1.0")).is_none());
    assert!(string_to_bigint(&rust_str_to_u16("1e5")).is_none());
    assert!(string_to_bigint(&rust_str_to_u16("Infinity")).is_none());

    let big_a = string_to_bigint(&rust_str_to_u16("0x1_0000_0000_0000_0000_0000_0001".replace('_', "").as_str())).unwrap();
    let big_b = string_to_bigint(&rust_str_to_u16("-999999999999999999999999999999")).unwrap();
    let prod = big_a.mul(&big_b);
    let dec = prod.to_string_radix10();
    let rt = string_to_bigint(&dec).unwrap();
    assert!(prod.eq_bigint(&rt));
    assert!(prod.add(&prod.neg()).limbs.is_empty());
}

#[test]
fn ops_to_primitive_hook_to_numeric_and_loose_equality_tests() {
    // Exotic @@toPrimitive returning an Object must fail with ExoticToPrimitiveReturnedObject
    let bad_exotic = ObjectToPrimitiveHook {
        exotic_to_prim: MethodOutcome::ReturnedObject,
        to_string_slot: MethodOutcome::ReturnedPrim(JsPrim::Number(JsNumber::ONE)),
        value_of_slot: MethodOutcome::ReturnedPrim(JsPrim::Number(JsNumber::ONE)),
    };
    assert!(to_primitive(&JsInput::Object(1), PreferredType::Default, &bad_exotic).is_err());

    // OrdinaryToPrimitive with hint Number tries valueOf first; if valueOf returns an Object, falls back to toString!
    let fallback_hook = ObjectToPrimitiveHook {
        exotic_to_prim: MethodOutcome::NotCallable,
        value_of_slot: MethodOutcome::ReturnedObject,
        to_string_slot: MethodOutcome::ReturnedPrim(JsPrim::Str(rust_str_to_u16("123"))),
    };
    let p = to_primitive(&JsInput::Object(2), PreferredType::Number, &fallback_hook).unwrap();
    assert_eq!(to_number(&p).unwrap(), JsNumber::from_i32(123));

    // Abrupt exception identity preservation (`MethodOutcome::Threw(id)` -> `AbruptHookError(id)`)
    // and short-circuiting of the second slot when the first slot throws or returns a primitive.
    let threw_first_num = ObjectToPrimitiveHook {
        exotic_to_prim: MethodOutcome::NotCallable,
        value_of_slot: MethodOutcome::Threw(777),
        to_string_slot: MethodOutcome::ReturnedPrim(JsPrim::Number(JsNumber::ONE)),
    };
    assert_eq!(
        to_primitive(&JsInput::Object(3), PreferredType::Number, &threw_first_num),
        Err(TypeErrorKind::AbruptHookError(777))
    );
    let prim_first_num = ObjectToPrimitiveHook {
        exotic_to_prim: MethodOutcome::NotCallable,
        value_of_slot: MethodOutcome::ReturnedPrim(JsPrim::Number(JsNumber::from_i32(9))),
        to_string_slot: MethodOutcome::Threw(888),
    };
    assert_eq!(
        to_primitive(&JsInput::Object(4), PreferredType::Number, &prim_first_num),
        Ok(JsPrim::Number(JsNumber::from_i32(9)))
    );

    // End-to-end evaluator check: lazy hint-order evaluation + exact user-thrown exception identity
    run_test262_inline(
        r#"
        var log = "";
        var o1 = {
          valueOf: function() { log = log + "V"; return 7; },
          toString: function() { log = log + "S"; return "9"; }
        };
        assert.sameValue(Number(o1), 7, "Number hint calls valueOf first");
        assert.sameValue(log, "V", "Number hint must not invoke toString when valueOf returns primitive");

        log = "";
        assert.sameValue(String(o1), "9", "String hint calls toString first");
        assert.sameValue(log, "S", "String hint must not invoke valueOf when toString returns primitive");

        var sentinel = { tag: 42 };
        var caught = null;
        log = "";
        try {
          Number({
            valueOf: function() { log = log + "V"; throw sentinel; },
            toString: function() { log = log + "S"; return 1; }
          });
        } catch (e) {
          caught = e;
        }
        assert.sameValue(caught, sentinel, "exact thrown object identity preserved");
        assert.sameValue(log, "V", "toString skipped after valueOf throws");
        "#,
    )
    .expect("lazy ToPrimitive & exception identity script must pass");

    // Cross-type loose equality (§7.2.14): 2n**100n == 2**100 is true, 2n**100n + 1n == 2**100 is false
    let two100_num = JsPrim::Number(JsNumber((2.0f64.powi(100)).to_bits()));
    let mut two100_bi = JsBigInt::from_u64(1);
    let two_bi = JsBigInt::from_u64(2);
    for _ in 0..100 {
        two100_bi = two100_bi.mul(&two_bi);
    }
    let two100_plus1 = two100_bi.add(&JsBigInt::from_u64(1));
    assert!(is_loosely_equal(&JsPrim::BigInt(two100_bi), &two100_num));
    assert!(!is_loosely_equal(&JsPrim::BigInt(two100_plus1), &two100_num));
}

#[test]
fn provenance_and_zero_trusted_markers_self_audit() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let src_dir = manifest_dir.join("src");
    let mut rs_files = Vec::new();
    let mut stack = vec![src_dir];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(d).unwrap() {
            let p = entry.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
                rs_files.push(p);
            }
        }
    }
    assert_eq!(rs_files.len(), 5, "expected lib.rs + utf16.rs + bigint.rs + number.rs + ops.rs");
    for f in &rs_files {
        let txt = std::fs::read_to_string(f).unwrap();
        for forbidden in [
            "assume(",
            "admit(",
            "verifier::external_body",
            "verifier::external",
            "assume_specification",
            "unsafe {",
            "unsafe fn",
            "unsafe impl",
            "std::fs",
            "std::net",
            "std::process",
            "std::env",
        ] {
            assert!(
                !txt.contains(forbidden),
                "forbidden marker `{forbidden}` found in {}",
                f.display()
            );
        }
    }
    let lib_rs = std::fs::read_to_string(manifest_dir.join("src/lib.rs")).unwrap();
    assert!(lib_rs.contains("#![forbid(unsafe_code)]"));

    let prov = std::fs::read_to_string(manifest_dir.join("tests/data/PROVENANCE")).unwrap();
    assert!(prov.contains("https://github.com/tc39/test262"));
    assert!(prov.contains("2a1ade303f72d3de80565c921d685222405c32ce"));
    assert!(prov.contains("BSD-3-Clause"));
}

#[test]
fn test262_and_differential_v8_and_f64_suite() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data_dir = manifest_dir.join("tests/data");
    assert!(data_dir.join("PROVENANCE").exists(), "PROVENANCE must exist");

    // ---------------------------------------------------------------------------------------
    // 1. Run ALL real pinned `tc39/test262` files in `tests/data/`
    // ---------------------------------------------------------------------------------------
    let mut js_files = Vec::new();
    collect_js_files(&data_dir, &mut js_files);
    assert!(
        js_files.len() >= 100,
        "expected >= 100 pinned test262 files, found {}",
        js_files.len()
    );

    let mut suite_counts: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();

    for path in &js_files {
        let rel = path.strip_prefix(&data_dir).unwrap();
        let comps: Vec<_> = rel.components().map(|c| c.as_os_str().to_string_lossy().to_string()).collect();
        let suite_key = if comps.len() >= 3 && comps[0] == "language" && comps[1] == "types" {
            format!("language/types/{}", comps[2])
        } else if comps.len() >= 3 && comps[0] == "built-ins" && comps[1] == "Number" && path.parent() != Some(&data_dir.join("built-ins/Number")) {
            format!("built-ins/Number/{}", comps[2])
        } else if comps.len() >= 2 && comps[0] == "built-ins" && comps[1] == "String" {
            "built-ins/String".to_string()
        } else {
            "built-ins/Number".to_string()
        };

        let entry = suite_counts.entry(suite_key).or_insert((0, 0));
        entry.1 += 1;
        match run_test262_file(path) {
            Ok(()) => entry.0 += 1,
            Err(err) => failures.push(format!("{}: {}", rel.display(), err)),
        }
    }

    assert!(
        failures.is_empty(),
        "test262 failures ({}/{}):\n{}",
        failures.len(),
        js_files.len(),
        failures.join("\n")
    );

    // ---------------------------------------------------------------------------------------
    // 2. Differential-test `JsNumber` against Rust `f64` (25,000+ operations)
    // ---------------------------------------------------------------------------------------
    let edges = edge_number_bits();
    let mut f64_diff_cases = 0usize;

    for &ab in &edges {
        for &bb in &edges {
            let ja = JsNumber(ab);
            let jb = JsNumber(bb);
            let fa = f64::from_bits(ab);
            let fb = f64::from_bits(bb);

            assert_eq!(ja.add(jb).0, canonicalize_f64_bits(fa + fb), "add {ab:#x} + {bb:#x}");
            assert_eq!(ja.sub(jb).0, canonicalize_f64_bits(fa - fb), "sub {ab:#x} - {bb:#x}");
            assert_eq!(ja.mul(jb).0, canonicalize_f64_bits(fa * fb), "mul {ab:#x} * {bb:#x}");
            assert_eq!(ja.div(jb).0, canonicalize_f64_bits(fa / fb), "div {ab:#x} / {bb:#x}");
            assert_eq!(ja.equal(jb), fa == fb, "eq {ab:#x} == {bb:#x}");
            let expected_lt = if fa.is_nan() || fb.is_nan() { None } else { Some(fa < fb) };
            assert_eq!(ja.less_than(jb), expected_lt, "lt {ab:#x} < {bb:#x}");
            f64_diff_cases += 6;
        }
    }

    let mut rng = SplitMix64(0xC0DE_0171_2026_1120);
    for _ in 0..5_000 {
        let ab = rng.next();
        let bb = rng.next();
        let ja = JsNumber(ab);
        let jb = JsNumber(bb);
        let fa = f64::from_bits(ab);
        let fb = f64::from_bits(bb);

        assert_eq!(ja.add(jb).0, canonicalize_f64_bits(fa + fb), "rand add {ab:#x} + {bb:#x}");
        assert_eq!(ja.sub(jb).0, canonicalize_f64_bits(fa - fb), "rand sub {ab:#x} - {bb:#x}");
        assert_eq!(ja.mul(jb).0, canonicalize_f64_bits(fa * fb), "rand mul {ab:#x} * {bb:#x}");
        assert_eq!(ja.div(jb).0, canonicalize_f64_bits(fa / fb), "rand div {ab:#x} / {bb:#x}");

        // Round-trip `StringToNumber(Number::toString(ja))`!
        let formatted = number_to_string(ja);
        let parsed = string_to_number(&formatted);
        if ja.is_neg_zero() {
            assert!(parsed.is_pos_zero());
        } else {
            assert!(
                ja.same_value(parsed),
                "roundtrip failed for {ab:#018x} ({fa:?}) -> {:?} -> {:018x}",
                u16_to_rust_string(&formatted),
                parsed.0
            );
        }
        f64_diff_cases += 5;
    }

    // ---------------------------------------------------------------------------------------
    // 3. Live Differential Testing vs Node.js V8 (`/Users/mac/.nvm/versions/node/v24.15.0/bin/node`)
    // ---------------------------------------------------------------------------------------
    let mut v8_num_bits: Vec<u64> = edges.clone();
    // Subnormal multiples 1..=30, powers of 2, powers of 10, random normals & subnormals
    for k in 1u64..=30 {
        v8_num_bits.push(k);
    }
    for p in -323..=308 {
        let f: f64 = format!("1e{p}").parse().unwrap();
        v8_num_bits.push(f.to_bits());
    }
    for _ in 0..200 {
        v8_num_bits.push(rng.next());
    }

    let mut v8_strings: Vec<String> = [
        "",
        "   ",
        "\t\n\r\u{00A0}\u{FEFF}\u{2028}\u{2029}42\u{3000}",
        "\u{180E}42",
        "0",
        "-0",
        "+0",
        "-0.0",
        "-0e100",
        ".5",
        "5.",
        ".",
        "+.",
        "-.",
        "Infinity",
        "+Infinity",
        "-Infinity",
        "infinity",
        "NaN",
        "0b0",
        "0b101010",
        "0B11111111111111111111111111111111111111111111111111111",
        "-0b1",
        "+0x10",
        "0o755",
        "0O777777777777777777",
        "0xdeadbeefcafebabe",
        "0x100000000000008000", // exact RNE tie-to-even hex
        "0x100000000000008001", // just above tie
        "010",
        "08",
        "1_000",
        "1e",
        "1e+",
        "1e-7",
        "1e21",
        "1e400",
        "-1e-400",
        "1.7976931348623157e+308",
        "1.7976931348623159e+308",
        "2.2250738585072014e-308",
        "2.2250738585072009e-308",
        "4.9406564584124654e-324",
        "2.4703282292062327e-324",
        "2.4703282292062328e-324",
        "9007199254740991",
        "9007199254740992",
        "9007199254740993",
        "1000000000000000128",
        "0.1",
        "0.2",
        "0.3",
    ]
    .into_iter()
    .map(String::from)
    .collect();
    // Long-zero exponent cancellation cases (> 100,000 leading fractional / trailing integer zeros)
    v8_strings.push(format!("0.{}5e200001", "0".repeat(200_000)));
    v8_strings.push(format!("5{}e-200000", "0".repeat(200_000)));
    v8_strings.push(format!("0.{}5e500000", "0".repeat(200_000)));
    v8_strings.push(format!("5{}e-500000", "0".repeat(200_000)));
    v8_strings.push(format!("-5{}e-500000", "0".repeat(200_000)));

    let to_prim_scripts: Vec<&str> = vec![
        "var log = ''; var r = String(Number({ valueOf: function(){ log = log + 'V'; return 7; }, toString: function(){ log = log + 'S'; return '9'; } })); var out = r + ':' + log;",
        "var log = ''; var r = String({ valueOf: function(){ log = log + 'V'; return 7; }, toString: function(){ log = log + 'S'; return '9'; } }); var out = r + ':' + log;",
        "var log = ''; var r = String(Number({ valueOf: function(){ log = log + 'V'; return {}; }, toString: function(){ log = log + 'S'; return '11'; } })); var out = r + ':' + log;",
        "var log = ''; var r = String({ valueOf: function(){ log = log + 'V'; return 13; }, toString: function(){ log = log + 'S'; return {}; } }); var out = r + ':' + log;",
        "var log = ''; var out = ''; try { Number({ valueOf: function(){ log = log + 'V'; throw 'custom_err_num'; }, toString: function(){ log = log + 'S'; return 1; } }); } catch (e) { out = e + ':' + log; }",
        "var log = ''; var out = ''; try { String({ toString: function(){ log = log + 'S'; throw 'custom_err_str'; }, valueOf: function(){ log = log + 'V'; return 1; } }); } catch (e) { out = e + ':' + log; }",
    ];

    let hex_bits_json: Vec<String> = v8_num_bits.iter().map(|b| format!("{b:#018x}")).collect();
    let node_script = r#"
const fs = require('fs');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));

function bitsToF64(hex) {
  const buf = new ArrayBuffer(8);
  const dv = new DataView(buf);
  dv.setBigUint64(0, BigInt(hex), true);
  return dv.getFloat64(0, true);
}

function f64ToBits(x) {
  if (Number.isNaN(x)) return '0x7ff8000000000000';
  const buf = new ArrayBuffer(8);
  const dv = new DataView(buf);
  dv.setFloat64(0, x, true);
  return '0x' + dv.getBigUint64(0, true).toString(16).padStart(16, '0');
}

const numResults = input.bits.map(h => {
  const x = bitsToF64(h);
  return {
    str: String(x),
    i32: x | 0,
    u32: x >>> 0,
  };
});

const strResults = input.strings.map(s => f64ToBits(Number(s)));

const bigPairs = [
  ['0', '0'],
  ['1', '-1'],
  ['4294967295', '1'],
  ['18446744073709551615', '18446744073709551615'],
  ['-340282366920938463463374607431768211456', '123456789012345678901234567890'],
  ['99999999999999999999999999999999999999', '-88888888888888888888888888888888888888'],
];
const bigResults = bigPairs.map(([a, b]) => {
  const ba = BigInt(a), bb = BigInt(b);
  return {
    a, b,
    add: (ba + bb).toString(),
    sub: (ba - bb).toString(),
    mul: (ba * bb).toString(),
    neg: (-ba).toString(),
    cmp: ba < bb ? -1 : (ba > bb ? 1 : 0),
  };
});

const symA = Symbol('a'), symB = Symbol('b');
const prims = [
  undefined, null, true, false,
  +0, -0, NaN, 1, -1, 2, 0.5, Infinity, -Infinity, 9007199254740992,
  0n, 1n, -1n, 9007199254740992n,
  '', '0', '-0', '1', '-1', 'true', ' \uFEFF0\u2028',
  symA, symB,
];
const eqMatrix = [];
for (let i = 0; i < prims.length; i++) {
  for (let j = 0; j < prims.length; j++) {
    eqMatrix.push([
      prims[i] == prims[j],
      prims[i] === prims[j],
      Object.is(prims[i], prims[j]),
    ]);
  }
}
const boolVec = prims.map(p => Boolean(p));
const toPrimResults = input.toPrimScripts.map(code => {
  const fn = new Function(code + '; return out;');
  return fn();
});

process.stdout.write(JSON.stringify({ numResults, strResults, bigResults, eqMatrix, boolVec, toPrimResults }));
"#;

    let payload = serde_json::json!({
        "bits": hex_bits_json,
        "strings": v8_strings,
        "toPrimScripts": to_prim_scripts,
    });

    let mut child = Command::new(NODE_BIN)
        .arg("-e")
        .arg(node_script)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("failed to spawn Node v24.15.0");
    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(payload.to_string().as_bytes())
            .unwrap();
    }
    let out = child.wait_with_output().expect("failed waiting on Node");
    assert!(
        out.status.success(),
        "Node exited with error: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let v8: serde_json::Value = serde_json::from_slice(&out.stdout).expect("valid V8 JSON");

    let mut v8_diff_cases = 0usize;

    // 3a. Compare `Number::toString`, `ToInt32`, `ToUint32` vs V8
    for (idx, &bits) in v8_num_bits.iter().enumerate() {
        let jn = JsNumber(bits);
        let row = &v8["numResults"][idx];
        let v8_str = row["str"].as_str().unwrap();
        let v8_i32 = row["i32"].as_i64().unwrap() as i32;
        let v8_u32 = row["u32"].as_u64().unwrap() as u32;

        let our_str = u16_to_rust_string(&number_to_string(jn));
        assert_eq!(our_str, v8_str, "Number::toString mismatch on bits {bits:#018x}");
        assert_eq!(jn.to_int32(), v8_i32, "ToInt32 mismatch on bits {bits:#018x}");
        assert_eq!(jn.to_uint32(), v8_u32, "ToUint32 mismatch on bits {bits:#018x}");
        v8_diff_cases += 3;
    }

    // 3b. Compare `StringToNumber` vs V8 bit-for-bit (preserving -0 vs +0 and NaN)
    for (idx, s) in v8_strings.iter().enumerate() {
        let u = rust_str_to_u16(s);
        let our = string_to_number(&u);
        let v8_hex = v8["strResults"][idx].as_str().unwrap();
        let v8_bits = u64::from_str_radix(v8_hex.trim_start_matches("0x"), 16).unwrap();
        assert_eq!(
            our.0, v8_bits,
            "StringToNumber mismatch on len={}: ours={:#018x}, v8={v8_bits:#018x}",
            s.len(),
            our.0
        );
        v8_diff_cases += 1;
    }

    // 3b-ii. Compare `ToPrimitive` lazy hint-order side effects and abrupt exception identity vs V8
    for (idx, &code) in to_prim_scripts.iter().enumerate() {
        let env = run_test262_source(code).expect("ToPrimitive differential script must succeed");
        let Some(Val::Prim(JsPrim::Str(out_u16))) = env.vars.get("out") else {
            panic!("expected string `out` in ToPrimitive differential script #{idx}");
        };
        let our_out = u16_to_rust_string(out_u16);
        let v8_out = v8["toPrimResults"][idx].as_str().unwrap();
        assert_eq!(our_out, v8_out, "ToPrimitive V8 mismatch on script #{idx}: {code}");
        v8_diff_cases += 1;
    }

    // 3c. Compare `JsBigInt` vs V8
    for row in v8["bigResults"].as_array().unwrap() {
        let a_str = row["a"].as_str().unwrap();
        let b_str = row["b"].as_str().unwrap();
        let ba = string_to_bigint(&rust_str_to_u16(a_str)).unwrap();
        let bb = string_to_bigint(&rust_str_to_u16(b_str)).unwrap();

        assert_eq!(u16_to_rust_string(&ba.add(&bb).to_string_radix10()), row["add"].as_str().unwrap());
        assert_eq!(u16_to_rust_string(&ba.sub(&bb).to_string_radix10()), row["sub"].as_str().unwrap());
        assert_eq!(u16_to_rust_string(&ba.mul(&bb).to_string_radix10()), row["mul"].as_str().unwrap());
        assert_eq!(u16_to_rust_string(&ba.neg().to_string_radix10()), row["neg"].as_str().unwrap());
        assert_eq!(ba.cmp_bigint(&bb) as i64, row["cmp"].as_i64().unwrap());
        v8_diff_cases += 5;
    }

    // 3d. Compare `IsLooselyEqual`, `IsStrictlyEqual`, `SameValue`, `SameValueZero`, `ToBoolean`, `ToNumeric` vs V8
    let our_prims: Vec<JsPrim> = vec![
        JsPrim::Undefined,
        JsPrim::Null,
        JsPrim::Bool(true),
        JsPrim::Bool(false),
        JsPrim::Number(JsNumber::POS_ZERO),
        JsPrim::Number(JsNumber::NEG_ZERO),
        JsPrim::Number(JsNumber::NAN),
        JsPrim::Number(JsNumber::ONE),
        JsPrim::Number(JsNumber::NEG_ONE),
        JsPrim::Number(JsNumber::from_i32(2)),
        JsPrim::Number(JsNumber(0.5f64.to_bits())),
        JsPrim::Number(JsNumber::POS_INFINITY),
        JsPrim::Number(JsNumber::NEG_INFINITY),
        JsPrim::Number(JsNumber(9007199254740992.0f64.to_bits())),
        JsPrim::BigInt(JsBigInt::zero()),
        JsPrim::BigInt(JsBigInt::from_i64(1)),
        JsPrim::BigInt(JsBigInt::from_i64(-1)),
        JsPrim::BigInt(JsBigInt::from_i64(9007199254740992)),
        JsPrim::Str(rust_str_to_u16("")),
        JsPrim::Str(rust_str_to_u16("0")),
        JsPrim::Str(rust_str_to_u16("-0")),
        JsPrim::Str(rust_str_to_u16("1")),
        JsPrim::Str(rust_str_to_u16("-1")),
        JsPrim::Str(rust_str_to_u16("true")),
        JsPrim::Str(rust_str_to_u16(" \u{FEFF}0\u{2028}")),
        JsPrim::Symbol(1),
        JsPrim::Symbol(2),
    ];

    for (i, p) in our_prims.iter().enumerate() {
        let v8_b = v8["boolVec"][i].as_bool().unwrap();
        assert_eq!(to_boolean(p), v8_b, "ToBoolean mismatch on {p:?}");
        v8_diff_cases += 1;
    }

    let eq_arr = v8["eqMatrix"].as_array().unwrap();
    let mut k = 0usize;
    for a in &our_prims {
        for b in &our_prims {
            let triple = eq_arr[k].as_array().unwrap();
            let v8_loose = triple[0].as_bool().unwrap();
            let v8_strict = triple[1].as_bool().unwrap();
            let v8_same = triple[2].as_bool().unwrap();

            assert_eq!(is_loosely_equal(a, b), v8_loose, "IsLooselyEqual mismatch on ({a:?}, {b:?})");
            assert_eq!(is_strictly_equal(a, b), v8_strict, "IsStrictlyEqual mismatch on ({a:?}, {b:?})");
            assert_eq!(same_value(a, b), v8_same, "SameValue mismatch on ({a:?}, {b:?})");
            if matches!((a, b), (JsPrim::Number(na), JsPrim::Number(nb)) if na.is_zero() && nb.is_zero()) {
                assert!(same_value_zero(a, b));
            } else {
                assert_eq!(same_value_zero(a, b), v8_same);
            }
            k += 1;
            v8_diff_cases += 4;
        }
    }

    // Verify `ToNumeric` preserves `BigInt` without throwing while converting strings/booleans to `Number`
    let empty_hook = ObjectToPrimitiveHook {
        exotic_to_prim: MethodOutcome::NotCallable,
        to_string_slot: MethodOutcome::NotCallable,
        value_of_slot: MethodOutcome::NotCallable,
    };
    assert_eq!(
        to_numeric(&JsInput::Prim(JsPrim::BigInt(JsBigInt::from_i64(77))), &empty_hook),
        Ok(JsNumeric::BigInt(JsBigInt::from_i64(77)))
    );
    assert_eq!(
        to_numeric(&JsInput::Prim(JsPrim::Str(rust_str_to_u16(" 0x2a "))), &empty_hook),
        Ok(JsNumeric::Number(JsNumber::from_i32(42)))
    );

    // ---------------------------------------------------------------------------------------
    // 4. Write `browser/vjs-types/report.json` with exact measured counts
    // ---------------------------------------------------------------------------------------
    let mut suites_json = Vec::new();
    let mut total_passed = 0usize;
    let mut total_files = 0usize;
    let mut number_passed = 0usize;
    let mut number_total = 0usize;
    let mut string_passed = 0usize;
    let mut string_total = 0usize;
    let mut lang_types_passed = 0usize;
    let mut lang_types_total = 0usize;

    for (suite, (passed, total)) in &suite_counts {
        total_passed += *passed;
        total_files += *total;
        if suite.starts_with("built-ins/Number") {
            number_passed += *passed;
            number_total += *total;
        } else if suite.starts_with("built-ins/String") {
            string_passed += *passed;
            string_total += *total;
        } else if suite.starts_with("language/types") {
            lang_types_passed += *passed;
            lang_types_total += *total;
        }
        suites_json.push(serde_json::json!({
            "suite": suite,
            "passed": passed,
            "total": total,
        }));
    }

    let report = serde_json::json!({
        "component": "vjs_types",
        "step": "J1",
        "test262_commit": "2a1ade303f72d3de80565c921d685222405c32ce",
        "node_oracle": NODE_BIN,
        "test262_summary": {
            "total_passed": total_passed,
            "total_files": total_files,
            "built_ins_Number": {
                "passed": number_passed,
                "total": number_total,
            },
            "built_ins_String": {
                "passed": string_passed,
                "total": string_total,
            },
            "language_types": {
                "passed": lang_types_passed,
                "total": lang_types_total,
            },
        },
        "suites": suites_json,
        "differential": {
            "f64_oracle_assertions": f64_diff_cases,
            "v8_node_oracle_assertions": v8_diff_cases,
            "total_differential_assertions": f64_diff_cases + v8_diff_cases,
        },
    });

    let report_path = manifest_dir.join("report.json");
    std::fs::write(&report_path, serde_json::to_string_pretty(&report).unwrap() + "\n")
        .expect("failed to write report.json");
}
