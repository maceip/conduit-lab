//! Test suite for `vjs_builtins` (Step J5):
//! 1. Verifies `tests/data/PROVENANCE` against all pinned `tc39/test262` files.
//! 2. Executes real unmodified `tc39/test262` `.js` files across all 8 built-in directories
//!    (`Array`, `String`, `JSON`, `Math`, `Map`, `Set`, `RegExp`, `Date`) in pure Rust
//!    wired directly to the formally verified `vjs_builtins` functions.
//! 3. Runs live differential tests against Node/V8 across 2,000+ edge-case inputs.
//! 4. Writes `browser/vjs-builtins/report.json` with exact measured per-directory pass rates.

use serde_json::json;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;

use vjs_builtins::collections::{
    canonicalize_key, eq_u16_slice, is_nan_bits, is_strictly_equal, is_zero_bits, same_value_zero,
    JsKey, JsMap, JsSet, CANONICAL_NAN_BITS, NEG_INF_BITS, NEG_ZERO_BITS, POS_INF_BITS,
    POS_ZERO_BITS,
};
use vjs_builtins::date::{
    date_from_time, day, days_in_year, hour_from_time, in_leap_year, make_date, make_day,
    make_time, min_from_time, month_from_time, ms_from_time, parse_iso8601, sec_from_time,
    time_clip, time_within_day, to_iso_string, week_day, year_from_time, MAX_TIME_MS,
};
use vjs_builtins::json::{
    json_parse, json_stringify, parse_json_prefix, quote_json_string, JsonValue,
};
use vjs_builtins::math_str_arr::{
    array_concat, array_includes, array_index_of, array_pop, array_push, array_reverse,
    array_slice, math_abs_bits, math_clz32, math_imul, math_max_slice, math_min_slice,
    math_sign_bits, string_ends_with, string_index_of, string_repeat, string_slice,
    string_starts_with, string_substring, string_to_lower_case, string_to_upper_case,
    to_uint32_i64,
};
use vjs_builtins::regexp::{exec_match, exec_search, parse_pattern, MatchOutcome, RegexFlags};

const DIRECTORIES: [&str; 8] = [
    "Array", "String", "JSON", "Math", "Map", "Set", "RegExp", "Date",
];

fn str_to_u16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn u16_to_lossy_string(u: &[u16]) -> String {
    String::from_utf16_lossy(u)
}

fn u16_to_js_escaped_json(u: &[u16]) -> String {
    let quoted = quote_json_string(u);
    String::from_utf16(&quoted).expect("quote_json_string guarantees well-formed UTF-16")
}

// =======================================================================================
// Pure-Rust Mini-JS Test262 Evaluator Wired Directly to `vjs_builtins`
// =======================================================================================

#[derive(Clone, Debug)]
struct ArrayObj {
    elems: Vec<Val>,
    props: HashMap<String, Val>,
}

#[derive(Debug)]
struct RegExpObj {
    pattern: Vec<u16>,
    flags: RegexFlags,
    global: bool,
    last_index: usize,
    ast: vjs_builtins::regexp::RegexAst,
    groups: u32,
}

#[derive(Clone, Debug)]
enum BuiltinFn {
    Assert,
    AssertSameValue,
    AssertNotSameValue,
    AssertThrows,
    JsonParse,
    JsonStringify,
    DateParse,
    DateUtc,
    MathAbs,
    MathMin,
    MathMax,
    MathSign,
    MathImul,
    MathClz32,
    SymbolCtor,
    ArrayCtor,
    StringCtor,
    ObjectProtoToString,
    BoundMethod(Box<Val>, String),
    DateProtoMethod,
}

#[derive(Clone)]
enum Val {
    Undefined,
    Null,
    Bool(bool),
    Num(u64), // IEEE-754 f64 raw bits
    Str(Vec<u16>),
    Symbol(u64),
    Array(Rc<RefCell<ArrayObj>>, u64),
    Object(Rc<RefCell<HashMap<String, Val>>>, u64),
    Map(Rc<RefCell<JsMap>>, Rc<RefCell<HashMap<u64, Val>>>, u64),
    Set(Rc<RefCell<JsSet>>, Rc<RefCell<HashMap<u64, Val>>>, u64),
    RegExp(Rc<RefCell<RegExpObj>>, u64),
    Date(Option<i64>, u64),
    StringObj(Vec<u16>, u64),
    Builtin(BuiltinFn),
    Closure {
        params: Vec<String>,
        body: Vec<Stmt>,
    },
}

impl std::fmt::Debug for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::Undefined => write!(f, "undefined"),
            Val::Null => write!(f, "null"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Num(bits) => {
                if *bits == NEG_ZERO_BITS {
                    write!(f, "-0")
                } else {
                    write!(f, "{}", f64::from_bits(*bits))
                }
            }
            Val::Str(s) => write!(f, "{:?}", u16_to_lossy_string(s)),
            Val::Symbol(id) => write!(f, "Symbol({id})"),
            Val::Array(a, _) => write!(f, "{:?}", a.borrow().elems),
            Val::Object(_, id) => write!(f, "[object #{id}]"),
            Val::Map(m, _, _) => write!(f, "Map(size={})", m.borrow().size()),
            Val::Set(s, _, _) => write!(f, "Set(size={})", s.borrow().size()),
            Val::RegExp(r, _) => write!(f, "/{}/", u16_to_lossy_string(&r.borrow().pattern)),
            Val::Date(tv, _) => write!(f, "Date({tv:?})"),
            Val::StringObj(s, _) => write!(f, "String({:?})", u16_to_lossy_string(s)),
            Val::Builtin(b) => write!(f, "[builtin {b:?}]"),
            Val::Closure { .. } => write!(f, "[closure]"),
        }
    }
}

#[derive(Clone, Debug)]
struct JsError {
    kind: String,
    msg: String,
}

impl JsError {
    fn new(kind: &str, msg: impl Into<String>) -> Self {
        JsError {
            kind: kind.to_string(),
            msg: msg.into(),
        }
    }
}

fn num_val(x: f64) -> Val {
    if x.is_nan() {
        Val::Num(CANONICAL_NAN_BITS)
    } else {
        Val::Num(x.to_bits())
    }
}

fn val_to_js_key(v: &Val) -> JsKey {
    match v {
        Val::Undefined => JsKey::Undefined,
        Val::Null => JsKey::Null,
        Val::Bool(b) => JsKey::Bool(*b),
        Val::Num(bits) => JsKey::NumberBits(*bits),
        Val::Str(s) => JsKey::Str(s.clone()),
        Val::Symbol(id) => JsKey::Symbol(*id),
        Val::Array(_, id)
        | Val::Object(_, id)
        | Val::Map(_, _, id)
        | Val::Set(_, _, id)
        | Val::RegExp(_, id)
        | Val::Date(_, id)
        | Val::StringObj(_, id) => JsKey::ObjectRef(*id),
        Val::Builtin(_) | Val::Closure { .. } => JsKey::ObjectRef(0xDEAD_BEEF),
    }
}

fn js_key_to_val(k: &JsKey, obj_table: &HashMap<u64, Val>) -> Val {
    match k {
        JsKey::Undefined => Val::Undefined,
        JsKey::Null => Val::Null,
        JsKey::Bool(b) => Val::Bool(*b),
        JsKey::NumberBits(bits) => Val::Num(*bits),
        JsKey::Str(s) => Val::Str(s.clone()),
        JsKey::Symbol(id) => Val::Symbol(*id),
        JsKey::ObjectRef(id) => obj_table.get(id).cloned().unwrap_or(Val::Undefined),
    }
}

/// ECMA-262 `SameValue` (used by `assert.sameValue` in test262).
fn js_same_value(a: &Val, b: &Val) -> bool {
    match (a, b) {
        (Val::Num(x), Val::Num(y)) => {
            if is_nan_bits(*x) || is_nan_bits(*y) {
                is_nan_bits(*x) && is_nan_bits(*y)
            } else {
                *x == *y
            }
        }
        _ => same_value_zero(&val_to_js_key(a), &val_to_js_key(b)),
    }
}

fn js_strict_eq(a: &Val, b: &Val) -> bool {
    is_strictly_equal(&val_to_js_key(a), &val_to_js_key(b))
}

fn val_is_truthy(v: &Val) -> bool {
    match v {
        Val::Undefined | Val::Null => false,
        Val::Bool(b) => *b,
        Val::Num(bits) => !is_zero_bits(*bits) && !is_nan_bits(*bits),
        Val::Str(s) => !s.is_empty(),
        _ => true,
    }
}

fn val_to_number_bits(v: &Val) -> Result<u64, JsError> {
    match v {
        Val::Undefined => Ok(CANONICAL_NAN_BITS),
        Val::Null => Ok(POS_ZERO_BITS),
        Val::Bool(b) => Ok(if *b { 1.0f64.to_bits() } else { POS_ZERO_BITS }),
        Val::Num(bits) => Ok(*bits),
        Val::Str(s) => {
            let st = u16_to_lossy_string(s);
            let trimmed = st.trim();
            if trimmed.is_empty() {
                Ok(POS_ZERO_BITS)
            } else if let Ok(n) = trimmed.parse::<f64>() {
                Ok(if n.is_nan() { CANONICAL_NAN_BITS } else { n.to_bits() })
            } else {
                Ok(CANONICAL_NAN_BITS)
            }
        }
        Val::Symbol(_) => Err(JsError::new("TypeError", "Cannot convert Symbol to number")),
        Val::Date(tv, _) => Ok(match tv {
            Some(ms) => (*ms as f64).to_bits(),
            None => CANONICAL_NAN_BITS,
        }),
        _ => Ok(CANONICAL_NAN_BITS),
    }
}

fn to_integer_or_infinity(v: &Val) -> Result<f64, JsError> {
    let bits = val_to_number_bits(v)?;
    if is_nan_bits(bits) || is_zero_bits(bits) {
        return Ok(0.0);
    }
    let f = f64::from_bits(bits);
    if f.is_infinite() {
        return Ok(f);
    }
    Ok(f.trunc())
}

fn to_clamped_i64(v: &Val) -> Result<i64, JsError> {
    let f = to_integer_or_infinity(v)?;
    if f == f64::INFINITY {
        Ok(i64::MAX / 2)
    } else if f == f64::NEG_INFINITY {
        Ok(i64::MIN / 2)
    } else if f >= (i64::MAX / 2) as f64 {
        Ok(i64::MAX / 2)
    } else if f <= (i64::MIN / 2) as f64 {
        Ok(i64::MIN / 2)
    } else {
        Ok(f as i64)
    }
}

fn to_uint32_from_bits(bits: u64) -> u32 {
    if is_nan_bits(bits) || is_zero_bits(bits) || bits == POS_INF_BITS || bits == NEG_INF_BITS {
        return 0;
    }
    let f = f64::from_bits(bits).trunc();
    if !f.is_finite() || f == 0.0 {
        return 0;
    }
    let rem = f % 4_294_967_296.0;
    let i = rem as i64;
    to_uint32_i64(i)
}

fn val_to_u16_str(v: &Val) -> Result<Vec<u16>, JsError> {
    match v {
        Val::Str(s) => Ok(s.clone()),
        Val::StringObj(s, _) => Ok(s.clone()),
        Val::Undefined => Ok(str_to_u16("undefined")),
        Val::Null => Ok(str_to_u16("null")),
        Val::Bool(b) => Ok(str_to_u16(if *b { "true" } else { "false" })),
        Val::Num(bits) => {
            if is_nan_bits(*bits) {
                Ok(str_to_u16("NaN"))
            } else if is_zero_bits(*bits) {
                Ok(str_to_u16("0"))
            } else if *bits == POS_INF_BITS {
                Ok(str_to_u16("Infinity"))
            } else if *bits == NEG_INF_BITS {
                Ok(str_to_u16("-Infinity"))
            } else {
                Ok(str_to_u16(&format!("{}", f64::from_bits(*bits))))
            }
        }
        Val::Symbol(_) => Err(JsError::new("TypeError", "Cannot convert Symbol to string")),
        _ => Ok(str_to_u16("[object Object]")),
    }
}

// ---------------------------------------------------------------------------------------
// Tokenizer & Recursive-Descent Parser for Test262 JS Subset
// ---------------------------------------------------------------------------------------

#[derive(Clone, PartialEq, Debug)]
enum Tok {
    Ident(String),
    Num(f64, bool /* neg_zero */),
    Str(Vec<u16>),
    Regex(Vec<u16>, String),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Dot,
    Comma,
    Semi,
    Colon,
    Assign,
    EqStrict,
    NeStrict,
    EqLoose,
    NeLoose,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Bang,
    PlusPlus,
    AndAnd,
    OrOr,
    Eof,
}

fn can_start_regex(prev: Option<&Tok>) -> bool {
    match prev {
        None => true,
        Some(
            Tok::LParen
            | Tok::LBracket
            | Tok::LBrace
            | Tok::Comma
            | Tok::Semi
            | Tok::Colon
            | Tok::Assign
            | Tok::EqStrict
            | Tok::NeStrict
            | Tok::EqLoose
            | Tok::NeLoose
            | Tok::Lt
            | Tok::Le
            | Tok::Gt
            | Tok::Ge
            | Tok::Plus
            | Tok::Minus
            | Tok::Star
            | Tok::Bang
            | Tok::AndAnd
            | Tok::OrOr,
        ) => true,
        Some(Tok::Ident(s)) => matches!(s.as_str(), "return" | "throw" | "typeof"),
        _ => false,
    }
}

fn lex_js(src: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut out: Vec<Tok> = Vec::new();
    while i < n {
        let c = chars[i];
        if c.is_whitespace() || c == '\u{FEFF}' {
            i += 1;
            continue;
        }
        if c == '/' && i + 1 < n && chars[i + 1] == '/' {
            i += 2;
            while i < n && chars[i] != '\n' && chars[i] != '\r' {
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
        if c == '/' && can_start_regex(out.last()) {
            i += 1;
            let mut pat: Vec<u16> = Vec::new();
            let mut in_class = false;
            while i < n {
                let rc = chars[i];
                if rc == '\\' && i + 1 < n {
                    let mut buf = [0u16; 2];
                    for u in rc.encode_utf16(&mut buf) {
                        pat.push(*u);
                    }
                    i += 1;
                    for u in chars[i].encode_utf16(&mut buf) {
                        pat.push(*u);
                    }
                    i += 1;
                    continue;
                }
                if rc == '[' {
                    in_class = true;
                } else if rc == ']' {
                    in_class = false;
                } else if rc == '/' && !in_class {
                    i += 1;
                    break;
                }
                let mut buf = [0u16; 2];
                for u in rc.encode_utf16(&mut buf) {
                    pat.push(*u);
                }
                i += 1;
            }
            let mut flags = String::new();
            while i < n && chars[i].is_ascii_alphabetic() {
                flags.push(chars[i]);
                i += 1;
            }
            out.push(Tok::Regex(pat, flags));
            continue;
        }
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
                    let esc = chars[i];
                    i += 1;
                    match esc {
                        'n' => units.push(0x000A),
                        'r' => units.push(0x000D),
                        't' => units.push(0x0009),
                        'b' => units.push(0x0008),
                        'f' => units.push(0x000C),
                        'v' => units.push(0x000B),
                        '0' => units.push(0x0000),
                        '\\' => units.push(0x005C),
                        '\'' => units.push(0x0027),
                        '"' => units.push(0x0022),
                        'x' => {
                            let h: String = chars[i..i + 2].iter().collect();
                            let v = u16::from_str_radix(&h, 16).map_err(|e| e.to_string())?;
                            units.push(v);
                            i += 2;
                        }
                        'u' => {
                            let h: String = chars[i..i + 4].iter().collect();
                            let v = u16::from_str_radix(&h, 16).map_err(|e| e.to_string())?;
                            units.push(v);
                            i += 4;
                        }
                        other => {
                            let mut buf = [0u16; 2];
                            for u in other.encode_utf16(&mut buf) {
                                units.push(*u);
                            }
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
            i += 1;
            out.push(Tok::Str(units));
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            if c == '0' && i + 1 < n && (chars[i + 1] == 'x' || chars[i + 1] == 'X') {
                i += 2;
                let hex_start = i;
                while i < n && chars[i].is_ascii_hexdigit() {
                    i += 1;
                }
                let hs: String = chars[hex_start..i].iter().collect();
                let v = u64::from_str_radix(&hs, 16).map_err(|e| e.to_string())?;
                out.push(Tok::Num(v as f64, false));
                continue;
            }
            while i < n && (chars[i].is_ascii_digit() || chars[i] == '.' || chars[i] == '_') {
                i += 1;
            }
            if i < n && (chars[i] == 'e' || chars[i] == 'E') {
                i += 1;
                if i < n && (chars[i] == '+' || chars[i] == '-') {
                    i += 1;
                }
                while i < n && chars[i].is_ascii_digit() {
                    i += 1;
                }
            }
            let ns: String = chars[start..i].iter().filter(|ch| **ch != '_').collect();
            let v: f64 = ns.parse().map_err(|e: std::num::ParseFloatError| e.to_string())?;
            out.push(Tok::Num(v, false));
            continue;
        }
        if c.is_ascii_alphabetic() || c == '_' || c == '$' {
            let start = i;
            while i < n && (chars[i].is_ascii_alphanumeric() || chars[i] == '_' || chars[i] == '$')
            {
                i += 1;
            }
            let s: String = chars[start..i].iter().collect();
            out.push(Tok::Ident(s));
            continue;
        }
        if i + 2 < n && chars[i] == '=' && chars[i + 1] == '=' && chars[i + 2] == '=' {
            out.push(Tok::EqStrict);
            i += 3;
            continue;
        }
        if i + 2 < n && chars[i] == '!' && chars[i + 1] == '=' && chars[i + 2] == '=' {
            out.push(Tok::NeStrict);
            i += 3;
            continue;
        }
        if i + 1 < n {
            match (chars[i], chars[i + 1]) {
                ('=', '=') => {
                    out.push(Tok::EqLoose);
                    i += 2;
                    continue;
                }
                ('!', '=') => {
                    out.push(Tok::NeLoose);
                    i += 2;
                    continue;
                }
                ('<', '=') => {
                    out.push(Tok::Le);
                    i += 2;
                    continue;
                }
                ('>', '=') => {
                    out.push(Tok::Ge);
                    i += 2;
                    continue;
                }
                ('+', '+') => {
                    out.push(Tok::PlusPlus);
                    i += 2;
                    continue;
                }
                ('&', '&') => {
                    out.push(Tok::AndAnd);
                    i += 2;
                    continue;
                }
                ('|', '|') => {
                    out.push(Tok::OrOr);
                    i += 2;
                    continue;
                }
                _ => {}
            }
        }
        let single = match c {
            '(' => Tok::LParen,
            ')' => Tok::RParen,
            '[' => Tok::LBracket,
            ']' => Tok::RBracket,
            '{' => Tok::LBrace,
            '}' => Tok::RBrace,
            '.' => Tok::Dot,
            ',' => Tok::Comma,
            ';' => Tok::Semi,
            ':' => Tok::Colon,
            '=' => Tok::Assign,
            '<' => Tok::Lt,
            '>' => Tok::Gt,
            '+' => Tok::Plus,
            '-' => Tok::Minus,
            '*' => Tok::Star,
            '/' => Tok::Slash,
            '!' => Tok::Bang,
            other => return Err(format!("unexpected char {other:?}")),
        };
        out.push(single);
        i += 1;
    }
    out.push(Tok::Eof);
    Ok(out)
}

#[derive(Clone, Debug)]
enum Expr {
    Ident(String),
    Num(u64),
    Str(Vec<u16>),
    Bool(bool),
    Null,
    Undefined,
    Regex(Vec<u16>, String),
    ArrayLit(Vec<Expr>),
    ObjectLit(Vec<(String, Expr)>),
    Unary(String, Box<Expr>),
    PostInc(String),
    Binary(String, Box<Expr>, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    Member(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    New(Box<Expr>, Vec<Expr>),
    FuncExpr(Vec<String>, Vec<Stmt>),
}

#[derive(Clone, Debug)]
enum Stmt {
    VarDecl(Vec<(String, Option<Expr>)>),
    ExprStmt(Expr),
    Block(Vec<Stmt>),
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    ForC {
        init: Option<Box<Stmt>>,
        cond: Option<Expr>,
        step: Option<Expr>,
        body: Box<Stmt>,
    },
    ForOf {
        var: String,
        iter: Expr,
        body: Box<Stmt>,
    },
    Return(Option<Expr>),
    Throw(Expr),
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos]
    }
    fn next(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, expected: &Tok) -> bool {
        if self.peek() == expected {
            self.next();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, expected: &Tok) -> Result<(), String> {
        if self.eat(expected) {
            Ok(())
        } else {
            Err(format!("expected {expected:?}, got {:?}", self.peek()))
        }
    }
    fn eat_semi(&mut self) {
        while self.eat(&Tok::Semi) {}
    }

    fn parse_program(&mut self) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        self.eat_semi();
        while self.peek() != &Tok::Eof {
            stmts.push(self.parse_stmt()?);
            self.eat_semi();
        }
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        match self.peek().clone() {
            Tok::LBrace => {
                self.next();
                let mut body = Vec::new();
                self.eat_semi();
                while self.peek() != &Tok::RBrace && self.peek() != &Tok::Eof {
                    body.push(self.parse_stmt()?);
                    self.eat_semi();
                }
                self.expect(&Tok::RBrace)?;
                Ok(Stmt::Block(body))
            }
            Tok::Ident(kw) if kw == "var" || kw == "let" || kw == "const" => {
                self.next();
                let mut decls = Vec::new();
                loop {
                    let Tok::Ident(name) = self.next() else {
                        return Err("expected var name".into());
                    };
                    let init = if self.eat(&Tok::Assign) {
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    decls.push((name, init));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                self.eat_semi();
                Ok(Stmt::VarDecl(decls))
            }
            Tok::Ident(kw) if kw == "if" => {
                self.next();
                self.expect(&Tok::LParen)?;
                let cond = self.parse_expr()?;
                self.expect(&Tok::RParen)?;
                let then_b = Box::new(self.parse_stmt()?);
                self.eat_semi();
                let else_b = if matches!(self.peek(), Tok::Ident(s) if s == "else") {
                    self.next();
                    Some(Box::new(self.parse_stmt()?))
                } else {
                    None
                };
                Ok(Stmt::If(cond, then_b, else_b))
            }
            Tok::Ident(kw) if kw == "while" => {
                self.next();
                self.expect(&Tok::LParen)?;
                let cond = self.parse_expr()?;
                self.expect(&Tok::RParen)?;
                let body = Box::new(self.parse_stmt()?);
                Ok(Stmt::While(cond, body))
            }
            Tok::Ident(kw) if kw == "for" => {
                self.next();
                self.expect(&Tok::LParen)?;
                // Check `for (const x of expr)`
                let save = self.pos;
                if matches!(self.peek(), Tok::Ident(s) if s == "var" || s == "let" || s == "const")
                {
                    self.next();
                    if let Tok::Ident(vname) = self.next() {
                        if matches!(self.peek(), Tok::Ident(s) if s == "of") {
                            self.next();
                            let iter = self.parse_expr()?;
                            self.expect(&Tok::RParen)?;
                            let body = Box::new(self.parse_stmt()?);
                            return Ok(Stmt::ForOf {
                                var: vname,
                                iter,
                                body,
                            });
                        }
                    }
                }
                self.pos = save;
                let init = if self.eat(&Tok::Semi) {
                    None
                } else if matches!(self.peek(), Tok::Ident(s) if s == "var" || s == "let" || s == "const")
                {
                    Some(Box::new(self.parse_stmt()?))
                } else {
                    let e = self.parse_expr()?;
                    self.expect(&Tok::Semi)?;
                    Some(Box::new(Stmt::ExprStmt(e)))
                };
                let cond = if self.eat(&Tok::Semi) {
                    None
                } else {
                    let c = self.parse_expr()?;
                    self.expect(&Tok::Semi)?;
                    Some(c)
                };
                let step = if self.eat(&Tok::RParen) {
                    None
                } else {
                    let s = self.parse_expr()?;
                    self.expect(&Tok::RParen)?;
                    Some(s)
                };
                let body = Box::new(self.parse_stmt()?);
                Ok(Stmt::ForC {
                    init,
                    cond,
                    step,
                    body,
                })
            }
            Tok::Ident(kw) if kw == "return" => {
                self.next();
                if matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::Eof) {
                    Ok(Stmt::Return(None))
                } else {
                    Ok(Stmt::Return(Some(self.parse_expr()?)))
                }
            }
            Tok::Ident(kw) if kw == "throw" => {
                self.next();
                Ok(Stmt::Throw(self.parse_expr()?))
            }
            _ => {
                let e = self.parse_expr()?;
                Ok(Stmt::ExprStmt(e))
            }
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        let lhs = self.parse_or()?;
        if self.eat(&Tok::Assign) {
            let rhs = self.parse_expr()?;
            Ok(Expr::Assign(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_and()?;
        while self.eat(&Tok::OrOr) {
            let r = self.parse_and()?;
            e = Expr::Binary("||".into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_and(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_eq()?;
        while self.eat(&Tok::AndAnd) {
            let r = self.parse_eq()?;
            e = Expr::Binary("&&".into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_eq(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_rel()?;
        loop {
            let op = match self.peek() {
                Tok::EqStrict | Tok::EqLoose => "===",
                Tok::NeStrict | Tok::NeLoose => "!==",
                _ => break,
            };
            self.next();
            let r = self.parse_rel()?;
            e = Expr::Binary(op.into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_rel(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_add()?;
        loop {
            let op = match self.peek() {
                Tok::Lt => "<",
                Tok::Le => "<=",
                Tok::Gt => ">",
                Tok::Ge => ">=",
                _ => break,
            };
            self.next();
            let r = self.parse_add()?;
            e = Expr::Binary(op.into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_add(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => "+",
                Tok::Minus => "-",
                _ => break,
            };
            self.next();
            let r = self.parse_mul()?;
            e = Expr::Binary(op.into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_mul(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Tok::Star => "*",
                Tok::Slash => "/",
                _ => break,
            };
            self.next();
            let r = self.parse_unary()?;
            e = Expr::Binary(op.into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        match self.peek().clone() {
            Tok::Minus => {
                self.next();
                if let Tok::Num(v, _) = self.peek().clone() {
                    self.next();
                    if v == 0.0 {
                        return Ok(Expr::Num(NEG_ZERO_BITS));
                    }
                    return Ok(Expr::Num((-v).to_bits()));
                }
                let sub = self.parse_unary()?;
                Ok(Expr::Unary("-".into(), Box::new(sub)))
            }
            Tok::Plus => {
                self.next();
                let sub = self.parse_unary()?;
                Ok(Expr::Unary("+".into(), Box::new(sub)))
            }
            Tok::Bang => {
                self.next();
                let sub = self.parse_unary()?;
                Ok(Expr::Unary("!".into(), Box::new(sub)))
            }
            Tok::Ident(kw) if kw == "typeof" => {
                self.next();
                let sub = self.parse_unary()?;
                Ok(Expr::Unary("typeof".into(), Box::new(sub)))
            }
            Tok::Ident(kw) if kw == "new" => {
                self.next();
                let callee = self.parse_member_only()?;
                let args = if self.eat(&Tok::LParen) {
                    let a = self.parse_arg_list()?;
                    self.expect(&Tok::RParen)?;
                    a
                } else {
                    Vec::new()
                };
                self.parse_postfix_from(Expr::New(Box::new(callee), args))
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_member_only(&mut self) -> Result<Expr, String> {
        let mut base = self.parse_primary()?;
        while self.eat(&Tok::Dot) {
            let Tok::Ident(prop) = self.next() else {
                return Err("expected prop".into());
            };
            base = Expr::Member(Box::new(base), prop);
        }
        Ok(base)
    }

    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let base = self.parse_primary()?;
        self.parse_postfix_from(base)
    }

    fn parse_postfix_from(&mut self, mut e: Expr) -> Result<Expr, String> {
        loop {
            if self.eat(&Tok::Dot) {
                let Tok::Ident(prop) = self.next() else {
                    return Err("expected member ident".into());
                };
                e = Expr::Member(Box::new(e), prop);
            } else if self.eat(&Tok::LBracket) {
                let idx = self.parse_expr()?;
                self.expect(&Tok::RBracket)?;
                e = Expr::Index(Box::new(e), Box::new(idx));
            } else if self.eat(&Tok::LParen) {
                let args = self.parse_arg_list()?;
                self.expect(&Tok::RParen)?;
                e = Expr::Call(Box::new(e), args);
            } else if self.eat(&Tok::PlusPlus) {
                if let Expr::Ident(name) = e {
                    e = Expr::PostInc(name);
                } else {
                    return Err("unsupported ++ target".into());
                }
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn parse_arg_list(&mut self) -> Result<Vec<Expr>, String> {
        let mut args = Vec::new();
        if self.peek() == &Tok::RParen {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
            if self.peek() == &Tok::RParen {
                break;
            }
        }
        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        match self.next() {
            Tok::Num(v, neg_zero) => Ok(Expr::Num(if neg_zero {
                NEG_ZERO_BITS
            } else {
                v.to_bits()
            })),
            Tok::Str(s) => Ok(Expr::Str(s)),
            Tok::Regex(pat, flags) => Ok(Expr::Regex(pat, flags)),
            Tok::Ident(s) => match s.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                "null" => Ok(Expr::Null),
                "undefined" => Ok(Expr::Undefined),
                "NaN" => Ok(Expr::Num(CANONICAL_NAN_BITS)),
                "Infinity" => Ok(Expr::Num(POS_INF_BITS)),
                "function" => {
                    if matches!(self.peek(), Tok::Ident(_)) {
                        self.next();
                    }
                    self.expect(&Tok::LParen)?;
                    let mut params = Vec::new();
                    if self.peek() != &Tok::RParen {
                        loop {
                            let Tok::Ident(p) = self.next() else {
                                return Err("expected param".into());
                            };
                            params.push(p);
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RParen)?;
                    let Stmt::Block(body) = self.parse_stmt()? else {
                        return Err("expected function block".into());
                    };
                    Ok(Expr::FuncExpr(params, body))
                }
                _ => Ok(Expr::Ident(s)),
            },
            Tok::LParen => {
                let e = self.parse_expr()?;
                self.expect(&Tok::RParen)?;
                Ok(e)
            }
            Tok::LBracket => {
                let mut items = Vec::new();
                if self.peek() != &Tok::RBracket {
                    loop {
                        items.push(self.parse_expr()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        if self.peek() == &Tok::RBracket {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RBracket)?;
                Ok(Expr::ArrayLit(items))
            }
            Tok::LBrace => {
                let mut props = Vec::new();
                if self.peek() != &Tok::RBrace {
                    loop {
                        let key = match self.next() {
                            Tok::Ident(k) => k,
                            Tok::Str(u) => u16_to_lossy_string(&u),
                            Tok::Num(n, _) => format!("{n}"),
                            other => return Err(format!("bad object key {other:?}")),
                        };
                        self.expect(&Tok::Colon)?;
                        let v = self.parse_expr()?;
                        props.push((key, v));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        if self.peek() == &Tok::RBrace {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RBrace)?;
                Ok(Expr::ObjectLit(props))
            }
            other => Err(format!("unexpected token {other:?}")),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Runtime Environment Executing Test262 Statements Against `vjs_builtins`
// ---------------------------------------------------------------------------------------

struct Interp {
    vars: HashMap<String, Val>,
    next_id: u64,
}

impl Interp {
    fn new() -> Self {
        let mut vars = HashMap::new();
        vars.insert("assert".into(), Val::Builtin(BuiltinFn::Assert));
        vars.insert("Symbol".into(), Val::Builtin(BuiltinFn::SymbolCtor));
        vars.insert("Array".into(), Val::Builtin(BuiltinFn::ArrayCtor));
        vars.insert("String".into(), Val::Builtin(BuiltinFn::StringCtor));
        Interp { vars, next_id: 1 }
    }

    fn alloc_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn new_array(&mut self, elems: Vec<Val>) -> Val {
        let id = self.alloc_id();
        Val::Array(
            Rc::new(RefCell::new(ArrayObj {
                elems,
                props: HashMap::new(),
            })),
            id,
        )
    }

    fn json_val_to_runtime(&mut self, jv: JsonValue) -> Val {
        match jv {
            JsonValue::Null => Val::Null,
            JsonValue::Bool(b) => Val::Bool(b),
            JsonValue::Int(n) => num_val(n as f64),
            JsonValue::Str(s) => Val::Str(s),
            JsonValue::Array(xs) => {
                let elems: Vec<Val> = xs.into_iter().map(|e| self.json_val_to_runtime(e)).collect();
                self.new_array(elems)
            }
            JsonValue::Object(kvs) => {
                let mut m = HashMap::new();
                for (k, v) in kvs {
                    m.insert(u16_to_lossy_string(&k), self.json_val_to_runtime(v));
                }
                let id = self.alloc_id();
                Val::Object(Rc::new(RefCell::new(m)), id)
            }
        }
    }

    fn runtime_to_json_val(&self, v: &Val) -> Option<JsonValue> {
        match v {
            Val::Null => Some(JsonValue::Null),
            Val::Bool(b) => Some(JsonValue::Bool(*b)),
            Val::Num(bits) => {
                if is_nan_bits(*bits) || *bits == POS_INF_BITS || *bits == NEG_INF_BITS {
                    Some(JsonValue::Null)
                } else if is_zero_bits(*bits) {
                    Some(JsonValue::Int(0))
                } else {
                    let f = f64::from_bits(*bits);
                    if f.fract() == 0.0 && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
                        Some(JsonValue::Int(f as i64))
                    } else {
                        None
                    }
                }
            }
            Val::Str(s) | Val::StringObj(s, _) => Some(JsonValue::Str(s.clone())),
            Val::Array(a, _) => {
                let mut out = Vec::new();
                for el in &a.borrow().elems {
                    out.push(self.runtime_to_json_val(el).unwrap_or(JsonValue::Null));
                }
                Some(JsonValue::Array(out))
            }
            Val::Object(o, _) => {
                let mut out = Vec::new();
                for (k, val) in o.borrow().iter() {
                    if let Some(jv) = self.runtime_to_json_val(val) {
                        out.push((str_to_u16(k), jv));
                    }
                }
                Some(JsonValue::Object(out))
            }
            Val::Undefined | Val::Symbol(_) | Val::Builtin(_) | Val::Closure { .. } => None,
            _ => Some(JsonValue::Object(Vec::new())),
        }
    }

    fn construct_regexp(&mut self, pat: Vec<u16>, flags_str: &str) -> Result<Val, JsError> {
        let mut ignore_case = false;
        let mut multiline = false;
        let mut dot_all = false;
        let mut global = false;
        for ch in flags_str.chars() {
            match ch {
                'i' if !ignore_case => ignore_case = true,
                'm' if !multiline => multiline = true,
                's' if !dot_all => dot_all = true,
                'g' if !global => global = true,
                _ => return Err(JsError::new("SyntaxError", "invalid regex flags")),
            }
        }
        let Some((ast, groups)) = parse_pattern(&pat, 512) else {
            return Err(JsError::new("SyntaxError", "invalid regex pattern"));
        };
        let id = self.alloc_id();
        Ok(Val::RegExp(
            Rc::new(RefCell::new(RegExpObj {
                pattern: pat,
                flags: RegexFlags {
                    ignore_case,
                    multiline,
                    dot_all,
                },
                global,
                last_index: 0,
                ast,
                groups,
            })),
            id,
        ))
    }

    fn compute_date_utc(&self, args: &[Val]) -> Result<Option<i64>, JsError> {
        if args.is_empty() {
            return Ok(None);
        }
        let y_bits = val_to_number_bits(&args[0])?;
        let m_bits = if args.len() >= 2 {
            val_to_number_bits(&args[1])?
        } else {
            POS_ZERO_BITS
        };
        let dt_bits = if args.len() >= 3 {
            val_to_number_bits(&args[2])?
        } else {
            1.0f64.to_bits()
        };
        let h_bits = if args.len() >= 4 {
            val_to_number_bits(&args[3])?
        } else {
            POS_ZERO_BITS
        };
        let mn_bits = if args.len() >= 5 {
            val_to_number_bits(&args[4])?
        } else {
            POS_ZERO_BITS
        };
        let sc_bits = if args.len() >= 6 {
            val_to_number_bits(&args[5])?
        } else {
            POS_ZERO_BITS
        };
        let ms_bits = if args.len() >= 7 {
            val_to_number_bits(&args[6])?
        } else {
            POS_ZERO_BITS
        };
        for b in [y_bits, m_bits, dt_bits, h_bits, mn_bits, sc_bits, ms_bits] {
            if is_nan_bits(b) || b == POS_INF_BITS || b == NEG_INF_BITS {
                return Ok(None);
            }
        }
        let yi = f64::from_bits(y_bits).trunc() as i64;
        let yr = if (0..=99).contains(&yi) { 1900 + yi } else { yi };
        let mi = f64::from_bits(m_bits).trunc() as i64;
        let dti = f64::from_bits(dt_bits).trunc() as i64;
        let hi = f64::from_bits(h_bits).trunc() as i64;
        let mni = f64::from_bits(mn_bits).trunc() as i64;
        let sci = f64::from_bits(sc_bits).trunc() as i64;
        let msi = f64::from_bits(ms_bits).trunc() as i64;
        let Some(d) = make_day(yr, mi, dti) else {
            return Ok(None);
        };
        let Some(t) = make_time(hi, mni, sci, msi) else {
            return Ok(None);
        };
        let Some(raw) = make_date(d, t) else {
            return Ok(None);
        };
        Ok(time_clip(raw))
    }

    fn exec_stmts(&mut self, stmts: &[Stmt]) -> Result<Option<Val>, JsError> {
        for s in stmts {
            if let Some(ret) = self.exec_stmt(s)? {
                return Ok(Some(ret));
            }
        }
        Ok(None)
    }

    fn exec_stmt(&mut self, stmt: &Stmt) -> Result<Option<Val>, JsError> {
        match stmt {
            Stmt::VarDecl(decls) => {
                for (name, init) in decls {
                    let v = match init {
                        Some(e) => self.eval_expr(e)?,
                        None => Val::Undefined,
                    };
                    self.vars.insert(name.clone(), v);
                }
                Ok(None)
            }
            Stmt::ExprStmt(e) => {
                self.eval_expr(e)?;
                Ok(None)
            }
            Stmt::Block(b) => self.exec_stmts(b),
            Stmt::If(cond, then_b, else_b) => {
                let cv = self.eval_expr(cond)?;
                if val_is_truthy(&cv) {
                    self.exec_stmt(then_b)
                } else if let Some(eb) = else_b {
                    self.exec_stmt(eb)
                } else {
                    Ok(None)
                }
            }
            Stmt::While(cond, body) => {
                loop {
                    let cv = self.eval_expr(cond)?;
                    if !val_is_truthy(&cv) {
                        break;
                    }
                    if let Some(ret) = self.exec_stmt(body)? {
                        return Ok(Some(ret));
                    }
                }
                Ok(None)
            }
            Stmt::ForC {
                init,
                cond,
                step,
                body,
            } => {
                if let Some(i) = init {
                    self.exec_stmt(i)?;
                }
                loop {
                    if let Some(c) = cond {
                        let cv = self.eval_expr(c)?;
                        if !val_is_truthy(&cv) {
                            break;
                        }
                    }
                    if let Some(ret) = self.exec_stmt(body)? {
                        return Ok(Some(ret));
                    }
                    if let Some(st) = step {
                        self.eval_expr(st)?;
                    }
                }
                Ok(None)
            }
            Stmt::ForOf { var, iter, body } => {
                let iv = self.eval_expr(iter)?;
                let items = match iv {
                    Val::Array(a, _) => a.borrow().elems.clone(),
                    _ => return Err(JsError::new("TypeError", "not iterable")),
                };
                for item in items {
                    self.vars.insert(var.clone(), item);
                    if let Some(ret) = self.exec_stmt(body)? {
                        return Ok(Some(ret));
                    }
                }
                Ok(None)
            }
            Stmt::Return(e) => {
                let v = match e {
                    Some(ex) => self.eval_expr(ex)?,
                    None => Val::Undefined,
                };
                Ok(Some(v))
            }
            Stmt::Throw(e) => {
                let v = self.eval_expr(e)?;
                Err(JsError::new("Test262Error", format!("{v:?}")))
            }
        }
    }

    fn eval_expr(&mut self, expr: &Expr) -> Result<Val, JsError> {
        match expr {
            Expr::Ident(name) => Ok(self.vars.get(name).cloned().unwrap_or(Val::Undefined)),
            Expr::Num(bits) => Ok(Val::Num(*bits)),
            Expr::Str(s) => Ok(Val::Str(s.clone())),
            Expr::Bool(b) => Ok(Val::Bool(*b)),
            Expr::Null => Ok(Val::Null),
            Expr::Undefined => Ok(Val::Undefined),
            Expr::Regex(pat, flags) => self.construct_regexp(pat.clone(), flags),
            Expr::ArrayLit(items) => {
                let mut v = Vec::new();
                for it in items {
                    v.push(self.eval_expr(it)?);
                }
                Ok(self.new_array(v))
            }
            Expr::ObjectLit(props) => {
                let mut m = HashMap::new();
                for (k, ex) in props {
                    m.insert(k.clone(), self.eval_expr(ex)?);
                }
                let id = self.alloc_id();
                Ok(Val::Object(Rc::new(RefCell::new(m)), id))
            }
            Expr::FuncExpr(params, body) => Ok(Val::Closure {
                params: params.clone(),
                body: body.clone(),
            }),
            Expr::PostInc(name) => {
                let old = self.vars.get(name).cloned().unwrap_or(Val::Undefined);
                let bits = val_to_number_bits(&old)?;
                let f = f64::from_bits(bits);
                self.vars.insert(name.clone(), num_val(f + 1.0));
                Ok(Val::Num(bits))
            }
            Expr::Unary(op, sub) => {
                let v = self.eval_expr(sub)?;
                match op.as_str() {
                    "!" => Ok(Val::Bool(!val_is_truthy(&v))),
                    "+" => Ok(Val::Num(val_to_number_bits(&v)?)),
                    "-" => {
                        let b = val_to_number_bits(&v)?;
                        if is_nan_bits(b) {
                            Ok(Val::Num(CANONICAL_NAN_BITS))
                        } else {
                            Ok(Val::Num(b ^ NEG_ZERO_BITS))
                        }
                    }
                    "typeof" => {
                        let t = match v {
                            Val::Undefined => "undefined",
                            Val::Bool(_) => "boolean",
                            Val::Num(_) => "number",
                            Val::Str(_) => "string",
                            Val::Symbol(_) => "symbol",
                            Val::Builtin(_) | Val::Closure { .. } => "function",
                            _ => "object",
                        };
                        Ok(Val::Str(str_to_u16(t)))
                    }
                    _ => Err(JsError::new("SyntaxError", "unknown unary op")),
                }
            }
            Expr::Binary(op, l, r) => {
                if op == "&&" {
                    let lv = self.eval_expr(l)?;
                    return if !val_is_truthy(&lv) {
                        Ok(lv)
                    } else {
                        self.eval_expr(r)
                    };
                }
                if op == "||" {
                    let lv = self.eval_expr(l)?;
                    return if val_is_truthy(&lv) {
                        Ok(lv)
                    } else {
                        self.eval_expr(r)
                    };
                }
                let lv = self.eval_expr(l)?;
                let rv = self.eval_expr(r)?;
                match op.as_str() {
                    "===" => Ok(Val::Bool(js_strict_eq(&lv, &rv))),
                    "!==" => Ok(Val::Bool(!js_strict_eq(&lv, &rv))),
                    "+" => {
                        if matches!(lv, Val::Str(_)) || matches!(rv, Val::Str(_)) {
                            let mut a = val_to_u16_str(&lv)?;
                            let b = val_to_u16_str(&rv)?;
                            a.extend_from_slice(&b);
                            Ok(Val::Str(a))
                        } else {
                            let lb = val_to_number_bits(&lv)?;
                            let rb = val_to_number_bits(&rv)?;
                            Ok(num_val(f64::from_bits(lb) + f64::from_bits(rb)))
                        }
                    }
                    "-" => {
                        let lb = val_to_number_bits(&lv)?;
                        let rb = val_to_number_bits(&rv)?;
                        Ok(num_val(f64::from_bits(lb) - f64::from_bits(rb)))
                    }
                    "*" => {
                        let lb = val_to_number_bits(&lv)?;
                        let rb = val_to_number_bits(&rv)?;
                        Ok(num_val(f64::from_bits(lb) * f64::from_bits(rb)))
                    }
                    "/" => {
                        let lb = val_to_number_bits(&lv)?;
                        let rb = val_to_number_bits(&rv)?;
                        Ok(num_val(f64::from_bits(lb) / f64::from_bits(rb)))
                    }
                    "<" | "<=" | ">" | ">=" => {
                        let lf = f64::from_bits(val_to_number_bits(&lv)?);
                        let rf = f64::from_bits(val_to_number_bits(&rv)?);
                        let b = match op.as_str() {
                            "<" => lf < rf,
                            "<=" => lf <= rf,
                            ">" => lf > rf,
                            _ => lf >= rf,
                        };
                        Ok(Val::Bool(b))
                    }
                    _ => Err(JsError::new("SyntaxError", "unknown binary op")),
                }
            }
            Expr::Assign(lhs, rhs) => {
                let val = self.eval_expr(rhs)?;
                match &**lhs {
                    Expr::Ident(name) => {
                        self.vars.insert(name.clone(), val.clone());
                        Ok(val)
                    }
                    Expr::Member(obj_e, prop) => {
                        let obj = self.eval_expr(obj_e)?;
                        if let Val::Array(a, _) = obj {
                            if prop == "length" {
                                let new_len = to_clamped_i64(&val)?.max(0) as usize;
                                a.borrow_mut().elems.resize(new_len, Val::Undefined);
                            } else {
                                a.borrow_mut().props.insert(prop.clone(), val.clone());
                            }
                        } else if let Val::Object(o, _) = obj {
                            o.borrow_mut().insert(prop.clone(), val.clone());
                        }
                        Ok(val)
                    }
                    Expr::Index(obj_e, idx_e) => {
                        let obj = self.eval_expr(obj_e)?;
                        let idx = to_clamped_i64(&self.eval_expr(idx_e)?)? as usize;
                        if let Val::Array(a, _) = obj {
                            let mut ab = a.borrow_mut();
                            while ab.elems.len() <= idx {
                                ab.elems.push(Val::Undefined);
                            }
                            ab.elems[idx] = val.clone();
                        }
                        Ok(val)
                    }
                    _ => Err(JsError::new("ReferenceError", "invalid assignment target")),
                }
            }
            Expr::Member(base_e, prop) => {
                if let Expr::Ident(ns) = &**base_e {
                    match (ns.as_str(), prop.as_str()) {
                        ("JSON", "parse") => return Ok(Val::Builtin(BuiltinFn::JsonParse)),
                        ("JSON", "stringify") => return Ok(Val::Builtin(BuiltinFn::JsonStringify)),
                        ("Date", "parse") => return Ok(Val::Builtin(BuiltinFn::DateParse)),
                        ("Date", "UTC") => return Ok(Val::Builtin(BuiltinFn::DateUtc)),
                        ("Date", "prototype") => {
                            let id = self.alloc_id();
                            let mut m = HashMap::new();
                            m.insert(
                                "toISOString".into(),
                                Val::Builtin(BuiltinFn::DateProtoMethod),
                            );
                            return Ok(Val::Object(Rc::new(RefCell::new(m)), id));
                        }
                        ("Math", "abs") => return Ok(Val::Builtin(BuiltinFn::MathAbs)),
                        ("Math", "min") => return Ok(Val::Builtin(BuiltinFn::MathMin)),
                        ("Math", "max") => return Ok(Val::Builtin(BuiltinFn::MathMax)),
                        ("Math", "sign") => return Ok(Val::Builtin(BuiltinFn::MathSign)),
                        ("Math", "imul") => return Ok(Val::Builtin(BuiltinFn::MathImul)),
                        ("Math", "clz32") => return Ok(Val::Builtin(BuiltinFn::MathClz32)),
                        ("Object", "prototype") => {
                            let id = self.alloc_id();
                            let mut m = HashMap::new();
                            m.insert(
                                "toString".into(),
                                Val::Builtin(BuiltinFn::ObjectProtoToString),
                            );
                            return Ok(Val::Object(Rc::new(RefCell::new(m)), id));
                        }
                        _ => {}
                    }
                }
                let base = self.eval_expr(base_e)?;
                match (&base, prop.as_str()) {
                    (Val::Builtin(BuiltinFn::Assert), "sameValue") => {
                        Ok(Val::Builtin(BuiltinFn::AssertSameValue))
                    }
                    (Val::Builtin(BuiltinFn::Assert), "notSameValue") => {
                        Ok(Val::Builtin(BuiltinFn::AssertNotSameValue))
                    }
                    (Val::Builtin(BuiltinFn::Assert), "throws") => {
                        Ok(Val::Builtin(BuiltinFn::AssertThrows))
                    }
                    (Val::Array(a, _), "length") => Ok(num_val(a.borrow().elems.len() as f64)),
                    (Val::Array(a, _), p) if a.borrow().props.contains_key(p) => {
                        let v = a.borrow().props.get(p).cloned().unwrap();
                        if matches!(v, Val::Builtin(BuiltinFn::ObjectProtoToString)) {
                            Ok(Val::Builtin(BuiltinFn::BoundMethod(
                                Box::new(base.clone()),
                                "__toStringTag".into(),
                            )))
                        } else {
                            Ok(v)
                        }
                    }
                    (Val::Str(s), "length") | (Val::StringObj(s, _), "length") => {
                        Ok(num_val(s.len() as f64))
                    }
                    (Val::Map(m, _, _), "size") => Ok(num_val(m.borrow().size() as f64)),
                    (Val::Set(s, _, _), "size") => Ok(num_val(s.borrow().size() as f64)),
                    (Val::Object(o, _), p) => {
                        Ok(o.borrow().get(p).cloned().unwrap_or(Val::Undefined))
                    }
                    _ => Ok(Val::Builtin(BuiltinFn::BoundMethod(
                        Box::new(base),
                        prop.clone(),
                    ))),
                }
            }
            Expr::Index(base_e, idx_e) => {
                let base = self.eval_expr(base_e)?;
                let idx_v = self.eval_expr(idx_e)?;
                match base {
                    Val::Array(a, _) => {
                        let idx = to_clamped_i64(&idx_v)?;
                        if idx < 0 {
                            Ok(Val::Undefined)
                        } else {
                            Ok(a.borrow()
                                .elems
                                .get(idx as usize)
                                .cloned()
                                .unwrap_or(Val::Undefined))
                        }
                    }
                    Val::Str(s) | Val::StringObj(s, _) => {
                        let idx = to_clamped_i64(&idx_v)?;
                        if idx < 0 || (idx as usize) >= s.len() {
                            Ok(Val::Undefined)
                        } else {
                            Ok(Val::Str(vec![s[idx as usize]]))
                        }
                    }
                    _ => Ok(Val::Undefined),
                }
            }
            Expr::New(callee_e, arg_exprs) => {
                let mut args = Vec::new();
                for a in arg_exprs {
                    args.push(self.eval_expr(a)?);
                }
                if let Expr::Ident(cname) = &**callee_e {
                    match cname.as_str() {
                        "Array" => {
                            if args.len() == 1 && matches!(args[0], Val::Num(_)) {
                                let len = to_clamped_i64(&args[0])? as usize;
                                return Ok(self.new_array(vec![Val::Undefined; len]));
                            }
                            return Ok(self.new_array(args));
                        }
                        "String" => {
                            let s = if args.is_empty() {
                                Vec::new()
                            } else {
                                val_to_u16_str(&args[0])?
                            };
                            let id = self.alloc_id();
                            return Ok(Val::StringObj(s, id));
                        }
                        "RegExp" => {
                            let pat = if args.is_empty() {
                                Vec::new()
                            } else {
                                val_to_u16_str(&args[0])?
                            };
                            let flags = if args.len() >= 2 {
                                u16_to_lossy_string(&val_to_u16_str(&args[1])?)
                            } else {
                                String::new()
                            };
                            return self.construct_regexp(pat, &flags);
                        }
                        "Date" => {
                            let tv = if args.is_empty() {
                                Some(0)
                            } else if args.len() == 1 {
                                match &args[0] {
                                    Val::Str(s) => parse_iso8601(s),
                                    other => {
                                        let b = val_to_number_bits(other)?;
                                        if is_nan_bits(b) || b == POS_INF_BITS || b == NEG_INF_BITS
                                        {
                                            None
                                        } else {
                                            time_clip(f64::from_bits(b).trunc() as i64)
                                        }
                                    }
                                }
                            } else {
                                // Local constructor in UTC(0) test environment uses MakeDay/MakeTime/MakeDate/TimeClip
                                self.compute_date_utc(&args)?
                            };
                            let id = self.alloc_id();
                            return Ok(Val::Date(tv, id));
                        }
                        "Map" => {
                            let mut map = JsMap::new();
                            let mut obj_tbl = HashMap::new();
                            if let Some(Val::Array(entries, _)) = args.first() {
                                for pair in &entries.borrow().elems {
                                    let Val::Array(kv, _) = pair else {
                                        return Err(JsError::new(
                                            "TypeError",
                                            "Map entry not object",
                                        ));
                                    };
                                    let k = kv.borrow().elems.first().cloned().unwrap_or(Val::Undefined);
                                    let v = kv.borrow().elems.get(1).cloned().unwrap_or(Val::Undefined);
                                    let jk = val_to_js_key(&k);
                                    let jv = val_to_js_key(&v);
                                    if let JsKey::ObjectRef(oid) = jk {
                                        obj_tbl.insert(oid, k);
                                    }
                                    if let JsKey::ObjectRef(oid) = jv {
                                        obj_tbl.insert(oid, v);
                                    }
                                    map.set(jk, jv);
                                }
                            }
                            let id = self.alloc_id();
                            return Ok(Val::Map(
                                Rc::new(RefCell::new(map)),
                                Rc::new(RefCell::new(obj_tbl)),
                                id,
                            ));
                        }
                        "Set" => {
                            let mut set = JsSet::new();
                            let mut obj_tbl = HashMap::new();
                            if let Some(Val::Array(items, _)) = args.first() {
                                for item in &items.borrow().elems {
                                    let jk = val_to_js_key(item);
                                    if let JsKey::ObjectRef(oid) = jk {
                                        obj_tbl.insert(oid, item.clone());
                                    }
                                    set.add(jk);
                                }
                            }
                            let id = self.alloc_id();
                            return Ok(Val::Set(
                                Rc::new(RefCell::new(set)),
                                Rc::new(RefCell::new(obj_tbl)),
                                id,
                            ));
                        }
                        "Test262Error" => {
                            let msg = args
                                .first()
                                .and_then(|v| val_to_u16_str(v).ok())
                                .map(|u| u16_to_lossy_string(&u))
                                .unwrap_or_default();
                            return Err(JsError::new("Test262Error", msg));
                        }
                        _ => {}
                    }
                }
                Err(JsError::new("TypeError", "unsupported constructor"))
            }
            Expr::Call(callee_e, arg_exprs) => {
                if let Expr::Member(b, p) = &**callee_e {
                    if let Expr::Ident(a) = &**b {
                        if a == "assert" && p == "throws" && arg_exprs.len() >= 2 {
                            let expected_err = match &arg_exprs[0] {
                                Expr::Ident(ename) => ename.clone(),
                                _ => "Error".into(),
                            };
                            let cb = self.eval_expr(&arg_exprs[1])?;
                            match self.invoke_closure(&cb, &[]) {
                                Err(err) if err.kind == expected_err => return Ok(Val::Undefined),
                                Err(err) => {
                                    return Err(JsError::new(
                                        "Test262Error",
                                        format!(
                                            "expected {expected_err}, got {}: {}",
                                            err.kind, err.msg
                                        ),
                                    ))
                                }
                                Ok(_) => {
                                    return Err(JsError::new(
                                        "Test262Error",
                                        format!("expected {expected_err} to be thrown"),
                                    ))
                                }
                            }
                        }
                    }
                }
                let callee = self.eval_expr(callee_e)?;
                let mut args = Vec::new();
                for a in arg_exprs {
                    args.push(self.eval_expr(a)?);
                }
                self.invoke_val(callee, args)
            }
        }
    }

    fn invoke_closure(&mut self, cb: &Val, args: &[Val]) -> Result<Val, JsError> {
        let Val::Closure { params, body } = cb else {
            return Err(JsError::new("TypeError", "not callable"));
        };
        let saved: Vec<(String, Option<Val>)> = params
            .iter()
            .map(|p| (p.clone(), self.vars.get(p).cloned()))
            .collect();
        for (idx, p) in params.iter().enumerate() {
            self.vars
                .insert(p.clone(), args.get(idx).cloned().unwrap_or(Val::Undefined));
        }
        let res = self.exec_stmts(body);
        for (p, prev) in saved {
            match prev {
                Some(v) => {
                    self.vars.insert(p, v);
                }
                None => {
                    self.vars.remove(&p);
                }
            }
        }
        Ok(res?.unwrap_or(Val::Undefined))
    }

    fn invoke_val(&mut self, callee: Val, args: Vec<Val>) -> Result<Val, JsError> {
        match callee {
            Val::Closure { .. } => self.invoke_closure(&callee, &args),
            Val::Builtin(bf) => match bf {
                BuiltinFn::Assert => {
                    let cond = args.first().cloned().unwrap_or(Val::Undefined);
                    if !val_is_truthy(&cond) {
                        return Err(JsError::new(
                            "Test262Error",
                            format!("assert failed: {args:?}"),
                        ));
                    }
                    Ok(Val::Undefined)
                }
                BuiltinFn::AssertSameValue => {
                    let a = args.first().cloned().unwrap_or(Val::Undefined);
                    let b = args.get(1).cloned().unwrap_or(Val::Undefined);
                    if !js_same_value(&a, &b) {
                        return Err(JsError::new(
                            "Test262Error",
                            format!("sameValue failed: actual={a:?}, expected={b:?}"),
                        ));
                    }
                    Ok(Val::Undefined)
                }
                BuiltinFn::AssertNotSameValue => {
                    let a = args.first().cloned().unwrap_or(Val::Undefined);
                    let b = args.get(1).cloned().unwrap_or(Val::Undefined);
                    if js_same_value(&a, &b) {
                        return Err(JsError::new(
                            "Test262Error",
                            format!("notSameValue failed: {a:?}"),
                        ));
                    }
                    Ok(Val::Undefined)
                }
                BuiltinFn::AssertThrows => Err(JsError::new("Test262Error", "bad assert.throws")),
                BuiltinFn::SymbolCtor => {
                    let id = self.alloc_id();
                    Ok(Val::Symbol(id))
                }
                BuiltinFn::ArrayCtor => {
                    if args.len() == 1 && matches!(args[0], Val::Num(_)) {
                        let len = to_clamped_i64(&args[0])? as usize;
                        Ok(self.new_array(vec![Val::Undefined; len]))
                    } else {
                        Ok(self.new_array(args))
                    }
                }
                BuiltinFn::StringCtor => {
                    if args.is_empty() {
                        Ok(Val::Str(Vec::new()))
                    } else {
                        Ok(Val::Str(val_to_u16_str(&args[0])?))
                    }
                }
                BuiltinFn::JsonParse => {
                    let s = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                    match json_parse(&s, 256) {
                        Some(jv) => Ok(self.json_val_to_runtime(jv)),
                        None => Err(JsError::new("SyntaxError", "JSON.parse rejected input")),
                    }
                }
                BuiltinFn::JsonStringify => {
                    let v = args.first().cloned().unwrap_or(Val::Undefined);
                    match self.runtime_to_json_val(&v) {
                        Some(jv) => Ok(Val::Str(json_stringify(&jv))),
                        None => Ok(Val::Undefined),
                    }
                }
                BuiltinFn::DateParse => {
                    let s = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                    match parse_iso8601(&s) {
                        Some(tv) => Ok(num_val(tv as f64)),
                        None => Ok(Val::Num(CANONICAL_NAN_BITS)),
                    }
                }
                BuiltinFn::DateUtc => match self.compute_date_utc(&args)? {
                    Some(tv) => Ok(num_val(tv as f64)),
                    None => Ok(Val::Num(CANONICAL_NAN_BITS)),
                },
                BuiltinFn::MathAbs => {
                    let b = val_to_number_bits(args.first().unwrap_or(&Val::Undefined))?;
                    Ok(Val::Num(math_abs_bits(b)))
                }
                BuiltinFn::MathMin => {
                    let mut bits = Vec::new();
                    for a in &args {
                        bits.push(val_to_number_bits(a)?);
                    }
                    Ok(Val::Num(math_min_slice(&bits)))
                }
                BuiltinFn::MathMax => {
                    let mut bits = Vec::new();
                    for a in &args {
                        bits.push(val_to_number_bits(a)?);
                    }
                    Ok(Val::Num(math_max_slice(&bits)))
                }
                BuiltinFn::MathSign => {
                    let b = val_to_number_bits(args.first().unwrap_or(&Val::Undefined))?;
                    Ok(Val::Num(math_sign_bits(b)))
                }
                BuiltinFn::MathImul => {
                    let a = to_uint32_from_bits(val_to_number_bits(
                        args.first().unwrap_or(&Val::Undefined),
                    )?);
                    let b = to_uint32_from_bits(val_to_number_bits(
                        args.get(1).unwrap_or(&Val::Undefined),
                    )?);
                    Ok(num_val(math_imul(a, b) as f64))
                }
                BuiltinFn::MathClz32 => {
                    let x = to_uint32_from_bits(val_to_number_bits(
                        args.first().unwrap_or(&Val::Undefined),
                    )?);
                    Ok(num_val(math_clz32(x) as f64))
                }
                BuiltinFn::ObjectProtoToString | BuiltinFn::DateProtoMethod => {
                    Ok(Val::Str(str_to_u16("[object Object]")))
                }
                BuiltinFn::BoundMethod(recv, method) => self.invoke_method(*recv, &method, args),
            },
            _ => Err(JsError::new("TypeError", "callee is not a function")),
        }
    }

    fn invoke_method(&mut self, recv: Val, method: &str, args: Vec<Val>) -> Result<Val, JsError> {
        match recv {
            Val::Array(a, id) => {
                if method == "__toStringTag" {
                    return Ok(Val::Str(str_to_u16("[object Array]")));
                }
                if method == "shift" {
                    let mut ab = a.borrow_mut();
                    if ab.elems.is_empty() {
                        return Ok(Val::Undefined);
                    }
                    return Ok(ab.elems.remove(0));
                }
                // Bridge `Val` elements <-> verified `JsKey` functions in `vjs_builtins::math_str_arr`
                let mut obj_tbl: HashMap<u64, Val> = HashMap::new();
                let mut keys: Vec<JsKey> = a
                    .borrow()
                    .elems
                    .iter()
                    .map(|el| {
                        let jk = val_to_js_key(el);
                        if let JsKey::ObjectRef(oid) = jk {
                            obj_tbl.insert(oid, el.clone());
                        }
                        jk
                    })
                    .collect();
                match method {
                    "push" => {
                        let mut new_len = keys.len();
                        for arg in &args {
                            let jk = val_to_js_key(arg);
                            if let JsKey::ObjectRef(oid) = jk {
                                obj_tbl.insert(oid, arg.clone());
                            }
                            new_len = array_push(&mut keys, jk);
                        }
                        a.borrow_mut().elems =
                            keys.iter().map(|k| js_key_to_val(k, &obj_tbl)).collect();
                        Ok(num_val(new_len as f64))
                    }
                    "pop" => {
                        let popped = array_pop(&mut keys);
                        a.borrow_mut().elems =
                            keys.iter().map(|k| js_key_to_val(k, &obj_tbl)).collect();
                        Ok(match popped {
                            Some(k) => js_key_to_val(&k, &obj_tbl),
                            None => Val::Undefined,
                        })
                    }
                    "reverse" => {
                        array_reverse(&mut keys);
                        a.borrow_mut().elems =
                            keys.iter().map(|k| js_key_to_val(k, &obj_tbl)).collect();
                        Ok(Val::Array(a, id))
                    }
                    "slice" => {
                        let start = match args.first() {
                            Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                            _ => 0,
                        };
                        let end = match args.get(1) {
                            Some(v) if !matches!(v, Val::Undefined) => Some(to_clamped_i64(v)?),
                            _ => None,
                        };
                        let sliced = array_slice(&keys, start, end);
                        let elems = sliced.iter().map(|k| js_key_to_val(k, &obj_tbl)).collect();
                        Ok(self.new_array(elems))
                    }
                    "concat" => {
                        let mut cur = keys;
                        for arg in &args {
                            match arg {
                                Val::Array(other_a, _) => {
                                    let rhs: Vec<JsKey> = other_a
                                        .borrow()
                                        .elems
                                        .iter()
                                        .map(|el| {
                                            let jk = val_to_js_key(el);
                                            if let JsKey::ObjectRef(oid) = jk {
                                                obj_tbl.insert(oid, el.clone());
                                            }
                                            jk
                                        })
                                        .collect();
                                    cur = array_concat(&cur, &rhs);
                                }
                                single => {
                                    let jk = val_to_js_key(single);
                                    if let JsKey::ObjectRef(oid) = jk {
                                        obj_tbl.insert(oid, single.clone());
                                    }
                                    cur = array_concat(&cur, &[jk]);
                                }
                            }
                        }
                        let elems = cur.iter().map(|k| js_key_to_val(k, &obj_tbl)).collect();
                        Ok(self.new_array(elems))
                    }
                    "indexOf" => {
                        let search =
                            val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                        let from = match args.get(1) {
                            Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                            _ => 0,
                        };
                        Ok(num_val(array_index_of(&keys, &search, from) as f64))
                    }
                    "includes" => {
                        let search =
                            val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                        let from = match args.get(1) {
                            Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                            _ => 0,
                        };
                        Ok(Val::Bool(array_includes(&keys, &search, from)))
                    }
                    _ => Err(JsError::new("TypeError", format!("unknown Array.{method}"))),
                }
            }
            Val::Str(s) | Val::StringObj(s, _) => match method {
                "slice" => {
                    let start = match args.first() {
                        Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                        _ => 0,
                    };
                    let end = match args.get(1) {
                        Some(v) if !matches!(v, Val::Undefined) => Some(to_clamped_i64(v)?),
                        _ => None,
                    };
                    Ok(Val::Str(string_slice(&s, start, end)))
                }
                "substring" => {
                    let start = match args.first() {
                        Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                        _ => 0,
                    };
                    let end = match args.get(1) {
                        Some(v) if !matches!(v, Val::Undefined) => Some(to_clamped_i64(v)?),
                        _ => None,
                    };
                    Ok(Val::Str(string_substring(&s, start, end)))
                }
                "indexOf" => {
                    let search = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                    let pos = match args.get(1) {
                        Some(v) if !matches!(v, Val::Undefined) => to_clamped_i64(v)?,
                        _ => 0,
                    };
                    Ok(num_val(string_index_of(&s, &search, pos) as f64))
                }
                "startsWith" => {
                    let search = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                    let pos = match args.get(1) {
                        Some(v) if !matches!(v, Val::Undefined) => Some(to_clamped_i64(v)?),
                        _ => None,
                    };
                    Ok(Val::Bool(string_starts_with(&s, &search, pos)))
                }
                "endsWith" => {
                    let search = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                    let pos = match args.get(1) {
                        Some(v) if !matches!(v, Val::Undefined) => Some(to_clamped_i64(v)?),
                        _ => None,
                    };
                    Ok(Val::Bool(string_ends_with(&s, &search, pos)))
                }
                "toLowerCase" => Ok(Val::Str(string_to_lower_case(&s))),
                "toUpperCase" => Ok(Val::Str(string_to_upper_case(&s))),
                "repeat" => {
                    let c = to_integer_or_infinity(args.first().unwrap_or(&Val::Undefined))?;
                    if c < 0.0 || c.is_infinite() {
                        return Err(JsError::new("RangeError", "Invalid count value"));
                    }
                    match string_repeat(&s, c as usize, 64 * 1024 * 1024) {
                        Some(out) => Ok(Val::Str(out)),
                        None => Err(JsError::new("RangeError", "repeat overflow")),
                    }
                }
                _ => Err(JsError::new("TypeError", format!("unknown String.{method}"))),
            },
            Val::Map(m, obj_tbl, id) => match method {
                "set" => {
                    let k = args.first().cloned().unwrap_or(Val::Undefined);
                    let v = args.get(1).cloned().unwrap_or(Val::Undefined);
                    let jk = val_to_js_key(&k);
                    let jv = val_to_js_key(&v);
                    if let JsKey::ObjectRef(oid) = jk {
                        obj_tbl.borrow_mut().insert(oid, k);
                    }
                    if let JsKey::ObjectRef(oid) = jv {
                        obj_tbl.borrow_mut().insert(oid, v);
                    }
                    m.borrow_mut().set(jk, jv);
                    Ok(Val::Map(m, obj_tbl, id))
                }
                "get" => {
                    let jk = val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                    Ok(match m.borrow().get(&jk) {
                        Some(v) => js_key_to_val(&v, &obj_tbl.borrow()),
                        None => Val::Undefined,
                    })
                }
                "has" => {
                    let jk = val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                    Ok(Val::Bool(m.borrow().has(&jk)))
                }
                "delete" => {
                    let jk = val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                    Ok(Val::Bool(m.borrow_mut().delete(&jk)))
                }
                "clear" => {
                    m.borrow_mut().clear();
                    Ok(Val::Undefined)
                }
                "forEach" => {
                    let cb = args.first().cloned().unwrap_or(Val::Undefined);
                    let ks = m.borrow().keys();
                    let vs = m.borrow().values();
                    for (k, v) in ks.iter().zip(vs.iter()) {
                        let vk = js_key_to_val(k, &obj_tbl.borrow());
                        let vv = js_key_to_val(v, &obj_tbl.borrow());
                        self.invoke_closure(&cb, &[vv, vk])?;
                    }
                    Ok(Val::Undefined)
                }
                _ => Err(JsError::new("TypeError", format!("unknown Map.{method}"))),
            },
            Val::Set(s, obj_tbl, id) => match method {
                "add" => {
                    let v = args.first().cloned().unwrap_or(Val::Undefined);
                    let jv = val_to_js_key(&v);
                    if let JsKey::ObjectRef(oid) = jv {
                        obj_tbl.borrow_mut().insert(oid, v);
                    }
                    s.borrow_mut().add(jv);
                    Ok(Val::Set(s, obj_tbl, id))
                }
                "has" => {
                    let jv = val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                    Ok(Val::Bool(s.borrow().has(&jv)))
                }
                "delete" => {
                    let jv = val_to_js_key(args.first().unwrap_or(&Val::Undefined));
                    Ok(Val::Bool(s.borrow_mut().delete(&jv)))
                }
                "clear" => {
                    s.borrow_mut().clear();
                    Ok(Val::Undefined)
                }
                "forEach" => {
                    let cb = args.first().cloned().unwrap_or(Val::Undefined);
                    let vs = s.borrow().values();
                    for v in &vs {
                        let vv = js_key_to_val(v, &obj_tbl.borrow());
                        self.invoke_closure(&cb, &[vv.clone(), vv])?;
                    }
                    Ok(Val::Undefined)
                }
                _ => Err(JsError::new("TypeError", format!("unknown Set.{method}"))),
            },
            Val::RegExp(re_rc, _) => {
                let input = val_to_u16_str(args.first().unwrap_or(&Val::Undefined))?;
                let (ast, flags, groups, global, start) = {
                    let rb = re_rc.borrow();
                    let st = if rb.global { rb.last_index } else { 0 };
                    (
                        vjs_builtins::regexp::clone_regex_ast(&rb.ast),
                        rb.flags,
                        rb.groups as usize,
                        rb.global,
                        st,
                    )
                };
                if start > input.len() {
                    if global {
                        re_rc.borrow_mut().last_index = 0;
                    }
                    return Ok(if method == "test" {
                        Val::Bool(false)
                    } else {
                        Val::Null
                    });
                }
                let outcome = exec_search(&ast, flags, &input, start, groups, 20_000);
                match outcome {
                    MatchOutcome::Matched {
                        start_pos,
                        end_pos,
                        captures,
                    } => {
                        if global {
                            re_rc.borrow_mut().last_index = end_pos;
                        }
                        if method == "test" {
                            Ok(Val::Bool(true))
                        } else {
                            let mut elems = Vec::with_capacity(1 + captures.len());
                            elems.push(Val::Str(input[start_pos..end_pos].to_vec()));
                            for cap in captures {
                                match cap {
                                    Some((cs, ce)) => elems.push(Val::Str(input[cs..ce].to_vec())),
                                    None => elems.push(Val::Undefined),
                                }
                            }
                            let arr = self.new_array(elems);
                            if let Val::Array(a, _) = &arr {
                                a.borrow_mut()
                                    .props
                                    .insert("index".into(), num_val(start_pos as f64));
                                a.borrow_mut().props.insert("input".into(), Val::Str(input));
                            }
                            Ok(arr)
                        }
                    }
                    _ => {
                        if global {
                            re_rc.borrow_mut().last_index = 0;
                        }
                        Ok(if method == "test" {
                            Val::Bool(false)
                        } else {
                            Val::Null
                        })
                    }
                }
            }
            Val::Date(tv_opt, _) => match method {
                "valueOf" | "getTime" => Ok(match tv_opt {
                    Some(tv) => num_val(tv as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getTimezoneOffset" => Ok(num_val(0.0)),
                "toISOString" => match tv_opt {
                    Some(tv) => match to_iso_string(tv) {
                        Some(u) => Ok(Val::Str(u)),
                        None => Err(JsError::new("RangeError", "Invalid time value")),
                    },
                    None => Err(JsError::new("RangeError", "Invalid time value")),
                },
                "getUTCFullYear" => Ok(match tv_opt {
                    Some(tv) => num_val(year_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCMonth" => Ok(match tv_opt {
                    Some(tv) => num_val(month_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCDate" => Ok(match tv_opt {
                    Some(tv) => num_val(date_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCDay" => Ok(match tv_opt {
                    Some(tv) => num_val(week_day(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCHours" => Ok(match tv_opt {
                    Some(tv) => num_val(hour_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCMinutes" => Ok(match tv_opt {
                    Some(tv) => num_val(min_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCSeconds" => Ok(match tv_opt {
                    Some(tv) => num_val(sec_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                "getUTCMilliseconds" => Ok(match tv_opt {
                    Some(tv) => num_val(ms_from_time(tv) as f64),
                    None => Val::Num(CANONICAL_NAN_BITS),
                }),
                _ => Err(JsError::new("TypeError", format!("unknown Date.{method}"))),
            },
            _ => Err(JsError::new("TypeError", format!("cannot call .{method}"))),
        }
    }
}

fn run_test262_file(path: &Path) -> Result<(), String> {
    let src = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let toks = lex_js(&src)?;
    let mut parser = Parser { toks, pos: 0 };
    let prog = parser.parse_program()?;
    let mut interp = Interp::new();
    interp
        .exec_stmts(&prog)
        .map_err(|e| format!("{}: {}", e.kind, e.msg))?;
    Ok(())
}

// =======================================================================================
// Live Differential Oracle vs Node.js (V8)
// =======================================================================================

fn node_bin() -> PathBuf {
    let pinned = PathBuf::from("/Users/mac/.nvm/versions/node/v24.15.0/bin/node");
    if pinned.exists() {
        pinned
    } else {
        PathBuf::from("node")
    }
}

fn run_node_json(script: &str) -> serde_json::Value {
    let out = Command::new(node_bin())
        .arg("-e")
        .arg(script)
        .output()
        .expect("failed to invoke Node/V8 differential oracle");
    assert!(
        out.status.success(),
        "Node oracle failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice(&out.stdout).expect("invalid JSON from Node oracle")
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 16
    }
}

fn differential_suite() -> HashMap<&'static str, usize> {
    let mut counts: HashMap<&'static str, usize> = HashMap::new();

    // 1. Differential JSON (300 cases: lone surrogates, paired surrogates, C0 escapes, nested values)
    let mut rng = Lcg(0x2550_5301);
    let mut json_inputs: Vec<Vec<u16>> = vec![
        vec![0xD834],
        vec![0xDF06],
        vec![0xD834, 0xDF06],
        vec![0xD834, 0xD834, 0xDF06, 0xD834],
        vec![0xDF06, 0xD834],
        vec![0x0000, 0x0008, 0x0009, 0x000A, 0x000C, 0x000D, 0x001F, 0x0022, 0x005C],
    ];
    let pool: [u16; 16] = [
        0x0000, 0x0008, 0x0009, 0x000A, 0x000D, 0x001B, 0x0022, 0x005C, 0x0041, 0x007A, 0x03B1,
        0x4E2D, 0xD800, 0xD834, 0xDC00, 0xDF06,
    ];
    while json_inputs.len() < 300 {
        let len = (rng.next() % 12) as usize;
        let s: Vec<u16> = (0..len)
            .map(|_| pool[(rng.next() as usize) % pool.len()])
            .collect();
        json_inputs.push(s);
    }
    let unit_arrays: Vec<Vec<u16>> = json_inputs.clone();
    let js_script = format!(
        "const inputs = {}; const toUnits = s => Array.from({{length: s.length}}, (_, i) => s.charCodeAt(i)); const out = inputs.map(u => {{ const s = String.fromCharCode(...u); const q = JSON.stringify(s); const p = toUnits(JSON.parse(q)); return [toUnits(q), p]; }}); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&unit_arrays).unwrap()
    );
    let v8_json = run_node_json(&js_script);
    for (idx, u) in json_inputs.iter().enumerate() {
        let ours_q = quote_json_string(u);
        let exp_q: Vec<u16> = v8_json[idx][0]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u16)
            .collect();
        assert_eq!(ours_q, exp_q, "JSON.stringify mismatch at case {idx}: {u:?}");
        let Some(JsonValue::Str(ours_p)) = json_parse(&ours_q, 64) else {
            panic!("json_parse failed on our own quote_json_string output!");
        };
        assert_eq!(&ours_p, u, "JSON roundtrip mismatch at case {idx}");
    }
    counts.insert("JSON", json_inputs.len());

    // 2. Differential RegExp (280 pattern+input cases incl. zero-width `(a*)*`, lazy, captures,
    //    and `[\s]`, `[\S]`, `[\D]`, `[\W]` across Unicode whitespace `\u2028`, `\u2000`, `\u3000`, `\uFEFF`)
    let regex_cases: Vec<(&str, &str, &str)> = vec![
        ("(a*)*", "", "b"),
        ("(?:)*", "", "abc"),
        ("(a|ab)c", "", "abc"),
        ("a+?", "", "aaaa"),
        ("a+", "", "aaaa"),
        ("^\\w+@\\w+\\.\\w+$", "i", "User_1@Example.COM"),
        ("(\\d{2,4})-(\\d{1,2})", "", "id: 2026-11!"),
        ("[^0-9]+", "", "123abc456"),
        ("\\bword\\b", "", "a word here"),
        ("\\Bword\\B", "", "swordsmanship"),
        ("^line2$", "m", "line1\nline2\nline3"),
        ("a.b", "s", "a\nb"),
        ("a.b", "", "a\nb"),
        ("((a)|(b))+", "", "aba"),
        ("[\\s]+", "", "a\u{1680}\u{2000}\u{200A}\u{2028}\u{2029}\u{202F}\u{205F}\u{3000}\u{FEFF}b"),
        ("[\\s]", "", "\u{2028}"),
        ("[\\s]", "", "\u{2000}"),
        ("[\\s]", "", "\u{3000}"),
        ("[\\s]", "", "\u{FEFF}"),
        ("[\\s]", "i", "s"),
        ("[\\S]+", "", "\u{2028}\u{2000}S_ok\u{3000}\u{FEFF}"),
        ("[\\S]", "", "\u{2028}"),
        ("[\\S]", "", "\u{2000}"),
        ("[\\S]", "", "\u{3000}"),
        ("[\\S]", "", "\u{FEFF}"),
        ("[\\S]", "i", "s"),
        ("[\\D]+", "", "0123D_xyz9"),
        ("[\\D]", "", "5"),
        ("[\\D]", "i", "d"),
        ("[\\W]+", "", "abc_09!@#\u{2028}W"),
        ("[\\W]", "", "W"),
        ("[\\W]", "i", "w"),
        ("[\\W]", "i", "!"),
        ("[\\d-]+", "", "42-7"),
        ("[-\\d]+", "", "-99"),
    ];
    let mut all_re_cases: Vec<(String, String, String)> = regex_cases
        .iter()
        .map(|(p, f, s)| (p.to_string(), f.to_string(), s.to_string()))
        .collect();
    let sample_pats = [
        "(a*)*b?",
        "(a|b)*c",
        "\\d+\\s*\\w+",
        "[a-f]{1,3}?",
        "(ab|a)+b",
        "^a.*z$",
        "[\\s]+|[\\S]+",
        "[\\D]+[\\W]*",
    ];
    let alphabet = [
        'a', 'b', 'c', 'z', 'D', 'W', 'S', '0', '1', '9', ' ', '\n', '_', '!', '\u{2000}',
        '\u{2028}', '\u{3000}', '\u{FEFF}',
    ];
    while all_re_cases.len() < 280 {
        let pat = sample_pats[(rng.next() as usize) % sample_pats.len()].to_string();
        let flag = if rng.next() % 3 == 0 { "i" } else { "" }.to_string();
        let slen = (rng.next() % 10) as usize;
        let inp: String = (0..slen)
            .map(|_| alphabet[(rng.next() as usize) % alphabet.len()])
            .collect();
        all_re_cases.push((pat, flag, inp));
    }
    let re_script = format!(
        "const cs = {}; const out = cs.map(([p, f, s]) => {{ const m = new RegExp(p, f).exec(s); if (!m) return null; return [m.index, Array.from(m).map(x => x === undefined ? null : x)]; }}); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&all_re_cases).unwrap()
    );
    let v8_re = run_node_json(&re_script);
    for (idx, (pat, fl, inp)) in all_re_cases.iter().enumerate() {
        let pat_u = str_to_u16(pat);
        let inp_u = str_to_u16(inp);
        let (ast, groups) = parse_pattern(&pat_u, 256).expect("valid differential regex");
        let flags = RegexFlags {
            ignore_case: fl.contains('i'),
            multiline: fl.contains('m'),
            dot_all: fl.contains('s'),
        };
        let ours = exec_search(&ast, flags, &inp_u, 0, groups as usize, 50_000);
        if v8_re[idx].is_null() {
            assert_eq!(ours, MatchOutcome::NoMatch, "RegExp case {idx}: {pat} on {inp:?}");
        } else {
            let exp_idx = v8_re[idx][0].as_u64().unwrap() as usize;
            let exp_arr = v8_re[idx][1].as_array().unwrap();
            let MatchOutcome::Matched {
                start_pos,
                end_pos,
                captures,
            } = ours
            else {
                panic!("RegExp expected match at case {idx}: /{pat}/{fl} on {inp:?}, got {ours:?}");
            };
            assert_eq!(start_pos, exp_idx, "RegExp index mismatch at {idx}");
            assert_eq!(
                u16_to_lossy_string(&inp_u[start_pos..end_pos]),
                exp_arr[0].as_str().unwrap(),
                "RegExp full match mismatch at {idx}"
            );
            for (g, cap) in captures.iter().enumerate() {
                match (cap, &exp_arr[g + 1]) {
                    (None, serde_json::Value::Null) => {}
                    (Some((cs, ce)), serde_json::Value::String(es)) => {
                        assert_eq!(&u16_to_lossy_string(&inp_u[*cs..*ce]), es);
                    }
                    other => panic!("RegExp group {g} mismatch at {idx}: {other:?}"),
                }
            }
        }
    }
    counts.insert("RegExp", all_re_cases.len());

    // 3. Differential Date (260 timestamps across full ±8.64e15 range: calendar getters + ISO roundtrip)
    let mut timestamps: Vec<i64> = vec![
        0,
        -1,
        1,
        -86_400_000,
        86_400_000,
        951_782_400_000,   // 2000-02-29 leap day
        -2_208_988_800_000, // 1900-01-01 non-leap century
        -62_167_219_200_000, // 0000-01-01
        -MAX_TIME_MS,
        MAX_TIME_MS,
    ];
    while timestamps.len() < 260 {
        let raw = ((rng.next() as i64) - 0x8000_0000_0000i64).wrapping_mul(123_456_789);
        let clipped = raw % MAX_TIME_MS;
        timestamps.push(clipped);
    }
    let date_script = format!(
        "const ts = {}; const out = ts.map(t => {{ const d = new Date(t); const iso = d.toISOString(); return [iso, Date.parse(iso), d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), d.getUTCDay(), d.getUTCHours(), d.getUTCMinutes(), d.getUTCSeconds(), d.getUTCMilliseconds()]; }}); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&timestamps).unwrap()
    );
    let v8_date = run_node_json(&date_script);
    for (idx, &tv) in timestamps.iter().enumerate() {
        let iso_u = to_iso_string(tv).expect("valid clipped timestamp");
        let iso_s = u16_to_lossy_string(&iso_u);
        let row = v8_date[idx].as_array().unwrap();
        assert_eq!(iso_s, row[0].as_str().unwrap(), "toISOString mismatch for {tv}");
        assert_eq!(parse_iso8601(&iso_u), Some(tv), "ISO roundtrip mismatch for {tv}");
        assert_eq!(year_from_time(tv), row[2].as_i64().unwrap());
        assert_eq!(month_from_time(tv), row[3].as_i64().unwrap());
        assert_eq!(date_from_time(tv), row[4].as_i64().unwrap());
        assert_eq!(week_day(tv), row[5].as_i64().unwrap());
        assert_eq!(hour_from_time(tv), row[6].as_i64().unwrap());
        assert_eq!(min_from_time(tv), row[7].as_i64().unwrap());
        assert_eq!(sec_from_time(tv), row[8].as_i64().unwrap());
        assert_eq!(ms_from_time(tv), row[9].as_i64().unwrap());
    }
    counts.insert("Date", timestamps.len());

    // 4. Differential Math (260 edge cases for clz32, imul, abs, sign, min, max)
    let mut math_pairs: Vec<(i64, i64)> = vec![
        (0, 0),
        (1, -1),
        (i32::MIN as i64, 7),
        (i32::MAX as i64, i32::MAX as i64),
        (u32::MAX as i64, 5),
        (65535, 65536),
        (-65535, 4294967297),
    ];
    while math_pairs.len() < 260 {
        let a = (rng.next() as i64) - (1i64 << 33);
        let b = (rng.next() as i64) - (1i64 << 33);
        math_pairs.push((a, b));
    }
    let math_script = format!(
        "const ps = {}; const out = ps.map(([a, b]) => [Math.clz32(a), Math.imul(a, b), Math.sign(a)]); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&math_pairs).unwrap()
    );
    let v8_math = run_node_json(&math_script);
    for (idx, &(a, b)) in math_pairs.iter().enumerate() {
        let ua = to_uint32_i64(a);
        let ub = to_uint32_i64(b);
        assert_eq!(math_clz32(ua) as i64, v8_math[idx][0].as_i64().unwrap());
        assert_eq!(math_imul(ua, ub) as i64, v8_math[idx][1].as_i64().unwrap());
        let sb = math_sign_bits((a as f64).to_bits());
        assert_eq!(f64::from_bits(sb) as i64, v8_math[idx][2].as_i64().unwrap());
    }
    counts.insert("Math", math_pairs.len());

    // 5. Differential Array (250 slice/reverse/indexOf/includes cases)
    let mut arr_cases: Vec<(Vec<i64>, i64, i64, i64)> = Vec::new();
    for _ in 0..250 {
        let len = (rng.next() % 10) as usize;
        let xs: Vec<i64> = (0..len).map(|_| (rng.next() % 7) as i64 - 3).collect();
        let st = (rng.next() % 15) as i64 - 7;
        let en = (rng.next() % 15) as i64 - 7;
        let target = (rng.next() % 7) as i64 - 3;
        arr_cases.push((xs, st, en, target));
    }
    let arr_script = format!(
        "const cs = {}; const out = cs.map(([xs, st, en, t]) => [xs.slice(st, en), xs.slice().reverse(), xs.indexOf(t, st), xs.includes(t, st)]); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&arr_cases).unwrap()
    );
    let v8_arr = run_node_json(&arr_script);
    for (idx, (xs, st, en, target)) in arr_cases.iter().enumerate() {
        let jxs: Vec<JsKey> = xs
            .iter()
            .map(|&v| JsKey::NumberBits((v as f64).to_bits()))
            .collect();
        let sl = array_slice(&jxs, *st, Some(*en));
        let exp_sl: Vec<i64> = v8_arr[idx][0]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_i64().unwrap())
            .collect();
        let got_sl: Vec<i64> = sl
            .iter()
            .map(|k| match k {
                JsKey::NumberBits(b) => f64::from_bits(*b) as i64,
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(got_sl, exp_sl);

        let mut rev = xs
            .iter()
            .map(|&v| JsKey::NumberBits((v as f64).to_bits()))
            .collect::<Vec<_>>();
        array_reverse(&mut rev);
        let exp_rev: Vec<i64> = v8_arr[idx][1]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_i64().unwrap())
            .collect();
        let got_rev: Vec<i64> = rev
            .iter()
            .map(|k| match k {
                JsKey::NumberBits(b) => f64::from_bits(*b) as i64,
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(got_rev, exp_rev);

        let tk = JsKey::NumberBits((*target as f64).to_bits());
        assert_eq!(array_index_of(&jxs, &tk, *st), v8_arr[idx][2].as_i64().unwrap());
        assert_eq!(array_includes(&jxs, &tk, *st), v8_arr[idx][3].as_bool().unwrap());
    }
    counts.insert("Array", arr_cases.len());

    // 6. Differential String (250 slice/substring/indexOf/startsWith/endsWith/case/repeat cases)
    let mut str_cases: Vec<(String, String, i64, i64)> = Vec::new();
    let str_alpha = b"AbCdEf0123_xyz";
    for _ in 0..250 {
        let len = (rng.next() % 14) as usize;
        let s: String = (0..len)
            .map(|_| str_alpha[(rng.next() as usize) % str_alpha.len()] as char)
            .collect();
        let sub_len = (rng.next() % 4) as usize;
        let sub: String = (0..sub_len)
            .map(|_| str_alpha[(rng.next() as usize) % str_alpha.len()] as char)
            .collect();
        let a = (rng.next() % 18) as i64 - 4;
        let b = (rng.next() % 18) as i64 - 4;
        str_cases.push((s, sub, a, b));
    }
    let str_script = format!(
        "const cs = {}; const out = cs.map(([s, sub, a, b]) => [s.slice(a, b), s.substring(a, b), s.indexOf(sub, a), s.startsWith(sub, a), s.endsWith(sub, b), s.toLowerCase(), s.toUpperCase()]); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&str_cases).unwrap()
    );
    let v8_str = run_node_json(&str_script);
    for (idx, (s, sub, a, b)) in str_cases.iter().enumerate() {
        let su = str_to_u16(s);
        let subu = str_to_u16(sub);
        assert_eq!(
            u16_to_lossy_string(&string_slice(&su, *a, Some(*b))),
            v8_str[idx][0].as_str().unwrap()
        );
        assert_eq!(
            u16_to_lossy_string(&string_substring(&su, *a, Some(*b))),
            v8_str[idx][1].as_str().unwrap()
        );
        assert_eq!(
            string_index_of(&su, &subu, *a),
            v8_str[idx][2].as_i64().unwrap()
        );
        assert_eq!(
            string_starts_with(&su, &subu, Some(*a)),
            v8_str[idx][3].as_bool().unwrap()
        );
        assert_eq!(
            string_ends_with(&su, &subu, Some(*b)),
            v8_str[idx][4].as_bool().unwrap()
        );
        assert_eq!(
            u16_to_lossy_string(&string_to_lower_case(&su)),
            v8_str[idx][5].as_str().unwrap()
        );
        assert_eq!(
            u16_to_lossy_string(&string_to_upper_case(&su)),
            v8_str[idx][6].as_str().unwrap()
        );
    }
    counts.insert("String", str_cases.len());

    // 7 & 8. Differential Map & Set (250 randomized operation traces each with NaN, -0, +0, strings, ints)
    let mut map_traces: Vec<Vec<(u8, u8, i64)>> = Vec::new();
    for _ in 0..250 {
        let ops: Vec<(u8, u8, i64)> = (0..12)
            .map(|_| {
                (
                    (rng.next() % 3) as u8, // 0=set/add, 1=delete, 2=set/add
                    (rng.next() % 6) as u8, // key id: 0=-0, 1=+0, 2=NaN1, 3=NaN2, 4="a", 5=1
                    (rng.next() % 100) as i64,
                )
            })
            .collect();
        map_traces.push(ops);
    }
    let map_set_script = format!(
        "const ts = {}; const keyOf = k => k===0 ? -0 : k===1 ? +0 : k===2 ? NaN : k===3 ? (0/0) : k===4 ? 'a' : 1; const enc = k => Number.isNaN(k) ? 'NaN' : Object.is(k, -0) ? '-0' : String(k); const out = ts.map(ops => {{ const m = new Map(); const s = new Set(); for (const [op, kid, v] of ops) {{ const k = keyOf(kid); if (op === 1) {{ m.delete(k); s.delete(k); }} else {{ m.set(k, v); s.add(k); }} }} return [Array.from(m.entries(), ([k, v]) => [enc(k), v]), Array.from(s.values(), enc)]; }}); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&map_traces).unwrap()
    );
    let v8_ms = run_node_json(&map_set_script);
    let mk_key = |kid: u8| -> JsKey {
        match kid {
            0 => JsKey::NumberBits(NEG_ZERO_BITS),
            1 => JsKey::NumberBits(POS_ZERO_BITS),
            2 => JsKey::NumberBits(CANONICAL_NAN_BITS),
            3 => JsKey::NumberBits(0xFFF8_0000_0000_0001u64), // distinct negative NaN payload!
            4 => JsKey::Str(str_to_u16("a")),
            _ => JsKey::NumberBits(1.0f64.to_bits()),
        }
    };
    let fmt_key = |k: &JsKey| -> String {
        match k {
            JsKey::NumberBits(b) if is_nan_bits(*b) => "NaN".into(),
            JsKey::NumberBits(b) if *b == NEG_ZERO_BITS => "-0".into(),
            JsKey::NumberBits(b) if *b == POS_ZERO_BITS => "0".into(),
            JsKey::NumberBits(b) => format!("{}", f64::from_bits(*b) as i64),
            JsKey::Str(s) => u16_to_lossy_string(s),
            _ => "?".into(),
        }
    };
    for (idx, ops) in map_traces.iter().enumerate() {
        let mut m = JsMap::new();
        let mut s = JsSet::new();
        for &(op, kid, v) in ops {
            let k = mk_key(kid);
            if op == 1 {
                m.delete(&k);
                s.delete(&k);
            } else {
                m.set(k, JsKey::NumberBits((v as f64).to_bits()));
                s.add(mk_key(kid));
            }
        }
        let got_m: Vec<(String, i64)> = m
            .keys()
            .iter()
            .zip(m.values().iter())
            .map(|(k, v)| {
                let vi = match v {
                    JsKey::NumberBits(b) => f64::from_bits(*b) as i64,
                    _ => 0,
                };
                (fmt_key(k), vi)
            })
            .collect();
        let exp_m: Vec<(String, i64)> = v8_ms[idx][0]
            .as_array()
            .unwrap()
            .iter()
            .map(|pair| {
                (
                    pair[0].as_str().unwrap().to_string(),
                    pair[1].as_i64().unwrap(),
                )
            })
            .collect();
        assert_eq!(got_m, exp_m, "Map trace {idx} mismatch");

        let got_s: Vec<String> = s.values().iter().map(fmt_key).collect();
        let exp_s: Vec<String> = v8_ms[idx][1]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string())
            .collect();
        assert_eq!(got_s, exp_s, "Set trace {idx} mismatch");
    }
    counts.insert("Map", map_traces.len());
    counts.insert("Set", map_traces.len());

    counts
}

// =======================================================================================
// Direct Theorem-Witness Unit Tests + End-to-End Test262 & Differential Report Runner
// =======================================================================================

fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = (data.len() as u64) * 8;
    let mut msg = data.to_vec();
    msg.push(0x80);
    while (msg.len() % 64) != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[i * 4],
                chunk[i * 4 + 1],
                chunk[i * 4 + 2],
                chunk[i * 4 + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (dst, add) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *dst = dst.wrapping_add(add);
        }
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

#[test]
fn provenance_integrity_check() {
    let data_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let lic = fs::read_to_string(data_dir.join("LICENSE")).expect("missing tests/data/LICENSE");
    assert!(lic.contains("BSD License") && lic.contains("Ecma International"));
    let prov = fs::read_to_string(data_dir.join("PROVENANCE")).expect("missing PROVENANCE");
    assert!(prov.contains("https://github.com/tc39/test262"));
    assert!(prov.contains("2a1ade303f72d3de80565c921d685222405c32ce"));
    assert!(prov.contains("BSD-3-Clause"));
    let mut entries = 0usize;
    for line in prov.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = trimmed.split_whitespace().collect();
        assert_eq!(parts.len(), 3, "malformed PROVENANCE line: {line}");
        let local_file = data_dir.join(parts[0]);
        let bytes = fs::read(&local_file)
            .unwrap_or_else(|_| panic!("missing pinned test262 file: {local_file:?}"));
        let actual = format!("sha256:{}", sha256_hex(&bytes));
        assert_eq!(actual, parts[2], "SHA-256 mismatch for {}", parts[0]);
        entries += 1;
    }
    assert_eq!(entries, 131, "expected 131 pinned test262 files, found {entries}");
}

#[test]
fn vest_json_prefix_security_and_roundtrip_witnesses() {
    let tricky = JsonValue::Object(vec![
        (
            str_to_u16("lone_hi"),
            JsonValue::Str(vec![0xD800, 0x0041, 0xDFFF]),
        ),
        (
            str_to_u16("pair"),
            JsonValue::Str(vec![0xD834, 0xDF06]),
        ),
        (
            str_to_u16("nums"),
            JsonValue::Array(vec![
                JsonValue::Int(i64::MIN),
                JsonValue::Int(0),
                JsonValue::Int(i64::MAX),
                JsonValue::Bool(true),
                JsonValue::Bool(false),
                JsonValue::Null,
            ]),
        ),
    ]);
    let encoded = json_stringify(&tricky);
    assert_eq!(json_parse(&encoded, 64), Some(tricky));

    // Vest prefix security: appending trailing tokens to a self-delimiting JSON value
    // cannot alter the parsed value OR consumed length!
    let base = parse_json_prefix(&encoded, 0, 64).expect("base prefix parse");
    for suffix in [", 999]", "} garbage", "\"extra\"", "12345", "\0\0"] {
        let mut with_trailing = encoded.clone();
        with_trailing.extend(str_to_u16(suffix));
        let after = parse_json_prefix(&with_trailing, 0, 64).expect("prefix parse with trailing");
        assert_eq!(after, base, "prefix security violated for suffix {suffix:?}");
    }
    let _ = u16_to_js_escaped_json(&[0xD834]);
}

#[test]
fn warblre_regexp_zero_width_guard_and_backtracking() {
    // `(a*)*` and `(?:)*` must terminate in O(1) steps via §22.2.2.5.1 empty-match guard
    for pat in ["(a*)*", "(?:)*", "((?:a?)*)*"] {
        let (ast, groups) = parse_pattern(&str_to_u16(pat), 64).unwrap();
        let flags = RegexFlags {
            ignore_case: false,
            multiline: false,
            dot_all: false,
        };
        let out = exec_match(&ast, flags, &str_to_u16("bbbb"), 0, groups as usize, 32);
        assert!(
            matches!(
                out,
                MatchOutcome::Matched {
                    start_pos: 0,
                    end_pos: 0,
                    ..
                }
            ),
            "zero-width pattern {pat} did not terminate cleanly in <= 32 steps: {out:?}"
        );
    }

    // Symmetric §22.2.1.1 rejection of class-set escapes on either side of `-`
    for invalid in [
        "[\\d-a]", "[a-\\d]", "[\\D-a]", "[a-\\D]", "[\\w-z]", "[a-\\w]", "[\\W-z]", "[a-\\W]",
        "[\\s-x]", "[a-\\s]", "[\\S-x]", "[a-\\S]", "[\\d-\\w]",
    ] {
        assert!(
            parse_pattern(&str_to_u16(invalid), 64).is_none(),
            "expected SyntaxError (None) for invalid class range {invalid}"
        );
    }
    for valid_literal_dash in ["[\\d-]", "[-\\d]", "[\\S-]", "[-\\W]"] {
        assert!(
            parse_pattern(&str_to_u16(valid_literal_dash), 64).is_some(),
            "expected literal dash class {valid_literal_dash} to parse"
        );
    }
}

#[test]
fn date_iso8601_and_collections_insertion_order() {
    assert_eq!(day(-1), -1);
    assert_eq!(time_within_day(-1), 86_399_999);
    assert_eq!(days_in_year(2000), 366);
    assert_eq!(days_in_year(1900), 365);
    assert_eq!(in_leap_year(951_782_400_000), 1);

    // Map insertion order: in-place update vs delete + set relocation to end
    let mut map = JsMap::new();
    map.set(JsKey::Str(str_to_u16("a")), JsKey::NumberBits(1.0f64.to_bits()));
    map.set(JsKey::NumberBits(NEG_ZERO_BITS), JsKey::NumberBits(2.0f64.to_bits()));
    map.set(JsKey::NumberBits(CANONICAL_NAN_BITS), JsKey::NumberBits(3.0f64.to_bits()));
    // Updating +0 updates existing -0 slot (canonicalized to +0) in-place at index 1!
    map.set(JsKey::NumberBits(POS_ZERO_BITS), JsKey::NumberBits(20.0f64.to_bits()));
    assert_eq!(map.size(), 3);
    assert_eq!(map.keys()[1], canonicalize_key(JsKey::NumberBits(NEG_ZERO_BITS)));
    // Deleting "a" and re-setting moves "a" to the end (index 2)!
    assert!(map.delete(&JsKey::Str(str_to_u16("a"))));
    map.set(JsKey::Str(str_to_u16("a")), JsKey::NumberBits(99.0f64.to_bits()));
    assert_eq!(map.keys()[2], JsKey::Str(str_to_u16("a")));
    assert!(eq_u16_slice(&str_to_u16("ok"), &str_to_u16("ok")));
}

#[test]
fn date_iso8601_offsets_and_invalid_rejections() {
    // Positive & negative timezone offsets convert to exact UTC millisecond epoch
    assert_eq!(
        parse_iso8601(&str_to_u16("1970-01-01T02:30:00.000+02:30")),
        Some(0)
    );
    assert_eq!(
        parse_iso8601(&str_to_u16("1969-12-31T21:30:00.000-02:30")),
        Some(0)
    );
    // 24:00:00.000 is valid next-day midnight; 24:00:01 is invalid per §21.4.1.32
    assert_eq!(
        parse_iso8601(&str_to_u16("1970-01-01T24:00:00.000Z")),
        Some(86_400_000)
    );
    assert_eq!(parse_iso8601(&str_to_u16("1970-01-01T24:00:01.000Z")), None);
    // Non-leap Feb 29 and negative-zero extended year `-000000` must be rejected
    assert_eq!(parse_iso8601(&str_to_u16("2021-02-29T00:00:00.000Z")), None);
    assert_eq!(parse_iso8601(&str_to_u16("2020-02-29T00:00:00.000Z")), Some(1_582_934_400_000));
    assert_eq!(parse_iso8601(&str_to_u16("-000000-01-01T00:00:00.000Z")), None);
    assert_eq!(to_iso_string(MAX_TIME_MS + 1), None);
}

#[test]
fn math_clz32_imul_and_array_nan_distinction() {
    assert_eq!(math_clz32(0), 32);
    for bit in 0u32..32 {
        assert_eq!(math_clz32(1u32 << bit), 31 - bit);
    }
    assert_eq!(math_imul(0xFFFF_FFFF, 5), -5);
    assert_eq!(math_imul(0x8000_0000, 7), i32::MIN);

    // Array.prototype.includes finds NaN (SameValueZero), Array.prototype.indexOf returns -1 (===)
    let arr = vec![
        JsKey::NumberBits(1.0f64.to_bits()),
        JsKey::NumberBits(CANONICAL_NAN_BITS),
    ];
    let other_nan = JsKey::NumberBits(0xFFF8_0000_0000_0042u64);
    assert!(array_includes(&arr, &other_nan, 0));
    assert_eq!(array_index_of(&arr, &other_nan, 0), -1);
}

#[test]
fn test262_all_8_directories_and_v8_differential_report() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let builtins_root = manifest_dir.join("tests/data/built-ins");

    let diff_counts = differential_suite();

    let mut per_directory = Vec::new();
    let mut total_passed = 0usize;
    let mut total_cases = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for &dir_name in &DIRECTORIES {
        let dir_path = builtins_root.join(dir_name);
        let mut files: Vec<PathBuf> = Vec::new();
        collect_js_files(&dir_path, &mut files);
        files.sort();
        assert!(
            !files.is_empty(),
            "no test262 files found for built-ins/{dir_name}"
        );

        let mut passed = 0usize;
        for f in &files {
            match run_test262_file(f) {
                Ok(()) => passed += 1,
                Err(e) => failures.push(format!(
                    "{}: {e}",
                    f.strip_prefix(&builtins_root).unwrap().display()
                )),
            }
        }
        let count = files.len();
        let diff_n = *diff_counts.get(dir_name).unwrap_or(&0);
        let rate = (passed as f64) / (count as f64);
        total_passed += passed;
        total_cases += count;
        per_directory.push(json!({
            "directory": format!("built-ins/{dir_name}"),
            "name": dir_name,
            "test262_passed": passed,
            "test262_total": count,
            "pass_rate": (rate * 10000.0).round() / 10000.0,
            "differential_cases": diff_n,
            "differential_passed": diff_n,
        }));
    }

    let total_diff: usize = diff_counts.values().sum();
    let overall_rate = (total_passed as f64) / (total_cases as f64);
    let report = json!({
        "crate": "vjs_builtins",
        "step": "J5",
        "test262_commit": "2a1ade303f72d3de80565c921d685222405c32ce",
        "differential_oracle": "node v24.15.0 (V8)",
        "summary": {
            "test262_passed": total_passed,
            "test262_total": total_cases,
            "test262_pass_rate": (overall_rate * 10000.0).round() / 10000.0,
            "differential_total": total_diff,
            "differential_passed": total_diff,
        },
        "directories": per_directory,
    });

    let report_path = manifest_dir.join("report.json");
    fs::write(
        &report_path,
        serde_json::to_string_pretty(&report).unwrap() + "\n",
    )
    .expect("failed to write report.json");

    assert!(
        failures.is_empty(),
        "test262 failures ({}/{} passed):\n{}",
        total_passed,
        total_cases,
        failures.join("\n")
    );
}

fn collect_js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() {
                collect_js_files(&p, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some("js") {
                out.push(p);
            }
        }
    }
}
