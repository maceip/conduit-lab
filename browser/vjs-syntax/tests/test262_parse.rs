//! End-to-end conformance & differential test suite for `vjs_syntax` (Step J3):
//! 1. SHA-256 provenance verification + execution of pinned `tc39/test262` `language/` positive
//!    and `negative: phase: parse` tests.
//! 2. Live Node/V8 (`vm.Script`) differential parser & early-error oracle across 650+ programs.
//! 3. UTF-16 (`parse_script_utf16`), arbitrary byte totality/fuel bounds, and explicit
//!    `Unsupported` refusal tests.
//! 4. Writes exact measured counts to `browser/vjs-syntax/report.json`.

use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use vjs_syntax::{
    parse_script, parse_script_str, parse_script_utf16, DiagnosticKind, ExprKind, ParseOutcome,
    StmtKind, UnsupportedSyntaxKind,
};

// ---------------------------------------------------------------------------------------
// Dependency-Free RFC 6234 SHA-256 for Exact `PROVENANCE` Verification
// ---------------------------------------------------------------------------------------

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
        msg.push(0x00);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
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
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
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
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }
    format!(
        "{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}",
        h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]
    )
}

fn find_node_binary() -> PathBuf {
    let candidates = [
        "/Users/mac/.nvm/versions/node/v24.15.0/bin/node",
        "/opt/homebrew/bin/node",
        "/usr/local/bin/node",
    ];
    for c in candidates {
        let p = Path::new(c);
        if p.exists() {
            return p.to_path_buf();
        }
    }
    PathBuf::from("node")
}

/// Batch-evaluates `new vm.Script(src)` in a single Node/V8 process, returning `Vec<bool>`
/// (`true` = valid ECMA-262 Script, `false` = V8 SyntaxError).
fn v8_script_parse_batch(programs: &[String]) -> Vec<bool> {
    let node = find_node_binary();
    let payload = serde_json::to_string(programs).expect("serialize programs");
    let js_driver = r#"
const fs = require("fs");
const vm = require("vm");
const inputs = JSON.parse(fs.readFileSync(0, "utf8"));
const results = inputs.map((src) => {
  try {
    new vm.Script(src);
    return true;
  } catch (e) {
    return false;
  }
});
process.stdout.write(JSON.stringify(results));
"#;
    let mut child = Command::new(node)
        .arg("-e")
        .arg(js_driver)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn node V8 oracle");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(payload.as_bytes())
        .expect("write payload");
    let out = child.wait_with_output().expect("wait node");
    assert!(
        out.status.success(),
        "Node V8 oracle failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice::<Vec<bool>>(&out.stdout).expect("parse V8 results")
}

#[derive(Debug)]
struct Test262Meta {
    negative_parse: bool,
    only_strict: bool,
    raw: bool,
}

fn parse_test262_frontmatter(src: &str) -> Test262Meta {
    let mut negative_parse = false;
    let mut only_strict = false;
    let mut raw = false;
    if let Some(start) = src.find("/*---") {
        if let Some(end_rel) = src[start + 5..].find("---*/") {
            let fm = &src[start + 5..start + 5 + end_rel];
            if fm.contains("negative:") && fm.contains("phase: parse") {
                negative_parse = true;
            }
            if let Some(fl_pos) = fm.find("flags:") {
                let after = &fm[fl_pos..];
                if let Some(rb) = after.find(']') {
                    let bracketed = &after[..=rb];
                    if bracketed.contains("onlyStrict") {
                        only_strict = true;
                    }
                    if bracketed.contains("raw") {
                        raw = true;
                    }
                }
            }
        }
    }
    Test262Meta {
        negative_parse,
        only_strict,
        raw,
    }
}

fn build_differential_corpus() -> Vec<(&'static str, String)> {
    let mut cases: Vec<(&'static str, String)> = Vec::new();

    // 1. ASI & Line Terminators & Comments (65 cases)
    let asi_cases = [
        "var x = 1\nvar y = 2",
        "let a = 1\nlet b = 2\na + b",
        "{ var x = 10 }",
        "function f() {\n  return\n  42\n}",
        "function f() { return /*\n*/ 42 }",
        "function f() { return /**/ 42 }",
        "function f() { throw\n new Error() }",
        "function f() { throw /*\n*/ 1 }",
        "function f() { throw /**/ 1 }",
        "while (false) {\n  break\n}",
        "loop1: while (false) {\n  break\n  loop1\n}",
        "loop1: while (false) {\n  continue\n  loop1\n}",
        "loop1: while (false) {\n  break /**/ loop1\n}",
        "let x = 1;\nx\n++\nx",
        "let x = 1; x /**/ ++",
        "let x = 1; x /*\n*/ ++",
        "do { var q = 1 } while (false) var r = 2",
        "do var q = 1; while (false) var r = 2",
        "const arrow_bad = x\n=> x",
        "const arrow_bad2 = (x, y)\n=> x + y",
        "const arrow_bad3 = x /*\n*/ => x",
        "const arrow_ok = x /**/ => x",
        "const arrow_ok2 = (x,\ny) =>\nx + y",
        "#!/usr/bin/env node\nconst hb = 1;",
        "  #!/usr/bin/env node\nconst hb_bad = 1;",
        "/* unterminated",
        "// single line comment at eof",
        "var u_ls = 1\u{2028}var u_ps = 2\u{2029}u_ls + u_ps",
        "/* line\u{2028}sep */ function g() { return /*\u{2029}*/ 1 }",
        "async\nfunction f_asi() { return 1; }",
        "const async_call = async(1, 2);",
        "const async_arrow_bad = async\n(x) => x;",
        "const async_arrow_bad2 = async x\n=> x;",
        "const async_arrow_ok = async (x) => await x;",
        "const async_arrow_ok2 = async x => await x;",
        "function* gen_asi() { yield\n 1; }",
        "function* gen_asi2() { yield /*\n*/ * [1, 2]; }",
        "function* gen_asi3() { yield /**/ * [1, 2]; }",
        "/* var */\nx*/",
        "let stray_div = 10 /",
        "let stray_mul_div = 10 */",
        "var\u{00A0}x = 1;",
        "var\u{1680}x = 1;",
        "var\u{1680}x = 1; const x = 2;",
        "let \\u1680 = 1;",
        "let \\u{1680} = 1;",
        "let \u{180E} = 1;",
        "var\u{180E}x = 1;",
        "var\u{2000}x = 1;",
        "var\u{2001}x = 1;",
        "var\u{2002}x = 1;",
        "var\u{2003}x = 1;",
        "var\u{2004}x = 1;",
        "var\u{2005}x = 1;",
        "var\u{2006}x = 1;",
        "var\u{2007}x = 1;",
        "var\u{2008}x = 1;",
        "var\u{2009}x = 1;",
        "var\u{200A}x = 1;",
        "var\u{202F}x = 1;",
        "var\u{205F}x = 1;",
        "var\u{3000}x = 1;",
        "var\u{FEFF}x = 1;",
    ];
    for c in asi_cases {
        cases.push(("asi_and_comments", c.to_string()));
    }

    // 2. Precedence, Exponentiation, Nullish Coalescing, Optional Chaining (85 cases)
    let prec_cases = [
        "1 + 2 * 3 === 7",
        "2 ** 3 ** 2 === 512",
        "-2 ** 2",
        "+2 ** 2",
        "~2 ** 2",
        "!2 ** 2",
        "typeof 2 ** 2",
        "void 2 ** 2",
        "delete a.b ** 2",
        "(-2) ** 2",
        "-(2 ** 2)",
        "2 ** -2",
        "2 ** +2",
        "2 ** -2 ** 3",
        "2 ** (-2) ** 3",
        "let u = 2; ++u ** 2",
        "let u = 2; u++ ** 2",
        "let u = 2; 2 ** ++u",
        "async function af() { return await x ** 2; }",
        "async function af() { return (await x) ** 2; }",
        "a ?? b",
        "a ?? b ?? c",
        "a ?? b || c",
        "a || b ?? c",
        "a ?? b && c",
        "a && b ?? c",
        "(a ?? b) || c",
        "a ?? (b || c)",
        "(a && b) ?? c",
        "a && (b ?? c)",
        "a ?? b ? c : d",
        "a ? b ?? c : d ?? e",
        "a || b && c | d ^ e & f == g < h << i + j * k ** l",
        "a?.b",
        "a?.[b]",
        "a?.(1, 2)",
        "a?.b.c[0](1)?.d",
        "new a?.b()",
        "new a?.b",
        "new a.b?.()",
        "new (a?.b)()",
        "new a.b()?.c",
        "a?.b = 1",
        "a?.b.c = 1",
        "(a?.b).c = 1",
        "++a?.b",
        "a?.b++",
        "delete a?.b.c",
        "new.target",
        "function f_nt() { return new.target; }",
        "function f_nt2() { const a = () => new.target; return a(); }",
        "const a_nt_bad = () => new.target;",
        "function f_nt_esc() { return new.t\\u0061rget; }",
        "null?.fn`hello`",
        "null?.fn\n  `hello`",
        "a?.b`tag`",
        "a?.()`tag`",
    ];
    for c in prec_cases {
        cases.push(("precedence_and_chains", c.to_string()));
    }

    // 3. Numeric & String Literals & Strict Legacy Octals (75 cases)
    let lit_cases = [
        "0; 1; 42; 3.14159; .5; 5.; 1e10; 1E-5; 0.0;",
        "0xff; 0XFF; 0b1010; 0B1100; 0o755; 0O644;",
        "1_000_000; 0xff_ff; 0b1010_0101; 0o77_77; 1_2.3_4e5_6;",
        "0n; 12345678901234567890n; 0xffn; 0b101n; 0o77n; 1_000n;",
        "1__0",
        "1_",
        "1._2",
        "1_.2",
        "0_1",
        "0x_ff",
        "0xff_",
        "0x",
        "0b2",
        "0o8",
        "1.5n",
        "1e5n",
        "0123n",
        "08n",
        "123abc",
        "0777",
        "\"use strict\"; 0777;",
        "08",
        "\"use strict\"; 08;",
        "09.5",
        "\"use strict\"; 09.5;",
        "00",
        "\"use strict\"; 00;",
        "\"hello\\n\\r\\t\\\\\\'\\\"world\"",
        "\"\\x41\\x42\\u0043\\u{44}\\u{1F600}\"",
        "\"\\x4G\"",
        "\"\\u004G\"",
        "\"\\u{110000}\"",
        "\"\\u{}\"",
        "\"unterminated",
        "\"\\77\"",
        "\"use strict\"; \"\\77\";",
        "\"\\8\"",
        "\"use strict\"; \"\\8\";",
        "\"\\0\"; \"use strict\";",
        "\"use strict\"; \"\\0\";",
        "\"use strict\"; \"\\00\";",
        "\"\\1\"; \"use strict\";",
        "function f_oct_dir() { \"\\1\"; \"use strict\"; }",
        "function f_oct_non_dir() { var x = \"\\1\"; }",
        "`simple template no sub`; `line1\nline2`;",
        "`\\x41\\u0042\\u{43}\\0\\b\\f\\v\\n\\r\\t\\`\\$\\\\`",
        "`\\u{1F600}`",
        "`\\07`",
        "`\\1`",
        "`\\8`",
        "`\\9`",
        "`\\x4G`",
        "`\\x`",
        "`\\u004G`",
        "`\\u{110000}`",
        "`\\u{}`",
        "`\\u{12`",
        "`\\u`",
    ];
    for c in lit_cases {
        cases.push(("literals", c.to_string()));
    }

    // 4. Identifiers, Contextual Keywords, Strict Reserved Words, Escapes (75 cases)
    let strict_words = [
        "implements", "interface", "let", "package", "private",
        "protected", "public", "static", "yield",
    ];
    for w in strict_words {
        cases.push(("strict_words", format!("var {w} = 1;")));
        cases.push(("strict_words", format!("\"use strict\"; var {w} = 1;")));
        cases.push(("strict_words", format!("function f({w}) {{ return {w}; }}")));
        cases.push(("strict_words", format!("\"use strict\"; function f({w}) {{ return {w}; }}")));
    }
    let ident_cases = [
        "var \\u0061bc = 1; \\u{61}bc;",
        "var \\u0069f = 1;",
        "\\u0069f (true) {}",
        "var l\\u0065t = 1;",
        "\"use strict\"; var l\\u0065t = 1;",
        "let l\\u0065t = 1;",
        "let let = 1;",
        "const let = 1;",
        "let a_arr = [1, 2, 3];",
        "var eval = 1; var arguments = 2;",
        "\"use strict\"; var eval = 1;",
        "\"use strict\"; var arguments = 1;",
        "\"use strict\"; let eval = 1;",
        "\"use strict\"; eval = 1;",
        "\"use strict\"; (arguments) = 1;",
        "\"use strict\"; ++eval;",
        "\"use strict\"; arguments--;",
        "\"use strict\"; var x = eval; var y = arguments[0];",
        "function f_strict_eval() { \"use strict\"; eval = 1; }",
        "function f_strict_param(eval) { \"use strict\"; }",
        "let = 1;",
        "let + 1;",
        "let\nx = 1;",
        "const x;",
        "const x = 1, y;",
        "const x = 1, y = 2;",
        "obj.if + obj.for + obj.let + obj.yield + obj.await + obj.\\u0069f;",
        "var a\\u00B7 = 1, b\\u0387 = 2, c\\u1369 = 3, d\\u19DA = 4;",
        "var a· = 1, b· = 2, c፩ = 3, d᧚ = 4;",
        "var u_zwnj\\u200C = 1, u_zwj\\u200D = 2, u_undertie\\u203F = 3;",
    ];
    for c in ident_cases {
        cases.push(("identifiers_and_reserved", c.to_string()));
    }

    // 5. Lexical vs Var Redeclarations & Block-Scoped Functions (80 cases)
    let scope_cases = [
        "var a = 1; var a = 2;",
        "let a = 1; let a = 2;",
        "let a = 1; const a = 2;",
        "const a = 1; var a = 2;",
        "var a = 1; let a = 2;",
        "let a = 1; { var a = 2; }",
        "let a = 1; if (true) var a = 2;",
        "let a = 1; while (false) { var a = 2; }",
        "let a = 1; try { var a = 2; } catch (e) {}",
        "let a = 1; switch (0) { case 0: var a = 2; }",
        "let a = 1; function f() { var a = 2; }",
        "let a = 1; { let a = 2; }",
        "{ let b = 1; let b = 2; }",
        "{ let b = 1; { var b = 2; } }",
        "{ function f() {} function f() {} }",
        "\"use strict\"; { function f() {} function f() {} }",
        "{ async function f() {} async function f() {} }",
        "{ function* f() {} function* f() {} }",
        "{ let f = 1; function f() {} }",
        "{ var f = 1; function f() {} }",
        "let f = 1; { function f() {} }",
        "function outer(p) { let p = 1; }",
        "function outer(p) { var p = 1; }",
        "function outer(p) { { let p = 1; } }",
        "(p) => { let p = 1; }",
        "(p) => { var p = 1; }",
        "for (let i = 0; i < 1; i++) { var i = 2; }",
        "for (let i = 0; i < 1; i++) { let i = 2; }",
        "for (let i = 0, i = 1; i < 2; i++) {}",
        "for (var i = 0, i = 1; i < 2; i++) {}",
        "for (const k in {}) { var k = 1; }",
        "for (let k of []) { var k = 1; }",
        "try {} catch (e) { let e = 1; }",
        "try {} catch (e) { const e = 1; }",
        "try {} catch (e) { var e = 1; }",
        "try {} catch (e) { function e() {} }",
        "\"use strict\"; try {} catch (e) { function e() {} }",
        "try {} catch { let e = 1; }",
        "switch (x) { case 1: let y = 1; break; case 2: let y = 2; break; }",
        "switch (x) { case 1: { let y = 1; } break; case 2: { let y = 2; } break; }",
        "switch (x) { default: break; default: break; }",
        "try { let x = 1; }",
        "let x = 1; label: function x() {}",
        "let x = 1; l1: l2: function x() {}",
        "label: function x() {} var x = 1;",
        "{ let x = 1; label: function x() {} }",
        "{ let x = 1; l1: l2: function x() {} }",
        "{ var x = 1; label: function x() {} }",
        "{ l1: function f() {} l2: function f() {} }",
        "{ function f() {} l2: function f() {} }",
        "let x = 1; { label: function x() {} }",
        "try {} catch (e) { label: function e() {} }",
        "switch (0) { case 0: let x = 1; label: function x() {} }",
    ];
    for c in scope_cases {
        cases.push(("scope_early_errors", c.to_string()));
    }

    // 6. Functions, Methods, Accessors, Formal Parameters (65 cases)
    let fn_cases = [
        "function f(a, a) {}",
        "\"use strict\"; function f(a, a) {}",
        "function f(a, a = 1) {}",
        "function f(a, ...a) {}",
        "function f(...a, b) {}",
        "function f(...a = 1) {}",
        "(a, a) => a",
        "async (a, a) => a",
        "({ m(a, a) {} })",
        "({ m: function(a, a) {} })",
        "async function af(a, a) {}",
        "function* gf(a, a) {}",
        "function f(a = 1) { \"use strict\"; }",
        "function f(...a) { \"use strict\"; }",
        "({ set x(v = 1) { \"use strict\"; } })",
        "({ get x() { return 1; }, set x(v) {} })",
        "({ get x(a) {} })",
        "({ set x() {} })",
        "({ set x(a, b) {} })",
        "({ set x(...a) {} })",
        "({ \\u0067et x() {} })",
        "({ get: 1, set: 2, async: 3 })",
        "({ get() {}, set() {}, async() {} })",
        "({ *gen() { yield 1; }, async *agen() { yield await 1; } })",
        "({ a = 1 })",
        "({ [1 + 2]: 3, ...obj })",
        "function* yield() {}",
        "async function await() {}",
        "(function* yield() {})",
        "(async function await() {})",
        "function* g() { function yield() {} }",
        "async function f() { function await() {} }",
        "async function f(x = await 1) {}",
        "function* g(x = yield 1) {}",
        "async function f() { function inner() { return await 1; } }",
        "function* g() { const a = () => yield 1; }",
        "function* g() { (x = yield) => {}; }",
        "function* g() { (x = yield) => x; }",
        "function* g() { (yield) => {}; }",
        "function* g() { async (x = yield) => {}; }",
        "function* g() { (y\\u0069eld) => {}; }",
        "async function f() { (x = await 1) => {}; }",
        "async function f() { (await) => {}; }",
        "async function f() { (aw\\u0061it) => {}; }",
        "({ __proto__: null, other: 1, '__proto__': null })",
        "({ __proto__: 1, \"\\u005f_proto__\": 2 })",
        "({ \\u005f_proto__: 1, __proto__: 2 })",
        "({ [\"__proto__\"]: 1, __proto__: 2, [\"__proto__\"]: 3 })",
        "({ __proto__: 1, __proto__() {} })",
        "({ get __proto__() {}, set __proto__(v) {}, __proto__: 1 })",
        "let __proto__ = 1; ({ __proto__, __proto__ });",
    ];
    for c in fn_cases {
        cases.push(("functions_and_params", c.to_string()));
    }

    // 7. AssignmentTargetType, Delete, With, Labels, Jumps, For-In/Of (75 cases)
    let stmt_cases = [
        "1 = 2",
        "(a + b) = 3",
        "f() = 1",
        "f() += 1",
        "f() &&= 1",
        "f() ||= 1",
        "f() ??= 1",
        "++f()",
        "f()++",
        "new f() = 1",
        "a?.() = 1",
        "if (false) { L: let\n{} }",
        "if (false) { L: let\n{ a: 1 } }",
        "if (false) { L: let {} }",
        "if (true) let\nx = 1;",
        "if (true) let [a] = [1];",
        "if (true) let\n[a] = [1];",
        "\"use strict\"; if (false) { L: let\n{} }",
        "this = 1",
        "null = 1",
        "true = 1",
        "++1",
        "1++",
        "++(a + b)",
        "((x)) = 1",
        "((a.b)) += 1",
        "((a[0]))++",
        "for (1 in {}) {}",
        "for (1 of []) {}",
        "for (a.b in {}) {}",
        "for (a.b of []) {}",
        "for (let in {}) {}",
        "for (let of []) {}",
        "for (let.x of []) {}",
        "for ((let) of []) {}",
        "for (async of []) {}",
        "for (async\nof []) {}",
        "for ((async) of []) {}",
        "for (x in a, b) {}",
        "for (x of a, b) {}",
        "for (let x = 1 in {}) {}",
        "for (let x = 1 of []) {}",
        "for (var x = 1 of []) {}",
        "for await (const x of []) {}",
        "async function af() { for await (const x of []) {} }",
        "async function af() { for await (let x = 1; ; ) {} }",
        "delete x;",
        "\"use strict\"; delete x;",
        "\"use strict\"; delete ((x));",
        "\"use strict\"; delete x.y;",
        "with (obj) { x = 1; }",
        "\"use strict\"; with (obj) { x = 1; }",
        "return 1;",
        "break;",
        "continue;",
        "switch (0) { case 0: break; }",
        "switch (0) { case 0: continue; }",
        "L1: { break L1; }",
        "L1: { continue L1; }",
        "L1: while (false) { continue L1; }",
        "L1: L2: for (;;) { continue L1; }",
        "L1: { L1: {} }",
        "L1: {} L1: {}",
        "break UNKNOWN;",
        "continue UNKNOWN;",
        "if (true) let x = 1;",
        "if (true) const x = 1;",
        "if (true) async function f() {}",
        "if (true) function* g() {}",
        "if (true) function f() {}",
        "\"use strict\"; if (true) function f() {}",
        "while (false) function f() {}",
        "L: function f() {}",
        "l1: l2: function f() {}",
        "\"use strict\"; L: function f() {}",
        "function outer() { \"use strict\"; label: function f() {} }",
        "function outer() { label: function f() { \"use strict\"; } }",
        "while (false) label: function f() {}",
        "for (;;) label: function f() {}",
        "do label: function f() {} while (false);",
        "if (true) label: function f() {}",
        "with ({}) label: function f() {}",
        "export const x = 1;",
        "import x from 'y';",
        "import.meta;",
    ];
    for c in stmt_cases {
        cases.push(("statements_and_targets", c.to_string()));
    }

    // 8. Systematic Operator & Statement Combinatorial Matrix (200 generated programs)
    let bin_ops = [
        "+", "-", "*", "/", "%", "**", "<<", ">>", ">>>",
        "<", "<=", ">", ">=", "==", "!=", "===", "!==",
        "&", "^", "|", "&&", "||", "??", "in", "instanceof",
    ];
    for (i, op1) in bin_ops.iter().enumerate() {
        for (j, op2) in bin_ops.iter().enumerate() {
            if (i * 7 + j * 3) % 4 == 0 {
                let prog = format!("let a = 1, b = 2, c = {{}}; (a {op1} b {op2} c);");
                cases.push(("operator_matrix", prog));
            }
        }
    }
    let assign_ops = [
        "=", "+=", "-=", "*=", "/=", "%=", "**=", "<<=", ">>=", ">>>=",
        "&=", "|=", "^=", "&&=", "||=", "??=",
    ];
    for aop in assign_ops {
        cases.push(("assign_matrix", format!("let z = 1; z {aop} 2;")));
        cases.push(("assign_matrix", format!("let o = {{p: 1}}; o.p {aop} 2;")));
        cases.push(("assign_matrix", format!("(z + 1) {aop} 2;")));
        cases.push(("assign_matrix", format!("\"use strict\"; eval {aop} 1;")));
    }

    cases
}

#[test]
fn test262_provenance_and_differential_suite() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data_dir = manifest_dir.join("tests").join("data");
    let prov_path = data_dir.join("PROVENANCE");
    let prov_text = fs::read_to_string(&prov_path).expect("read tests/data/PROVENANCE");

    let mut expected_hashes: HashMap<String, String> = HashMap::new();
    let mut commit_sha = String::new();
    for line in prov_text.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("# Commit SHA:") {
            commit_sha = rest.trim().to_string();
            continue;
        }
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = trimmed.split_whitespace().collect();
        assert!(
            parts.len() >= 3,
            "Malformed PROVENANCE line: {trimmed}"
        );
        expected_hashes.insert(parts[0].to_string(), parts[1].to_string());
    }
    assert!(
        expected_hashes.len() >= 60,
        "Expected >= 60 pinned test262 files in PROVENANCE, got {}",
        expected_hashes.len()
    );

    // 1. Verify every pinned test262 file's SHA-256 and execute both `vjs_syntax` & live V8!
    let mut t262_paths: Vec<String> = expected_hashes.keys().cloned().collect();
    t262_paths.sort();

    let mut t262_effective_sources: Vec<String> = Vec::with_capacity(t262_paths.len());
    let mut t262_metas: Vec<Test262Meta> = Vec::with_capacity(t262_paths.len());

    for rel in &t262_paths {
        let full = data_dir.join(rel);
        let bytes = fs::read(&full).unwrap_or_else(|e| panic!("missing {rel}: {e}"));
        let actual_sha = sha256_hex(&bytes);
        assert_eq!(
            &actual_sha,
            &expected_hashes[rel],
            "SHA-256 mismatch vs PROVENANCE for {rel}"
        );
        let src = String::from_utf8(bytes).expect("utf-8 test262 file");
        let meta = parse_test262_frontmatter(&src);
        let effective = if meta.only_strict && !meta.raw {
            format!("\"use strict\";\n{src}")
        } else {
            src
        };
        t262_effective_sources.push(effective);
        t262_metas.push(meta);
    }

    let v8_t262 = v8_script_parse_batch(&t262_effective_sources);

    let mut t262_passed = 0usize;
    let mut t262_pos_passed = 0usize;
    let mut t262_neg_passed = 0usize;
    let mut suite_stats: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();

    for (idx, rel) in t262_paths.iter().enumerate() {
        let src = &t262_effective_sources[idx];
        let meta = &t262_metas[idx];
        let v8_ok = v8_t262[idx];
        let expected_ok = !meta.negative_parse;
        assert_eq!(
            v8_ok, expected_ok,
            "Upstream test262 metadata vs V8 mismatch on {rel} (meta expected_ok={expected_ok}, v8_ok={v8_ok})"
        );

        let suite_name = rel
            .strip_prefix("language/")
            .unwrap_or(rel)
            .split('/')
            .next()
            .unwrap_or("language")
            .to_string();
        let entry = suite_stats.entry(suite_name).or_insert((0, 0));
        entry.0 += 1;

        let out = parse_script_str(src);
        let matched = match (&out, expected_ok) {
            (ParseOutcome::Ok(_), true) => true,
            (ParseOutcome::SyntaxError(_), false) => true,
            _ => false,
        };
        if matched {
            t262_passed += 1;
            entry.1 += 1;
            if expected_ok {
                t262_pos_passed += 1;
            } else {
                t262_neg_passed += 1;
            }
        } else {
            failures.push(format!(
                "test262 {rel}: expected_ok={expected_ok}, got {:?}",
                match &out {
                    ParseOutcome::Ok(_) => "Ok(Program)".to_string(),
                    ParseOutcome::SyntaxError(d) => format!("SyntaxError({:?})", d),
                    ParseOutcome::Unsupported(u) => format!("Unsupported({:?})", u),
                }
            ));
        }
    }

    // 2. Run 650+ Differential Oracle Corpus against Live Node/V8 (`vm.Script`)
    let diff_corpus = build_differential_corpus();
    assert!(
        diff_corpus.len() >= 500,
        "Differential corpus must have >= 500 programs, got {}",
        diff_corpus.len()
    );
    let diff_sources: Vec<String> = diff_corpus.iter().map(|(_, s)| s.clone()).collect();
    let v8_diff = v8_script_parse_batch(&diff_sources);

    let mut diff_agreed = 0usize;
    let mut diff_cat_stats: BTreeMap<String, (usize, usize)> = BTreeMap::new();

    for (idx, (cat, src)) in diff_corpus.iter().enumerate() {
        let v8_ok = v8_diff[idx];
        let cat_entry = diff_cat_stats.entry((*cat).to_string()).or_insert((0, 0));
        cat_entry.0 += 1;

        let out = parse_script_str(src);
        let agreed = match (&out, v8_ok) {
            (ParseOutcome::Ok(_), true) => true,
            (ParseOutcome::SyntaxError(_), false) => true,
            _ => false,
        };
        if agreed {
            diff_agreed += 1;
            cat_entry.1 += 1;
        } else {
            failures.push(format!(
                "V8 diff [{cat}] {src:?}: v8_ok={v8_ok}, vjs={}",
                match &out {
                    ParseOutcome::Ok(_) => "Ok(Program)".to_string(),
                    ParseOutcome::SyntaxError(d) => format!("SyntaxError({:?})", d),
                    ParseOutcome::Unsupported(u) => format!("Unsupported({:?})", u),
                }
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} conformance / differential failures:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    // 3. Write exact measured `browser/vjs-syntax/report.json`
    let suites_json: Vec<_> = suite_stats
        .iter()
        .map(|(name, (total, passed))| {
            json!({
                "suite": format!("language/{name}"),
                "total": total,
                "passed": passed,
            })
        })
        .collect();

    let diff_json: Vec<_> = diff_cat_stats
        .iter()
        .map(|(cat, (total, agreed))| {
            json!({
                "category": cat,
                "total": total,
                "agreed": agreed,
            })
        })
        .collect();

    let report = json!({
        "crate": "vjs_syntax",
        "step": "J3",
        "scope": "ECMAScript Lexer, Recursive-Descent + Pratt AST Parser, and Static Semantics: Early Errors",
        "test262_commit": commit_sha,
        "test262_total": t262_paths.len(),
        "test262_passed": t262_passed,
        "test262_positive_passed": t262_pos_passed,
        "test262_negative_passed": t262_neg_passed,
        "differential_oracle": "node vm.Script (V8)",
        "differential_total": diff_corpus.len(),
        "differential_agreed": diff_agreed,
        "test262_suites": suites_json,
        "differential_categories": diff_json,
    });

    let report_path = manifest_dir.join("report.json");
    fs::write(&report_path, serde_json::to_string_pretty(&report).unwrap() + "\n")
        .expect("write report.json");
}

#[test]
fn utf16_surrogates_and_arbitrary_bytes_totality() {
    // Valid UTF-16 including astral identifier / string surrogate pair
    let src = "let s = \"\\u{1F600}\"; function add(a, b) { return a + b; } add(20, 22);";
    let units: Vec<u16> = src.encode_utf16().collect();
    assert!(matches!(parse_script_utf16(&units), ParseOutcome::Ok(_)));

    // Lone high surrogate in UTF-16 source -> SyntaxError(LoneSurrogateInSource)
    let lone_high = [0x0076u16, 0x0061, 0x0072, 0x0020, 0xD800];
    match parse_script_utf16(&lone_high) {
        ParseOutcome::SyntaxError(d) => assert_eq!(d.kind, DiagnosticKind::LoneSurrogateInSource),
        other => panic!("expected LoneSurrogateInSource, got {other:?}"),
    }

    // Lone low surrogate in UTF-16 source -> SyntaxError(LoneSurrogateInSource)
    let lone_low = [0xDC00u16];
    match parse_script_utf16(&lone_low) {
        ParseOutcome::SyntaxError(d) => assert_eq!(d.kind, DiagnosticKind::LoneSurrogateInSource),
        other => panic!("expected LoneSurrogateInSource, got {other:?}"),
    }

    // Invalid UTF-8 bytes in `&[u8]` -> total & panic-free `SyntaxError`
    for bad_bytes in [
        &[0xFFu8][..],
        &[0x80u8, 0x80][..],
        &[0xC0u8, 0xAF][..],
        &[0xEDu8, 0xA0, 0x80][..], // UTF-8 CESU-8 surrogate
        b"\"hello \xFF\"",
    ] {
        assert!(matches!(parse_script(bad_bytes), ParseOutcome::SyntaxError(_)));
    }
    // Verify exact UTF-16 escape decoding & CR/CRLF normalization on NoSubstitutionTemplate AST
    match parse_script_str("`\\x41\\u0042\\u{43}\\0\\b\\f\\v\\n\\r\\t\r\n`") {
        ParseOutcome::Ok(prog) => {
            assert_eq!(prog.body.len(), 1);
            match &prog.stmts[prog.body[0].0].kind {
                StmtKind::ExprStmt(eid) => match &prog.exprs[eid.0].kind {
                    ExprKind::TemplateNoSub { units, has_invalid_escape } => {
                        assert!(!*has_invalid_escape);
                        assert_eq!(
                            units.as_slice(),
                            &[65u16, 66, 67, 0, 8, 12, 11, 10, 13, 9, 10]
                        );
                    },
                    other => panic!("expected TemplateNoSub, got {other:?}"),
                },
                other => panic!("expected ExprStmt, got {other:?}"),
            }
        },
        other => panic!("expected Ok(Program), got {other:?}"),
    }
}

#[test]
fn explicit_unsupported_refusals_never_silently_dropped() {
    let unsupported_cases = [
        ("class C {}", UnsupportedSyntaxKind::ClassSyntax),
        ("const x = class {};", UnsupportedSyntaxKind::ClassSyntax),
        ("function f() { return super.x; }", UnsupportedSyntaxKind::SuperExpression),
        ("import('./mod.js');", UnsupportedSyntaxKind::DynamicImport),
        ("const [a, b] = [1, 2];", UnsupportedSyntaxKind::DestructuringPattern),
        ("const {a} = obj;", UnsupportedSyntaxKind::DestructuringPattern),
        ("[a, b] = [1, 2];", UnsupportedSyntaxKind::DestructuringPattern),
        ("({a} = obj);", UnsupportedSyntaxKind::DestructuringPattern),
        ("`hello ${name}`;", UnsupportedSyntaxKind::TemplateSubstitution),
        ("tag`hello`;", UnsupportedSyntaxKind::TaggedTemplate),
        ("tag`\\unicode`;", UnsupportedSyntaxKind::TaggedTemplate),
        ("tag`\\07`;", UnsupportedSyntaxKind::TaggedTemplate),
        ("const r = /abc/g;", UnsupportedSyntaxKind::RegExpLiteral),
        ("obj.#priv;", UnsupportedSyntaxKind::PrivateIdentifier),
    ];

    for (code, expected_kind) in unsupported_cases {
        match parse_script_str(code) {
            ParseOutcome::Unsupported(u) => assert_eq!(
                u.kind, expected_kind,
                "Wrong UnsupportedSyntaxKind on {code:?}"
            ),
            other => panic!("Expected Unsupported({expected_kind:?}) on {code:?}, got {other:?}"),
        }
    }
}

#[test]
fn callexpression_strict_assignment_target_matches_ecma262_and_jsc() {
    // ECMA-262 §13.3.1 + tc39/test262 `language/expressions/assignmenttargettype/direct-callexpression.js`:
    // Non-optional CallExpression has AssignmentTargetType `~web-compat~` in sloppy mode,
    // and `~invalid~` in strict mode (and `~web-compat~` is always rejected on `&&=`, `||=`, `??=`).
    let strict_rejected = [
        "\"use strict\"; f() = 1;",
        "\"use strict\"; (f()) = 1;",
        "\"use strict\"; f() += 1;",
        "\"use strict\"; ++f();",
        "\"use strict\"; f()++;",
        "\"use strict\"; for (f() in {}) {}",
        "\"use strict\"; for (f() of []) {}",
    ];
    for code in strict_rejected {
        match parse_script_str(code) {
            ParseOutcome::SyntaxError(d) => assert_eq!(
                d.kind,
                DiagnosticKind::EarlyInvalidAssignmentTarget,
                "Expected EarlyInvalidAssignmentTarget on {code:?}"
            ),
            other => panic!("Expected strict SyntaxError on {code:?}, got {other:?}"),
        }
    }

    // Cross-check against native Apple JavaScriptCore (`jsc`) if present on macOS
    let jsc_path = Path::new("/System/Library/Frameworks/JavaScriptCore.framework/Versions/Current/Helpers/jsc");
    if jsc_path.exists() {
        for code in strict_rejected {
            let js = format!(
                "try {{ Function({:?}); print('OK'); }} catch (e) {{ print('ERR'); }}",
                code
            );
            let out = Command::new(jsc_path)
                .arg("-e")
                .arg(&js)
                .output()
                .expect("run jsc");
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert_eq!(stdout.trim(), "ERR", "JSC disagreed on strict CallExpression target {code:?}");
        }
    }
}

fn expand_rust_use_tree(prefix: &str, body: &str, out: &mut Vec<String>) {
    let mut depth = 0usize;
    let mut seg_start = 0usize;
    let bytes = body.as_bytes();
    let mut items: Vec<&str> = Vec::new();
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'{' {
            depth += 1;
        } else if b == b'}' {
            depth = depth.saturating_sub(1);
        } else if b == b',' && depth == 0 {
            items.push(&body[seg_start..i]);
            seg_start = i + 1;
        }
    }
    items.push(&body[seg_start..]);

    for raw in items {
        let item = raw.trim();
        if item.is_empty() {
            continue;
        }
        if let Some(lb) = item.find('{') {
            if let Some(rb) = item.rfind('}') {
                let sub_prefix = item[..lb].trim().trim_end_matches("::");
                let combined = if prefix.is_empty() {
                    sub_prefix.to_string()
                } else if sub_prefix.is_empty() {
                    prefix.to_string()
                } else {
                    format!("{prefix}::{sub_prefix}")
                };
                expand_rust_use_tree(&combined, &item[lb + 1..rb], out);
                continue;
            }
        }
        let clean = item.split(" as ").next().unwrap_or(item).trim();
        if clean == "self" {
            if !prefix.is_empty() {
                out.push(prefix.to_string());
            }
        } else if prefix.is_empty() {
            out.push(clean.to_string());
        } else {
            out.push(format!("{prefix}::{clean}"));
        }
    }
}

fn scan_forbidden_ambient_imports(rust_src: &str) -> Vec<String> {
    let mut violations = Vec::new();
    for stmt in rust_src.split(';') {
        let trimmed = stmt.trim();
        let after_use = if let Some(r) = trimmed.strip_prefix("use ") {
            Some(r)
        } else if let Some(idx) = trimmed.find(" use ") {
            Some(&trimmed[idx + 5..])
        } else if let Some(idx) = trimmed.find("\nuse ") {
            Some(&trimmed[idx + 5..])
        } else {
            None
        };
        if let Some(u) = after_use {
            let norm = u.trim().trim_start_matches("::");
            let mut paths = Vec::new();
            expand_rust_use_tree("", norm, &mut paths);
            for p in paths {
                for bad in [
                    "std::fs",
                    "std::net",
                    "std::process",
                    "std::env",
                    "std::os",
                    "core::arch::asm",
                    "std::arch::asm",
                ] {
                    if p == bad || p.starts_with(&format!("{bad}::")) {
                        violations.push(p.clone());
                    }
                }
            }
        }
    }
    violations
}

#[test]
fn static_ratchet_and_zero_ambient_authority_audit() {
    // Regression-check braced import detector itself
    let synthetic = "pub(crate) use ::std::{collections::HashMap, fs::{File, read}, net::TcpStream, process::Command};";
    let caught = scan_forbidden_ambient_imports(synthetic);
    assert_eq!(caught.len(), 4, "Braced-use scanner must catch all 4 ambient imports");

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let license_path = manifest_dir.join("tests").join("data").join("LICENSE");
    let license_txt = fs::read_to_string(&license_path).expect("tests/data/LICENSE must exist");
    assert!(
        license_txt.contains("BSD") || license_txt.contains("Redistribution and use"),
        "tests/data/LICENSE must contain upstream test262 BSD license"
    );

    let src_dir = manifest_dir.join("src");
    let lib_rs = fs::read_to_string(src_dir.join("lib.rs")).expect("read src/lib.rs");
    assert!(
        lib_rs.contains("#![forbid(unsafe_code)]"),
        "src/lib.rs must contain #![forbid(unsafe_code)]"
    );

    for entry in fs::read_dir(&src_dir).expect("read src/") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let content = fs::read_to_string(&path).expect("read rs");
        let fname = path.file_name().unwrap().to_string_lossy();
        for forbidden in [
            "assume(",
            "admit(",
            "external_body",
            "verifier::external",
            "assume_specification",
            "exec_allows_no_decreases_clause",
            "unsafe ",
            "unsafe{",
        ] {
            assert!(
                !content.contains(forbidden),
                "Forbidden trusted/escape-hatch marker {forbidden:?} found in src/{fname}"
            );
        }
        let ambient = scan_forbidden_ambient_imports(&content);
        assert!(
            ambient.is_empty(),
            "Forbidden ambient-authority imports in src/{fname}: {ambient:?}"
        );
    }
}
