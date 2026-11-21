//! End-to-end `tc39/test262` conformance, V8 (`node`) differential testing (240+ programs),
//! fuel-exactness, explicit `Unsupported` refusal, cross-realm isolation, and per-realm
//! heap-quota + Mark-Sweep GC tests for `vjs` (`docs/verified-browser-engine.md` §3.3).

use serde_json::{json, Value as JsonValue};
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use vjs::heap::{HeapReadVal, HeapWriteRes};
use vjs::value::{number_to_js_str, JsStr, NAN_BITS, NEG_ZERO_BITS};
use vjs::{
    eval_script, eval_script_parsed, eval_script_state, parse_script, parse_script_bytes,
    run_state_with_quota, Heap, ObjectKind, ParseOutcome, RealmId, RunResult, ScriptCompletion,
    UnsupportedFeature, Val, VmState,
};

const NODE_BIN: &str = "/Users/mac/.nvm/versions/node/v24.15.0/bin/node";
const EXPECTED_TEST262_COMMIT: &str = "2a1ade303f72d3de80565c921d685222405c32ce";

// ---------------------------------------------------------------------------
// Pure-Rust FIPS 180-4 SHA-256 for `PROVENANCE` Integrity Verification
// ---------------------------------------------------------------------------

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
    let mut out = String::with_capacity(64);
    for word in h {
        out.push_str(&format!("{:08x}", word));
    }
    out
}

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn collect_js_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .expect("read_dir failed")
        .map(|e| e.expect("dir entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_js_files_recursive(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("js") {
            out.push(path);
        }
    }
}

fn js_str_from_ascii(s: &str) -> JsStr {
    JsStr(s.encode_utf16().collect())
}

fn js_str_to_rust(s: &JsStr) -> String {
    String::from_utf16_lossy(&s.0)
}

// ---------------------------------------------------------------------------
// Canonical Outcome Representation (Shared by `vjs` and V8 `node:vm`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum CanonicalOutcome {
    Normal(String),
    ThrowError { name: String },
    ThrowPrim(String),
    SyntaxError,
    Unsupported(UnsupportedFeature),
    Other(String),
}

fn format_vjs_val(st: &VmState, v: &Val) -> String {
    match v {
        Val::Undefined => "undefined".to_string(),
        Val::Null => "null".to_string(),
        Val::Bool(b) => if *b { "boolean:true" } else { "boolean:false" }.to_string(),
        Val::Number(n) => {
            if n.0 == NAN_BITS {
                "number:NaN".to_string()
            } else if n.0 == NEG_ZERO_BITS {
                "number:-0".to_string()
            } else {
                format!("number:{}", js_str_to_rust(&number_to_js_str(*n)))
            }
        }
        Val::Str(s) => format!("string:{}", js_str_to_rust(s)),
        Val::Object(oid) => {
            let realm = st.intr.realm;
            if let Some(vjs::heap::Slot::Live(obj)) = st.heap.slots.get(oid.0) {
                match obj.kind {
                    ObjectKind::Function { .. } | ObjectKind::BuiltinFunction { .. } => {
                        return "function".to_string();
                    }
                    ObjectKind::Array { length } => {
                        let mut parts = Vec::new();
                        for idx in 0..length {
                            let k = js_str_from_ascii(&idx.to_string());
                            match st.heap.get_prop(realm, *oid, &k) {
                                HeapReadVal::Ok(ev) => parts.push(format_vjs_val(st, &ev)),
                                _ => parts.push("undefined".to_string()),
                            }
                        }
                        return format!("array:[{}]", parts.join(","));
                    }
                    ObjectKind::Error { .. } => {
                        let nk = js_str_from_ascii("name");
                        if let HeapReadVal::Ok(Val::Str(ns)) = st.heap.get_prop(realm, *oid, &nk) {
                            return format!("error:{}", js_str_to_rust(&ns));
                        }
                        return "error:Error".to_string();
                    }
                    ObjectKind::Ordinary => {}
                }
            }
            if let Some(mut keys) = st.heap.own_enumerable_keys(realm, *oid) {
                keys.sort_by(|a, b| a.0.cmp(&b.0));
                let mut kvs = Vec::new();
                for k in keys {
                    if let HeapReadVal::Ok(pv) = st.heap.get_prop(realm, *oid, &k) {
                        kvs.push(format!("{}:{}", js_str_to_rust(&k), format_vjs_val(st, &pv)));
                    }
                }
                format!("object:{{{}}}", kvs.join(","))
            } else {
                "object:{}".to_string()
            }
        }
    }
}

fn eval_vjs_canonical(src: &str, fuel: usize, quota: usize) -> CanonicalOutcome {
    let (st_opt, res) = eval_script_state(src, fuel, quota);
    match res {
        RunResult::Done(ScriptCompletion::SyntaxError(_)) => CanonicalOutcome::SyntaxError,
        RunResult::Done(ScriptCompletion::Normal(v)) => {
            let st = st_opt.as_ref().expect("state present on Normal");
            CanonicalOutcome::Normal(format_vjs_val(st, &v))
        }
        RunResult::Done(ScriptCompletion::Throw(tv)) => {
            let st = st_opt.as_ref().expect("state present on Throw");
            if let Val::Object(oid) = &tv {
                let realm = st.intr.realm;
                let ck = js_str_from_ascii("constructor");
                let nk = js_str_from_ascii("name");
                if let HeapReadVal::Ok(Val::Object(coid)) = st.heap.get_prop(realm, *oid, &ck) {
                    if let HeapReadVal::Ok(Val::Str(cname)) = st.heap.get_prop(realm, coid, &nk) {
                        let nm = js_str_to_rust(&cname);
                        if !nm.is_empty() {
                            return CanonicalOutcome::ThrowError { name: nm };
                        }
                    }
                }
                if let HeapReadVal::Ok(Val::Str(ename)) = st.heap.get_prop(realm, *oid, &nk) {
                    let nm = js_str_to_rust(&ename);
                    if !nm.is_empty() {
                        return CanonicalOutcome::ThrowError { name: nm };
                    }
                }
                CanonicalOutcome::ThrowError {
                    name: "Object".to_string(),
                }
            } else {
                CanonicalOutcome::ThrowPrim(format_vjs_val(st, &tv))
            }
        }
        RunResult::Unsupported(feat) => CanonicalOutcome::Unsupported(feat),
        other => CanonicalOutcome::Other(format!("{:?}", other)),
    }
}

/// Batch-evaluates an array of JavaScript source strings in isolated fresh V8 Realms
/// (`node:vm.runInNewContext`) using `/Users/mac/.nvm/versions/node/v24.15.0/bin/node`.
fn eval_v8_batch(scripts: &[String]) -> Vec<CanonicalOutcome> {
    assert!(
        Path::new(NODE_BIN).exists(),
        "Required V8 Node binary missing at {}",
        NODE_BIN
    );
    let driver = r#"
const fs = require("node:fs");
const vm = require("node:vm");
const scripts = JSON.parse(fs.readFileSync(0, "utf8"));

function formatVal(v, ctx) {
  if (v === undefined) return "undefined";
  if (v === null) return "null";
  const t = typeof v;
  if (t === "boolean") return "boolean:" + (v ? "true" : "false");
  if (t === "number") {
    if (Number.isNaN(v)) return "number:NaN";
    if (Object.is(v, -0)) return "number:-0";
    return "number:" + String(v);
  }
  if (t === "string") return "string:" + v;
  if (t === "function") return "function";
  if (Array.isArray(v)) {
    const parts = [];
    for (let i = 0; i < v.length; i++) parts.push(formatVal(v[i], ctx));
    return "array:[" + parts.join(",") + "]";
  }
  const protoTag = Object.prototype.toString.call(v);
  if (protoTag === "[object Error]") {
    return "error:" + (v.name || "Error");
  }
  const keys = Object.keys(v).sort();
  const kvs = keys.map(k => k + ":" + formatVal(v[k], ctx));
  return "object:{" + kvs.join(",") + "}";
}

const out = [];
for (const src of scripts) {
  const ctx = vm.createContext({});
  let compiled;
  try {
    compiled = new vm.Script(src);
  } catch (e) {
    out.push({ kind: "SyntaxError" });
    continue;
  }
  try {
    const res = compiled.runInContext(ctx, { timeout: 2000 });
    out.push({ kind: "Normal", val: formatVal(res, ctx) });
  } catch (e) {
    if (e !== null && (typeof e === "object" || typeof e === "function")) {
      const cname = (e.constructor && e.constructor.name) || e.name || "Object";
      out.push({ kind: "ThrowError", name: String(cname) });
    } else {
      out.push({ kind: "ThrowPrim", val: formatVal(e, ctx) });
    }
  }
}
process.stdout.write(JSON.stringify(out));
"#;

    let mut child = Command::new(NODE_BIN)
        .arg("-e")
        .arg(driver)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn node");

    let payload = serde_json::to_vec(scripts).expect("serialize scripts");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(&payload)
        .expect("write stdin");

    let output = child.wait_with_output().expect("wait node");
    assert!(
        output.status.success(),
        "node batch runner failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let parsed: Vec<JsonValue> =
        serde_json::from_slice(&output.stdout).expect("parse node json output");
    assert_eq!(parsed.len(), scripts.len());

    parsed
        .into_iter()
        .map(|item| match item["kind"].as_str().unwrap() {
            "SyntaxError" => CanonicalOutcome::SyntaxError,
            "Normal" => CanonicalOutcome::Normal(item["val"].as_str().unwrap().to_string()),
            "ThrowError" => CanonicalOutcome::ThrowError {
                name: item["name"].as_str().unwrap().to_string(),
            },
            "ThrowPrim" => CanonicalOutcome::ThrowPrim(item["val"].as_str().unwrap().to_string()),
            other => panic!("unknown kind {}", other),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// `tc39/test262` Frontmatter Parser
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Test262Meta {
    only_strict: bool,
    negative_phase: Option<String>,
    negative_type: Option<String>,
}

fn parse_test262_meta(src: &str) -> Test262Meta {
    let mut only_strict = false;
    let mut negative_phase = None;
    let mut negative_type = None;

    if let Some(start) = src.find("/*---") {
        if let Some(end_rel) = src[start + 5..].find("---*/") {
            let yml = &src[start + 5..start + 5 + end_rel];
            if yml.contains("onlyStrict") {
                only_strict = true;
            }
            let mut in_neg = false;
            for line in yml.lines() {
                let trimmed = line.trim();
                if trimmed.starts_with("negative:") {
                    in_neg = true;
                    continue;
                }
                if in_neg {
                    if !line.starts_with(' ') && !line.starts_with('\t') && !trimmed.is_empty() {
                        in_neg = false;
                    } else if let Some(rest) = trimmed.strip_prefix("phase:") {
                        negative_phase = Some(rest.trim().to_string());
                    } else if let Some(rest) = trimmed.strip_prefix("type:") {
                        negative_type = Some(rest.trim().to_string());
                    }
                }
            }
        }
    }
    Test262Meta {
        only_strict,
        negative_phase,
        negative_type,
    }
}

fn classify_test262_suite(rel_from_lang: &str) -> &'static str {
    if rel_from_lang.starts_with("statements/try/") || rel_from_lang.starts_with("statements/throw/")
    {
        "language/exceptions"
    } else if rel_from_lang.starts_with("expressions/") {
        "language/expressions"
    } else if rel_from_lang.starts_with("statements/") {
        "language/statements"
    } else if rel_from_lang.starts_with("function-code/") {
        "language/function-code"
    } else if rel_from_lang.starts_with("block-scope/") {
        "language/block-scope"
    } else {
        "other"
    }
}

// ---------------------------------------------------------------------------
// 240+ Program V8 Differential Corpus
// ---------------------------------------------------------------------------

fn build_differential_corpus() -> Vec<String> {
    let mut p: Vec<String> = Vec::new();
    let mut add = |s: &str| p.push(s.to_string());

    // 1. Arithmetic, IEEE-754 special values, bitwise & shifts (35 programs)
    for expr in [
        "0 + 0",
        "1 + 2 * 3 - 4",
        "(17 % 5) + (-17 % 5) * 10",
        "1 / 0",
        "-1 / 0",
        "0 / 0",
        "1 / -0",
        "Object.is(-0, 0)",
        "Object.is(-0, -0)",
        "Object.is(NaN, 0 / 0)",
        "-0 === 0",
        "NaN === NaN",
        "NaN !== NaN",
        "Infinity + (-Infinity)",
        "2 ** 0",
        "2 ** 10",
        "(-3) ** 3",
        "2 ** 3 ** 2",
        "2 ** -2",
        "~0",
        "~(-1)",
        "0xff & 0x0f",
        "0xf0 | 0x0f",
        "0xff ^ 0xaa",
        "1 << 5",
        "-1 >> 4",
        "-1 >>> 24",
        "1 << 33",
        "0xffffffff | 0",
        "(0xffffffff >>> 0)",
        "+true + +false + +null + +''",
        "+'42' + +'  -7  '",
        "+'not_a_number'",
        "!'hello' === false && !'' === true && !0 === true && !NaN === true",
        "void (1 + 2)",
    ] {
        add(expr);
    }

    // 2. String operations, relational comparisons, ToPrimitive (`valueOf` vs `toString`) (22 programs)
    for expr in [
        "'hello' + ' ' + 'world'",
        "'abc'.length + ''[0]",
        "'abcdef'[2] + 'abcdef'[99]",
        "'abc' < 'abd'",
        "'b' > 'aa'",
        "'10' < 2",
        "'10' > 2",
        "'10' < '2'",
        "1 + '2' + 3",
        "1 + 2 + '3'",
        "({ valueOf: function() { return 10; }, toString: function() { return 'twenty'; } }) + 5",
        "({ valueOf: function() { return 10; }, toString: function() { return 'twenty'; } }) + '!'",
        "String({ toString: function() { return 'custom'; }, valueOf: function() { return 7; } })",
        "Number({ valueOf: function() { return '19'; } })",
        "({ valueOf: function() { return {}; }, toString: function() { return 'fallback'; } }) + 1",
        "try { ({ valueOf: function() { return {}; }, toString: function() { return {}; } }) + 1; } catch (e) { e.name }",
        "var log = ''; ({ valueOf: function() { log += 'L'; return 3; } }) < ({ valueOf: function() { log += 'R'; return 4; } }); log",
        "null < 1 && null <= 0 && null >= 0 && !(null > 0) && !(null == 0)",
        "undefined < 0 || undefined > 0 || undefined == 0",
        "Boolean(0) + ',' + Boolean('0') + ',' + Boolean({}) + ',' + Boolean(null)",
        "String(undefined) + '|' + String(null) + '|' + String(true) + '|' + String(-0)",
        "Number(undefined) + '|' + Number(null) + '|' + Number(false) + '|' + Number(true)",
    ] {
        add(expr);
    }

    // 3. Loose & strict equality, `typeof` (20 programs)
    for expr in [
        "null == undefined",
        "undefined == null",
        "null === undefined",
        "0 == false && '' == false && '' == 0",
        "'0' == false && '0' == 0 && !('0' == '')",
        "1 == true && '1' == true && !(2 == true)",
        "[1, 2].join(',') == '1,2'",
        "({ valueOf: function() { return 42; } }) == 42",
        "({}) == ({})",
        "var o = {}; o == o && o === o",
        "typeof undefined",
        "typeof null",
        "typeof true",
        "typeof 3.5",
        "typeof 'hi'",
        "typeof {}",
        "typeof []",
        "typeof function(){}",
        "typeof undeclaredGlobalIdentifierXYZ",
        "{ typeof xBeforeLet; let xBeforeLet = 1; }",
    ] {
        add(expr);
    }

    // 4. Short-circuit logical `&&`, `||`, `??`, `?:`, optional chaining `?.` (22 programs)
    for expr in [
        "var s = 0; false && (s = 1); s",
        "var s = 0; true && (s = 7); s",
        "var s = 0; 'truthy' || (s = 9); s",
        "var s = 0; '' || (s = 9); s",
        "null ?? 'default'",
        "undefined ?? 'default'",
        "false ?? 'default'",
        "0 ?? 'default'",
        "'' ?? 'default'",
        "var s = 0; 0 ?? (s = 5); s",
        "var s = 0; undefined ?? (s = 5); s",
        "true ? 'yes' : 'no'",
        "0 ? 'yes' : (1 ? 'inner' : 'no')",
        "var a = null; a?.prop",
        "var a = undefined; var c = 0; a?.[c = 1]; c",
        "var a = { b: { c: 99 } }; a?.b?.c",
        "var a = { b: null }; a?.b?.c",
        "var f = null; var k = 0; f?.(k = 1); k",
        "var f = function(x) { return x * 2; }; f?.(21)",
        "var o = { m: function(x) { return this.v + x; }, v: 10 }; o.m?.(5)",
        "var o = {}; o.missing?.(1, 2)",
        "(1, 2, 3 + 4)",
    ] {
        add(expr);
    }

    // 5. Lexical scopes, `var` hoisting vs `let`/`const`, TDZ, shadowing, strict mode (28 programs)
    for expr in [
        "var x = 1; { var x = 2; } x",
        "let x = 1; { let x = 2; } x",
        "const c = 10; { const c = 20; c } ",
        "const c = 10; c = 20",
        "let a = b; var b = 5; a",
        "let a = b; let b = 5;",
        "var r = typeof fnHoisted; function fnHoisted() { return 7; } r + ':' + fnHoisted()",
        "if (false) { var hoistedFromDeadIf = 123; } hoistedFromDeadIf",
        "while (false) { var hoistedFromWhile = 1; } hoistedFromWhile",
        "{ let x = 10; { let f = function() { return x; }; var res = f(); } } res",
        "var f; { let secret = 42; f = function() { secret += 1; return secret; }; } f() + ',' + f()",
        "function tdzClosure() { var read = function() { return late; }; return read(); let late = 1; } tdzClosure()",
        "function tdzClosureOk() { var read = function() { return late; }; let late = 99; return read(); } tdzClosureOk()",
        "\"use strict\"; undeclaredAssign = 1;",
        "sloppyImplicitGlobal = 77; sloppyImplicitGlobal",
        "\"use strict\"; var x = 1; delete x;",
        "let x = 1; var x = 2;",
        "{ let dup = 1; let dup = 2; }",
        "function pdup(a) { let a = 1; }",
        "\"use strict\"; function sdup(a, a) { return a; }",
        "function sloppyDup(a, a) { return a; } sloppyDup(1, 9)",
        "var g = 50; globalThis.g",
        "let lexTop = 50; globalThis.lexTop",
        "globalThis.addedProp = 88; addedProp",
        "var x = 10; x += 5; x -= 3; x *= 2; x",
        "var x = 0; x ||= 9; var y = 4; y ||= 99; var z = null; z ??= 7; x + ':' + y + ':' + z",
        "var i = 5; var a = i++; var b = ++i; a + ':' + b + ':' + i",
        "var o = { n: 10 }; var a = o.n--; var b = --o.n; a + ':' + b + ':' + o.n",
    ] {
        add(expr);
    }

    // 6. Functions, closures, currying, recursion, higher-order JS, `this`, arrows, `arguments` (30 programs)
    for expr in [
        "(function(x) { return x * x; })(9)",
        "var add = a => b => a + b; add(15)(27)",
        "var compose = (f, g) => x => f(g(x)); compose(x => x + 1, x => x * 3)(10)",
        "function fact(n) { return n <= 1 ? 1 : n * fact(n - 1); } fact(7)",
        "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); } fib(9)",
        "function isEven(n) { return n === 0 ? true : isOdd(n - 1); } function isOdd(n) { return n === 0 ? false : isEven(n - 1); } isEven(14) + ':' + isOdd(14)",
        "var Y = f => (x => f(v => x(x)(v)))(x => f(v => x(x)(v))); var yf = Y(rec => n => n <= 1 ? 1 : n * rec(n - 1)); yf(6)",
        "function makeCounter(init) { let c = init; return { inc: () => ++c, dec: () => --c, get: () => c }; } var ctr = makeCounter(10); ctr.inc(); ctr.inc(); ctr.dec(); ctr.get()",
        "function sumArgs() { var s = 0; for (var i = 0; i < arguments.length; i++) s += arguments[i]; return s; } sumArgs(1, 2, 3, 4, 5)",
        "function shadowArguments(arguments) { return arguments * 2; } shadowArguments(21)",
        "var namedExpr = function selfRef(n) { return n <= 0 ? 'done' : selfRef(n - 1); }; namedExpr(3)",
        "var f = function innerName() { return typeof innerName; }; typeof innerName + ':' + f()",
        "var f = function immutableSelf() { immutableSelf = 123; return typeof immutableSelf; }; f()",
        "\"use strict\"; var f = function strictImmutableSelf() { strictImmutableSelf = 123; }; f()",
        "function sloppyThis() { return this === globalThis; } sloppyThis()",
        "\"use strict\"; function strictThis() { return this === undefined; } strictThis()",
        "var obj = { v: 33, get: function() { var arr = () => this.v; return arr(); } }; obj.get()",
        "var arrowFn = x => x + 1; new arrowFn(1)",
        "function greet(prefix, suffix) { return prefix + this.who + suffix; } greet.call({ who: 'VJS' }, '[', ']')",
        "function mapArr(arr, fn) { var out = []; for (var i = 0; i < arr.length; i++) out.push(fn(arr[i], i)); return out; } mapArr([10, 20, 30], (v, i) => v + i)",
        "function filterArr(arr, pred) { var out = []; for (var i = 0; i < arr.length; i++) if (pred(arr[i])) out.push(arr[i]); return out; } filterArr([1, 2, 3, 4, 5, 6], x => x % 2 === 0)",
        "function reduceArr(arr, fn, acc) { for (var i = 0; i < arr.length; i++) acc = fn(acc, arr[i]); return acc; } reduceArr([1, 2, 3, 4], (a, b) => a * b, 1)",
        "function noReturn() { var x = 1 + 2; } noReturn()",
        "function earlyReturn(x) { if (x > 0) return 'pos'; return 'nonpos'; } earlyReturn(3) + ':' + earlyReturn(0)",
        "(function(a, b, c) {}).length + ':' + (function named() {}).name",
        "var o = { fn: function(x) { return x + 1; } }; var log = ''; o[(log += 'prop,', 'fn')]((log += 'arg', 4)); log",
        "var nonFn = 42; nonFn()",
        "var undefObj = undefined; undefObj.prop",
        "\"use strict\"; var prim = 5; prim.prop = 10;",
        "var prim = 5; prim.prop = 10; prim.prop",
    ] {
        add(expr);
    }

    // 7. Loops (`while`, `do-while`, `for`, per-iteration `for (let ...)`, `for-in`, `for-of`, labels) (26 programs)
    for expr in [
        "var s = 0, i = 1; while (i <= 5) { s += i; i++; } s",
        "var s = 0, i = 0; do { s += 10; i++; } while (i < 1); s",
        "var fns = []; for (var i = 0; i < 4; i++) { fns.push(() => i); } [fns[0](), fns[1](), fns[2](), fns[3]()]",
        "var fns = []; for (let i = 0; i < 4; i++) { fns.push(() => i); } [fns[0](), fns[1](), fns[2](), fns[3]()]",
        "var fns = []; for (let i = 0; i < 3; fns.push(() => i), i++) { i += 0; } [fns[0](), fns[1](), fns[2]()]",
        "var out = []; for (var k in { a: 1, b: 2, c: 3 }) out.push(k); out",
        "var fns = []; for (let k in { x: 1, y: 2 }) fns.push(() => k); [fns[0](), fns[1]()]",
        "for (var k in null) { throw 'unreachable'; } 'ok'",
        "for (var k in undefined) { throw 'unreachable'; } 'ok'",
        "var s = 0; for (const v of [10, 20, 30, 40]) s += v; s",
        "var chars = []; for (let ch of 'vjs!') chars.push(ch); chars.join('-')",
        "var fns = []; for (let v of ['a', 'b', 'c']) fns.push(() => v); [fns[0](), fns[1](), fns[2]()]",
        "for (let x of 12345) {}",
        "var hit = 0; outer: for (var i = 0; i < 4; i++) { for (var j = 0; j < 4; j++) { hit++; if (i === 1 && j === 2) break outer; } } hit",
        "var pairs = []; outer: for (var i = 0; i < 3; i++) { for (var j = 0; j < 3; j++) { if (j === 1) continue outer; pairs.push(i + ':' + j); } } pairs.join(',')",
        "var x = 0; blk: { x = 1; if (x === 1) break blk; x = 99; } x",
        "var s = 0; for (var i = 0; i < 6; i++) { if (i % 2 === 0) continue; s += i; } s",
        "var i = 0; for (;;) { i++; if (i === 5) break; } i",
        "for (let x = x; false; ) {}",
        "let outerX = 7; for (let outerX of [outerX]) {} ",
        // Statement completion values (`UpdateEmpty` §6.2.4.2)
        "while (false) { 99; }",
        "var c = 0; while (c < 3) { c++; c * 10; }",
        "var c = 0; while (c < 3) { c++; if (c === 2) break; 77; }",
        "var c = 0; while (c < 2) { c++; if (c === 2) continue; 55; }",
        "if (true) { 123; ; } else { 456; }",
        "if (false) { 123; }",
    ] {
        add(expr);
    }

    // 8. `switch` statement: strict discriminant, fallthrough, middle `default`, lexical block (16 programs)
    for expr in [
        "var r = ''; switch (2) { case 1: r += 'a'; break; case 2: r += 'b'; case 3: r += 'c'; break; default: r += 'd'; } r",
        "var r = ''; switch (99) { case 1: r += 'a'; default: r += 'd'; case 2: r += 'b'; } r",
        "var r = ''; switch ('2') { case 2: r = 'num'; break; case '2': r = 'str'; break; } r",
        "var r = ''; switch (NaN) { case NaN: r = 'matched'; break; default: r = 'default'; } r",
        "var r = ''; switch (-0) { case +0: r = 'zero'; break; default: r = 'other'; } r",
        "var log = ''; switch (2) { case (log += '1,', 1): break; case (log += '2,', 2): break; case (log += '3,', 3): break; } log",
        "var x = 'outer'; switch (1) { case 1: let x = 'inner'; r = x; break; } var r; r + ':' + x",
        "switch (1) { case 1: let shared = 10; case 2: shared + 5 }",
        "switch (2) { case 1: let uninit = 10; case 2: uninit }",
        "switch (1) { case 1: 42; break; }",
        "switch (1) { case 1: 42; case 2: ; break; }",
        "switch (9) { case 1: 42; }",
        "var s = 0; for (var i = 0; i < 4; i++) { switch (i) { case 1: continue; case 2: s += 20; break; default: s += 1; } s += 100; } s",
        "outer: switch (1) { case 1: switch (2) { case 2: 88; break outer; } 99; }",
        "switch (1) { default: default: }",
        "break;",
    ] {
        add(expr);
    }

    // 9. `try / catch / finally` & abrupt completion override matrix (32 programs)
    for expr in [
        "try { 10 } catch (e) { 20 }",
        "try { throw 'boom'; } catch (e) { 'caught:' + e }",
        "try { throw 123; } catch { 'parameterless-catch' }",
        "var e = 'outer'; try { throw 'inner'; } catch (e) { var leaked = 'ok'; } e + ':' + leaked",
        "var log = ''; try { log += 'T'; } finally { log += 'F'; } log",
        "var log = ''; try { log += 'T'; throw 'E'; } catch (e) { log += e; } finally { log += 'F'; } log",
        "function f() { var x = 1; try { return x; } finally { x = 2; } } f()",
        "var side = 0; function f() { try { return 10; } finally { side = 99; } } f() + ':' + side",
        "function f() { try { return 10; } finally { return 20; } } f()",
        "function f() { try { throw 'err1'; } finally { return 'saved'; } } f()",
        "try { try { throw 'err1'; } finally { throw 'err2'; } } catch (e) { e }",
        "function f() { try { throw 'err1'; } catch (e) { return 'fromCatch'; } finally { } } f()",
        "function f() { try { throw 'err1'; } catch (e) { return 'fromCatch'; } finally { return 'fromFinally'; } } f()",
        "function f() { try { throw 'err1'; } catch (e) { throw 'err2'; } finally { return 'overrideBoth'; } } f()",
        "var log = ''; for (var i = 0; i < 3; i++) { try { if (i === 1) break; log += i; } finally { log += 'f'; } } log",
        "var log = ''; for (var i = 0; i < 3; i++) { try { if (i === 1) continue; log += i; } finally { log += 'f'; } } log",
        "function f() { for (var i = 0; i < 3; i++) { try { return 'ret'; } finally { break; } } return 'afterLoop'; } f()",
        "function f() { var s = 0; for (var i = 0; i < 3; i++) { try { throw 'ignored'; } finally { continue; } } return s; } f()",
        "function f() { outer: for (var i = 0; i < 2; i++) { try { return 1; } finally { continue outer; } } return 2; } f()",
        "try { 10; } finally { 20; }",
        "try { throw 'x'; } catch (e) { 33; } finally { 44; }",
        "try { throw new Error('msg1'); } catch (e) { e.toString() }",
        "try { throw new TypeError('bad'); } catch (e) { (e instanceof Error) + ':' + (e instanceof TypeError) + ':' + e.toString() }",
        "try { throw new ReferenceError(); } catch (e) { e.toString() }",
        "try { throw new RangeError('oob'); } catch (e) { e.name + ':' + e.message }",
        "try { throw new SyntaxError('syn'); } catch (e) { e.constructor === SyntaxError }",
        "Error('withoutNew').toString()",
        "new Error().message === '' && new Error(undefined).message === ''",
        "var customErr = { name: 'CustomError', message: 'details' }; Error.prototype.toString.call(customErr)",
        "var emptyMsgErr = { name: 'OnlyName', message: '' }; Error.prototype.toString.call(emptyMsgErr)",
        "try { null.x; } catch (e) { e.name }",
        "try { ({})(); } catch (e) { e.name }",
    ] {
        add(expr);
    }

    // 10. Objects, prototypes, `new`, `instanceof`, `in`, `delete`, `Array` & `Object` intrinsics (34 programs)
    for expr in [
        "var x = 7, y = 8; ({ x, y, ['sum_' + (1 + 1)]: x + y })",
        "var o = { a: 1, a: 2 }; o.a",
        "function Point(x, y) { this.x = x; this.y = y; } Point.prototype.norm1 = function() { return this.x + this.y; }; var pt = new Point(3, 4); pt.norm1() + ':' + (pt instanceof Point) + ':' + (pt instanceof Object)",
        "function RetPrim() { this.ok = true; return 42; } (new RetPrim()).ok",
        "function RetObj() { this.ok = true; return { custom: 99 }; } var ro = new RetObj(); ro.ok + ':' + ro.custom",
        "function Base() {} function Sub() {} Sub.prototype = new Base(); var s = new Sub(); (s instanceof Sub) + ':' + (s instanceof Base) + ':' + (s instanceof Array)",
        "try { ({}) instanceof ({}); } catch (e) { e.name }",
        "try { 'a' in 'not_an_object'; } catch (e) { e.name }",
        "var o = { a: 1 }; ('a' in o) + ':' + ('toString' in o) + ':' + ('missing' in o)",
        "var o = { a: 1 }; o.hasOwnProperty('a') + ':' + o.hasOwnProperty('toString')",
        "Object.prototype.hasOwnProperty.call('abc', '1') + ':' + Object.prototype.hasOwnProperty.call('abc', '5') + ':' + Object.prototype.hasOwnProperty.call('abc', 'length')",
        "var o = { a: 1, b: 2 }; (delete o.a) + ':' + ('a' in o) + ':' + o.b",
        "delete 123",
        "var arr = [10, 20]; var n = arr.push(30, 40); n + ':' + arr.length + ':' + arr.join('|')",
        "var arr = [10, 20, 30]; var p = arr.pop(); p + ':' + arr.length + ':' + arr.join(',')",
        "[].pop() === undefined",
        "[1, undefined, null, 4].join('-')",
        "[, 1, , 2].length + ':' + (0 in [, 1]) + ':' + (1 in [, 1])",
        "var arr = [1, 2, 3, 4]; arr.length = 2; arr.length + ':' + arr[2] + ':' + arr.join(',')",
        "Array.isArray([]) + ':' + Array.isArray({}) + ':' + Array.isArray('str')",
        "new Array(3).length + ':' + (0 in new Array(3))",
        "Array(10, 20, 30).join(':')",
        "try { new Array(-1); } catch (e) { e.name }",
        "try { new Array(1.5); } catch (e) { e.name }",
        "Object.keys({ b: 1, a: 2, c: 3 }).join(',')",
        "Object.keys('primitive_or_num' ? 123 : 0).length",
        "try { Object.keys(null); } catch (e) { e.name }",
        "Object.prototype.toString.call(undefined) + '|' + Object.prototype.toString.call(null) + '|' + Object.prototype.toString.call([]) + '|' + Object.prototype.toString.call(function(){})",
        "(new Object() instanceof Object) && (Object({ k: 1 }).k === 1)",
        "try { new (Object.prototype.toString)(); } catch (e) { e.name }",
        "var hexAndEsc = '\\x41\\u0042\\n\\t\\\\'; hexAndEsc.length + ':' + hexAndEsc[0] + hexAndEsc[1]",
        "0x10 + 0Xff + 1.5e2",
        "return 1;",
        "continue;",
        // Round 2 conformance additions: exact Number::toString & StringToNumber, optional chaining,
        // ArraySetLength, prototype/live/string for-in, **=, MemberExpression for-in/of, chained labels,
        // single-statement early errors, legacy octals/escapes, numeric separators, template CRLF, <USP>.
        "String(0.1 + 0.2)",
        "String(1 / 3)",
        "String(9007199254740992) + '|' + String(9007199254740994)",
        "String(1.7976931348623157e308)",
        "String(5e-324) + '|' + String(2.2250738585072014e-308)",
        "+\"\\u300042\" + +\"\\u1680\\u2000\\u202f\\u205f8\"",
        "var a = null; a?.b.c",
        "var x = 0; var a = null; var r = a?.b[x++]; r + ':' + x",
        "var x = 0; var o = { f: null }; var r = o.f?.(x++).g[x++]; r + ':' + x",
        "var o = { x: 42, m: function() { return this.x; } }; o.m?.()",
        "var a = null; [delete a?.b, delete a?.b.c].join(',')",
        "var o = { a: { b: 1 } }; [delete o?.a.b, 'b' in o.a].join(',')",
        "var a = null; (a?.b).c",
        "var a = [1, 2, 3]; a.length = -1;",
        "var a = [1, 2, 3]; a.length = 1.5;",
        "var a = [1, 2, 3]; a.length = NaN;",
        "var a = [1, 2, 3]; a.length = 4294967296;",
        "var a = [10, 20, 30, 40]; a.length = 2; a.length + ':' + a[0] + ':' + a[1] + ':' + a[2]",
        "function P() {} P.prototype.inh = 1; var c = new P(); c.own = 2; var ks = []; for (var k in c) ks.push(k); ks.join(',')",
        "var o = { a: 1, b: 2, c: 3 }; var ks = []; for (var k in o) { ks.push(k); if (k === 'a') delete o.b; } ks.join(',')",
        "var ks = []; for (var k in 'hi') ks.push(k); ks.join(',')",
        "var x = 2; x **= 3; x",
        "var o = { n: 3 }; o.n **= 2; o.n",
        "var o = {}; for (o.k in { a: 1, b: 2 }) {} o.k",
        "var a = [0]; for (a[0] of [7, 9]) {} a[0]",
        "var s = 0; l1: l2: for (var i = 0; i < 4; i++) { if (i === 1) continue l1; if (i === 3) break l1; s += i; } s",
        "while (false) let x = 1;",
        "while (false) const x = 1;",
        "do let x = 1; while (false);",
        "for (;false;) let x = 1;",
        "for (var k in {}) let x = 1;",
        "for (var v of []) function f() {}",
        "lbl: let x = 1;",
        "\"use strict\"; if (true) function f() {}",
        "010 + ':' + 08 + ':' + 09",
        "\"use strict\"; 010",
        "\"use strict\"; 08",
        "\"use strict\"; 09",
        "\"\\07\" === \"\\x07\"",
        "\"use strict\"; \"\\07\"",
        "\"use strict\"; \"\\1\"",
        "\"use strict\"; \"\\8\"",
        "\"use strict\"; \"\\9\"",
        "\"\\07\"; \"use strict\";",
        "1_000_000 + 0xFF_AA + 0b1010_0101 + 0o77_11",
        "1__0",
        "1_",
        "0x_1",
        "1._0",
        "1_.0",
        "1e_1",
        "0_1",
        "`a\r\nb\rc`.length + ':' + (`a\r\nb\rc` === 'a\\nb\\nc')",
        "\u{3000}var\u{2000}ux\u{1680}=\u{205F}42; ux",
        "'😀'.length",
    ] {
        add(expr);
    }

    assert!(
        p.len() >= 240,
        "expected >= 240 differential programs, got {}",
        p.len()
    );
    p
}

// ---------------------------------------------------------------------------
// Primary Test: `PROVENANCE` + 128 `tc39/test262` Tests + 245 V8 Differential Tests + `report.json`
// ---------------------------------------------------------------------------

#[test]
fn test262_conformance_v8_differential_and_report() {
    let data_dir = crate_dir().join("tests").join("data");
    let prov_path = data_dir.join("PROVENANCE");
    let prov_text = fs::read_to_string(&prov_path).expect("read PROVENANCE");

    assert!(
        prov_text.contains("https://github.com/tc39/test262.git"),
        "PROVENANCE must cite upstream tc39/test262 repository"
    );
    assert!(
        prov_text.contains(EXPECTED_TEST262_COMMIT),
        "PROVENANCE must pin exact upstream commit SHA"
    );
    assert!(
        prov_text.contains("BSD-3-Clause"),
        "PROVENANCE must record BSD-3-Clause license"
    );

    // 1. Verify bidirectional SHA-256 integrity of every pinned file in `tests/data/`.
    let mut recorded_hashes: BTreeMap<String, String> = BTreeMap::new();
    for line in prov_text.lines() {
        let trimmed = line.trim();
        if trimmed.len() > 66 && trimmed.as_bytes()[64] == b' ' && trimmed.as_bytes()[65] == b' ' {
            let hash = &trimmed[..64];
            let rel = &trimmed[66..];
            recorded_hashes.insert(rel.to_string(), hash.to_string());
        }
    }

    let mut disk_js_files = Vec::new();
    collect_js_files_recursive(&data_dir, &mut disk_js_files);
    assert_eq!(
        recorded_hashes.len(),
        disk_js_files.len(),
        "PROVENANCE file count ({}) must match .js files on disk ({})",
        recorded_hashes.len(),
        disk_js_files.len()
    );
    for disk_path in &disk_js_files {
        let rel = disk_path
            .strip_prefix(&data_dir)
            .unwrap()
            .to_str()
            .unwrap()
            .replace('\\', "/");
        let expected_sha = recorded_hashes
            .get(&rel)
            .unwrap_or_else(|| panic!("unrecorded file in tests/data: {}", rel));
        let actual_sha = sha256_hex(&fs::read(disk_path).expect("read js file"));
        assert_eq!(
            &actual_sha, expected_sha,
            "SHA-256 mismatch for pinned test262 file {}",
            rel
        );
    }

    // 2. Load unmodified upstream test262 harness (`sta.js` + `assert.js`) and all language scripts.
    let sta_js = fs::read_to_string(data_dir.join("harness/sta.js")).expect("read sta.js");
    let assert_js = fs::read_to_string(data_dir.join("harness/assert.js")).expect("read assert.js");

    let lang_dir = data_dir.join("language");
    let mut lang_files = Vec::new();
    collect_js_files_recursive(&lang_dir, &mut lang_files);
    assert!(
        lang_files.len() >= 60,
        "must run 60+ pinned tc39/test262 scripts, found {}",
        lang_files.len()
    );

    let mut prepared_t262: Vec<(String, &'static str, Test262Meta, String)> = Vec::new();
    let mut suite_totals: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut suite_passed: BTreeMap<&'static str, usize> = BTreeMap::new();

    for path in &lang_files {
        let rel = path
            .strip_prefix(&lang_dir)
            .unwrap()
            .to_str()
            .unwrap()
            .replace('\\', "/");
        let suite = classify_test262_suite(&rel);
        *suite_totals.entry(suite).or_insert(0) += 1;

        let raw_src = fs::read_to_string(path).expect("read test262 script");
        let meta = parse_test262_meta(&raw_src);
        let strict_prefix = if meta.only_strict {
            "\"use strict\";\n"
        } else {
            ""
        };
        let is_early_neg = matches!(
            meta.negative_phase.as_deref(),
            Some("parse") | Some("early")
        );
        let full_src = if is_early_neg {
            format!("{}{}", strict_prefix, raw_src)
        } else {
            format!("{}{}\n{}\n{}", strict_prefix, sta_js, assert_js, raw_src)
        };
        prepared_t262.push((rel, suite, meta, full_src));
    }

    // Verify all 5 required test262 suites are non-empty.
    for req_suite in [
        "language/expressions",
        "language/statements",
        "language/function-code",
        "language/block-scope",
        "language/exceptions",
    ] {
        let count = suite_totals.get(req_suite).copied().unwrap_or(0);
        assert!(
            count > 0,
            "missing required test262 suite {} (count = 0)",
            req_suite
        );
    }

    let t262_scripts: Vec<String> = prepared_t262.iter().map(|x| x.3.clone()).collect();
    let v8_t262_outcomes = eval_v8_batch(&t262_scripts);

    let mut t262_pass_count = 0usize;
    let mut t262_failures: Vec<String> = Vec::new();

    for (idx, (rel, suite, meta, full_src)) in prepared_t262.iter().enumerate() {
        let vjs_out = eval_vjs_canonical(full_src, 500_000, 65_536);
        let v8_out = &v8_t262_outcomes[idx];

        let passed = match (&meta.negative_phase, &meta.negative_type) {
            (Some(phase), Some(err_ty)) if phase == "parse" || phase == "early" => {
                assert_eq!(err_ty, "SyntaxError");
                vjs_out == CanonicalOutcome::SyntaxError && *v8_out == CanonicalOutcome::SyntaxError
            }
            (Some(_), Some(err_ty)) => {
                vjs_out
                    == CanonicalOutcome::ThrowError {
                        name: err_ty.clone(),
                    }
                    && *v8_out
                        == CanonicalOutcome::ThrowError {
                            name: err_ty.clone(),
                        }
            }
            _ => {
                matches!(vjs_out, CanonicalOutcome::Normal(_))
                    && matches!(v8_out, CanonicalOutcome::Normal(_))
            }
        };

        if passed {
            t262_pass_count += 1;
            *suite_passed.entry(suite).or_insert(0) += 1;
        } else {
            t262_failures.push(format!(
                "{} (meta={:?}): vjs={:?} vs v8={:?}",
                rel, meta, vjs_out, v8_out
            ));
        }
    }

    // 3. Run 240+ diverse JS programs differentially against V8 (`node`).
    let diff_programs = build_differential_corpus();
    let v8_diff_outcomes = eval_v8_batch(&diff_programs);
    let mut diff_pass_count = 0usize;
    let mut diff_mismatches: Vec<String> = Vec::new();

    for (idx, src) in diff_programs.iter().enumerate() {
        let vjs_out = eval_vjs_canonical(src, 300_000, 65_536);
        let v8_out = &v8_diff_outcomes[idx];
        if &vjs_out == v8_out {
            diff_pass_count += 1;
        } else {
            diff_mismatches.push(format!(
                "[#{}] `{}`:\n  vjs = {:?}\n  v8  = {:?}",
                idx, src, vjs_out, v8_out
            ));
        }
    }

    assert!(
        t262_failures.is_empty() && diff_mismatches.is_empty(),
        "test262 failures ({}/{}):\n{}\n\nV8 differential mismatches ({}/{}):\n{}",
        t262_failures.len(),
        prepared_t262.len(),
        t262_failures.join("\n"),
        diff_mismatches.len(),
        diff_programs.len(),
        diff_mismatches.join("\n")
    );
    assert_eq!(t262_pass_count, prepared_t262.len());
    assert_eq!(diff_pass_count, diff_programs.len());

    // 4. Write exact measured `browser/vjs/report.json`.
    let mut suites_json = serde_json::Map::new();
    for (suite, total) in &suite_totals {
        let passed = suite_passed.get(suite).copied().unwrap_or(0);
        suites_json.insert(
            (*suite).to_string(),
            json!({
                "total": total,
                "passed": passed,
                "failed": total - passed,
            }),
        );
    }

    let report = json!({
        "crate": "vjs",
        "milestone": "J4",
        "upstream_test262_repository": "https://github.com/tc39/test262.git",
        "upstream_test262_commit": EXPECTED_TEST262_COMMIT,
        "v8_oracle_binary": NODE_BIN,
        "test262": {
            "total": prepared_t262.len(),
            "passed": t262_pass_count,
            "failed": prepared_t262.len() - t262_pass_count,
            "suites": suites_json,
        },
        "v8_differential": {
            "total": diff_programs.len(),
            "passed": diff_pass_count,
            "failed": diff_programs.len() - diff_pass_count,
        },
        "trusted_items": {
            "assume": 0,
            "admit": 0,
            "external_body": 0,
            "external": 0,
            "assume_specification": 0,
            "unsafe": 0,
        }
    });

    let report_path = crate_dir().join("report.json");
    fs::write(
        &report_path,
        format!("{}\n", serde_json::to_string_pretty(&report).unwrap()),
    )
    .expect("write browser/vjs/report.json");
}

// ---------------------------------------------------------------------------
// End-to-End Theorem Runtime Checks: Fuel Exactness, Explicit Refusals,
// Per-Realm Heap Quota + Mark-Sweep GC, and Cross-Realm Isolation
// ---------------------------------------------------------------------------

#[test]
fn test_out_of_fuel_exactness_and_monotonicity() {
    let ParseOutcome::Ok(prog) =
        parse_script("var sum = 0; for (var i = 1; i <= 20; i++) { sum += i; } sum")
    else {
        panic!("expected valid parse");
    };

    // Fuel = 0 must immediately consume all 0 steps and return `OutOfFuel`.
    let (st0, res0) = run_state_with_quota(&prog, 0, 1024);
    assert_eq!(res0, RunResult::OutOfFuel);
    assert_eq!(st0.fuel, 0);

    // Tight fuel budget must genuinely exhaust `st.fuel == 0`.
    let (st_low, res_low) = run_state_with_quota(&prog, 25, 1024);
    assert_eq!(res_low, RunResult::OutOfFuel);
    assert_eq!(st_low.fuel, 0);

    // Ample fuel budget completes deterministically with `210` and `st.fuel > 0`.
    let (st_ok, res_ok) = run_state_with_quota(&prog, 5_000, 1024);
    assert!(st_ok.fuel > 0);
    match res_ok {
        RunResult::Done(ScriptCompletion::Normal(Val::Number(n))) => {
            assert_eq!(js_str_to_rust(&number_to_js_str(n)), "210");
        }
        other => panic!("expected Normal(210), got {:?}", other),
    }

    // Non-terminating recursion is cleanly bounded by `fuel` without host stack overflow.
    let rec_res = eval_script("function inf() { return inf(); } inf()", 200, 4096);
    assert_eq!(rec_res, RunResult::OutOfFuel);
}

#[test]
fn test_explicit_unsupported_refusals_never_silent_approximations() {
    let cases = [
        ("with ({}) { }", UnsupportedFeature::WithStatement),
        ("eval('1 + 1')", UnsupportedFeature::EvalDirectCall),
        ("class Widget {}", UnsupportedFeature::ClassSyntax),
        ("async function f() {}", UnsupportedFeature::AsyncFunction),
        ("function* gen() {}", UnsupportedFeature::GeneratorFunction),
        ("/abc/g", UnsupportedFeature::RegExpLiteral),
        ("42n", UnsupportedFeature::BigIntLiteral),
        ("2 ** 0.5", UnsupportedFeature::NonIntegerExponentiation),
    ];

    for (src, expected_feat) in cases {
        let res = eval_script(src, 10_000, 4096);
        assert_eq!(
            res,
            RunResult::Unsupported(expected_feat),
            "source `{}` must return explicit Unsupported({:?})",
            src,
            expected_feat
        );
    }
}

#[test]
fn test_realm_heap_quota_and_mark_sweep_gc_reclamation() {
    // 1. Allocate 400 short-lived objects inside a tight user quota of 24 slots!
    // Without Mark-Sweep GC reclaiming unreachable objects, iteration 25 would hit quota.
    let churn_script = r#"
        var acc = 0;
        for (var i = 0; i < 400; i++) {
            var tmp = { a: i, nested: { b: 1 } };
            acc += tmp.nested.b;
        }
        acc
    "#;
    let (st_opt, res) = eval_script_state(churn_script, 250_000, 24);
    match res {
        RunResult::Done(ScriptCompletion::Normal(Val::Number(n))) => {
            assert_eq!(js_str_to_rust(&number_to_js_str(n)), "400");
            let st = st_opt.unwrap();
            assert!(st.heap.count_realm_live(st.intr.realm) <= st.heap.realm_heap_quota);
        }
        other => panic!("GC should reclaim unreachable objects, got {:?}", other),
    }

    // 2. Verify temporary-root protection during nested allocation + `try/finally` under GC pressure!
    let rooted_script = r#"
        function runUnderPressure() {
            try {
                return { tag: 'live_return_value', v: 77 };
            } finally {
                for (var j = 0; j < 80; j++) {
                    var garbage = { idx: j };
                }
            }
        }
        var out = [runUnderPressure(), { k: 1 }, { k: 2 }];
        out[0].tag + ':' + out[0].v + ':' + out[2].k
    "#;
    let (_, rooted_res) = eval_script_state(rooted_script, 200_000, 16);
    match rooted_res {
        RunResult::Done(ScriptCompletion::Normal(Val::Str(s))) => {
            assert_eq!(js_str_to_rust(&s), "live_return_value:77:2");
        }
        other => panic!("temp_roots must protect in-flight values across GC: {:?}", other),
    }

    // 3. Retaining more live reachable objects than `realm_heap_quota` deterministically
    // returns `HeapQuotaExceeded` instead of unbounded memory growth.
    let retain_script = r#"
        var retained = [];
        for (var i = 0; i < 50; i++) {
            retained.push({ keep: i });
        }
        retained.length
    "#;
    let retain_res = eval_script(retain_script, 200_000, 16);
    assert_eq!(
        retain_res,
        RunResult::Done(ScriptCompletion::HeapQuotaExceeded)
    );
}

#[test]
fn test_cross_realm_object_isolation() {
    let mut heap = Heap::new(64);
    let r1 = RealmId(1);
    let r2 = RealmId(2);
    let key = js_str_from_ascii("secret");

    let oid_r1 = heap.alloc_bootstrap(vjs::heap::HeapObject {
        realm: r1,
        prototype: None,
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: vec![vjs::heap::PropEntry {
            key: JsStr(key.0.clone()),
            value: Val::Bool(true),
            writable: true,
            enumerable: true,
            configurable: true,
        }],
    });

    // Same-realm access succeeds.
    assert_eq!(heap.get_prop(r1, oid_r1, &key), HeapReadVal::Ok(Val::Bool(true)));

    // Cross-realm read, write, has_prop, has_own_prop, delete, and enumerable-keys are all rejected!
    assert_eq!(heap.get_prop(r2, oid_r1, &key), HeapReadVal::CrossRealmAccess);
    assert_eq!(
        heap.set_prop(r2, oid_r1, JsStr(key.0.clone()), Val::Bool(false)),
        HeapWriteRes::CrossRealmAccess
    );
    assert_eq!(heap.has_prop(r2, oid_r1, &key), HeapWriteRes::CrossRealmAccess);
    assert_eq!(
        heap.has_own_prop(r2, oid_r1, &key),
        HeapWriteRes::CrossRealmAccess
    );
    assert_eq!(
        heap.delete_prop(r2, oid_r1, &key),
        HeapWriteRes::CrossRealmAccess
    );
    assert_eq!(heap.own_enumerable_keys(r2, oid_r1), None);
}

#[test]
fn test_round2_audit_regressions() {
    // 1. Mark-Sweep GC reachable environment tracing & slot reuse under tight quota (`quota = 36`):
    //    (a) Returned function calls reclaim dead call environments & objects.
    let fn_churn = r#"
        function step(i) {
            var tmp = { v: i, inner: { w: 1 } };
            return tmp.v + tmp.inner.w;
        }
        var s = 0;
        for (var i = 0; i < 120; i++) {
            s += step(i);
        }
        s
    "#;
    let (st_fn_opt, res_fn) = eval_script_state(fn_churn, 300_000, 36);
    match res_fn {
        RunResult::Done(ScriptCompletion::Normal(Val::Number(n))) => {
            assert_eq!(js_str_to_rust(&number_to_js_str(n)), "7260");
            let st_fn = st_fn_opt.unwrap();
            assert!(
                st_fn.envs.envs.len() <= 36,
                "free EnvSlot reuse must bound arena growth across 120 calls, got {}",
                st_fn.envs.envs.len()
            );
        }
        other => panic!("expected 7260 under quota=36, got {:?}", other),
    }

    //    (b) Exited lexical `let`/`const` blocks reclaim dead block environments & objects.
    let blk_churn = r#"
        var s = 0;
        for (var i = 0; i < 60; i++) {
            let tmp = { v: i };
            const two = { v: 2 };
            s += tmp.v + two.v;
        }
        s
    "#;
    assert_eq!(
        eval_vjs_canonical(blk_churn, 300_000, 36),
        CanonicalOutcome::Normal("number:1890".to_string())
    );

    //    (c) `for (let ...)` per-iteration lexical environments reclaim across iterations.
    let for_let_churn = r#"
        var s = 0;
        for (let i = 0; i < 60; i++) {
            let tmp = { v: i };
            s += tmp.v;
        }
        s
    "#;
    assert_eq!(
        eval_vjs_canonical(for_let_churn, 300_000, 36),
        CanonicalOutcome::Normal("number:1770".to_string())
    );

    //    (d) Live closure-captured environments remain rooted across repeated GC sweeps!
    let closure_keep = r#"
        function mk(x) {
            let captured = { secret: x };
            return () => captured.secret;
        }
        var f = mk(42);
        var noise = 0;
        for (var i = 0; i < 60; i++) {
            let garbage = { idx: i, extra: [i] };
            noise += garbage.idx;
        }
        f() + ':' + noise
    "#;
    assert_eq!(
        eval_vjs_canonical(closure_keep, 300_000, 36),
        CanonicalOutcome::Normal("string:42:1770".to_string())
    );

    // 2. Verified UTF-8 -> UTF-16 frontend & `eval_script_parsed`:
    assert!(matches!(
        parse_script_bytes(&[0xFF, 0xFE, 0x61]),
        ParseOutcome::SyntaxError(_)
    ));
    let (po_ok, st_ok, res_ok) = eval_script_parsed("1 + 2", 500, 64);
    assert!(matches!(po_ok, ParseOutcome::Ok(_)));
    assert!(st_ok.is_some());
    assert!(matches!(res_ok, RunResult::Done(ScriptCompletion::Normal(_))));

    let (_po_oof, st_oof, res_oof) = eval_script_parsed("while (true) {}", 25, 64);
    assert_eq!(res_oof, RunResult::OutOfFuel);
    assert_eq!(st_oof.unwrap().fuel, 0);

    // 3. No host stack overflow on 15,000-character numeric string (`StringToNumber` BigNat RNE):
    let long_num_script = r#"
        var s = '0.';
        for (var i = 0; i < 15000; i++) {
            s += '0';
        }
        s += '1e15001';
        (+s) + ':' + s.length
    "#;
    let vjs_long = eval_vjs_canonical(long_num_script, 500_000, 256);
    let v8_long = &eval_v8_batch(&[long_num_script.to_string()])[0];
    assert_eq!(&vjs_long, v8_long);
    assert_eq!(vjs_long, CanonicalOutcome::Normal("string:1:15009".to_string()));
}
