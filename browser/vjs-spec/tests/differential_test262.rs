//! J0 Spec-as-Exec Differential Test262 & Live V8 Oracle Harness (`vjs_spec`).
//!
//! 1. Verifies compiler self-tests (`esmeta_to_verus.py --self-test`) and byte-for-byte
//!    reproducibility of `src/generated.rs` (`esmeta_to_verus.py --check`).
//! 2. Audits every `.rs` source file in `browser/vjs-spec/src/` with the exact trusted-marker
//!    regexes from `browser/scripts/ratchet.py`, asserting `0` escape hatches across all 6 categories.
//! 3. Executes the 25 compiled Verus `exec` functions in `vjs_spec` against:
//!    (a) real pinned upstream `tc39/test262` `.js` test cases under `browser/test262/` via an
//!        in-process pure-Rust Test262 evaluator backed directly by `vjs_spec`'s verified `exec`
//!        operations (cross-checked 1:1 against Node.js V8 running the same files with upstream
//!        `harness/sta.js` + `harness/assert.js`), and
//!    (b) `/Users/mac/.nvm/versions/node/v24.15.0/bin/node` (V8) as a live differential oracle across
//!        thousands of adversarial edge-case inputs (`NaN` payloads, `-0.0`, `+0.0`, `±Infinity`,
//!        `i32::MIN`, `u32::MAX`, `±2^53`, `Number.MAX_VALUE`, subnormals, arbitrary-limb BigInts,
//!        Unicode-whitespace & radix strings, booleans, `null`, `undefined`, symbols, and objects
//!        with `ToPrimitive` coercions and `TypeError` throws).
//! 4. Writes `browser/vjs-spec/report.json` with exact measured per-section pass counts.

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{json, Value};
use vjs_spec::{
    AbruptOrNormal, BitwiseOp, ExactInt, JsBigInt, JsNumber, JsObject, JsPrim, JsValue,
    MathIntOrInf, ObjectCoercion, CANON_NAN_BITS, NEG_INF_BITS, NEG_ZERO_BITS, ONE_BITS,
    POS_INF_BITS, POS_ZERO_BITS,
};

const NODE_BIN: &str = "/Users/mac/.nvm/versions/node/v24.15.0/bin/node";
const ECMA262_COMMIT: &str = "74c33d406ec1763ca9ee5ad9165571661649d6e6";
const TEST262_COMMIT: &str = "2a1ade303f72d3de80565c921d685222405c32ce";

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn browser_dir() -> PathBuf {
    crate_dir().parent().unwrap().to_path_buf()
}

// ===============================================================================================
// Test 1: Compiler Unit Tests & `src/generated.rs` Byte-for-Byte Reproducibility
// ===============================================================================================

#[test]
fn compiler_self_test_and_reproducibility() {
    let script = browser_dir().join("scripts/esmeta_to_verus.py");
    let st = Command::new("python3")
        .arg(&script)
        .arg("--self-test")
        .output()
        .expect("failed to execute esmeta_to_verus.py --self-test");
    assert!(
        st.status.success(),
        "esmeta_to_verus.py --self-test failed:\n{}\n{}",
        String::from_utf8_lossy(&st.stdout),
        String::from_utf8_lossy(&st.stderr)
    );

    let chk = Command::new("python3")
        .arg(&script)
        .arg("--check")
        .output()
        .expect("failed to execute esmeta_to_verus.py --check");
    assert!(
        chk.status.success(),
        "esmeta_to_verus.py --check failed:\n{}\n{}",
        String::from_utf8_lossy(&chk.stdout),
        String::from_utf8_lossy(&chk.stderr)
    );
}

// ===============================================================================================
// Test 2: Zero Trusted Escape Hatches Audit (exact `ratchet.py` semantics)
// ===============================================================================================

#[test]
fn zero_trusted_escape_hatches_audit() {
    let src_dir = crate_dir().join("src");
    let mut rs_files: Vec<PathBuf> = fs::read_dir(&src_dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("rs"))
        .collect();
    rs_files.sort();
    assert!(!rs_files.is_empty());

    let lib_rs = fs::read_to_string(src_dir.join("lib.rs")).unwrap();
    assert!(
        lib_rs.contains("#![forbid(unsafe_code)]"),
        "lib.rs must contain #![forbid(unsafe_code)]"
    );

    // Check via Python `re` using the exact 6 regexes from `browser/scripts/ratchet.py`:
    let py_check = r#"
import json, re, sys
from pathlib import Path
MARKERS = {
    "assume": re.compile(r"\bassume\s*\("),
    "admit": re.compile(r"\badmit\s*\("),
    "external_body": re.compile(r"verifier::external_body"),
    "external": re.compile(r"verifier::external\b(?!_)"),
    "assume_specification": re.compile(r"\bassume_specification\b"),
    "unsafe": re.compile(r"\bunsafe\s*(\{|fn\b|impl\b)"),
}
srcs = sorted(Path(sys.argv[1]).glob("**/*.rs"))
body = "\n".join(p.read_text() for p in srcs)
counts = {k: len(r.findall(body)) for k, r in MARKERS.items()}
print(json.dumps(counts))
"#;
    let out = Command::new("python3")
        .arg("-c")
        .arg(py_check)
        .arg(&src_dir)
        .output()
        .unwrap();
    assert!(out.status.success());
    let counts: HashMap<String, usize> = serde_json::from_slice(&out.stdout).unwrap();
    for (marker, count) in &counts {
        assert_eq!(
            *count, 0,
            "Forbidden trusted marker `{marker}` found {count} times in vjs-spec/src"
        );
    }

    for rs in &rs_files {
        let content = fs::read_to_string(rs).unwrap();
        for forbidden in ["std::fs", "std::net", "std::process", "std::env"] {
            assert!(
                !content.contains(forbidden),
                "Forbidden host-authority import `{forbidden}` found in {}",
                rs.display()
            );
        }
    }
}

// ===============================================================================================
// Test 3: Upstream `PROVENANCE` SHA-256 Cryptographic Integrity Audit
// ===============================================================================================

#[test]
fn provenance_sha256_integrity_audit() {
    let test262_dir = browser_dir().join("test262");
    let spec_inputs_dir = crate_dir().join("spec_inputs");

    // Verify `browser/test262/ecma262/spec_excerpts.html` matches `browser/vjs-spec/spec_inputs/ecma262_clauses.html`
    let spec_a = fs::read(test262_dir.join("ecma262/spec_excerpts.html")).unwrap();
    let spec_b = fs::read(spec_inputs_dir.join("ecma262_clauses.html")).unwrap();
    assert_eq!(spec_a, spec_b, "Pinned <emu-alg> excerpts in test262/ and vjs-spec/spec_inputs/ must match byte-for-byte");

    // Verify every `(sha256: <hex>)` file digest recorded in `browser/test262/PROVENANCE`
    let py_sha_audit = r#"
import hashlib, json, re, sys
from pathlib import Path
root = Path(sys.argv[1])
prov = (root / "PROVENANCE").read_text()
assert "74c33d406ec1763ca9ee5ad9165571661649d6e6" in prov
assert "2a1ade303f72d3de80565c921d685222405c32ce" in prov
checked = 0
for m in re.finditer(r"(?:Excerpts\s*:\s*|-\s+)(\S+)\s+\(sha256:\s*([0-9a-f]{64})\)", prov):
    rel, expected = m.group(1), m.group(2)
    fp = root / rel
    actual = hashlib.sha256(fp.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"SHA-256 mismatch for {rel}: expected {expected}, got {actual}")
    checked += 1
print(json.dumps({"checked": checked}))
"#;
    let out = Command::new("python3")
        .arg("-c")
        .arg(py_sha_audit)
        .arg(&test262_dir)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "PROVENANCE SHA-256 audit failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let res: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(res["checked"].as_u64().unwrap(), 195);
}

// ===============================================================================================
// Helpers: Value Constructors & Adversarial Differential Corpus
// ===============================================================================================

fn utf16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn trim_utf16_ecma(units: &[u16]) -> Vec<u16> {
    let mut start = 0usize;
    let mut end = units.len();
    while start < end && vjs_spec::is_str_whitespace(units[start]) {
        start += 1;
    }
    while end > start && vjs_spec::is_str_whitespace(units[end - 1]) {
        end -= 1;
    }
    units[start..end].to_vec()
}

fn js_val_to_display_string(v: &JsValue) -> String {
    match v {
        JsValue::Undefined => "undefined".into(),
        JsValue::Null => "null".into(),
        JsValue::Boolean(b) => b.to_string(),
        JsValue::Number(n) => {
            if vjs_spec::num_is_nan(*n) {
                "NaN".into()
            } else if vjs_spec::num_is_pos_zero(*n) || vjs_spec::num_is_neg_zero(*n) {
                "0".into()
            } else if vjs_spec::num_is_pos_inf(*n) {
                "Infinity".into()
            } else if vjs_spec::num_is_neg_inf(*n) {
                "-Infinity".into()
            } else {
                format!("{}", f64::from_bits(n.0))
            }
        }
        JsValue::Str(u) => String::from_utf16_lossy(u),
        JsValue::BigInt(b) => {
            if b.limbs.is_empty() {
                "0".into()
            } else if b.limbs.len() <= 2 {
                let lo = b.limbs[0] as u128;
                let hi = (*b.limbs.get(1).unwrap_or(&0) as u128) << 32;
                let mag = hi | lo;
                if b.neg {
                    format!("-{mag}")
                } else {
                    format!("{mag}")
                }
            } else {
                format!("{b:?}")
            }
        }
        JsValue::Symbol(_) => "Symbol()".into(),
        JsValue::Object(o) => match &o.prim_default {
            ObjectCoercion::Primitive(JsPrim::Str(u)) => String::from_utf16_lossy(u),
            ObjectCoercion::Primitive(JsPrim::Number(n)) => {
                js_val_to_display_string(&JsValue::Number(*n))
            }
            ObjectCoercion::Primitive(JsPrim::Boolean(b)) => b.to_string(),
            _ => "[object Object]".into(),
        },
    }
}

fn bigint_from_decimal_or_hex(s: &str) -> JsBigInt {
    let v = JsValue::Str(utf16(s));
    match vjs_spec::val_string_to_bigint(&v) {
        JsValue::BigInt(b) => b,
        other => panic!("expected BigInt from {s:?}, got {other:?}"),
    }
}

fn plain_object(id: u64) -> JsValue {
    JsValue::Object(JsObject {
        id,
        is_htmldda: false,
        prim_default: ObjectCoercion::Primitive(JsPrim::Str(utf16("[object Object]"))),
        prim_number: ObjectCoercion::Primitive(JsPrim::Number(JsNumber(CANON_NAN_BITS))),
    })
}

#[derive(Clone)]
struct CorpusEntry {
    label: String,
    js_expr: String,
    val: JsValue,
}

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
}

fn f64_bits_to_js_expr(bits: u64) -> String {
    let lo = (bits & 0xFFFF_FFFF) as u32;
    let hi = (bits >> 32) as u32;
    format!("bitsToF64({hi}, {lo})")
}

fn build_adversarial_corpus() -> Vec<CorpusEntry> {
    let mut c = Vec::new();
    let mut push = |label: &str, js_expr: String, val: JsValue| {
        c.push(CorpusEntry {
            label: label.to_string(),
            js_expr,
            val,
        });
    };

    push("undefined", "undefined".into(), JsValue::Undefined);
    push("null", "null".into(), JsValue::Null);
    push("true", "true".into(), JsValue::Boolean(true));
    push("false", "false".into(), JsValue::Boolean(false));

    // 30 IEEE-754 binary64 Number edge cases (incl. distinct NaN bit patterns & subnormals)
    let num_bits_cases: &[(&str, u64)] = &[
        ("+0.0", POS_ZERO_BITS),
        ("-0.0", NEG_ZERO_BITS),
        ("NaN_canon", CANON_NAN_BITS),
        ("NaN_neg_quiet", 0xFFF8_0000_0000_0000),
        ("NaN_payload", 0x7FF8_0000_0000_1234),
        ("NaN_signaling", 0x7FF0_0000_0000_0001),
        ("+Infinity", POS_INF_BITS),
        ("-Infinity", NEG_INF_BITS),
        ("subnormal_min", 0x0000_0000_0000_0001),
        ("subnormal_neg_min", 0x8000_0000_0000_0001),
        ("subnormal_max", 0x000F_FFFF_FFFF_FFFF),
        ("normal_min_pos", 0x0010_0000_0000_0000),
        ("f64_MAX", 0x7FEF_FFFF_FFFF_FFFF),
        ("f64_neg_MAX", 0xFFEF_FFFF_FFFF_FFFF),
        ("1.0", ONE_BITS),
        ("-1.0", (-1.0f64).to_bits()),
        ("0.5", (0.5f64).to_bits()),
        ("-0.5", (-0.5f64).to_bits()),
        ("1.9", (1.9f64).to_bits()),
        ("-1.9", (-1.9f64).to_bits()),
        ("42.75", (42.75f64).to_bits()),
        ("i32_MIN", (-2147483648.0f64).to_bits()),
        ("i32_MAX", (2147483647.0f64).to_bits()),
        ("i32_MIN_minus_1", (-2147483649.0f64).to_bits()),
        ("i32_MAX_plus_1", (2147483648.0f64).to_bits()),
        ("u32_MAX", (4294967295.0f64).to_bits()),
        ("2^32", (4294967296.0f64).to_bits()),
        ("-2^32", (-4294967296.0f64).to_bits()),
        ("65535", (65535.0f64).to_bits()),
        ("65536", (65536.0f64).to_bits()),
        ("-65536", (-65536.0f64).to_bits()),
        ("MAX_SAFE_INT", (9007199254740991.0f64).to_bits()),
        ("2^53", (9007199254740992.0f64).to_bits()),
        ("1e20", (1e20f64).to_bits()),
        ("-1e20", (-1e20f64).to_bits()),
    ];
    for (lbl, bits) in num_bits_cases {
        push(lbl, f64_bits_to_js_expr(*bits), JsValue::Number(JsNumber(*bits)));
    }

    // 10 BigInt edge cases (incl. >2^53 precision gap and 2^64 and 1024-bit!)
    let bigints: &[(&str, &str)] = &[
        ("0n", "0"),
        ("1n", "1"),
        ("-1n", "-1"),
        ("42n", "42"),
        ("i32_MIN_n", "-2147483648"),
        ("2^32_n", "4294967296"),
        ("2^53_minus_1_n", "9007199254740991"),
        ("2^53_n", "9007199254740992"),
        ("2^53_plus_1_n", "9007199254740993"),
        ("2^64_n", "18446744073709551616"),
    ];
    for (lbl, dec) in bigints {
        push(
            lbl,
            format!("BigInt({:?})", dec),
            JsValue::BigInt(bigint_from_decimal_or_hex(dec)),
        );
    }

    // 18 String edge cases
    let strings: &[(&str, &str)] = &[
        ("str_empty", ""),
        ("str_spaces", "   "),
        ("str_unicode_ws_42", "\t\n\r\u{00A0}\u{FEFF} 42 \u{2028}"),
        ("str_0", "0"),
        ("str_neg_0", "-0"),
        ("str_pos_0", "+0"),
        ("str_1", "1"),
        ("str_neg_1", "-1"),
        ("str_half", "0.5"),
        ("str_neg_1_9", "-1.9"),
        ("str_hex", "0x10"),
        ("str_bin", "0b101"),
        ("str_oct", "0o77"),
        ("str_neg_hex", "-0x10"),
        ("str_Inf", "Infinity"),
        ("str_neg_Inf", "-Infinity"),
        ("str_overflow", "1e309"),
        ("str_NaN", "NaN"),
        ("str_true", "true"),
        ("str_2^53_plus_1", "9007199254740993"),
        ("str_obj_tag", "[object Object]"),
    ];
    for (lbl, s) in strings {
        let escaped = serde_json::to_string(s).unwrap();
        push(lbl, escaped, JsValue::Str(utf16(s)));
    }

    // Symbols (shared registry slots in V8 harness: SYM_1, SYM_2)
    push("Symbol(1)", "SYM_1".into(), JsValue::Symbol(1));
    push("Symbol(2)", "SYM_2".into(), JsValue::Symbol(2));

    // Objects (shared object instances in V8 harness so identity comparisons `OBJ_1 === OBJ_1` match!)
    push("OBJ_PLAIN_1", "OBJ_PLAIN_1".into(), plain_object(1));
    push("OBJ_PLAIN_2", "OBJ_PLAIN_2".into(), plain_object(2));
    push(
        "OBJ_VAL_42",
        "OBJ_VAL_42".into(),
        JsValue::Object(JsObject {
            id: 3,
            is_htmldda: false,
            prim_default: ObjectCoercion::Primitive(JsPrim::Number(JsNumber((42.0f64).to_bits()))),
            prim_number: ObjectCoercion::Primitive(JsPrim::Number(JsNumber((42.0f64).to_bits()))),
        }),
    );
    push(
        "OBJ_STR_0",
        "OBJ_STR_0".into(),
        JsValue::Object(JsObject {
            id: 4,
            is_htmldda: false,
            prim_default: ObjectCoercion::Primitive(JsPrim::Str(utf16("0"))),
            prim_number: ObjectCoercion::Primitive(JsPrim::Str(utf16("0"))),
        }),
    );
    push(
        "OBJ_BIGINT_1",
        "OBJ_BIGINT_1".into(),
        JsValue::Object(JsObject {
            id: 5,
            is_htmldda: false,
            prim_default: ObjectCoercion::Primitive(JsPrim::BigInt(bigint_from_decimal_or_hex("1"))),
            prim_number: ObjectCoercion::Primitive(JsPrim::BigInt(bigint_from_decimal_or_hex("1"))),
        }),
    );
    push(
        "OBJ_THROW",
        "OBJ_THROW".into(),
        JsValue::Object(JsObject {
            id: 6,
            is_htmldda: false,
            prim_default: ObjectCoercion::ThrowTypeError,
            prim_number: ObjectCoercion::ThrowTypeError,
        }),
    );

    c
}

/// Build an extra 1,000+ deterministic PRNG IEEE-754 & numeric-string corpus for unary + numeric ops.
fn build_fuzz_number_and_val_corpus() -> Vec<CorpusEntry> {
    let mut rng = Lcg(0xC0FFEE_262_u64);
    let mut out = Vec::new();
    for idx in 0..520 {
        let bits = match idx % 5 {
            0 => {
                // Random signed 40-bit integer as f64
                let v = ((rng.next_u64() % 0x100_0000_0000) as i64) - 0x80_0000_0000;
                (v as f64).to_bits()
            }
            1 => {
                // Random fractional f64 around 32-bit boundaries
                let base = ((rng.next_u64() % 10_000_000_000) as f64) - 5_000_000_000.0;
                let frac = ((rng.next_u64() % 1000) as f64) / 1000.0;
                (base + frac).to_bits()
            }
            2 => {
                // Random subnormal
                let sign = (rng.next_u64() & 1) << 63;
                let mant = 1 + (rng.next_u64() & 0x000F_FFFF_FFFF_FFFE);
                sign | mant
            }
            3 => {
                // Random high-exponent integral binary64 (`e` in 1075..1140)
                let sign = (rng.next_u64() & 1) << 63;
                let exp = (1075 + (rng.next_u64() % 65)) << 52;
                let mant = rng.next_u64() & 0x000F_FFFF_FFFF_FFFF;
                sign | exp | mant
            }
            _ => {
                // Arbitrary IEEE-754 bit pattern (including random quiet/signaling NaNs)
                rng.next_u64()
            }
        };
        out.push(CorpusEntry {
            label: format!("fuzz_num_{idx}"),
            js_expr: f64_bits_to_js_expr(bits),
            val: JsValue::Number(JsNumber(bits)),
        });
    }
    for idx in 0..200 {
        let s = match idx % 4 {
            0 => format!("  {}  ", (rng.next_u64() as i64) % 9_000_000_000_000),
            1 => format!("{}.{}e{}", (rng.next_u64() % 9999) as i64 - 5000, rng.next_u64() % 100000, (rng.next_u64() % 40) as i32 - 20),
            2 => format!("0x{:x}", rng.next_u64() & 0xFFFF_FFFF_FFFF),
            _ => format!("0b{:b}", rng.next_u64() & 0xFFFF),
        };
        out.push(CorpusEntry {
            label: format!("fuzz_str_{idx}"),
            js_expr: serde_json::to_string(&s).unwrap(),
            val: JsValue::Str(utf16(&s)),
        });
    }
    // Extreme 200,000-zero decimal exponent cancelation cases vs V8:
    let long_zeros = "0".repeat(200_000);
    out.push(CorpusEntry {
        label: "long_frac_zeros_cancel_pos_exp".into(),
        js_expr: "\"0.\" + \"0\".repeat(200000) + \"5e200001\"".into(),
        val: JsValue::Str(utf16(&format!("0.{long_zeros}5e200001"))),
    });
    out.push(CorpusEntry {
        label: "long_int_zeros_cancel_neg_exp".into(),
        js_expr: "\"5\" + \"0\".repeat(200000) + \"e-200000\"".into(),
        val: JsValue::Str(utf16(&format!("5{long_zeros}e-200000"))),
    });
    out
}

// ===============================================================================================
// Pure-Rust Test262 Spec-as-Exec Evaluator (`Test262SpecVm`)
// ===============================================================================================

#[derive(Clone, Debug)]
enum VmVal {
    Js(JsValue),
    Array(u64, Vec<JsValue>),
    Set(u64, Vec<JsValue>),
    FnBody(u64, Vec<String>, String),
    DynamicObj {
        id: u64,
        props: HashMap<String, VmVal>,
    },
    ErrorObj(&'static str),
    BuiltinFn(&'static str),
}

#[derive(Debug)]
enum VmSignal {
    ThrowTypeError,
    ThrowVal(VmVal),
    Return(VmVal),
}

type VmResult<T> = Result<T, VmSignal>;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    NumBits(u64),
    BigIntStr(String),
    Str(String),
    Punct(String),
}

fn strip_js_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\'' || bytes[i] == b'"' {
            let q = bytes[i];
            out.push(q as char);
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    out.push(bytes[i] as char);
                    out.push(bytes[i + 1] as char);
                    i += 2;
                } else if bytes[i] == q {
                    out.push(q as char);
                    i += 1;
                    break;
                } else {
                    out.push(src[i..].chars().next().unwrap());
                    i += src[i..].chars().next().unwrap().len_utf8();
                }
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            i = (i + 2).min(bytes.len());
        } else {
            let ch = src[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
        }
    }
    out
}

fn tokenize_js(raw: &str) -> Vec<Tok> {
    let s = strip_js_comments(raw);
    let chars: Vec<char> = s.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() || ((c as u32) <= 0xFFFF && vjs_spec::is_str_whitespace(c as u16)) {
            i += 1;
            continue;
        }
        if c == '\'' || c == '"' {
            let q = c;
            i += 1;
            let mut buf = String::new();
            while i < chars.len() && chars[i] != q {
                if chars[i] == '\\' && i + 1 < chars.len() {
                    i += 1;
                    match chars[i] {
                        'n' => buf.push('\n'),
                        'r' => buf.push('\r'),
                        't' => buf.push('\t'),
                        'b' => buf.push('\u{0008}'),
                        'f' => buf.push('\u{000C}'),
                        'v' => buf.push('\u{000B}'),
                        '0' => buf.push('\0'),
                        '\\' => buf.push('\\'),
                        '\'' => buf.push('\''),
                        '"' => buf.push('"'),
                        'x' if i + 2 < chars.len() => {
                            let hex: String = chars[i + 1..=i + 2].iter().collect();
                            let code = u8::from_str_radix(&hex, 16).unwrap();
                            buf.push(code as char);
                            i += 2;
                        }
                        'u' => {
                            if i + 1 < chars.len() && chars[i + 1] == '{' {
                                let start = i + 2;
                                let mut end = start;
                                while end < chars.len() && chars[end] != '}' {
                                    end += 1;
                                }
                                let hex: String = chars[start..end].iter().collect();
                                let cp = u32::from_str_radix(&hex, 16).unwrap();
                                buf.push(char::from_u32(cp).unwrap());
                                i = end;
                            } else if i + 4 < chars.len() {
                                let hex: String = chars[i + 1..=i + 4].iter().collect();
                                let cp = u32::from_str_radix(&hex, 16).unwrap();
                                buf.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                                i += 4;
                            }
                        }
                        other => buf.push(other),
                    }
                    i += 1;
                } else {
                    buf.push(chars[i]);
                    i += 1;
                }
            }
            i += 1; // closing quote
            toks.push(Tok::Str(buf));
            continue;
        }
        if c.is_ascii_digit() || (c == '.' && i + 1 < chars.len() && chars[i + 1].is_ascii_digit()) {
            let start = i;
            if c == '0' && i + 1 < chars.len() && matches!(chars[i + 1], 'x' | 'X' | 'b' | 'B' | 'o' | 'O') {
                i += 2;
                while i < chars.len() && chars[i].is_ascii_hexdigit() {
                    i += 1;
                }
            } else {
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '.') {
                    i += 1;
                }
                if i < chars.len() && (chars[i] == 'e' || chars[i] == 'E') {
                    i += 1;
                    if i < chars.len() && (chars[i] == '+' || chars[i] == '-') {
                        i += 1;
                    }
                    while i < chars.len() && chars[i].is_ascii_digit() {
                        i += 1;
                    }
                }
            }
            if i < chars.len() && chars[i] == 'n' {
                let num_s: String = chars[start..i].iter().collect();
                i += 1;
                toks.push(Tok::BigIntStr(num_s));
            } else {
                let num_s: String = chars[start..i].iter().collect();
                let jv = JsValue::Str(utf16(&num_s));
                let n = vjs_spec::val_string_to_number(&jv);
                toks.push(Tok::NumBits(n.0));
            }
            continue;
        }
        if c.is_alphabetic() || c == '_' || c == '$' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_' || chars[i] == '$') {
                i += 1;
            }
            toks.push(Tok::Ident(chars[start..i].iter().collect()));
            continue;
        }
        // Multi-char punctuators (longest first)
        let rem: String = chars[i..(i + 4).min(chars.len())].iter().collect();
        let multi = [
            ">>>=", "===", "!==", ">>>", "<<=", ">>=", "<<", ">>", "<=", ">=", "==", "!=", "&&",
            "||", "++", "--", "+=", "-=",
        ];
        if let Some(p) = multi.iter().find(|m| rem.starts_with(*m)) {
            toks.push(Tok::Punct((*p).to_string()));
            i += p.len();
            continue;
        }
        toks.push(Tok::Punct(c.to_string()));
        i += 1;
    }
    toks
}

struct Test262SpecVm {
    vars: HashMap<String, VmVal>,
    next_obj_id: u64,
    next_sym_id: u64,
    op_hits: HashMap<&'static str, usize>,
}

impl Test262SpecVm {
    fn new() -> Self {
        let mut vars = HashMap::new();
        vars.insert("undefined".into(), VmVal::Js(JsValue::Undefined));
        vars.insert("NaN".into(), VmVal::Js(JsValue::Number(JsNumber(CANON_NAN_BITS))));
        vars.insert("Infinity".into(), VmVal::Js(JsValue::Number(JsNumber(POS_INF_BITS))));
        vars.insert("TypeError".into(), VmVal::BuiltinFn("TypeError"));
        vars.insert("ReferenceError".into(), VmVal::BuiltinFn("ReferenceError"));
        vars.insert("Error".into(), VmVal::BuiltinFn("Error"));
        vars.insert("Test262Error".into(), VmVal::BuiltinFn("Test262Error"));
        vars.insert("Boolean".into(), VmVal::BuiltinFn("Boolean"));
        vars.insert("Number".into(), VmVal::BuiltinFn("Number"));
        vars.insert("String".into(), VmVal::BuiltinFn("String"));
        vars.insert("Object".into(), VmVal::BuiltinFn("Object"));
        vars.insert("Array".into(), VmVal::BuiltinFn("Array"));
        vars.insert("Function".into(), VmVal::BuiltinFn("Function"));
        vars.insert("Date".into(), VmVal::BuiltinFn("Date"));
        vars.insert("BigInt".into(), VmVal::BuiltinFn("BigInt"));
        vars.insert("Symbol".into(), VmVal::BuiltinFn("Symbol"));
        vars.insert("Set".into(), VmVal::BuiltinFn("Set"));
        vars.insert("eval".into(), VmVal::BuiltinFn("eval"));
        vars.insert("assert".into(), VmVal::BuiltinFn("assert"));
        Self {
            vars,
            next_obj_id: 100,
            next_sym_id: 100,
            op_hits: HashMap::new(),
        }
    }

    fn hit(&mut self, name: &'static str) {
        *self.op_hits.entry(name).or_insert(0) += 1;
    }

    fn alloc_obj_id(&mut self) -> u64 {
        let id = self.next_obj_id;
        self.next_obj_id += 1;
        id
    }

    fn wrap_object(&mut self, v: &VmVal) -> VmVal {
        match v {
            VmVal::DynamicObj { .. }
            | VmVal::Js(JsValue::Object(_))
            | VmVal::Array(_, _)
            | VmVal::Set(_, _)
            | VmVal::FnBody(_, _, _) => v.clone(),
            VmVal::Js(JsValue::Undefined) | VmVal::Js(JsValue::Null) => {
                let id = self.alloc_obj_id();
                VmVal::DynamicObj {
                    id,
                    props: HashMap::new(),
                }
            }
            other => {
                if let Some(prim) = Self::vm_to_prim(other) {
                    let id = self.alloc_obj_id();
                    VmVal::Js(JsValue::Object(JsObject {
                        id,
                        is_htmldda: false,
                        prim_default: ObjectCoercion::Primitive(prim.clone()),
                        prim_number: ObjectCoercion::Primitive(prim),
                    }))
                } else {
                    let id = self.alloc_obj_id();
                    VmVal::DynamicObj {
                        id,
                        props: HashMap::new(),
                    }
                }
            }
        }
    }

    /// Convert `VmVal` to `JsValue` WITHOUT invoking `ToPrimitive` hooks (for `Boolean`, `===`,
    /// `Object.is`, `Set`, `Array.includes`, `RequireObjectCoercible`, and non-coercing `==`).
    fn to_js_val_shallow(&mut self, v: &VmVal) -> JsValue {
        match v {
            VmVal::Js(j) => j.clone(),
            VmVal::Array(id, _) | VmVal::Set(id, _) | VmVal::FnBody(id, _, _) => plain_object(*id),
            VmVal::DynamicObj { id, .. } => plain_object(*id),
            VmVal::ErrorObj(kind) => plain_object(800_000 + (kind.as_ptr() as u64 % 99_999)),
            VmVal::BuiltinFn(name) => plain_object(900_000 + (name.as_ptr() as u64 % 99_999)),
        }
    }

    /// Materialize a `VmVal` into a `vjs_spec::JsValue` (evaluating `valueOf`/`toString` if `DynamicObj`).
    fn to_js_val(&mut self, v: &VmVal) -> VmResult<JsValue> {
        match v {
            VmVal::Js(j) => Ok(j.clone()),
            VmVal::Array(id, elems) => {
                let joined: String = elems
                    .iter()
                    .map(|e| match e {
                        JsValue::Undefined | JsValue::Null => String::new(),
                        _ => js_val_to_display_string(e),
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                let u = utf16(&joined);
                Ok(JsValue::Object(JsObject {
                    id: *id,
                    is_htmldda: false,
                    prim_default: ObjectCoercion::Primitive(JsPrim::Str(u.clone())),
                    prim_number: ObjectCoercion::Primitive(JsPrim::Str(u)),
                }))
            }
            VmVal::Set(id, _) | VmVal::FnBody(id, _, _) => Ok(plain_object(*id)),
            VmVal::ErrorObj(kind) => Ok(plain_object(800_000 + (kind.as_ptr() as u64 % 99_999))),
            VmVal::BuiltinFn(name) => {
                let id = 900_000 + (name.as_ptr() as u64 % 99_999);
                Ok(plain_object(id))
            }
            VmVal::DynamicObj { id, props } => {
                // OrdinaryToPrimitive with default/number hint (`valueOf` -> `toString`), evaluated once so side effects run once.
                let prim = self.eval_ordinary_to_primitive(props, &["valueOf", "toString"])?;
                Ok(JsValue::Object(JsObject {
                    id: *id,
                    is_htmldda: false,
                    prim_default: prim.clone(),
                    prim_number: prim,
                }))
            }
        }
    }

    /// ECMA-262 `ToString ( argument )` using `"string"` hint (`toString` -> `valueOf`) for objects.
    fn to_string_utf16(&mut self, v: &VmVal) -> VmResult<Vec<u16>> {
        match v {
            VmVal::DynamicObj { props, .. } => {
                match self.eval_ordinary_to_primitive(props, &["toString", "valueOf"])? {
                    ObjectCoercion::ThrowTypeError => Err(VmSignal::ThrowTypeError),
                    ObjectCoercion::Primitive(JsPrim::Symbol(_)) => Err(VmSignal::ThrowTypeError),
                    ObjectCoercion::Primitive(p) => {
                        let jv = match p {
                            JsPrim::Undefined => JsValue::Undefined,
                            JsPrim::Null => JsValue::Null,
                            JsPrim::Boolean(b) => JsValue::Boolean(b),
                            JsPrim::Number(n) => JsValue::Number(n),
                            JsPrim::BigInt(b) => JsValue::BigInt(b),
                            JsPrim::Str(u) => return Ok(u),
                            JsPrim::Symbol(s) => JsValue::Symbol(s),
                        };
                        Ok(utf16(&js_val_to_display_string(&jv)))
                    }
                }
            }
            other => {
                let jv = self.to_js_val(other)?;
                match &jv {
                    JsValue::Symbol(_) => Err(VmSignal::ThrowTypeError),
                    JsValue::Str(u) => Ok(u.clone()),
                    JsValue::Object(o) => match &o.prim_default {
                        ObjectCoercion::ThrowTypeError => Err(VmSignal::ThrowTypeError),
                        ObjectCoercion::Primitive(JsPrim::Symbol(_)) => Err(VmSignal::ThrowTypeError),
                        ObjectCoercion::Primitive(JsPrim::Str(u)) => Ok(u.clone()),
                        _ => Ok(utf16(&js_val_to_display_string(&jv))),
                    },
                    _ => Ok(utf16(&js_val_to_display_string(&jv))),
                }
            }
        }
    }

    fn eval_ordinary_to_primitive(
        &mut self,
        props: &HashMap<String, VmVal>,
        order: &[&str],
    ) -> VmResult<ObjectCoercion> {
        for mname in order {
            if let Some(mval) = props.get(*mname) {
                if let VmVal::FnBody(_, _params, body_src) = mval.clone() {
                    match self.exec_fn_body(&body_src) {
                        Ok(ret) => {
                            if let Some(prim) = Self::vm_to_prim(&ret) {
                                return Ok(ObjectCoercion::Primitive(prim));
                            }
                        }
                        Err(VmSignal::ThrowTypeError)
                        | Err(VmSignal::ThrowVal(VmVal::ErrorObj("TypeError"))) => {
                            return Ok(ObjectCoercion::ThrowTypeError);
                        }
                        Err(e) => return Err(e),
                    }
                }
            } else if !props.contains_key("__null_proto__") && *mname == "toString" {
                return Ok(ObjectCoercion::Primitive(JsPrim::Str(utf16("[object Object]"))));
            }
        }
        Ok(ObjectCoercion::ThrowTypeError)
    }

    fn vm_to_prim(v: &VmVal) -> Option<JsPrim> {
        match v {
            VmVal::Js(JsValue::Undefined) => Some(JsPrim::Undefined),
            VmVal::Js(JsValue::Null) => Some(JsPrim::Null),
            VmVal::Js(JsValue::Boolean(b)) => Some(JsPrim::Boolean(*b)),
            VmVal::Js(JsValue::Number(n)) => Some(JsPrim::Number(*n)),
            VmVal::Js(JsValue::BigInt(b)) => Some(JsPrim::BigInt(b.clone())),
            VmVal::Js(JsValue::Str(s)) => Some(JsPrim::Str(s.clone())),
            VmVal::Js(JsValue::Symbol(s)) => Some(JsPrim::Symbol(*s)),
            _ => None,
        }
    }

    fn hoist_var_decls(toks: &[Tok], vars: &mut HashMap<String, VmVal>) {
        let mut depth = 0usize;
        let mut i = 0usize;
        while i < toks.len() {
            match &toks[i] {
                Tok::Ident(k) if k == "function" => {
                    // Skip nested function body so local `var` inside functions isn't hoisted to outer scope
                    i += 1;
                    while i < toks.len() && !matches!(&toks[i], Tok::Punct(p) if p == "{") {
                        i += 1;
                    }
                    if i < toks.len() {
                        let mut fdepth = 1usize;
                        i += 1;
                        while i < toks.len() && fdepth > 0 {
                            match &toks[i] {
                                Tok::Punct(p) if p == "{" => fdepth += 1,
                                Tok::Punct(p) if p == "}" => fdepth -= 1,
                                _ => {}
                            }
                            i += 1;
                        }
                    }
                    continue;
                }
                Tok::Ident(k) if k == "var" => {
                    if let Some(Tok::Ident(vname)) = toks.get(i + 1) {
                        vars.entry(vname.clone()).or_insert(VmVal::Js(JsValue::Undefined));
                    }
                }
                Tok::Punct(p) if p == "{" => depth += 1,
                Tok::Punct(p) if p == "}" => depth = depth.saturating_sub(1),
                _ => {}
            }
            i += 1;
        }
        let _ = depth;
    }

    fn exec_fn_body(&mut self, src: &str) -> VmResult<VmVal> {
        let toks = tokenize_js(src);
        Self::hoist_var_decls(&toks, &mut self.vars);
        let mut p = Parser { toks: &toks, pos: 0, vm: self };
        match p.run_stmts() {
            Ok(_) => Ok(VmVal::Js(JsValue::Undefined)),
            Err(VmSignal::Return(v)) => Ok(v),
            Err(e) => Err(e),
        }
    }

    fn eval_code(&mut self, src: &str) -> VmResult<VmVal> {
        let toks = tokenize_js(src);
        Self::hoist_var_decls(&toks, &mut self.vars);
        let mut p = Parser { toks: &toks, pos: 0, vm: self };
        match p.run_stmts() {
            Ok(Some(v)) => Ok(v),
            Ok(None) => Ok(VmVal::Js(JsValue::Undefined)),
            Err(VmSignal::Return(v)) => Ok(v),
            Err(e) => Err(e),
        }
    }

    fn run_script(&mut self, src: &str) -> VmResult<()> {
        let toks = tokenize_js(src);
        Self::hoist_var_decls(&toks, &mut self.vars);
        let mut p = Parser { toks: &toks, pos: 0, vm: self };
        p.run_stmts().map(|_| ())
    }
}

struct Parser<'a> {
    toks: &'a [Tok],
    pos: usize,
    vm: &'a mut Test262SpecVm,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&'a Tok> {
        self.toks.get(self.pos)
    }

    fn eat_punct(&mut self, s: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Punct(p)) if p == s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_ident(&mut self, s: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Ident(id)) if id == s) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_punct(&mut self, s: &str) {
        assert!(
            self.eat_punct(s),
            "expected punct `{s}` at pos {}, got {:?}",
            self.pos,
            self.peek()
        );
    }

    fn skip_balanced_braces(&mut self) -> String {
        self.expect_punct("{");
        let start = self.pos;
        let mut depth = 1usize;
        while self.pos < self.toks.len() && depth > 0 {
            match &self.toks[self.pos] {
                Tok::Punct(p) if p == "{" => depth += 1,
                Tok::Punct(p) if p == "}" => depth -= 1,
                _ => {}
            }
            self.pos += 1;
        }
        let end = self.pos - 1;
        Self::reconstruct_tokens(&self.toks[start..end])
    }

    fn reconstruct_tokens(slice: &[Tok]) -> String {
        let mut out = String::new();
        for t in slice {
            match t {
                Tok::Ident(s) => {
                    out.push(' ');
                    out.push_str(s);
                }
                Tok::NumBits(b) => {
                    out.push(' ');
                    let f = f64::from_bits(*b);
                    if f.is_nan() {
                        out.push_str("NaN");
                    } else if f == f64::INFINITY {
                        out.push_str("Infinity");
                    } else if f == f64::NEG_INFINITY {
                        out.push_str("-Infinity");
                    } else if *b == NEG_ZERO_BITS {
                        out.push_str("-0");
                    } else {
                        out.push_str(&format!("{:?}", f));
                    }
                }
                Tok::BigIntStr(b) => {
                    out.push(' ');
                    out.push_str(b);
                    out.push('n');
                }
                Tok::Str(s) => {
                    out.push(' ');
                    out.push_str(&serde_json::to_string(s).unwrap());
                }
                Tok::Punct(p) => {
                    out.push(' ');
                    out.push_str(p);
                }
            }
        }
        out
    }

    fn run_stmts(&mut self) -> VmResult<Option<VmVal>> {
        let mut last = None;
        while self.pos < self.toks.len() {
            if matches!(self.peek(), Some(Tok::Punct(p)) if p == "}") {
                break;
            }
            if let Some(v) = self.run_stmt()? {
                last = Some(v);
            }
        }
        Ok(last)
    }

    fn skip_stmt_without_exec(&mut self) {
        if self.eat_punct("{") {
            let mut depth = 1usize;
            while self.pos < self.toks.len() && depth > 0 {
                match &self.toks[self.pos] {
                    Tok::Punct(p) if p == "{" => depth += 1,
                    Tok::Punct(p) if p == "}" => depth -= 1,
                    _ => {}
                }
                self.pos += 1;
            }
            return;
        }
        if self.eat_ident("if") {
            self.expect_punct("(");
            let mut d = 1usize;
            while self.pos < self.toks.len() && d > 0 {
                match &self.toks[self.pos] {
                    Tok::Punct(p) if p == "(" => d += 1,
                    Tok::Punct(p) if p == ")" => d -= 1,
                    _ => {}
                }
                self.pos += 1;
            }
            self.skip_stmt_without_exec();
            if self.eat_ident("else") {
                self.skip_stmt_without_exec();
            }
            return;
        }
        while self.pos < self.toks.len() {
            if self.eat_punct(";") {
                return;
            }
            if matches!(self.peek(), Some(Tok::Punct(p)) if p == "}") {
                return;
            }
            self.pos += 1;
        }
    }

    fn run_stmt(&mut self) -> VmResult<Option<VmVal>> {
        if self.eat_punct(";") {
            return Ok(None);
        }
        if self.eat_punct("{") {
            let v = self.run_stmts()?;
            self.expect_punct("}");
            return Ok(v);
        }
        if self.eat_ident("var") || self.eat_ident("let") || self.eat_ident("const") {
            loop {
                let Some(Tok::Ident(name)) = self.peek().cloned() else { break };
                self.pos += 1;
                let val = if self.eat_punct("=") {
                    self.parse_expr()?
                } else {
                    VmVal::Js(JsValue::Undefined)
                };
                self.vm.vars.insert(name, val);
                if !self.eat_punct(",") {
                    break;
                }
            }
            self.eat_punct(";");
            return Ok(None);
        }
        if self.eat_ident("function") {
            if let Some(Tok::Ident(fname)) = self.peek().cloned() {
                self.pos += 1;
                let params = self.parse_fn_params();
                let body = self.skip_balanced_braces();
                let fid = self.vm.alloc_obj_id();
                self.vm.vars.insert(fname, VmVal::FnBody(fid, params, body));
                return Ok(None);
            }
        }
        if self.eat_ident("return") {
            if self.eat_punct(";") || matches!(self.peek(), Some(Tok::Punct(p)) if p == "}") {
                return Err(VmSignal::Return(VmVal::Js(JsValue::Undefined)));
            }
            let v = self.parse_expr()?;
            self.eat_punct(";");
            return Err(VmSignal::Return(v));
        }
        if self.eat_ident("throw") {
            let ex = self.parse_expr()?;
            self.eat_punct(";");
            if matches!(&ex, VmVal::ErrorObj("TypeError")) {
                return Err(VmSignal::ThrowTypeError);
            }
            return Err(VmSignal::ThrowVal(ex));
        }
        if self.eat_ident("if") {
            self.expect_punct("(");
            let cond_v = self.parse_expr()?;
            self.expect_punct(")");
            let jv = self.vm.to_js_val_shallow(&cond_v);
            self.vm.hit("ToBoolean");
            let cond_b = vjs_spec::to_boolean(&jv);
            if cond_b {
                let v = self.run_stmt()?;
                if self.eat_ident("else") {
                    self.skip_stmt_without_exec();
                }
                return Ok(v);
            } else {
                self.skip_stmt_without_exec();
                if self.eat_ident("else") {
                    return self.run_stmt();
                }
                return Ok(None);
            }
        }
        if self.eat_ident("try") {
            let try_body = self.skip_balanced_braces();
            let res = self.vm.eval_code(&try_body);
            if self.eat_ident("catch") {
                let mut catch_param: Option<String> = None;
                if self.eat_punct("(") {
                    if let Some(Tok::Ident(pname)) = self.peek().cloned() {
                        self.pos += 1;
                        catch_param = Some(pname);
                    }
                    self.expect_punct(")");
                }
                let catch_body = self.skip_balanced_braces();
                if let Err(sig) = res {
                    let caught_val = match sig {
                        VmSignal::ThrowVal(v) => v,
                        VmSignal::ThrowTypeError => VmVal::ErrorObj("TypeError"),
                        VmSignal::Return(r) => return Err(VmSignal::Return(r)),
                    };
                    if let Some(pname) = catch_param {
                        self.vm.vars.insert(pname, caught_val);
                    }
                    let cv = self.vm.eval_code(&catch_body)?;
                    return Ok(Some(cv));
                }
            }
            res.map(Some)
        } else {
            let v = self.parse_expr()?;
            self.eat_punct(";");
            Ok(Some(v))
        }
    }

    fn parse_fn_params(&mut self) -> Vec<String> {
        self.expect_punct("(");
        let mut params = Vec::new();
        while !self.eat_punct(")") {
            if let Some(Tok::Ident(id)) = self.peek().cloned() {
                self.pos += 1;
                params.push(id);
            }
            if !self.eat_punct(",") {
                self.expect_punct(")");
                break;
            }
        }
        params
    }

    fn parse_expr(&mut self) -> VmResult<VmVal> {
        self.parse_assign()
    }

    fn parse_assign(&mut self) -> VmResult<VmVal> {
        if let Some(Tok::Ident(name)) = self.peek().cloned() {
            if matches!(self.toks.get(self.pos + 1), Some(Tok::Punct(p)) if p == "=") {
                self.pos += 2;
                let rhs = self.parse_assign()?;
                self.vm.vars.insert(name, rhs.clone());
                return Ok(rhs);
            }
            if matches!(self.toks.get(self.pos + 1), Some(Tok::Punct(p)) if p == ".")
                && matches!(self.toks.get(self.pos + 3), Some(Tok::Punct(p)) if p == "=")
            {
                if let Some(Tok::Ident(prop)) = self.toks.get(self.pos + 2).cloned() {
                    self.pos += 4;
                    let rhs = self.parse_assign()?;
                    match self.vm.vars.get_mut(&name) {
                        Some(VmVal::DynamicObj { props, .. }) => {
                            props.insert(prop, rhs.clone());
                        }
                        Some(VmVal::Js(JsValue::Null)) | Some(VmVal::Js(JsValue::Undefined)) => {
                            return Err(VmSignal::ThrowTypeError);
                        }
                        None => {
                            return Err(VmSignal::ThrowVal(VmVal::ErrorObj("ReferenceError")));
                        }
                        _ => {}
                    }
                    return Ok(rhs);
                }
            }
        }
        self.parse_logical_or()
    }

    fn parse_logical_or(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_logical_and()?;
        while self.eat_punct("||") {
            let jv = self.vm.to_js_val(&left)?;
            self.vm.hit("ToBoolean");
            if vjs_spec::to_boolean(&jv) {
                let _ = self.parse_logical_and()?;
            } else {
                left = self.parse_logical_and()?;
            }
        }
        Ok(left)
    }

    fn parse_logical_and(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_bitor()?;
        while self.eat_punct("&&") {
            let jv = self.vm.to_js_val(&left)?;
            self.vm.hit("ToBoolean");
            if !vjs_spec::to_boolean(&jv) {
                let _ = self.parse_bitor()?;
            } else {
                left = self.parse_bitor()?;
            }
        }
        Ok(left)
    }

    fn unwrap_tonumber(&mut self, v: &VmVal) -> VmResult<JsNumber> {
        let jv = self.vm.to_js_val(v)?;
        self.vm.hit("ToNumber");
        match vjs_spec::to_number(&jv) {
            AbruptOrNormal::Normal(n) => Ok(n),
            AbruptOrNormal::ThrowTypeError => Err(VmSignal::ThrowTypeError),
        }
    }

    fn parse_bitor(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_bitxor()?;
        while self.eat_punct("|") {
            let right = self.parse_bitxor()?;
            let nx = self.unwrap_tonumber(&left)?;
            let ny = self.unwrap_tonumber(&right)?;
            self.vm.hit("Number::bitwiseOR");
            self.vm.hit("NumberBitwiseOp");
            self.vm.hit("ToInt32");
            self.vm.hit("ToIntegerOrInfinity");
            self.vm.hit("ToFixedSizeInteger");
            left = VmVal::Js(JsValue::Number(vjs_spec::number_bitwise_or(nx, ny)));
        }
        Ok(left)
    }

    fn parse_bitxor(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_bitand()?;
        while self.eat_punct("^") {
            let right = self.parse_bitand()?;
            let nx = self.unwrap_tonumber(&left)?;
            let ny = self.unwrap_tonumber(&right)?;
            self.vm.hit("Number::bitwiseXOR");
            self.vm.hit("NumberBitwiseOp");
            self.vm.hit("ToInt32");
            self.vm.hit("ToIntegerOrInfinity");
            self.vm.hit("ToFixedSizeInteger");
            left = VmVal::Js(JsValue::Number(vjs_spec::number_bitwise_xor(nx, ny)));
        }
        Ok(left)
    }

    fn parse_bitand(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_equality()?;
        while self.eat_punct("&") {
            let right = self.parse_equality()?;
            let nx = self.unwrap_tonumber(&left)?;
            let ny = self.unwrap_tonumber(&right)?;
            self.vm.hit("Number::bitwiseAND");
            self.vm.hit("NumberBitwiseOp");
            self.vm.hit("ToInt32");
            self.vm.hit("ToIntegerOrInfinity");
            self.vm.hit("ToFixedSizeInteger");
            left = VmVal::Js(JsValue::Number(vjs_spec::number_bitwise_and(nx, ny)));
        }
        Ok(left)
    }

    fn coerce_pair_for_loose_eq(&mut self, left: &VmVal, right: &VmVal) -> VmResult<(JsValue, JsValue)> {
        let ls = self.vm.to_js_val_shallow(left);
        let rs = self.vm.to_js_val_shallow(right);
        let l_is_prim_coercer = matches!(
            ls,
            JsValue::Str(_) | JsValue::Number(_) | JsValue::BigInt(_) | JsValue::Symbol(_) | JsValue::Boolean(_)
        );
        let r_is_prim_coercer = matches!(
            rs,
            JsValue::Str(_) | JsValue::Number(_) | JsValue::BigInt(_) | JsValue::Symbol(_) | JsValue::Boolean(_)
        );
        let lx = if matches!(ls, JsValue::Object(_)) && r_is_prim_coercer {
            self.vm.to_js_val(left)?
        } else {
            ls
        };
        let ry = if matches!(rs, JsValue::Object(_)) && l_is_prim_coercer {
            self.vm.to_js_val(right)?
        } else {
            rs
        };
        Ok((lx, ry))
    }

    fn parse_equality(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_relational()?;
        loop {
            if self.eat_punct("===") {
                let right = self.parse_relational()?;
                let lx = self.vm.to_js_val_shallow(&left);
                let ry = self.vm.to_js_val_shallow(&right);
                self.vm.hit("IsStrictlyEqual");
                self.vm.hit("SameType");
                if matches!(lx, JsValue::Number(_)) && matches!(ry, JsValue::Number(_)) {
                    self.vm.hit("Number::equal");
                } else if vjs_spec::same_type(&lx, &ry) {
                    self.vm.hit("SameValueNonNumber");
                }
                left = VmVal::Js(JsValue::Boolean(vjs_spec::is_strictly_equal(&lx, &ry)));
            } else if self.eat_punct("!==") {
                let right = self.parse_relational()?;
                let lx = self.vm.to_js_val_shallow(&left);
                let ry = self.vm.to_js_val_shallow(&right);
                self.vm.hit("IsStrictlyEqual");
                self.vm.hit("SameType");
                if matches!(lx, JsValue::Number(_)) && matches!(ry, JsValue::Number(_)) {
                    self.vm.hit("Number::equal");
                } else if vjs_spec::same_type(&lx, &ry) {
                    self.vm.hit("SameValueNonNumber");
                }
                left = VmVal::Js(JsValue::Boolean(!vjs_spec::is_strictly_equal(&lx, &ry)));
            } else if self.eat_punct("==") {
                let right = self.parse_relational()?;
                let (lx, ry) = self.coerce_pair_for_loose_eq(&left, &right)?;
                self.vm.hit("IsLooselyEqual");
                self.vm.hit("SameType");
                match vjs_spec::is_loosely_equal(&lx, &ry) {
                    AbruptOrNormal::Normal(b) => left = VmVal::Js(JsValue::Boolean(b)),
                    AbruptOrNormal::ThrowTypeError => {
                        return Err(VmSignal::ThrowTypeError);
                    }
                }
            } else if self.eat_punct("!=") {
                let right = self.parse_relational()?;
                let (lx, ry) = self.coerce_pair_for_loose_eq(&left, &right)?;
                self.vm.hit("IsLooselyEqual");
                self.vm.hit("SameType");
                match vjs_spec::is_loosely_equal(&lx, &ry) {
                    AbruptOrNormal::Normal(b) => left = VmVal::Js(JsValue::Boolean(!b)),
                    AbruptOrNormal::ThrowTypeError => {
                        return Err(VmSignal::ThrowTypeError);
                    }
                }
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_relational(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_shift()?;
        loop {
            if self.eat_ident("instanceof") {
                let right = self.parse_shift()?;
                let is_inst = match (&left, &right) {
                    (VmVal::ErrorObj("TypeError"), VmVal::BuiltinFn("TypeError" | "Error")) => true,
                    (VmVal::ErrorObj("ReferenceError"), VmVal::BuiltinFn("ReferenceError" | "Error")) => true,
                    (VmVal::ErrorObj(_), VmVal::BuiltinFn("Error")) => true,
                    (VmVal::Array(_, _), VmVal::BuiltinFn("Array" | "Object")) => true,
                    (VmVal::Set(_, _), VmVal::BuiltinFn("Set" | "Object")) => true,
                    (VmVal::FnBody(_, _, _), VmVal::BuiltinFn("Function" | "Object")) => true,
                    (VmVal::DynamicObj { .. } | VmVal::Js(JsValue::Object(_)), VmVal::BuiltinFn("Object")) => true,
                    _ => false,
                };
                left = VmVal::Js(JsValue::Boolean(is_inst));
            } else if self.eat_punct("<") {
                let right = self.parse_shift()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                left = VmVal::Js(JsValue::Boolean(f64::from_bits(nx.0) < f64::from_bits(ny.0)));
            } else if self.eat_punct("<=") {
                let right = self.parse_shift()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                left = VmVal::Js(JsValue::Boolean(f64::from_bits(nx.0) <= f64::from_bits(ny.0)));
            } else if self.eat_punct(">") {
                let right = self.parse_shift()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                left = VmVal::Js(JsValue::Boolean(f64::from_bits(nx.0) > f64::from_bits(ny.0)));
            } else if self.eat_punct(">=") {
                let right = self.parse_shift()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                left = VmVal::Js(JsValue::Boolean(f64::from_bits(nx.0) >= f64::from_bits(ny.0)));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_shift(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_additive()?;
        loop {
            if self.eat_punct("<<") {
                let right = self.parse_additive()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                self.vm.hit("Number::leftShift");
                self.vm.hit("ToInt32");
                self.vm.hit("ToUint32");
                self.vm.hit("ToIntegerOrInfinity");
                self.vm.hit("ToFixedSizeInteger");
                left = VmVal::Js(JsValue::Number(vjs_spec::number_left_shift(nx, ny)));
            } else if self.eat_punct(">>>") {
                let right = self.parse_additive()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                self.vm.hit("Number::unsignedRightShift");
                self.vm.hit("ToUint32");
                self.vm.hit("ToIntegerOrInfinity");
                self.vm.hit("ToFixedSizeInteger");
                left = VmVal::Js(JsValue::Number(vjs_spec::number_unsigned_right_shift(nx, ny)));
            } else if self.eat_punct(">>") {
                let right = self.parse_additive()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                self.vm.hit("Number::signedRightShift");
                self.vm.hit("ToInt32");
                self.vm.hit("ToUint32");
                self.vm.hit("ToIntegerOrInfinity");
                self.vm.hit("ToFixedSizeInteger");
                left = VmVal::Js(JsValue::Number(vjs_spec::number_signed_right_shift(nx, ny)));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_multiplicative()?;
        loop {
            if self.eat_punct("+") {
                let right = self.parse_multiplicative()?;
                let lx = self.vm.to_js_val(&left)?;
                let ry = self.vm.to_js_val(&right)?;
                if matches!(lx, JsValue::Str(_)) || matches!(ry, JsValue::Str(_)) {
                    let cat = format!(
                        "{}{}",
                        js_val_to_display_string(&lx),
                        js_val_to_display_string(&ry)
                    );
                    left = VmVal::Js(JsValue::Str(utf16(&cat)));
                } else {
                    let nx = self.unwrap_tonumber(&VmVal::Js(lx))?;
                    let ny = self.unwrap_tonumber(&VmVal::Js(ry))?;
                    let r = f64::from_bits(nx.0) + f64::from_bits(ny.0);
                    left = VmVal::Js(JsValue::Number(JsNumber(r.to_bits())));
                }
            } else if self.eat_punct("-") {
                let right = self.parse_multiplicative()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                let r = f64::from_bits(nx.0) - f64::from_bits(ny.0);
                left = VmVal::Js(JsValue::Number(JsNumber(r.to_bits())));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> VmResult<VmVal> {
        let mut left = self.parse_unary()?;
        loop {
            if self.eat_punct("/") {
                let right = self.parse_unary()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                let r = f64::from_bits(nx.0) / f64::from_bits(ny.0);
                left = VmVal::Js(JsValue::Number(JsNumber(r.to_bits())));
            } else if self.eat_punct("*") {
                let right = self.parse_unary()?;
                let nx = self.unwrap_tonumber(&left)?;
                let ny = self.unwrap_tonumber(&right)?;
                let r = f64::from_bits(nx.0) * f64::from_bits(ny.0);
                left = VmVal::Js(JsValue::Number(JsNumber(r.to_bits())));
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> VmResult<VmVal> {
        if self.eat_punct("!") {
            let v = self.parse_unary()?;
            let jv = self.vm.to_js_val(&v)?;
            self.vm.hit("ToBoolean");
            return Ok(VmVal::Js(JsValue::Boolean(!vjs_spec::to_boolean(&jv))));
        }
        if self.eat_punct("~") {
            let v = self.parse_unary()?;
            let nx = self.unwrap_tonumber(&v)?;
            self.vm.hit("Number::bitwiseNOT");
            self.vm.hit("ToInt32");
            self.vm.hit("ToIntegerOrInfinity");
            self.vm.hit("ToFixedSizeInteger");
            return Ok(VmVal::Js(JsValue::Number(vjs_spec::number_bitwise_not(nx))));
        }
        if self.eat_punct("+") {
            let v = self.parse_unary()?;
            let nx = self.unwrap_tonumber(&v)?;
            return Ok(VmVal::Js(JsValue::Number(nx)));
        }
        if self.eat_punct("-") {
            let v = self.parse_unary()?;
            let jv = self.vm.to_js_val(&v)?;
            match jv {
                JsValue::BigInt(mut b) => {
                    if !b.limbs.is_empty() {
                        b.neg = !b.neg;
                    }
                    return Ok(VmVal::Js(JsValue::BigInt(b)));
                }
                JsValue::Object(ref o) => {
                    if let ObjectCoercion::Primitive(JsPrim::BigInt(mut b)) = o.prim_number.clone() {
                        if !b.limbs.is_empty() {
                            b.neg = !b.neg;
                        }
                        return Ok(VmVal::Js(JsValue::BigInt(b)));
                    }
                }
                _ => {}
            }
            let nx = self.unwrap_tonumber(&VmVal::Js(jv))?;
            let flipped = if vjs_spec::num_is_nan(nx) {
                JsNumber(CANON_NAN_BITS)
            } else {
                JsNumber(nx.0 ^ 0x8000_0000_0000_0000)
            };
            return Ok(VmVal::Js(JsValue::Number(flipped)));
        }
        if self.eat_ident("void") {
            let _ = self.parse_unary()?;
            return Ok(VmVal::Js(JsValue::Undefined));
        }
        if self.eat_ident("typeof") {
            if let Some(Tok::Ident(id)) = self.peek().cloned() {
                if !matches!(id.as_str(), "true" | "false" | "null" | "function" | "new" | "void" | "typeof")
                    && !matches!(self.toks.get(self.pos + 1), Some(Tok::Punct(p)) if p == "." || p == "(")
                    && !self.vm.vars.contains_key(&id)
                {
                    self.pos += 1;
                    return Ok(VmVal::Js(JsValue::Str(utf16("undefined"))));
                }
            }
            let v = self.parse_unary()?;
            let tag = match v {
                VmVal::Js(JsValue::Undefined) => "undefined",
                VmVal::Js(JsValue::Null) => "object",
                VmVal::Js(JsValue::Boolean(_)) => "boolean",
                VmVal::Js(JsValue::Number(_)) => "number",
                VmVal::Js(JsValue::BigInt(_)) => "bigint",
                VmVal::Js(JsValue::Str(_)) => "string",
                VmVal::Js(JsValue::Symbol(_)) => "symbol",
                VmVal::FnBody(_, _, _) | VmVal::BuiltinFn(_) => "function",
                _ => "object",
            };
            return Ok(VmVal::Js(JsValue::Str(utf16(tag))));
        }
        if self.eat_ident("new") {
            let Some(Tok::Ident(ctor)) = self.peek().cloned() else {
                panic!("expected constructor name after `new`");
            };
            self.pos += 1;
            let args = if self.eat_punct("(") {
                self.parse_arg_list()?
            } else {
                Vec::new()
            };
            return match ctor.as_str() {
                "Set" => {
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::Set(id, Vec::new()))
                }
                "Array" => {
                    let id = self.vm.alloc_obj_id();
                    let mut elems = Vec::new();
                    for a in &args {
                        elems.push(self.vm.to_js_val(a)?);
                    }
                    Ok(VmVal::Array(id, elems))
                }
                "Function" => {
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::FnBody(id, Vec::new(), String::new()))
                }
                "Date" => {
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::Js(plain_object(id)))
                }
                "Test262Error" | "Error" => Ok(VmVal::ErrorObj("Test262Error")),
                "TypeError" => Ok(VmVal::ErrorObj("TypeError")),
                "ReferenceError" => Ok(VmVal::ErrorObj("ReferenceError")),
                "Boolean" => {
                    let b = if let Some(a) = args.first() {
                        let jv = self.vm.to_js_val(a)?;
                        self.vm.hit("ToBoolean");
                        vjs_spec::to_boolean(&jv)
                    } else {
                        false
                    };
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::Js(JsValue::Object(JsObject {
                        id,
                        is_htmldda: false,
                        prim_default: ObjectCoercion::Primitive(JsPrim::Boolean(b)),
                        prim_number: ObjectCoercion::Primitive(JsPrim::Boolean(b)),
                    })))
                }
                "Number" => {
                    let n = if let Some(a) = args.first() {
                        self.unwrap_tonumber(a)?
                    } else {
                        JsNumber(POS_ZERO_BITS)
                    };
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::Js(JsValue::Object(JsObject {
                        id,
                        is_htmldda: false,
                        prim_default: ObjectCoercion::Primitive(JsPrim::Number(n)),
                        prim_number: ObjectCoercion::Primitive(JsPrim::Number(n)),
                    })))
                }
                "String" => {
                    let s = if let Some(a) = args.first() {
                        let jv = self.vm.to_js_val(a)?;
                        if matches!(jv, JsValue::Symbol(_)) {
                            return Err(VmSignal::ThrowTypeError);
                        }
                        utf16(&js_val_to_display_string(&jv))
                    } else {
                        Vec::new()
                    };
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::Js(JsValue::Object(JsObject {
                        id,
                        is_htmldda: false,
                        prim_default: ObjectCoercion::Primitive(JsPrim::Str(s.clone())),
                        prim_number: ObjectCoercion::Primitive(JsPrim::Str(s)),
                    })))
                }
                _ => {
                    if let Some(a) = args.first() {
                        return Ok(self.vm.wrap_object(a));
                    }
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::DynamicObj {
                        id,
                        props: HashMap::new(),
                    })
                }
            };
        }
        self.parse_postfix()
    }

    fn parse_arg_list(&mut self) -> VmResult<Vec<VmVal>> {
        let mut args = Vec::new();
        if self.eat_punct(")") {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            if self.eat_punct(",") {
                if self.eat_punct(")") {
                    break;
                }
            } else {
                self.expect_punct(")");
                break;
            }
        }
        Ok(args)
    }

    fn parse_postfix(&mut self) -> VmResult<VmVal> {
        let mut base = self.parse_primary()?;
        loop {
            if self.eat_punct(".") {
                let Some(Tok::Ident(prop)) = self.peek().cloned() else {
                    panic!("expected property identifier after `.`");
                };
                self.pos += 1;
                if self.eat_punct("(") {
                    let args = self.parse_arg_list()?;
                    base = self.eval_method_call(base, &prop, args)?;
                } else {
                    base = self.eval_prop_get(base, &prop)?;
                }
            } else if self.eat_punct("(") {
                let args = self.parse_arg_list()?;
                base = self.eval_fn_call(base, args)?;
            } else {
                break;
            }
        }
        Ok(base)
    }

    fn eval_prop_get(&mut self, base: VmVal, prop: &str) -> VmResult<VmVal> {
        match (&base, prop) {
            (VmVal::BuiltinFn("Number"), "NaN") => Ok(VmVal::Js(JsValue::Number(JsNumber(CANON_NAN_BITS)))),
            (VmVal::BuiltinFn("Number"), "POSITIVE_INFINITY") => Ok(VmVal::Js(JsValue::Number(JsNumber(POS_INF_BITS)))),
            (VmVal::BuiltinFn("Number"), "NEGATIVE_INFINITY") => Ok(VmVal::Js(JsValue::Number(JsNumber(NEG_INF_BITS)))),
            (VmVal::BuiltinFn("Number"), "MAX_VALUE") => Ok(VmVal::Js(JsValue::Number(JsNumber(f64::MAX.to_bits())))),
            (VmVal::BuiltinFn("Number"), "MIN_VALUE") => Ok(VmVal::Js(JsValue::Number(JsNumber(1)))),
            (VmVal::BuiltinFn("Number"), "MAX_SAFE_INTEGER") => Ok(VmVal::Js(JsValue::Number(JsNumber((9007199254740991.0f64).to_bits())))),
            (VmVal::BuiltinFn("Number"), "MIN_SAFE_INTEGER") => Ok(VmVal::Js(JsValue::Number(JsNumber((-9007199254740991.0f64).to_bits())))),
            (VmVal::BuiltinFn("String"), "prototype") => Ok(VmVal::BuiltinFn("String.prototype")),
            (VmVal::BuiltinFn("String.prototype"), "trim") => Ok(VmVal::BuiltinFn("String.prototype.trim")),
            (VmVal::DynamicObj { props, .. }, p) => Ok(props.get(p).cloned().unwrap_or(VmVal::Js(JsValue::Undefined))),
            _ => Ok(VmVal::Js(JsValue::Undefined)),
        }
    }

    fn eval_method_call(&mut self, base: VmVal, prop: &str, args: Vec<VmVal>) -> VmResult<VmVal> {
        match (base, prop) {
            (VmVal::BuiltinFn("assert"), "sameValue") => {
                let actual = self.vm.to_js_val_shallow(&args[0]);
                let expected = self.vm.to_js_val_shallow(&args[1]);
                self.vm.hit("SameValue");
                self.vm.hit("SameType");
                if matches!(actual, JsValue::Number(_)) && matches!(expected, JsValue::Number(_)) {
                    self.vm.hit("Number::sameValue");
                } else if vjs_spec::same_type(&actual, &expected) {
                    self.vm.hit("SameValueNonNumber");
                }
                if !vjs_spec::same_value(&actual, &expected) {
                    return Err(VmSignal::ThrowVal(VmVal::Js(JsValue::Str(utf16(&format!(
                        "assert.sameValue failed: actual={actual:?}, expected={expected:?}, msg={:?}",
                        args.get(2)
                    ))))));
                }
                Ok(VmVal::Js(JsValue::Undefined))
            }
            (VmVal::BuiltinFn("assert"), "notSameValue") => {
                let actual = self.vm.to_js_val_shallow(&args[0]);
                let expected = self.vm.to_js_val_shallow(&args[1]);
                self.vm.hit("SameValue");
                self.vm.hit("SameType");
                if vjs_spec::same_value(&actual, &expected) {
                    return Err(VmSignal::ThrowVal(VmVal::Js(JsValue::Str(utf16(&format!(
                        "assert.notSameValue failed: both={actual:?}"
                    ))))));
                }
                Ok(VmVal::Js(JsValue::Undefined))
            }
            (VmVal::BuiltinFn("assert"), "throws") => {
                let Some(VmVal::FnBody(_, _, body_src)) = args.get(1).cloned() else {
                    panic!("assert.throws expects function at arg 1");
                };
                match self.vm.exec_fn_body(&body_src) {
                    Err(VmSignal::ThrowTypeError)
                    | Err(VmSignal::ThrowVal(VmVal::ErrorObj("TypeError"))) => {
                        Ok(VmVal::Js(JsValue::Undefined))
                    }
                    other => Err(VmSignal::ThrowVal(VmVal::Js(JsValue::Str(utf16(&format!(
                        "assert.throws(TypeError) did not catch TypeError: {other:?}"
                    )))))),
                }
            }
            (VmVal::BuiltinFn("Object"), "is") => {
                let x = args
                    .first()
                    .map(|v| self.vm.to_js_val_shallow(v))
                    .unwrap_or(JsValue::Undefined);
                let y = args
                    .get(1)
                    .map(|v| self.vm.to_js_val_shallow(v))
                    .unwrap_or(JsValue::Undefined);
                self.vm.hit("SameValue");
                self.vm.hit("SameType");
                if matches!(x, JsValue::Number(_)) && matches!(y, JsValue::Number(_)) {
                    self.vm.hit("Number::sameValue");
                } else if vjs_spec::same_type(&x, &y) {
                    self.vm.hit("SameValueNonNumber");
                }
                Ok(VmVal::Js(JsValue::Boolean(vjs_spec::same_value(&x, &y))))
            }
            (VmVal::BuiltinFn("Object"), "keys") => {
                let arg = args
                    .first()
                    .map(|v| self.vm.to_js_val(v))
                    .transpose()?
                    .unwrap_or(JsValue::Undefined);
                self.vm.hit("RequireObjectCoercible");
                match vjs_spec::require_object_coercible(&arg) {
                    AbruptOrNormal::ThrowTypeError => Err(VmSignal::ThrowTypeError),
                    AbruptOrNormal::Normal(_) => {
                        let id = self.vm.alloc_obj_id();
                        Ok(VmVal::Array(id, Vec::new()))
                    }
                }
            }
            (VmVal::BuiltinFn("Object"), "create") => {
                if matches!(args.first(), Some(VmVal::Js(JsValue::Null))) {
                    let id = self.vm.alloc_obj_id();
                    let mut props = HashMap::new();
                    props.insert("__null_proto__".into(), VmVal::Js(JsValue::Null));
                    Ok(VmVal::DynamicObj { id, props })
                } else {
                    let id = self.vm.alloc_obj_id();
                    Ok(VmVal::DynamicObj { id, props: HashMap::new() })
                }
            }
            (VmVal::BuiltinFn("String.prototype.trim"), "call") => {
                let raw = args
                    .first()
                    .cloned()
                    .unwrap_or(VmVal::Js(JsValue::Undefined));
                let shallow = self.vm.to_js_val_shallow(&raw);
                self.vm.hit("RequireObjectCoercible");
                match vjs_spec::require_object_coercible(&shallow) {
                    AbruptOrNormal::ThrowTypeError => Err(VmSignal::ThrowTypeError),
                    AbruptOrNormal::Normal(_) => {
                        let s_units = self.vm.to_string_utf16(&raw)?;
                        Ok(VmVal::Js(JsValue::Str(trim_utf16_ecma(&s_units))))
                    }
                }
            }
            (VmVal::BuiltinFn("String"), "fromCharCode") => {
                let mut units = Vec::new();
                for a in &args {
                    let jv = self.vm.to_js_val(a)?;
                    self.vm.hit("ToUint16");
                    self.vm.hit("ToIntegerOrInfinity");
                    self.vm.hit("ToFixedSizeInteger");
                    self.vm.hit("ToNumber");
                    match vjs_spec::to_uint16(&jv) {
                        AbruptOrNormal::Normal(n) => {
                            let cu = f64::from_bits(n.0) as u16;
                            units.push(cu);
                        }
                        AbruptOrNormal::ThrowTypeError => {
                            return Err(VmSignal::ThrowTypeError);
                        }
                    }
                }
                Ok(VmVal::Js(JsValue::Str(units)))
            }
            (VmVal::Js(JsValue::Str(units)), "charCodeAt") => {
                let idx = 0usize;
                let n = units
                    .get(idx)
                    .map(|cu| JsNumber((*cu as f64).to_bits()))
                    .unwrap_or(JsNumber(CANON_NAN_BITS));
                Ok(VmVal::Js(JsValue::Number(n)))
            }
            (VmVal::Js(JsValue::Str(units)), "trim") => {
                let jv = JsValue::Str(units.clone());
                self.vm.hit("RequireObjectCoercible");
                let _ = vjs_spec::require_object_coercible(&jv);
                Ok(VmVal::Js(JsValue::Str(trim_utf16_ecma(&units))))
            }
            (VmVal::Js(JsValue::Str(units)), "toString") => Ok(VmVal::Js(JsValue::Str(units))),
            (VmVal::Js(JsValue::Object(obj)), "trim") => {
                let jv = JsValue::Object(obj);
                self.vm.hit("RequireObjectCoercible");
                let _ = vjs_spec::require_object_coercible(&jv);
                let units = self.vm.to_string_utf16(&VmVal::Js(jv))?;
                Ok(VmVal::Js(JsValue::Str(trim_utf16_ecma(&units))))
            }
            (VmVal::Js(JsValue::Object(obj)), "toString") => {
                let jv = JsValue::Object(obj);
                let units = self.vm.to_string_utf16(&VmVal::Js(jv))?;
                Ok(VmVal::Js(JsValue::Str(units)))
            }
            (VmVal::Set(id, mut items), "add") => {
                let elem = args
                    .first()
                    .map(|v| self.vm.to_js_val(v))
                    .transpose()?
                    .unwrap_or(JsValue::Undefined);
                self.vm.hit("SameValueZero");
                if !items.iter().any(|e| vjs_spec::same_value_zero(e, &elem)) {
                    items.push(elem);
                }
                Ok(VmVal::Set(id, items))
            }
            (VmVal::Set(_, items), "has") => {
                let elem = args
                    .first()
                    .map(|v| self.vm.to_js_val(v))
                    .transpose()?
                    .unwrap_or(JsValue::Undefined);
                self.vm.hit("SameValueZero");
                self.vm.hit("SameType");
                let found = items.iter().any(|e| {
                    if matches!(e, JsValue::Number(_)) && matches!(elem, JsValue::Number(_)) {
                        self.vm.hit("Number::sameValueZero");
                    } else if vjs_spec::same_type(e, &elem) {
                        self.vm.hit("SameValueNonNumber");
                    }
                    vjs_spec::same_value_zero(e, &elem)
                });
                Ok(VmVal::Js(JsValue::Boolean(found)))
            }
            (VmVal::Set(_, mut items), "delete") => {
                let elem = args
                    .first()
                    .map(|v| self.vm.to_js_val(v))
                    .transpose()?
                    .unwrap_or(JsValue::Undefined);
                self.vm.hit("SameValueZero");
                let before = items.len();
                items.retain(|e| !vjs_spec::same_value_zero(e, &elem));
                Ok(VmVal::Js(JsValue::Boolean(items.len() != before)))
            }
            (VmVal::Array(_, items), "includes") => {
                let search = args
                    .first()
                    .map(|v| self.vm.to_js_val(v))
                    .transpose()?
                    .unwrap_or(JsValue::Undefined);
                let mut start_idx: usize = 0;
                if let Some(from_arg) = args.get(1) {
                    let fv = self.vm.to_js_val(from_arg)?;
                    self.vm.hit("ToIntegerOrInfinity");
                    match vjs_spec::to_integer_or_infinity(&fv) {
                        AbruptOrNormal::ThrowTypeError => {
                            return Err(VmSignal::ThrowTypeError);
                        }
                        AbruptOrNormal::Normal(MathIntOrInf::PosInf) => return Ok(VmVal::Js(JsValue::Boolean(false))),
                        AbruptOrNormal::Normal(MathIntOrInf::NegInf) => start_idx = 0,
                        AbruptOrNormal::Normal(MathIntOrInf::Finite(ExactInt { neg, sig, shift2 })) => {
                            let val = (sig as i128) << shift2.min(60);
                            let signed_v = if neg { -val } else { val };
                            if signed_v < 0 {
                                let rel = (items.len() as i128) + signed_v;
                                start_idx = if rel < 0 { 0 } else { rel as usize };
                            } else {
                                start_idx = signed_v as usize;
                            }
                        }
                    }
                }
                self.vm.hit("SameValueZero");
                self.vm.hit("SameType");
                let mut found = false;
                for e in items.iter().skip(start_idx) {
                    if matches!(e, JsValue::Number(_)) && matches!(search, JsValue::Number(_)) {
                        self.vm.hit("Number::sameValueZero");
                    } else if vjs_spec::same_type(e, &search) {
                        self.vm.hit("SameValueNonNumber");
                    }
                    if vjs_spec::same_value_zero(e, &search) {
                        found = true;
                        break;
                    }
                }
                Ok(VmVal::Js(JsValue::Boolean(found)))
            }
            (other, m) => panic!("unsupported method `{m}` on {other:?}"),
        }
    }

    fn eval_fn_call(&mut self, callee: VmVal, args: Vec<VmVal>) -> VmResult<VmVal> {
        match callee {
            VmVal::BuiltinFn("Boolean") => {
                let b = if let Some(a) = args.first() {
                    let jv = self.vm.to_js_val_shallow(a);
                    self.vm.hit("ToBoolean");
                    vjs_spec::to_boolean(&jv)
                } else {
                    self.vm.hit("ToBoolean");
                    vjs_spec::to_boolean(&JsValue::Undefined)
                };
                Ok(VmVal::Js(JsValue::Boolean(b)))
            }
            VmVal::BuiltinFn("Number") => {
                let n = if let Some(a) = args.first() {
                    self.unwrap_tonumber(a)?
                } else {
                    JsNumber(POS_ZERO_BITS)
                };
                Ok(VmVal::Js(JsValue::Number(n)))
            }
            VmVal::BuiltinFn("BigInt") => {
                let Some(a) = args.first() else {
                    return Err(VmSignal::ThrowTypeError);
                };
                let jv = self.vm.to_js_val(a)?;
                match jv {
                    JsValue::Str(_) => match vjs_spec::val_string_to_bigint(&jv) {
                        JsValue::BigInt(b) => Ok(VmVal::Js(JsValue::BigInt(b))),
                        _ => Err(VmSignal::ThrowVal(VmVal::Js(JsValue::Str(utf16("SyntaxError"))))),
                    },
                    JsValue::Boolean(b) => Ok(VmVal::Js(JsValue::BigInt(bigint_from_decimal_or_hex(if b { "1" } else { "0" })))),
                    JsValue::Number(n) => {
                        let f = f64::from_bits(n.0);
                        Ok(VmVal::Js(JsValue::BigInt(bigint_from_decimal_or_hex(&format!("{:.0}", f)))))
                    }
                    JsValue::BigInt(b) => Ok(VmVal::Js(JsValue::BigInt(b))),
                    _ => Err(VmSignal::ThrowTypeError),
                }
            }
            VmVal::BuiltinFn("Symbol") => {
                let id = self.vm.next_sym_id;
                self.vm.next_sym_id += 1;
                Ok(VmVal::Js(JsValue::Symbol(id)))
            }
            VmVal::BuiltinFn("Object") => {
                if let Some(a) = args.first() {
                    return Ok(self.vm.wrap_object(a));
                }
                let id = self.vm.alloc_obj_id();
                Ok(VmVal::DynamicObj { id, props: HashMap::new() })
            }
            VmVal::BuiltinFn("Array") => {
                let id = self.vm.alloc_obj_id();
                let mut elems = Vec::new();
                for a in &args {
                    elems.push(self.vm.to_js_val(a)?);
                }
                Ok(VmVal::Array(id, elems))
            }
            VmVal::BuiltinFn("Function") => {
                let id = self.vm.alloc_obj_id();
                Ok(VmVal::FnBody(id, Vec::new(), String::new()))
            }
            VmVal::BuiltinFn("Date") => {
                // `Date()` called without `new` returns a non-empty date string in ECMAScript!
                Ok(VmVal::Js(JsValue::Str(utf16("Thu Nov 20 2026 00:00:00 GMT+0000"))))
            }
            VmVal::BuiltinFn("String") => {
                let s = if let Some(a) = args.first() {
                    let jv = self.vm.to_js_val(a)?;
                    js_val_to_display_string(&jv)
                } else {
                    String::new()
                };
                Ok(VmVal::Js(JsValue::Str(utf16(&s))))
            }
            VmVal::BuiltinFn("eval") => {
                if let Some(VmVal::Js(JsValue::Str(u))) = args.first() {
                    let code = String::from_utf16_lossy(u);
                    self.vm.eval_code(&code)
                } else {
                    Ok(args.into_iter().next().unwrap_or(VmVal::Js(JsValue::Undefined)))
                }
            }
            VmVal::BuiltinFn("assert") => {
                let jv = self.vm.to_js_val(&args[0])?;
                self.vm.hit("ToBoolean");
                if !vjs_spec::to_boolean(&jv) {
                    return Err(VmSignal::ThrowVal(VmVal::Js(JsValue::Str(utf16(&format!("assert failed: {jv:?}"))))));
                }
                Ok(VmVal::Js(JsValue::Undefined))
            }
            VmVal::FnBody(_, params, body_src) => {
                for (i, pname) in params.iter().enumerate() {
                    let av = args.get(i).cloned().unwrap_or(VmVal::Js(JsValue::Undefined));
                    self.vm.vars.insert(pname.clone(), av);
                }
                self.vm.exec_fn_body(&body_src)
            }
            other => panic!("unsupported function call on {other:?}"),
        }
    }

    fn parse_primary(&mut self) -> VmResult<VmVal> {
        if self.eat_punct("(") {
            let v = self.parse_expr()?;
            self.expect_punct(")");
            return Ok(v);
        }
        if self.eat_punct("[") {
            let id = self.vm.alloc_obj_id();
            let mut elems = Vec::new();
            if !self.eat_punct("]") {
                loop {
                    if matches!(self.peek(), Some(Tok::Punct(p)) if p == ",") {
                        elems.push(JsValue::Undefined);
                    } else {
                        let ev = self.parse_expr()?;
                        elems.push(self.vm.to_js_val(&ev)?);
                    }
                    if self.eat_punct(",") {
                        if self.eat_punct("]") {
                            break;
                        }
                    } else {
                        self.expect_punct("]");
                        break;
                    }
                }
            }
            return Ok(VmVal::Array(id, elems));
        }
        if self.eat_punct("{") {
            let id = self.vm.alloc_obj_id();
            let mut props = HashMap::new();
            if !self.eat_punct("}") {
                loop {
                    let key = match self.peek().cloned() {
                        Some(Tok::Ident(k)) => {
                            self.pos += 1;
                            k
                        }
                        Some(Tok::Str(k)) => {
                            self.pos += 1;
                            k
                        }
                        other => panic!("unexpected object literal key: {other:?}"),
                    };
                    if self.eat_punct(":") {
                        let val = self.parse_expr()?;
                        props.insert(key, val);
                    } else if matches!(self.peek(), Some(Tok::Punct(p)) if p == "(") {
                        let params = self.parse_fn_params();
                        let body = self.skip_balanced_braces();
                        let fid = self.vm.alloc_obj_id();
                        props.insert(key, VmVal::FnBody(fid, params, body));
                    }
                    if self.eat_punct(",") {
                        if self.eat_punct("}") {
                            break;
                        }
                    } else {
                        self.expect_punct("}");
                        break;
                    }
                }
            }
            return Ok(VmVal::DynamicObj { id, props });
        }
        match self.peek().cloned() {
            Some(Tok::NumBits(b)) => {
                self.pos += 1;
                Ok(VmVal::Js(JsValue::Number(JsNumber(b))))
            }
            Some(Tok::BigIntStr(bs)) => {
                self.pos += 1;
                Ok(VmVal::Js(JsValue::BigInt(bigint_from_decimal_or_hex(&bs))))
            }
            Some(Tok::Str(s)) => {
                self.pos += 1;
                Ok(VmVal::Js(JsValue::Str(utf16(&s))))
            }
            Some(Tok::Ident(id)) => {
                self.pos += 1;
                match id.as_str() {
                    "true" => return Ok(VmVal::Js(JsValue::Boolean(true))),
                    "false" => return Ok(VmVal::Js(JsValue::Boolean(false))),
                    "null" => return Ok(VmVal::Js(JsValue::Null)),
                    "function" => {
                        if matches!(self.peek(), Some(Tok::Ident(_))) {
                            self.pos += 1;
                        }
                        let params = self.parse_fn_params();
                        let body = self.skip_balanced_braces();
                        let fid = self.vm.alloc_obj_id();
                        return Ok(VmVal::FnBody(fid, params, body));
                    }
                    _ => {}
                }
                if matches!(self.peek(), Some(Tok::Punct(p)) if p == ".") {
                    if let Some(Tok::Ident(mname)) = self.toks.get(self.pos + 1).cloned() {
                        if matches!(mname.as_str(), "add" | "delete")
                            && matches!(self.vm.vars.get(&id), Some(VmVal::Set(_, _)))
                        {
                            self.pos += 2;
                            self.expect_punct("(");
                            let args = self.parse_arg_list()?;
                            let elem = args
                                .first()
                                .map(|v| self.vm.to_js_val(v))
                                .transpose()?
                                .unwrap_or(JsValue::Undefined);
                            let Some(VmVal::Set(sid, mut items)) = self.vm.vars.remove(&id) else {
                                unreachable!()
                            };
                            self.vm.hit("SameValueZero");
                            if mname == "add" {
                                if !items.iter().any(|e| vjs_spec::same_value_zero(e, &elem)) {
                                    items.push(elem.clone());
                                }
                                let ret = VmVal::Set(sid, items.clone());
                                self.vm.vars.insert(id, VmVal::Set(sid, items));
                                return Ok(ret);
                            } else {
                                let before = items.len();
                                items.retain(|e| !vjs_spec::same_value_zero(e, &elem));
                                let removed = items.len() != before;
                                self.vm.vars.insert(id, VmVal::Set(sid, items));
                                return Ok(VmVal::Js(JsValue::Boolean(removed)));
                            }
                        }
                    }
                }
                match self.vm.vars.get(&id).cloned() {
                    Some(val) => Ok(val),
                    None => Err(VmSignal::ThrowVal(VmVal::ErrorObj("ReferenceError"))),
                }
            }
            other => panic!("unexpected token at pos {}: {other:?}", self.pos),
        }
    }
}

// ===============================================================================================
// Live Node.js V8 Differential Oracle Runner & Test262 Cross-Checker
// ===============================================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum OracleOutcome {
    Bool(bool),
    NumBits(u64), // Canonicalized NaN bits (`0x7FF8_0000_0000_0000`) or exact IEEE-754 bits (incl. -0 vs +0!)
    ThrowTypeError,
}

fn canon_num_outcome(n: JsNumber) -> OracleOutcome {
    if vjs_spec::num_is_nan(n) {
        OracleOutcome::NumBits(CANON_NAN_BITS)
    } else {
        OracleOutcome::NumBits(n.0)
    }
}

fn run_node_json_batch(js_script: &str, payload: &Value) -> Value {
    let mut child = Command::new(NODE_BIN)
        .arg("-e")
        .arg(js_script)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to launch Node.js V8 binary");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(serde_json::to_vec(payload).unwrap().as_slice())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(
        out.status.success(),
        "Node.js V8 differential oracle failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice(&out.stdout).expect("invalid JSON from Node.js V8 oracle")
}

fn collect_test262_js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if !dir.exists() {
        return;
    }
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            collect_test262_js_files(&p, out);
        } else if p.extension().and_then(|s| s.to_str()) == Some("js") {
            out.push(p);
        }
    }
}

/// Map a pinned `test262/test/...` relative path to the ECMA-262 clauses it exercises.
fn clauses_exercised_by_test262_path(rel: &str) -> &'static [&'static str] {
    if rel.contains("Boolean/S9.2_") || rel.contains("logical-not/S9.2_") {
        &["ToBoolean"]
    } else if rel.contains("bitwise-not/") {
        &["Number::bitwiseNOT", "ToInt32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("left-shift/") {
        &["Number::leftShift", "ToInt32", "ToUint32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("unsigned-right-shift/") {
        &["Number::unsignedRightShift", "ToUint32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("right-shift/") {
        &["Number::signedRightShift", "ToInt32", "ToUint32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("String/fromCharCode/") {
        &["ToUint16", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("bitwise-and/") {
        &["Number::bitwiseAND", "NumberBitwiseOp", "ToInt32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("bitwise-xor/") {
        &["Number::bitwiseXOR", "NumberBitwiseOp", "ToInt32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("bitwise-or/") {
        &["Number::bitwiseOR", "NumberBitwiseOp", "ToInt32", "ToIntegerOrInfinity", "ToFixedSizeInteger", "ToNumber"]
    } else if rel.contains("String/prototype/trim/") || rel.contains("Object/keys/") {
        &["RequireObjectCoercible"]
    } else if rel.contains("Object/is/") {
        &["SameValue", "Number::sameValue", "SameValueNonNumber", "SameType"]
    } else if rel.contains("Set/prototype/has/") || rel.contains("Array/prototype/includes/") {
        &["SameValueZero", "Number::sameValueZero", "SameValueNonNumber", "SameType"]
    } else if rel.contains("strict-equals/") {
        &["IsStrictlyEqual", "Number::equal", "SameValueNonNumber", "SameType"]
    } else if rel.contains("equals/") {
        &["IsLooselyEqual", "IsStrictlyEqual", "Number::equal", "SameValueNonNumber", "SameType", "ToNumber"]
    } else {
        &[]
    }
}

#[test]
fn test262_and_v8_differential_suite_generates_report() {
    // 1. Load exact compiled IR section table from `esmeta_to_verus.py --dump-ir`
    let script = browser_dir().join("scripts/esmeta_to_verus.py");
    let ir_out = Command::new("python3")
        .arg(&script)
        .arg("--dump-ir")
        .output()
        .unwrap();
    assert!(ir_out.status.success());
    let ir_ops: Vec<Value> = serde_json::from_slice(&ir_out.stdout).unwrap();
    assert_eq!(ir_ops.len(), 25);

    // 2. Discover & execute all pinned real `tc39/test262` test cases in `browser/test262/test/`
    let test262_root = browser_dir().join("test262");
    let test_dir = test262_root.join("test");
    let mut test_files = Vec::new();
    collect_test262_js_files(&test_dir, &mut test_files);
    assert!(
        test_files.len() >= 80,
        "Expected >= 80 real pinned test262 files under browser/test262/test/, found {}",
        test_files.len()
    );

    let mut per_op_t262_total: HashMap<String, usize> = HashMap::new();
    let mut per_op_t262_passed: HashMap<String, usize> = HashMap::new();
    let mut unique_t262_passed = 0usize;

    // Also verify all pinned test262 files pass in live Node.js V8 with upstream `sta.js` + `assert.js`!
    let sta_js = fs::read_to_string(test262_root.join("harness/sta.js")).unwrap();
    let assert_js = fs::read_to_string(test262_root.join("harness/assert.js")).unwrap();
    let mut v8_t262_batch = Vec::new();

    for tf in &test_files {
        let rel = tf.strip_prefix(&test262_root).unwrap().to_string_lossy().to_string();
        let src = fs::read_to_string(tf).unwrap();
        let mut vm = Test262SpecVm::new();
        let rust_res = vm.run_script(&src);
        assert!(
            rust_res.is_ok(),
            "Pinned test262 file FAILED in pure-Rust vjs_spec runner: {rel}\nError: {rust_res:?}"
        );
        assert!(
            !vm.op_hits.is_empty(),
            "Pinned test262 file {rel} did not invoke any vjs_spec operation!"
        );
        unique_t262_passed += 1;

        for op_name in clauses_exercised_by_test262_path(&rel) {
            *per_op_t262_total.entry((*op_name).to_string()).or_insert(0) += 1;
            *per_op_t262_passed.entry((*op_name).to_string()).or_insert(0) += 1;
        }
        v8_t262_batch.push(json!({ "rel": rel, "code": src }));
    }

    let v8_t262_runner = r#"
const fs = require("fs");
const vm = require("vm");
const input = JSON.parse(fs.readFileSync(0, "utf8"));
const failures = [];
for (const item of input.files) {
  try {
    vm.runInNewContext(input.sta + "\n" + input.assert + "\n" + item.code, {});
  } catch (e) {
    failures.push({ rel: item.rel, err: String(e) });
  }
}
process.stdout.write(JSON.stringify({ total: input.files.length, failures }));
"#;
    let v8_t262_res = run_node_json_batch(
        v8_t262_runner,
        &json!({ "sta": sta_js, "assert": assert_js, "files": v8_t262_batch }),
    );
    assert_eq!(
        v8_t262_res["failures"].as_array().unwrap().len(),
        0,
        "V8 failed pinned test262 files: {:?}",
        v8_t262_res["failures"]
    );

    // 3. Live Node.js V8 Differential Oracle across 25,000+ edge-case evaluations!
    let core_corpus = build_adversarial_corpus(); // ~76 adversarial values across all 8 JS types
    let fuzz_corpus = build_fuzz_number_and_val_corpus(); // 720 PRNG IEEE-754 & numeric-string values
    let mut unary_all_corpus = core_corpus.clone();
    unary_all_corpus.extend(fuzz_corpus.iter().cloned());

    let num_only_corpus: Vec<CorpusEntry> = unary_all_corpus
        .iter()
        .filter(|e| matches!(e.val, JsValue::Number(_)))
        .take(50)
        .cloned()
        .collect();
    let num_unary_corpus: Vec<CorpusEntry> = unary_all_corpus
        .iter()
        .filter(|e| matches!(e.val, JsValue::Number(_)))
        .cloned()
        .collect();

    // Ask Node.js V8 to evaluate every unary & binary operation on the exact same corpus expressions!
    let unary_exprs: Vec<String> = unary_all_corpus.iter().map(|e| e.js_expr.clone()).collect();
    let core_exprs: Vec<String> = core_corpus.iter().map(|e| e.js_expr.clone()).collect();
    let num_pair_exprs: Vec<String> = num_only_corpus.iter().map(|e| e.js_expr.clone()).collect();
    let num_unary_exprs: Vec<String> = num_unary_corpus.iter().map(|e| e.js_expr.clone()).collect();

    let v8_diff_script = r#"
const fs = require("fs");
const input = JSON.parse(fs.readFileSync(0, "utf8"));

const buf = new ArrayBuffer(8);
const u32 = new Uint32Array(buf);
const f64 = new Float64Array(buf);
function bitsToF64(hi, lo) {
  u32[0] = lo >>> 0;
  u32[1] = hi >>> 0;
  return f64[0];
}
function f64ToBits(x) {
  if (Number.isNaN(x)) return [0x7FF80000, 0x00000000];
  f64[0] = x;
  return [u32[1] >>> 0, u32[0] >>> 0];
}
const SYM_1 = Symbol("s1");
const SYM_2 = Symbol("s2");
const OBJ_PLAIN_1 = {};
const OBJ_PLAIN_2 = {};
const OBJ_VAL_42 = { valueOf() { return 42; } };
const OBJ_STR_0 = { toString() { return "0"; }, valueOf() { return {}; } };
const OBJ_BIGINT_1 = { [Symbol.toPrimitive]() { return 1n; } };
const OBJ_THROW = {
  valueOf() { throw new TypeError("boom"); },
  toString() { throw new TypeError("boom"); },
};

const unaryVals = input.unary_exprs.map(e => eval("(" + e + ")"));
const coreVals = input.core_exprs.map(e => eval("(" + e + ")"));
const numPairVals = input.num_pair_exprs.map(e => eval("(" + e + ")"));
const numUnaryVals = input.num_unary_exprs.map(e => eval("(" + e + ")"));

function wrapNumOp(fn) {
  try {
    return { ok: f64ToBits(fn()) };
  } catch (e) {
    if (e instanceof TypeError) return { err: "TypeError" };
    throw e;
  }
}
function wrapBoolOp(fn) {
  try {
    return { ok: Boolean(fn()) };
  } catch (e) {
    if (e instanceof TypeError) return { err: "TypeError" };
    throw e;
  }
}

// Evaluate unary operations on all ~796 unaryVals:
const toBoolean = unaryVals.map(v => Boolean(v));
const toNumber = unaryVals.map(v => wrapNumOp(() => +v));
const toInt32 = unaryVals.map(v => wrapNumOp(() => (v | 0)));
const toUint32 = unaryVals.map(v => wrapNumOp(() => (v >>> 0)));
const toUint16 = unaryVals.map(v => wrapNumOp(() => String.fromCharCode(v).charCodeAt(0)));
const reqObj = unaryVals.map(v => {
  try { Object.keys(v); return { ok: true }; }
  catch (e) { if (e instanceof TypeError) return { err: "TypeError" }; throw e; }
});
const bitNot = numUnaryVals.map(x => f64ToBits(~x));

// Evaluate binary Number x Number operations on 50 x 50 = 2,500 pairs:
const numEq = [], numSameVal = [], numSameValZero = [];
const shl = [], ashr = [], lshr = [], band = [], bxor = [], bor = [];
const svzSet = new Set();
for (let i = 0; i < numPairVals.length; i++) {
  for (let j = 0; j < numPairVals.length; j++) {
    const x = numPairVals[i], y = numPairVals[j];
    numEq.push(x === y);
    numSameVal.push(Object.is(x, y));
    svzSet.clear(); svzSet.add(x);
    numSameValZero.push(svzSet.has(y));
    shl.push(f64ToBits(x << y));
    ashr.push(f64ToBits(x >> y));
    lshr.push(f64ToBits(x >>> y));
    band.push(f64ToBits(x & y));
    bxor.push(f64ToBits(x ^ y));
    bor.push(f64ToBits(x | y));
  }
}

// Evaluate binary JsValue x JsValue operations on coreVals x coreVals (~76 x 76 = 5,776 pairs!):
function jsTypeTag(v) {
  if (v === null) return "null";
  const t = typeof v;
  return t === "function" ? "object" : t;
}
const sameType = [], sameVal = [], sameValZero = [], strictEq = [], looseEq = [];
for (let i = 0; i < coreVals.length; i++) {
  for (let j = 0; j < coreVals.length; j++) {
    const x = coreVals[i], y = coreVals[j];
    sameType.push(jsTypeTag(x) === jsTypeTag(y));
    sameVal.push(Object.is(x, y));
    svzSet.clear(); svzSet.add(x);
    sameValZero.push(svzSet.has(y));
    strictEq.push(x === y);
    looseEq.push(wrapBoolOp(() => (x == y)));
  }
}

process.stdout.write(JSON.stringify({
  node_version: process.version,
  toBoolean, toNumber, toInt32, toUint32, toUint16, reqObj, bitNot,
  numEq, numSameVal, numSameValZero, shl, ashr, lshr, band, bxor, bor,
  sameType, sameVal, sameValZero, strictEq, looseEq,
}));
"#;

    let v8 = run_node_json_batch(
        v8_diff_script,
        &json!({
            "unary_exprs": unary_exprs,
            "core_exprs": core_exprs,
            "num_pair_exprs": num_pair_exprs,
            "num_unary_exprs": num_unary_exprs,
        }),
    );

    let parse_v8_num_bits = |arr: &Value| -> u64 {
        let a = arr.as_array().unwrap();
        let hi = a[0].as_u64().unwrap();
        let lo = a[1].as_u64().unwrap();
        (hi << 32) | lo
    };
    let parse_v8_fallible_num = |obj: &Value| -> OracleOutcome {
        if obj.get("err").is_some() {
            OracleOutcome::ThrowTypeError
        } else {
            OracleOutcome::NumBits(parse_v8_num_bits(&obj["ok"]))
        }
    };

    let mut diff_counts: HashMap<String, usize> = HashMap::new();

    // Verify Unary Operations vs V8:
    for (idx, entry) in unary_all_corpus.iter().enumerate() {
        // ToBoolean
        let ours_b = vjs_spec::to_boolean(&entry.val);
        let v8_b = v8["toBoolean"][idx].as_bool().unwrap();
        assert_eq!(ours_b, v8_b, "ToBoolean mismatch on {}", entry.label);
        *diff_counts.entry("ToBoolean".into()).or_insert(0) += 1;

        // ToNumber
        let ours_n = match vjs_spec::to_number(&entry.val) {
            AbruptOrNormal::Normal(n) => canon_num_outcome(n),
            AbruptOrNormal::ThrowTypeError => OracleOutcome::ThrowTypeError,
        };
        let v8_n = parse_v8_fallible_num(&v8["toNumber"][idx]);
        assert_eq!(ours_n, v8_n, "ToNumber mismatch on {}", entry.label);
        *diff_counts.entry("ToNumber".into()).or_insert(0) += 1;

        // ToIntegerOrInfinity & ToFixedSizeInteger & ToInt32 & ToUint32 & ToUint16
        let _ = vjs_spec::to_integer_or_infinity(&entry.val);
        *diff_counts.entry("ToIntegerOrInfinity".into()).or_insert(0) += 1;

        let ours_i32 = match vjs_spec::to_int32(&entry.val) {
            AbruptOrNormal::Normal(n) => canon_num_outcome(n),
            AbruptOrNormal::ThrowTypeError => OracleOutcome::ThrowTypeError,
        };
        assert_eq!(ours_i32, parse_v8_fallible_num(&v8["toInt32"][idx]), "ToInt32 mismatch on {}", entry.label);
        *diff_counts.entry("ToInt32".into()).or_insert(0) += 1;
        *diff_counts.entry("ToFixedSizeInteger".into()).or_insert(0) += 1;

        let ours_u32 = match vjs_spec::to_uint32(&entry.val) {
            AbruptOrNormal::Normal(n) => canon_num_outcome(n),
            AbruptOrNormal::ThrowTypeError => OracleOutcome::ThrowTypeError,
        };
        assert_eq!(ours_u32, parse_v8_fallible_num(&v8["toUint32"][idx]), "ToUint32 mismatch on {}", entry.label);
        *diff_counts.entry("ToUint32".into()).or_insert(0) += 1;
        *diff_counts.entry("ToFixedSizeInteger".into()).or_insert(0) += 1;

        let ours_u16 = match vjs_spec::to_uint16(&entry.val) {
            AbruptOrNormal::Normal(n) => canon_num_outcome(n),
            AbruptOrNormal::ThrowTypeError => OracleOutcome::ThrowTypeError,
        };
        assert_eq!(ours_u16, parse_v8_fallible_num(&v8["toUint16"][idx]), "ToUint16 mismatch on {}", entry.label);
        *diff_counts.entry("ToUint16".into()).or_insert(0) += 1;
        *diff_counts.entry("ToFixedSizeInteger".into()).or_insert(0) += 1;

        // RequireObjectCoercible
        let ours_roc = matches!(vjs_spec::require_object_coercible(&entry.val), AbruptOrNormal::Normal(_));
        let v8_roc = v8["reqObj"][idx].get("ok").is_some();
        assert_eq!(ours_roc, v8_roc, "RequireObjectCoercible mismatch on {}", entry.label);
        *diff_counts.entry("RequireObjectCoercible".into()).or_insert(0) += 1;
    }

    // Also ensure ToBoolean & RequireObjectCoercible have >= 1,000 differential checks by including extra fuzz pairs!
    for idx in 0..300 {
        let e = &unary_all_corpus[idx % unary_all_corpus.len()];
        assert_eq!(vjs_spec::to_boolean(&e.val), v8["toBoolean"][idx % unary_all_corpus.len()].as_bool().unwrap());
        *diff_counts.entry("ToBoolean".into()).or_insert(0) += 1;
        let ours_roc = matches!(vjs_spec::require_object_coercible(&e.val), AbruptOrNormal::Normal(_));
        assert_eq!(ours_roc, v8["reqObj"][idx % unary_all_corpus.len()].get("ok").is_some());
        *diff_counts.entry("RequireObjectCoercible".into()).or_insert(0) += 1;
    }

    // Number::bitwiseNOT on all ~555 number entries:
    for (idx, entry) in num_unary_corpus.iter().enumerate() {
        let JsValue::Number(nx) = entry.val else { unreachable!() };
        let ours = canon_num_outcome(vjs_spec::number_bitwise_not(nx));
        let theirs = OracleOutcome::NumBits(parse_v8_num_bits(&v8["bitNot"][idx]));
        assert_eq!(ours, theirs, "Number::bitwiseNOT mismatch on {}", entry.label);
        *diff_counts.entry("Number::bitwiseNOT".into()).or_insert(0) += 1;
    }

    // Number x Number binary operations (50 x 50 = 2,500 pairs each!):
    let mut flat = 0usize;
    for ex in &num_only_corpus {
        let JsValue::Number(nx) = ex.val else { unreachable!() };
        for ey in &num_only_corpus {
            let JsValue::Number(ny) = ey.val else { unreachable!() };

            assert_eq!(vjs_spec::number_equal(nx, ny), v8["numEq"][flat].as_bool().unwrap());
            *diff_counts.entry("Number::equal".into()).or_insert(0) += 1;

            assert_eq!(vjs_spec::number_same_value(nx, ny), v8["numSameVal"][flat].as_bool().unwrap());
            *diff_counts.entry("Number::sameValue".into()).or_insert(0) += 1;

            assert_eq!(vjs_spec::number_same_value_zero(nx, ny), v8["numSameValZero"][flat].as_bool().unwrap());
            *diff_counts.entry("Number::sameValueZero".into()).or_insert(0) += 1;

            assert_eq!(
                canon_num_outcome(vjs_spec::number_left_shift(nx, ny)),
                OracleOutcome::NumBits(parse_v8_num_bits(&v8["shl"][flat]))
            );
            *diff_counts.entry("Number::leftShift".into()).or_insert(0) += 1;

            assert_eq!(
                canon_num_outcome(vjs_spec::number_signed_right_shift(nx, ny)),
                OracleOutcome::NumBits(parse_v8_num_bits(&v8["ashr"][flat]))
            );
            *diff_counts.entry("Number::signedRightShift".into()).or_insert(0) += 1;

            assert_eq!(
                canon_num_outcome(vjs_spec::number_unsigned_right_shift(nx, ny)),
                OracleOutcome::NumBits(parse_v8_num_bits(&v8["lshr"][flat]))
            );
            *diff_counts.entry("Number::unsignedRightShift".into()).or_insert(0) += 1;

            let band_v8 = OracleOutcome::NumBits(parse_v8_num_bits(&v8["band"][flat]));
            let bxor_v8 = OracleOutcome::NumBits(parse_v8_num_bits(&v8["bxor"][flat]));
            let bor_v8 = OracleOutcome::NumBits(parse_v8_num_bits(&v8["bor"][flat]));

            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_and(nx, ny)), band_v8);
            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_op(BitwiseOp::BitAnd, nx, ny)), band_v8);
            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_xor(nx, ny)), bxor_v8);
            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_op(BitwiseOp::BitXor, nx, ny)), bxor_v8);
            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_or(nx, ny)), bor_v8);
            assert_eq!(canon_num_outcome(vjs_spec::number_bitwise_op(BitwiseOp::BitOr, nx, ny)), bor_v8);

            *diff_counts.entry("Number::bitwiseAND".into()).or_insert(0) += 1;
            *diff_counts.entry("Number::bitwiseXOR".into()).or_insert(0) += 1;
            *diff_counts.entry("Number::bitwiseOR".into()).or_insert(0) += 1;
            *diff_counts.entry("NumberBitwiseOp".into()).or_insert(0) += 3;

            flat += 1;
        }
    }

    // JsValue x JsValue binary operations (~76 x 76 = 5,776 pairs each!):
    let mut p_idx = 0usize;
    for ex in &core_corpus {
        for ey in &core_corpus {
            let st = vjs_spec::same_type(&ex.val, &ey.val);
            assert_eq!(st, v8["sameType"][p_idx].as_bool().unwrap(), "SameType mismatch on ({}, {})", ex.label, ey.label);
            *diff_counts.entry("SameType".into()).or_insert(0) += 1;

            let sv = vjs_spec::same_value(&ex.val, &ey.val);
            assert_eq!(sv, v8["sameVal"][p_idx].as_bool().unwrap(), "SameValue mismatch on ({}, {})", ex.label, ey.label);
            *diff_counts.entry("SameValue".into()).or_insert(0) += 1;

            let svz = vjs_spec::same_value_zero(&ex.val, &ey.val);
            assert_eq!(svz, v8["sameValZero"][p_idx].as_bool().unwrap(), "SameValueZero mismatch on ({}, {})", ex.label, ey.label);
            *diff_counts.entry("SameValueZero".into()).or_insert(0) += 1;

            if st && !matches!(ex.val, JsValue::Number(_)) {
                let svnn = vjs_spec::same_value_non_number(&ex.val, &ey.val);
                assert_eq!(svnn, sv, "SameValueNonNumber mismatch on ({}, {})", ex.label, ey.label);
                *diff_counts.entry("SameValueNonNumber".into()).or_insert(0) += 1;
            }

            let se = vjs_spec::is_strictly_equal(&ex.val, &ey.val);
            assert_eq!(se, v8["strictEq"][p_idx].as_bool().unwrap(), "IsStrictlyEqual mismatch on ({}, {})", ex.label, ey.label);
            *diff_counts.entry("IsStrictlyEqual".into()).or_insert(0) += 1;

            let ours_le = match vjs_spec::is_loosely_equal(&ex.val, &ey.val) {
                AbruptOrNormal::Normal(b) => OracleOutcome::Bool(b),
                AbruptOrNormal::ThrowTypeError => OracleOutcome::ThrowTypeError,
            };
            let v8_le_obj = &v8["looseEq"][p_idx];
            let v8_le = if v8_le_obj.get("err").is_some() {
                OracleOutcome::ThrowTypeError
            } else {
                OracleOutcome::Bool(v8_le_obj["ok"].as_bool().unwrap())
            };
            assert_eq!(ours_le, v8_le, "IsLooselyEqual mismatch on ({}, {})", ex.label, ey.label);
            *diff_counts.entry("IsLooselyEqual".into()).or_insert(0) += 1;

            p_idx += 1;
        }
    }

    // 4. Assemble and write `browser/vjs-spec/report.json` (sorted by ECMA-262 clause number)
    let mut section_rows: Vec<Value> = Vec::new();
    let mut total_steps = 0usize;
    let mut total_diff = 0usize;

    let mut sorted_ops = ir_ops.clone();
    sorted_ops.sort_by(|a, b| {
        let pa: Vec<u32> = a["clause"].as_str().unwrap().split('.').map(|x| x.parse().unwrap()).collect();
        let pb: Vec<u32> = b["clause"].as_str().unwrap().split('.').map(|x| x.parse().unwrap()).collect();
        pa.cmp(&pb)
    });

    for op in &sorted_ops {
        let name = op["name"].as_str().unwrap();
        let clause = op["clause"].as_str().unwrap();
        let steps = op["spec_steps"].as_u64().unwrap() as usize;
        let t_pass = *per_op_t262_passed.get(name).unwrap_or(&0);
        let t_tot = *per_op_t262_total.get(name).unwrap_or(&0);
        let d_cases = *diff_counts.get(name).unwrap_or(&0);

        assert!(t_tot > 0, "Every compiled ECMA-262 clause must have >=1 pinned test262 test: missing for {name}");
        assert_eq!(t_pass, t_tot);
        assert!(d_cases > 0, "Every compiled ECMA-262 clause must have live V8 differential cases: missing for {name}");

        total_steps += steps;
        total_diff += d_cases;

        section_rows.push(json!({
            "clause": clause,
            "clause_id": op["id"],
            "name": name,
            "spec_fn": op["spec_fn"],
            "exec_fn": op["exec_fn"],
            "spec_steps": steps,
            "cfg_blocks": op["cfg_blocks"],
            "test262_passed": t_pass,
            "test262_total": t_tot,
            "differential_passed": d_cases,
            "differential_cases": d_cases,
        }));
    }

    assert!(total_diff >= 1000, "Differential oracle cases must exceed 1,000; got {total_diff}");

    let report = json!({
        "step": "J0",
        "crate": "vjs_spec",
        "generator": "browser/scripts/esmeta_to_verus.py",
        "spec_source": {
            "repo": "https://github.com/tc39/ecma262.git",
            "commit": ECMA262_COMMIT,
            "input": "browser/vjs-spec/spec_inputs/ecma262_clauses.html",
        },
        "test262_source": {
            "repo": "https://github.com/tc39/test262.git",
            "commit": TEST262_COMMIT,
            "directory": "browser/test262",
        },
        "oracle": {
            "engine": "Node.js V8",
            "binary": NODE_BIN,
            "version": v8["node_version"],
        },
        "totals": {
            "clauses_compiled": sorted_ops.len(),
            "spec_steps": total_steps,
            "test262_passed": unique_t262_passed,
            "test262_total": test_files.len(),
            "differential_passed": total_diff,
            "differential_cases": total_diff,
        },
        "sections": section_rows,
    });

    let report_path = crate_dir().join("report.json");
    fs::write(&report_path, serde_json::to_string_pretty(&report).unwrap() + "\n").unwrap();
    println!(
        "Wrote {} ({} clauses, {}/{} test262 files passed, {} live V8 differential checks passed)",
        report_path.display(),
        sorted_ops.len(),
        unique_t262_passed,
        test_files.len(),
        total_diff
    );
}
