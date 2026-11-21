//! J4b Integration Test Suite:
//! 1. Real pinned WPT `webidl/` and conversion test vectors (`tests/data/*`), parsed directly
//!    from upstream WPT files (`web-platform-tests/wpt@e8ca145562683547fb32faa7cfa9feb4cc99054b`).
//! 2. Live differential oracle against Node.js v24 (V8) across 600+ IEEE-754, `[Clamp]`,
//!    modulo-2^32, `ByteString`, `USVString`, `record`, and `EventInit` inputs.
//! 3. Capability security runtime verification (`KernelCapTable` + `dispatch`: tamper/forgery,
//!    use-after-revoke, ABA slot reallocation, cross-realm, cross-origin, attenuation
//!    monotonicity, and partition non-interference).
//! 4. Engine-wide static zero-ambient-authority & zero-trusted-marker audit across `browser/`,
//!    emitting `browser/vjs-webidl/report.json`.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use vjs_webidl::caps::{
    CapHandle, CapKind, CapPerms, HostError, KernelCapTable, OriginId, RealmId,
    PERM_ALL, PERM_LOG, PERM_NETWORK, PERM_NONE, PERM_READ, PERM_SCHEDULE, PERM_WRITE,
};
use vjs_webidl::conversions::*;
use vjs_webidl::dispatch::{
    dispatch, verified_revoke_then_dispatch_refused, HostRequest, HostState,
};

fn utf16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn js_str(s: &str) -> JsValue {
    JsValue::String(utf16(s))
}

fn js_f64(x: f64) -> JsValue {
    JsValue::Number(x.to_bits())
}

fn make_plain_obj(
    arena: &mut JsObjectArena,
    own: Vec<(&str, bool, JsValue)>,
    proto: Vec<(&str, JsValue)>,
) -> JsValue {
    let own_props = own
        .into_iter()
        .map(|(k, enumerable, value)| JsOwnProp {
            key: utf16(k),
            is_symbol: false,
            enumerable,
            is_getter: false,
            getter_throws: None,
            value,
        })
        .collect();
    let proto_props = proto
        .into_iter()
        .map(|(k, value)| JsProtoProp {
            key: utf16(k),
            value,
        })
        .collect();
    let id = arena.alloc(JsObjectRecord {
        own_props,
        proto_props,
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    });
    JsValue::Object(id)
}

fn make_plain_obj_u16(
    arena: &mut JsObjectArena,
    own: Vec<(Vec<u16>, bool, JsValue)>,
) -> JsValue {
    let own_props = own
        .into_iter()
        .map(|(key, enumerable, value)| JsOwnProp {
            key,
            is_symbol: false,
            enumerable,
            is_getter: false,
            getter_throws: None,
            value,
        })
        .collect();
    let id = arena.alloc(JsObjectRecord {
        own_props,
        proto_props: Vec::new(),
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    });
    JsValue::Object(id)
}

fn make_custom_props_obj(arena: &mut JsObjectArena, own_props: Vec<JsOwnProp>) -> JsValue {
    let id = arena.alloc(JsObjectRecord {
        own_props,
        proto_props: Vec::new(),
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    });
    JsValue::Object(id)
}

fn make_iterable_obj(arena: &mut JsObjectArena, items: Vec<JsValue>) -> JsValue {
    let id = arena.alloc(JsObjectRecord {
        own_props: Vec::new(),
        proto_props: Vec::new(),
        iterator: JsIterator::Items(items),
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    });
    JsValue::Object(id)
}

/// Decode JS string literal escapes (`\uXXXX`, `\0`, `\n`, `\r`, `\t`, `\\`, `\'`, `\"`)
/// into raw UTF-16 code units (preserving lone surrogates such as `\uD800`!).
fn parse_js_utf16_literal(raw: &str) -> Vec<u16> {
    let chars: Vec<char> = raw.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' && i + 1 < chars.len() {
            match chars[i + 1] {
                '0' => {
                    out.push(0x0000);
                    i += 2;
                }
                'n' => {
                    out.push(0x000A);
                    i += 2;
                }
                'r' => {
                    out.push(0x000D);
                    i += 2;
                }
                't' => {
                    out.push(0x0009);
                    i += 2;
                }
                '\\' => {
                    out.push(0x005C);
                    i += 2;
                }
                '\'' => {
                    out.push(0x0027);
                    i += 2;
                }
                '"' => {
                    out.push(0x0022);
                    i += 2;
                }
                'u' if i + 5 < chars.len() => {
                    let hex: String = chars[i + 2..i + 6].iter().collect();
                    let code = u16::from_str_radix(&hex, 16)
                        .unwrap_or_else(|_| panic!("invalid \\u escape: {hex}"));
                    out.push(code);
                    i += 6;
                }
                other => {
                    let mut buf = [0u16; 2];
                    out.extend_from_slice(other.encode_utf16(&mut buf));
                    i += 2;
                }
            }
        } else {
            let mut buf = [0u16; 2];
            out.extend_from_slice(chars[i].encode_utf16(&mut buf));
            i += 1;
        }
    }
    out
}

fn scalars_to_utf8_bytes(scalars: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for &cp in scalars {
        let ch = char::from_u32(cp).expect("verified scalar must be valid char");
        let mut buf = [0u8; 4];
        bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
    }
    bytes
}

#[derive(Clone, Debug)]
struct SuiteCount {
    name: &'static str,
    wpt_path: &'static str,
    passed: usize,
    total: usize,
}

// ---------------------------------------------------------------------------------------
// 1. WPT Pinned Test Suites (Parsed from `tests/data/*`)
// ---------------------------------------------------------------------------------------

fn run_wpt_enforcerange() -> SuiteCount {
    let src = include_str!("data/idbobjectstore-getAll-enforcerange.any.js");
    // Extract `[NaN, Infinity, -Infinity, -1, -Number.MAX_SAFE_INTEGER]` from WPT file
    let bracket_start = src.find("[NaN,").expect("WPT [EnforceRange] list present");
    let bracket_end = src[bracket_start..].find(']').unwrap() + bracket_start;
    let raw_items: Vec<&str> = src[bracket_start + 1..bracket_end]
        .split(',')
        .map(str::trim)
        .collect();
    assert_eq!(raw_items.len(), 5);

    let arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    for token in raw_items {
        let val = match token {
            "NaN" => JsValue::Number(F64_CANON_NAN),
            "Infinity" => JsValue::Number(F64_POS_INF),
            "-Infinity" => JsValue::Number(F64_NEG_INF),
            "-1" => js_f64(-1.0),
            "-Number.MAX_SAFE_INTEGER" => js_f64(-9007199254740991.0),
            other => panic!("unexpected WPT token in idbobjectstore-getAll-enforcerange: {other}"),
        };
        total += 2;
        assert_eq!(
            to_idl_unsigned_long(&arena, &val, IntAttr::EnforceRange),
            Err(IdlError::TypeError)
        );
        assert_eq!(
            to_idl_unsigned_long_long(&arena, &val, IntAttr::EnforceRange),
            Err(IdlError::TypeError)
        );
        passed += 2;
    }

    // Additional boundary checks across all 8 integer types under [EnforceRange]:
    // Note Web IDL §3.2.4 step 6.2: IntegerPart(-0.9) == 0, which IS in [0, upperBound]!
    // Also includes decimal-fraction strings ("42.9", "-0.9", "42.") via exact RNE StringToNumber!
    let boundary_cases: Vec<(JsValue, Result<u32, IdlError>)> = vec![
        (js_f64(-0.9), Ok(0)),
        (js_f64(-0.0), Ok(0)),
        (js_f64(0.9), Ok(0)),
        (js_str("42.9"), Ok(42)),
        (js_str("42."), Ok(42)),
        (js_str("-0.9"), Ok(0)),
        (js_str("1e2"), Ok(100)),
        (js_str("4294967296.0"), Err(IdlError::TypeError)),
        (js_str("not-a-number"), Err(IdlError::TypeError)),
        (js_f64(4294967295.9), Ok(u32::MAX)),
        (js_f64(4294967296.0), Err(IdlError::TypeError)),
        (JsValue::Symbol(1), Err(IdlError::TypeError)),
        (JsValue::BigInt { neg: false, mag: 1 }, Err(IdlError::TypeError)),
    ];
    for (v, expected) in boundary_cases {
        total += 1;
        assert_eq!(to_idl_unsigned_long(&arena, &v, IntAttr::EnforceRange), expected);
        passed += 1;
    }

    // 64-bit safe integer bounds: ±(2^53 - 1) succeeds, ±2^53 throws TypeError
    total += 4;
    assert_eq!(
        to_idl_long_long(&arena, &js_f64(9007199254740991.0), IntAttr::EnforceRange),
        Ok(MAX_SAFE_INT_I64)
    );
    assert_eq!(
        to_idl_long_long(&arena, &js_f64(-9007199254740991.0), IntAttr::EnforceRange),
        Ok(MIN_SAFE_INT_I64)
    );
    assert_eq!(
        to_idl_long_long(&arena, &js_f64(9007199254740992.0), IntAttr::EnforceRange),
        Err(IdlError::TypeError)
    );
    assert_eq!(
        to_idl_unsigned_long_long(&arena, &js_f64(9007199254740992.0), IntAttr::EnforceRange),
        Err(IdlError::TypeError)
    );
    passed += 4;

    SuiteCount {
        name: "EnforceRange (IDB + 8 integer types)",
        wpt_path: "IndexedDB/idbobjectstore-getAll-enforcerange.any.js",
        passed,
        total,
    }
}

fn run_wpt_clamp() -> SuiteCount {
    let src = include_str!("data/close-invalid.any.js");
    assert!(src.contains("[0x10000 + 1000, \"2**16+1000\"]"));
    assert!(src.contains("[NaN, \"NaN\"]"));
    assert!(src.contains("[\"string\", \"String\"]"));
    assert!(src.contains("[null, \"null\"]"));

    let arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // Parse and execute every `[expr, label]` pair from WPT `websockets/close-invalid.any.js`:
    // WebSocket.close([Clamp] optional unsigned short code)
    for line in src.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') && trimmed.ends_with("],") {
            let inner = &trimmed[1..trimmed.len() - 2];
            if let Some((expr, _label)) = inner.split_once(',') {
                let expr = expr.trim();
                let (js_in, expected_clamped): (JsValue, u16) = match expr {
                    "0" => (js_f64(0.0), 0),
                    "500" => (js_f64(500.0), 500),
                    "NaN" => (JsValue::Number(F64_CANON_NAN), 0),
                    "\"string\"" => (js_str("string"), 0),
                    "null" => (JsValue::Null, 0),
                    "0x10000 + 1000" => (js_f64(66536.0), 65535), // Clamped to 65535, NOT modulo 1000!
                    other => panic!("unexpected close-invalid expr: {other}"),
                };
                total += 1;
                let got = to_idl_unsigned_short(&arena, &js_in, IntAttr::Clamp).unwrap();
                assert_eq!(got, expected_clamped, "WPT close-invalid expr {expr}");
                // Verify contrast with Standard modulo-2^16 on 0x10000 + 1000:
                if expr == "0x10000 + 1000" {
                    assert_eq!(
                        to_idl_unsigned_short(&arena, &js_in, IntAttr::Standard).unwrap(),
                        1000u16
                    );
                }
                passed += 1;
            }
        }
    }
    assert_eq!(passed, 6);

    // Ties-to-even checks across signed & unsigned types per Web IDL §3.2.4 step 7.2
    let octet_ties: &[(f64, u8)] = &[
        (f64::NAN, 0),
        (f64::NEG_INFINITY, 0),
        (f64::INFINITY, 255),
        (-0.0, 0),
        (-0.5, 0),
        (0.5, 0),
        (0.5000001, 1),
        (1.5, 2),
        (2.5, 2),
        (3.5, 4),
        (4.5, 4),
        (253.5, 254),
        (254.5, 254),
        (255.5, 255),
        (1000.0, 255),
    ];
    for &(x, exp) in octet_ties {
        total += 1;
        assert_eq!(to_idl_octet(&arena, &js_f64(x), IntAttr::Clamp), Ok(exp), "octet clamp {x}");
        passed += 1;
    }

    let byte_ties: &[(f64, i8)] = &[
        (f64::NAN, 0),
        (f64::NEG_INFINITY, -128),
        (f64::INFINITY, 127),
        (-0.5, 0),
        (-1.5, -2),
        (-2.5, -2),
        (-3.5, -4),
        (-127.5, -128),
        (-128.9, -128),
        (126.5, 126),
        (127.5, 127),
    ];
    for &(x, exp) in byte_ties {
        total += 1;
        assert_eq!(to_idl_byte(&arena, &js_f64(x), IntAttr::Clamp), Ok(exp), "byte clamp {x}");
        passed += 1;
    }

    // String-encoded decimal fractions & scientific notation under [Clamp] and Standard:
    let str_clamp_cases: &[(&str, u8)] = &[
        ("1.5", 2),
        ("2.5", 2),
        ("3.5", 4),
        ("-0.5", 0),
        (".5", 0),
        ("0.5000001", 1),
        ("254.5", 254),
        ("255.5", 255),
        ("42.", 42),
        ("2.5e1", 25),
        ("1.5e0", 2),
    ];
    for &(s, exp) in str_clamp_cases {
        total += 1;
        assert_eq!(
            to_idl_octet(&arena, &js_str(s), IntAttr::Clamp),
            Ok(exp),
            "octet string clamp {s:?}"
        );
        passed += 1;
    }
    total += 2;
    assert_eq!(to_idl_long(&arena, &js_str("42.9"), IntAttr::Standard), Ok(42));
    assert_eq!(to_idl_long(&arena, &js_str("-42.9"), IntAttr::Standard), Ok(-42));
    passed += 2;

    SuiteCount {
        name: "Clamp ties-to-even (WebSockets + byte/octet)",
        wpt_path: "websockets/close-invalid.any.js",
        passed,
        total,
    }
}

fn run_wpt_usvstring_surrogates() -> SuiteCount {
    let enc_src = include_str!("data/api-surrogates-utf8.any.js");
    let ws_src = include_str!("data/Close-reason-unpaired-surrogates.any.js");
    let arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // 1. Extract `var reason = "\uD807";` and `var replacementChar = "\uFFFD";` from WPT
    assert!(ws_src.contains("var reason = \"\\uD807\";"));
    total += 1;
    let ws_reason = JsValue::String(parse_js_utf16_literal("\\uD807"));
    let ws_usv = to_idl_usv_string(&arena, &ws_reason).unwrap();
    assert_eq!(ws_usv, vec![0xFFFDu16]);
    assert_eq!(usv_normalize_units(&ws_usv), ws_usv); // idempotence
    passed += 1;

    // 2. Parse all 6 objects from `badStrings` in `encoding/api-surrogates-utf8.any.js`
    let mut parsed_blocks = 0usize;
    for chunk in enc_src.split('{').skip(1) {
        let Some(body) = chunk.split('}').next() else { continue };
        if !body.contains("input:") || !body.contains("expected:") || !body.contains("decoded:") {
            continue;
        }
        let extract_single_quoted = |field: &str| -> String {
            let idx = body.find(field).unwrap() + field.len();
            let rest = body[idx..].trim_start();
            let rest = rest.strip_prefix('\'').unwrap();
            let end = rest.find('\'').unwrap();
            rest[..end].to_string()
        };
        let input_lit = extract_single_quoted("input:");
        let decoded_lit = extract_single_quoted("decoded:");

        let exp_idx = body.find("expected:").unwrap() + "expected:".len();
        let exp_rest = body[exp_idx..].trim_start();
        let b_start = exp_rest.find('[').unwrap();
        let b_end = exp_rest.find(']').unwrap();
        let expected_utf8: Vec<u8> = exp_rest[b_start + 1..b_end]
            .split(',')
            .map(|tok| {
                let t = tok.trim();
                u8::from_str_radix(t.strip_prefix("0x").unwrap_or(t), 16).unwrap()
            })
            .collect();

        let raw_units = parse_js_utf16_literal(&input_lit);
        let expected_decoded_units = parse_js_utf16_literal(&decoded_lit);

        total += 1;
        let usv_units = to_idl_usv_string(&arena, &JsValue::String(raw_units.clone())).unwrap();
        assert_eq!(usv_units, expected_decoded_units, "USVString mismatch on {input_lit}");
        // Verify idempotence: usv(usv(s)) == usv(s)
        assert_eq!(usv_normalize_units(&usv_units), usv_units);
        // Verify scalar decoding -> UTF-8 matches WPT's exact `expected` byte array
        let scalars = usv_to_scalars(&raw_units);
        assert_eq!(scalars_to_utf8_bytes(&scalars), expected_utf8);
        passed += 1;
        parsed_blocks += 1;
    }
    assert_eq!(parsed_blocks, 6);

    // 3. Valid surrogate pair preservation (`\uD83D\uDCA9` U+1F4A9 PILE OF POO from urlsearchparams)
    let url_src = include_str!("data/urlsearchparams-constructor.any.js");
    assert!(url_src.contains("\\uD83D\\uDCA9"));
    total += 1;
    let poo = parse_js_utf16_literal("a\\uD83D\\uDCA9b");
    let poo_usv = to_idl_usv_string(&arena, &JsValue::String(poo.clone())).unwrap();
    assert_eq!(poo_usv, poo, "valid surrogate pair must be preserved untouched");
    assert_eq!(usv_to_scalars(&poo), vec![0x61, 0x1F4A9, 0x62]);
    passed += 1;

    SuiteCount {
        name: "USVString unpaired surrogates & pairs",
        wpt_path: "encoding/api-surrogates-utf8.any.js",
        passed,
        total,
    }
}

fn run_wpt_urlsearchparams_records_and_sequences() -> SuiteCount {
    let src = include_str!("data/urlsearchparams-constructor.any.js");
    assert!(src.contains("\"\\uD835x\": \"1\""));
    assert!(src.contains("\"x\\uDC53\": \"1\""));
    assert!(src.contains("new URLSearchParams([[1]])"));
    assert!(src.contains("new URLSearchParams([[1,2,3]])"));

    let mut arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // Exact WPT surrogate key collision + ordered-map in-place upsert vectors from lines 166–173:
    // Case 1: {"\uD835x": "1", "xx": "2", "\uD83Dx": "3"} -> [["\uFFFDx", "3"], ["xx", "2"]]
    total += 1;
    let obj1 = make_plain_obj_u16(
        &mut arena,
        vec![
            (parse_js_utf16_literal("\\uD835x"), true, js_str("1")),
            (parse_js_utf16_literal("xx"), true, js_str("2")),
            (parse_js_utf16_literal("\\uD83Dx"), true, js_str("3")),
        ],
    );
    let rec1 = to_idl_record_usv_string(&arena, &obj1).unwrap();
    assert_eq!(
        rec1,
        vec![
            (parse_js_utf16_literal("\\uFFFDx"), utf16("3")),
            (utf16("xx"), utf16("2")),
        ]
    );
    passed += 1;

    // Case 2: {"x\uDC53": "1", "x\uDC5C": "2", "x\uDC65": "3"} -> [["x\uFFFD", "3"]]
    total += 1;
    let obj2 = make_plain_obj_u16(
        &mut arena,
        vec![
            (parse_js_utf16_literal("x\\uDC53"), true, js_str("1")),
            (parse_js_utf16_literal("x\\uDC5C"), true, js_str("2")),
            (parse_js_utf16_literal("x\\uDC65"), true, js_str("3")),
        ],
    );
    let rec2 = to_idl_record_usv_string(&arena, &obj2).unwrap();
    assert_eq!(rec2, vec![(parse_js_utf16_literal("x\\uFFFD"), utf16("3"))]);
    passed += 1;

    // Case 3: {"a\0b": "42", "c\uD83D": "23", "d\u1234": "foo"}
    total += 1;
    let obj3 = make_plain_obj_u16(
        &mut arena,
        vec![
            (parse_js_utf16_literal("a\\0b"), true, js_str("42")),
            (parse_js_utf16_literal("c\\uD83D"), true, js_str("23")),
            (parse_js_utf16_literal("d\\u1234"), true, js_str("foo")),
        ],
    );
    let rec3 = to_idl_record_usv_string(&arena, &obj3).unwrap();
    assert_eq!(
        rec3,
        vec![
            (parse_js_utf16_literal("a\\0b"), utf16("42")),
            (parse_js_utf16_literal("c\\uFFFD"), utf16("23")),
            (parse_js_utf16_literal("d\\u1234"), utf16("foo")),
        ]
    );
    passed += 1;

    // Case 4: sequence<sequence<USVString>> invalid tuple lengths [[1]] & [[1,2,3]] -> TypeError,
    // and [[1, 2], ['a', 'b']] -> [["1", "2"], ["a", "b"]]
    total += 3;
    let inner_one = make_iterable_obj(&mut arena, vec![js_f64(1.0)]);
    let outer_one = make_iterable_obj(&mut arena, vec![inner_one]);
    assert_eq!(to_idl_usv_sequence_pairs(&arena, &outer_one), Err(IdlError::TypeError));

    let inner_three = make_iterable_obj(&mut arena, vec![js_f64(1.0), js_f64(2.0), js_f64(3.0)]);
    let outer_three = make_iterable_obj(&mut arena, vec![inner_three]);
    assert_eq!(to_idl_usv_sequence_pairs(&arena, &outer_three), Err(IdlError::TypeError));

    let p_num = make_iterable_obj(&mut arena, vec![js_f64(1.0), js_f64(2.0)]);
    let p_str = make_iterable_obj(&mut arena, vec![js_str("a"), js_str("b")]);
    let outer_valid = make_iterable_obj(&mut arena, vec![p_num, p_str]);
    assert_eq!(
        to_idl_usv_sequence_pairs(&arena, &outer_valid),
        Ok(vec![(utf16("1"), utf16("2")), (utf16("a"), utf16("b"))])
    );
    passed += 3;

    SuiteCount {
        name: "URLSearchParams USVString records & sequences",
        wpt_path: "url/urlsearchparams-constructor.any.js",
        passed,
        total,
    }
}

fn run_wpt_bytestring_and_headers_record() -> SuiteCount {
    let err_src = include_str!("data/headers-errors.any.js");
    let rec_src = include_str!("data/headers-record.any.js");
    assert!(err_src.contains("invalid\u{0100}"));
    assert!(rec_src.contains("new Headers(null)"));
    assert!(rec_src.contains("enumerable: true"));

    let mut arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // Extract `"invalidĀ"` (`U+0100`) from `headers-errors.any.js`
    total += 5;
    assert_eq!(to_idl_byte_string(&arena, &js_str("invalid\u{0100}")), Err(IdlError::TypeError));
    // Latin-1 `0x00..=0xFF` roundtrips losslessly with exact length preservation
    let all_256: Vec<u8> = (0u8..=255u8).collect();
    let js_256 = to_js_byte_string(&all_256);
    let back_256 = to_idl_byte_string(&arena, &js_256).unwrap();
    assert_eq!(back_256.len(), 256);
    assert_eq!(back_256, all_256);

    // Headers([["name"]]) & Headers([["invalid", "invalidValue1", "invalidValue2"]]) -> TypeError
    let s1 = make_iterable_obj(&mut arena, vec![js_str("name")]);
    let o1 = make_iterable_obj(&mut arena, vec![s1]);
    assert_eq!(to_idl_headers_sequence_pairs(&arena, &o1), Err(IdlError::TypeError));

    let s3 = make_iterable_obj(
        &mut arena,
        vec![js_str("invalid"), js_str("invalidValue1"), js_str("invalidValue2")],
    );
    let o3 = make_iterable_obj(&mut arena, vec![s3]);
    assert_eq!(to_idl_headers_sequence_pairs(&arena, &o3), Err(IdlError::TypeError));

    let s_bad = make_iterable_obj(&mut arena, vec![js_str("invalid\u{0100}"), js_str("Value1")]);
    let o_bad = make_iterable_obj(&mut arena, vec![s_bad]);
    assert_eq!(to_idl_headers_sequence_pairs(&arena, &o_bad), Err(IdlError::TypeError));
    passed += 5;

    // WPT `headers-record.any.js`:
    // 1. `null` -> TypeError
    // 2. Prototype properties `{ c: "d" }` and non-enumerable own `{ e: "f" }` (even with a
    //    throwing getter!) are skipped; only own enumerable `{ a: "b" }` is included!
    // 3. `{ a: "b", "\uFFFF": <throwing getter> }` throws TypeError on key conversion BEFORE `[[Get]]`.
    // 4. Duplicate `ownKeys` (`["a", "c", "a", "c"]`) throws TypeError at `[[OwnPropertyKeys]]`.
    // 5. Enumerable `[Symbol.toStringTag]` throws TypeError converting Symbol key to ByteString,
    //    whereas non-enumerable `[Symbol.toStringTag]` is skipped without throwing!
    total += 6;
    assert_eq!(to_idl_record_byte_string(&arena, &JsValue::Null), Err(IdlError::TypeError));
    let rec_obj = make_plain_obj(
        &mut arena,
        vec![
            ("a", true, js_str("b")),
            ("e", false, js_str("f")),
        ],
        vec![("c", js_str("d"))],
    );
    let parsed_rec = to_idl_record_byte_string(&arena, &rec_obj).unwrap();
    assert_eq!(parsed_rec, vec![(b"a".to_vec(), b"b".to_vec())]);

    // Non-enumerable properties with `getter_throws: Some(...)` are never `[[Get]]`-accessed!
    let non_enum_getter_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("a"),
                is_symbol: false,
                enumerable: false,
                is_getter: true,
                getter_throws: Some(501),
                value: JsValue::Undefined,
            },
            JsOwnProp {
                key: utf16("c"),
                is_symbol: false,
                enumerable: true,
                is_getter: false,
                getter_throws: None,
                value: js_str("d"),
            },
            JsOwnProp {
                key: utf16("e"),
                is_symbol: false,
                enumerable: false,
                is_getter: true,
                getter_throws: Some(502),
                value: JsValue::Undefined,
            },
        ],
    );
    assert_eq!(
        to_idl_record_byte_string(&arena, &non_enum_getter_obj),
        Ok(vec![(b"c".to_vec(), b"d".to_vec())])
    );

    // Invalid key `"\uFFFF"` throws TypeError BEFORE `[[Get]]` (`headers-record.any.js:123–146`):
    // note `getter_throws: Some(999)` would return `AbruptException(999)` if `[[Get]]` ran!
    let bad_key_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("a"),
                is_symbol: false,
                enumerable: true,
                is_getter: false,
                getter_throws: None,
                value: js_str("b"),
            },
            JsOwnProp {
                key: vec![0xFFFF],
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: Some(999),
                value: js_str("d"),
            },
        ],
    );
    assert_eq!(to_idl_record_byte_string(&arena, &bad_key_obj), Err(IdlError::TypeError));

    // Duplicate ownKeys `["a", "c", "a", "c"]` throws TypeError (`headers-record.any.js:245–267`)
    let dup_keys_obj = make_plain_obj(
        &mut arena,
        vec![
            ("a", true, js_str("b")),
            ("c", true, js_str("d")),
            ("a", true, js_str("b")),
            ("c", true, js_str("d")),
        ],
        vec![],
    );
    assert_eq!(to_idl_record_byte_string(&arena, &dup_keys_obj), Err(IdlError::TypeError));

    // Enumerable Symbol key throws TypeError BEFORE `[[Get]]` (`headers-record.any.js:269–303`),
    // while non-enumerable Symbol key is skipped (`headers-record.any.js:305–357`)!
    let enum_sym_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("a"),
                is_symbol: false,
                enumerable: true,
                is_getter: false,
                getter_throws: None,
                value: js_str("b"),
            },
            JsOwnProp {
                key: vec![],
                is_symbol: true,
                enumerable: true,
                is_getter: true,
                getter_throws: Some(888),
                value: js_str("nope"),
            },
        ],
    );
    assert_eq!(to_idl_record_byte_string(&arena, &enum_sym_obj), Err(IdlError::TypeError));

    let non_enum_sym_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("a"),
                is_symbol: false,
                enumerable: true,
                is_getter: false,
                getter_throws: None,
                value: js_str("b"),
            },
            JsOwnProp {
                key: vec![],
                is_symbol: true,
                enumerable: false,
                is_getter: true,
                getter_throws: Some(889),
                value: JsValue::Undefined,
            },
            JsOwnProp {
                key: utf16("c"),
                is_symbol: false,
                enumerable: true,
                is_getter: false,
                getter_throws: None,
                value: js_str("d"),
            },
        ],
    );
    assert_eq!(
        to_idl_record_byte_string(&arena, &non_enum_sym_obj),
        Ok(vec![(b"a".to_vec(), b"b".to_vec()), (b"c".to_vec(), b"d".to_vec())])
    );
    passed += 6;

    SuiteCount {
        name: "ByteString & Headers record/sequence",
        wpt_path: "fetch/api/headers/headers-errors.any.js",
        passed,
        total,
    }
}

fn run_wpt_event_and_dictionaries() -> SuiteCount {
    let ev_src = include_str!("data/Event-constructors.any.js");
    let rx_src = include_str!("data/no-regexp-special-casing.any.js");
    let set_src = include_str!("data/setter-argument.html");
    assert!(ev_src.contains("bubblesIGNORED"));
    assert!(rx_src.contains("/(?:)/"));
    assert!(set_src.contains("undefined value should be stringified"));

    let mut arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // WPT `Event-constructors.any.js` cases:
    // 1. Missing/undefined/null EventInit -> all false
    total += 3;
    assert_eq!(
        to_idl_event_init(&arena, &JsValue::Undefined),
        Ok(EventInit { bubbles: false, cancelable: false, composed: false })
    );
    assert_eq!(
        to_idl_event_init(&arena, &JsValue::Null),
        Ok(EventInit { bubbles: false, cancelable: false, composed: false })
    );
    // Primitive non-null/undefined (e.g. number `1` or string `"foo"`) -> TypeError per §3.2.20 step 1!
    assert_eq!(to_idl_event_init(&arena, &js_f64(1.0)), Err(IdlError::TypeError));
    passed += 3;

    // 2. `{ bubbles: true, cancelable: false }`, `{ bubblesIGNORED: true, cancelable: true }`,
    //    `{ "bubbles\0IGNORED": true, cancelable: true }`, `{ bubbles: true, cancelable: false, sweet: "x" }`,
    //    plus prototype-inherited `composed: true`!
    total += 4;
    let d1 = make_plain_obj(
        &mut arena,
        vec![
            ("bubbles", true, JsValue::Bool(true)),
            ("cancelable", true, JsValue::Bool(false)),
            ("sweet", true, js_str("x")),
        ],
        vec![],
    );
    let init1 = to_idl_event_init(&arena, &d1).unwrap();
    assert_eq!(init1, EventInit { bubbles: true, cancelable: false, composed: false });
    // Verify ToJS -> ToIDL roundtrip on EventInit!
    let d1_js = to_js_event_init(&mut arena, &init1).unwrap();
    assert_eq!(to_idl_event_init(&arena, &d1_js), Ok(init1));

    let d2 = make_plain_obj(
        &mut arena,
        vec![
            ("bubblesIGNORED", true, JsValue::Bool(true)),
            ("bubbles\0IGNORED", true, JsValue::Bool(true)),
            ("cancelable", true, JsValue::Bool(true)),
        ],
        vec![("composed", JsValue::Bool(true))], // inherited via prototype!
    );
    assert_eq!(
        to_idl_event_init(&arena, &d2),
        Ok(EventInit { bubbles: false, cancelable: true, composed: true })
    );

    // WPT `Event-constructors.any.js:15–18`:
    // `var test_error = { name: "test" }; assert_throws_exactly(test_error, () => new Event({ toString() { throw test_error; } }))`
    let throw_obj_id = arena.alloc(JsObjectRecord {
        own_props: Vec::new(),
        proto_props: Vec::new(),
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::ThrowException(777),
        to_number_override: None,
    });
    assert_eq!(
        to_idl_dom_string(&arena, &JsValue::Object(throw_obj_id), false),
        Err(IdlError::AbruptException(777))
    );

    // WPT `setter-argument.html`: undefined argument stringifies to `"undefined"` for DOMString
    assert_eq!(
        to_idl_dom_string(&arena, &JsValue::Undefined, false),
        Ok(utf16("undefined"))
    );
    passed += 4;

    // WPT `Event-constructors.any.js:91–112`:
    // Object defines `get cancelable()`, `get bubbles()`, `get sweet()` in reverse order,
    // and asserts `called == ["bubbles", "cancelable"]` (strict lexicographical order;
    // unknown `sweet` is NEVER accessed even if its getter throws!).
    total += 3;
    let getter_order_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("cancelable"),
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: None,
                value: JsValue::Bool(false),
            },
            JsOwnProp {
                key: utf16("bubbles"),
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: None,
                value: JsValue::Bool(true),
            },
            JsOwnProp {
                key: utf16("sweet"),
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: Some(404),
                value: js_str("x"),
            },
        ],
    );
    let (logged_init, called) = to_idl_event_init_logged(&arena, &getter_order_obj).unwrap();
    assert_eq!(
        logged_init,
        EventInit { bubbles: true, cancelable: false, composed: false }
    );
    assert_eq!(called, vec![utf16("bubbles"), utf16("cancelable")]);

    // Abrupt lexicographical order: `{ get cancelable() { throw 222; }, get bubbles() { throw 111; } }`
    // MUST throw `111` (evaluating `"bubbles"` before `"cancelable"`)!
    let abrupt_lex_obj = make_custom_props_obj(
        &mut arena,
        vec![
            JsOwnProp {
                key: utf16("cancelable"),
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: Some(222),
                value: JsValue::Undefined,
            },
            JsOwnProp {
                key: utf16("bubbles"),
                is_symbol: false,
                enumerable: true,
                is_getter: true,
                getter_throws: Some(111),
                value: JsValue::Undefined,
            },
        ],
    );
    assert_eq!(
        to_idl_event_init(&arena, &abrupt_lex_obj),
        Err(IdlError::AbruptException(111))
    );
    passed += 3;

    // WPT `no-regexp-special-casing.any.js`: RegExp converts as ordinary Object to dictionary,
    // sequence (with Symbol.iterator), and USVString (`"/(?:)/"`)!
    total += 1;
    let rx_id = arena.alloc(JsObjectRecord {
        own_props: vec![JsOwnProp {
            key: utf16("bubbles"),
            is_symbol: false,
            enumerable: true,
            is_getter: false,
            getter_throws: None,
            value: JsValue::Bool(true),
        }],
        proto_props: Vec::new(),
        iterator: JsIterator::Items(vec![js_f64(7.0), js_f64(8.0)]),
        to_string_hook: JsToStringHook::ReturnStr(utf16("/(?:)/")),
        to_number_override: None,
    });
    let rx_val = JsValue::Object(rx_id);
    assert_eq!(to_idl_event_init(&arena, &rx_val).unwrap().bubbles, true);
    assert_eq!(to_idl_sequence_long(&arena, &rx_val, IntAttr::Standard).unwrap(), vec![7, 8]);
    assert_eq!(to_idl_usv_string(&arena, &rx_val).unwrap(), utf16("/(?:)/"));
    passed += 1;

    // Core host dictionaries: RequestInit, StorageOp, NodeOp, UrlHref
    total += 4;
    let req_default = to_idl_request_init(&arena, &JsValue::Undefined).unwrap();
    assert_eq!(req_default.method, b"GET".to_vec());
    assert_eq!(req_default.credentials, utf16("same-origin"));
    assert_eq!(req_default.mode, utf16("cors"));
    assert!(!req_default.keepalive);

    // StorageOp missing required `op` throws TypeError!
    let empty_obj = make_plain_obj(&mut arena, vec![], vec![]);
    assert_eq!(to_idl_storage_op(&arena, &empty_obj), Err(IdlError::TypeError));

    // NodeOp with out-of-range negative `nodeId` throws TypeError via `[EnforceRange]`!
    let bad_node = make_plain_obj(
        &mut arena,
        vec![("nodeId", true, js_f64(-5.0)), ("op", true, js_str("setText"))],
        vec![],
    );
    assert_eq!(to_idl_node_op(&arena, &bad_node), Err(IdlError::TypeError));

    // UrlHref normalizes lone surrogates in `href` and clamps `portOverride`!
    let url_obj = make_plain_obj(
        &mut arena,
        vec![
            ("href", true, JsValue::String(parse_js_utf16_literal("https://ex.test/\\uD800"))),
            ("portOverride", true, js_f64(99999.0)),
        ],
        vec![],
    );
    let parsed_url = to_idl_url_href(&arena, &url_obj).unwrap();
    assert_eq!(parsed_url.href, parse_js_utf16_literal("https://ex.test/\\uFFFD"));
    assert_eq!(parsed_url.port_override, Some(65535));
    passed += 4;

    SuiteCount {
        name: "Dictionaries (EventInit, RequestInit, StorageOp, NodeOp, UrlHref)",
        wpt_path: "dom/events/Event-constructors.any.js",
        passed,
        total,
    }
}

fn run_wpt_dom_exception_and_sequence() -> SuiteCount {
    let dom_src = include_str!("data/DOMException-constructor-behavior.any.js");
    let seq_src = include_str!("data/sequence-conversion.html");
    assert!(seq_src.contains("ctx.setLineDash([1, 2])"));

    let mut arena = JsObjectArena::new();
    let mut passed = 0usize;
    let mut total = 0usize;

    // Parse all `{name: "...", code: N}` rows directly from `DOMException-constructor-behavior.any.js`!
    let mut table_rows = 0usize;
    for line in dom_src.lines() {
        let t = line.trim();
        if t.starts_with("{name:") {
            let q1 = t.find('"').unwrap();
            let q2 = t[q1 + 1..].find('"').unwrap() + q1 + 1;
            let name = &t[q1 + 1..q2];
            let c_idx = t.find("code:").unwrap() + "code:".len();
            let c_end = t[c_idx..].find('}').unwrap() + c_idx;
            let expected_code: u16 = t[c_idx..c_end].trim().parse().unwrap();

            total += 1;
            let rec = construct_dom_exception(
                &arena,
                Some(&js_str("msg")),
                Some(&js_str(name)),
            )
            .unwrap();
            assert_eq!(rec.message, utf16("msg"));
            assert_eq!(rec.name, utf16(name));
            assert_eq!(rec.code, expected_code, "DOMException legacy code for {name}");
            passed += 1;
            table_rows += 1;
        }
    }
    assert_eq!(table_rows, 35);

    // Constructor default & null cases from `DOMException-constructor-behavior.any.js`:
    total += 3;
    let ex_none = construct_dom_exception(&arena, None, None).unwrap();
    assert_eq!((ex_none.message, ex_none.name, ex_none.code), (utf16(""), utf16("Error"), 0));
    let ex_null = construct_dom_exception(&arena, Some(&JsValue::Null), None).unwrap();
    assert_eq!((ex_null.message, ex_null.name, ex_null.code), (utf16("null"), utf16("Error"), 0));
    let ex_undef =
        construct_dom_exception(&arena, Some(&js_str("bar")), Some(&JsValue::Undefined)).unwrap();
    assert_eq!((ex_undef.message, ex_undef.name, ex_undef.code), (utf16("bar"), utf16("Error"), 0));
    passed += 3;

    // Sequence conversions from `webidl/ecmascript-binding/sequence-conversion.html`:
    total += 3;
    let arr = make_iterable_obj(&mut arena, vec![js_f64(13.0), js_f64(14.0), js_f64(15.0), js_f64(16.0)]);
    assert_eq!(to_idl_sequence_long(&arena, &arr, IntAttr::Standard), Ok(vec![13, 14, 15, 16]));
    let non_iter = make_plain_obj(&mut arena, vec![], vec![]);
    assert_eq!(to_idl_sequence_long(&arena, &non_iter, IntAttr::Standard), Err(IdlError::TypeError));
    // `new URLSearchParams(["key", "value"])` -> inner `"key"` is not an Object -> TypeError!
    let str_arr = make_iterable_obj(&mut arena, vec![js_str("key"), js_str("value")]);
    assert_eq!(to_idl_usv_sequence_pairs(&arena, &str_arr), Err(IdlError::TypeError));
    passed += 3;

    SuiteCount {
        name: "DOMException & sequence-conversion",
        wpt_path: "webidl/ecmascript-binding/es-exceptions/DOMException-constructor-behavior.any.js",
        passed,
        total,
    }
}

// ---------------------------------------------------------------------------------------
// 2. Live Differential Oracle vs Node.js v24 (V8)
// ---------------------------------------------------------------------------------------

fn resolve_node_binary() -> String {
    if Command::new("node")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
    {
        return "node".to_string();
    }
    let nvm_node = "/Users/mac/.nvm/versions/node/v24.15.0/bin/node";
    assert!(
        Path::new(nvm_node).exists(),
        "Node.js binary must exist on PATH or at {nvm_node}"
    );
    nvm_node.to_string()
}

fn run_node_v8_differential_oracle() -> (String, usize) {
    let node_bin = resolve_node_binary();

    // Generate 220 deterministic numeric bit patterns covering NaN, ±0, ±Inf, subnormals,
    // half-way ties, power-of-two boundaries, negative values, and large exponents.
    let mut num_bits: Vec<u64> = vec![
        F64_POS_ZERO,
        F64_NEG_ZERO,
        F64_POS_INF,
        F64_NEG_INF,
        F64_CANON_NAN,
        1u64,                       // min positive subnormal
        (1u64 << 52) - 1,           // max positive subnormal
        0x8000_0000_0000_0001u64,   // min negative subnormal
    ];
    let special_f64s: &[f64] = &[
        -2147483649.0, -2147483648.0, -2147483647.0, -65536.0, -65535.5, -256.5, -255.5,
        -129.0, -128.5, -128.0, -127.5, -2.5, -1.5, -1.0, -0.9, -0.500001, -0.5, -0.499999,
        -0.1, 0.1, 0.499999, 0.5, 0.500001, 0.9, 1.0, 1.5, 2.5, 3.5, 4.5, 126.5, 127.0, 127.5,
        128.0, 253.5, 254.5, 255.0, 255.5, 256.0, 65535.0, 65536.0, 2147483647.0, 2147483648.0,
        4294967295.0, 4294967296.0, 9007199254740991.0, 9007199254740992.0, -9007199254740991.0,
        -9007199254740992.0, 1.0e20, -1.0e20, 1.0e100, -1.0e100,
    ];
    for &x in special_f64s {
        num_bits.push(x.to_bits());
    }
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..160 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let sign = (state >> 63) & 1;
        let exp = 1018u64 + ((state >> 40) % 90u64);
        let mant = state & 0x000F_FFFF_FFFF_FFFFu64;
        num_bits.push((sign << 63) | (exp << 52) | mant);
    }

    // Exact dyadic numbers for Number::toString parity against V8 `String(x)`
    let dyadic_to_string_f64s: &[f64] = &[
        0.0, -0.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY,
        0.5, -0.5, 0.25, -0.25, 0.75, 0.125, -0.125, 0.875,
        1.5, -1.5, 1.25, 1.75, 1.875, 42.0, -42.5, 1024.0625,
        9007199254740991.0, -9007199254740991.0,
    ];
    let dyadic_bits: Vec<u64> = dyadic_to_string_f64s.iter().map(|x| x.to_bits()).collect();

    // Generate 80 UTF-16 test vectors including lone surrogates, reversed pairs, valid pairs, ASCII/Latin-1
    let mut utf16_cases: Vec<Vec<u16>> = vec![
        vec![],
        vec![0x0000],
        vec![0xD800],
        vec![0xDBFF],
        vec![0xDC00],
        vec![0xDFFF],
        vec![0xDC00, 0xD800],
        vec![0xD800, 0xD800, 0xDC00],
        vec![0xD83D, 0xDCA9],
        vec![0x0041, 0x00FF, 0x0100],
        vec![0x0048, 0x0065, 0x006C, 0x006C, 0x006F, 0x00FF],
    ];
    let palette: &[u16] = &[0x0000, 0x0041, 0x007F, 0x00FF, 0x0100, 0xD800, 0xD83D, 0xDC00, 0xDCA9, 0xFFFD];
    for _ in 0..70 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let len = ((state >> 32) % 8) as usize;
        let mut s = Vec::with_capacity(len);
        for _ in 0..len {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            s.push(palette[((state >> 48) as usize) % palette.len()]);
        }
        utf16_cases.push(s);
    }

    // String-to-Number vectors (decimal fractions, RNE half-way ties, scientific notation,
    // subnormals, overflow/underflow, >780-digit sticky truncation, radix literals, whitespace,
    // and syntax errors) compared bit-for-bit + across Web IDL integer conversions against V8!
    let huge_cancel_pos = format!("0.{}5e2001", "0".repeat(2000));
    let huge_cancel_neg = format!("5{}e-2000", "0".repeat(2000));
    let sticky_900 = format!("1.{}1", "0".repeat(900));
    let hex_overflow = format!("0x{}", "f".repeat(300));
    let raw_str_nums: Vec<String> = vec![
        "".into(),
        "   \t\r\n\u{00A0}\u{FEFF}  ".into(),
        "\u{180E}1".into(),
        "0".into(),
        "-0".into(),
        "+0".into(),
        "0.0".into(),
        "-0.0".into(),
        "+0.0".into(),
        "-000.000e+999999".into(),
        ".5".into(),
        "-.5".into(),
        "+.5".into(),
        "0.5".into(),
        "-0.5".into(),
        "1.5".into(),
        "-1.5".into(),
        "2.5".into(),
        "-2.5".into(),
        "3.5".into(),
        "42.".into(),
        "-42.".into(),
        "42.9".into(),
        "-42.9".into(),
        "0.1".into(),
        "0.2".into(),
        "0.3".into(),
        "-0.1".into(),
        "-0.3".into(),
        "253.5".into(),
        "254.5".into(),
        "255.5".into(),
        "-127.5".into(),
        "-128.5".into(),
        "65535.9".into(),
        "4294967295.9".into(),
        "4294967296.0".into(),
        "9007199254740991".into(),
        "9007199254740992".into(),
        "9007199254740993".into(),
        "1e20".into(),
        "-1e20".into(),
        "1.25e-3".into(),
        "-1.25E+3".into(),
        "1e-400".into(),
        "-1e-400".into(),
        "1e400".into(),
        "-1e400".into(),
        "1.7976931348623157e+308".into(),
        "1.7976931348623159e+308".into(),
        "-1.7976931348623157e+308".into(),
        "-1.7976931348623159e+308".into(),
        "2.2250738585072014e-308".into(),
        "2.225073858507201e-308".into(),
        "5e-324".into(),
        "-5e-324".into(),
        "2.4703282292062327e-324".into(),
        "2.4703282292062328e-324".into(),
        huge_cancel_pos,
        huge_cancel_neg,
        sticky_900,
        "0x0".into(),
        "0Xff".into(),
        "0xdeadbeef".into(),
        "0x10000000000000800".into(),
        "0x10000000000001800".into(),
        hex_overflow,
        "-0x1".into(),
        "0b101010".into(),
        "0B0".into(),
        "0o777".into(),
        "0O1234567".into(),
        "Infinity".into(),
        "+Infinity".into(),
        "-Infinity".into(),
        "infinity".into(),
        "NaN".into(),
        ".".into(),
        "-.".into(),
        "+.".into(),
        "1.2.3".into(),
        "1e".into(),
        "1e+".into(),
        "1e-".into(),
        "0x".into(),
        "0b2".into(),
        "0o8".into(),
        "123abc".into(),
        "  \t-987.654e-2\n ".into(),
    ];
    let mut str_num_cases: Vec<Vec<u16>> = raw_str_nums.iter().map(|s| utf16(s)).collect();
    for _ in 0..40 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let neg = if (state & 1) == 0 { "" } else { "-" };
        let int_part = (state >> 8) % 100_000;
        let frac_part = (state >> 28) % 1_000_000;
        let exp_part = (((state >> 48) % 41) as i32) - 20;
        let generated = format!("{neg}{int_part}.{frac_part:06}e{exp_part}");
        str_num_cases.push(utf16(&generated));
    }

    let payload = serde_json::json!({
        "num_bits": num_bits.iter().map(|b| b.to_string()).collect::<Vec<_>>(),
        "dyadic_bits": dyadic_bits.iter().map(|b| b.to_string()).collect::<Vec<_>>(),
        "utf16_cases": utf16_cases,
        "str_num_cases": str_num_cases,
    });

    let js_oracle = r#"
const fs = require('node:fs');
const util = require('node:util');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));

function bitsToF64(decStr) {
  const buf = new ArrayBuffer(8);
  const dv = new DataView(buf);
  dv.setBigUint64(0, BigInt(decStr), true);
  return dv.getFloat64(0, true);
}

function f64ToBitsStr(x) {
  const buf = new ArrayBuffer(8);
  const dv = new DataView(buf);
  dv.setFloat64(0, x, true);
  return dv.getBigUint64(0, true).toString();
}

const clamp8 = new Uint8ClampedArray(1);
function evalIdlNum(x) {
  clamp8[0] = x;
  let u32EnforceOk = false;
  let u32EnforceVal = 0;
  if (Number.isFinite(x)) {
    const ip = Math.trunc(x);
    if (ip >= 0 && ip <= 0xFFFFFFFF) {
      u32EnforceOk = true;
      u32EnforceVal = ip === 0 ? 0 : ip;
    }
  }
  return {
    i32_std: x | 0,
    u32_std: x >>> 0,
    u8_clamp: clamp8[0],
    u32_enforce_ok: u32EnforceOk,
    u32_enforce_val: u32EnforceVal,
  };
}

const numOut = input.num_bits.map(s => evalIdlNum(bitsToF64(s)));

const dyadicStrOut = input.dyadic_bits.map(s => String(bitsToF64(s)));

const strOut = input.utf16_cases.map(units => {
  const s = String.fromCharCode(...units);
  const usv = util.toUSVString(s);
  const usvUnits = Array.from({ length: usv.length }, (_, i) => usv.charCodeAt(i));
  let byteOk = true;
  try {
    // Web IDL ByteString check: every code unit <= 255
    btoa(s);
  } catch (_) {
    byteOk = false;
  }
  return { usvUnits, byteOk };
});

const strNumOut = input.str_num_cases.map(units => {
  let s = '';
  for (let i = 0; i < units.length; i += 4096) {
    s += String.fromCharCode(...units.slice(i, i + 4096));
  }
  const x = +s;
  return {
    is_nan: Number.isNaN(x),
    bits: f64ToBitsStr(x),
    idl: evalIdlNum(x),
  };
});

const engine = `Node.js ${process.version} (V8 ${process.versions.v8})`;
process.stdout.write(JSON.stringify({ engine, numOut, dyadicStrOut, strOut, strNumOut }));
"#;

    let mut child = Command::new(&node_bin)
        .arg("-e")
        .arg(js_oracle)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("spawn node differential oracle");
    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(payload.to_string().as_bytes())
            .unwrap();
    }
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "Node oracle failed: {}", String::from_utf8_lossy(&out.stderr));
    let parsed: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    let engine = parsed["engine"].as_str().unwrap().to_string();

    let arena = JsObjectArena::new();
    let mut diff_cases = 0usize;

    for (idx, &bits) in num_bits.iter().enumerate() {
        let row = &parsed["numOut"][idx];
        let v = JsValue::Number(bits);
        let ours_i32 = to_idl_long(&arena, &v, IntAttr::Standard).unwrap();
        let ours_u32 = to_idl_unsigned_long(&arena, &v, IntAttr::Standard).unwrap();
        let ours_u8_clamp = to_idl_octet(&arena, &v, IntAttr::Clamp).unwrap();
        let ours_u32_enf = to_idl_unsigned_long(&arena, &v, IntAttr::EnforceRange);

        assert_eq!(ours_i32 as i64, row["i32_std"].as_i64().unwrap(), "i32 std bits={bits:#x}");
        assert_eq!(ours_u32 as u64, row["u32_std"].as_u64().unwrap(), "u32 std bits={bits:#x}");
        assert_eq!(
            ours_u8_clamp as u64,
            row["u8_clamp"].as_u64().unwrap(),
            "u8 clamp bits={bits:#x}"
        );
        let exp_enf_ok = row["u32_enforce_ok"].as_bool().unwrap();
        assert_eq!(ours_u32_enf.is_ok(), exp_enf_ok, "u32 EnforceRange ok bits={bits:#x}");
        if exp_enf_ok {
            assert_eq!(
                ours_u32_enf.unwrap() as u64,
                row["u32_enforce_val"].as_u64().unwrap(),
                "u32 EnforceRange val bits={bits:#x}"
            );
        }
        diff_cases += 4;
    }

    for (idx, &bits) in dyadic_bits.iter().enumerate() {
        let expected = parsed["dyadicStrOut"][idx].as_str().unwrap();
        let got = to_idl_dom_string(&arena, &JsValue::Number(bits), false).unwrap();
        assert_eq!(got, utf16(expected), "Number::toString diff on {expected}");
        diff_cases += 1;
    }

    for (idx, units) in utf16_cases.iter().enumerate() {
        let row = &parsed["strOut"][idx];
        let expected_usv: Vec<u16> = row["usvUnits"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap() as u16)
            .collect();
        let expected_byte_ok = row["byteOk"].as_bool().unwrap();

        let v = JsValue::String(units.clone());
        let ours_usv = to_idl_usv_string(&arena, &v).unwrap();
        assert_eq!(ours_usv, expected_usv, "USVString diff on {units:?}");
        let ours_bs = to_idl_byte_string(&arena, &v);
        assert_eq!(ours_bs.is_ok(), expected_byte_ok, "ByteString diff on {units:?}");
        diff_cases += 2;
    }

    for (idx, units) in str_num_cases.iter().enumerate() {
        let row = &parsed["strNumOut"][idx];
        let label = String::from_utf16_lossy(&units[..units.len().min(64)]);
        let ours_bits = string_to_number_bits(units);
        if row["is_nan"].as_bool().unwrap() {
            assert_eq!(ours_bits, F64_CANON_NAN, "StringToNumber NaN diff on {label:?}");
        } else {
            let v8_bits: u64 = row["bits"].as_str().unwrap().parse().unwrap();
            assert_eq!(
                ours_bits, v8_bits,
                "StringToNumber IEEE-754 bits diff on {label:?}: ours={ours_bits:#018x} v8={v8_bits:#018x}"
            );
        }

        let idl = &row["idl"];
        let v = JsValue::String(units.clone());
        let ours_i32 = to_idl_long(&arena, &v, IntAttr::Standard).unwrap();
        let ours_u32 = to_idl_unsigned_long(&arena, &v, IntAttr::Standard).unwrap();
        let ours_u8_clamp = to_idl_octet(&arena, &v, IntAttr::Clamp).unwrap();
        let ours_u32_enf = to_idl_unsigned_long(&arena, &v, IntAttr::EnforceRange);

        assert_eq!(ours_i32 as i64, idl["i32_std"].as_i64().unwrap(), "str i32 std on {label:?}");
        assert_eq!(ours_u32 as u64, idl["u32_std"].as_u64().unwrap(), "str u32 std on {label:?}");
        assert_eq!(
            ours_u8_clamp as u64,
            idl["u8_clamp"].as_u64().unwrap(),
            "str u8 clamp on {label:?}"
        );
        let exp_enf_ok = idl["u32_enforce_ok"].as_bool().unwrap();
        assert_eq!(ours_u32_enf.is_ok(), exp_enf_ok, "str u32 EnforceRange ok on {label:?}");
        if exp_enf_ok {
            assert_eq!(
                ours_u32_enf.unwrap() as u64,
                idl["u32_enforce_val"].as_u64().unwrap(),
                "str u32 EnforceRange val on {label:?}"
            );
        }
        diff_cases += 5;
    }

    assert!(diff_cases >= 1600);
    (engine, diff_cases)
}

// ---------------------------------------------------------------------------------------
// 3. Capability Handle Security & Cross-Realm/Origin Non-Interference Checks
// ---------------------------------------------------------------------------------------

fn run_capability_security_checks() -> usize {
    let xrealm_src = include_str!("data/invalid-this-value-cross-realm.html");
    assert!(xrealm_src.contains("Cross-realm operation throws"));

    let mut table = KernelCapTable::new();
    let mut arena = JsObjectArena::new();
    let mut state = HostState::new();
    let mut checks = 0usize;

    let realm1 = RealmId(1);
    let realm2 = RealmId(2);
    let origin_a = OriginId(100);
    let origin_b = OriginId(200);

    // Allocate capabilities across all 7 CapKinds
    let h_doc = table
        .allocate(realm1, origin_a, CapKind::DomDocument, PERM_READ | PERM_WRITE, 1)
        .unwrap();
    let h_node = table
        .allocate(realm1, origin_a, CapKind::DomNode, PERM_READ | PERM_WRITE, 1)
        .unwrap();
    let h_fetch = table
        .allocate(realm1, origin_a, CapKind::FetchOrigin, PERM_NETWORK, 0)
        .unwrap();
    let h_cookie = table
        .allocate(realm1, origin_a, CapKind::CookieJarOrigin, PERM_READ | PERM_WRITE, 0)
        .unwrap();
    let h_storage = table
        .allocate(realm1, origin_a, CapKind::StorageOrigin, PERM_READ | PERM_WRITE, 0)
        .unwrap();
    let h_console = table
        .allocate(realm1, origin_a, CapKind::ConsoleSink, PERM_LOG, 0)
        .unwrap();
    let h_timer = table
        .allocate(realm1, origin_a, CapKind::TimerQueue, PERM_SCHEDULE, 0)
        .unwrap();
    let h_storage_b = table
        .allocate(realm2, origin_b, CapKind::StorageOrigin, PERM_READ | PERM_WRITE, 0)
        .unwrap();
    checks += 8;

    // 1. Valid dispatch on Realm 1 / Origin A & Realm 2 / Origin B
    let set_op_a = make_plain_obj(
        &mut arena,
        vec![
            ("key", true, js_str("token")),
            ("op", true, js_str("set")),
            ("value", true, js_str("secret-A")),
        ],
        vec![],
    );
    let set_op_b = make_plain_obj(
        &mut arena,
        vec![
            ("key", true, js_str("token")),
            ("op", true, js_str("set")),
            ("value", true, js_str("secret-B")),
        ],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_storage,
            &HostRequest::StorageCommand {
                target_origin: origin_a,
                storage_op_js: set_op_a,
                is_write: true,
            },
        ),
        Ok(JsValue::Undefined)
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm2,
            h_storage_b,
            &HostRequest::StorageCommand {
                target_origin: origin_b,
                storage_op_js: set_op_b,
                is_write: true,
            },
        ),
        Ok(JsValue::Undefined)
    );
    checks += 2;

    // 2. Cross-Realm & Cross-Origin Non-Interference:
    // Realm 2 attempting to use Realm 1's handle, OR Realm 1 attempting to target Origin B with Origin A's handle
    let snapshot = state.clone();
    let get_op = make_plain_obj(
        &mut arena,
        vec![("key", true, js_str("token")), ("op", true, js_str("get"))],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm2,
            h_storage,
            &HostRequest::StorageCommand {
                target_origin: origin_a,
                storage_op_js: get_op.clone(),
                is_write: false,
            },
        ),
        Err(HostError::CrossRealmViolation)
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_storage,
            &HostRequest::StorageCommand {
                target_origin: origin_b,
                storage_op_js: get_op.clone(),
                is_write: false,
            },
        ),
        Err(HostError::CrossRealmViolation)
    );
    assert_eq!(state, snapshot, "zero state mutation on CrossRealmViolation");
    checks += 2;

    // 3. Handle Forgery / Tamper Resistance (perms, generation, realm, kind, out-of-bounds slot)
    let forged_candidates = [
        CapHandle { perms: PERM_ALL, ..h_storage },
        CapHandle { generation: h_storage.generation + 1, ..h_storage },
        CapHandle { realm: realm2, ..h_storage },
        CapHandle { kind: CapKind::FetchOrigin, ..h_storage },
        CapHandle { slot: 9999, ..h_storage },
    ];
    for forged in forged_candidates {
        assert_eq!(
            dispatch(
                &table,
                &arena,
                &mut state,
                forged.realm,
                forged,
                &HostRequest::StorageCommand {
                    target_origin: origin_a,
                    storage_op_js: get_op.clone(),
                    is_write: false,
                },
            ),
            Err(HostError::RevokedOrInvalidHandle)
        );
        checks += 1;
    }
    assert_eq!(state, snapshot);

    // 4. Permission Attenuation Monotonicity:
    // Escalating `h_fetch` (PERM_NETWORK) to `PERM_NETWORK | PERM_WRITE` is refused!
    assert_eq!(
        table.attenuate(h_fetch, PERM_NETWORK | PERM_WRITE),
        Err(HostError::PermissionEscalation)
    );
    // Attenuating `h_storage` (READ | WRITE) to read-only (`PERM_READ`) succeeds:
    let h_storage_ro = table.attenuate(h_storage, CapPerms::new(PERM_READ).0).unwrap();
    assert!(CapPerms::new(h_storage_ro.perms).is_subset_of(CapPerms::new(h_storage.perms)));
    // Read succeeds on `h_storage_ro`:
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_storage_ro,
            &HostRequest::StorageCommand {
                target_origin: origin_a,
                storage_op_js: get_op.clone(),
                is_write: false,
            },
        ),
        Ok(js_str("secret-A"))
    );
    // Write is refused with `InsufficientPermissions` on `h_storage_ro`:
    let overwrite_op = make_plain_obj(
        &mut arena,
        vec![
            ("key", true, js_str("token")),
            ("op", true, js_str("set")),
            ("value", true, js_str("hacked")),
        ],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_storage_ro,
            &HostRequest::StorageCommand {
                target_origin: origin_a,
                storage_op_js: overwrite_op,
                is_write: true,
            },
        ),
        Err(HostError::InsufficientPermissions)
    );
    // Further attenuating `h_storage_ro` to `PERM_NONE` succeeds, while escalating back to `PERM_WRITE` fails:
    assert_eq!(table.attenuate(h_storage_ro, PERM_WRITE), Err(HostError::PermissionEscalation));
    let _h_none = table.attenuate(h_storage_ro, PERM_NONE).unwrap();
    checks += 5;

    // 5. Exercise remaining CapKinds (DomDocument, DomNode, FetchOrigin, CookieJarOrigin, ConsoleSink, TimerQueue)
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_doc,
            &HostRequest::DomSetTitle {
                target_origin: origin_a,
                title_js: js_str("Verified Page"),
            },
        ),
        Ok(JsValue::Undefined)
    );
    let node_mut = make_plain_obj(
        &mut arena,
        vec![
            ("nodeId", true, js_f64(1.0)),
            ("op", true, js_str("setText")),
            ("textContent", true, js_str("Updated")),
        ],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_node,
            &HostRequest::DomMutateNode {
                target_origin: origin_a,
                node_op_js: node_mut,
            },
        ),
        Ok(JsValue::Bool(true))
    );
    // Per-Node Confinement (No Confused-Deputy Across DOM Nodes):
    // Create a second node (`node_id = 42`) in the same `(realm1, origin_a)` partition, and prove
    // a capability handle scoped to node `42` (`resource_id = 42`) CANNOT mutate node `1` (and
    // conversely `h_node` scoped to node `1` CANNOT mutate node `42`)!
    let h_doc_42 = table
        .allocate(realm1, origin_a, CapKind::DomDocument, PERM_READ | PERM_WRITE, 42)
        .unwrap();
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_doc_42,
            &HostRequest::DomSetTitle {
                target_origin: origin_a,
                title_js: js_str("Frame 42"),
            },
        ),
        Ok(JsValue::Undefined)
    );
    let h_node_42 = table
        .allocate(realm1, origin_a, CapKind::DomNode, PERM_READ | PERM_WRITE, 42)
        .unwrap();
    let hijack_node_1 = make_plain_obj(
        &mut arena,
        vec![
            ("nodeId", true, js_f64(1.0)),
            ("op", true, js_str("setText")),
            ("textContent", true, js_str("Hijacked")),
        ],
        vec![],
    );
    let pre_hijack_state = state.clone();
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_node_42,
            &HostRequest::DomMutateNode {
                target_origin: origin_a,
                node_op_js: hijack_node_1,
            },
        ),
        Err(HostError::InsufficientPermissions)
    );
    assert_eq!(state, pre_hijack_state, "confused-deputy node mismatch must not mutate state");
    // Symmetric check: `h_node` (resource_id = 1) cannot mutate node `42` either:
    let mutate_node_42 = make_plain_obj(
        &mut arena,
        vec![
            ("nodeId", true, js_f64(42.0)),
            ("op", true, js_str("setText")),
            ("textContent", true, js_str("Node42Text")),
        ],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_node,
            &HostRequest::DomMutateNode {
                target_origin: origin_a,
                node_op_js: mutate_node_42.clone(),
            },
        ),
        Err(HostError::InsufficientPermissions)
    );
    assert_eq!(state, pre_hijack_state);
    // Meanwhile `h_node_42` CAN mutate its own `nodeId == 42`, leaving node `1` untouched:
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_node_42,
            &HostRequest::DomMutateNode {
                target_origin: origin_a,
                node_op_js: mutate_node_42,
            },
        ),
        Ok(JsValue::Bool(true))
    );
    assert_eq!(state.dom_nodes[0].node_id, 1);
    assert_eq!(state.dom_nodes[0].text_content, Some(utf16("Updated")));
    assert_eq!(state.dom_nodes[1].node_id, 42);
    assert_eq!(state.dom_nodes[1].text_content, Some(utf16("Node42Text")));
    checks += 5;
    let url_dict = make_plain_obj(
        &mut arena,
        vec![("href", true, js_str("https://origin-a.example/api"))],
        vec![],
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_fetch,
            &HostRequest::FetchSend {
                target_origin: origin_a,
                url_href_js: url_dict,
                request_init_js: JsValue::Undefined,
            },
        ),
        Ok(JsValue::Bool(true))
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_cookie,
            &HostRequest::CookieSet {
                target_origin: origin_a,
                cookie_js: js_str("sid=abc123"),
            },
        ),
        Ok(JsValue::Undefined)
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_cookie,
            &HostRequest::CookieCount { target_origin: origin_a },
        ),
        Ok(js_f64(1.0))
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_console,
            &HostRequest::ConsoleLog {
                target_origin: origin_a,
                message_js: JsValue::String(parse_js_utf16_literal("log:\\uD800")),
            },
        ),
        Ok(JsValue::Undefined)
    );
    assert_eq!(state.console[0].message, parse_js_utf16_literal("log:\\uFFFD"));
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_timer,
            &HostRequest::TimerSetTimeout {
                target_origin: origin_a,
                delay_js: js_f64(-25.0), // clamped to 0ms!
                callback_id_js: js_f64(7.0),
            },
        ),
        Ok(js_f64(0.0))
    );
    assert_eq!(state.timers[0].delay_ms, 0);
    checks += 7;

    // 6. Use-After-Revoke & Permanent ABA Non-Revivability Across Slot Reuse:
    let state_before_revoke = state.clone();
    let res_revoked = verified_revoke_then_dispatch_refused(
        &mut table,
        &arena,
        &mut state,
        realm1,
        h_cookie,
        &HostRequest::CookieCount { target_origin: origin_a },
    );
    assert_eq!(res_revoked, Err(HostError::RevokedOrInvalidHandle));
    assert_eq!(state, state_before_revoke);

    // Reallocate into the retired slot (`h_cookie.slot`) and verify the old handle `h_cookie`
    // STILL fails with `RevokedOrInvalidHandle` even with identical realm/origin/kind/perms!
    let h_cookie_reborn = table
        .allocate(realm1, origin_a, CapKind::CookieJarOrigin, PERM_READ | PERM_WRITE, 0)
        .unwrap();
    assert_eq!(h_cookie_reborn.slot, h_cookie.slot);
    assert_eq!(h_cookie_reborn.generation, h_cookie.generation + 1);
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_cookie,
            &HostRequest::CookieCount { target_origin: origin_a },
        ),
        Err(HostError::RevokedOrInvalidHandle)
    );
    assert_eq!(
        dispatch(
            &table,
            &arena,
            &mut state,
            realm1,
            h_cookie_reborn,
            &HostRequest::CookieCount { target_origin: origin_a },
        ),
        Ok(js_f64(1.0))
    );
    checks += 3;

    checks
}

// ---------------------------------------------------------------------------------------
// 4. Engine-Wide Static Zero-Ambient-Authority & Escape-Hatch Scanner
// ---------------------------------------------------------------------------------------

/// Strip `//` line comments, `/* ... */` nested block comments, raw string literals `r#*"..."#*`,
/// and `"..."` string literals (preserving `\n` line numbers) so the scanner inspects actual
/// Rust code tokens without comment/string false positives.
fn strip_comments_and_strings(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            let mut depth = 1usize;
            while i + 1 < bytes.len() && depth > 0 {
                if bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'*' && bytes[i + 1] == b'/' {
                    depth -= 1;
                    i += 2;
                } else {
                    if bytes[i] == b'\n' {
                        out.push('\n');
                    }
                    i += 1;
                }
            }
        } else if bytes[i] == b'r' && i + 1 < bytes.len() && (bytes[i + 1] == b'#' || bytes[i + 1] == b'"') {
            let mut j = i + 1;
            let mut hashes = 0usize;
            while j < bytes.len() && bytes[j] == b'#' {
                hashes += 1;
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'"' {
                out.push('"');
                j += 1;
                while j < bytes.len() {
                    if bytes[j] == b'"'
                        && j + hashes < bytes.len()
                        && bytes[j + 1..j + 1 + hashes].iter().all(|&b| b == b'#')
                    {
                        out.push('"');
                        j += 1 + hashes;
                        break;
                    }
                    if bytes[j] == b'\n' {
                        out.push('\n');
                    }
                    j += 1;
                }
                i = j;
            } else {
                out.push('r');
                i += 1;
            }
        } else if bytes[i] == b'"' {
            out.push('"');
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 2;
                } else {
                    if bytes[i] == b'\n' {
                        out.push('\n');
                    }
                    i += 1;
                }
            }
            if i < bytes.len() {
                out.push('"');
                i += 1;
            }
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

/// Split top-level comma-separated items inside a Rust `use` group `{ a, b::{c, d}, e }`.
fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (idx, ch) in s.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                let piece = s[start..idx].trim();
                if !piece.is_empty() {
                    parts.push(piece);
                }
                start = idx + 1;
            }
            _ => {}
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        parts.push(tail);
    }
    parts
}

/// Recursively flatten a Rust `use` tree (`std::{io, fs::{self, File}, net::TcpStream}`) into
/// canonical `::`-separated paths (`["std::io", "std::fs", "std::fs::File", "std::net::TcpStream"]`).
fn expand_use_tree(prefix: &str, tree: &str, out: &mut Vec<String>) {
    let compact: String = tree
        .split(" as ")
        .next()
        .unwrap_or(tree)
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let t = compact.strip_prefix("::").unwrap_or(&compact);
    if t.is_empty() {
        return;
    }
    if let Some(brace_idx) = t.find('{') {
        if let Some(close_idx) = t.rfind('}') {
            let head = t[..brace_idx].trim_end_matches("::");
            let new_prefix = match (prefix.is_empty(), head.is_empty()) {
                (true, true) => String::new(),
                (true, false) => head.to_string(),
                (false, true) => prefix.to_string(),
                (false, false) => format!("{prefix}::{head}"),
            };
            let inner = &t[brace_idx + 1..close_idx];
            for item in split_top_level_commas(inner) {
                expand_use_tree(&new_prefix, item, out);
            }
            return;
        }
    }
    if t == "self" {
        if !prefix.is_empty() {
            out.push(prefix.to_string());
        }
    } else if prefix.is_empty() {
        out.push(t.to_string());
    } else {
        out.push(format!("{prefix}::{t}"));
    }
}

/// Extract all `use ...;` statements (including `pub use`, `pub(crate) use`, and multi-line
/// nested braced `use` trees) from comment/string-stripped Rust code, returning `(line_no, path)`.
fn extract_flattened_use_paths(stripped: &str) -> Vec<(usize, String)> {
    let bytes = stripped.as_bytes();
    let mut results = Vec::new();
    let mut i = 0usize;
    let mut line_no = 1usize;

    let is_ident_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_';

    while i < bytes.len() {
        if bytes[i] == b'\n' {
            line_no += 1;
            i += 1;
            continue;
        }
        if i + 3 <= bytes.len()
            && &bytes[i..i + 3] == b"use"
            && (i == 0 || !is_ident_byte(bytes[i - 1]))
            && (i + 3 == bytes.len()
                || bytes[i + 3].is_ascii_whitespace()
                || bytes[i + 3] == b':'
                || bytes[i + 3] == b'{')
        {
            let use_line = line_no;
            let mut j = i + 3;
            let mut brace_depth = 0usize;
            while j < bytes.len() {
                if bytes[j] == b'\n' {
                    line_no += 1;
                } else if bytes[j] == b'{' {
                    brace_depth += 1;
                } else if bytes[j] == b'}' {
                    brace_depth = brace_depth.saturating_sub(1);
                } else if bytes[j] == b';' && brace_depth == 0 {
                    break;
                }
                j += 1;
            }
            let tree_str = &stripped[i + 3..j.min(bytes.len())];
            let mut paths = Vec::new();
            expand_use_tree("", tree_str, &mut paths);
            for p in paths {
                results.push((use_line, p));
            }
            i = (j + 1).min(bytes.len());
            continue;
        }
        i += 1;
    }
    results
}

fn classify_forbidden_use_path(path: &str) -> Option<&'static str> {
    let p = path.strip_prefix("::").unwrap_or(path);
    let check_prefix = |cand: &str| -> bool {
        p == cand || p.starts_with(&format!("{cand}::"))
    };
    if p == "std::*" {
        Some("std::* (wildcard ambient import)")
    } else if check_prefix("std::fs") {
        Some("std::fs")
    } else if check_prefix("std::net") {
        Some("std::net")
    } else if check_prefix("std::process") {
        Some("std::process")
    } else if check_prefix("std::env") {
        Some("std::env")
    } else if check_prefix("std::os") {
        Some("std::os")
    } else if check_prefix("std::arch::asm") || check_prefix("std::arch::global_asm") {
        Some("std::arch::asm")
    } else if check_prefix("core::arch::asm") || check_prefix("core::arch::global_asm") {
        Some("core::arch::asm")
    } else if check_prefix("libc") {
        Some("libc")
    } else if check_prefix("nix") {
        Some("nix")
    } else {
        None
    }
}

/// Scan a single Rust source file (stripped of comments & string literals) for both:
/// 1) Grouped/nested/multi-line `use` trees (`use std::{io, fs};`, `core::{mem, arch::asm}`, etc.),
/// 2) Inline fully-qualified ambient-authority or raw-syscall tokens (`std::fs`, `extern crate libc`, `syscall(`, etc.).
fn scan_rust_source_for_ambient_authority(rel_path: &str, raw: &str) -> Vec<String> {
    let inline_patterns: &[(&str, &str)] = &[
        ("std::fs", "std::fs"),
        ("std::net", "std::net"),
        ("std::process", "std::process"),
        ("std::env", "std::env"),
        ("std::os::", "std::os::"),
        ("libc::", "libc::"),
        ("nix::", "nix::"),
        ("extern crate libc", "externcratelibc"),
        ("extern crate nix", "externcratenix"),
        ("std::arch::asm", "std::arch::asm"),
        ("std::arch::global_asm", "std::arch::global_asm"),
        ("core::arch::asm", "core::arch::asm"),
        ("core::arch::global_asm", "core::arch::global_asm"),
        ("extern \"C\"", "extern\"C\""),
        ("extern \"system\"", "extern\"system\""),
        ("syscall(", "syscall("),
    ];

    let stripped = strip_comments_and_strings(raw);
    let mut violations = Vec::new();

    for (use_line, flat_path) in extract_flattened_use_paths(&stripped) {
        if let Some(label) = classify_forbidden_use_path(&flat_path) {
            let msg = format!(
                "{rel_path}:{use_line}: forbidden ambient-authority use `{label}` (expanded `{flat_path}`)"
            );
            if !violations.contains(&msg) {
                violations.push(msg);
            }
        }
    }

    for (line_no, line) in stripped.lines().enumerate() {
        let compact: String = line.chars().filter(|c| !c.is_whitespace()).collect();
        for &(label, compact_needle) in inline_patterns {
            if compact.contains(compact_needle) {
                let msg = format!(
                    "{rel_path}:{}: forbidden ambient-authority token `{label}`",
                    line_no + 1
                );
                if !violations.contains(&msg) {
                    violations.push(msg);
                }
            }
        }
    }

    violations
}

fn collect_non_test_rs_files(dir: &Path, acc: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    let mut sorted: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|x| x.path())).collect();
    sorted.sort();
    for path in sorted {
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else { continue };
        if path.is_dir() {
            if matches!(name, "tests" | "target" | ".cargo" | ".git") {
                continue;
            }
            collect_non_test_rs_files(&path, acc);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            acc.push(path);
        }
    }
}

#[derive(Debug)]
struct AuditSummary {
    crates_scanned: Vec<String>,
    files_scanned: usize,
    lines_scanned: usize,
    violations: Vec<String>,
    vjs_webidl_trusted: BTreeMap<&'static str, usize>,
}

fn run_ambient_authority_audit(browser_root: &Path) -> AuditSummary {
    let mut crate_dirs: Vec<PathBuf> = fs::read_dir(browser_root)
        .expect("read browser/ directory")
        .filter_map(|e| e.ok().map(|x| x.path()))
        .filter(|p| p.is_dir() && p.join("Cargo.toml").exists())
        .collect();
    crate_dirs.sort();

    let mut crates_scanned = Vec::new();
    let mut files_scanned = 0usize;
    let mut lines_scanned = 0usize;
    let mut violations = Vec::new();

    for crate_dir in &crate_dirs {
        let dir_name = crate_dir.file_name().unwrap().to_str().unwrap().to_string();
        let is_vjs_or_sandbox = dir_name.starts_with("vjs") || dir_name == "vwasm";
        let mut rs_files = Vec::new();
        collect_non_test_rs_files(crate_dir, &mut rs_files);
        crates_scanned.push(dir_name.clone());

        for fpath in rs_files {
            let raw = fs::read_to_string(&fpath).expect("read .rs source");
            files_scanned += 1;
            lines_scanned += raw.lines().count();
            if is_vjs_or_sandbox {
                let rel = fpath.strip_prefix(browser_root).unwrap().display().to_string();
                violations.extend(scan_rust_source_for_ambient_authority(&rel, &raw));
            }
        }
    }

    // Check `vjs-webidl/src/**/*.rs` for `#![forbid(unsafe_code)]` and zero trusted markers
    let webidl_root = browser_root.join("vjs-webidl");
    let lib_rs = fs::read_to_string(webidl_root.join("src/lib.rs")).unwrap();
    assert!(lib_rs.contains("#![forbid(unsafe_code)]"));

    let mut webidl_srcs = Vec::new();
    collect_non_test_rs_files(&webidl_root, &mut webidl_srcs);
    let combined_body: String = webidl_srcs
        .iter()
        .map(|p| fs::read_to_string(p).unwrap())
        .collect::<Vec<_>>()
        .join("\n");

    let count_word_call = |word: &str| -> usize {
        let stripped = strip_comments_and_strings(&combined_body);
        stripped
            .match_indices(word)
            .filter(|&(idx, _)| {
                let prev_ok = idx == 0
                    || !stripped.as_bytes()[idx - 1].is_ascii_alphanumeric()
                        && stripped.as_bytes()[idx - 1] != b'_';
                let rest = stripped[idx + word.len()..].trim_start();
                prev_ok && rest.starts_with('(')
            })
            .count()
    };

    let stripped_body = strip_comments_and_strings(&combined_body);
    let mut trusted = BTreeMap::new();
    trusted.insert("assume", count_word_call("assume"));
    trusted.insert("admit", count_word_call("admit"));
    trusted.insert("external_body", stripped_body.matches("verifier::external_body").count());
    let ext_total = stripped_body.matches("verifier::external").count();
    let ext_body = stripped_body.matches("verifier::external_").count();
    trusted.insert("external", ext_total.saturating_sub(ext_body));
    trusted.insert("assume_specification", stripped_body.matches("assume_specification").count());
    let unsafe_count = stripped_body.matches("unsafe {").count()
        + stripped_body.matches("unsafe fn").count()
        + stripped_body.matches("unsafe impl").count();
    trusted.insert("unsafe", unsafe_count);

    AuditSummary {
        crates_scanned,
        files_scanned,
        lines_scanned,
        violations,
        vjs_webidl_trusted: trusted,
    }
}

/// Pure-Rust FIPS 180-4 / RFC 6234 SHA-256 digest for byte-for-byte `PROVENANCE` verification.
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
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
        for (dst, add) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *dst = dst.wrapping_add(add);
        }
    }

    h.iter().map(|word| format!("{word:08x}")).collect()
}

#[test]
fn wpt_enforcerange_conversions() {
    let s = run_wpt_enforcerange();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_clamp_ties_to_even_conversions() {
    let s = run_wpt_clamp();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_usvstring_surrogates_and_idempotence() {
    let s = run_wpt_usvstring_surrogates();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_urlsearchparams_records_and_sequences() {
    let s = run_wpt_urlsearchparams_records_and_sequences();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_bytestring_and_headers_records() {
    let s = run_wpt_bytestring_and_headers_record();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_event_and_host_dictionaries_lexicographic_order() {
    let s = run_wpt_event_and_dictionaries();
    assert_eq!(s.passed, s.total);
}

#[test]
fn wpt_dom_exception_and_sequence_conversions() {
    let s = run_wpt_dom_exception_and_sequence();
    assert_eq!(s.passed, s.total);
}

#[test]
fn all_eight_integer_types_and_primitives_roundtrip() {
    let mut arena = JsObjectArena::new();
    // any & undefined & boolean
    assert_eq!(to_idl_undefined(&js_f64(99.0)), ());
    assert_eq!(to_js_undefined(), JsValue::Undefined);
    assert!(!to_idl_boolean(&JsValue::Undefined));
    assert!(!to_idl_boolean(&JsValue::Null));
    assert!(!to_idl_boolean(&JsValue::Number(F64_NEG_ZERO)));
    assert!(!to_idl_boolean(&JsValue::Number(F64_CANON_NAN)));
    assert!(to_idl_boolean(&js_str("0")));
    assert_eq!(
        to_idl_any(&JsValue::Number(0x7FF0_0000_0000_1234)),
        IdlAny::UnrestrictedDouble(F64_CANON_NAN)
    );

    // Roundtrip across all 8 integer types under Standard, EnforceRange, and Clamp
    for attr in [IntAttr::Standard, IntAttr::EnforceRange, IntAttr::Clamp] {
        for v in [i8::MIN, -1, 0, 1, i8::MAX] {
            assert_eq!(to_idl_byte(&arena, &to_js_byte(v), attr), Ok(v));
        }
        for v in [0u8, 1, 128, u8::MAX] {
            assert_eq!(to_idl_octet(&arena, &to_js_octet(v), attr), Ok(v));
        }
        for v in [i16::MIN, -257, 0, 257, i16::MAX] {
            assert_eq!(to_idl_short(&arena, &to_js_short(v), attr), Ok(v));
        }
        for v in [0u16, 1, 32768, u16::MAX] {
            assert_eq!(to_idl_unsigned_short(&arena, &to_js_unsigned_short(v), attr), Ok(v));
        }
        for v in [i32::MIN, -65537, 0, 65537, i32::MAX] {
            assert_eq!(to_idl_long(&arena, &to_js_long(v), attr), Ok(v));
        }
        for v in [0u32, 1, 2147483648, u32::MAX] {
            assert_eq!(to_idl_unsigned_long(&arena, &to_js_unsigned_long(v), attr), Ok(v));
        }
        for v in [MIN_SAFE_INT_I64, -4294967297, 0, 4294967297, MAX_SAFE_INT_I64] {
            assert_eq!(to_idl_long_long(&arena, &to_js_long_long(v), attr), Ok(v));
        }
        for v in [0u64, 1, 4294967296, MAX_SAFE_INT_U64] {
            assert_eq!(
                to_idl_unsigned_long_long(&arena, &to_js_unsigned_long_long(v), attr),
                Ok(v)
            );
        }
    }

    // Nullable & record ToJS roundtrip
    assert_eq!(to_idl_nullable_long(&arena, &to_js_nullable_long(None), IntAttr::Standard), Ok(None));
    assert_eq!(
        to_idl_nullable_long(&arena, &to_js_nullable_long(Some(-42)), IntAttr::Standard),
        Ok(Some(-42))
    );
    let entries = vec![(utf16("k1"), utf16("v1")), (utf16("k2"), utf16("v2"))];
    let rec_js = to_js_record_dom_string(&mut arena, &entries).unwrap();
    assert_eq!(to_idl_record_dom_string(&arena, &rec_js), Ok(entries));
}

#[test]
fn capability_security_and_non_interference_suite() {
    let cnt = run_capability_security_checks();
    assert!(cnt >= 30);
}

#[test]
fn node_v8_live_differential_oracle_suite() {
    let (engine, diff_cases) = run_node_v8_differential_oracle();
    assert!(engine.starts_with("Node.js v"));
    assert!(diff_cases >= 1000);
}

#[test]
fn end_to_end_wpt_differential_security_and_ambient_audit() {
    let suites = vec![
        run_wpt_enforcerange(),
        run_wpt_clamp(),
        run_wpt_usvstring_surrogates(),
        run_wpt_urlsearchparams_records_and_sequences(),
        run_wpt_bytestring_and_headers_record(),
        run_wpt_event_and_dictionaries(),
        run_wpt_dom_exception_and_sequence(),
    ];

    let wpt_passed: usize = suites.iter().map(|s| s.passed).sum();
    let wpt_total: usize = suites.iter().map(|s| s.total).sum();
    assert_eq!(wpt_passed, wpt_total);
    assert!(wpt_passed >= 100, "expected >= 100 WPT assertions, got {wpt_passed}");

    let (engine, diff_cases) = run_node_v8_differential_oracle();
    let cap_cases = run_capability_security_checks();

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let browser_root = manifest_dir.parent().expect("browser/ parent directory");
    let audit = run_ambient_authority_audit(browser_root);

    assert!(
        audit.violations.is_empty(),
        "Ambient-authority violations detected in vjs* crates: {:?}",
        audit.violations
    );
    for (&marker, &cnt) in &audit.vjs_webidl_trusted {
        assert_eq!(cnt, 0, "Trusted escape-hatch marker `{marker}` must be 0, found {cnt}");
    }

    let report = serde_json::json!({
        "crate": "vjs_webidl",
        "step": "J4b",
        "spec_source": "whatwg/webidl@54a5f2de6a34e27a517a49370bc07d8943b0be11",
        "wpt_source": "web-platform-tests/wpt@e8ca145562683547fb32faa7cfa9feb4cc99054b",
        "wpt_passed": wpt_passed,
        "wpt_total": wpt_total,
        "wpt_failed": wpt_total - wpt_passed,
        "wpt_suites": suites.iter().map(|s| serde_json::json!({
            "name": s.name,
            "wpt_path": s.wpt_path,
            "passed": s.passed,
            "total": s.total,
        })).collect::<Vec<_>>(),
        "differential_oracle": {
            "engine": engine,
            "cases_passed": diff_cases,
            "cases_total": diff_cases,
        },
        "capability_security_cases": cap_cases,
        "ambient_authority_audit": {
            "crates_scanned": audit.crates_scanned,
            "files_scanned": audit.files_scanned,
            "lines_scanned": audit.lines_scanned,
            "forbidden_imports_found": audit.violations.len(),
            "violations": audit.violations,
            "trusted_markers": audit.vjs_webidl_trusted,
        },
    });

    let report_path = manifest_dir.join("report.json");
    fs::write(&report_path, serde_json::to_string_pretty(&report).unwrap() + "\n")
        .expect("write browser/vjs-webidl/report.json");
}

#[test]
fn ambient_authority_scanner_catches_braced_and_nested_imports() {
    // 1. Simple braced import (`use std::{io, fs};`)
    let v1 = scan_rust_source_for_ambient_authority("synth1.rs", "use std::{io, fs};\n");
    assert_eq!(v1.len(), 1, "expected std::fs violation, got {v1:?}");
    assert!(v1[0].contains("std::fs"));

    // 2. Multi-capability grouped import (`net`, `env`, `process` alongside benign `BTreeMap`)
    let v2 = scan_rust_source_for_ambient_authority(
        "synth2.rs",
        "use std::{collections::BTreeMap, net::TcpStream, env::var, process::Command};\n",
    );
    assert_eq!(v2.len(), 3, "expected 3 violations (net, env, process), got {v2:?}");
    assert!(v2.iter().any(|m| m.contains("std::net")));
    assert!(v2.iter().any(|m| m.contains("std::env")));
    assert!(v2.iter().any(|m| m.contains("std::process")));

    // 3. Multi-line nested `pub(crate) use ::std::{..., os::{...}}` and `core::{..., arch::asm}`
    let v3 = scan_rust_source_for_ambient_authority(
        "synth3.rs",
        "pub(crate) use ::std::{\n    fmt::Debug,\n    os::{fd::RawFd, unix::net::UnixStream},\n};\nuse core::{mem::size_of, arch::{asm, global_asm}};\n",
    );
    assert!(v3.iter().any(|m| m.contains("std::os")), "expected std::os in {v3:?}");
    assert!(v3.iter().any(|m| m.contains("core::arch::asm")), "expected core::arch::asm in {v3:?}");

    // 4. Wildcard `use std::*;` and `extern crate libc;`
    let v4 = scan_rust_source_for_ambient_authority(
        "synth4.rs",
        "use std::*;\nextern crate libc;\n",
    );
    assert_eq!(v4.len(), 2, "expected wildcard + libc violations, got {v4:?}");

    // 5. Benign grouped imports + comments/strings mentioning `use std::{io, fs};` produce 0 false positives
    let clean = scan_rust_source_for_ambient_authority(
        "clean.rs",
        "// use std::{io, fs};\n/* use core::{mem, arch::asm}; */\nuse std::{collections::{BTreeMap, VecDeque}, fmt::{self, Debug}};\nfn msg() -> &'static str { \"use std::{net::TcpStream, process::Command};\" }\n",
    );
    assert!(clean.is_empty(), "expected 0 violations on clean source, got {clean:?}");
}

#[test]
fn verify_provenance_manifest_integrity() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data_dir = manifest_dir.join("tests/data");
    let license_text = fs::read_to_string(data_dir.join("LICENSE"))
        .expect("tests/data/LICENSE must be present alongside PROVENANCE");
    assert!(license_text.contains("3-Clause BSD License"));
    assert!(license_text.contains("web-platform-tests contributors"));
    let prov = fs::read_to_string(data_dir.join("PROVENANCE")).expect("read PROVENANCE");
    assert!(prov.contains("web-platform-tests/wpt@e8ca145562683547fb32faa7cfa9feb4cc99054b"));
    assert!(prov.contains("BSD-3-Clause"));

    let mut file_entries = 0usize;
    for line in prov.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let (local_file, rest) = trimmed.split_once(':').expect("PROVENANCE entry format");
        let p = data_dir.join(local_file.trim());
        assert!(p.exists(), "PROVENANCE file missing on disk: {}", p.display());
        let bytes = fs::read(&p).expect("read WPT file");
        assert!(!bytes.is_empty());

        let sha_marker = "sha256=";
        let sha_start = rest.find(sha_marker).expect("sha256 recorded in PROVENANCE") + sha_marker.len();
        let expected_sha = &rest[sha_start..sha_start + 64];
        let actual_sha = sha256_hex(&bytes);
        assert_eq!(
            actual_sha, expected_sha,
            "SHA-256 mismatch for pinned WPT file {}",
            local_file.trim()
        );
        file_entries += 1;
    }
    assert_eq!(file_entries, 13);
}
