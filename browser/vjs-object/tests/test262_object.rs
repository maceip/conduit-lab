//! Integration, real pinned `tc39/test262`, and live Node/V8 differential test suite for `vjs_object`.
//!
//! Executes:
//! 1. Exhaustive & property-based tests of IEEE-754 `u32` bit conversions, `SameValue`,
//!    `PropKey` canonicalization, §6.2.6 `PropertyDescriptor`, §10.1.6.3 `ValidateAndApplyPropertyDescriptor`,
//!    §10.1 Ordinary internal methods, §7.3.15–7.3.16 `SetIntegrityLevel` & `TestIntegrityLevel`,
//!    §10.4.2 Array exotic `ArrayCreate` / `ArraySetLength` / `[[DefineOwnProperty]]`, and §6.1.7.3 invariants.
//! 2. All 100 real pinned `tc39/test262` `.js` files under `tests/data/built-ins/Object/**` and
//!    `tests/data/built-ins/Array/length/**` parsed from JS source and evaluated directly against
//!    `vjs_object::Heap` AND cross-checked against live Node.js V8.
//! 3. 600 multi-step randomized Object & Array mutation traces differentially tested against live
//!    Node.js V8 (`/Users/mac/.nvm/versions/node/v24.15.0/bin/node`), writing `report.json`.

use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::{json, Value as JsonValue};

use vjs_object::array::{
    array_create, array_create_checked, array_define_own_property, array_length, array_set_length,
    coerce_array_length_value, define_own_property, js_set,
};
use vjs_object::descriptor::{
    complete_property_descriptor, from_complete_descriptor, is_accessor_descriptor,
    is_compatible_property_descriptor, is_data_descriptor, is_generic_descriptor,
    validate_and_apply_property_descriptor, validate_descriptor_fields, CompleteDescriptor,
    PropertyDescriptor,
};
use vjs_object::heap::{
    f64_bits_to_exact_u32, length_prop_key, prop_key_from_ascii, prop_key_from_utf16, same_value,
    same_value_zero, u32_to_f64_bits, Heap, JsBigInt, JsError, JsVal, ObjId, ObjectKind, PropKey,
    CANONICAL_NAN_BITS, NEG_ZERO_BITS, POS_ZERO_BITS,
};
use vjs_object::ordinary::{
    object_freeze, object_is_frozen, object_is_sealed, object_seal, ordinary_define_own_property,
    ordinary_delete, ordinary_get, ordinary_get_own_property, ordinary_get_prototype_of,
    ordinary_has_property, ordinary_is_extensible, ordinary_own_property_keys,
    ordinary_prevent_extensions, ordinary_set, ordinary_set_prototype_of, GetOutcome, SetOutcome,
};

const NODE_BIN: &str = "/Users/mac/.nvm/versions/node/v24.15.0/bin/node";

/// Runs a script of any size on Node/V8 through stdin. Linux limits one argument to 128 KiB, so
/// `node -e` cannot carry the batched scripts.
fn run_node_stdin(script: &str) -> std::process::Output {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(NODE_BIN)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start Node.js V8 oracle");
    // Node reads the whole script before running it, so this cannot deadlock against its output.
    let mut stdin = child.stdin.take().unwrap();
    stdin.write_all(script.as_bytes()).expect("failed to send script to Node.js");
    drop(stdin);
    child.wait_with_output().expect("failed to execute Node.js V8 oracle")
}

fn utf16_from_str(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn utf16_to_string(u: &[u16]) -> String {
    String::from_utf16_lossy(u)
}

fn js_str(s: &str) -> JsVal {
    JsVal::Str(utf16_from_str(s))
}

fn js_num(n: f64) -> JsVal {
    JsVal::NumberBits(n.to_bits())
}

fn key_str(s: &str) -> PropKey {
    prop_key_from_utf16(utf16_from_str(s))
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 32
    }
}

// ---------------------------------------------------------------------------------------
// 1. Direct Unit & Property-Based Tests of Verified `vjs_object` Modules
// ---------------------------------------------------------------------------------------

#[test]
fn test_ieee754_u32_bits_roundtrip_and_f64_oracle() {
    let edges: [u32; 14] = [
        0,
        1,
        2,
        3,
        7,
        255,
        256,
        65535,
        65536,
        (1u32 << 31) - 1,
        1u32 << 31,
        u32::MAX - 2,
        u32::MAX - 1,
        u32::MAX,
    ];
    for &n in &edges {
        let bits = u32_to_f64_bits(n);
        assert_eq!(bits, (n as f64).to_bits(), "u32_to_f64_bits({n})");
        assert_eq!(f64_bits_to_exact_u32(bits), Some(n));
    }

    let mut rng = Lcg(0x1eee_7540_u64);
    for _ in 0..50_000 {
        let n = rng.next() as u32;
        let bits = u32_to_f64_bits(n);
        assert_eq!(bits, (n as f64).to_bits());
        assert_eq!(f64_bits_to_exact_u32(bits), Some(n));
    }

    // -0.0 decodes to Some(0) per SameValueZero(𝔽(newLen), numberLen)
    assert_eq!(f64_bits_to_exact_u32((-0.0f64).to_bits()), Some(0));
    // Non-integral, negative, overflow, NaN, Infinity -> None
    for bad in [
        -1.0f64,
        -0.5,
        0.5,
        1.5,
        4294967295.5,
        4294967296.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::from_bits(1), // subnormal
    ] {
        assert_eq!(f64_bits_to_exact_u32(bad.to_bits()), None, "bad={bad}");
    }
}

#[test]
fn test_same_value_and_same_value_zero() {
    let p0 = JsVal::NumberBits(POS_ZERO_BITS);
    let n0 = JsVal::NumberBits(NEG_ZERO_BITS);
    let nan1 = JsVal::NumberBits(CANONICAL_NAN_BITS);
    let nan2 = JsVal::NumberBits(0xfff8_0000_0000_0001u64);

    assert!(!same_value(&p0, &n0));
    assert!(same_value_zero(&p0, &n0));
    assert!(same_value(&nan1, &nan2));
    assert!(same_value_zero(&nan1, &nan2));

    // BigInt trailing zero normalization in SameValue
    let bi_zero_a = JsVal::BigInt(JsBigInt {
        neg: false,
        limbs: vec![],
    });
    let bi_zero_b = JsVal::BigInt(JsBigInt {
        neg: true,
        limbs: vec![0, 0],
    });
    assert!(same_value(&bi_zero_a, &bi_zero_b));

    let bi_5_a = JsVal::BigInt(JsBigInt {
        neg: false,
        limbs: vec![5],
    });
    let bi_5_b = JsVal::BigInt(JsBigInt {
        neg: false,
        limbs: vec![5, 0, 0],
    });
    assert!(same_value(&bi_5_a, &bi_5_b));
}

#[test]
fn test_prop_key_canonicalization() {
    assert_eq!(prop_key_from_ascii(b"0"), PropKey::ArrayIndex(0));
    assert_eq!(
        prop_key_from_ascii(b"4294967294"),
        PropKey::ArrayIndex(4_294_967_294)
    );
    // 2^32 - 1 is NOT an array index per ECMA-262 §6.1.7!
    assert!(matches!(prop_key_from_ascii(b"4294967295"), PropKey::Str(_)));
    assert!(matches!(prop_key_from_ascii(b"4294967296"), PropKey::Str(_)));
    assert!(matches!(prop_key_from_ascii(b"00"), PropKey::Str(_)));
    assert!(matches!(prop_key_from_ascii(b"01"), PropKey::Str(_)));
    assert!(matches!(prop_key_from_ascii(b"-0"), PropKey::Str(_)));
    assert!(matches!(prop_key_from_ascii(b""), PropKey::Str(_)));
    assert_eq!(prop_key_from_ascii(b"length"), length_prop_key());
}

#[test]
fn test_descriptors_and_validate_and_apply() {
    // Mixed data + accessor rejected by ToPropertyDescriptor validation
    let mixed = PropertyDescriptor {
        value: Some(js_num(1.0)),
        writable: None,
        get: Some(None),
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert_eq!(validate_descriptor_fields(&mixed), Err(JsError::TypeError));

    // Generic descriptor completes to Data with defaults { undefined, false, false, false }
    let gen = PropertyDescriptor::empty();
    assert!(is_generic_descriptor(&gen));
    assert!(!is_data_descriptor(&gen));
    assert!(!is_accessor_descriptor(&gen));
    let completed = complete_property_descriptor(&gen);
    assert_eq!(
        completed,
        PropertyDescriptor::data(JsVal::Undefined, false, false, false)
    );

    // Non-configurable writable=true Data -> simultaneous { value: 2, writable: false } succeeds (§10.1.6.3 step 5e)
    let cur = Some(CompleteDescriptor::Data {
        value: js_num(1.0),
        writable: true,
        enumerable: true,
        configurable: false,
    });
    let upd = PropertyDescriptor {
        value: Some(js_num(2.0)),
        writable: Some(false),
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    let (ok, after) = validate_and_apply_property_descriptor(true, true, &upd, &cur);
    assert!(ok);
    assert_eq!(
        after,
        Some(CompleteDescriptor::Data {
            value: js_num(2.0),
            writable: false,
            enumerable: true,
            configurable: false,
        })
    );

    // Now writable=false, configurable=false: writable false->true forbidden, Data->Accessor forbidden, -0 vs +0 forbidden
    let flip_w = PropertyDescriptor {
        value: None,
        writable: Some(true),
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert!(!is_compatible_property_descriptor(true, &flip_w, &after));

    let to_acc = PropertyDescriptor {
        value: None,
        writable: None,
        get: Some(None),
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert!(!is_compatible_property_descriptor(true, &to_acc, &after));

    let zero_cur = Some(CompleteDescriptor::Data {
        value: JsVal::NumberBits(POS_ZERO_BITS),
        writable: false,
        enumerable: false,
        configurable: false,
    });
    let neg_zero_upd = PropertyDescriptor {
        value: Some(JsVal::NumberBits(NEG_ZERO_BITS)),
        writable: None,
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert!(!is_compatible_property_descriptor(
        true,
        &neg_zero_upd,
        &zero_cur
    ));

    // Distinct NaN bit patterns succeed via SameValue
    let nan_cur = Some(CompleteDescriptor::Data {
        value: JsVal::NumberBits(CANONICAL_NAN_BITS),
        writable: false,
        enumerable: false,
        configurable: false,
    });
    let nan_upd = PropertyDescriptor {
        value: Some(JsVal::NumberBits(0xfff8_0000_0000_0001u64)),
        writable: None,
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert!(is_compatible_property_descriptor(true, &nan_upd, &nan_cur));
}

#[test]
fn test_prototype_cycles_and_non_extensible_set_proto() {
    let mut heap = Heap::new();
    let a = heap.alloc_ordinary(None);
    let b = heap.alloc_ordinary(Some(a));
    let c = heap.alloc_ordinary(Some(b));
    let d = heap.alloc_ordinary(None);

    // Direct self-cycle a -> a rejected
    assert!(!ordinary_set_prototype_of(&mut heap, a, Some(a)));
    // 2-cycle a -> b -> a rejected
    assert!(!ordinary_set_prototype_of(&mut heap, a, Some(b)));
    // 3-cycle a -> c -> b -> a rejected
    assert!(!ordinary_set_prototype_of(&mut heap, a, Some(c)));
    // Valid re-parenting a -> d (making c -> b -> a -> d -> None!) succeeds and updates proto_ranks!
    assert!(ordinary_set_prototype_of(&mut heap, a, Some(d)));
    assert_eq!(ordinary_get_prototype_of(&heap, a), Some(d));
    // Now d -> c would create 4-cycle d -> c -> b -> a -> d -> rejected!
    assert!(!ordinary_set_prototype_of(&mut heap, d, Some(c)));

    // Non-extensible: SameValue prototype succeeds, any other prototype fails
    ordinary_prevent_extensions(&mut heap, b);
    assert!(!ordinary_is_extensible(&heap, b));
    assert!(ordinary_set_prototype_of(&mut heap, b, Some(a)));
    assert!(!ordinary_set_prototype_of(&mut heap, b, None));
    assert!(!ordinary_set_prototype_of(&mut heap, b, Some(d)));
}

#[test]
fn test_own_property_keys_ordering() {
    let mut heap = Heap::new();
    let o = heap.alloc_ordinary(None);
    let s1 = PropKey::Symbol(100);
    let s2 = PropKey::Symbol(200);

    for k in [
        key_str("b"),
        s1.clone(),
        key_str("4294967295"),
        key_str("10"),
        key_str("4294967294"),
        s2.clone(),
        key_str("a"),
        key_str("2"),
        key_str("01"),
        key_str("0"),
    ] {
        let d = PropertyDescriptor::data(js_num(1.0), true, true, true);
        assert!(ordinary_define_own_property(&mut heap, o, &k, &d));
    }

    // Redefining "b" and s1 in-place must NOT change chronological creation order
    let upd = PropertyDescriptor::data(js_num(99.0), false, true, true);
    assert!(ordinary_define_own_property(&mut heap, o, &key_str("b"), &upd));
    assert!(ordinary_define_own_property(&mut heap, o, &s1, &upd));

    let keys = ordinary_own_property_keys(&heap, o);
    assert_eq!(
        keys,
        vec![
            PropKey::ArrayIndex(0),
            PropKey::ArrayIndex(2),
            PropKey::ArrayIndex(10),
            PropKey::ArrayIndex(4_294_967_294),
            key_str("b"),
            key_str("4294967295"),
            key_str("a"),
            key_str("01"),
            s1.clone(),
            s2.clone(),
        ]
    );

    // Deleting "b" and recreating moves "b" to the end of string keys (still before symbols!)
    assert!(ordinary_delete(&mut heap, o, &key_str("b")));
    assert!(ordinary_define_own_property(
        &mut heap,
        o,
        &key_str("b"),
        &PropertyDescriptor::data(js_num(3.0), true, true, true)
    ));
    let keys2 = ordinary_own_property_keys(&heap, o);
    assert_eq!(
        keys2,
        vec![
            PropKey::ArrayIndex(0),
            PropKey::ArrayIndex(2),
            PropKey::ArrayIndex(10),
            PropKey::ArrayIndex(4_294_967_294),
            key_str("4294967295"),
            key_str("a"),
            key_str("01"),
            key_str("b"),
            s1,
            s2,
        ]
    );
}

#[test]
fn test_ordinary_get_has_set_delete_and_integrity() {
    let mut heap = Heap::new();
    let proto = heap.alloc_ordinary(None);
    let getter_fn = heap.alloc_ordinary(None);
    let setter_fn = heap.alloc_ordinary(None);

    // Define non-writable data `ro` and accessor `acc` on `proto`
    ordinary_define_own_property(
        &mut heap,
        proto,
        &key_str("ro"),
        &PropertyDescriptor::data(js_num(7.0), false, true, false),
    );
    ordinary_define_own_property(
        &mut heap,
        proto,
        &key_str("acc"),
        &PropertyDescriptor::accessor(Some(getter_fn), Some(setter_fn), true, true),
    );

    let child = heap.alloc_ordinary(Some(proto));
    assert!(ordinary_has_property(&heap, child, &key_str("ro")));
    assert!(!ordinary_has_property(&heap, child, &key_str("missing")));
    assert_eq!(
        ordinary_get(&heap, child, &key_str("ro"), &JsVal::Object(child)),
        GetOutcome::Value(js_num(7.0))
    );
    assert_eq!(
        ordinary_get(&heap, child, &key_str("acc"), &JsVal::Object(child)),
        GetOutcome::CallGetter {
            getter: getter_fn,
            receiver: JsVal::Object(child)
        }
    );

    // Inherited non-writable data blocks [[Set]] on extensible child!
    assert_eq!(
        ordinary_set(
            &mut heap,
            child,
            &key_str("ro"),
            &js_num(8.0),
            &JsVal::Object(child)
        ),
        SetOutcome::Result(false)
    );
    assert!(ordinary_get_own_property(&heap, child, &key_str("ro")).is_none());

    // Inherited setter returns CallSetter hook
    assert_eq!(
        ordinary_set(
            &mut heap,
            child,
            &key_str("acc"),
            &js_num(42.0),
            &JsVal::Object(child)
        ),
        SetOutcome::CallSetter {
            setter: setter_fn,
            receiver: JsVal::Object(child),
            value: js_num(42.0)
        }
    );

    // Primitive receiver returns false
    assert_eq!(
        ordinary_set(&mut heap, child, &key_str("x"), &js_num(1.0), &js_num(5.0)),
        SetOutcome::Result(false)
    );

    // Normal [[Set]] creates configurable, enumerable, writable own property on child
    assert_eq!(
        ordinary_set(
            &mut heap,
            child,
            &key_str("x"),
            &js_num(11.0),
            &JsVal::Object(child)
        ),
        SetOutcome::Result(true)
    );
    assert!(!object_is_sealed(&heap, child));
    assert!(!object_is_frozen(&heap, child));

    object_seal(&mut heap, child);
    assert!(object_is_sealed(&heap, child));
    assert!(!object_is_frozen(&heap, child)); // x is still writable!
    assert!(!ordinary_delete(&mut heap, child, &key_str("x")));

    object_freeze(&mut heap, child);
    assert!(object_is_frozen(&heap, child));
    assert!(object_is_sealed(&heap, child));
}

#[test]
fn test_array_exotic_length_and_nonconfigurable_barrier() {
    let mut heap = Heap::new();
    assert_eq!(
        array_create_checked(&mut heap, (u32::MAX as u64) + 1, None),
        Err(JsError::RangeError)
    );
    let arr = array_create(&mut heap, 0, None);
    assert_eq!(array_length(&heap, arr), 0);

    // Auto-extend via element index 4 -> length = 5
    assert_eq!(
        array_define_own_property(
            &mut heap,
            arr,
            &PropKey::ArrayIndex(4),
            &PropertyDescriptor::data(js_str("four"), true, true, true)
        ),
        Ok(true)
    );
    assert_eq!(array_length(&heap, arr), 5);

    // Non-configurable element at index 2
    assert_eq!(
        array_define_own_property(
            &mut heap,
            arr,
            &PropKey::ArrayIndex(2),
            &PropertyDescriptor::data(js_str("pinned"), true, true, false)
        ),
        Ok(true)
    );
    // Sparse element at max array index 4294967294 -> length = 4294967295
    assert_eq!(
        array_define_own_property(
            &mut heap,
            arr,
            &PropKey::ArrayIndex(4_294_967_294),
            &PropertyDescriptor::data(js_str("top"), true, true, true)
        ),
        Ok(true)
    );
    assert_eq!(array_length(&heap, arr), u32::MAX);

    // Shrink length towards 0 with writable: false -> deletes 4294967294 & 4, stops at 2, sets length = 3 and writable = false, returns Ok(false)!
    let shrink_desc = PropertyDescriptor {
        value: Some(js_num(0.0)),
        writable: Some(false),
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert_eq!(array_set_length(&mut heap, arr, &shrink_desc), Ok(false));
    assert_eq!(array_length(&heap, arr), 3);
    assert!(ordinary_get_own_property(&heap, arr, &PropKey::ArrayIndex(4_294_967_294)).is_none());
    assert!(ordinary_get_own_property(&heap, arr, &PropKey::ArrayIndex(4)).is_none());
    assert!(ordinary_get_own_property(&heap, arr, &PropKey::ArrayIndex(2)).is_some());

    // Now length is non-writable: defining element at index 3 fails!
    assert_eq!(
        array_define_own_property(
            &mut heap,
            arr,
            &PropKey::ArrayIndex(3),
            &PropertyDescriptor::data(js_num(9.0), true, true, true)
        ),
        Ok(false)
    );

    // Coercion edge cases
    assert_eq!(
        coerce_array_length_value(&JsVal::NumberBits(NEG_ZERO_BITS)),
        Ok(0)
    );
    assert_eq!(coerce_array_length_value(&js_str("  0x10 ")), Ok(16));
    assert_eq!(coerce_array_length_value(&js_str("-0")), Ok(0));
    assert_eq!(coerce_array_length_value(&js_str("-0.0")), Ok(0));
    assert_eq!(coerce_array_length_value(&js_str("-0e5")), Ok(0));
    assert_eq!(coerce_array_length_value(&js_str("3.0")), Ok(3));
    assert_eq!(coerce_array_length_value(&js_str("3.")), Ok(3));
    assert_eq!(coerce_array_length_value(&js_str(".0")), Ok(0));
    assert_eq!(coerce_array_length_value(&js_str("1e2")), Ok(100));
    assert_eq!(coerce_array_length_value(&js_str("1.5e2")), Ok(150));
    assert_eq!(coerce_array_length_value(&js_str("10e-1")), Ok(1));
    // Deep 200,000-zero scientific cancellation differential check vs live Node/V8
    let deep_pos = format!("0.{}5e200001", "0".repeat(200_000));
    let deep_neg = format!("5{}e-200000", "0".repeat(200_000));
    assert_eq!(coerce_array_length_value(&js_str(&deep_pos)), Ok(5));
    assert_eq!(coerce_array_length_value(&js_str(&deep_neg)), Ok(5));
    let v8_deep = Command::new(NODE_BIN)
        .arg("-e")
        .arg("const a = []; a.length = '0.' + '0'.repeat(200000) + '5e200001'; const b = []; b.length = '5' + '0'.repeat(200000) + 'e-200000'; process.stdout.write(a.length + ':' + b.length);")
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&v8_deep.stdout), "5:5");
    assert_eq!(
        coerce_array_length_value(&js_str("1e-1")),
        Err(JsError::RangeError)
    );
    assert_eq!(
        coerce_array_length_value(&js_str(".")),
        Err(JsError::RangeError)
    );
    assert_eq!(
        coerce_array_length_value(&js_str("+")),
        Err(JsError::RangeError)
    );
    assert_eq!(
        coerce_array_length_value(&js_str("-")),
        Err(JsError::RangeError)
    );
    assert_eq!(
        coerce_array_length_value(&js_str("1.5")),
        Err(JsError::RangeError)
    );
    use vjs_object::string_to_f64::string_to_f64_bits;

    // IEEE-754 binary64 RNE String coercion in ArraySetLength (§10.4.2.4 steps 3-5)
    // Differential check against BOTH live Node.js V8 and native Apple JavaScriptCore (`jsc`)!
    let rne_len_cases: [(&str, Option<u32>); 11] = [
        ("1.00000000000000001", Some(1)),
        ("1e-400", Some(0)),
        ("-1e-400", Some(0)),
        ("4294967294.99999999999999999", Some(4_294_967_295)),
        ("4294967295.0000000000005", Some(4_294_967_295)),
        ("4294967295.0000005", None),
        ("4294967295.5", None),
        ("0x00000000000000000000000001", Some(1)),
        ("0x100000000", None),
        ("0x", None),
        ("Infinity", None),
    ];
    let mut rne_js_check = String::from("const out = [];\n");
    for (s, expected) in &rne_len_cases {
        let mut h = Heap::new();
        let a = array_create(&mut h, 7, None);
        let pd = PropertyDescriptor {
            value: Some(js_str(s)),
            writable: None,
            get: None,
            set: None,
            enumerable: None,
            configurable: None,
        };
        let res = array_set_length(&mut h, a, &pd);
        match expected {
            Some(exp_len) => {
                assert_eq!(coerce_array_length_value(&js_str(s)), Ok(*exp_len), "case {s}");
                assert_eq!(res, Ok(true), "array_set_length {s}");
                assert_eq!(array_length(&h, a), *exp_len, "array_length {s}");
            }
            None => {
                assert_eq!(
                    coerce_array_length_value(&js_str(s)),
                    Err(JsError::RangeError),
                    "case {s}"
                );
                assert_eq!(res, Err(JsError::RangeError), "array_set_length {s}");
            }
        }
        rne_js_check.push_str(&format!(
            "try {{ const a = [1,2,3]; a.length = {}; out.push(String(a.length)); }} catch (e) {{ out.push(e.name); }}\n",
            serde_json::to_string(s).unwrap()
        ));
    }
    let expected_tags: Vec<String> = rne_len_cases
        .iter()
        .map(|(_, e)| match e {
            Some(n) => n.to_string(),
            None => "RangeError".to_string(),
        })
        .collect();
    let v8_rne_out = Command::new(NODE_BIN)
        .arg("-e")
        .arg(format!("{rne_js_check}process.stdout.write(JSON.stringify(out));"))
        .output()
        .unwrap();
    let v8_rne_parsed: Vec<String> = serde_json::from_slice(&v8_rne_out.stdout).unwrap();
    assert_eq!(v8_rne_parsed, expected_tags, "V8 RNE ArraySetLength mismatch");

    let jsc_path = Path::new("/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc");
    if jsc_path.exists() {
        let jsc_rne_out = Command::new(jsc_path)
            .arg("-e")
            .arg(format!("{rne_js_check}print(JSON.stringify(out));"))
            .output()
            .unwrap();
        let jsc_rne_parsed: Vec<String> = serde_json::from_slice(&jsc_rne_out.stdout).unwrap();
        assert_eq!(jsc_rne_parsed, expected_tags, "JSC RNE ArraySetLength mismatch");
    }

    // Bit-exact IEEE-754 RNE differential test of `string_to_f64_bits` vs Node/V8 across boundaries & ties
    let mut rne_bit_cases: Vec<String> = vec![
        "".into(),
        " \t\n\u{feff} ".into(),
        "0".into(),
        "-0".into(),
        "-0.0".into(),
        "-0e5".into(),
        "1.00000000000000001".into(),
        "1.0000000000000001".into(),
        "1.0000000000000002".into(),
        "1e-400".into(),
        "-1e-400".into(),
        "4294967294.99999999999999999".into(),
        "5e-324".into(),
        "2.4703282292062327e-324".into(),
        "2.4703282292062328e-324".into(),
        "7.4109846876186982e-324".into(),
        "2.2250738585072014e-308".into(),
        "2.2250738585072009e-308".into(),
        "1.7976931348623157e308".into(),
        "1.7976931348623159e308".into(),
        "9007199254740993".into(),
        "9007199254740995".into(),
        "Infinity".into(),
        "+Infinity".into(),
        "-Infinity".into(),
        "infinity".into(),
        "0x0".into(),
        "0xffffffff".into(),
        "0x100000000".into(),
        format!("0x{}", "f".repeat(260)),
        "0b10101".into(),
        "0o777".into(),
        "\u{180e}1".into(),
        "1_000".into(),
    ];
    let mut rng_rne = Lcg(0x7540_f640_u64);
    for _ in 0..200 {
        let m = (rng_rne.next() % 1_000_000_000) + 1;
        let e = ((rng_rne.next() % 650) as i32) - 330;
        let sign = if rng_rne.next() % 3 == 0 { "-" } else { "" };
        rne_bit_cases.push(format!("{sign}{m}e{e}"));
    }
    let v8_bits_script = format!(
        "const cases = {}; const out = cases.map(s => {{ const n = Number(s); if (Number.isNaN(n)) return 'NaN'; const b = Buffer.alloc(8); b.writeDoubleBE(n, 0); return b.toString('hex'); }}); process.stdout.write(JSON.stringify(out));",
        serde_json::to_string(&rne_bit_cases).unwrap()
    );
    let v8_bits_out = Command::new(NODE_BIN)
        .arg("-e")
        .arg(&v8_bits_script)
        .output()
        .unwrap();
    let v8_hexes: Vec<String> = serde_json::from_slice(&v8_bits_out.stdout).unwrap();
    for (s, exp_hex) in rne_bit_cases.iter().zip(v8_hexes.iter()) {
        let got = string_to_f64_bits(&utf16_from_str(s));
        if exp_hex == "NaN" {
            assert_eq!(got, CANONICAL_NAN_BITS, "expected NaN on {s:?}");
        } else {
            let exp_bits = u64::from_str_radix(exp_hex, 16).unwrap();
            assert_eq!(got, exp_bits, "bit mismatch on {s:?}: got {got:#018x}, v8 {exp_bits:#018x}");
        }
    }

    assert_eq!(
        coerce_array_length_value(&JsVal::Symbol(1)),
        Err(JsError::TypeError)
    );
}

// ---------------------------------------------------------------------------------------
// 2. Real Pinned `tc39/test262` JS Subset Parser & Evaluator Backed by `vjs_object::Heap`
// ---------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Num(f64),
    Str(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Dot,
    Comma,
    Semi,
    Colon,
    Assign,
    EqEq,
    NotEq,
    EqStrict,
    NotEqStrict,
    AndAnd,
    OrOr,
    Bang,
    Plus,
    Minus,
    Eof,
}

fn lex_js(src: &str) -> Result<Vec<Tok>, String> {
    let bytes = src.as_bytes();
    let n = bytes.len();
    let mut i = 0;
    let mut out = Vec::new();
    while i < n {
        let b = bytes[i];
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if i + 1 < n && b == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < n && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if i + 1 < n && b == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < n && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            i += 2;
            continue;
        }
        if b == b'"' || b == b'\'' {
            let quote = b;
            i += 1;
            let mut s = String::new();
            while i < n && bytes[i] != quote {
                if bytes[i] == b'\\' && i + 1 < n {
                    i += 1;
                    match bytes[i] {
                        b'n' => s.push('\n'),
                        b'r' => s.push('\r'),
                        b't' => s.push('\t'),
                        b'\\' => s.push('\\'),
                        b'"' => s.push('"'),
                        b'\'' => s.push('\''),
                        other => s.push(other as char),
                    }
                } else {
                    let ch = src[i..].chars().next().unwrap();
                    s.push(ch);
                    i += ch.len_utf8() - 1;
                }
                i += 1;
            }
            i += 1;
            out.push(Tok::Str(s));
            continue;
        }
        if b.is_ascii_digit() {
            let start = i;
            if b == b'0' && i + 1 < n && (bytes[i + 1] == b'x' || bytes[i + 1] == b'X') {
                i += 2;
                while i < n && bytes[i].is_ascii_hexdigit() {
                    i += 1;
                }
                let val = u64::from_str_radix(&src[start + 2..i], 16)
                    .map_err(|e| format!("hex parse error: {e}"))?;
                out.push(Tok::Num(val as f64));
                continue;
            }
            while i < n && (bytes[i].is_ascii_digit() || bytes[i] == b'.') {
                i += 1;
            }
            if i < n && (bytes[i] == b'e' || bytes[i] == b'E') {
                i += 1;
                if i < n && (bytes[i] == b'+' || bytes[i] == b'-') {
                    i += 1;
                }
                while i < n && bytes[i].is_ascii_digit() {
                    i += 1;
                }
            }
            let val: f64 = src[start..i]
                .parse()
                .map_err(|e| format!("num parse error: {e}"))?;
            out.push(Tok::Num(val));
            continue;
        }
        if b.is_ascii_alphabetic() || b == b'_' || b == b'$' {
            let start = i;
            while i < n
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$')
            {
                i += 1;
            }
            out.push(Tok::Ident(src[start..i].to_string()));
            continue;
        }
        if i + 2 < n && &src[i..i + 3] == "===" {
            out.push(Tok::EqStrict);
            i += 3;
            continue;
        }
        if i + 2 < n && &src[i..i + 3] == "!==" {
            out.push(Tok::NotEqStrict);
            i += 3;
            continue;
        }
        if i + 1 < n && &src[i..i + 2] == "==" {
            out.push(Tok::EqEq);
            i += 2;
            continue;
        }
        if i + 1 < n && &src[i..i + 2] == "!=" {
            out.push(Tok::NotEq);
            i += 2;
            continue;
        }
        if i + 1 < n && &src[i..i + 2] == "&&" {
            out.push(Tok::AndAnd);
            i += 2;
            continue;
        }
        if i + 1 < n && &src[i..i + 2] == "||" {
            out.push(Tok::OrOr);
            i += 2;
            continue;
        }
        let tok = match b {
            b'(' => Tok::LParen,
            b')' => Tok::RParen,
            b'{' => Tok::LBrace,
            b'}' => Tok::RBrace,
            b'[' => Tok::LBracket,
            b']' => Tok::RBracket,
            b'.' => Tok::Dot,
            b',' => Tok::Comma,
            b';' => Tok::Semi,
            b':' => Tok::Colon,
            b'=' => Tok::Assign,
            b'!' => Tok::Bang,
            b'+' => Tok::Plus,
            b'-' => Tok::Minus,
            _ => return Err(format!("Unsupported token char {:?}", b as char)),
        };
        out.push(tok);
        i += 1;
    }
    out.push(Tok::Eof);
    Ok(out)
}

#[derive(Clone, Debug)]
enum ObjPropInit {
    Value(String, Expr),
    Getter(String, Vec<String>, Vec<Stmt>),
    Setter(String, Vec<String>, Vec<Stmt>),
}

#[derive(Clone, Debug)]
enum Expr {
    Ident(String),
    Num(f64),
    Str(String),
    Bool(bool),
    Null,
    Undefined,
    ObjectLit(Vec<ObjPropInit>),
    ArrayLit(Vec<Option<Expr>>),
    FuncExpr(Option<String>, Vec<String>, Vec<Stmt>),
    Member(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    New(Box<Expr>, Vec<Expr>),
    Unary(String, Box<Expr>),
    Binary(String, Box<Expr>, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
enum Stmt {
    Empty,
    Block(Vec<Stmt>),
    Var(Vec<(String, Option<Expr>)>),
    FuncDecl(String, Vec<String>, Vec<Stmt>),
    Return(Option<Expr>),
    Throw(Expr),
    TryCatch(Vec<Stmt>, String, Vec<Stmt>),
    ExprStmt(Expr),
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
    fn eat_semi(&mut self) {
        if matches!(self.peek(), Tok::Semi) {
            self.next();
        }
    }
    fn expect(&mut self, expected: &Tok) -> Result<(), String> {
        let got = self.next();
        if &got == expected {
            Ok(())
        } else {
            Err(format!("Expected {expected:?}, got {got:?}"))
        }
    }
    fn expect_ident(&mut self) -> Result<String, String> {
        match self.next() {
            Tok::Ident(s) => Ok(s),
            other => Err(format!("Expected identifier, got {other:?}")),
        }
    }
    fn parse_program(&mut self) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        while !matches!(self.peek(), Tok::Eof) {
            stmts.push(self.parse_stmt()?);
        }
        Ok(stmts)
    }
    fn parse_block(&mut self) -> Result<Vec<Stmt>, String> {
        self.expect(&Tok::LBrace)?;
        let mut stmts = Vec::new();
        while !matches!(self.peek(), Tok::RBrace | Tok::Eof) {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(&Tok::RBrace)?;
        Ok(stmts)
    }
    fn parse_params(&mut self) -> Result<Vec<String>, String> {
        self.expect(&Tok::LParen)?;
        let mut params = Vec::new();
        while !matches!(self.peek(), Tok::RParen | Tok::Eof) {
            params.push(self.expect_ident()?);
            if matches!(self.peek(), Tok::Comma) {
                self.next();
            }
        }
        self.expect(&Tok::RParen)?;
        Ok(params)
    }
    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        match self.peek().clone() {
            Tok::Semi => {
                self.next();
                Ok(Stmt::Empty)
            }
            Tok::LBrace => Ok(Stmt::Block(self.parse_block()?)),
            Tok::Ident(k) if k == "var" || k == "let" || k == "const" => {
                self.next();
                let mut decls = Vec::new();
                loop {
                    let name = self.expect_ident()?;
                    let init = if matches!(self.peek(), Tok::Assign) {
                        self.next();
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    decls.push((name, init));
                    if matches!(self.peek(), Tok::Comma) {
                        self.next();
                    } else {
                        break;
                    }
                }
                self.eat_semi();
                Ok(Stmt::Var(decls))
            }
            Tok::Ident(k) if k == "function" => {
                self.next();
                let name = self.expect_ident()?;
                let params = self.parse_params()?;
                let body = self.parse_block()?;
                Ok(Stmt::FuncDecl(name, params, body))
            }
            Tok::Ident(k) if k == "return" => {
                self.next();
                if matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::Eof) {
                    self.eat_semi();
                    Ok(Stmt::Return(None))
                } else {
                    let e = self.parse_expr()?;
                    self.eat_semi();
                    Ok(Stmt::Return(Some(e)))
                }
            }
            Tok::Ident(k) if k == "throw" => {
                self.next();
                let e = self.parse_expr()?;
                self.eat_semi();
                Ok(Stmt::Throw(e))
            }
            Tok::Ident(k) if k == "try" => {
                self.next();
                let try_b = self.parse_block()?;
                let kw = self.expect_ident()?;
                if kw != "catch" {
                    return Err(format!("Expected catch, got {kw}"));
                }
                self.expect(&Tok::LParen)?;
                let err_var = self.expect_ident()?;
                self.expect(&Tok::RParen)?;
                let catch_b = self.parse_block()?;
                Ok(Stmt::TryCatch(try_b, err_var, catch_b))
            }
            _ => {
                let e = self.parse_expr()?;
                self.eat_semi();
                Ok(Stmt::ExprStmt(e))
            }
        }
    }
    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_assign()
    }
    fn parse_assign(&mut self) -> Result<Expr, String> {
        let lhs = self.parse_or()?;
        if matches!(self.peek(), Tok::Assign) {
            self.next();
            let rhs = self.parse_assign()?;
            return Ok(Expr::Assign(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }
    fn parse_or(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_and()?;
        while matches!(self.peek(), Tok::OrOr) {
            self.next();
            let r = self.parse_and()?;
            e = Expr::Binary("||".into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }
    fn parse_and(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_eq()?;
        while matches!(self.peek(), Tok::AndAnd) {
            self.next();
            let r = self.parse_eq()?;
            e = Expr::Binary("&&".into(), Box::new(e), Box::new(r));
        }
        Ok(e)
    }
    fn parse_eq(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_rel()?;
        loop {
            let op = match self.peek() {
                Tok::EqStrict => "===",
                Tok::NotEqStrict => "!==",
                Tok::EqEq => "==",
                Tok::NotEq => "!=",
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
        while let Tok::Ident(k) = self.peek() {
            if k == "instanceof" || k == "in" {
                let op = k.clone();
                self.next();
                let r = self.parse_add()?;
                e = Expr::Binary(op, Box::new(e), Box::new(r));
            } else {
                break;
            }
        }
        Ok(e)
    }
    fn parse_add(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => "+",
                Tok::Minus => "-",
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
            Tok::Bang => {
                self.next();
                Ok(Expr::Unary("!".into(), Box::new(self.parse_unary()?)))
            }
            Tok::Plus => {
                self.next();
                Ok(Expr::Unary("+".into(), Box::new(self.parse_unary()?)))
            }
            Tok::Minus => {
                self.next();
                Ok(Expr::Unary("-".into(), Box::new(self.parse_unary()?)))
            }
            Tok::Ident(k) if k == "typeof" || k == "delete" => {
                self.next();
                Ok(Expr::Unary(k, Box::new(self.parse_unary()?)))
            }
            Tok::Ident(k) if k == "new" => {
                self.next();
                let callee = self.parse_member_base()?;
                let args = if matches!(self.peek(), Tok::LParen) {
                    self.parse_args()?
                } else {
                    Vec::new()
                };
                let mut expr = Expr::New(Box::new(callee), args);
                expr = self.parse_postfix_tail(expr)?;
                Ok(expr)
            }
            _ => self.parse_postfix(),
        }
    }
    fn parse_args(&mut self) -> Result<Vec<Expr>, String> {
        self.expect(&Tok::LParen)?;
        let mut args = Vec::new();
        while !matches!(self.peek(), Tok::RParen | Tok::Eof) {
            args.push(self.parse_expr()?);
            if matches!(self.peek(), Tok::Comma) {
                self.next();
            }
        }
        self.expect(&Tok::RParen)?;
        Ok(args)
    }
    fn parse_member_base(&mut self) -> Result<Expr, String> {
        let mut e = self.parse_primary()?;
        loop {
            match self.peek() {
                Tok::Dot => {
                    self.next();
                    let prop = self.expect_ident()?;
                    e = Expr::Member(Box::new(e), prop);
                }
                Tok::LBracket => {
                    self.next();
                    let idx = self.parse_expr()?;
                    self.expect(&Tok::RBracket)?;
                    e = Expr::Index(Box::new(e), Box::new(idx));
                }
                _ => break,
            }
        }
        Ok(e)
    }
    fn parse_postfix_tail(&mut self, mut e: Expr) -> Result<Expr, String> {
        loop {
            match self.peek() {
                Tok::Dot => {
                    self.next();
                    let prop = self.expect_ident()?;
                    e = Expr::Member(Box::new(e), prop);
                }
                Tok::LBracket => {
                    self.next();
                    let idx = self.parse_expr()?;
                    self.expect(&Tok::RBracket)?;
                    e = Expr::Index(Box::new(e), Box::new(idx));
                }
                Tok::LParen => {
                    let args = self.parse_args()?;
                    e = Expr::Call(Box::new(e), args);
                }
                _ => break,
            }
        }
        Ok(e)
    }
    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let base = self.parse_primary()?;
        self.parse_postfix_tail(base)
    }
    fn parse_prop_name(&mut self) -> Result<String, String> {
        match self.next() {
            Tok::Ident(s) | Tok::Str(s) => Ok(s),
            Tok::Num(n) => Ok(format!("{n}")),
            other => Err(format!("Expected property name, got {other:?}")),
        }
    }
    fn parse_primary(&mut self) -> Result<Expr, String> {
        match self.next() {
            Tok::Num(n) => Ok(Expr::Num(n)),
            Tok::Str(s) => Ok(Expr::Str(s)),
            Tok::Ident(s) => match s.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                "null" => Ok(Expr::Null),
                "undefined" => Ok(Expr::Undefined),
                "NaN" => Ok(Expr::Num(f64::NAN)),
                "Infinity" => Ok(Expr::Num(f64::INFINITY)),
                "function" => {
                    let name = if let Tok::Ident(_) = self.peek() {
                        Some(self.expect_ident()?)
                    } else {
                        None
                    };
                    let params = self.parse_params()?;
                    let body = self.parse_block()?;
                    Ok(Expr::FuncExpr(name, params, body))
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
                while !matches!(self.peek(), Tok::RBracket | Tok::Eof) {
                    if matches!(self.peek(), Tok::Comma) {
                        self.next();
                        items.push(None);
                    } else {
                        items.push(Some(self.parse_expr()?));
                        if matches!(self.peek(), Tok::Comma) {
                            self.next();
                        }
                    }
                }
                self.expect(&Tok::RBracket)?;
                Ok(Expr::ArrayLit(items))
            }
            Tok::LBrace => {
                let mut props = Vec::new();
                while !matches!(self.peek(), Tok::RBrace | Tok::Eof) {
                    if let Tok::Ident(gs) = self.peek().clone() {
                        if (gs == "get" || gs == "set")
                            && !matches!(self.toks.get(self.pos + 1), Some(Tok::Colon | Tok::Comma | Tok::RBrace))
                        {
                            self.next();
                            let pname = self.parse_prop_name()?;
                            let params = self.parse_params()?;
                            let body = self.parse_block()?;
                            if gs == "get" {
                                props.push(ObjPropInit::Getter(pname, params, body));
                            } else {
                                props.push(ObjPropInit::Setter(pname, params, body));
                            }
                            if matches!(self.peek(), Tok::Comma) {
                                self.next();
                            }
                            continue;
                        }
                    }
                    let key = self.parse_prop_name()?;
                    self.expect(&Tok::Colon)?;
                    let val = self.parse_expr()?;
                    props.push(ObjPropInit::Value(key, val));
                    if matches!(self.peek(), Tok::Comma) {
                        self.next();
                    }
                }
                self.expect(&Tok::RBrace)?;
                Ok(Expr::ObjectLit(props))
            }
            other => Err(format!("Unexpected primary token {other:?}")),
        }
    }
}

#[derive(Clone, Debug)]
enum HostFn {
    User {
        params: Vec<String>,
        body: Vec<Stmt>,
    },
    Builtin(&'static str),
}

struct TestRealm {
    heap: Heap,
    object_proto: ObjId,
    function_proto: ObjId,
    array_proto: ObjId,
    bool_proto: ObjId,
    str_proto: ObjId,
    num_proto: ObjId,
    type_error_proto: ObjId,
    range_error_proto: ObjId,
    test262_error_proto: ObjId,
    funcs: HashMap<usize, HostFn>,
    next_sym: u64,
    vars: HashMap<String, JsVal>,
}

#[derive(Debug)]
enum EvalFlow {
    Normal(JsVal),
    Return(JsVal),
    Throw(JsVal),
    HarnessFailure(String),
}

impl TestRealm {
    fn new() -> Self {
        let mut heap = Heap::new();
        let object_proto = heap.alloc_ordinary(None);
        let function_proto = heap.alloc_ordinary(Some(object_proto));
        let array_proto = array_create(&mut heap, 0, Some(object_proto));
        let bool_proto = heap.alloc_ordinary(Some(object_proto));
        let str_proto = heap.alloc_ordinary(Some(object_proto));
        let num_proto = heap.alloc_ordinary(Some(object_proto));
        let error_proto = heap.alloc_ordinary(Some(object_proto));
        let type_error_proto = heap.alloc_ordinary(Some(error_proto));
        let range_error_proto = heap.alloc_ordinary(Some(error_proto));
        let test262_error_proto = heap.alloc_ordinary(Some(error_proto));

        let mut r = TestRealm {
            heap,
            object_proto,
            function_proto,
            array_proto,
            bool_proto,
            str_proto,
            num_proto,
            type_error_proto,
            range_error_proto,
            test262_error_proto,
            funcs: HashMap::new(),
            next_sym: 1,
            vars: HashMap::new(),
        };

        // Wire built-in methods onto Object.prototype
        let has_own_fn = r.alloc_builtin_fn("Object.prototype.hasOwnProperty");
        r.def_method(object_proto, "hasOwnProperty", has_own_fn);
        let is_proto_fn = r.alloc_builtin_fn("Object.prototype.isPrototypeOf");
        r.def_method(object_proto, "isPrototypeOf", is_proto_fn);

        // Function.prototype.call
        let call_fn = r.alloc_builtin_fn("Function.prototype.call");
        r.def_method(function_proto, "call", call_fn);

        // Object constructor & static methods
        let obj_ctor = r.alloc_builtin_fn("Object");
        r.def_const_prop(obj_ctor, "prototype", JsVal::Object(object_proto));
        for (name, tag) in [
            ("defineProperty", "Object.defineProperty"),
            ("getOwnPropertyDescriptor", "Object.getOwnPropertyDescriptor"),
            ("getOwnPropertyNames", "Object.getOwnPropertyNames"),
            ("getOwnPropertySymbols", "Object.getOwnPropertySymbols"),
            ("preventExtensions", "Object.preventExtensions"),
            ("isExtensible", "Object.isExtensible"),
            ("seal", "Object.seal"),
            ("isSealed", "Object.isSealed"),
            ("freeze", "Object.freeze"),
            ("isFrozen", "Object.isFrozen"),
            ("getPrototypeOf", "Object.getPrototypeOf"),
            ("setPrototypeOf", "Object.setPrototypeOf"),
            ("create", "Object.create"),
            ("hasOwn", "Object.hasOwn"),
            ("is", "Object.is"),
        ] {
            let fn_id = r.alloc_builtin_fn(tag);
            r.def_method(obj_ctor, name, fn_id);
        }
        r.vars.insert("Object".into(), JsVal::Object(obj_ctor));

        // Array constructor & Array.isArray
        let arr_ctor = r.alloc_builtin_fn("Array");
        r.def_const_prop(arr_ctor, "prototype", JsVal::Object(array_proto));
        let is_arr_fn = r.alloc_builtin_fn("Array.isArray");
        r.def_method(arr_ctor, "isArray", is_arr_fn);
        r.vars.insert("Array".into(), JsVal::Object(arr_ctor));

        // Wrapper / Symbol / Number / Error constructors
        let sym_ctor = r.alloc_builtin_fn("Symbol");
        r.vars.insert("Symbol".into(), JsVal::Object(sym_ctor));

        let bool_ctor = r.alloc_builtin_fn("Boolean");
        r.def_const_prop(bool_ctor, "prototype", JsVal::Object(bool_proto));
        r.vars.insert("Boolean".into(), JsVal::Object(bool_ctor));

        let str_ctor = r.alloc_builtin_fn("String");
        r.def_const_prop(str_ctor, "prototype", JsVal::Object(str_proto));
        r.vars.insert("String".into(), JsVal::Object(str_ctor));

        let num_ctor = r.alloc_builtin_fn("Number");
        r.def_const_prop(num_ctor, "prototype", JsVal::Object(num_proto));
        r.def_const_prop(num_ctor, "POSITIVE_INFINITY", js_num(f64::INFINITY));
        r.def_const_prop(num_ctor, "NEGATIVE_INFINITY", js_num(f64::NEG_INFINITY));
        r.def_const_prop(num_ctor, "MAX_VALUE", js_num(f64::MAX));
        r.def_const_prop(num_ctor, "MIN_VALUE", js_num(f64::MIN_POSITIVE));
        r.vars.insert("Number".into(), JsVal::Object(num_ctor));

        let te_ctor = r.alloc_builtin_fn("TypeError");
        r.def_const_prop(te_ctor, "prototype", JsVal::Object(type_error_proto));
        r.vars.insert("TypeError".into(), JsVal::Object(te_ctor));

        let re_ctor = r.alloc_builtin_fn("RangeError");
        r.def_const_prop(re_ctor, "prototype", JsVal::Object(range_error_proto));
        r.vars.insert("RangeError".into(), JsVal::Object(re_ctor));

        let t262_ctor = r.alloc_builtin_fn("Test262Error");
        r.def_const_prop(t262_ctor, "prototype", JsVal::Object(test262_error_proto));
        r.vars.insert("Test262Error".into(), JsVal::Object(t262_ctor));

        // test262 harness globals: assert, assert.sameValue, assert.throws, verifyProperty, verifyNotWritable, compareArray
        let assert_fn = r.alloc_builtin_fn("assert");
        let sv_fn = r.alloc_builtin_fn("assert.sameValue");
        r.def_method(assert_fn, "sameValue", sv_fn);
        let th_fn = r.alloc_builtin_fn("assert.throws");
        r.def_method(assert_fn, "throws", th_fn);
        let ca_fn = r.alloc_builtin_fn("compareArray");
        r.def_method(assert_fn, "compareArray", ca_fn);
        r.vars.insert("assert".into(), JsVal::Object(assert_fn));
        r.vars.insert("compareArray".into(), JsVal::Object(ca_fn));

        let vp_fn = r.alloc_builtin_fn("verifyProperty");
        r.vars.insert("verifyProperty".into(), JsVal::Object(vp_fn));
        let vnw_fn = r.alloc_builtin_fn("verifyNotWritable");
        r.vars.insert("verifyNotWritable".into(), JsVal::Object(vnw_fn));

        r
    }

    fn alloc_builtin_fn(&mut self, tag: &'static str) -> ObjId {
        let id = self.heap.alloc_ordinary(Some(self.function_proto));
        self.funcs.insert(id.0, HostFn::Builtin(tag));
        id
    }

    fn alloc_user_fn(&mut self, params: Vec<String>, body: Vec<Stmt>) -> ObjId {
        let id = self.heap.alloc_ordinary(Some(self.function_proto));
        let proto = self.heap.alloc_ordinary(Some(self.object_proto));
        let _ = ordinary_define_own_property(
            &mut self.heap,
            id,
            &key_str("prototype"),
            &PropertyDescriptor::data(JsVal::Object(proto), true, false, false),
        );
        self.funcs.insert(id.0, HostFn::User { params, body });
        id
    }

    fn def_method(&mut self, obj: ObjId, name: &str, fn_id: ObjId) {
        let _ = define_own_property(
            &mut self.heap,
            obj,
            &key_str(name),
            &PropertyDescriptor::data(JsVal::Object(fn_id), true, false, true),
        );
    }

    fn def_const_prop(&mut self, obj: ObjId, name: &str, val: JsVal) {
        let _ = define_own_property(
            &mut self.heap,
            obj,
            &key_str(name),
            &PropertyDescriptor::data(val, false, false, false),
        );
    }

    fn make_error(&mut self, err: JsError) -> JsVal {
        let proto = match err {
            JsError::TypeError => self.type_error_proto,
            JsError::RangeError => self.range_error_proto,
            JsError::Unsupported(_) => self.type_error_proto,
        };
        JsVal::Object(self.heap.alloc_ordinary(Some(proto)))
    }

    fn throw_type_error(&mut self) -> EvalFlow {
        let e = self.make_error(JsError::TypeError);
        EvalFlow::Throw(e)
    }

    fn val_to_prop_key(&self, v: &JsVal) -> PropKey {
        match v {
            JsVal::Symbol(s) => PropKey::Symbol(*s),
            JsVal::Str(u) => prop_key_from_utf16(u.clone()),
            JsVal::Undefined => key_str("undefined"),
            JsVal::Null => key_str("null"),
            JsVal::Bool(b) => key_str(if *b { "true" } else { "false" }),
            JsVal::NumberBits(bits) => {
                let f = f64::from_bits(*bits);
                if f == 0.0 {
                    PropKey::ArrayIndex(0)
                } else if f.is_nan() {
                    key_str("NaN")
                } else if f == f64::INFINITY {
                    key_str("Infinity")
                } else if f == f64::NEG_INFINITY {
                    key_str("-Infinity")
                } else if f.fract() == 0.0 && f >= 0.0 && f <= (u64::MAX as f64) {
                    key_str(&format!("{}", f as u64))
                } else {
                    key_str(&format!("{f}"))
                }
            }
            JsVal::BigInt(_) | JsVal::Object(_) => key_str("[object Object]"),
        }
    }

    fn to_boolean(&self, v: &JsVal) -> bool {
        match v {
            JsVal::Undefined | JsVal::Null => false,
            JsVal::Bool(b) => *b,
            JsVal::NumberBits(bits) => {
                let f = f64::from_bits(*bits);
                f != 0.0 && !f.is_nan()
            }
            JsVal::Str(s) => !s.is_empty(),
            JsVal::BigInt(bi) => bi.limbs.iter().any(|&x| x != 0),
            JsVal::Symbol(_) | JsVal::Object(_) => true,
        }
    }

    fn get_prop(&mut self, obj: ObjId, key: &PropKey, receiver: &JsVal) -> EvalFlow {
        match ordinary_get(&self.heap, obj, key, receiver) {
            GetOutcome::Value(v) => EvalFlow::Normal(v),
            GetOutcome::CallGetter { getter, receiver } => self.call_fn(getter, receiver, &[]),
        }
    }

    fn set_prop(&mut self, obj: ObjId, key: &PropKey, val: &JsVal, receiver: &JsVal) -> EvalFlow {
        match js_set(&mut self.heap, obj, key, val, receiver) {
            Err(e) => EvalFlow::Throw(self.make_error(e)),
            Ok(SetOutcome::Result(_)) => EvalFlow::Normal(val.clone()),
            Ok(SetOutcome::CallSetter {
                setter,
                receiver,
                value,
            }) => {
                let flow = self.call_fn(setter, receiver, &[value]);
                match flow {
                    EvalFlow::Normal(_) => EvalFlow::Normal(val.clone()),
                    other => other,
                }
            }
        }
    }

    fn js_obj_to_descriptor(&mut self, desc_obj: ObjId) -> Result<PropertyDescriptor, EvalFlow> {
        let mut out = PropertyDescriptor::empty();
        if ordinary_has_property(&self.heap, desc_obj, &key_str("enumerable")) {
            let v = match self.get_prop(desc_obj, &key_str("enumerable"), &JsVal::Object(desc_obj))
            {
                EvalFlow::Normal(v) => v,
                other => return Err(other),
            };
            out.enumerable = Some(self.to_boolean(&v));
        }
        if ordinary_has_property(&self.heap, desc_obj, &key_str("configurable")) {
            let v =
                match self.get_prop(desc_obj, &key_str("configurable"), &JsVal::Object(desc_obj)) {
                    EvalFlow::Normal(v) => v,
                    other => return Err(other),
                };
            out.configurable = Some(self.to_boolean(&v));
        }
        if ordinary_has_property(&self.heap, desc_obj, &key_str("value")) {
            let v = match self.get_prop(desc_obj, &key_str("value"), &JsVal::Object(desc_obj)) {
                EvalFlow::Normal(v) => v,
                other => return Err(other),
            };
            out.value = Some(v);
        }
        if ordinary_has_property(&self.heap, desc_obj, &key_str("writable")) {
            let v = match self.get_prop(desc_obj, &key_str("writable"), &JsVal::Object(desc_obj)) {
                EvalFlow::Normal(v) => v,
                other => return Err(other),
            };
            out.writable = Some(self.to_boolean(&v));
        }
        if ordinary_has_property(&self.heap, desc_obj, &key_str("get")) {
            let v = match self.get_prop(desc_obj, &key_str("get"), &JsVal::Object(desc_obj)) {
                EvalFlow::Normal(v) => v,
                other => return Err(other),
            };
            match v {
                JsVal::Undefined => out.get = Some(None),
                JsVal::Object(oid) if self.funcs.contains_key(&oid.0) => out.get = Some(Some(oid)),
                _ => return Err(self.throw_type_error()),
            }
        }
        if ordinary_has_property(&self.heap, desc_obj, &key_str("set")) {
            let v = match self.get_prop(desc_obj, &key_str("set"), &JsVal::Object(desc_obj)) {
                EvalFlow::Normal(v) => v,
                other => return Err(other),
            };
            match v {
                JsVal::Undefined => out.set = Some(None),
                JsVal::Object(oid) if self.funcs.contains_key(&oid.0) => out.set = Some(Some(oid)),
                _ => return Err(self.throw_type_error()),
            }
        }
        if validate_descriptor_fields(&out).is_err() {
            return Err(self.throw_type_error());
        }
        Ok(out)
    }

    fn descriptor_to_js_obj(&mut self, cd: &CompleteDescriptor) -> JsVal {
        let pd = from_complete_descriptor(cd);
        let o = self.heap.alloc_ordinary(Some(self.object_proto));
        if let Some(v) = pd.value {
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("value"),
                &PropertyDescriptor::data(v, true, true, true),
            );
        }
        if let Some(w) = pd.writable {
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("writable"),
                &PropertyDescriptor::data(JsVal::Bool(w), true, true, true),
            );
        }
        if let Some(g) = pd.get {
            let gv = g.map(JsVal::Object).unwrap_or(JsVal::Undefined);
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("get"),
                &PropertyDescriptor::data(gv, true, true, true),
            );
        }
        if let Some(s) = pd.set {
            let sv = s.map(JsVal::Object).unwrap_or(JsVal::Undefined);
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("set"),
                &PropertyDescriptor::data(sv, true, true, true),
            );
        }
        if let Some(e) = pd.enumerable {
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("enumerable"),
                &PropertyDescriptor::data(JsVal::Bool(e), true, true, true),
            );
        }
        if let Some(c) = pd.configurable {
            let _ = ordinary_define_own_property(
                &mut self.heap,
                o,
                &key_str("configurable"),
                &PropertyDescriptor::data(JsVal::Bool(c), true, true, true),
            );
        }
        JsVal::Object(o)
    }

    fn call_fn(&mut self, fn_id: ObjId, this_val: JsVal, args: &[JsVal]) -> EvalFlow {
        let Some(host_fn) = self.funcs.get(&fn_id.0).cloned() else {
            return self.throw_type_error();
        };
        match host_fn {
            HostFn::User { params, body } => {
                let saved = self.vars.clone();
                for (idx, p) in params.iter().enumerate() {
                    let v = args.get(idx).cloned().unwrap_or(JsVal::Undefined);
                    self.vars.insert(p.clone(), v);
                }
                let res = self.exec_stmts(&body);
                for p in &params {
                    if let Some(old) = saved.get(p) {
                        self.vars.insert(p.clone(), old.clone());
                    } else {
                        self.vars.remove(p);
                    }
                }
                match res {
                    EvalFlow::Return(v) => EvalFlow::Normal(v),
                    EvalFlow::Normal(_) => EvalFlow::Normal(JsVal::Undefined),
                    other => other,
                }
            }
            HostFn::Builtin(tag) => self.call_builtin(tag, this_val, args),
        }
    }

    fn call_builtin(&mut self, tag: &str, this_val: JsVal, args: &[JsVal]) -> EvalFlow {
        let a0 = args.first().cloned().unwrap_or(JsVal::Undefined);
        let a1 = args.get(1).cloned().unwrap_or(JsVal::Undefined);
        let a2 = args.get(2).cloned().unwrap_or(JsVal::Undefined);

        match tag {
            "Object" => match a0 {
                JsVal::Undefined | JsVal::Null => {
                    EvalFlow::Normal(JsVal::Object(self.heap.alloc_ordinary(Some(self.object_proto))))
                }
                JsVal::Object(_) => EvalFlow::Normal(a0),
                _ => EvalFlow::Normal(JsVal::Object(self.heap.alloc_ordinary(Some(self.object_proto)))),
            },
            "Symbol" => {
                let s = self.next_sym;
                self.next_sym += 1;
                EvalFlow::Normal(JsVal::Symbol(s))
            }
            "Boolean" => EvalFlow::Normal(JsVal::Bool(self.to_boolean(&a0))),
            "String" => EvalFlow::Normal(js_str("")),
            "Number" => EvalFlow::Normal(js_num(0.0)),
            "TypeError" => EvalFlow::Normal(self.make_error(JsError::TypeError)),
            "RangeError" => EvalFlow::Normal(self.make_error(JsError::RangeError)),
            "Test262Error" => {
                let id = self.heap.alloc_ordinary(Some(self.test262_error_proto));
                EvalFlow::Normal(JsVal::Object(id))
            }
            "Array" => self.construct_array(args),
            "Array.isArray" => {
                let is_arr = match a0 {
                    JsVal::Object(oid) => self.heap.objects[oid.0].kind == ObjectKind::Array,
                    _ => false,
                };
                EvalFlow::Normal(JsVal::Bool(is_arr))
            }
            "Function.prototype.call" => {
                let JsVal::Object(target_fn) = this_val else {
                    return self.throw_type_error();
                };
                let rest = if args.is_empty() { &[] } else { &args[1..] };
                self.call_fn(target_fn, a0, rest)
            }
            "Object.prototype.hasOwnProperty" => {
                let JsVal::Object(oid) = this_val else {
                    return self.throw_type_error();
                };
                let k = self.val_to_prop_key(&a0);
                let has = ordinary_get_own_property(&self.heap, oid, &k).is_some();
                EvalFlow::Normal(JsVal::Bool(has))
            }
            "Object.prototype.isPrototypeOf" => {
                let JsVal::Object(proto_id) = this_val else {
                    return self.throw_type_error();
                };
                let JsVal::Object(mut cur) = a0 else {
                    return EvalFlow::Normal(JsVal::Bool(false));
                };
                while let Some(p) = ordinary_get_prototype_of(&self.heap, cur) {
                    if p == proto_id {
                        return EvalFlow::Normal(JsVal::Bool(true));
                    }
                    cur = p;
                }
                EvalFlow::Normal(JsVal::Bool(false))
            }
            "Object.defineProperty" => {
                let JsVal::Object(oid) = a0 else {
                    return self.throw_type_error();
                };
                let key = self.val_to_prop_key(&a1);
                let JsVal::Object(desc_oid) = a2 else {
                    return self.throw_type_error();
                };
                let desc = match self.js_obj_to_descriptor(desc_oid) {
                    Ok(d) => d,
                    Err(flow) => return flow,
                };
                match define_own_property(&mut self.heap, oid, &key, &desc) {
                    Ok(true) => EvalFlow::Normal(JsVal::Object(oid)),
                    Ok(false) => self.throw_type_error(),
                    Err(e) => EvalFlow::Throw(self.make_error(e)),
                }
            }
            "Object.getOwnPropertyDescriptor" => {
                if matches!(a0, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let JsVal::Object(oid) = a0 else {
                    return EvalFlow::Normal(JsVal::Undefined);
                };
                let key = self.val_to_prop_key(&a1);
                match ordinary_get_own_property(&self.heap, oid, &key) {
                    None => EvalFlow::Normal(JsVal::Undefined),
                    Some(cd) => EvalFlow::Normal(self.descriptor_to_js_obj(&cd)),
                }
            }
            "Object.getOwnPropertyNames" => {
                let JsVal::Object(oid) = a0 else {
                    return self.throw_type_error();
                };
                let keys = ordinary_own_property_keys(&self.heap, oid);
                let mut str_vals = Vec::new();
                for k in keys {
                    match k {
                        PropKey::ArrayIndex(idx) => str_vals.push(js_str(&idx.to_string())),
                        PropKey::Str(u) => str_vals.push(JsVal::Str(u)),
                        PropKey::Symbol(_) => {}
                    }
                }
                let arr = array_create(&mut self.heap, str_vals.len() as u32, Some(self.array_proto));
                for (idx, v) in str_vals.into_iter().enumerate() {
                    let _ = array_define_own_property(
                        &mut self.heap,
                        arr,
                        &PropKey::ArrayIndex(idx as u32),
                        &PropertyDescriptor::data(v, true, true, true),
                    );
                }
                EvalFlow::Normal(JsVal::Object(arr))
            }
            "Object.getOwnPropertySymbols" => {
                let JsVal::Object(oid) = a0 else {
                    return self.throw_type_error();
                };
                let keys = ordinary_own_property_keys(&self.heap, oid);
                let mut sym_vals = Vec::new();
                for k in keys {
                    if let PropKey::Symbol(sym) = k {
                        sym_vals.push(JsVal::Symbol(sym));
                    }
                }
                let arr = array_create(&mut self.heap, sym_vals.len() as u32, Some(self.array_proto));
                for (idx, v) in sym_vals.into_iter().enumerate() {
                    let _ = array_define_own_property(
                        &mut self.heap,
                        arr,
                        &PropKey::ArrayIndex(idx as u32),
                        &PropertyDescriptor::data(v, true, true, true),
                    );
                }
                EvalFlow::Normal(JsVal::Object(arr))
            }
            "Object.preventExtensions" => {
                if let JsVal::Object(oid) = a0 {
                    ordinary_prevent_extensions(&mut self.heap, oid);
                }
                EvalFlow::Normal(a0)
            }
            "Object.isExtensible" => {
                let ext = match a0 {
                    JsVal::Object(oid) => ordinary_is_extensible(&self.heap, oid),
                    _ => false,
                };
                EvalFlow::Normal(JsVal::Bool(ext))
            }
            "Object.seal" => {
                if let JsVal::Object(oid) = a0 {
                    object_seal(&mut self.heap, oid);
                }
                EvalFlow::Normal(a0)
            }
            "Object.isSealed" => {
                let sealed = match a0 {
                    JsVal::Object(oid) => object_is_sealed(&self.heap, oid),
                    _ => true,
                };
                EvalFlow::Normal(JsVal::Bool(sealed))
            }
            "Object.freeze" => {
                if let JsVal::Object(oid) = a0 {
                    object_freeze(&mut self.heap, oid);
                }
                EvalFlow::Normal(a0)
            }
            "Object.isFrozen" => {
                let frozen = match a0 {
                    JsVal::Object(oid) => object_is_frozen(&self.heap, oid),
                    _ => true,
                };
                EvalFlow::Normal(JsVal::Bool(frozen))
            }
            "Object.getPrototypeOf" => {
                if matches!(a0, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let JsVal::Object(oid) = a0 else {
                    return self.throw_type_error();
                };
                let p = ordinary_get_prototype_of(&self.heap, oid)
                    .map(JsVal::Object)
                    .unwrap_or(JsVal::Null);
                EvalFlow::Normal(p)
            }
            "Object.setPrototypeOf" => {
                if matches!(a0, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let proto = match a1 {
                    JsVal::Null => None,
                    JsVal::Object(pid) => Some(pid),
                    _ => return self.throw_type_error(),
                };
                let JsVal::Object(oid) = a0 else {
                    return EvalFlow::Normal(a0);
                };
                if ordinary_set_prototype_of(&mut self.heap, oid, proto) {
                    EvalFlow::Normal(JsVal::Object(oid))
                } else {
                    self.throw_type_error()
                }
            }
            "Object.create" => {
                let proto = match a0 {
                    JsVal::Null => None,
                    JsVal::Object(pid) => Some(pid),
                    _ => return self.throw_type_error(),
                };
                let o = self.heap.alloc_ordinary(proto);
                EvalFlow::Normal(JsVal::Object(o))
            }
            "Object.hasOwn" => {
                if matches!(a0, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let JsVal::Object(oid) = a0 else {
                    return EvalFlow::Normal(JsVal::Bool(false));
                };
                let key = self.val_to_prop_key(&a1);
                let has = ordinary_get_own_property(&self.heap, oid, &key).is_some();
                EvalFlow::Normal(JsVal::Bool(has))
            }
            "Object.is" => EvalFlow::Normal(JsVal::Bool(same_value(&a0, &a1))),
            "assert" => {
                if !self.to_boolean(&a0) {
                    EvalFlow::HarnessFailure(format!("assert failed: {a0:?} ({a1:?})"))
                } else {
                    EvalFlow::Normal(JsVal::Undefined)
                }
            }
            "assert.sameValue" => {
                if !same_value(&a0, &a1) {
                    EvalFlow::HarnessFailure(format!(
                        "assert.sameValue failed: actual={a0:?}, expected={a1:?} ({a2:?})"
                    ))
                } else {
                    EvalFlow::Normal(JsVal::Undefined)
                }
            }
            "assert.throws" => {
                let JsVal::Object(expected_ctor) = a0 else {
                    return EvalFlow::HarnessFailure("assert.throws missing ctor".into());
                };
                let JsVal::Object(cb) = a1 else {
                    return EvalFlow::HarnessFailure("assert.throws missing callback".into());
                };
                match self.call_fn(cb, JsVal::Undefined, &[]) {
                    EvalFlow::Throw(err_val) => {
                        if self.is_instance_of(&err_val, expected_ctor) {
                            EvalFlow::Normal(JsVal::Undefined)
                        } else {
                            EvalFlow::HarnessFailure(format!(
                                "assert.throws caught wrong error: {err_val:?}"
                            ))
                        }
                    }
                    EvalFlow::Normal(v) => EvalFlow::HarnessFailure(format!(
                        "assert.throws expected exception, got Normal({v:?})"
                    )),
                    other => other,
                }
            }
            "compareArray" => {
                let (JsVal::Object(arr1), JsVal::Object(arr2)) = (a0, a1) else {
                    return EvalFlow::HarnessFailure("compareArray non-object".into());
                };
                let l1 = array_length(&self.heap, arr1);
                let l2 = array_length(&self.heap, arr2);
                if l1 != l2 {
                    return EvalFlow::HarnessFailure(format!("compareArray len {l1} != {l2}"));
                }
                for i in 0..l1 {
                    let k = PropKey::ArrayIndex(i);
                    let v1 = match self.get_prop(arr1, &k, &JsVal::Object(arr1)) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let v2 = match self.get_prop(arr2, &k, &JsVal::Object(arr2)) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    if !same_value(&v1, &v2) {
                        return EvalFlow::HarnessFailure(format!(
                            "compareArray[{i}]: {v1:?} != {v2:?}"
                        ));
                    }
                }
                EvalFlow::Normal(JsVal::Bool(true))
            }
            "verifyProperty" => {
                let JsVal::Object(oid) = a0 else {
                    return EvalFlow::HarnessFailure("verifyProperty non-object".into());
                };
                let key = self.val_to_prop_key(&a1);
                let JsVal::Object(exp_oid) = a2 else {
                    return EvalFlow::HarnessFailure("verifyProperty non-object spec".into());
                };
                let Some(actual) = ordinary_get_own_property(&self.heap, oid, &key) else {
                    return EvalFlow::HarnessFailure(format!(
                        "verifyProperty missing own property {key:?}"
                    ));
                };
                let pd = from_complete_descriptor(&actual);
                if ordinary_has_property(&self.heap, exp_oid, &key_str("value")) {
                    let ev = match self.get_prop(exp_oid, &key_str("value"), &JsVal::Object(exp_oid))
                    {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let av = match &actual {
                        CompleteDescriptor::Data { value, .. } => value.clone(),
                        CompleteDescriptor::Accessor { .. } => {
                            match self.get_prop(oid, &key, &JsVal::Object(oid)) {
                                EvalFlow::Normal(v) => v,
                                other => return other,
                            }
                        }
                    };
                    if !same_value(&av, &ev) {
                        return EvalFlow::HarnessFailure(format!(
                            "verifyProperty value mismatch: actual={av:?}, expected={ev:?}"
                        ));
                    }
                }
                for (attr, actual_opt) in [
                    ("writable", pd.writable),
                    ("enumerable", pd.enumerable),
                    ("configurable", pd.configurable),
                ] {
                    if ordinary_has_property(&self.heap, exp_oid, &key_str(attr)) {
                        let ev =
                            match self.get_prop(exp_oid, &key_str(attr), &JsVal::Object(exp_oid)) {
                                EvalFlow::Normal(v) => self.to_boolean(&v),
                                other => return other,
                            };
                        if actual_opt != Some(ev) {
                            return EvalFlow::HarnessFailure(format!(
                                "verifyProperty {attr} mismatch: actual={actual_opt:?}, expected={ev}"
                            ));
                        }
                    }
                }
                EvalFlow::Normal(JsVal::Bool(true))
            }
            "verifyNotWritable" => {
                let JsVal::Object(oid) = a0 else {
                    return EvalFlow::HarnessFailure("verifyNotWritable non-object".into());
                };
                let key = self.val_to_prop_key(&a1);
                let before = match self.get_prop(oid, &key, &JsVal::Object(oid)) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                let _ = self.set_prop(oid, &key, &js_str("unlikelyValue"), &JsVal::Object(oid));
                let after = match self.get_prop(oid, &key, &JsVal::Object(oid)) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                if !same_value(&before, &after) {
                    EvalFlow::HarnessFailure("verifyNotWritable mutated property!".into())
                } else {
                    EvalFlow::Normal(JsVal::Undefined)
                }
            }
            other => EvalFlow::HarnessFailure(format!("Unhandled builtin {other}")),
        }
    }

    fn construct_array(&mut self, args: &[JsVal]) -> EvalFlow {
        if args.len() == 1 {
            if let JsVal::NumberBits(bits) = args[0] {
                match f64_bits_to_exact_u32(bits) {
                    Some(len) => {
                        let a = array_create(&mut self.heap, len, Some(self.array_proto));
                        return EvalFlow::Normal(JsVal::Object(a));
                    }
                    None => {
                        let e = self.make_error(JsError::RangeError);
                        return EvalFlow::Throw(e);
                    }
                }
            }
        }
        let a = array_create(&mut self.heap, args.len() as u32, Some(self.array_proto));
        for (idx, v) in args.iter().enumerate() {
            let _ = array_define_own_property(
                &mut self.heap,
                a,
                &PropKey::ArrayIndex(idx as u32),
                &PropertyDescriptor::data(v.clone(), true, true, true),
            );
        }
        EvalFlow::Normal(JsVal::Object(a))
    }

    fn is_instance_of(&self, val: &JsVal, ctor: ObjId) -> bool {
        let JsVal::Object(mut cur) = *val else {
            return false;
        };
        let Some(CompleteDescriptor::Data {
            value: JsVal::Object(target_proto),
            ..
        }) = ordinary_get_own_property(&self.heap, ctor, &key_str("prototype"))
        else {
            return false;
        };
        while let Some(p) = ordinary_get_prototype_of(&self.heap, cur) {
            if p == target_proto {
                return true;
            }
            cur = p;
        }
        false
    }

    fn exec_stmts(&mut self, stmts: &[Stmt]) -> EvalFlow {
        // Hoist function declarations first per ES function hoisting
        for s in stmts {
            if let Stmt::FuncDecl(name, params, body) = s {
                let fn_id = self.alloc_user_fn(params.clone(), body.clone());
                self.vars.insert(name.clone(), JsVal::Object(fn_id));
            }
        }
        let mut last = JsVal::Undefined;
        for s in stmts {
            match s {
                Stmt::Empty | Stmt::FuncDecl(_, _, _) => {}
                Stmt::Block(inner) => match self.exec_stmts(inner) {
                    EvalFlow::Normal(v) => last = v,
                    other => return other,
                },
                Stmt::Var(decls) => {
                    for (name, init) in decls {
                        if let Some(expr) = init {
                            match self.eval_expr(expr) {
                                EvalFlow::Normal(v) => {
                                    self.vars.insert(name.clone(), v);
                                }
                                other => return other,
                            }
                        } else if !self.vars.contains_key(name) {
                            self.vars.insert(name.clone(), JsVal::Undefined);
                        }
                    }
                }
                Stmt::Return(opt) => {
                    let v = match opt {
                        None => JsVal::Undefined,
                        Some(e) => match self.eval_expr(e) {
                            EvalFlow::Normal(v) => v,
                            other => return other,
                        },
                    };
                    return EvalFlow::Return(v);
                }
                Stmt::Throw(e) => match self.eval_expr(e) {
                    EvalFlow::Normal(v) => return EvalFlow::Throw(v),
                    other => return other,
                },
                Stmt::TryCatch(try_b, err_var, catch_b) => match self.exec_stmts(try_b) {
                    EvalFlow::Throw(err_val) => {
                        self.vars.insert(err_var.clone(), err_val);
                        match self.exec_stmts(catch_b) {
                            EvalFlow::Normal(v) => last = v,
                            other => return other,
                        }
                    }
                    EvalFlow::Normal(v) => last = v,
                    other => return other,
                },
                Stmt::ExprStmt(e) => match self.eval_expr(e) {
                    EvalFlow::Normal(v) => last = v,
                    other => return other,
                },
            }
        }
        EvalFlow::Normal(last)
    }

    fn eval_expr(&mut self, expr: &Expr) -> EvalFlow {
        match expr {
            Expr::Num(n) => EvalFlow::Normal(js_num(*n)),
            Expr::Str(s) => EvalFlow::Normal(js_str(s)),
            Expr::Bool(b) => EvalFlow::Normal(JsVal::Bool(*b)),
            Expr::Null => EvalFlow::Normal(JsVal::Null),
            Expr::Undefined => EvalFlow::Normal(JsVal::Undefined),
            Expr::Ident(name) => {
                let v = self.vars.get(name).cloned().unwrap_or(JsVal::Undefined);
                EvalFlow::Normal(v)
            }
            Expr::FuncExpr(opt_name, params, body) => {
                let fn_id = self.alloc_user_fn(params.clone(), body.clone());
                if let Some(n) = opt_name {
                    self.vars.insert(n.clone(), JsVal::Object(fn_id));
                }
                EvalFlow::Normal(JsVal::Object(fn_id))
            }
            Expr::ArrayLit(items) => {
                let a = array_create(&mut self.heap, items.len() as u32, Some(self.array_proto));
                for (idx, item) in items.iter().enumerate() {
                    if let Some(sub) = item {
                        let v = match self.eval_expr(sub) {
                            EvalFlow::Normal(v) => v,
                            other => return other,
                        };
                        let _ = array_define_own_property(
                            &mut self.heap,
                            a,
                            &PropKey::ArrayIndex(idx as u32),
                            &PropertyDescriptor::data(v, true, true, true),
                        );
                    }
                }
                EvalFlow::Normal(JsVal::Object(a))
            }
            Expr::ObjectLit(props) => {
                let o = self.heap.alloc_ordinary(Some(self.object_proto));
                for init in props {
                    match init {
                        ObjPropInit::Value(k, e) => {
                            let v = match self.eval_expr(e) {
                                EvalFlow::Normal(v) => v,
                                other => return other,
                            };
                            let pk = key_str(k);
                            let _ = define_own_property(
                                &mut self.heap,
                                o,
                                &pk,
                                &PropertyDescriptor::data(v, true, true, true),
                            );
                        }
                        ObjPropInit::Getter(k, params, body) => {
                            let gid = self.alloc_user_fn(params.clone(), body.clone());
                            let pk = key_str(k);
                            let mut pd = PropertyDescriptor::empty();
                            pd.get = Some(Some(gid));
                            pd.enumerable = Some(true);
                            pd.configurable = Some(true);
                            let _ = define_own_property(&mut self.heap, o, &pk, &pd);
                        }
                        ObjPropInit::Setter(k, params, body) => {
                            let sid = self.alloc_user_fn(params.clone(), body.clone());
                            let pk = key_str(k);
                            let mut pd = PropertyDescriptor::empty();
                            pd.set = Some(Some(sid));
                            pd.enumerable = Some(true);
                            pd.configurable = Some(true);
                            let _ = define_own_property(&mut self.heap, o, &pk, &pd);
                        }
                    }
                }
                EvalFlow::Normal(JsVal::Object(o))
            }
            Expr::Member(base, prop) => {
                let bv = match self.eval_expr(base) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                if matches!(bv, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let JsVal::Object(oid) = bv else {
                    return EvalFlow::Normal(JsVal::Undefined);
                };
                self.get_prop(oid, &key_str(prop), &bv)
            }
            Expr::Index(base, idx_e) => {
                let bv = match self.eval_expr(base) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                let iv = match self.eval_expr(idx_e) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                if matches!(bv, JsVal::Undefined | JsVal::Null) {
                    return self.throw_type_error();
                }
                let JsVal::Object(oid) = bv else {
                    return EvalFlow::Normal(JsVal::Undefined);
                };
                let k = self.val_to_prop_key(&iv);
                self.get_prop(oid, &k, &bv)
            }
            Expr::Assign(lhs, rhs) => match &**lhs {
                Expr::Ident(name) => {
                    let rv = match self.eval_expr(rhs) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    self.vars.insert(name.clone(), rv.clone());
                    EvalFlow::Normal(rv)
                }
                Expr::Member(base, prop) => {
                    let bv = match self.eval_expr(base) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let rv = match self.eval_expr(rhs) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let JsVal::Object(oid) = bv else {
                        return self.throw_type_error();
                    };
                    self.set_prop(oid, &key_str(prop), &rv, &bv)
                }
                Expr::Index(base, idx_e) => {
                    let bv = match self.eval_expr(base) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let iv = match self.eval_expr(idx_e) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let rv = match self.eval_expr(rhs) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    let JsVal::Object(oid) = bv else {
                        return self.throw_type_error();
                    };
                    let k = self.val_to_prop_key(&iv);
                    self.set_prop(oid, &k, &rv, &bv)
                }
                other => EvalFlow::HarnessFailure(format!("Invalid assignment LHS {other:?}")),
            },
            Expr::Call(callee, arg_exprs) => {
                let (this_val, fn_val) = match &**callee {
                    Expr::Member(base, prop) => {
                        let bv = match self.eval_expr(base) {
                            EvalFlow::Normal(v) => v,
                            other => return other,
                        };
                        let JsVal::Object(oid) = bv else {
                            return self.throw_type_error();
                        };
                        let fv = match self.get_prop(oid, &key_str(prop), &bv) {
                            EvalFlow::Normal(v) => v,
                            other => return other,
                        };
                        (bv, fv)
                    }
                    _ => {
                        let fv = match self.eval_expr(callee) {
                            EvalFlow::Normal(v) => v,
                            other => return other,
                        };
                        (JsVal::Undefined, fv)
                    }
                };
                let mut args = Vec::new();
                for ae in arg_exprs {
                    match self.eval_expr(ae) {
                        EvalFlow::Normal(v) => args.push(v),
                        other => return other,
                    }
                }
                let JsVal::Object(fn_id) = fn_val else {
                    return self.throw_type_error();
                };
                self.call_fn(fn_id, this_val, &args)
            }
            Expr::New(callee, arg_exprs) => {
                let fv = match self.eval_expr(callee) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                let mut args = Vec::new();
                for ae in arg_exprs {
                    match self.eval_expr(ae) {
                        EvalFlow::Normal(v) => args.push(v),
                        other => return other,
                    }
                }
                let JsVal::Object(fn_id) = fv else {
                    return self.throw_type_error();
                };
                match self.funcs.get(&fn_id.0).cloned() {
                    Some(HostFn::Builtin("Array")) => self.construct_array(&args),
                    Some(HostFn::Builtin("Object")) => EvalFlow::Normal(JsVal::Object(
                        self.heap.alloc_ordinary(Some(self.object_proto)),
                    )),
                    Some(HostFn::Builtin("Boolean")) => EvalFlow::Normal(JsVal::Object(
                        self.heap.alloc_ordinary(Some(self.bool_proto)),
                    )),
                    Some(HostFn::Builtin("String")) => EvalFlow::Normal(JsVal::Object(
                        self.heap.alloc_ordinary(Some(self.str_proto)),
                    )),
                    Some(HostFn::Builtin("Number")) => EvalFlow::Normal(JsVal::Object(
                        self.heap.alloc_ordinary(Some(self.num_proto)),
                    )),
                    Some(HostFn::Builtin("TypeError")) => {
                        EvalFlow::Normal(self.make_error(JsError::TypeError))
                    }
                    Some(HostFn::Builtin("RangeError")) => {
                        EvalFlow::Normal(self.make_error(JsError::RangeError))
                    }
                    Some(HostFn::Builtin("Test262Error")) => EvalFlow::Normal(JsVal::Object(
                        self.heap.alloc_ordinary(Some(self.test262_error_proto)),
                    )),
                    Some(HostFn::User { .. }) => {
                        let proto = match ordinary_get_own_property(
                            &self.heap,
                            fn_id,
                            &key_str("prototype"),
                        ) {
                            Some(CompleteDescriptor::Data {
                                value: JsVal::Object(pid),
                                ..
                            }) => Some(pid),
                            _ => Some(self.object_proto),
                        };
                        let inst = self.heap.alloc_ordinary(proto);
                        match self.call_fn(fn_id, JsVal::Object(inst), &args) {
                            EvalFlow::Normal(JsVal::Object(ret_obj)) => {
                                EvalFlow::Normal(JsVal::Object(ret_obj))
                            }
                            EvalFlow::Normal(_) => EvalFlow::Normal(JsVal::Object(inst)),
                            other => other,
                        }
                    }
                    _ => self.throw_type_error(),
                }
            }
            Expr::Unary(op, sub) => {
                if op == "delete" {
                    return match &**sub {
                        Expr::Member(base, prop) => {
                            let bv = match self.eval_expr(base) {
                                EvalFlow::Normal(v) => v,
                                other => return other,
                            };
                            let JsVal::Object(oid) = bv else {
                                return EvalFlow::Normal(JsVal::Bool(true));
                            };
                            let ok = ordinary_delete(&mut self.heap, oid, &key_str(prop));
                            EvalFlow::Normal(JsVal::Bool(ok))
                        }
                        Expr::Index(base, idx_e) => {
                            let bv = match self.eval_expr(base) {
                                EvalFlow::Normal(v) => v,
                                other => return other,
                            };
                            let iv = match self.eval_expr(idx_e) {
                                EvalFlow::Normal(v) => v,
                                other => return other,
                            };
                            let JsVal::Object(oid) = bv else {
                                return EvalFlow::Normal(JsVal::Bool(true));
                            };
                            let k = self.val_to_prop_key(&iv);
                            let ok = ordinary_delete(&mut self.heap, oid, &k);
                            EvalFlow::Normal(JsVal::Bool(ok))
                        }
                        _ => EvalFlow::Normal(JsVal::Bool(true)),
                    };
                }
                let v = match self.eval_expr(sub) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                match op.as_str() {
                    "!" => EvalFlow::Normal(JsVal::Bool(!self.to_boolean(&v))),
                    "+" => match v {
                        JsVal::NumberBits(b) => EvalFlow::Normal(JsVal::NumberBits(b)),
                        _ => EvalFlow::Normal(js_num(f64::NAN)),
                    },
                    "-" => match v {
                        JsVal::NumberBits(b) => {
                            EvalFlow::Normal(js_num(-f64::from_bits(b)))
                        }
                        _ => EvalFlow::Normal(js_num(f64::NAN)),
                    },
                    "typeof" => {
                        let ts = match v {
                            JsVal::Undefined => "undefined",
                            JsVal::Null => "object",
                            JsVal::Bool(_) => "boolean",
                            JsVal::NumberBits(_) => "number",
                            JsVal::BigInt(_) => "bigint",
                            JsVal::Str(_) => "string",
                            JsVal::Symbol(_) => "symbol",
                            JsVal::Object(oid) => {
                                if self.funcs.contains_key(&oid.0) {
                                    "function"
                                } else {
                                    "object"
                                }
                            }
                        };
                        EvalFlow::Normal(js_str(ts))
                    }
                    _ => EvalFlow::HarnessFailure(format!("Unknown unary {op}")),
                }
            }
            Expr::Binary(op, l, r) => {
                if op == "&&" {
                    let lv = match self.eval_expr(l) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    if !self.to_boolean(&lv) {
                        return EvalFlow::Normal(lv);
                    }
                    return self.eval_expr(r);
                }
                if op == "||" {
                    let lv = match self.eval_expr(l) {
                        EvalFlow::Normal(v) => v,
                        other => return other,
                    };
                    if self.to_boolean(&lv) {
                        return EvalFlow::Normal(lv);
                    }
                    return self.eval_expr(r);
                }
                let lv = match self.eval_expr(l) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                let rv = match self.eval_expr(r) {
                    EvalFlow::Normal(v) => v,
                    other => return other,
                };
                match op.as_str() {
                    "===" | "==" => {
                        let eq = match (&lv, &rv) {
                            (JsVal::NumberBits(a), JsVal::NumberBits(b)) => {
                                f64::from_bits(*a) == f64::from_bits(*b)
                            }
                            (JsVal::Null, JsVal::Undefined) | (JsVal::Undefined, JsVal::Null)
                                if op == "==" =>
                            {
                                true
                            }
                            _ => same_value(&lv, &rv),
                        };
                        EvalFlow::Normal(JsVal::Bool(eq))
                    }
                    "!==" | "!=" => {
                        let eq = match (&lv, &rv) {
                            (JsVal::NumberBits(a), JsVal::NumberBits(b)) => {
                                f64::from_bits(*a) == f64::from_bits(*b)
                            }
                            (JsVal::Null, JsVal::Undefined) | (JsVal::Undefined, JsVal::Null)
                                if op == "!=" =>
                            {
                                true
                            }
                            _ => same_value(&lv, &rv),
                        };
                        EvalFlow::Normal(JsVal::Bool(!eq))
                    }
                    "instanceof" => {
                        let JsVal::Object(ctor_id) = rv else {
                            return self.throw_type_error();
                        };
                        EvalFlow::Normal(JsVal::Bool(self.is_instance_of(&lv, ctor_id)))
                    }
                    "in" => {
                        let JsVal::Object(oid) = rv else {
                            return self.throw_type_error();
                        };
                        let k = self.val_to_prop_key(&lv);
                        EvalFlow::Normal(JsVal::Bool(ordinary_has_property(&self.heap, oid, &k)))
                    }
                    "+" => match (&lv, &rv) {
                        (JsVal::NumberBits(a), JsVal::NumberBits(b)) => {
                            EvalFlow::Normal(js_num(f64::from_bits(*a) + f64::from_bits(*b)))
                        }
                        (JsVal::Str(a), JsVal::Str(b)) => {
                            let mut c = a.clone();
                            c.extend_from_slice(b);
                            EvalFlow::Normal(JsVal::Str(c))
                        }
                        _ => EvalFlow::Normal(js_str("")),
                    },
                    "-" => match (&lv, &rv) {
                        (JsVal::NumberBits(a), JsVal::NumberBits(b)) => {
                            EvalFlow::Normal(js_num(f64::from_bits(*a) - f64::from_bits(*b)))
                        }
                        _ => EvalFlow::Normal(js_num(f64::NAN)),
                    },
                    _ => EvalFlow::HarnessFailure(format!("Unknown binary {op}")),
                }
            }
        }
    }
}

fn run_test262_file_on_vjs_object(path: &Path) -> Result<(), String> {
    let src = fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let toks = lex_js(&src)?;
    let mut parser = Parser { toks, pos: 0 };
    let stmts = parser.parse_program()?;
    let mut realm = TestRealm::new();
    match realm.exec_stmts(&stmts) {
        EvalFlow::Normal(_) => Ok(()),
        EvalFlow::Return(_) => Ok(()),
        EvalFlow::Throw(v) => Err(format!("Uncaught JS exception {v:?}")),
        EvalFlow::HarnessFailure(msg) => Err(msg),
    }
}

fn collect_js_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        let mut sorted: Vec<_> = entries.filter_map(|e| e.ok()).collect();
        sorted.sort_by_key(|e| e.path());
        for entry in sorted {
            let p = entry.path();
            if p.is_dir() {
                collect_js_files(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("js") {
                out.push(p);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------
// 3. Live Differential Fuzzing Oracle vs Node.js V8 (600 Multi-Step Object/Array Traces)
// ---------------------------------------------------------------------------------------

fn serialize_js_val_expr(v: &JsVal) -> String {
    match v {
        JsVal::Undefined => "undefined".into(),
        JsVal::Null => "null".into(),
        JsVal::Bool(b) => b.to_string(),
        JsVal::NumberBits(bits) => {
            if *bits == NEG_ZERO_BITS {
                "-0".into()
            } else if *bits == POS_ZERO_BITS {
                "0".into()
            } else {
                let f = f64::from_bits(*bits);
                if f.is_nan() {
                    "NaN".into()
                } else if f == f64::INFINITY {
                    "Infinity".into()
                } else if f == f64::NEG_INFINITY {
                    "-Infinity".into()
                } else {
                    format!("{f}")
                }
            }
        }
        JsVal::Str(u) => serde_json::to_string(&utf16_to_string(u)).unwrap(),
        JsVal::Symbol(id) => format!("SYMS[{id}]"),
        JsVal::Object(oid) => format!("OBJS[{}]", oid.0),
        JsVal::BigInt(_) => "0n".into(),
    }
}

fn serialize_prop_key_expr(k: &PropKey) -> String {
    match k {
        PropKey::ArrayIndex(idx) => serde_json::to_string(&idx.to_string()).unwrap(),
        PropKey::Str(u) => serde_json::to_string(&utf16_to_string(u)).unwrap(),
        PropKey::Symbol(id) => format!("SYMS[{id}]"),
    }
}

fn format_key_tag(k: &PropKey) -> String {
    match k {
        PropKey::ArrayIndex(idx) => format!("S:{idx}"),
        PropKey::Str(u) => format!("S:{}", utf16_to_string(u)),
        PropKey::Symbol(id) => format!("Y:{id}"),
    }
}

fn format_val_tag(v: &JsVal) -> String {
    match v {
        JsVal::Undefined => "U".into(),
        JsVal::Null => "N".into(),
        JsVal::Bool(b) => format!("B:{b}"),
        JsVal::NumberBits(bits) => {
            if *bits == NEG_ZERO_BITS {
                "F:-0".into()
            } else if *bits == POS_ZERO_BITS {
                "F:+0".into()
            } else {
                let f = f64::from_bits(*bits);
                if f.is_nan() {
                    "F:NaN".into()
                } else {
                    format!("F:{f}")
                }
            }
        }
        JsVal::Str(u) => format!("S:{}", utf16_to_string(u)),
        JsVal::Symbol(id) => format!("Y:{id}"),
        JsVal::Object(oid) => format!("O:{}", oid.0),
        JsVal::BigInt(_) => "I".into(),
    }
}

fn snapshot_heap(heap: &Heap, tracked: &[ObjId]) -> JsonValue {
    let mut objs = Vec::new();
    for &oid in tracked {
        let proto = ordinary_get_prototype_of(heap, oid)
            .map(|p| json!(p.0))
            .unwrap_or(JsonValue::Null);
        let ext = ordinary_is_extensible(heap, oid);
        let sealed = object_is_sealed(heap, oid);
        let frozen = object_is_frozen(heap, oid);
        let own_keys = ordinary_own_property_keys(heap, oid);
        let key_tags: Vec<String> = own_keys.iter().map(format_key_tag).collect();
        let mut descs = Vec::new();
        for k in &own_keys {
            let cd = ordinary_get_own_property(heap, oid, k).unwrap();
            let dj = match cd {
                CompleteDescriptor::Data {
                    value,
                    writable,
                    enumerable,
                    configurable,
                } => json!({
                    "k": format_key_tag(k),
                    "kind": "data",
                    "v": format_val_tag(&value),
                    "w": writable,
                    "e": enumerable,
                    "c": configurable,
                }),
                CompleteDescriptor::Accessor {
                    get,
                    set,
                    enumerable,
                    configurable,
                } => json!({
                    "k": format_key_tag(k),
                    "kind": "acc",
                    "g": get.map(|x| x.0 as i64).unwrap_or(-1),
                    "s": set.map(|x| x.0 as i64).unwrap_or(-1),
                    "e": enumerable,
                    "c": configurable,
                }),
            };
            descs.push(dj);
        }
        objs.push(json!({
            "id": oid.0,
            "proto": proto,
            "ext": ext,
            "sealed": sealed,
            "frozen": frozen,
            "keys": key_tags,
            "descs": descs,
        }));
    }
    json!(objs)
}

fn run_differential_v8_traces(num_traces: usize) -> (usize, usize, usize, bool) {
    let mut rng = Lcg(0xd1ff_2620_0b1ec7u64);
    let mut js_batch = String::from(
        r#"
const SYMS = { 1: Symbol("s1"), 2: Symbol("s2"), 3: Symbol("s3") };
function valTag(v, objIdxMap, symRevMap) {
  if (v === undefined) return "U";
  if (v === null) return "N";
  if (typeof v === "boolean") return "B:" + v;
  if (typeof v === "number") {
    if (Number.isNaN(v)) return "F:NaN";
    if (Object.is(v, -0)) return "F:-0";
    if (Object.is(v, +0)) return "F:+0";
    return "F:" + v;
  }
  if (typeof v === "string") return "S:" + v;
  if (typeof v === "symbol") return "Y:" + symRevMap.get(v);
  if (typeof v === "object" || typeof v === "function") return "O:" + objIdxMap.get(v);
  return "?";
}
function keyTag(k, symRevMap) {
  if (typeof k === "symbol") return "Y:" + symRevMap.get(k);
  return "S:" + k;
}
function specIsFrozen(o) {
  if (Object.isExtensible(o)) return false;
  for (const k of Reflect.ownKeys(o)) {
    const d = Object.getOwnPropertyDescriptor(o, k);
    if (d.configurable) return false;
    if ("writable" in d && d.writable) return false;
  }
  return true;
}
function snap(OBJS, trackedIds, v8BugCounter) {
  const objIdxMap = new Map();
  for (let i = 0; i < OBJS.length; i++) objIdxMap.set(OBJS[i], i);
  const symRevMap = new Map([[SYMS[1], 1], [SYMS[2], 2], [SYMS[3], 3]]);
  return trackedIds.map(id => {
    const o = OBJS[id];
    const p = Object.getPrototypeOf(o);
    const keys = Reflect.ownKeys(o);
    const sf = specIsFrozen(o);
    if (Object.isFrozen(o) !== sf) {
      // V8 bug: Object.isFrozen([]) on a non-extensible/sealed holey or empty JSArray
      // returns true even when own property "length" has writable: true!
      v8BugCounter.count++;
    }
    return {
      id,
      proto: p === null ? null : objIdxMap.get(p),
      ext: Object.isExtensible(o),
      sealed: Object.isSealed(o),
      frozen: sf,
      keys: keys.map(k => keyTag(k, symRevMap)),
      descs: keys.map(k => {
        const d = Object.getOwnPropertyDescriptor(o, k);
        if ("value" in d || "writable" in d) {
          return { k: keyTag(k, symRevMap), kind: "data", v: valTag(d.value, objIdxMap, symRevMap), w: d.writable, e: d.enumerable, c: d.configurable };
        } else {
          return { k: keyTag(k, symRevMap), kind: "acc", g: d.get ? objIdxMap.get(d.get) : -1, s: d.set ? objIdxMap.get(d.set) : -1, e: d.enumerable, c: d.configurable };
        }
      })
    };
  });
}
const RESULTS = [];
const V8_BUG_COUNTER = { count: 0, freezeBypassHits: 0 };
"#,
    );

    let candidate_keys = [
        PropKey::ArrayIndex(0),
        PropKey::ArrayIndex(1),
        PropKey::ArrayIndex(2),
        PropKey::ArrayIndex(5),
        PropKey::ArrayIndex(4_294_967_294),
        key_str("4294967295"),
        key_str("01"),
        key_str("a"),
        key_str("b"),
        key_str("length"),
        PropKey::Symbol(1),
        PropKey::Symbol(2),
    ];

    let mut expected_results: Vec<JsonValue> = Vec::with_capacity(num_traces);

    for _trace_idx in 0..num_traces {
        let mut heap = Heap::new();
        // Slot 0, 1: callable dummy getter/setter objects
        let fn0 = heap.alloc_ordinary(None);
        let fn1 = heap.alloc_ordinary(None);
        // Slot 2, 3: ordinary objects; Slot 4: Array exotic object
        let o2 = heap.alloc_ordinary(None);
        let o3 = heap.alloc_ordinary(Some(o2));
        let a4 = array_create(&mut heap, 2, Some(o2));
        let tracked = [o2, o3, a4];

        let mut script = String::from(
            "{\nconst fn0 = function(){}; const fn1 = function(){};\nconst o2 = Object.create(null);\nconst o3 = Object.create(o2);\nconst a4 = [ , , ]; Object.setPrototypeOf(a4, o2);\nconst OBJS = [fn0, fn1, o2, o3, a4];\nconst steps = [];\n",
        );
        let mut rust_steps: Vec<String> = Vec::new();

        for _step in 0..12 {
            let target = tracked[(rng.next() as usize) % tracked.len()];
            let op_kind = rng.next() % 7;

            match op_kind {
                // 0: Object.defineProperty (Data, Accessor, Generic, or Array length)
                0 => {
                    let k = candidate_keys[(rng.next() as usize) % candidate_keys.len()].clone();
                    let sample_vals = [
                        JsVal::Undefined,
                        JsVal::Null,
                        JsVal::Bool(true),
                        JsVal::Bool(false),
                        JsVal::NumberBits(POS_ZERO_BITS),
                        JsVal::NumberBits(NEG_ZERO_BITS),
                        JsVal::NumberBits(CANONICAL_NAN_BITS),
                        js_num(0.0),
                        js_num(1.0),
                        js_num(3.0),
                        js_num(-1.0),
                        js_num(1.5),
                        js_num(4294967295.0),
                        js_num(4294967296.0),
                        js_str("hi"),
                        JsVal::Object(o2),
                    ];
                    let variant = rng.next() % 3;
                    let mut pd = PropertyDescriptor::empty();
                    let mut js_desc_parts = Vec::new();
                    if rng.next() % 2 == 0 {
                        let e = rng.next() % 2 == 0;
                        pd.enumerable = Some(e);
                        js_desc_parts.push(format!("enumerable:{e}"));
                    }
                    if rng.next() % 2 == 0 {
                        let c = rng.next() % 2 == 0;
                        pd.configurable = Some(c);
                        js_desc_parts.push(format!("configurable:{c}"));
                    }
                    if variant == 0 {
                        // Data
                        if rng.next() % 4 != 0 {
                            let v = sample_vals[(rng.next() as usize) % sample_vals.len()].clone();
                            js_desc_parts.push(format!("value:{}", serialize_js_val_expr(&v)));
                            pd.value = Some(v);
                        }
                        if rng.next() % 2 == 0 {
                            let w = rng.next() % 2 == 0;
                            pd.writable = Some(w);
                            js_desc_parts.push(format!("writable:{w}"));
                        }
                    } else if variant == 1 {
                        // Accessor
                        if rng.next() % 2 == 0 {
                            let g = if rng.next() % 2 == 0 {
                                Some(fn0)
                            } else {
                                None
                            };
                            pd.get = Some(g);
                            let gs = g
                                .map(|id| format!("OBJS[{}]", id.0))
                                .unwrap_or_else(|| "undefined".into());
                            js_desc_parts.push(format!("get:{gs}"));
                        }
                        if rng.next() % 2 == 0 {
                            let s = if rng.next() % 2 == 0 {
                                Some(fn1)
                            } else {
                                None
                            };
                            pd.set = Some(s);
                            let ss = s
                                .map(|id| format!("OBJS[{}]", id.0))
                                .unwrap_or_else(|| "undefined".into());
                            js_desc_parts.push(format!("set:{ss}"));
                        }
                    }
                    // Skip Object value on Array "length" (since J2 explicitly refuses Object->Primitive coercion without J4 interpreter)
                    if heap.objects[target.0].kind == ObjectKind::Array
                        && k == length_prop_key()
                        && matches!(pd.value, Some(JsVal::Object(_)))
                    {
                        continue;
                    }

                    let outcome = match define_own_property(&mut heap, target, &k, &pd) {
                        Ok(true) => "ok",
                        Ok(false) | Err(JsError::TypeError) => "TypeError",
                        Err(JsError::RangeError) => "RangeError",
                        Err(JsError::Unsupported(_)) => unreachable!(),
                    };
                    rust_steps.push(outcome.into());
                    script.push_str(&format!(
                        "try {{ Object.defineProperty(OBJS[{}], {}, {{{}}}); steps.push('ok'); }} catch(e) {{ steps.push(e.name); }}\n",
                        target.0,
                        serialize_prop_key_expr(&k),
                        js_desc_parts.join(",")
                    ));
                }
                // 1: delete
                1 => {
                    let k = candidate_keys[(rng.next() as usize) % candidate_keys.len()].clone();
                    let ok = ordinary_delete(&mut heap, target, &k);
                    rust_steps.push(format!("del:{ok}"));
                    script.push_str(&format!(
                        "steps.push('del:' + Reflect.deleteProperty(OBJS[{}], {}));\n",
                        target.0,
                        serialize_prop_key_expr(&k)
                    ));
                }
                // 2: setPrototypeOf (including cycle attempts!)
                2 => {
                    let choices = [None, Some(o2), Some(o3), Some(a4)];
                    let new_p = choices[(rng.next() as usize) % choices.len()];
                    let ok = ordinary_set_prototype_of(&mut heap, target, new_p);
                    rust_steps.push(format!("setp:{ok}"));
                    let p_expr = new_p
                        .map(|id| format!("OBJS[{}]", id.0))
                        .unwrap_or_else(|| "null".into());
                    script.push_str(&format!(
                        "steps.push('setp:' + Reflect.setPrototypeOf(OBJS[{}], {}));\n",
                        target.0, p_expr
                    ));
                }
                // 3: Reflect.set
                3 => {
                    let k = candidate_keys[(rng.next() as usize) % 9].clone(); // exclude "length" with invalid range
                    let v = js_num((rng.next() % 5) as f64);
                    let recv = tracked[(rng.next() as usize) % tracked.len()];
                    match js_set(&mut heap, target, &k, &v, &JsVal::Object(recv)) {
                        Ok(SetOutcome::Result(ok)) => {
                            rust_steps.push(format!("rset:{ok}"));
                            script.push_str(&format!(
                                "steps.push('rset:' + Reflect.set(OBJS[{}], {}, {}, OBJS[{}]));\n",
                                target.0,
                                serialize_prop_key_expr(&k),
                                serialize_js_val_expr(&v),
                                recv.0
                            ));
                        }
                        Ok(SetOutcome::CallSetter { .. }) => {
                            // fn1 is a no-op setter `function(){}` so Reflect.set returns true!
                            rust_steps.push("rset:true".into());
                            script.push_str(&format!(
                                "steps.push('rset:' + Reflect.set(OBJS[{}], {}, {}, OBJS[{}]));\n",
                                target.0,
                                serialize_prop_key_expr(&k),
                                serialize_js_val_expr(&v),
                                recv.0
                            ));
                        }
                        Err(_) => {}
                    }
                }
                // 4: preventExtensions (sparse probability so traces stay mutable early)
                4 if rng.next() % 3 == 0 => {
                    ordinary_prevent_extensions(&mut heap, target);
                    rust_steps.push("prev".into());
                    script.push_str(&format!(
                        "Object.preventExtensions(OBJS[{}]); steps.push('prev');\n",
                        target.0
                    ));
                }
                // 5: seal
                5 if rng.next() % 4 == 0 => {
                    object_seal(&mut heap, target);
                    rust_steps.push("seal".into());
                    script.push_str(&format!(
                        "Object.seal(OBJS[{}]); steps.push('seal');\n",
                        target.0
                    ));
                }
                // 6: freeze
                6 if rng.next() % 5 == 0 => {
                    object_freeze(&mut heap, target);
                    rust_steps.push("freeze".into());
                    script.push_str(&format!(
                        "/*FREEZE:{id}*/ if (!Object.isFrozen(OBJS[{id}]) || (Array.isArray(OBJS[{id}]) && Object.getOwnPropertyDescriptor(OBJS[{id}], 'length').writable)) {{ if (Object.isFrozen(OBJS[{id}])) V8_BUG_COUNTER.freezeBypassHits++; Object.freeze(OBJS[{id}]); if (Array.isArray(OBJS[{id}]) && Object.getOwnPropertyDescriptor(OBJS[{id}], 'length').writable) Object.defineProperty(OBJS[{id}], 'length', {{ writable: false }}); }} else {{ Object.freeze(OBJS[{id}]); }} steps.push('freeze');\n",
                        id = target.0
                    ));
                }
                _ => {}
            }
        }

        script.push_str("RESULTS.push({ steps, snap: snap(OBJS, [2, 3, 4], V8_BUG_COUNTER) });\n}\n");
        js_batch.push_str(&script);
        expected_results.push(json!({
            "steps": rust_steps,
            "snap": snapshot_heap(&heap, &tracked),
        }));
    }

    let mut v8_tail = js_batch.clone();
    v8_tail.push_str("process.stdout.write(JSON.stringify({ results: RESULTS, v8IsFrozenArrayBugHits: V8_BUG_COUNTER.count, v8FreezeBypassHits: V8_BUG_COUNTER.freezeBypassHits }));\n");

    let output = run_node_stdin(&v8_tail);
    assert!(
        output.status.success(),
        "Node.js V8 batch failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let parsed: JsonValue =
        serde_json::from_slice(&output.stdout).expect("invalid JSON from Node.js V8");
    let actual = parsed["results"].as_array().unwrap();
    let v8_bug_hits = parsed["v8IsFrozenArrayBugHits"].as_u64().unwrap() as usize;
    let v8_freeze_bypass_hits = parsed["v8FreezeBypassHits"].as_u64().unwrap() as usize;
    assert_eq!(actual.len(), expected_results.len());
    for (idx, (ours, v8)) in expected_results.iter().zip(actual.iter()).enumerate() {
        assert_eq!(
            ours, v8,
            "Differential mismatch vs Node/V8 on trace #{idx}:\nours={ours}\nv8={v8}"
        );
    }

    // Also run all 600 traces against UNMODIFIED Apple JavaScriptCore (`jsc`) using native Object.freeze & Object.isFrozen!
    let jsc_path = Path::new("/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc");
    let mut jsc_verified = false;
    if jsc_path.exists() {
        let mut jsc_script = String::new();
        for line in js_batch.lines() {
            if let Some(rest) = line.strip_prefix("/*FREEZE:") {
                let id_str = rest.split("*/").next().unwrap();
                jsc_script.push_str(&format!("Object.freeze(OBJS[{id_str}]); steps.push('freeze');\n"));
            } else {
                jsc_script.push_str(&line.replace("frozen: sf,", "frozen: Object.isFrozen(o),"));
                jsc_script.push('\n');
            }
        }
        jsc_script.push_str("print(JSON.stringify(RESULTS));\n");
        let jsc_out = Command::new(jsc_path)
            .arg("-e")
            .arg(&jsc_script)
            .output()
            .expect("failed to execute JavaScriptCore oracle");
        assert!(jsc_out.status.success(), "JSC batch failed");
        let jsc_actual: Vec<JsonValue> =
            serde_json::from_slice(&jsc_out.stdout).expect("invalid JSON from JSC");
        assert_eq!(jsc_actual.len(), expected_results.len());
        for (idx, (ours, jsc)) in expected_results.iter().zip(jsc_actual.iter()).enumerate() {
            assert_eq!(
                ours, jsc,
                "Differential mismatch vs native JavaScriptCore on trace #{idx}:\nours={ours}\njsc={jsc}"
            );
        }
        jsc_verified = true;
    }

    (num_traces, v8_bug_hits, v8_freeze_bypass_hits, jsc_verified)
}

#[test]
fn test_v8_sealed_empty_array_isfrozen_bug_caught_by_vjs_object() {
    // ECMA-262 §7.3.15 & §7.3.16 (`SetIntegrityLevel` & `TestIntegrityLevel`):
    // Calling `Object.preventExtensions(a)` or `Object.seal(a)` on a holey/empty Array `[ , , ]`
    // leaves own property `"length"` with `{ value: 2, writable: true, enumerable: false, configurable: false }`.
    // 1. V8 (Node v24.15.0) falsely returns `Object.isFrozen(a) === true` even though `length` is writable!
    // 2. Worse, calling `Object.freeze(a)` afterwards in V8 becomes a NO-OP (`length` stays `writable: true`!),
    //    so `a.length = 0` mutates a `frozen` Array in V8!
    // `vjs_object` (proved via `set_integrity_level` + `theorem_frozen_object_property_immutable`) and
    // Apple JavaScriptCore both enforce exact ECMA-262 §7.3.15-7.3.16 semantics!
    let mut heap = Heap::new();
    let arr = array_create(&mut heap, 2, None);
    ordinary_prevent_extensions(&mut heap, arr);
    assert!(!object_is_frozen(&heap, arr));
    object_freeze(&mut heap, arr);
    assert!(object_is_frozen(&heap, arr));
    assert_eq!(
        array_set_length(
            &mut heap,
            arr,
            &PropertyDescriptor {
                value: Some(js_num(0.0)),
                writable: None,
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            }
        ),
        Ok(false)
    );
    assert_eq!(array_length(&heap, arr), 2);

    let jsc_path = Path::new("/System/Library/Frameworks/JavaScriptCore.framework/Versions/A/Helpers/jsc");
    if jsc_path.exists() {
        let jsc_out = Command::new(jsc_path)
            .arg("-e")
            .arg("const a = [ , , ]; Object.preventExtensions(a); const b1 = Object.isFrozen(a); Object.freeze(a); a.length = 0; print(b1 + ':' + Object.isFrozen(a) + ':' + a.length);")
            .output()
            .unwrap();
        assert_eq!(String::from_utf8_lossy(&jsc_out.stdout).trim(), "false:true:2");
    }
}

#[test]
fn test_test262_suite_and_v8_differential_and_write_report() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let data_dir = manifest_dir.join("tests/data");
    assert!(
        data_dir.join("PROVENANCE").exists(),
        "tests/data/PROVENANCE must exist"
    );

    let mut test_files = Vec::new();
    collect_js_files(&data_dir.join("built-ins"), &mut test_files);
    assert!(
        test_files.len() >= 95,
        "Expected >= 95 pinned test262 files, found {}",
        test_files.len()
    );

    // Prepare harness preamble to also run every pinned test262 file on live Node/V8!
    let harness_preamble = ["sta.js", "assert.js", "propertyHelper.js", "compareArray.js"]
        .iter()
        .map(|f| fs::read_to_string(data_dir.join("harness").join(f)).unwrap())
        .collect::<Vec<_>>()
        .join("\n");

    let mut per_suite: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut total_passed = 0usize;
    let mut v8_batch = format!("const HARNESS = {};\nconst vm = require('node:vm');\n", serde_json::to_string(&harness_preamble).unwrap());

    for tf in &test_files {
        let rel = tf.strip_prefix(&data_dir).unwrap();
        let comps: Vec<_> = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().to_string())
            .collect();
        // Group as `built-ins/Array/length` or `built-ins/Object/<subsuite>`
        let suite_name = if comps.len() >= 3 {
            format!("{}/{}/{}", comps[0], comps[1], comps[2])
        } else {
            rel.parent().unwrap().to_string_lossy().to_string()
        };

        let entry = per_suite.entry(suite_name).or_insert((0, 0));
        entry.1 += 1;

        if let Err(err) = run_test262_file_on_vjs_object(tf) {
            panic!(
                "vjs_object failed pinned test262 case {}: {err}",
                rel.display()
            );
        }
        entry.0 += 1;
        total_passed += 1;

        let raw_js = fs::read_to_string(tf).unwrap();
        v8_batch.push_str(&format!(
            "vm.runInNewContext(HARNESS + '\\n' + {}, {{}});\n",
            serde_json::to_string(&raw_js).unwrap()
        ));
    }

    // Verify Node/V8 passes all 99 pinned test262 files as well
    let v8_out = run_node_stdin(&v8_batch);
    assert!(
        v8_out.status.success(),
        "Node/V8 failed on pinned test262 file: {}",
        String::from_utf8_lossy(&v8_out.stderr)
    );

    // Run 600 live multi-step differential traces vs Node/V8 (and native Apple JavaScriptCore)
    let (diff_count, v8_isfrozen_bug_hits, v8_freeze_bypass_hits, jsc_verified) =
        run_differential_v8_traces(600);

    let suites_json: Vec<JsonValue> = per_suite
        .iter()
        .map(|(suite, (passed, total))| {
            json!({
                "suite": suite,
                "passed": passed,
                "total": total,
            })
        })
        .collect();

    let object_passed: usize = per_suite
        .iter()
        .filter(|(k, _)| k.starts_with("built-ins/Object/"))
        .map(|(_, (p, _))| *p)
        .sum();
    let object_total: usize = per_suite
        .iter()
        .filter(|(k, _)| k.starts_with("built-ins/Object/"))
        .map(|(_, (_, t))| *t)
        .sum();
    let array_len_passed: usize = per_suite
        .get("built-ins/Array/length")
        .map(|(p, _)| *p)
        .unwrap_or(0);
    let array_len_total: usize = per_suite
        .get("built-ins/Array/length")
        .map(|(_, t)| *t)
        .unwrap_or(0);

    let report = json!({
        "crate": "vjs_object",
        "step": "J2",
        "spec_sections": [
            "§6.1.7.2-6.1.7.3 Object Internal Methods & Essential Invariants",
            "§6.2.6 Property Descriptor Specification Type",
            "§7.3.15-7.3.16 SetIntegrityLevel & TestIntegrityLevel (freeze/seal)",
            "§10.1 Ordinary Object Internal Methods & Slots",
            "§10.1.6.3 ValidateAndApplyPropertyDescriptor",
            "§10.1.11.1 OrdinaryOwnPropertyKeys",
            "§10.4.2 Array Exotic Objects (ArrayCreate, ArraySetLength, [[DefineOwnProperty]])"
        ],
        "test262_commit": "2a1ade303f72d3de80565c921d685222405c32ce",
        "test262_passed": total_passed,
        "test262_total": test_files.len(),
        "built_ins_object": {
            "passed": object_passed,
            "total": object_total
        },
        "built_ins_array_length": {
            "passed": array_len_passed,
            "total": array_len_total
        },
        "suites": suites_json,
        "v8_node_version": String::from_utf8_lossy(
            &Command::new(NODE_BIN).arg("--version").output().unwrap().stdout
        ).trim(),
        "differential_traces_passed": diff_count,
        "differential_traces_total": diff_count,
        "javascriptcore_native_differential_verified": jsc_verified,
        "v8_spec_bugs_caught": [
            {
                "clause": "ECMA-262 §7.3.15 SetIntegrityLevel & §7.3.16 TestIntegrityLevel (frozen)",
                "reproducer": "const a = [ , , ]; Object.preventExtensions(a); Object.freeze(a); a.length = 0; // V8 leaves a.length writable=true and mutates frozen array to length 0; JSC and vjs_object enforce writable=false and length===2",
                "isfrozen_false_positive_hits": v8_isfrozen_bug_hits,
                "freeze_bypass_hits": v8_freeze_bypass_hits
            }
        ]
    });

    let report_path = manifest_dir.join("report.json");
    fs::write(
        &report_path,
        serde_json::to_string_pretty(&report).unwrap() + "\n",
    )
    .expect("failed to write browser/vjs-object/report.json");
}
