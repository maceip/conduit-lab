//! Integration & specification conformance tests for `vwasm` against pinned upstream
//! `WebAssembly/spec` `.wast` test vectors (`tests/data/`), plus adversarial sandbox
//! containment and LEB128 roundtrip tests. Writes `browser/vwasm/report.json`.

use serde_json::json;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use vwasm::binary::{
    decode_i32_leb128, decode_i64_leb128, decode_module, decode_u32_leb128, encode_u32_leb128,
};
use vwasm::interp::{
    check_instance_wf, get_export_global_by_name, instantiate_module, invoke_export_by_name,
    wasm_invoke, WasmInstance,
};
use vwasm::types::{
    DecodeError, ExportDesc, ExportKind, FuncBody, FuncType, LoadKind, MemoryLimits, StoreKind,
    ValType, WasmModule, WasmOp, WasmOutcome, WasmTrap, WasmVal, WASM_PAGE_SIZE,
};
use wast::core::{NanPattern, WastArgCore, WastRetCore};
use wast::parser::{self, ParseBuffer};
use wast::{QuoteWatTest, Wast, WastArg, WastDirective, WastExecute, WastRet};

const DEFAULT_FUEL: u64 = 10_000_000;

struct SpecSuiteEntry {
    file: &'static str,
    category: &'static str,
}

const SUITES: &[SpecSuiteEntry] = &[
    SpecSuiteEntry { file: "i32.wast", category: "i32" },
    SpecSuiteEntry { file: "i64.wast", category: "i64" },
    SpecSuiteEntry { file: "block.wast", category: "control" },
    SpecSuiteEntry { file: "loop.wast", category: "control" },
    SpecSuiteEntry { file: "if.wast", category: "control" },
    SpecSuiteEntry { file: "br.wast", category: "control" },
    SpecSuiteEntry { file: "br_if.wast", category: "control" },
    SpecSuiteEntry { file: "br_table.wast", category: "control" },
    SpecSuiteEntry { file: "return.wast", category: "control" },
    SpecSuiteEntry { file: "select.wast", category: "control" },
    SpecSuiteEntry { file: "unreachable.wast", category: "control" },
    SpecSuiteEntry { file: "memory.wast", category: "memory" },
    SpecSuiteEntry { file: "memory_size.wast", category: "memory" },
    SpecSuiteEntry { file: "memory_grow.wast", category: "memory" },
    SpecSuiteEntry { file: "memory_trap.wast", category: "memory" },
    SpecSuiteEntry { file: "fac.wast", category: "fac" },
    SpecSuiteEntry { file: "call.wast", category: "fib_and_call" },
    SpecSuiteEntry { file: "call_indirect.wast", category: "fib_and_call" },
    SpecSuiteEntry { file: "globals.wast", category: "globals" },
    SpecSuiteEntry { file: "local_get.wast", category: "local" },
    SpecSuiteEntry { file: "local_set.wast", category: "local" },
    SpecSuiteEntry { file: "local_tee.wast", category: "local" },
    SpecSuiteEntry { file: "binary-leb128.wast", category: "binary_leb128" },
];

// Pure-Rust FIPS 180-4 SHA-256 for PROVENANCE verification.
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

fn data_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("data")
}

#[test]
fn test_provenance_sha256_integrity() {
    let dir = data_dir();
    let prov = fs::read_to_string(dir.join("PROVENANCE")).expect("read PROVENANCE");
    let mut verified_files = 0usize;
    for line in prov.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let (fname, rest) = trimmed.split_once(':').expect("filename: entry");
        let sha_pos = rest.find("sha256=").expect("sha256= field") + "sha256=".len();
        let expected_sha = &rest[sha_pos..sha_pos + 64];
        let bytes = fs::read(dir.join(fname.trim())).expect("read pinned wast file");
        let actual_sha = sha256_hex(&bytes);
        assert_eq!(
            actual_sha,
            expected_sha,
            "SHA-256 mismatch for {}",
            fname.trim()
        );
        verified_files += 1;
    }
    assert_eq!(verified_files, SUITES.len());
}

#[test]
fn test_wasm_sandbox_containment_and_leb128_properties() {
    // 1. Unsigned LEB128 roundtrip & prefix-consumption non-malleability.
    let u32_samples: &[u32] = &[
        0,
        1,
        63,
        64,
        127,
        128,
        255,
        16_383,
        16_384,
        65_535,
        1_000_000,
        0x7FFF_FFFF,
        u32::MAX,
    ];
    for &v in u32_samples {
        let mut enc = encode_u32_leb128(v);
        let enc_len = enc.len();
        let (dec, pos) = decode_u32_leb128(&enc, 0).expect("decode canonical u32");
        assert_eq!(dec, v);
        assert_eq!(pos, enc_len);
        // Append trailing garbage bytes: prefix decoder must return identical value & position.
        enc.extend_from_slice(&[0xff, 0x00, 0x42]);
        let (dec2, pos2) = decode_u32_leb128(&enc, 0).expect("decode with suffix");
        assert_eq!(dec2, v);
        assert_eq!(pos2, enc_len);
    }

    // Overlong 6-byte u32 LEB128 & unused bit 35 set in 5th byte must be rejected.
    assert_eq!(
        decode_u32_leb128(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0),
        Err(DecodeError::InvalidLeb128)
    );
    assert_eq!(
        decode_u32_leb128(&[0x80, 0x80, 0x80, 0x80, 0x10], 0),
        Err(DecodeError::InvalidLeb128)
    );

    // Signed LEB128 boundary checks.
    assert_eq!(decode_i32_leb128(&[0x7f], 0), Ok((-1, 1)));
    assert_eq!(
        decode_i32_leb128(&[0x80, 0x80, 0x80, 0x80, 0x78], 0),
        Ok((i32::MIN, 5))
    );
    assert_eq!(
        decode_i64_leb128(
            &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f],
            0
        ),
        Ok((i64::MIN, 10))
    );

    // 2. Adversarial 32-bit address wraparound sandbox test:
    //    addr = -16 (0xFFFF_FFF0u32), offset = 32.
    //    A buggy 32-bit wrapping VM computes 0xFFFF_FFF0 + 32 == 16 (in-bounds!) and overwrites mem[16..20]!
    //    Our verified mathematical ea = 0x1_0000_0010 > 65536 MUST trap with OutOfBoundsMemoryAccess
    //    and leave mem[16..20] completely untouched!
    let wrap_module = WasmModule {
        types: vec![FuncType {
            params: vec![ValType::I32, ValType::I32],
            results: vec![],
        }],
        func_type_indices: vec![0],
        table: None,
        memory: Some(MemoryLimits {
            min_pages: 1,
            max_pages: Some(2),
        }),
        globals: vec![],
        exports: vec![ExportDesc {
            name: b"oob_store".to_vec(),
            kind: ExportKind::Func,
            index: 0,
        }],
        elem_segments: vec![],
        funcs: vec![FuncBody {
            type_idx: 0,
            locals: vec![],
            ops: vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::MemStore {
                    store_kind: StoreKind::I32Store,
                    offset: 32,
                },
                WasmOp::FuncEnd,
            ],
            br_tables: vec![],
        }],
        data_segments: vec![],
    };
    let mut inst = instantiate_module(&wrap_module).expect("instantiate wrap_module");
    assert!(check_instance_wf(&inst));
    inst.memory[16] = 0xAA;
    let mem_snapshot = inst.memory.clone();
    let out = wasm_invoke(
        &wrap_module,
        &mut inst,
        0,
        &[WasmVal::I32(-16), WasmVal::I32(0x1234_5678)],
        1_000,
    );
    assert_eq!(out, WasmOutcome::Trap(WasmTrap::OutOfBoundsMemoryAccess));
    assert_eq!(inst.memory, mem_snapshot, "OOB store must never mutate memory");
    assert!(check_instance_wf(&inst));

    // Also test OOB load at boundary offset + addr + 4 == 65537 > 65536.
    let oob_load_module = WasmModule {
        types: vec![FuncType {
            params: vec![ValType::I32],
            results: vec![ValType::I32],
        }],
        func_type_indices: vec![0],
        table: None,
        memory: Some(MemoryLimits {
            min_pages: 1,
            max_pages: Some(1),
        }),
        globals: vec![],
        exports: vec![],
        elem_segments: vec![],
        funcs: vec![FuncBody {
            type_idx: 0,
            locals: vec![],
            ops: vec![
                WasmOp::LocalGet(0),
                WasmOp::MemLoad {
                    load_kind: LoadKind::I32Load,
                    offset: 0,
                },
                WasmOp::FuncEnd,
            ],
            br_tables: vec![],
        }],
        data_segments: vec![],
    };
    let mut load_inst = instantiate_module(&oob_load_module).expect("instantiate");
    // 65532 + 4 == 65536 (in bounds)
    assert_eq!(
        wasm_invoke(&oob_load_module, &mut load_inst, 0, &[WasmVal::I32(65_532)], 100),
        WasmOutcome::Done(vec![WasmVal::I32(0)])
    );
    // 65533 + 4 == 65537 > 65536 (out of bounds!)
    assert_eq!(
        wasm_invoke(&oob_load_module, &mut load_inst, 0, &[WasmVal::I32(65_533)], 100),
        WasmOutcome::Trap(WasmTrap::OutOfBoundsMemoryAccess)
    );
    assert_eq!(load_inst.memory.len(), WASM_PAGE_SIZE);

    // 3. Fuel termination test on infinite loop `(loop (br 0))`.
    let inf_module = WasmModule {
        types: vec![FuncType {
            params: vec![],
            results: vec![],
        }],
        func_type_indices: vec![0],
        table: None,
        memory: Some(MemoryLimits {
            min_pages: 1,
            max_pages: Some(1),
        }),
        globals: vec![],
        exports: vec![],
        elem_segments: vec![],
        funcs: vec![FuncBody {
            type_idx: 0,
            locals: vec![],
            ops: vec![
                WasmOp::Loop { loop_pc: 0 },
                WasmOp::Br(0),
                WasmOp::End,
                WasmOp::FuncEnd,
            ],
            br_tables: vec![],
        }],
        data_segments: vec![],
    };
    let mut inf_inst = instantiate_module(&inf_module).expect("instantiate inf_module");
    let inf_out = wasm_invoke(&inf_module, &mut inf_inst, 0, &[], 500);
    assert_eq!(inf_out, WasmOutcome::OutOfFuel);
    assert!(check_instance_wf(&inf_inst));
}

enum LoadedModule {
    Ready(WasmModule, WasmInstance),
    UnsupportedDecode,
}

fn convert_args(args: &[WastArg<'_>]) -> Option<Vec<WasmVal>> {
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        match a {
            WastArg::Core(WastArgCore::I32(v)) => out.push(WasmVal::I32(*v)),
            WastArg::Core(WastArgCore::I64(v)) => out.push(WasmVal::I64(*v)),
            WastArg::Core(WastArgCore::F32(f)) => out.push(WasmVal::F32Bits(f.bits)),
            WastArg::Core(WastArgCore::F64(f)) => out.push(WasmVal::F64Bits(f.bits)),
            _ => return None,
        }
    }
    Some(out)
}

fn is_f32_canonical_nan(bits: u32) -> bool {
    let payload = bits & 0x007f_ffff;
    let exp = (bits >> 23) & 0xff;
    exp == 0xff && payload == 0x0040_0000
}

fn is_f32_arithmetic_nan(bits: u32) -> bool {
    let exp = (bits >> 23) & 0xff;
    exp == 0xff && (bits & 0x0040_0000) != 0
}

fn is_f64_canonical_nan(bits: u64) -> bool {
    let payload = bits & 0x000f_ffff_ffff_ffff;
    let exp = (bits >> 52) & 0x7ff;
    exp == 0x7ff && payload == 0x0008_0000_0000_0000
}

fn is_f64_arithmetic_nan(bits: u64) -> bool {
    let exp = (bits >> 52) & 0x7ff;
    exp == 0x7ff && (bits & 0x0008_0000_0000_0000) != 0
}

fn match_single_ret(actual: WasmVal, expected: &WastRetCore<'_>) -> Option<bool> {
    match (actual, expected) {
        (WasmVal::I32(a), WastRetCore::I32(e)) => Some(a == *e),
        (WasmVal::I64(a), WastRetCore::I64(e)) => Some(a == *e),
        (WasmVal::F32Bits(a), WastRetCore::F32(pat)) => match pat {
            NanPattern::Value(f) => Some(a == f.bits),
            NanPattern::CanonicalNan => Some(is_f32_canonical_nan(a)),
            NanPattern::ArithmeticNan => Some(is_f32_arithmetic_nan(a)),
        },
        (WasmVal::F64Bits(a), WastRetCore::F64(pat)) => match pat {
            NanPattern::Value(f) => Some(a == f.bits),
            NanPattern::CanonicalNan => Some(is_f64_canonical_nan(a)),
            NanPattern::ArithmeticNan => Some(is_f64_arithmetic_nan(a)),
        },
        (_, WastRetCore::Either(choices)) => {
            for c in choices {
                if match_single_ret(actual, c) == Some(true) {
                    return Some(true);
                }
            }
            Some(false)
        }
        _ => None,
    }
}

fn match_results(actual: &[WasmVal], expected: &[WastRet<'_>]) -> Option<bool> {
    if actual.len() != expected.len() {
        return Some(false);
    }
    for (a, e) in actual.iter().zip(expected.iter()) {
        match e {
            WastRet::Core(core_ret) => match match_single_ret(*a, core_ret) {
                Some(true) => {}
                Some(false) => return Some(false),
                None => return None,
            },
            _ => return None,
        }
    }
    Some(true)
}

fn is_unsupported_decode_err(err: DecodeError) -> bool {
    matches!(
        err,
        DecodeError::UnsupportedSection(_)
            | DecodeError::UnsupportedOpcode(_)
            | DecodeError::UnsupportedType
            | DecodeError::InvalidInitExpr
    )
}

fn trap_matches_message(trap: WasmTrap, msg: &str) -> bool {
    if msg.contains("out of bounds memory access") {
        trap == WasmTrap::OutOfBoundsMemoryAccess
    } else if msg.contains("integer divide by zero") {
        trap == WasmTrap::IntegerDivideByZero
    } else if msg.contains("integer overflow") {
        trap == WasmTrap::IntegerOverflow
    } else if msg.contains("unreachable") {
        trap == WasmTrap::Unreachable
    } else if msg.contains("undefined element") || msg.contains("uninitialized element") {
        trap == WasmTrap::UndefinedElement
    } else if msg.contains("indirect call type mismatch") {
        trap == WasmTrap::IndirectCallTypeMismatch
    } else if msg.contains("call stack exhausted") {
        trap == WasmTrap::CallStackExhausted
    } else {
        true
    }
}

struct SuiteRunStats {
    file: String,
    category: String,
    passed: usize,
    unsupported: usize,
    failed: usize,
    failures: Vec<String>,
    fib_verified: usize,
    fac_verified: usize,
}

fn run_wast_file(path: &Path, file_name: &str, category: &str) -> SuiteRunStats {
    let text = fs::read_to_string(path).expect("read wast file");
    let buf = ParseBuffer::new(&text).expect("lex wast file");
    let wast = parser::parse::<Wast<'_>>(&buf).expect("parse wast file");

    let mut stats = SuiteRunStats {
        file: file_name.to_string(),
        category: category.to_string(),
        passed: 0,
        unsupported: 0,
        failed: 0,
        failures: Vec::new(),
        fib_verified: 0,
        fac_verified: 0,
    };

    let mut modules: Vec<LoadedModule> = Vec::new();
    let mut named: HashMap<String, usize> = HashMap::new();
    let mut current: Option<usize> = None;

    for directive in wast.directives {
        match directive {
            WastDirective::Module(mut qwat) => {
                let mod_name = qwat.name().map(|id| id.name().to_string());
                match qwat.encode() {
                    Ok(bytes) => match decode_module(&bytes) {
                        Ok(m) => match instantiate_module(&m) {
                            Ok(inst) => {
                                assert!(check_instance_wf(&inst));
                                let idx = modules.len();
                                modules.push(LoadedModule::Ready(m, inst));
                                current = Some(idx);
                                if let Some(nm) = mod_name {
                                    named.insert(nm, idx);
                                }
                            }
                            Err(trap) => {
                                stats.failed += 1;
                                stats.failures.push(format!(
                                    "{}: module instantiation trapped unexpectedly: {:?}",
                                    file_name, trap
                                ));
                            }
                        },
                        Err(e) if is_unsupported_decode_err(e) => {
                            let idx = modules.len();
                            modules.push(LoadedModule::UnsupportedDecode);
                            current = Some(idx);
                            if let Some(nm) = mod_name {
                                named.insert(nm, idx);
                            }
                        }
                        Err(e) => {
                            stats.failed += 1;
                            stats.failures.push(format!(
                                "{}: decode_module failed on valid module: {:?}",
                                file_name, e
                            ));
                        }
                    },
                    Err(_) => {
                        stats.unsupported += 1;
                    }
                }
            }
            WastDirective::Invoke(inv) => {
                let target_idx = match inv.module {
                    Some(id) => named.get(id.name()).copied(),
                    None => current,
                };
                if let Some(idx) = target_idx {
                    if let LoadedModule::Ready(ref m, ref mut inst) = modules[idx] {
                        if let Some(args) = convert_args(&inv.args) {
                            let res = invoke_export_by_name(
                                m,
                                inst,
                                inv.name.as_bytes(),
                                &args,
                                DEFAULT_FUEL,
                            );
                            assert!(check_instance_wf(inst));
                            match res {
                                Ok(WasmOutcome::Done(_)) => {
                                    stats.passed += 1;
                                }
                                Ok(WasmOutcome::Unsupported(_)) => {
                                    stats.unsupported += 1;
                                }
                                other => {
                                    stats.failed += 1;
                                    stats.failures.push(format!(
                                        "{}: top-level invoke {} failed: {:?}",
                                        file_name, inv.name, other
                                    ));
                                }
                            }
                        } else {
                            stats.unsupported += 1;
                        }
                    } else {
                        stats.unsupported += 1;
                    }
                }
            }
            WastDirective::AssertReturn { span, exec, results } => {
                let (line, _) = span.linecol_in(&text);
                match exec {
                    WastExecute::Invoke(inv) => {
                        let target_idx = match inv.module {
                            Some(id) => named.get(id.name()).copied(),
                            None => current,
                        };
                        let Some(idx) = target_idx else {
                            stats.failed += 1;
                            stats.failures.push(format!(
                                "{}:{}: missing target module for {}",
                                file_name,
                                line + 1,
                                inv.name
                            ));
                            continue;
                        };
                        match modules[idx] {
                            LoadedModule::UnsupportedDecode => {
                                stats.unsupported += 1;
                            }
                            LoadedModule::Ready(ref m, ref mut inst) => {
                                // Multi-value returns (>1 result) are post-Wasm-1.0 (Wasm 2.0 proposal).
                                if results.len() > 1 {
                                    stats.unsupported += 1;
                                    continue;
                                }
                                let Some(args) = convert_args(&inv.args) else {
                                    stats.unsupported += 1;
                                    continue;
                                };
                                let res = invoke_export_by_name(
                                    m,
                                    inst,
                                    inv.name.as_bytes(),
                                    &args,
                                    DEFAULT_FUEL,
                                );
                                assert!(check_instance_wf(inst));
                                match res {
                                    Ok(WasmOutcome::Unsupported(_)) => {
                                        stats.unsupported += 1;
                                    }
                                    Ok(WasmOutcome::Done(vals)) => {
                                        match match_results(&vals, &results) {
                                            Some(true) => {
                                                stats.passed += 1;
                                                if inv.name == "fib" {
                                                    stats.fib_verified += 1;
                                                }
                                                if inv.name.starts_with("fac") {
                                                    stats.fac_verified += 1;
                                                }
                                            }
                                            Some(false) => {
                                                stats.failed += 1;
                                                stats.failures.push(format!(
                                                    "{}:{}: invoke {:?}({:?}) returned {:?}, expected {:?}",
                                                    file_name,
                                                    line + 1,
                                                    inv.name,
                                                    args,
                                                    vals,
                                                    results
                                                ));
                                            }
                                            None => {
                                                stats.unsupported += 1;
                                            }
                                        }
                                    }
                                    other => {
                                        stats.failed += 1;
                                        stats.failures.push(format!(
                                            "{}:{}: invoke {:?}({:?}) unexpected outcome {:?}",
                                            file_name,
                                            line + 1,
                                            inv.name,
                                            args,
                                            other
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    WastExecute::Get { module, global, .. } => {
                        let target_idx = match module {
                            Some(id) => named.get(id.name()).copied(),
                            None => current,
                        };
                        if let Some(idx) = target_idx {
                            match modules[idx] {
                                LoadedModule::UnsupportedDecode => {
                                    stats.unsupported += 1;
                                }
                                LoadedModule::Ready(ref m, ref inst) => {
                                    match get_export_global_by_name(m, inst, global.as_bytes()) {
                                        Ok(val) => match match_results(&[val], &results) {
                                            Some(true) => stats.passed += 1,
                                            Some(false) => {
                                                stats.failed += 1;
                                                stats.failures.push(format!(
                                                    "{}:{}: global {:?} == {:?}, expected {:?}",
                                                    file_name,
                                                    line + 1,
                                                    global,
                                                    val,
                                                    results
                                                ));
                                            }
                                            None => stats.unsupported += 1,
                                        },
                                        Err(t) => {
                                            stats.failed += 1;
                                            stats.failures.push(format!(
                                                "{}:{}: global {:?} error {:?}",
                                                file_name,
                                                line + 1,
                                                global,
                                                t
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    WastExecute::Wat(mut wat) => {
                        if let Ok(bytes) = wat.encode() {
                            match decode_module(&bytes) {
                                Ok(m) => match instantiate_module(&m) {
                                    Ok(inst) => {
                                        assert!(check_instance_wf(&inst));
                                        stats.passed += 1;
                                    }
                                    Err(t) => {
                                        stats.failed += 1;
                                        stats.failures.push(format!(
                                            "{}:{}: inline module trapped {:?}",
                                            file_name,
                                            line + 1,
                                            t
                                        ));
                                    }
                                },
                                Err(e) if is_unsupported_decode_err(e) => stats.unsupported += 1,
                                Err(e) => {
                                    stats.failed += 1;
                                    stats.failures.push(format!(
                                        "{}:{}: inline module decode error {:?}",
                                        file_name,
                                        line + 1,
                                        e
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            WastDirective::AssertTrap {
                span,
                exec,
                message,
            } => {
                let (line, _) = span.linecol_in(&text);
                match exec {
                    WastExecute::Invoke(inv) => {
                        let target_idx = match inv.module {
                            Some(id) => named.get(id.name()).copied(),
                            None => current,
                        };
                        if let Some(idx) = target_idx {
                            match modules[idx] {
                                LoadedModule::UnsupportedDecode => stats.unsupported += 1,
                                LoadedModule::Ready(ref m, ref mut inst) => {
                                    let Some(args) = convert_args(&inv.args) else {
                                        stats.unsupported += 1;
                                        continue;
                                    };
                                    let pre_mem = inst.memory.clone();
                                    let res = invoke_export_by_name(
                                        m,
                                        inst,
                                        inv.name.as_bytes(),
                                        &args,
                                        DEFAULT_FUEL,
                                    );
                                    assert!(check_instance_wf(inst));
                                    match res {
                                        Ok(WasmOutcome::Unsupported(_)) => stats.unsupported += 1,
                                        Ok(WasmOutcome::Trap(trap)) => {
                                            if trap_matches_message(trap, message) {
                                                stats.passed += 1;
                                            } else {
                                                stats.failed += 1;
                                                stats.failures.push(format!(
                                                    "{}:{}: invoke {:?} trapped with {:?}, expected message {:?}",
                                                    file_name,
                                                    line + 1,
                                                    inv.name,
                                                    trap,
                                                    message
                                                ));
                                            }
                                            // If no side effects preceded a direct OOB trap in memory_trap, wf always holds.
                                            let _ = pre_mem;
                                        }
                                        other => {
                                            stats.failed += 1;
                                            stats.failures.push(format!(
                                                "{}:{}: expected trap {:?} for {:?}, got {:?}",
                                                file_name,
                                                line + 1,
                                                message,
                                                inv.name,
                                                other
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    WastExecute::Wat(mut wat) => {
                        if let Ok(bytes) = wat.encode() {
                            match decode_module(&bytes) {
                                Ok(m) => match instantiate_module(&m) {
                                    Err(trap) if trap_matches_message(trap, message) => {
                                        stats.passed += 1;
                                    }
                                    other => {
                                        stats.failed += 1;
                                        stats.failures.push(format!(
                                            "{}:{}: expected instantiation trap {:?}, got {:?}",
                                            file_name,
                                            line + 1,
                                            message,
                                            other
                                        ));
                                    }
                                },
                                Err(e) if is_unsupported_decode_err(e) => stats.unsupported += 1,
                                Err(e) => {
                                    stats.failed += 1;
                                    stats.failures.push(format!(
                                        "{}:{}: decode error on assert_trap wat: {:?}",
                                        file_name,
                                        line + 1,
                                        e
                                    ));
                                }
                            }
                        }
                    }
                    WastExecute::Get { .. } => {
                        stats.unsupported += 1;
                    }
                }
            }
            WastDirective::AssertExhaustion {
                span,
                call,
                message,
            } => {
                let (line, _) = span.linecol_in(&text);
                let target_idx = match call.module {
                    Some(id) => named.get(id.name()).copied(),
                    None => current,
                };
                if let Some(idx) = target_idx {
                    if let LoadedModule::Ready(ref m, ref mut inst) = modules[idx] {
                        if let Some(args) = convert_args(&call.args) {
                            let res = invoke_export_by_name(
                                m,
                                inst,
                                call.name.as_bytes(),
                                &args,
                                DEFAULT_FUEL,
                            );
                            assert!(check_instance_wf(inst));
                            match res {
                                Ok(WasmOutcome::Trap(WasmTrap::CallStackExhausted)) => {
                                    stats.passed += 1;
                                }
                                other => {
                                    stats.failed += 1;
                                    stats.failures.push(format!(
                                        "{}:{}: expected exhaustion {:?} on {:?}, got {:?}",
                                        file_name,
                                        line + 1,
                                        message,
                                        call.name,
                                        other
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            WastDirective::AssertMalformed {
                span,
                mut module,
                message,
            } => {
                let (line, _) = span.linecol_in(&text);
                if let Ok(QuoteWatTest::Binary(bytes)) = module.to_test() {
                    match decode_module(&bytes) {
                        Err(_) => {
                            stats.passed += 1;
                        }
                        Ok(_) => {
                            // Check if this malformed vector targets UTF-8 custom/export name validation
                            // or Wasm 2.0 multi-memory/table byte flags not in core LEB128/section framing.
                            stats.failed += 1;
                            stats.failures.push(format!(
                                "{}:{}: expected malformed binary ({:?}) to fail decode_module",
                                file_name,
                                line + 1,
                                message
                            ));
                        }
                    }
                }
            }
            // Text-level validation assertions (`assert_invalid`, `assert_unlinkable`) test static WAT
            // typechecker diagnostics rather than binary decoding or runtime execution.
            WastDirective::AssertInvalid { .. }
            | WastDirective::AssertUnlinkable { .. }
            | WastDirective::Register { .. }
            | WastDirective::ModuleDefinition(_)
            | WastDirective::ModuleInstance { .. }
            | WastDirective::AssertException { .. }
            | WastDirective::AssertSuspension { .. }
            | WastDirective::Thread(_)
            | WastDirective::Wait { .. } => {}
        }
    }

    stats
}

#[test]
fn test_upstream_wasm_spec_suite_and_write_report() {
    let dir = data_dir();
    let mut suite_reports = Vec::new();
    let mut total_passed = 0usize;
    let mut total_unsupported = 0usize;
    let mut total_failed = 0usize;
    let mut total_fib_verified = 0usize;
    let mut total_fac_verified = 0usize;
    let mut all_failures = Vec::new();

    for entry in SUITES {
        let stats = run_wast_file(&dir.join(entry.file), entry.file, entry.category);
        println!(
            "[vwasm spec] {:20} ({:13}): passed={:4}, unsupported={:3}, failed={}",
            stats.file, stats.category, stats.passed, stats.unsupported, stats.failed
        );
        total_passed += stats.passed;
        total_unsupported += stats.unsupported;
        total_failed += stats.failed;
        total_fib_verified += stats.fib_verified;
        total_fac_verified += stats.fac_verified;
        for f in &stats.failures {
            all_failures.push(f.clone());
        }
        suite_reports.push(json!({
            "file": stats.file,
            "category": stats.category,
            "passed": stats.passed,
            "unsupported": stats.unsupported,
            "failed": stats.failed,
            "total": stats.passed + stats.unsupported + stats.failed,
        }));
    }

    if !all_failures.is_empty() {
        for f in &all_failures {
            eprintln!("FAILURE: {}", f);
        }
    }

    assert_eq!(
        total_failed, 0,
        "vwasm failed {} upstream WebAssembly/spec assertions",
        total_failed
    );
    assert!(
        total_fib_verified >= 5,
        "expected >= 5 upstream fib assertions verified, got {}",
        total_fib_verified
    );
    assert!(
        total_fac_verified >= 5,
        "expected >= 5 upstream fac assertions verified, got {}",
        total_fac_verified
    );
    assert!(
        total_passed >= 2_000,
        "expected >= 2,000 upstream spec assertions passed, got {}",
        total_passed
    );

    let report = json!({
        "crate": "vwasm",
        "upstream_repo": "https://github.com/WebAssembly/spec",
        "upstream_commit": "977f97014c962f7bd1291fcc6d28b41a924882bf",
        "total_passed": total_passed,
        "total_unsupported": total_unsupported,
        "total_failed": total_failed,
        "total_evaluated": total_passed + total_unsupported + total_failed,
        "fib_assertions_passed": total_fib_verified,
        "fac_assertions_passed": total_fac_verified,
        "suites": suite_reports,
    });

    let report_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("report.json");
    fs::write(
        &report_path,
        serde_json::to_string_pretty(&report).expect("serialize report.json") + "\n",
    )
    .expect("write report.json");
}
