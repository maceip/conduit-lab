//! Cross-crate end-to-end integration test exercising all 11 formally verified browser crates
//! (`vurl`, `vjs_spec`, `vjs_types`, `vjs_object`, `vjs_syntax`, `vjs`, `vjs_webidl`,
//! `vjs_builtins`, `vjs_gc`, `vjs_vm`, and `vwasm`) in one unified pipeline:
//!
//! 1. `vurl` (Phase 1): WHATWG IPv4, IPv6, and percent-encoding URL origin + payload extraction.
//! 2. `vjs_webidl` (J4b): Web IDL `USVString` conversion + generational `KernelCapTable` gating,
//!    cross-origin/cross-realm refusal, and revocation safety.
//! 3. `vjs_syntax` (J3): Total UTF-8/UTF-16 lexing, Pratt/RD AST parsing, and Static Semantics:
//!    Early Errors validation.
//! 4. `vjs` (J4): End-to-end script evaluation (`eval_script`) with lexical closures, `try`/`finally`,
//!    optional chaining, arrays, and fuel/heap-quota accounting.
//! 5. `vjs_spec` (J0), `vjs_types` (J1), `vjs_object` (J2), `vjs_builtins` (J5), `vjs_gc` (J6):
//!    ESMeta-compiled abstract ops, Burger-Dybvig IEEE-754 `Number::toString` + `BigInt`,
//!    ordinary & Array exotic object heap with `Object.freeze` (§6.1.7.3), Vest-style JSON
//!    round-trip + Warblre-style RegExp + `Map`/`Set` + `Date`, and tricolor Mark-Sweep GC +
//!    Promise microtask `drain_jobs`.
//! 6. `vjs_vm` (J7): Verified AST-to-bytecode compilation and stack VM execution (`compile_and_run_verified`).
//! 7. `vwasm` (J7): Sandboxed WebAssembly 1.0 binary decoding, execution (`run_sandboxed_wasm_bytes`),
//!    and deterministic OOB linear-memory containment.

use vurl::ipv4::ipv4_parse;
use vurl::ipv6::{ipv6_parse, ipv6_serialize};
use vurl::percent::{percent_decode, percent_encode, EncodeSet};

use vjs::{eval_script, RunResult, ScriptCompletion, Val};
use vjs_builtins::collections::{JsKey, JsMap, JsSet};
use vjs_builtins::date::{make_date, make_day, make_time, parse_iso8601, time_clip, to_iso_string};
use vjs_builtins::json::{json_parse, json_stringify, JsonValue};
use vjs_builtins::regexp::{exec_match, parse_pattern, MatchOutcome, RegexFlags};
use vjs_gc::gc::{GcHeap, GcPayload, Slot};
use vjs_gc::promise_jobs::{DrainOutcome, PromiseRuntime, PromiseState, ReactionHandler};
use vjs_gc::types::JsVal as GcVal;
use vjs_object::array::{array_create, array_define_own_property, array_length, array_set_length};
use vjs_object::descriptor::PropertyDescriptor;
use vjs_object::heap::{prop_key_from_ascii, Heap as ObjectHeap, JsVal as ObjVal, PropKey};
use vjs_object::ordinary::{
    object_freeze, object_is_frozen, ordinary_define_own_property, ordinary_get, GetOutcome,
};
use vjs_spec::{
    number_left_shift, same_value as spec_same_value, to_boolean as spec_to_boolean,
    to_int32 as spec_to_int32, AbruptOrNormal, JsNumber as SpecNum, JsValue as SpecVal,
};
use vjs_syntax::{check_early_errors, parse_script_str, ParseOutcome as SyntaxOutcome};
use vjs_types::bigint::string_to_bigint;
use vjs_types::number::{number_to_string, string_to_number, JsNumber as TypesNum};
use vjs_types::ops::{is_strictly_equal, JsPrim as TypesPrim};
use vjs_types::utf16::utf8_to_utf16;
use vjs_vm::ast::{
    expr_list_from_vec, BinOp as VmBinOp, ExecProgramOutcome, Expr as VmExpr, Func as VmFunc,
    Program as VmProgram, Stmt as VmStmt,
};
use vjs_vm::compiler_proof::compile_and_run_verified;
use vjs_webidl::caps::{
    CapKind, HostError, KernelCapTable, OriginId, RealmId, PERM_LOG, PERM_READ, PERM_WRITE,
};
use vjs_webidl::conversions::{to_idl_usv_string, JsObjectArena, JsValue as IdlJsVal};
use vjs_webidl::dispatch::{dispatch, HostRequest, HostState};
use vwasm::binary::encode_u32_leb128;
use vwasm::interp::run_sandboxed_wasm_bytes;
use vwasm::types::{WasmOutcome, WasmTrap, WasmVal};

fn push_u32_leb(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&encode_u32_leb128(v));
}

fn push_section(wasm: &mut Vec<u8>, section_id: u8, payload: &[u8]) {
    wasm.push(section_id);
    push_u32_leb(wasm, payload.len() as u32);
    wasm.extend_from_slice(payload);
}

/// Builds a valid Wasm 1.0 binary module with:
/// - 1 linear memory page (`min = 1`, `max = Some(1)`, 65,536 bytes)
/// - `func 0` (`(param i32) (result i32)`): computes iterative `fib(n)`, stores the result at
///   linear memory offset `0`, loads it back with `i32.load`, and returns it.
/// - `func 1` (`(param i32) (result i32)`): attempts `i32.load` at `addr` (used to verify OOB trap).
fn build_fib_and_bounds_wasm_module() -> Vec<u8> {
    let mut wasm = b"\0asm\x01\x00\x00\x00".to_vec();

    // Type section (id=1): 1 func type `(param i32) -> (result i32)`
    let mut ty = Vec::new();
    push_u32_leb(&mut ty, 1);
    ty.push(0x60);
    push_u32_leb(&mut ty, 1);
    ty.push(0x7F); // i32
    push_u32_leb(&mut ty, 1);
    ty.push(0x7F); // i32
    push_section(&mut wasm, 1, &ty);

    // Function section (id=3): 2 functions, both using type 0
    let mut funcs = Vec::new();
    push_u32_leb(&mut funcs, 2);
    push_u32_leb(&mut funcs, 0);
    push_u32_leb(&mut funcs, 0);
    push_section(&mut wasm, 3, &funcs);

    // Memory section (id=5): 1 memory with limits flag=1 (has max), min=1, max=1
    let mut mem = Vec::new();
    push_u32_leb(&mut mem, 1);
    mem.push(0x01);
    push_u32_leb(&mut mem, 1);
    push_u32_leb(&mut mem, 1);
    push_section(&mut wasm, 5, &mem);

    // Code section (id=10):
    // Body 0: locals: 3 x i32 -> local 0 = n, local 1 = a (0), local 2 = b (1), local 3 = tmp
    // block $done
    //   loop $lp
    //     local.get 0; i32.eqz; br_if 1 ($done)
    //     local.get 1; local.get 2; i32.add; local.set 3
    //     local.get 2; local.set 1
    //     local.get 3; local.set 2
    //     local.get 0; i32.const 1; i32.sub; local.set 0
    //     br 0 ($lp)
    //   end
    // end
    // i32.const 0; local.get 1; i32.store align=2 offset=0
    // i32.const 0; i32.load align=2 offset=0
    // end
    let mut body0 = Vec::new();
    push_u32_leb(&mut body0, 1); // 1 local declaration group
    push_u32_leb(&mut body0, 3); // 3 locals
    body0.push(0x7F); // i32
    body0.extend_from_slice(&[
        0x41, 0x00, 0x21, 0x01, // i32.const 0; local.set 1 (a = 0)
        0x41, 0x01, 0x21, 0x02, // i32.const 1; local.set 2 (b = 1)
        0x02, 0x40, // block (void)
        0x03, 0x40, // loop (void)
        0x20, 0x00, 0x45, 0x0D, 0x01, // local.get 0; i32.eqz; br_if 1
        0x20, 0x01, 0x20, 0x02, 0x6A, 0x21, 0x03, // tmp = a + b
        0x20, 0x02, 0x21, 0x01, // a = b
        0x20, 0x03, 0x21, 0x02, // b = tmp
        0x20, 0x00, 0x41, 0x01, 0x6B, 0x21, 0x00, // n = n - 1
        0x0C, 0x00, // br 0
        0x0B, // end loop
        0x0B, // end block
        0x41, 0x00, 0x20, 0x01, 0x36, 0x02, 0x00, // mem[0] = a (i32.store)
        0x41, 0x00, 0x28, 0x02, 0x00, // i32.load mem[0]
        0x0B, // end func
    ]);

    // Body 1: 0 locals; local.get 0; i32.load align=2 offset=0; end
    let body1: Vec<u8> = vec![
        0x00, // 0 local groups
        0x20, 0x00, // local.get 0
        0x28, 0x02, 0x00, // i32.load align=2 offset=0
        0x0B, // end func
    ];

    let mut code = Vec::new();
    push_u32_leb(&mut code, 2);
    push_u32_leb(&mut code, body0.len() as u32);
    code.extend_from_slice(&body0);
    push_u32_leb(&mut code, body1.len() as u32);
    code.extend_from_slice(&body1);
    push_section(&mut wasm, 10, &code);

    wasm
}

#[test]
fn full_pipeline_all_11_verified_browser_crates() {
    // =========================================================================
    // 1. Phase 1 (`vurl`): URL host parsing (IPv4 + IPv6) & percent-decoding
    // =========================================================================
    let origin_ip = ipv4_parse(b"127.0.0.1").expect("valid IPv4 origin host");
    assert_eq!(origin_ip, 0x7F00_0001);

    let ipv6_pieces = ipv6_parse(b"2001:db8::e").expect("valid compressed IPv6 host");
    assert_eq!(ipv6_pieces, vec![0x2001, 0x0db8, 0, 0, 0, 0, 0, 14]);
    assert_eq!(ipv6_serialize(&ipv6_pieces), b"2001:db8::e".to_vec());
    let seed_from_ipv6 = ipv6_pieces[7] as usize; // 14

    let raw_script = format!(
        "function makeAdder(k) {{ return (x) => x + k; }}\n\
         const bump = makeAdder(4);\n\
         let acc = 0;\n\
         const items = [2, 3, 5];\n\
         try {{\n\
           for (let i = 0; i < items.length; i++) {{ acc += items[i]; }}\n\
         }} finally {{\n\
           const maybe = null;\n\
           if ((maybe?.missing.prop ?? {seed_from_ipv6}) === {seed_from_ipv6}) {{ acc = bump(acc); }}\n\
         }}\n\
         acc;"
    );
    let encoded_query = percent_encode(raw_script.as_bytes(), EncodeSet::Component);
    assert!(encoded_query.windows(3).any(|w| w == b"%20" || w == b"%0A"));
    let decoded_bytes = percent_decode(&encoded_query);
    let decoded_script = String::from_utf8(decoded_bytes).expect("UTF-8 script roundtrip");
    assert_eq!(decoded_script, raw_script);

    // =========================================================================
    // 2. Step J4b (`vjs_webidl`): USVString sanitization + capability gating
    // =========================================================================
    let idl_arena = JsObjectArena::new();
    // Unpaired high surrogate 0xD800 must convert to U+FFFD and be idempotent.
    let mut dirty_utf16: Vec<u16> = "conduit:".encode_utf16().collect();
    dirty_utf16.push(0xD800);
    let sanitized_usv =
        to_idl_usv_string(&idl_arena, &IdlJsVal::String(dirty_utf16)).expect("USVString");
    assert_eq!(*sanitized_usv.last().unwrap(), 0xFFFD);
    let sanitized_twice =
        to_idl_usv_string(&idl_arena, &IdlJsVal::String(sanitized_usv.clone())).expect("idempotent");
    assert_eq!(sanitized_usv, sanitized_twice);

    let mut cap_table = KernelCapTable::new();
    let realm_main = RealmId(1);
    let realm_other = RealmId(2);
    let origin_local = OriginId(origin_ip);
    let origin_evil = OriginId(0x0A00_0001);

    let console_cap = cap_table
        .allocate(realm_main, origin_local, CapKind::ConsoleSink, PERM_LOG, 1)
        .expect("mint console capability");
    let _other_cap = cap_table
        .allocate(
            realm_other,
            origin_evil,
            CapKind::StorageOrigin,
            PERM_READ | PERM_WRITE,
            1,
        )
        .expect("mint isolated origin capability");

    let mut host_state = HostState::new();
    let log_req = HostRequest::ConsoleLog {
        target_origin: origin_local,
        message_js: IdlJsVal::String(sanitized_usv),
    };
    assert!(dispatch(&cap_table, &idl_arena, &mut host_state, realm_main, console_cap, &log_req).is_ok());
    assert_eq!(host_state.console.len(), 1);

    // Cross-origin attempt with `console_cap` must fail with zero state mutation.
    let before_cross = host_state.clone();
    let cross_req = HostRequest::ConsoleLog {
        target_origin: origin_evil,
        message_js: IdlJsVal::String("forged".encode_utf16().collect()),
    };
    assert_eq!(
        dispatch(&cap_table, &idl_arena, &mut host_state, realm_main, console_cap, &cross_req),
        Err(HostError::CrossRealmViolation)
    );
    assert_eq!(host_state, before_cross);

    // Revoking `console_cap` permanently blocks subsequent use.
    cap_table.revoke(console_cap).expect("revoke handle");
    assert_eq!(
        dispatch(&cap_table, &idl_arena, &mut host_state, realm_main, console_cap, &log_req),
        Err(HostError::RevokedOrInvalidHandle)
    );
    assert_eq!(host_state.console.len(), 1);

    // =========================================================================
    // 3. Step J3 (`vjs_syntax`): Verified lexer + Pratt/RD parser + Early Errors
    // =========================================================================
    match parse_script_str(&decoded_script) {
        SyntaxOutcome::Ok(prog) => {
            assert!(
                check_early_errors(&prog).is_ok(),
                "valid pipeline script must pass Static Semantics: Early Errors"
            );
        }
        other => panic!("expected ParseOutcome::Ok from vjs_syntax, got {other:?}"),
    }
    assert!(matches!(
        parse_script_str("let dup = 1; let dup = 2;"),
        SyntaxOutcome::SyntaxError(_)
    ));

    // =========================================================================
    // 4. Step J4 (`vjs`): Verified ECMAScript interpreter core (`eval_script`)
    // =========================================================================
    let eval_res = eval_script(&decoded_script, 50_000, 256);
    let n_bits = match eval_res {
        RunResult::Done(ScriptCompletion::Normal(Val::Number(num))) => num.0,
        other => panic!("expected Normal(Val::Number(14.0)), got {other:?}"),
    };
    assert_eq!(f64::from_bits(n_bits), 14.0);
    let fib_n = f64::from_bits(n_bits) as i64; // 14

    // =========================================================================
    // 5a. Step J0 (`vjs_spec`): ESMeta-compiled ECMA-262 abstract operations
    // =========================================================================
    let spec_val = SpecVal::Number(SpecNum(n_bits));
    assert!(spec_to_boolean(&spec_val));
    let shifted = number_left_shift(SpecNum(n_bits), SpecNum(2.0f64.to_bits()));
    assert_eq!(f64::from_bits(shifted.0), 56.0);
    match spec_to_int32(&SpecVal::Number(shifted)) {
        AbruptOrNormal::Normal(i32_num) => assert_eq!(f64::from_bits(i32_num.0), 56.0),
        other => panic!("expected Normal(56), got {other:?}"),
    }
    assert!(spec_same_value(
        &SpecVal::Number(shifted),
        &SpecVal::Number(SpecNum(56.0f64.to_bits()))
    ));

    // =========================================================================
    // 5b. Step J1 (`vjs_types`): Burger-Dybvig IEEE-754 Number::toString & BigInt
    // =========================================================================
    let formatted_n = number_to_string(TypesNum(n_bits));
    assert_eq!(String::from_utf16(&formatted_n.units).unwrap(), "14");
    let reparsed_n = string_to_number(&formatted_n);
    assert_eq!(reparsed_n.0, n_bits);
    assert!(is_strictly_equal(
        &TypesPrim::Number(TypesNum(n_bits)),
        &TypesPrim::Number(reparsed_n)
    ));
    let big_u16 = utf8_to_utf16(b"377").expect("UTF-8 -> UTF-16");
    let big_377 = string_to_bigint(&big_u16).expect("StringToBigInt('377')");
    assert_eq!(big_377.limbs, vec![377]);

    // =========================================================================
    // 5c. Step J2 (`vjs_object`): Ordinary & Array exotic heap + §6.1.7.3 freeze
    // =========================================================================
    let mut obj_heap = ObjectHeap::new();
    let rec_obj = obj_heap.alloc_ordinary(None);
    let key_n: PropKey = prop_key_from_ascii(b"n");
    let data_desc = PropertyDescriptor {
        value: Some(ObjVal::NumberBits(n_bits)),
        writable: Some(true),
        get: None,
        set: None,
        enumerable: Some(true),
        configurable: Some(true),
    };
    assert!(ordinary_define_own_property(&mut obj_heap, rec_obj, &key_n, &data_desc));
    object_freeze(&mut obj_heap, rec_obj);
    assert!(object_is_frozen(&obj_heap, rec_obj));
    assert_eq!(
        ordinary_get(&obj_heap, rec_obj, &key_n, &ObjVal::Object(rec_obj)),
        GetOutcome::Value(ObjVal::NumberBits(n_bits))
    );

    let arr_obj = array_create(&mut obj_heap, 0, None);
    let elem0_desc = PropertyDescriptor {
        value: Some(ObjVal::NumberBits(377.0f64.to_bits())),
        writable: Some(true),
        get: None,
        set: None,
        enumerable: Some(true),
        configurable: Some(true),
    };
    assert_eq!(
        array_define_own_property(&mut obj_heap, arr_obj, &PropKey::ArrayIndex(3), &elem0_desc),
        Ok(true)
    );
    assert_eq!(array_length(&obj_heap, arr_obj), 4);
    let len2_desc = PropertyDescriptor {
        value: Some(ObjVal::NumberBits(2.0f64.to_bits())),
        writable: None,
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    assert_eq!(
        array_set_length(&mut obj_heap, arr_obj, &len2_desc),
        Ok(true)
    );
    assert_eq!(array_length(&obj_heap, arr_obj), 2);

    // =========================================================================
    // 5d. Step J5 (`vjs_builtins`): Vest JSON, Warblre RegExp, Map/Set & Date
    // =========================================================================
    let json_doc = JsonValue::Object(vec![
        ("n".encode_utf16().collect(), JsonValue::Int(fib_n)),
        (
            "origin".encode_utf16().collect(),
            JsonValue::Str("127.0.0.1".encode_utf16().collect()),
        ),
    ]);
    let json_wire = json_stringify(&json_doc);
    let json_reparsed = json_parse(&json_wire, 512).expect("JSON roundtrip");
    assert_eq!(json_reparsed, json_doc);

    let pat_u16: Vec<u16> = "^[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+$".encode_utf16().collect();
    let (regex_ast, cap_count) = parse_pattern(&pat_u16, 256).expect("compile regex");
    let host_u16: Vec<u16> = "127.0.0.1".encode_utf16().collect();
    let flags = RegexFlags {
        ignore_case: false,
        multiline: false,
        dot_all: false,
    };
    assert!(matches!(
        exec_match(&regex_ast, flags, &host_u16, 0, cap_count as usize, 2_000),
        MatchOutcome::Matched { .. }
    ));

    let mut js_map = JsMap::new();
    js_map.set(
        JsKey::NumberBits((-0.0f64).to_bits()),
        JsKey::NumberBits(377.0f64.to_bits()),
    );
    assert_eq!(
        js_map.get(&JsKey::NumberBits(0.0f64.to_bits())),
        Some(JsKey::NumberBits(377.0f64.to_bits()))
    );
    let mut js_set = JsSet::new();
    js_set.add(JsKey::Str("verified".encode_utf16().collect()));
    assert_eq!(js_set.size(), 1);

    let day = make_day(2026, 10, 20).expect("valid day");
    let time_ms = make_time(12, 30, 0, 0).expect("valid time");
    let tv = time_clip(make_date(day, time_ms).expect("valid date")).expect("TimeClip valid");
    let iso = to_iso_string(tv).expect("toISOString");
    assert_eq!(parse_iso8601(&iso), Some(tv));

    // =========================================================================
    // 5e. Step J6 (`vjs_gc`): Tricolor Mark-Sweep GC & Promise FIFO Job Queue
    // =========================================================================
    let mut gc_heap = GcHeap::with_realms(&[(16, 4096)]).expect("realm quota");
    let live_child = gc_heap
        .alloc(0, 64, GcPayload::OrdinaryObject { proto_tag: 0, prop_count: 1 }, vec![])
        .unwrap();
    let live_root = gc_heap
        .alloc(0, 64, GcPayload::Closure { bytecode_id: 1, env_len: 1 }, vec![live_child])
        .unwrap();
    let dead_garbage = gc_heap
        .alloc(0, 128, GcPayload::OrdinaryObject { proto_tag: 0, prop_count: 4 }, vec![])
        .unwrap();
    let gc_stats = gc_heap.collect(&[live_root]);
    assert_eq!(gc_stats.surviving_slots, 2);
    assert_eq!(gc_stats.freed_slots, 1);
    assert_eq!(gc_stats.freed_bytes, 128);
    assert!(matches!(gc_heap.slots[dead_garbage], Slot::Free));

    let mut promise_rt = PromiseRuntime::new();
    let root_p = promise_rt.new_promise().unwrap();
    let chained_p = promise_rt
        .then(
            root_p,
            Some(ReactionHandler::AddInt {
                delta: 363,
                trace_id: 1,
            }),
            None,
        )
        .unwrap();
    promise_rt.fulfill_promise(root_p, GcVal::Int(fib_n)).unwrap();
    let drain_out = promise_rt.drain_jobs(32).unwrap();
    assert!(matches!(drain_out, DrainOutcome::Done { steps_executed: 1 }));
    assert_eq!(
        promise_rt.promises[chained_p].state,
        PromiseState::Fulfilled(GcVal::Int(377))
    );

    // =========================================================================
    // 6. Step J7a (`vjs_vm`): Verified JS AST -> Bytecode Compiler + Stack VM
    // =========================================================================
    // Function 0: recursive `fib(k)` (`if k <= 1 { return k; } return fib(k - 1) + fib(k - 2);`)
    let fib_func = VmFunc {
        num_params: 1,
        num_locals: 1,
        body: VmStmt::Seq(
            Box::new(VmStmt::If(
                VmExpr::BinOp(
                    VmBinOp::Le,
                    Box::new(VmExpr::Local(0)),
                    Box::new(VmExpr::Const(1)),
                ),
                Box::new(VmStmt::Return(VmExpr::Local(0))),
                Box::new(VmStmt::Nop),
            )),
            Box::new(VmStmt::Return(VmExpr::BinOp(
                VmBinOp::Add,
                Box::new(VmExpr::Call(
                    0,
                    Box::new(expr_list_from_vec(vec![VmExpr::BinOp(
                        VmBinOp::Sub,
                        Box::new(VmExpr::Local(0)),
                        Box::new(VmExpr::Const(1)),
                    )])),
                )),
                Box::new(VmExpr::Call(
                    0,
                    Box::new(expr_list_from_vec(vec![VmExpr::BinOp(
                        VmBinOp::Sub,
                        Box::new(VmExpr::Local(0)),
                        Box::new(VmExpr::Const(2)),
                    )])),
                )),
            ))),
        ),
    };
    let vm_prog = VmProgram {
        funcs: vec![fib_func],
        entry: 0,
        num_globals: 0,
    };
    let (ast_outcome, vm_outcome) =
        compile_and_run_verified(&vm_prog, &[fib_n], 50_000, 500_000).expect("compile_program");
    assert_eq!(ast_outcome, vm_outcome);
    match vm_outcome {
        ExecProgramOutcome::Done { val, .. } => assert_eq!(val, 377),
        other => panic!("expected Done {{ val: 377, .. }} from vjs_vm, got {other:?}"),
    }

    // =========================================================================
    // 7. Step J7b (`vwasm`): Sandboxed Wasm 1.0 Binary Execution & Containment
    // =========================================================================
    let wasm_bytes = build_fib_and_bounds_wasm_module();
    let (wasm_inst, wasm_out) =
        run_sandboxed_wasm_bytes(&wasm_bytes, 0, &[WasmVal::I32(fib_n as i32)], 100_000)
            .expect("valid Wasm module instantiation");
    assert_eq!(wasm_out, WasmOutcome::Done(vec![WasmVal::I32(377)]));
    assert_eq!(wasm_inst.memory.len(), 65_536);
    assert_eq!(
        i32::from_le_bytes(wasm_inst.memory[0..4].try_into().unwrap()),
        377
    );

    // Out-of-bounds read at byte 65,534 (4-byte i32 load spans 65,534..65,538 > 65,536)
    // must deterministically trap with `OutOfBoundsMemoryAccess` and preserve `memory.len()`.
    let (oob_inst, oob_out) =
        run_sandboxed_wasm_bytes(&wasm_bytes, 1, &[WasmVal::I32(65_534)], 10_000)
            .expect("valid Wasm module instantiation for OOB check");
    assert_eq!(oob_out, WasmOutcome::Trap(WasmTrap::OutOfBoundsMemoryAccess));
    assert_eq!(oob_inst.memory.len(), 65_536);
    assert!(oob_inst.memory.iter().all(|&b| b == 0));
}
