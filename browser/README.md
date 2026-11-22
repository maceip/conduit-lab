# Verified Browser Workspace (`browser/`)

Architecture & specification roadmap: [../docs/verified-browser-engine.md](../docs/verified-browser-engine.md) · CVE coverage audit: [../docs/vjs-plan-review.md](../docs/vjs-plan-review.md).

Every crate in this Cargo workspace enforces `#![forbid(unsafe_code)]`, has **zero** trusted escape hatches (Verus `--no-cheating` on every crate, a dependency-graph check, and a marker count over the files rustc actually compiled — see [`scripts/ratchet.py`](scripts/ratchet.py); what remains trusted is Verus, vstd, Z3, rustc, and the specs themselves), proves termination (`decreases` on all loops and recursive functions), and carries zero ambient host authority (`std::fs`, `std::net`, `std::process`, `std::env`, `std::os`) in `src/`. Exact verification counts, test counts, and timings are generated from live runs into [`ratchet.json`](ratchet.json) and [`../data/stats.json`](../data/stats.json).

---

## Verified Crates (11 Crates: Phase 1 `vurl` + `vjs` Track `J0`–`J7`)

| Step | Crate (`Path`) | Upstream Spec / Test Corpus | Proved Properties (`exec == spec` + Invariants) | Explicit Scope Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| **Phase 1** | `vurl` (`url/`) | `whatwg/url@4f461b81`, WPT `urltestdata.json` (`url/tests/data/PROVENANCE`) | Percent-encode/decode + 8 encode sets (roundtrip iff `%` in set), IPv4 host parser & `ends_in_a_number`, IPv6 parser (incl. IPv4-in-IPv6 & `::` compression) & shortest-hex serializer | Validation error reporting, opaque/domain hosts, IDNA, full URL state machine, and IPv6 serialize→parse roundtrip proof (tested on 200k random inputs) not yet modeled |
| **J0** | `vjs_spec` (`vjs-spec/`, `scripts/esmeta_to_verus.py`) | `tc39/ecma262@74c33d40` `<emu-alg>`, `tc39/test262@2a1ade30` (`test262/PROVENANCE`) | Untrusted `<emu-alg>`→Verus compiler emitting interleaved clause comments + machine-checked `spec fn` / `exec fn` across 25 ECMA-262 clauses (135 spec steps); byte-exact `--check` + V8 differential harness | Covers 25 numeric/conversion/comparison abstract-operation clauses; compiler itself is untrusted and verified per output via Verus + `test262`/V8 |
| **J1** | `vjs_types` (`vjs-types/`) | ECMA-262 §6.1 / §7.1 / §7.2, `tc39/test262@2a1ade30` (`built-ins/Number`, `String`, `language/types`) | Surrogate-aware UTF-16 (`CodePointAt`, `TrimString`, WTF-8), bit-exact IEEE-754 `JsNumber` + Burger-Dybvig shortest round-trip `Number::toString` + `BigNat` RNE `StringToNumber`, `ToInt32`/`ToUint32` modulo-$2^{32}$ theorems, canonical `JsBigInt`, `ToPrimitive`, `SameValue`/`SameValueZero`/`IsStrictlyEqual`/`IsLooselyEqual` | `Symbol` registry and locale-sensitive collations outside §6.1/§7.1/§7.2 not modeled |
| **J2** | `vjs_object` (`vjs-object/`) | ECMA-262 §6.1.7 / §6.2.6 / §7.3 / §10.1 / §10.4.2, `tc39/test262@2a1ade30` (`built-ins/Object`, `Array/length`) | Arena `Heap::wf` (acyclic `proto_rank` prototype chains), §6.2.6 `ValidateAndApplyPropertyDescriptor`, all §10.1 ordinary internal methods (`OwnPropertyKeys` integer-index→string→symbol order), `freeze`/`seal`, §10.4.2 Array exotic `length`, and all §6.1.7.3 Essential Internal Method Invariants | `TypedArray` and `arguments` exotic objects remain outside `vjs_object` (`Proxy` is proved in `vjs_gc`) |
| **J3** | `vjs_syntax` (`vjs-syntax/`) | ECMA-262 §11–§15, `tc39/test262@2a1ade30` (`language/` positive & `negative: phase: parse`) | Total panic-free UTF-8/UTF-16 lexer with ASI & full §12.2 `<USP>` whitespace, Pratt + recursive-descent AST parser (`Program::wf` + `grammar_wf`), Static Semantics: Early Errors (`LexicallyDeclaredNames`, `AssignmentTargetType`, strict mode, template escapes, Annex B.3.2 labeled functions) | Unimplemented syntax constructs return explicit `ParseOutcome::Unsupported(...)`, never silent misparses |
| **J4** | `vjs` (`vjs/`) | ECMA-262 §6.2.4 / §9.1 / §13–§15, `tc39/test262@2a1ade30` (`language/expressions`, `statements`, `exceptions`, `function-code`, `block-scope`) | End-to-end refinement & fuel-exactness theorems on `run`, `run_with_quota`, `eval_script`, `eval_script_state`, and `eval_script_parsed` (`Done` / `OutOfFuel` with `fuel == 0` / explicit `Unsupported`); `EnvArena` (`var`/`let`/`const`/TDZ + free-slot reuse); closures; `try`/`catch`/`finally` overrides; `OptChain`; `ArraySetLength`; prototype/live `for..in`; joint env+object Mark-Sweep GC under `realm_heap_quota` & `RealmId` isolation (`theorem_cross_realm_isolation`) | Features outside the proved interpreter core return explicit `RunResult::Unsupported(feature)` |
| **J4b** | `vjs_webidl` (`vjs-webidl/`) | `whatwg/webidl@54a5f2de`, `web-platform-tests/wpt@e8ca1455` (`vjs-webidl/tests/data/PROVENANCE`) | Web IDL §3.2 `ToIDL`/`ToJS` across `any`, `boolean`, all 8 integer types (`Standard`, `[EnforceRange]`, `[Clamp]` ties-to-even), `DOMString`, `ByteString`, `USVString` (idempotent, zero lone surrogates), `nullable`, `sequence`, `record`, dictionaries; generational `KernelCapTable` + `dispatch` proving no-use-after-revoke, ABA non-revivability, cross-realm/cross-origin non-interference across 6 `HostState` partitions, and per-node DOM confinement | Models typed Web IDL conversions and capability-gated host dispatch; full browser kernel IPC process manager remains a roadmap component |
| **J5** | `vjs_builtins` (`vjs-builtins/`) | ECMA-262 §21.3 / §21.4 / §22.1 / §22.2 / §23.1 / §24.1–2 / §25.5, `tc39/test262@2a1ade30` (8 `built-ins/*` suites) | Vest-style RFC 8259 / §25.5 `JSON.parse` & ES2019 `JSON.stringify` roundtrip + prefix non-malleability; Warblre-style terminating `RegExp` matcher (`\d/\w/\s` Unicode escapes + §22.2.2.5.1 empty-match progress guard); §21.4 `Date` calendar equations, `TimeClip`, and ISO-8601 roundtrip; `Math`, `Array`, `String`, and insertion-order `JsMap`/`JsSet` (`SameValueZero`) | Backreferences and lookbehind assertions in `RegExp` and locale time-zone tables in `Date` are not yet modeled |
| **J6** | `vjs_gc` (`vjs-gc/`) | ECMA-262 §6.1.7.3 / §9.5 / §10.5 / §27.2 / §27.5 / §27.7 / §28.1, `tc39/test262@2a1ade30` (`Promise`, `Proxy`, `Reflect`, `Generator*`) | Iterative tricolor Mark-Sweep GC (`spec_reachable` live-subgraph preservation, `!spec_reachable` slot/byte reclamation, per-realm byte/object quotas); `Proxy`/`Reflect` §6.1.7.3 post-trap invariant enforcement against arbitrary handler outputs + revocation; `Promise` settle-once monotonicity + FIFO microtask `drain_jobs` liveness under fuel; `Generator`/Async state machines | Standalone proved runtime subsystems (connected end-to-end in `vjs/tests/full_pipeline_j0_j7.rs`) |
| **J7** | `vjs_vm` (`vjs-vm/`) | CompCert/CakeML simulation model + 6 public benchmark kernels (`benchmarks.json`) | Verified AST evaluator, bytecode compiler, stack VM (`free_frames` pooling), and machine-checked simulation theorem `theorem_compile_program_correct` (`spec_run_vm(spec_compile_program(p)) == spec_eval_program(p)`) + `compile_and_run_verified` | Covers the structured integer/call/heap-array JS kernel subset benchmarked in `benchmarks.json` |
| **J7** | `vwasm` (`vwasm/`) | Wasm 1.0 Core Spec, `WebAssembly/spec@977f9701` (23 `.wast` suites, `vwasm/tests/data/PROVENANCE`) | `\0asm` v1 & LEB128 bounds/prefix/roundtrip proofs, `wasm_step == spec_wasm_step`, `wasm_invoke == spec_wasm_invoke` (`decreases fuel`), `i32`/`i64` ops (`lemma_div_rem_trap_characterization`), structured control flow, linear memory, and Sandbox Containment Theorems (`lemma_mem_access_oob_traps_cleanly`, `theorem_wasm_invoke_sandbox_containment`, `run_sandboxed_wasm_bytes`) | Implements Wasm 1.0 integer, control-flow, table/call_indirect, global, and linear-memory ops; `f32`/`f64` floating-point instructions return explicit `Unsupported` (54 cases across mixed `.wast` files, 0 failures) |

---

## Cross-Crate End-to-End Integration Test

[`vjs/tests/full_pipeline_j0_j7.rs`](vjs/tests/full_pipeline_j0_j7.rs) links all 11 crates via `[dev-dependencies]` (keeping `[dependencies]` in every crate restricted to `vstd` so per-crate `cargo-verus` verification remains isolated and fast) and executes one continuous in-process pipeline:
`vurl` IPv4/IPv6 + percent-decode → `vjs_webidl` `USVString` sanitization & `KernelCapTable` capability gating → `vjs_syntax` parse + early-error check → `vjs` script evaluation → `vjs_spec` / `vjs_types` / `vjs_object` / `vjs_builtins` / `vjs_gc` operations → `vjs_vm` verified bytecode compilation & execution → `vwasm` sandboxed Wasm 1.0 execution & OOB containment trap check.

---

## Running Verification, Conformance Suites & the Ratchet

```bash
source ~/workspaces/verus-stack/env.zsh
./scripts/use-local-verus.sh                                           # point vstd at local VERUS_SOURCE

# Verify any individual crate with Verus + Z3
"$VERUS_RELEASE/cargo-verus" verify -p vurl --fwd-verus-args-to roots -- --triggers-mode silent --no-cheating
"$VERUS_RELEASE/cargo-verus" verify -p vjs --fwd-verus-args-to roots -- --triggers-mode silent --no-cheating

# Run crate conformance & differential suites (plus cross-crate E2E pipeline)
cargo test -p vjs --test full_pipeline_j0_j7
cargo test --workspace --exclude vjs_vm
cargo test -p vjs_vm --release                                         # writes vjs-vm/benchmarks.json

# Run ESMeta specgen checks + re-verify & test all 11 crates -> writes ratchet.json
python3 scripts/ratchet.py
python3 ../scripts/collect_stats.py                                    # the same, plus data/stats.json, which must embed it

# What CI runs (.github/workflows/ratchet.yml); none of these write to the tree
python3 scripts/ratchet.py --quick                                     # no Verus: report is current and consistent
python3 scripts/ratchet.py --check                                     # re-verify + re-test, compare with ratchet.json
python3 scripts/test_ratchet.py                                        # replay known ways to fool the ratchet
```
