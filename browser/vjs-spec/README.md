# `vjs_spec` (J0): ECMA-262 `<emu-alg>`-to-Verus Compiler & Differential Test262 Harness

Part of `vjs` ([`docs/verified-browser-engine.md`](../../docs/verified-browser-engine.md) §3.3).

## Overview

`vjs_spec` implements Step **J0** of the verified ECMAScript engine:

1. **Untrusted Spec-to-Verus Compiler (`browser/scripts/esmeta_to_verus.py`)**:
   - Parses real upstream `tc39/ecma262` `<emu-clause>` signatures and hierarchical `<emu-alg>` step trees (`1.`, `a.`, `i.`) from `spec_inputs/ecma262_clauses.html` (pinned to `tc39/ecma262@74c33d406ec1763ca9ee5ad9165571661649d6e6`).
   - Lowers prose steps (`If ... , then` / `Else if` / `Else`, `Let _x_ be ...`, `set _x_ to ...`, `Assert: ...`, `Return ...`, `throw a *TypeError* exception`, `? Op(...)` / `! Op(...)` completion shorthands, `_int_ modulo 2^_bitWidth_`, IEEE-754 number/type predicates, and two's-complement bitwise/shift steps) into an explicit ESMeta/IRES-style typed AST + basic-block Control-Flow Graph (`IRCFG`) with SSA $\phi$-lifting and mutation analysis.
   - Synthesizes termination ranking functions (`decreases`) for recursive ECMA-262 operations (`ToNumber`, `IsLooselyEqual`) and emits `src/generated.rs` in topological call-graph order with **every ECMA-262 step interleaved right above its Verus `spec fn` and `exec fn` translation** (Warblre style).
2. **Zero Trusted Escape Hatches (`src/runtime.rs`, `src/generated.rs`, `src/lemmas.rs`)**:
   - `#![forbid(unsafe_code)]`, `assume: 0`, `admit: 0`, `external_body: 0`, `external: 0`, `assume_specification: 0`, `unsafe: 0`.
   - Exact IEEE-754 binary64 bit-level `JsNumber(u64)`, arbitrary-precision `JsBigInt` (`Vec<u32>` limbs), exact `truncate(ℝ(x))`, Euclidean `modulo 2^bitWidth`, `𝔽(k)` roundtrip theorem, and exact rational BigNat round-to-nearest-even `StringToNumber`.
   - Machine-checked algebraic metatheorems (`src/lemmas.rs` & `src/generated.rs`):
     - `SameType`, `SameValue`, and `SameValueZero` equivalence relations + §7.2.10 signed-zero coarsening note;
     - `IsStrictlyEqual` symmetry, transitivity, reflexivity iff non-`NaN`, and off-`NaN` agreement with `SameValueZero`;
     - Unconditional symmetry of `IsLooselyEqual` (`==`) across all ECMAScript language values + non-transitivity witness;
     - ECMA-262 §7.1.7 `<emu-note>`: `ToFixedSizeInteger` idempotence and invariance under `~signed~`/`~unsigned~` inversion across `1..=32`, plus idempotence, cross-idempotence, and non-`-0_𝔽` guarantees for `ToInt32`, `ToUint32`, and `ToUint16`;
     - `Number::bitwiseNOT` involution (`~~x == !ToInt32(x)`), `NumberBitwiseOp` commutativity, XOR self-annihilation, and De Morgan's law (`~(x & y) == (~x) | (~y)`).
3. **Spec-as-Exec Differential Test262 & V8 Oracle Harness (`tests/differential_test262.rs`)**:
   - Executes all 25 compiled Verus `exec` functions against real pinned `tc39/test262` test cases in `browser/test262/` and against live Node.js V8 across thousands of IEEE-754 / BigInt / String / Symbol / Object edge cases, writing measured per-clause pass counts to `report.json`.
