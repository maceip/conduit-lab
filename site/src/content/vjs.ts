// J0–J7 verified JavaScript & WebAssembly work order (docs/verified-browser-engine.md §3.3).
// Live status, verified function counts, test counts, and conformance pass rates
// are joined exclusively from browser/ratchet.json at runtime.
export interface VjsStep {
  step: string;
  short: string;
  scope: string;
  exit: string;
}

export const VJS_STEPS: VjsStep[] = [
  {
    step: 'J0',
    short: 'ECMA-262 spec compiler',
    scope: 'Compiles ESMeta <emu-alg> clauses directly into Verus spec functions and differential-tests them against tc39/test262.',
    exit: 'Generated specifications type-check cleanly; exec == spec proved across all generated steps.',
  },
  {
    step: 'J1',
    short: 'Primitive types & numeric conversions',
    scope: 'UTF-16 strings, IEEE-754 JsNumber (Burger-Dybvig shortest round-trip toString), JsBigInt, ToPrimitive, ToInt32/ToUint32, and equality.',
    exit: 'Exact exec == spec refinement backed by test262 Number, String, and language/types suites.',
  },
  {
    step: 'J2',
    short: 'Arena heap & object invariants',
    scope: 'Safe-Rust indexed arena heap, property descriptors, ordinary internal methods, and Array exotic length semantics.',
    exit: 'Heap well-formedness and ECMA-262 §6.1.7.3 Essential Internal Method Invariants proved.',
  },
  {
    step: 'J3',
    short: 'Lexer, Pratt parser & early errors',
    scope: 'UTF-8/UTF-16 lexer with ASI and Unicode space handling, Pratt/recursive-descent parser, and static Early Errors.',
    exit: 'Total panic-free lexing and parsing proved with explicit termination measures and AST well-formedness.',
  },
  {
    step: 'J4',
    short: 'ECMAScript interpreter core',
    scope: 'Lexical environments, closures, completion records, control flow, exceptions, and per-realm heap quotas.',
    exit: 'End-to-end step refinement, fuel exactness, and cross-realm isolation proved.',
  },
  {
    step: 'J4b',
    short: 'Web IDL capability boundary',
    scope: 'WHATWG Web IDL ToJS/ToIDL conversions and generational KernelCapTable gating every host call with zero ambient authority.',
    exit: 'USVString idempotence, no-use-after-revoke, and cross-origin non-interference proved.',
  },
  {
    step: 'J5',
    short: 'Core standard built-ins',
    scope: 'Vest-style JSON parser/serializer, terminating Warblre RegExp engine, Date (§21.4), Math, Array, String, Map, and Set.',
    exit: 'JSON roundtrip/prefix security and terminating RegExp matcher proved across test262 built-ins.',
  },
  {
    step: 'J6',
    short: 'Proved tricolor GC, async & Proxy',
    scope: 'Tricolor mark-sweep garbage collector, Proxy/Reflect invariant enforcement, Promise job queue, and Generators.',
    exit: 'Reachable-graph preservation, Proxy §6.1.7.3 compliance, and FIFO job-queue liveness proved.',
  },
  {
    step: 'J7',
    short: 'Bytecode compiler, VM & Wasm 1.0 sandbox',
    scope: 'Verified bytecode compiler and stack VM with frame recycling (vjs_vm) plus sandboxed WebAssembly 1.0 interpreter (vwasm).',
    exit: 'CompCert-style simulation proof (VM == AST) and Wasm linear-memory containment proved.',
  },
];

export const FUEL_THEOREM = `For every program p and fuel budget n, vjs::run(p, n) returns exactly one of:

  Done(v)          with v == spec_eval(p, n)
  OutOfFuel        only when the specification also requires > n steps
  Unsupported(f)   an explicit refusal — never a silent wrong answer

The ratchet shrinks Unsupported(f) over time; every clause is either
machine-proved or explicitly refused, never silently approximated.`;
