// docs/verified-browser-engine.md §3.3 — the vjs work order.
// Status is honest: as of the current ratchet, only vurl exists; every J-step is design.
export interface VjsStep {
  step: string;
  scope: string;
  exit: string;
}

export const VJS_STEPS: VjsStep[] = [
  { step: 'J0', scope: 'ESMeta → Verus spec generator; spec-as-exec differential harness vs test262', exit: 'Generated spec type-checks; per-section pass counts reported' },
  { step: 'J1', scope: 'Types & abstract ops: UTF-16 strings, Number (shortest round-trip toString), BigInt, ToPrimitive/ToNumber/ToString, equality', exit: 'exec == spec; test262 built-ins/Number + language/types subsets' },
  { step: 'J2', scope: 'Object model: property descriptors, ordinary internal methods, §6.1.7.3 invariants, Array exotic', exit: 'Invariant proofs; test262 built-ins/Object subset' },
  { step: 'J3', scope: 'Lexer, parser, early errors', exit: 'Proved against the grammar; test262 language/ parse tests' },
  { step: 'J4', scope: 'Interpreter core: environments, completions, expressions, statements, functions, closures, exceptions. Interim unverified safe mark-sweep collector under a per-realm heap quota', exit: 'Step refinement proved; real scripts run end to end; quota enforced' },
  { step: 'J4b', scope: 'Host boundary: Web IDL ToJS/ToIDL as specs; every host capability a kernel-issued handle; zero ambient authority', exit: 'Conversion proofs for top-N crawl-corpus sites; audit shows zero non-handle host accesses' },
  { step: 'J5', scope: 'Built-ins by real-site usage: Array, String, JSON (Vest roundtrip), Math, Map/Set, RegExp (Warblre port), Date', exit: 'Per-built-in proofs; test262 pass rate per directory' },
  { step: 'J6', scope: 'Promises, job queue, async/await, generators; replaces the interim collector with the proved GC; Proxy/Reflect', exit: 'Liveness under fuel; GC-preservation theorem' },
  { step: 'J7', scope: 'Bytecode compiler + interpreter with simulation proof; verified Wasm interpreter', exit: 'Compiler-correctness theorem; speed measured on a public benchmark set' },
];

export const FUEL_THEOREM = `for every program p and fuel n, vjs::run(p, n) returns exactly one of:

  Done(v)         with v == spec_eval(p, n)
  OutOfFuel       only if the spec also needs more than n steps
  Unsupported(f)  an explicit refusal — never a wrong answer

the ratchet shrinks the Unsupported set; a section is either
proved or reported unsupported, never silently approximated.`;