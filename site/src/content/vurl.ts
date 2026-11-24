// Real verbatim Verus code from browser/url/src/percent.rs (whatwg/url@4f461b81)
// plus the three illustrative failure states (counterexample, rlimit timeout, admit bypass).
export type ObligationState = 'verified' | 'failed' | 'timeout' | 'admit';
export type VerusLane = 'spec' | 'exec' | 'proof';

export interface CounterexampleBinding {
  symbol: string;
  sort: string;
  value: string;
}

export interface VerusCodeLine {
  lineNo: number;
  lane: VerusLane;
  text: string;
  obligation?: {
    state: ObligationState;
    summary: string;
    detail: string;
    vcFormula?: string;
    counterexample?: CounterexampleBinding[];
  };
}

export const VURL_VERIFIED_LINES: VerusCodeLine[] = [
  { lineNo: 1, lane: 'spec', text: '// WHATWG URL §1.3, transcribed from whatwg/url@4f461b81' },
  { lineNo: 2, lane: 'spec', text: 'pub open spec fn spec_percent_encode_byte(b: u8) -> Seq<u8> {' },
  { lineNo: 3, lane: 'spec', text: '    seq![0x25u8, upper_hex_digit(b as nat / 16), upper_hex_digit(b as nat % 16)]' },
  { lineNo: 4, lane: 'spec', text: '}' },
  { lineNo: 5, lane: 'exec', text: '' },
  { lineNo: 6, lane: 'exec', text: 'fn upper_hex(n: u8) -> (r: u8)' },
  {
    lineNo: 7,
    lane: 'spec',
    text: '    requires n < 16,',
    obligation: {
      state: 'verified',
      summary: 'Precondition checked at every call site',
      detail: 'Callers must prove n < 16 statically before invoking upper_hex; out-of-range nibbles cannot compile.',
    },
  },
  {
    lineNo: 8,
    lane: 'spec',
    text: '    ensures r == upper_hex_digit(n as nat),',
    obligation: {
      state: 'verified',
      summary: 'UNSAT across all 16 valid inputs in one symbolic Z3 query',
      detail: 'Verus encodes n as an 8-bit symbolic bitvector, assumes n < 16, and asks Z3 to find any n where r != upper_hex_digit(n). Z3 proves those constraints contradict each other.',
      vcFormula:
        'assume: bvult(n, 0x10)\nbody:   r = ite(bvult(n, 0x0a), bvadd(0x30, n), bvsub(bvadd(0x41, n), 0x0a))\nnegate: assert(r != spec_upper_hex_digit(n))   // search for any failing n\nz3:     UNSAT  (0 counterexamples -> proved for every n < 16)',
    },
  },
  { lineNo: 9, lane: 'exec', text: '{ if n < 10 { 0x30 + n } else { 0x41 + n - 10 } }' },
  { lineNo: 10, lane: 'proof', text: '' },
  { lineNo: 11, lane: 'exec', text: 'pub fn percent_encode(input: &[u8], set: EncodeSet) -> (out: Vec<u8>)' },
  {
    lineNo: 12,
    lane: 'spec',
    text: '    ensures out@ == spec_percent_encode(input@, set),',
    obligation: {
      state: 'verified',
      summary: 'Whole-loop refinement against recursive WHATWG specification',
      detail: 'For every byte slice of any length, the output Vec equals the recursive spec function element for element.',
    },
  },
  { lineNo: 13, lane: 'exec', text: '    while i < n' },
  {
    lineNo: 14,
    lane: 'proof',
    text: '        invariant spec_percent_encode(input@, set) == out@ + spec_percent_encode(input@.subrange(i as int, n as int), set),',
    obligation: {
      state: 'verified',
      summary: 'Inductive loop proof over unbounded slices (&[u8] of any length)',
      detail: 'Instead of unrolling the loop, Z3 proves base case (i = 0), single-step preservation (i -> i + 1), and exit (i == n), covering every slice length at once.',
      vcFormula:
        'base (i = 0):    out == []  ==>  spec(input) == [] + spec(input[0..n])    [UNSAT]\nstep (i -> i+1): inv(i) && i < n  ==>  inv(i + 1)                         [UNSAT]\nexit (i == n):   inv(n)  ==>  out == spec(input)  for any slice length n  [UNSAT]',
    },
  },
  {
    lineNo: 15,
    lane: 'proof',
    text: '        decreases n - i,',
    obligation: {
      state: 'verified',
      summary: 'Termination proved (n - i strictly decreases)',
      detail: 'Guarantees the encoder loop terminates for all inputs; infinite-loop denial-of-service is ruled out.',
    },
  },
  { lineNo: 16, lane: 'proof', text: '' },
  { lineNo: 17, lane: 'proof', text: 'pub proof fn lemma_decode_encode_roundtrip(s: Seq<u8>, set: EncodeSet)' },
  { lineNo: 18, lane: 'spec', text: '    requires spec_in_set(set, 0x25),' },
  {
    lineNo: 19,
    lane: 'spec',
    text: '    ensures spec_percent_decode(spec_percent_encode(s, set)) == s,',
    obligation: {
      state: 'verified',
      summary: 'Proved algebraic roundtrip — and its exact boundary condition',
      detail: 'decode(encode(s)) == s holds iff "%" (0x25) is in the encode set. For the six sets omitting "%", vurl also proves decode(encode("%41")) == "A".',
    },
  },
];

export const COUNTEREXAMPLE_LINES: VerusCodeLine[] = [
  { lineNo: 1, lane: 'exec', text: '// ILLUSTRATIVE mutation — not real vurl code (all 11 real crates have 0 errors).' },
  { lineNo: 2, lane: 'exec', text: 'fn hex_val(b: u8) -> (r: u8)' },
  {
    lineNo: 3,
    lane: 'spec',
    text: '    requires is_ascii_hex_digit(b),',
    obligation: {
      state: 'verified',
      summary: 'Input constrained to ASCII 0–9, A–F, a–f',
      detail: 'Precondition holds from caller.',
    },
  },
  {
    lineNo: 4,
    lane: 'spec',
    text: '    ensures r < 15, // 1-char typo: real vurl postcondition is r < 16',
    obligation: {
      state: 'failed',
      summary: 'Postcondition falsified — Z3 solves the negated query (SAT)',
      detail: 'Z3 searches for b satisfying is_ascii_hex_digit(b) && !(r < 15), finds a solution, and hands back the exact breaking byte.',
      vcFormula:
        'assume: is_ascii_hex_digit(b)\nbody:   r = ite(bvule(b, 0x39), bvsub(b, 0x30), bvadd(bvsub(bvand(b, 0xdf), 0x41), 10))\nnegate: assert(!(bvult(r, 15)))   // search for any hex byte with r >= 15\nz3:     SAT  -> counterexample found:',
      counterexample: [
        { symbol: 'b', sort: '(_ BitVec 8)', value: '0x46 ("F")' },
        { symbol: 'r', sort: '(_ BitVec 8)', value: '15  (violates r < 15)' },
      ],
    },
  },
  { lineNo: 5, lane: 'exec', text: "{ if b <= b'9' { b - b'0' } else { (b & 0xdf) - b'A' + 10 } }" },
];

export const TIMEOUT_LINES: VerusCodeLine[] = [
  { lineNo: 1, lane: 'exec', text: '// ILLUSTRATIVE solver budget exhaustion — unfinished is never treated as proved.' },
  { lineNo: 2, lane: 'exec', text: '#[verifier::rlimit(2)]' },
  { lineNo: 3, lane: 'proof', text: 'proof fn lemma_complex_quantifier_chain(buf: Seq<u8>)' },
  {
    lineNo: 4,
    lane: 'spec',
    text: '    ensures forall|i: int, j: int| 0 <= i < j < buf.len() ==> spec_order_ok(buf, i, j),',
    obligation: {
      state: 'timeout',
      summary: 'RLIMIT EXCEEDED — Z3 exhausted quantifier budget before UNSAT or SAT',
      detail: 'CI fails the build immediately. Fix by isolating the lemma with #[verifier::spinoff_prover] or adding explicit quantifier triggers.',
    },
  },
  { lineNo: 5, lane: 'proof', text: '{ /* nonlinear arithmetic or broad trigger loop exhausts rlimit */ }' },
];

export const ADMIT_LINES: VerusCodeLine[] = [
  { lineNo: 1, lane: 'exec', text: '// ILLUSTRATIVE escape hatch — counted as trusted, rejected by ratchet CI.' },
  { lineNo: 2, lane: 'exec', text: 'fn hex_val(b: u8) -> (r: u8)' },
  { lineNo: 3, lane: 'spec', text: '    requires is_ascii_hex_digit(b),' },
  { lineNo: 4, lane: 'spec', text: '    ensures r < 16,' },
  {
    lineNo: 5,
    lane: 'proof',
    text: '{ proof { admit(); } if b <= b\'9\' { b - b\'0\' } else { (b & 0xdf) - b\'A\' + 10 } }',
    obligation: {
      state: 'admit',
      summary: 'ASSUMED via admit() — solver bypassed and billed to Trusted Items',
      detail: 'browser/scripts/ratchet.py scans every crate for assume, admit, external_body, external, assume_specification, and unsafe. All 11 verified crates enforce 0.',
    },
  },
];

export interface VurlModule {
  id: string;
  summary: string;
  exec: string[];
  theorems: string[];
  gaps: string;
}

export const VURL_MODULES: VurlModule[] = [
  {
    id: 'percent',
    summary: 'Encode, decode & 6 algebraic theorems',
    exec: ['percent_encode', 'percent_decode', 'in_set', 'is_hex', 'hex_val', 'upper_hex'],
    theorems: [
      'lemma_form_urlencoded_note',
      'lemma_query_not_superset_of_fragment',
      'lemma_set_chain',
      'lemma_decode_encode_roundtrip',
      'lemma_sets_containing_percent',
      'lemma_roundtrip_fails_without_percent',
    ],
    gaps: 'spaceAsPlus form encoding and non-UTF-8 character sets are out of scope.',
  },
  {
    id: 'ipv4',
    summary: 'Address parser, numeric radix & host check',
    exec: ['split_dots', 'ipv4_number', 'ipv4_parse', 'ends_in_a_number'],
    theorems: ['Checker step 5 equivalence ("0x"/"0X" followed by ASCII hex digits)'],
    gaps: 'Non-fatal WHATWG validation error logging is not modeled; return values are proved.',
  },
  {
    id: 'ipv6',
    summary: 'Parser, canonical serializer & zero-run compression',
    exec: ['ipv6_parse', 'compressed_index', 'ipv6_serialize'],
    theorems: ['Serialized hex pieces use canonical shortest form (no leading zeros)'],
    gaps: 'Serialize → parse roundtrip is tested on 200,000 random addresses, not yet proved.',
  },
];

export interface ProofDagNode {
  id: string;
  label: string;
  subsystem: string;
  layer: 0 | 1;
  row: number;
}

export interface ProofDagEdge {
  from: string;
  to: string;
}

// Clean 2-layer bipartite topological layout (Specs & Helpers -> Implementations & Theorems).
// Every edge flows cleanly left-to-right with zero layer-skipping collisions or node overlap.
export const VURL_DAG_NODES: ProofDagNode[] = [
  // Layer 0: Specifications & verified primitives (left column)
  { id: 'spec_encode', label: 'spec_percent_encode', subsystem: 'percent · spec', layer: 0, row: 0 },
  { id: 'spec_decode', label: 'spec_percent_decode', subsystem: 'percent · spec', layer: 0, row: 1 },
  { id: 'thm_chain', label: 'lemma_set_chain', subsystem: 'percent · theorem', layer: 0, row: 2 },
  { id: 'ipv4_number', label: 'ipv4_number', subsystem: 'ipv4 · exec', layer: 0, row: 3.4 },
  { id: 'ends_number', label: 'ends_in_a_number', subsystem: 'ipv4 · exec', layer: 0, row: 4.4 },
  { id: 'compressed', label: 'compressed_index', subsystem: 'ipv6 · exec', layer: 0, row: 5.7 },

  // Layer 1: Proved implementations & algebraic theorems (right column)
  { id: 'exec_encode', label: 'percent_encode', subsystem: 'percent · exec', layer: 1, row: 0 },
  { id: 'exec_decode', label: 'percent_decode', subsystem: 'percent · exec', layer: 1, row: 1 },
  { id: 'thm_roundtrip', label: 'decode_encode_roundtrip', subsystem: 'percent · theorem', layer: 1, row: 2 },
  { id: 'thm_counter', label: 'roundtrip_fails_w/o_%', subsystem: 'percent · theorem', layer: 1, row: 3 },
  { id: 'ipv4_parse', label: 'ipv4_parse', subsystem: 'ipv4 · exec', layer: 1, row: 4 },
  { id: 'ipv6_parse', label: 'ipv6_parse', subsystem: 'ipv6 · exec', layer: 1, row: 5.2 },
  { id: 'ipv6_serialize', label: 'ipv6_serialize', subsystem: 'ipv6 · exec', layer: 1, row: 6.2 },
];

export const VURL_DAG_EDGES: ProofDagEdge[] = [
  { from: 'spec_encode', to: 'exec_encode' },
  { from: 'spec_decode', to: 'exec_decode' },
  { from: 'spec_encode', to: 'thm_roundtrip' },
  { from: 'spec_decode', to: 'thm_roundtrip' },
  { from: 'spec_encode', to: 'thm_counter' },
  { from: 'spec_decode', to: 'thm_counter' },
  { from: 'ipv4_number', to: 'ipv4_parse' },
  { from: 'ends_number', to: 'ipv4_parse' },
  { from: 'compressed', to: 'ipv6_parse' },
  { from: 'compressed', to: 'ipv6_serialize' },
];
