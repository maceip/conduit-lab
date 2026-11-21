import type { VerusEditorLine } from '@maceip/ix-workbench-primitives';
import type { ProofObligationNode, ProofObligationEdge } from '@maceip/ix-workbench-primitives';

// Pane 01 — real code from browser/url/src/percent.rs (whatwg/url@4f461b81).
// Excerpts are verbatim; line breaks inside long expressions are the only edit.
export const VURL_EDITOR_LINES: VerusEditorLine[] = [
  { text: '// WHATWG URL §1.3, transcribed from whatwg/url@4f461b81 (2026-11-19)', mode: 'spec' },
  { text: '/// "To percent-encode a byte byte, return a string consisting of U+0025 (%),', mode: 'spec' },
  { text: '///  followed by two ASCII upper hex digits representing byte."', mode: 'spec' },
  { text: 'pub open spec fn spec_percent_encode_byte(b: u8) -> Seq<u8> {', mode: 'spec' },
  { text: '    seq![0x25u8, upper_hex_digit(b as nat / 16), upper_hex_digit(b as nat % 16)]', mode: 'spec' },
  { text: '}', mode: 'spec' },
  { text: '', mode: 'exec' },
  { text: 'fn upper_hex(n: u8) -> (r: u8)', mode: 'exec' },
  {
    text: '    requires n < 16,',
    mode: 'exec',
    obligation: { state: 'verified', message: 'precondition: the caller must prove n < 16' },
  },
  {
    text: '    ensures r == upper_hex_digit(n as nat),',
    mode: 'exec',
    obligation: {
      state: 'verified',
      message: 'exec == spec for every n < 16 — one SMT query covers all inputs, not a sample',
    },
  },
  { text: '{ if n < 10 { 0x30 + n } else { 0x41 + n - 10 } }', mode: 'exec' },
  { text: '', mode: 'proof' },
  { text: 'pub fn percent_encode(input: &[u8], set: EncodeSet) -> (out: Vec<u8>)', mode: 'proof' },
  {
    text: '    ensures out@ == spec_percent_encode(input@, set),',
    mode: 'proof',
    obligation: { state: 'verified', message: 'the whole loop refines the recursive spec function' },
  },
  { text: '    while i < n', mode: 'proof' },
  { text: '        invariant spec_percent_encode(input@, set) ==', mode: 'proof' },
  {
    text: '            out@ + spec_percent_encode(input@.subrange(i as int, n as int), set),',
    mode: 'proof',
    obligation: {
      state: 'verified',
      message: 'remaining-computation invariant: what is done + what is left == the spec',
    },
  },
  {
    text: '        decreases n - i,',
    mode: 'proof',
    obligation: { state: 'verified', message: 'termination: n - i shrinks on every iteration — hangs are DoS' },
  },
  { text: '', mode: 'proof' },
  { text: 'pub proof fn lemma_decode_encode_roundtrip(s: Seq<u8>, set: EncodeSet)', mode: 'proof' },
  { text: '    requires spec_in_set(set, 0x25),', mode: 'proof' },
  {
    text: '    ensures spec_percent_decode(spec_percent_encode(s, set)) == s,',
    mode: 'proof',
    obligation: {
      state: 'verified',
      message: 'decode ∘ encode = id — but only when "%" itself is in the encode set',
    },
  },
];

// Pane 01 — "how it breaks". The failed obligation below is ILLUSTRATIVE (a one-character
// typo in a real vurl postcondition); vurl itself has 0 failed obligations. The timeout
// and admit rows show the other two ways a proof can fail to be a proof.
export const BREAK_EDITOR_LINES: VerusEditorLine[] = [
  { text: '// ILLUSTRATIVE failure — not vurl code. The real crate: 0 failed obligations.', mode: 'exec' },
  { text: 'fn hex_val(b: u8) -> (r: u8)', mode: 'exec' },
  { text: '    requires is_ascii_hex_digit(b),', mode: 'exec' },
  {
    text: '    ensures r < 15,   // typo: the real postcondition is r < 16',
    mode: 'exec',
    obligation: {
      state: 'failed',
      message: 'postcondition violated — Z3 returns a concrete input that breaks it',
      counterexample: [
        { symbol: 'b', sort: '(_ BitVec 8)', pre: '0x46 ("F")', post: '0x46' },
        { symbol: 'r', sort: '(_ BitVec 8)', pre: '—', post: '15  ⊭  r < 15' },
      ],
    },
  },
  { text: '{ /* same body as the real hex_val */ }', mode: 'exec' },
  { text: '', mode: 'exec' },
  { text: '// The other two ways a "proof" can fail to be one:', mode: 'exec' },
  {
    text: '#[verus::rlimit(2)]   // solver budget exhausted mid-query',
    mode: 'exec',
    obligation: {
      state: 'timeout',
      message: 'rlimit exceeded: Z3 gave up. Unfinished is NOT passed — CI treats it as a failure',
    },
  },
  {
    text: 'proof { admit() }     // trusted escape hatch, written by a human',
    mode: 'exec',
    obligation: {
      state: 'admit',
      message: 'admit / assume / external_body: the ratchet counts every one as trusted, never as verified',
    },
  },
];

// Pane 03 — the vurl obligation graph. Names are the real functions/lemmas in
// browser/url/src/{percent,ipv4,ipv6}.rs; states come from browser/ratchet.json at runtime.
export const VURL_DAG_NODES: Omit<ProofObligationNode, 'state'>[] = [
  { id: 'spec_encode', label: 'spec_percent_encode', subsystem: 'percent · spec' },
  { id: 'spec_decode', label: 'spec_percent_decode', subsystem: 'percent · spec' },
  { id: 'exec_encode', label: 'percent_encode', subsystem: 'percent · exec' },
  { id: 'exec_decode', label: 'percent_decode', subsystem: 'percent · exec' },
  { id: 'thm_chain', label: 'lemma_set_chain', subsystem: 'percent · theorem' },
  { id: 'thm_roundtrip', label: 'decode_encode_roundtrip', subsystem: 'percent · theorem' },
  { id: 'thm_counter', label: 'roundtrip_fails_w/o %', subsystem: 'percent · theorem' },
  { id: 'ipv4_number', label: 'ipv4_number', subsystem: 'ipv4 · exec' },
  { id: 'ipv4_parse', label: 'ipv4_parse', subsystem: 'ipv4 · exec' },
  { id: 'ends_number', label: 'ends_in_a_number', subsystem: 'ipv4 · exec' },
  { id: 'compressed', label: 'compressed_index', subsystem: 'ipv6 · exec' },
  { id: 'ipv6_parse', label: 'ipv6_parse', subsystem: 'ipv6 · exec' },
  { id: 'ipv6_serialize', label: 'ipv6_serialize', subsystem: 'ipv6 · exec' },
];

export const VURL_DAG_EDGES: ProofObligationEdge[] = [
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