# A browser engine we can formally verify over time

Status: design proposal. Phase 1 started in `browser/` (URL parser). Written 2026-11-20; JS engine plan added 2026-11-20; graphics-stack, XML, host-binding and usability revisions added 2026-11-20 after the CVE coverage review (`docs/vjs-plan-review.md`).

The goal is a browser that is usable on real sites from the first release, and whose
trusted part shrinks release by release as components are replaced by verified ones.
It is modeled on what worked in Verdict (verified X.509 validation in Verus) and is
built around the tools already in this workspace: Verus + Z3, VeriStruct, SkySynth,
Lean 4 / Vero, Nanvix, and the conduit-lab collector and bridge.

---

## 1. What Verdict teaches

Sources: the Verdict repository (`secure-foundations/verdict` at `9bc18bc`, 2025-11-18),
read directly, and the USENIX Security 2025 paper *Towards Practical, End-to-End
Formally Verified X.509 Certificate Validators with Verdict* (Lin et al.).

### 1.1 Techniques worth copying

1. **One end-to-end theorem, stated against a readable spec.** The top-level
   `validate_der` ensures `res == Query { policy, roots, bundle: parse(der), task }.valid()`.
   Everything (parser, path builder, policy) is checked against that one statement.
   The paper calls the split of *policy* from *mechanism* (parsing, path building)
   "an important factor" in keeping the effort tractable.
2. **Verified parser combinators (Vest).** Each format is built from combinators that
   carry three proofs: parse→serialize roundtrip, serialize→parse roundtrip, and
   *prefix security* (trailing bytes cannot change what was parsed). In the repo these
   are the `SecureSpecCombinator` obligations in `deps/vest/src/properties.rs`. That
   rules out malleability and parser-differential bugs by construction, and the paper
   reports performance on par with hand-written parsers (their parser: 0.024 s on 1,000
   CT certificates vs 9.32 s for ASN1⋆).
3. **Executable specs compiled to verified code (`rspec!`).** Policies are written once
   as Verus spec functions; a proc macro (`verdict-rspec`, ~1.7k lines, itself unverified
   but *not trusted*) emits the exec version plus the equivalence proof. That avoids
   writing every rule twice. The paper notes this duplication was the main maintenance
   burden in earlier work (ARMOR), and the authors are upstreaming a general version to Verus.
4. **Policies are small, auditable data-like code.** Chrome/Firefox/OpenSSL policies are
   405/400/372 lines vs 1,628 / 2,348 / 2,429 lines in the originals. Standard RFC
   properties are proved over them automatically (`standard::auto_std!`).
5. **Safe Rust only, enforced.** `#![forbid(unsafe_code)]` everywhere except trusted glue.
6. **Fast proof iteration.** 57 s single-threaded for the whole project (38 s parser,
   15 s path builder + policies); 72 `bit_vector` proofs and only 2 `nonlinear_arith`.
   Proofs are kept local so failures show up quickly.
7. **Build without the verifier.** `cargo build` strips annotations, so users who never
   install Verus can still consume the crate.

### 1.2 Pitfalls and limits seen in Verdict

| Pitfall | Evidence | What we do instead |
|---|---|---|
| Pinned to a **forked Verus branch** (`deps/verus` on branch `x509`); last push 2025-11-19 | `.gitmodules` | Track upstream Verus; weekly CI against the newest release (the Nanvix slab proof sat broken for 7 weeks for exactly this reason) |
| **Trusted string glue**: 54 `external_body` items in `verdict-polyfill` (Rc/Arc str conversions, equality) plus std prefix/suffix, UTF-8, case folding | `verdict-polyfill/src/lib.rs`; paper §7 | A small verified `vstr` crate early, because a browser is far more string-heavy than X.509 |
| **Unverified time conversion** (chrono) | paper §7 | Verify the few date/time parsers we need (HTTP-date, cookie Expires) |
| **Spec data fidelity**: the Chrome policy's public-suffix list is marked "this list is incomplete" | `verdict/src/policy/chrome.rs` | Generate data tables from upstream sources in CI and record their provenance |
| **Partial standard coverage**: policies conform to 8 / 10 / 11 of the RFC requirements checked | paper §5 | Publish the conformance matrix per component; never round it up |
| **Termination not proved** on the path builder (`exec_allows_no_decreases_clause`) | `verdict/src/validator.rs` | Require `decreases` on all kernel/parse loops; liveness matters for a browser (hangs are DoS) |
| **Boolean-only results** make error reporting hard | paper §7 | Policies return enums from day one |
| **Revocation (OCSP) not modeled** | paper §7 | Make policies parametric in pre-fetched state (their suggested approach) |
| The spec is trusted (a wrong policy is a proved-wrong validator) | paper §3 | Differential-test specs against real engines (they used 10M CT certs + Limbo) |

---

## 2. Prior work on verified browsers

These references are from memory and not re-checked for this draft. Confirm them before citing.

- **Quark** (Jang, Tatlock, Lerner, USENIX Security 2012): a small browser *kernel* verified
  in Coq, with unmodified WebKit running as untrusted sandboxed tab processes. It proved tab
  non-interference, cookie integrity and address-bar correctness. This "formal shim" is the
  pattern that lets a browser be usable before most of it is verified.
- **Featherweight Firefox** (Bohannon, Pierce): a formal model of browser/JS interaction.
- **Cassius / VizAssert** (Panchekha, Torlak et al.): CSS layout formalized for SMT; proves
  properties of page layouts.
- **JSCert / JSRef** (Bodin, Charguéraud, Gardner et al., POPL 2014): ES5 semantics in Coq, plus a
  reference interpreter extracted to OCaml and proved correct against JSCert for ES5 chapters 8–14.
  Running it on test262 found bugs in JSCert, JSRef, browsers, the standard, and test262 itself.
  Pitfall: parsing was not verified (it trusted the Closure parser). Source: [jscert/jscert](https://github.com/jscert/jscert).
- **ESMeta / JISET** (KAIST/Korea Univ. PLRG; CACM 2024): automatically extracts a mechanized spec
  (IRES control-flow graphs) from a given commit of ecma262 `spec.html`, then runs it as an
  interpreter and synthesizes conformance tests. Source: [es-meta/esmeta](https://github.com/es-meta/esmeta).
- **Warblre** (De Santo, Barrière, Pit-Claudel, ICFP 2024): ECMAScript 2023 regex semantics (§22.2)
  in Coq, with spec text interleaved line by line. It proves compilation and matching terminate with
  no assertion failures, and passes 495 of 498 test262 regex tests. Source: [arXiv 2403.11919](https://arxiv.org/abs/2403.11919).
- **KJS** (K framework): another executable JS semantics (from memory, not re-checked).
- **WasmCert (Coq/Isabelle), vWasm / rWasm** (Bosamiya et al.): verified Wasm semantics and
  provably safe Wasm sandboxing. This is a route to running untrusted code with a verified boundary.
- **Servo components** (html5ever, Stylo, WebRender): production Rust and unverified. These are the
  practical untrusted renderer for the first releases.

---

## 3. Design

### 3.1 Principle: a verified shim first, then a ratchet

Make the browser *usable on day one* by running a real (unverified) engine inside isolated
renderer processes, behind a small **verified kernel** that owns every security decision.
Then replace components one by one with verified ones, and never let the verified share go down.

```
                       ┌──────────────── verified (Verus) ─────────────────┐
  network ──► TLS ───► │  Net service     Origin/Policy engine   Kernel    │ ──► display
  (rustls) (Verdict    │  (Vest parsers:  (rspec! policies:      (tabs,    │     (pixels,
   for certs)          │   HTTP, URL,     SOP, CSP, cookies,     IPC,      │      input)
                       │   MIME, cookie)  CORS, mixed content)   nav/UI)   │
                       └───────────────▲─────────────────────────▲─────────┘
                                       │ typed IPC (Vest-encoded)│
                  ┌────────────────────┴───┐            ┌────────┴────────────┐
                  │ Renderer (untrusted)   │   ...      │ Renderer (untrusted)│
                  │ html5ever, Stylo, JS,  │            │ one per site        │
                  │ layout, paint          │            │                     │
                  └────────────────────────┘            └─────────────────────┘
                    each in a Nanvix process/microVM (or OS sandbox off-Nanvix)
```

### 3.2 Components and what gets proved

| Layer | Component | Day-one implementation | Theorem(s) to prove | Tool | Phase |
|---|---|---|---|---|---|
| Kernel | Tab/process manager, IPC router, navigation, address bar | New, Verus | Tab non-interference; address bar shows the origin of the displayed document; renderer can only reach its own origin's state (Quark properties) | Verus | 1 |
| Policy | Origin model, Same-Origin Policy, CORS, CSP, cookie jar, mixed-content, permissions | New, `rspec!`-style executable specs | Exec == spec; specs carry standard properties (e.g., cookie for host H never sent to H' unless domain-match) | Verus + rspec | 1–2 |
| Parsing | URL (WHATWG), HTTP/1.1 framing, headers, MIME sniffing, cookie header, data:, base64, percent-encoding, UTF-8/Encoding, XML (well-formedness subset; CVE-2026-125350 was an XML UAF exploited ITW) | New, Vest combinators or spec-transcribed state machines | Roundtrip + prefix security where a grammar exists (XML included); for algorithmic specs (URL), equivalence to a transcription of the spec algorithm + totality, no panics | Verus (Vest), Lean for metatheory | 1–2 |
| TLS | Certificate validation | Verdict as a dependency, behind rustls | Already proved by Verdict (Chrome policy) | Verus | 1 |
| Strings | `vstr` (UTF-8, ASCII case folding, prefix/suffix, split) | New | Removes Verdict-style trusted string glue | Verus | 1 |
| Isolation | Renderer sandbox | Nanvix processes (WHP host today), OS sandbox elsewhere | Builds on Nanvix's verified kheap / frame allocator; add an IPC-channel isolation proof | Verus (in Nanvix) | 2–3 |
| Content | HTML tokenizer, tree builder | html5ever (untrusted) → verified replacement | Tokenizer: equivalence to the WHATWG state machine + totality; tree builder: DOM well-formedness invariants | Verus, SkySynth for code from spec | 3 |
| Content | CSS tokenizer/parser | cssparser (untrusted) → Vest-based | Roundtrip/prefix security on tokens | Verus | 3 |
| Layout | Block/inline layout | Stylo + Servo layout (untrusted) | Cassius-style properties (determinism, no overflow of declared boxes) on a subset | Verus/Lean | 4+ |
| Graphics | Compositor/rasterizer (Skia-class), GPU translation layer (ANGLE-class), WebGPU (Dawn-class) — 4 of the last 20 ITW Chrome CVEs (Dawn UAF, Skia OOB write, 2× ANGLE incl. a potential sandbox escape) | WebRender + untrusted GPU stack; **no verified replacement planned** — day-one untrusted, contained like the rest of the renderer | Topology decided now: GPU work runs **per-site, inside each renderer's Nanvix process**; no cross-site shared GPU service, because a shared service would add a cross-origin IPC surface and invalidate the containment theorem. If driver/hardware reality later forces a shared service, it is re-classed kernel-grade: typed Vest-encoded IPC, its own isolation proof, zero access to any origin's state | Verus (IPC/isolation surface only) | 2–3 (topology + isolation proof); replacement open |
| Script | JS engine `vjs` (§3.3) | New safe-Rust interpreter, no JIT; an untrusted engine only as a temporary fallback that has a removal criterion | Each interpreter step refines the ECMA-262 spec step; heap well-formedness and the essential internal-method invariants (§6.1.7.3) for every object; the parser matches the grammar plus early errors; GC preserves the reachable heap; regex matches the spec and terminates | Verus, Lean, ESMeta-derived spec | 1–5 |
| Script | Wasm | Verified interpreter in `vjs`, later AOT via a verified sandboxing compiler | Interpreter refines the Wasm spec; compiled code stays inside its sandbox | Verus | 4+ |

Trust at release 1: Rust compiler, Verus + Z3, the specs, the IPC glue, the crypto
providers (libcrux/AWS-LC verified subsets as in Verdict's `verified-crypto`), and the sandbox.
Renderers are **outside** the TCB: a compromised renderer can only misrender its own
origin, which is the property the kernel proves.

**Scope decision — extensions.** Release 1 ships **no extension or plugin API**. That
removes a recurring Chrome attack surface (Extensions API / loader policy — e.g.
CVE-2025-4664, reportedly used in a targeted campaign, though Google never published an
ITW confirmation) instead of verifying it; none of the last 20 ITW CVEs is in this class,
and not shipping the surface keeps it that way. If extensions ever ship, they are
kernel-mediated, capability-scoped, and governed by their own `rspec!` policy spec —
never renderer-side ambient authority.

### 3.3 Verified JavaScript engine (`vjs`)

The JS engine is where most of Chrome's in-the-wild bugs land: of the eight Chrome
zero-days exploited in the wild in 2026 (as of 2026-11-20), four are V8 bugs — including
CVE-2026-85046, a type confusion — and the other four are XML, CSS, Dawn, and Skia. The
non-V8 half is answered by containment and the §3.2 Graphics/Parsing rows, not by `vjs`
(the full last-20 CVE list and coverage map are in `docs/vjs-plan-review.md`). Leaving
the engine unverified and hoping the sandbox holds is not acceptable. `vjs` is a
first-class verified component with its own end-to-end theorem.

**The theorem.** For every program `p` and fuel `n`:
`vjs::run(p, n)` returns exactly one of:
- `Done(v)` with `v == spec_eval(p, n)`;
- `OutOfFuel`, which happens only if the spec also needs more than `n` steps;
- `Unsupported(feature)`, an explicit refusal that is never a wrong answer.

The ratchet shrinks the `Unsupported` set. Each spec section is either proved or reported as unsupported, never silently approximated.

**Design choices.**
1. **Safe Rust, interpreter only, no JIT.** `#![forbid(unsafe_code)]` across the engine.
   The heap is an index-based arena, so memory safety holds by construction before any
   functional proof. Proofs give correctness, which is what stops type-confusion-style
   logic bugs. A JIT never enters the TCB. Performance work goes into a bytecode
   interpreter whose compiler has a simulation proof.
2. **Spec from the source text, not retyped.** We generate Verus spec functions from
   ESMeta's mechanized ECMA-262, pinned to an exact `spec.html` commit, as we did by hand for
   WHATWG URL in `browser/url`.
   - The generator is untrusted. The generated spec is trusted, so we keep each algorithm step's text next to its spec
     line (as Warblre does) and differential-test the spec, compiled to exec, against
     test262 and ESMeta's own interpreter.
   - This answers Verdict's "spec is trusted" pitfall and JSRef's
     "spec has bugs" finding.
3. **Same proof shape as `vurl`.**
   - One spec function per algorithm and per loop.
   - Exec code proved equal to it, with "remaining-computation" loop invariants.
   - Lexicographic `decreases` everywhere. Non-termination exists only in the explicit fuel parameter.
4. **Verify the parser.** JSRef trusted an external parser, so we don't. The lexer and
   parser are proved against the ECMA-262 lexical and syntactic grammars, early errors included.
   The AST→bytecode compiler, when it comes, has its own proof.
5. **Invariants that matter for security.**
   - Heap well-formedness (no dangling indices, shapes consistent with property maps).
   - The §6.1.7.3 invariants of the essential internal methods, proved for ordinary objects and for every exotic object (Array, Proxy, TypedArray, arguments).
   - Realm/agent separation, so a renderer's realms never share objects except through the kernel-mediated binding layer.
6. **Host boundary.** DOM and Web IDL bindings go through a verified conversion layer
   (Web IDL's ToJS/ToIDL algorithms as specs). The engine has no ambient authority: every host
   capability is a kernel-issued handle.
7. **GC.** A mark-sweep collector over the arena, proved to preserve the abstract heap
   restricted to reachable objects.
8. **Regex.** A port of Warblre's semantics to Verus, proved to match the spec,
   terminate, and never hit an assertion failure.

**Order of work.** Each step ships with test262 subsets in CI and its numbers in the ratchet report.

| Step | Scope | Exit criterion (measured) |
|---|---|---|
| J0 | ESMeta→Verus spec generator; spec-as-exec differential harness vs test262 | Generated spec for chosen sections type-checks; harness reports per-section pass counts |
| J1 | Types and abstract ops: UTF-16 strings, Number (incl. shortest round-trip Number::toString, StringToNumber), BigInt, ToPrimitive/ToNumber/ToString, equality | Proved exec == spec; test262 `built-ins/Number`, `language/types` subsets |
| J2 | Object model: property descriptors, ordinary internal methods, §6.1.7.3 invariants, Array exotic | Invariant proofs; test262 `built-ins/Object` subset |
| J3 | Lexer, parser, early errors | Proved against the grammar; test262 `language/` parse tests |
| J4 | Interpreter core: environments, completion records, expressions, statements, functions, closures, exceptions. Memory until J6: an **unverified safe-Rust mark-sweep collector** (safety by construction — worst case is leaks/slowdown, never UAF) under a per-realm heap quota | Step refinement proved; `vjs` runs real scripts end to end; heap quota enforced; J6 replaces the collector with the proved one |
| J4b | Host boundary: Web IDL ToJS/ToIDL conversions as spec functions; every host capability is a kernel-issued handle; no ambient authority in the engine | Conversion proofs for the IDL surface of the top-N crawl-corpus sites; engine-wide audit shows zero non-handle host accesses |
| J5 | Built-ins by real-site usage (measured from a crawl corpus): Array, String, JSON (Vest round trip), Math, Map/Set, RegExp (Warblre port), Date (verified date parsing) | Per-built-in proofs; test262 pass rate per directory |
| J6 | Promises, job queue, async/await, generators; GC proof; Proxy/Reflect | Liveness under fuel; GC theorem |
| J7 | Bytecode compiler + interpreter with simulation proof; verified Wasm interpreter | Compiler correctness theorem; speed measured on a public benchmark set |

**Usability bridge, with a removal date set by a measurement, not a calendar.**
- Day-one speed comes from the untrusted engine, **JIT included**: no-JIT is a rule for
  `vjs` (the verified TCB), never for the user-facing default path. A browser nobody uses
  protects nobody — the default renderer runs the fast untrusted engine inside its
  sandbox, and the kernel decides per origin.
- A "verified script" mode runs only `vjs` and shows `Unsupported(feature)` to the user instead of falling back silently.
- The untrusted engine is deleted once `vjs` passes the crawl corpus at the same rate it does.
- Until then, the collector reports the share of script executions that ran on `vjs`.
- Long-term speed for verified mode: J7's proved bytecode compiler first. If that is still
  too slow for daily use, the next candidate is an *untrusted* JIT whose emitted code is
  confined by a verified sandbox (rWasm/vWasm-style code-region isolation, reusing the
  Phase 4+ Wasm work) — the JIT stays outside the TCB; what is verified is the sandbox
  that contains its output. A decision point, not a commitment.

**Scale, stated plainly.** JSRef's proof covered ES5 chapters 8–14. Current ECMA-262
is several times larger. We don't estimate effort here. The ratchet report (proved
sections, `Unsupported` features, test262 pass rate, verification seconds) is the only
progress number we'll publish.

### 3.4 How each workspace tool is used

- **Verus + Z3**: all Rust proofs. Rules: upstream Verus only; `#![forbid(unsafe_code)]`
  outside named glue modules; every loop has `decreases`; per-function `rlimit` budgets;
  `spinoff_prover` for heavy functions; one proof module per spec (`*.spec.rs` /
  `*.proof.rs`, as Nanvix already does).
- **VeriStruct (proof repair)**: runs when a Verus upgrade or refactor breaks proofs. It
  is accepted only if the result verifies, with *zero* new `assume`/`admit`/`external_body`
  (CI diff-checks those counts). Weekly "upgrade Verus" CI job: bump → verify →
  VeriStruct on failures → PR. That turns the 7-week Nanvix stall into a routine job.
- **SkySynth (proof-driven synthesis)**: generates exec code from `rspec`/spec functions and
  Vest format descriptions (HTTP headers, MIME, cookie attributes), with Verus as the oracle.
  Humans review specs; the machine writes and proves code.
- **Lean 4 / Vero**: (a) metatheory that SMT handles badly, e.g. URL serializer idempotence
  over the full spec, or confluence of the tree-builder insertion modes, proved in Lean
  against the same spec text; (b) every component becomes a **frozen-spec benchmark
  instance** (Vero style: fixed API + spec, agent supplies impl + proof, graded by
  recompilation with anti-cheat). That gives a measurable score for how well agents push
  the ratchet.
- **Nanvix**: the renderer isolation substrate (one Nanvix process or microVM per site),
  already running on the Windows WHP host and reachable through the conduit-lab bridge.
  Its existing Verus proofs (bitmap, slab, kheap, frame allocator) are the bottom of the stack.
- **conduit-lab collector + site**: extend `scripts/collect_stats.py` to report, per
  component, verified obligations, `assume`/`external_body` counts, and verification time,
  all generated from real runs, so the ratchet is visible and cannot be inflated.

### 3.5 The ratchet metric

For each release, the collector records, per crate: verified functions, trusted
functions (`external_body`, `assume_specification`, `admit`, `assume`), unsafe blocks,
and verification seconds. CI fails if any crate's trusted count goes up without a
linked justification, or if the verified share of the TCB goes down.

---

## 4. Roadmap

| Phase | Deliverable | Usable? | Exit criterion (measured, not estimated) |
|---|---|---|---|
| 0 | Skeleton: kernel process + one html5ever/Servo renderer in an OS sandbox; collector reports trusted/verified counts | Renders static pages | Loads a fixed test corpus; ratchet report generated |
| 1 | Verified URL parser, `vstr`, origin model, cookie jar, SOP; Verdict for certs | Browsing HTTPS sites | WPT `url/` and cookie tests pass at the published rate; 0 `assume` in those crates |
| 2 | Verified kernel (non-interference, address bar), HTTP/1.1 parsing, CSP/CORS policies; renderers on Nanvix | Daily-driver for simple sites | Kernel theorems verified; differential tests vs a reference engine on a crawl corpus |
| 3 | Verified HTML tokenizer and CSS tokenizer replace untrusted ones | Same, smaller TCB | WPT html/syntax tokenizer tests; roundtrip proofs |
| 4+ | Tree builder invariants, layout properties, Wasm sandbox | — | Per-component theorems |
| JS track (parallel from Phase 1) | `vjs` steps J0–J7 (§3.3) | Verified-script mode from J4 | Per-step criteria in §3.3; untrusted engine removed when `vjs` matches its crawl-corpus pass rate |

## 5. Risks

- **Spec size.** WHATWG HTML/URL/Fetch are algorithmic and change constantly. Transcribe
  sections into specs with links to the exact spec commit; re-diff on spec updates.
- **Solver instability** as specs grow. Mitigate with small modules, explicit triggers,
  `rlimit` budgets, and CI that reports per-function times so regressions are seen early.
- **Proof debt from AI tools.** VeriStruct/SkySynth output must verify with no new trusted
  items; the collector enforces it.
- **Usability vs. verification pull.** The shim design keeps them separate: renderer
  features never wait on proofs, and proofs never block browsing.

## 6. First concrete steps

1. Create `verified-browser` workspace with crates `kernel`, `policy`, `net-parse`, `vstr`,
   `renderer-servo` (untrusted), and the ratchet collector.
2. Port the Vest combinators against upstream Verus (Verdict vendors them in `deps/vest`).
3. Write the WHATWG URL spec transcription as Verus spec functions; prove the exec parser.
4. Wire a Servo renderer behind a typed IPC boundary and render a static page.
