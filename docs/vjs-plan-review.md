# Review: the JS engine plan (§3.3 `vjs`) vs. the real Chrome zero-day surface

Date: 2026-11-20. Reviews `docs/verified-browser-engine.md` §3.2–§3.3 against the last 20
Chrome CVEs Google confirmed exploited in the wild. All CVE rows were verified against
primary sources (Chrome Releases Blog ITW wording, cross-checked with CISA KEV
v2026.11.18); cells marked "(KEV)" were not re-captured from the blog post itself.

State of implementation at review time: only `vurl` exists (65 verified functions,
0 trusted items, 2.17 s verification — `browser/ratchet.json`). Everything about `vjs`
is design.

---

## 1. Tradeoffs the plan is making

| # | Decision | Given up | Gained | Residual risk |
|---|---|---|---|---|
| 1 | Interpreter only, no JIT ever in TCB; bytecode + simulation proof deferred to J7 | ~10–100× performance vs TurboFan/Maglev; verified-script mode is slow on day one | The entire JIT-compiler bug class — where most exploited V8 bugs live — becomes inexpressible; step-refinement proofs stay tractable | Bytecode compiler proof is unsized and far out; perf target is "measured at J7", not a requirement |
| 2 | Safe Rust, `forbid(unsafe_code)`, index-based arena heap | FFI/ecosystem convenience; raw speed | UAF/OOB-write *memory corruption* eliminated by construction, before any proof runs | Logical type confusion (wrong value treated as wrong type) is still possible — caught only if the §6.1.7.3 invariant + heap well-formedness proofs actually cover every exotic object, as promised |
| 3 | Verified mark-sweep GC (J6) | A simple bump/leak or off-the-shelf collector | No dangling indices, no GC-introduced UAF | GC-preservation proofs are among the hardest in the plan; J6 is late in the order while J4 already runs real scripts — what collects garbage between J4 and J6 is unspecified |
| 4 | Spec generated from ESMeta text, pinned commit; generated spec *trusted*, generator not | Freedom from spec-drift management; the TCB now includes ECMA-262 text + human spec review | No transcription-error class (JSRef's pitfall); line-by-line spec fidelity (Warblre style); differential-tested vs test262 + ESMeta | A wrong spec is a *proved-wrong* engine (Verdict's own caveat). Pinned commit ⇒ continuous re-diff obligation against a living standard |
| 5 | Fuel semantics: `Done` / `OutOfFuel` / `Unsupported`, nothing else | Liveness; real sites need a fuel policy that is itself an unverified operational knob | Termination is provable everywhere; regex (Warblre port) kills the ReDoS class; refusals are never wrong answers | Warblre passes 495/498 test262 — three known semantic divergences become user-visible `Unsupported` or wrong-ish behavior; hangs become a DoS surface if fuel policy is wrong |
| 6 | Explicit `Unsupported` + "verified script" mode; untrusted engine kept until crawl-corpus parity, removal criterion measured not scheduled | Web compatibility for years; the plan's own motivating attack surface (an unverified engine in the renderer) ships in the meantime | Honesty ratchet: coverage is published per section, never silently approximated | No timeline ⇒ the fallback engine could become permanent; "same crawl-corpus pass rate" is a functional bar, not a security bar |
| 7 | Kernel-issued capability handles; verified Web IDL ToJS/ToIDL conversion layer | Direct-binding performance and convenience | No ambient authority in the engine; renderer compromise can't forge capabilities | The binding layer has a design paragraph but **no phase, no J-step, no exit criterion** — it is the largest unsized verification surface in §3.3 |
| 8 | Per-algorithm exec==spec proofs, lexicographic `decreases`, per-function `rlimit` | Proof velocity as specs grow; solver stability (plan's own §5 risk) | One composable end-to-end theorem per component, Verdict-style | ECMA-262 is several times JSRef's ES5 ch. 8–14 scope; effort is explicitly unestimated ⇒ schedule risk is unbounded |
| 9 | Scope: verify the JS engine + kernel/policy, *contain* everything else (Quark shim) | Whole-stack verification ambition | Tractable TCB; renderers outside it; usable browser before proofs finish | Containment is only as good as the kernel theorems + Nanvix isolation (Phases 2–3) — and see §3: whole CVE classes live outside the verified scope entirely |

## 2. The last 20 Chrome CVEs exploited in the wild (as of 2026-11-20)

| CVE | Patched | Component | Bug class | Fixed in | Reporter / campaign | KEV |
|---|---|---|---|---|---|---|
| CVE-2026-125350 | 2026-11-09 | XML (Blink) | Use-after-free | 157.0.8103.50 | Neonix Security + anon | added 11-10 |
| CVE-2026-87491 | 2026-09-08 | V8 | OOB write | 152.0.7977.x | reported by Google 2026-08-27 | added 09-09 |
| CVE-2026-85046 | 2026-09-03 | V8 | Type confusion | 152.0.7977.82 | Salvatore Gulizia | added 09-04 |
| CVE-2026-11645 | 2026-06-08 | V8 | OOB read/write | 149.0.7827.102 | pseudonymous | added 06-09 |
| CVE-2026-5281 | 2026-03-31 | Dawn (WebGPU) | Use-after-free | 146.0.7680.177 | — | **not in KEV** |
| CVE-2026-3909 | 2026-03-13 | Skia | OOB write | 146.0.7680.80 | Google TAG (targeted) | **not in KEV** |
| CVE-2026-3910 | 2026-03-12 | V8 | Inappropriate implementation | 146.0.7680.75 | Google TAG | added 03-13 |
| CVE-2026-2441 | 2026-02-13 | CSS (Blink) | Use-after-free | 145.0.7632.75 | Shaheen Fazim | added 02-17 |
| CVE-2025-14174 | 2025-12-10 | ANGLE | OOB memory access | 143.0.7499.109 | Apple SEAR + Google TAG | added 12-12 |
| CVE-2025-13223 | 2025-11-17 | V8 | Type confusion | 142.0.7444.175 | Google TAG | added 11-19 |
| CVE-2025-10585 | 2025-09-17 | V8 | Type confusion | 140.0.7339.185/.186 | Google TAG ($15k) | added 09-23 |
| CVE-2025-6558 | 2025-07-15 | ANGLE + GPU | Incorrect validation (potential **sandbox escape**) | 138.0.7204.157 | TAG (Lecitre, Stolyarov) | added 07-22 |
| CVE-2025-6554 | 2025-06-30 | V8 | Type confusion (arbitrary r/w) | 138.0.7204.96 | TAG (Lecitre); mitigated by config 06-26 | added 07-02 |
| CVE-2025-5419 | 2025-06-02 | V8 | OOB read/write | 137.0.7151.68 | TAG (Lecitre, Sevens) | added 06-05 |
| CVE-2025-2783 | 2025-03-25 | Mojo (Windows) | **Sandbox escape** — incorrect handle | 134.0.6998.165/.178 (KEV) | Kaspersky | added 03-27 |
| CVE-2024-7965 | 2024-08-21 | V8 | Inappropriate implementation | 128.0.6613.119/.120 (KEV) | TheDog; ITW noted in 08-26 post update | added 08-28 |
| CVE-2024-7971 | 2024-08-21 | V8 | Type confusion | 128.0.6613.119/.120 (KEV) | — | added 08-26 |
| CVE-2024-5274 | 2024-05-23 | V8 (Windows) | Type confusion | 125.0.6422.112/.113 | TAG (Lecitre) + Chrome Security | added 05-28 |
| CVE-2024-4947 | 2024-05-15 | V8 | Type confusion | 124.0.6367.201/.202 (KEV) | Kaspersky (Berdnikov, Larin) | added 05-20 |
| CVE-2024-4761 | 2024-05-13 | V8 (Mac first) | OOB write | 124.0.6367.207/.208 | Anonymous | added 05-16 |

Tally by component: **V8 13/20 (65%)** · Blink XML/CSS 2 · ANGLE 2 · Dawn 1 · Skia 1 · Mojo 1.
Tally by class: type confusion 7 · OOB read/write 6 · UAF 3 · inappropriate implementation 2 · sandbox escape/incorrect handle 2.

Method notes: every 2025–2026 desktop-stable blog post (115, enumerated via sitemap) was
scanned for Google's exact "exploit ... exists in the wild" wording; the six 2024/early-2025
rows were re-verified directly from their blog posts. KEV alone is insufficient —
CVE-2026-5281 and CVE-2026-3909 carry Google's ITW wording but are absent from KEV.
CVE-2025-4664 (Loader), widely reported as exploited in June 2025, carries **no** ITW
wording in any scanned post and is not in KEV, so it is excluded here. The 21st-most-recent
ITW CVE is CVE-2024-4671 (Visuals UAF, 2024-05-09).

Fact-check of §3.3's own claims: **CVE-2026-85046 is real** (V8 type confusion, fixed
152.0.7977.82, blog post 2026-09-03, KEV 2026-09-04), and "**at least four of 2026's
exploited Chrome zero-days are V8 bugs**" **holds** — 2026 had 8 ITW zero-days total
(4× V8: 87491, 85046, 11645, 3910; plus XML, CSS, Dawn, Skia).

## 3. Does this engine give coverage against those classes?

**Covered by construction, once built (13/20, the V8 block).** No JIT, safe-Rust arena,
and §6.1.7.3 internal-method invariants aim exactly at the dominant class: type confusion
and OOB bugs born in optimizing compilers and the object model. Memory-corruption
*manifestations* (UAF, OOB writes) can't exist in a `forbid(unsafe_code)` index arena;
logical confusion is what the invariant proofs are for. This is the strongest, best-argued
part of the plan — and it is 0% built. Until J4, and realistically until the untrusted
fallback is removed, V8-class protection equals whatever fallback engine ships inside a
not-yet-proven sandbox: the same bet Chrome makes today.

**Covered by the containment story, if the kernel theorems land (3/20).**
CVE-2025-2783 (Mojo handle → sandbox escape) is the direct analogue of the plan's typed
Vest-encoded IPC + "renderer can only reach its own origin's state" + per-site Nanvix
isolation. CVE-2025-6558 (ANGLE validation → potential sandbox escape) and the Blink
XML/CSS UAFs (CVE-2026-125350, CVE-2026-2441) land in untrusted renderers, where the
Quark-style shim is supposed to make compromise non-escapable. Note the CSS parser has a
verified replacement path (Phase 3) but **XML parsing appears nowhere in the component
table**.

**Not covered at all (4/20, 20%): the graphics stack.** Dawn, Skia, and ANGLE — one-fifth
of the recent ITW surface, including a TAG-reported targeted Skia bug and a potential
sandbox escape through GPU input validation — are absent from §3.2, from the architecture
diagram, and from the roadmap. In Chrome these live in the GPU process, which is
*shared across sites and more privileged than a renderer*; the plan's diagram has no GPU
service, and WebRender is mentioned only in passing (§2). This is the biggest hole: an
unverified cross-site GPU service inside or beside the "verified kernel" would undercut
the containment theorem the whole design rests on.

**Structurally absent (a plus):** no extensions/loader-policy CVEs appear in the last 20,
and the plan doesn't mention extensions — if the browser ships without an extension API,
that recurring ITW surface (loader policy, Extensions API) simply doesn't exist. Worth
stating as an explicit decision rather than an omission.

## 4. Recommendations

1. Add rows to §3.2 for the graphics stack (compositor/rasterizer à la Skia, GPU-translation
   layer à la ANGLE, WebGPU à la Dawn): day-one untrusted, with the process topology
   decided **now** — per-site GPU work vs. a shared GPU service changes the kernel's IPC
   theorem and the isolation proof (Phase 2–3).
2. Add XML parsing to the Parsing layer (it is 1/20 of the recent ITW list).
3. Give the Web IDL binding layer a phase and exit criterion in the J-table; today it is
   a design bullet carrying an unsized verification surface.
4. Specify what manages memory between J4 (real scripts run) and J6 (proved GC).
5. Record the extensions decision explicitly.
6. §3.3's CVE citations check out; consider updating the sentence to the fuller 2026 tally
   (8 ITW zero-days: 4× V8, XML, CSS, Dawn, Skia as of 2026-11-20) — the non-V8 half is
   exactly the gap in recommendation 1.
