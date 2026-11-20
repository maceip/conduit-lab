// Renders everything from data/stats.json (written by scripts/collect_stats.py).
// No value on the page is hard-coded: if a field is missing it is shown as "not recorded".
(() => {
  const $ = (id) => document.getElementById(id);
  const NR = "not recorded";

  function el(tag, attrs = {}, ...kids) {
    const n = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
      if (k === "class") n.className = v;
      else if (k === "text") n.textContent = v;
      else n.setAttribute(k, v);
    }
    for (const k of kids) if (k != null) n.append(k);
    return n;
  }
  const val = (v) => (v === null || v === undefined ? NR : String(v));
  const link = (href, text) => (href ? el("a", { class: "link", href, text }) : document.createTextNode(text));
  const fmtDate = (iso) => (iso ? new Date(iso).toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" }) : NR);
  const verusLine = (r) =>
    r && r.verified != null ? `${r.verified} verified, ${r.errors} errors` : `no result (exit ${val(r && r.exit_code)})`;
  const ok = (r) => r && r.exit_code === 0 && r.errors === 0;

  function commitUrl(repo) {
    const m = (repo.remote || "").match(/github\.com[:/](.+?)(\.git)?$/);
    return m && repo.commit ? `https://github.com/${m[1]}/commit/${repo.commit}` : null;
  }

  function li(parent, content, cls) {
    const item = el("li", cls ? { class: cls } : {});
    item.append(content);
    parent.append(item);
  }

  function render(s) {
    const tc = s.toolchains || {};
    const vstd = (s.verus || {}).vstd;
    const examples = (s.verus || {}).examples || [];
    const benches = (s.lean || {}).benchmarks || [];
    const repos = s.repos || [];
    const repo = (n) => repos.find((r) => r.name === n);
    const attempted = benches.filter((b) => b.status !== "skipped_mathlib" && b.status !== "no_lakefile");
    const passed = attempted.filter((b) => b.status === "passed");
    const skipped = benches.filter((b) => b.status === "skipped_mathlib");
    const openSorry = passed.reduce((a, b) => a + (b.sorry_count || 0), 0);

    // hero chips
    const chips = $("chips");
    const short = (v, re) => (v ? (v.match(re) || [null, v])[1] : null);
    [
      s.host && s.host.machine ? `${s.host.machine} native` : null,
      tc.z3 && `Z3 ${short(tc.z3, /version ([\d.]+)/)}`,
      tc.rustc && `Rust ${short(tc.rustc, /rustc ([\d.]+)/)}`,
      tc.lean && `Lean ${short(tc.lean, /version ([\d.]+)/)}`,
      tc.verus && `Verus ${tc.verus}`,
    ].filter(Boolean).forEach((t) => chips.append(el("span", { text: t })));

    // stats strip
    const stats = $("stats");
    const stat = (n, label, good) =>
      stats.append(el("div", {}, el("strong", { text: n, class: good === false ? "bad" : "" }), el("span", { text: label })));
    stat(vstd && vstd.verified != null ? String(vstd.verified) : NR, "vstd obligations verified", ok(vstd));
    const errs = [vstd, ...examples].reduce((a, r) => (r && r.errors != null ? a + r.errors : a), 0);
    stat(String(errs), "Verus errors (vstd + examples)", errs === 0);
    stat(`${passed.length}/${attempted.length}`, `Lean benchmarks built (${benches.length} total)`, passed.length === attempted.length);
    stat(String(openSorry), "open sorry in built benchmarks");

    // run meta
    const meta = $("run-meta");
    const row = (k, v) => meta.append(el("dt", { text: k }), el("dd", {}, v));
    row("Generated", document.createTextNode(fmtDate(s.generated_at)));
    row("Run duration", document.createTextNode(s.duration_seconds != null ? `${s.duration_seconds} s` : NR));
    row("Host", document.createTextNode(s.host ? `${val(s.host.system)} ${val(s.host.release)} / ${val(s.host.machine)}` : NR));
    row("Raw data", link("data/stats.json", "data/stats.json"));
    $("footer-run").textContent = `Last run ${fmtDate(s.generated_at)}`;

    // repos
    const rb = $("repos");
    for (const r of repos) {
      const dirty = el("td", { text: String(r.uncommitted_files), class: r.uncommitted_files ? "warn" : "" });
      rb.append(el("tr", {},
        el("td", { text: r.name }),
        el("td", {}, link(commitUrl(r), r.commit ? r.commit.slice(0, 10) : NR)),
        el("td", { text: fmtDate(r.commit_date) }),
        dirty));
    }

    // toolchains
    const tb = $("toolchains");
    for (const [k, v] of Object.entries(tc)) tb.append(el("tr", {}, el("td", { text: k }), el("td", {}, el("code", { text: val(v) }))));

    // cards
    const cv = $("card-verus");
    li(cv, el("span", {}, "vstd: ", link(vstd && vstd.log, verusLine(vstd))), ok(vstd) ? "" : "bad");
    for (const e of examples) li(cv, el("span", {}, `${e.file.split("/").pop()}: `, link(e.log, verusLine(e))), ok(e) ? "" : "bad");
    li(cv, document.createTextNode(`Z3: ${val(tc.z3)}`));
    li(cv, document.createTextNode(`rustc: ${val(tc.rustc)}`));

    const repoLines = (ul, r) => {
      if (!r) return li(ul, document.createTextNode(`repository: ${NR}`));
      li(ul, el("span", {}, "commit ", link(commitUrl(r), r.commit ? r.commit.slice(0, 10) : NR)));
      li(ul, document.createTextNode(`${r.uncommitted_files} uncommitted files`), r.uncommitted_files ? "warn" : "");
    };
    const cvs = $("card-veristruct");
    repoLines(cvs, repo("VeriStruct"));
    li(cvs, document.createTextNode("repair outcomes: not measured by the collector"));

    const csd = $("card-skydiscover");
    repoLines(csd, repo("skydiscover"));
    for (const c of (s.cli || []).filter((c) => c.name === "skydiscover"))
      li(csd, el("span", {}, el("code", { text: c.command }), " → ", link(c.log, `exit ${c.exit_code}`)), c.exit_code === 0 ? "" : "bad");

    const cvo = $("card-vero");
    repoLines(cvo, repo("vero"));
    li(cvo, document.createTextNode(`${passed.length}/${attempted.length} attempted benchmarks built`), passed.length === attempted.length ? "" : "bad");
    li(cvo, document.createTextNode(`${skipped.length} skipped (need mathlib)`));
    li(cvo, document.createTextNode(`${val(tc.lean)}`));

    // example proof
    const ex = examples[0];
    if (ex) {
      $("example-name").textContent = ex.file;
      $("example-result").append(el("span", { class: ok(ex) ? "pill good" : "pill bad", text: verusLine(ex) }),
        " ", link(ex.log, "raw log"), ` · ${val(ex.seconds)} s`);
      fetch(ex.source).then((r) => (r.ok ? r.text() : Promise.reject(r.status)))
        .then((t) => ($("example-src").textContent = t))
        .catch((e) => ($("example-src").textContent = `could not load ${ex.source} (${e})`));
    }

    // benchmarks table with filter
    const statuses = ["all", ...new Set(benches.map((b) => b.status))];
    const filters = $("bench-filters");
    const rows = $("bench-rows");
    const draw = (f) => {
      rows.replaceChildren();
      for (const b of benches.filter((b) => f === "all" || b.status === f)) {
        rows.append(el("tr", { "data-status": b.status },
          el("td", { text: b.name }),
          el("td", {}, el("span", { class: `pill ${b.status === "passed" ? "good" : b.status.startsWith("skipped") ? "muted" : "bad"}`, text: b.status.replace("_", " ") })),
          el("td", { text: val(b.jobs) }),
          el("td", { text: val(b.sorry_count) }),
          el("td", { text: val(b.seconds) }),
          el("td", {}, b.log ? link(b.log, "log") : document.createTextNode("—"))));
      }
      for (const btn of filters.children) btn.setAttribute("aria-pressed", String(btn.dataset.f === f));
    };
    for (const f of statuses) {
      const n = f === "all" ? benches.length : benches.filter((b) => b.status === f).length;
      const btn = el("button", { type: "button", "data-f": f, text: `${f.replace("_", " ")} (${n})` });
      btn.addEventListener("click", () => draw(f));
      filters.append(btn);
    }
    draw("all");

    // quickstart outputs
    $("qs-verus").textContent = ex ? `verification results:: ${verusLine(ex)}` : NR;
    const ar = benches.find((b) => b.name === "Arithmetic");
    $("qs-lean").textContent = ar && ar.status === "passed" ? `Build completed successfully (${val(ar.jobs)} jobs).` : `Arithmetic: ${val(ar && ar.status)}`;
  }

  fetch("data/stats.json", { cache: "no-cache" })
    .then((r) => (r.ok ? r.json() : Promise.reject(new Error(`HTTP ${r.status}`))))
    .then(render)
    .catch((e) => {
      const b = $("load-error");
      b.hidden = false;
      b.textContent = `Could not load data/stats.json (${e.message}). Run python3 scripts/collect_stats.py to generate it. No numbers are shown without it.`;
    });
})();
