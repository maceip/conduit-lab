// CONDUIT irrigation console. Every value comes from the local bridge (bridge/conduit_bridge.py);
// every control calls it. With no bridge, the page shows how to start one and all controls stay disabled.
(() => {
  const BRIDGE = (() => {
    try { return new URLSearchParams(location.search).get("bridge") || "http://127.0.0.1:8787"; }
    catch { return "http://127.0.0.1:8787"; }
  })();
  const $ = (id) => document.getElementById(id);
  const SVGNS = "http://www.w3.org/2000/svg";
  let S = null;            // last /api/status
  let online = false;
  let watchedJob = null;   // job id whose log is shown
  const busy = new Set();  // control keys with a request in flight

  // ---------------------------------------------------------------- helpers
  function svg(tag, attrs = {}, parent) {
    const n = document.createElementNS(SVGNS, tag);
    for (const [k, v] of Object.entries(attrs)) n.setAttribute(k, v);
    if (parent) parent.append(n);
    return n;
  }
  function el(tag, attrs = {}, ...kids) {
    const n = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
      if (k === "class") n.className = v; else if (k === "text") n.textContent = v; else n.setAttribute(k, v);
    }
    kids.forEach((k) => k != null && n.append(k));
    return n;
  }
  async function api(method, path, body) {
    const r = await fetch(BRIDGE + path, {
      method,
      headers: body ? { "Content-Type": "application/json" } : {},
      body: body ? JSON.stringify(body) : undefined,
    });
    const data = await r.json().catch(() => ({}));
    if (!r.ok) throw new Error(data.error || `HTTP ${r.status}`);
    return data;
  }
  async function act(key, btn, fn) {
    if (busy.has(key)) return;
    busy.add(key);
    if (btn) btn.setAttribute("aria-busy", "true");
    try {
      const res = await fn();
      if (res && res.job) watchJob(res.job, key);
      await refresh();
    } catch (e) {
      toastError(`${key}: ${e.message}`);
    } finally {
      busy.delete(key);
      if (btn) btn.removeAttribute("aria-busy");
      render();
    }
  }
  const localErrors = [];
  function toastError(text) {
    localErrors.push({ t: Date.now() / 1000, kind: "error", text });
    localErrors.splice(0, Math.max(0, localErrors.length - 20));
    renderEvents();
  }
  const fmtTime = (t) => new Date(t * 1000).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit", second: "2-digit" });
  const moistClass = (z) => (z.moisture < z.low ? "dry" : z.moisture > z.high ? "wet" : "ok");
  const BED_COLORS = { dry: "#7a4b2a", ok: "#2f7d4f", wet: "#1d5f8a" };

  // ---------------------------------------------------------------- static SVG zones
  const ZY = [60, 160, 260, 360];
  const zoneEls = ZY.map((y, i) => {
    const g = svg("g", { "data-zone": i, class: "zone" }, $("zones"));
    svg("path", { d: `M240 ${y} H292`, class: "pipe" }, g);
    svg("path", { d: `M240 ${y} H292`, class: "flow-line" }, g);
    svg("path", { d: `M316 ${y} H340`, class: "pipe" }, g);
    svg("path", { d: `M316 ${y} H340`, class: "flow-line" }, g);
    const valve = svg("g", { class: "valve-btn", tabindex: "0", role: "button" }, g);
    svg("rect", { x: 292, y: y - 12, width: 24, height: 24, rx: 5, class: "valve" }, valve);
    svg("path", { d: `M298 ${y - 6} L310 ${y + 6} M310 ${y - 6} L298 ${y + 6}`, stroke: "#5d7599", "stroke-width": 2 }, valve);
    const bed = svg("rect", { x: 340, y: y - 34, width: 390, height: 68, rx: 8, class: "bed", fill: "#14203a" }, g);
    const fill = svg("rect", { x: 340, y: y - 34, width: 0, height: 68, rx: 8, opacity: 0.85 }, g);
    svg("rect", { x: 340, y: y - 34, width: 390, height: 68, rx: 8, class: "bed-soil" }, g);
    const low = svg("line", { y1: y - 34, y2: y + 34, class: "thr" }, g);
    const high = svg("line", { y1: y - 34, y2: y + 34, class: "thr" }, g);
    const name = svg("text", { x: 356, y: y - 8, class: "zone-name" }, g);
    const info = svg("text", { x: 356, y: y + 14, class: "val" }, g);
    const drops = svg("g", { class: "drops" }, g);
    [0, 1, 2].forEach((k) => svg("circle", { cx: 360 + k * 120 + 40, cy: y - 30, r: 3 }, drops));
    const toggle = () => {
      if (valve.getAttribute("aria-disabled") === "true") return;
      const st = primaryState();
      const open = st && st.open[i];
      act(`valve${i}`, null, () => api("POST", "/api/command", { cmd: `${open ? "close" : "open"} ${i}` }));
    };
    valve.addEventListener("click", toggle);
    valve.addEventListener("keydown", (e) => (e.key === "Enter" || e.key === " ") && (e.preventDefault(), toggle()));
    return { g, valve, bed, fill, low, high, name, info };
  });

  // ---------------------------------------------------------------- state
  function primaryState() {
    if (!S) return null;
    const want = S.garden.sim.primary;
    const rt = S.runtimes[want];
    return rt && rt.running ? rt.state : null;
  }
  const anyRunning = () => !!S && Object.values(S.runtimes).some((r) => r.running);

  async function refresh() {
    try {
      S = await api("GET", "/api/status");
      online = true;
    } catch {
      online = false;
      S = null;
    }
    render();
  }

  async function watchJob(id, label) {
    watchedJob = id;
    $("job-title").textContent = label || "";
    while (watchedJob === id) {
      try {
        const j = await api("GET", `/api/jobs/${id}`);
        const pre = $("joblog");
        const stick = pre.scrollTop + pre.clientHeight >= pre.scrollHeight - 20;
        pre.textContent = j.log.join("\n");
        if (stick) pre.scrollTop = pre.scrollHeight;
        $("job-title").textContent = `${j.kind} · ${j.status}`;
        if (j.status !== "running") { await refresh(); break; }
      } catch (e) {
        $("job-title").textContent = `job ${id}: ${e.message}`;
        break;
      }
      await new Promise((r) => setTimeout(r, 1000));
    }
  }

  // ---------------------------------------------------------------- render
  function setDisabled(node, off) { node.disabled = !!off; }

  function render() {
    const conn = $("conn");
    conn.dataset.state = online ? "online" : S === null && conn.dataset.state === "connecting" ? "connecting" : "offline";
    $("conn-text").textContent = online
      ? `Bridge connected · ${S.bridge.lab}`
      : `No bridge at ${BRIDGE.replace(/^https?:\/\//, "")}`;
    $("setup").hidden = online;
    if (!online) conn.dataset.state = "offline";

    const pst = primaryState();
    const running = anyRunning();

    // verify
    setDisabled($("btn-verify"), !online || busy.has("verify") || (S && S.jobs.some((j) => j.kind === "verify" && j.status === "running")));
    const vr = $("verify-result");
    vr.replaceChildren();
    const v = S && S.garden.verification;
    if (v) {
      const good = v.exit_code === 0 && v.errors === 0;
      vr.append(el("span", { class: good ? "good" : "bad", text: v.verified != null ? `${v.verified} verified, ${v.errors} errors` : `verifier exit ${v.exit_code}` }),
        ` · ${fmtTime(v.at)} · ctl.rs ${v.ctl_sha256.slice(0, 12)}`);
    } else if (online) vr.textContent = "Not verified in this workspace yet.";

    // runtimes
    for (const name of ["macos", "nanvix"]) {
      const card = $(`rt-${name}`);
      const rt = S && S.runtimes[name];
      card.dataset.running = String(!!(rt && rt.running));
      card.querySelector(".rt-state").textContent = !rt ? "—" : rt.running ? `running · tick ${rt.state ? rt.state.ticks : "?"}` : "stopped";
      const detail = card.querySelector(".rt-detail");
      if (!rt) detail.textContent = "";
      else if (rt.error) detail.textContent = `Error: ${rt.error}`;
      else if (name === "macos") detail.textContent = rt.binary ? `binary ${rt.binary}` : "Not built. Press Verify & build.";
      else detail.textContent = rt.host ? `${rt.host} · ${rt.dir}` : "No Nanvix host configured. Start the bridge with --nanvix-host.";
      const btn = (a) => card.querySelector(`[data-act="${a}"]`);
      const jobRunning = (kind) => S && S.jobs.some((j) => j.kind === kind && j.status === "running");
      if (name === "macos") {
        setDisabled(btn("start"), !online || !rt || rt.running || !rt.binary || busy.has("macos-start"));
      } else {
        const p = rt && rt.probe;
        setDisabled(btn("probe"), !online || !rt || !rt.host || busy.has("nanvix-probe"));
        setDisabled(btn("sync"), !online || !rt || !rt.host || jobRunning("nanvix-build") || busy.has("nanvix-sync"));
        setDisabled(btn("start"), !online || !rt || rt.running || !(p && p.reachable && p.guest_built) || busy.has("nanvix-start"));
        const dl = card.querySelector(".probe");
        dl.replaceChildren();
        if (p && p.checked) {
          const yn = (b) => el("dd", { class: b ? "yes" : "no", text: b ? "yes" : "no" });
          dl.append(el("dt", { text: "reachable" }), yn(p.reachable));
          if (p.reachable) {
            dl.append(el("dt", { text: "WHP" }), yn(p.whp),
              el("dt", { text: "branch" }), el("dd", { text: `${p.branch} @ ${(p.commit || "").slice(0, 9)}` }),
              el("dt", { text: "nanvixd built" }), yn(p.nanvixd_built),
              el("dt", { text: "guest built" }), yn(p.guest_built),
              el("dt", { text: "ctl.rs matches" }), yn(p.ctl_matches_local));
          } else if (p.error) dl.append(el("dt", { text: "error" }), el("dd", { text: p.error }));
          dl.append(el("dt", { text: "checked" }), el("dd", { text: fmtTime(p.checked) }));
        }
      }
      setDisabled(btn("stop"), !online || !rt || !rt.running || busy.has(`${name}-stop`));
    }

    // agreement
    const ag = $("agree");
    const a = S && S.agreement;
    ag.className = "badge";
    if (!a || a.runtimes.length < 2) ag.textContent = a && a.runtimes.length === 1 ? `1 runtime: ${a.runtimes[0]}` : "no controller running";
    else { ag.textContent = a.agree ? `${a.runtimes.join(" + ")} in agreement` : "runtimes DISAGREE"; ag.classList.add(a.agree ? "good" : "bad"); }

    // sim controls
    const sim = S && S.garden.sim;
    setDisabled($("btn-run"), !online || !pst || busy.has("sim"));
    $("btn-run").textContent = sim && sim.running ? "Pause" : "Start";
    for (const id of ["tick", "refill", "primary", "btn-reset"]) setDisabled($(id), !online || busy.has(id));
    if (sim) {
      if (document.activeElement !== $("tick")) $("tick").value = sim.tick_ms;
      if (document.activeElement !== $("refill")) $("refill").value = sim.refill_per_tick;
      $("primary").value = sim.primary;
      $("tick-out").textContent = `${sim.tick_ms} ms`;
      $("refill-out").textContent = `${sim.refill_per_tick} L/tick`;
    } else { $("tick-out").textContent = ""; $("refill-out").textContent = ""; }

    // svg
    const lim = pst && pst.limits;
    $("limits").textContent = lim ? `pump feeds ≤ ${lim.max_open} zones · ${lim.flow} L/tick each · max run ${lim.max_run} ticks · tank ${lim.tank_cap} L` : "";
    const tankFrac = pst ? pst.tank / pst.limits.tank_cap : 0;
    const tw = $("tank-water");
    tw.setAttribute("height", String(232 * tankFrac));
    tw.setAttribute("y", String(94 + 232 * (1 - tankFrac)));
    $("tank-text").textContent = pst ? `${pst.tank} L` : "—";
    const nOpen = pst ? pst.open.filter(Boolean).length : 0;
    $("pump").classList.toggle("pump-on", nOpen > 0 && !!(sim && sim.running));
    $("pump-text").textContent = pst ? `${nOpen}/${pst.limits.max_open} zones` : "—";
    const zones = S ? S.garden.zones : [];
    zoneEls.forEach((ze, i) => {
      const z = zones[i];
      const open = !!(pst && pst.open[i]);
      ze.g.classList.toggle("open", open);
      ze.valve.setAttribute("aria-disabled", String(!online || !running));
      ze.valve.setAttribute("aria-label", z ? `${open ? "Close" : "Open"} ${z.name} valve` : "valve");
      ze.valve.style.cursor = online && running ? "pointer" : "not-allowed";
      if (!z) { ze.name.textContent = ""; ze.info.textContent = ""; ze.fill.setAttribute("width", "0"); return; }
      ze.fill.setAttribute("width", String(390 * z.moisture / 100));
      ze.fill.setAttribute("fill", BED_COLORS[moistClass(z)]);
      ze.low.setAttribute("x1", 340 + 3.9 * z.low); ze.low.setAttribute("x2", 340 + 3.9 * z.low);
      ze.high.setAttribute("x1", 340 + 3.9 * z.high); ze.high.setAttribute("x2", 340 + 3.9 * z.high);
      ze.name.textContent = `${z.name}${z.auto ? " · auto" : ""}`;
      ze.info.textContent = `${z.moisture.toFixed(1)}%` + (pst ? `  ${open ? `watering · run ${pst.run[i]}/${pst.limits.max_run}` : "valve closed"}  ${pst.delivered[i]} L` : "");
    });

    renderZonesTable(zones, pst, running);
    renderEvents();
  }

  function renderZonesTable(zones, pst, running) {
    const tb = $("zone-rows");
    if (tb.children.length !== zones.length) {
      tb.replaceChildren();
      zones.forEach((_, i) => {
        const tr = el("tr", { "data-zone": i });
        tr.innerHTML = `<td class="zn"></td><td><span class="mbar"><i></i></span><span class="mval"></span></td>
          <td class="vstate"></td><td class="run"></td><td class="del"></td>
          <td><input type="number" class="low" min="0" max="100" step="1" aria-label="low threshold"></td>
          <td><input type="number" class="high" min="0" max="100" step="1" aria-label="high threshold"></td>
          <td><input type="checkbox" class="auto" aria-label="automatic watering"></td>
          <td class="zone-actions"><button class="open-b">Open</button><button class="close-b ghost">Close</button></td>`;
        tr.querySelector(".open-b").addEventListener("click", (e) => act(`open${i}`, e.target, () => api("POST", "/api/command", { cmd: `open ${i}` })));
        tr.querySelector(".close-b").addEventListener("click", (e) => act(`close${i}`, e.target, () => api("POST", "/api/command", { cmd: `close ${i}` })));
        for (const k of ["low", "high"]) {
          tr.querySelector(`.${k}`).addEventListener("change", (e) => act(`zone${i}`, null, () => api("POST", `/api/zone/${i}`, { [k]: Number(e.target.value) })));
        }
        tr.querySelector(".auto").addEventListener("change", (e) => act(`zone${i}`, null, () => api("POST", `/api/zone/${i}`, { auto: e.target.checked })));
        tb.append(tr);
      });
    }
    zones.forEach((z, i) => {
      const tr = tb.children[i];
      const open = !!(pst && pst.open[i]);
      tr.querySelector(".zn").textContent = z.name;
      const bar = tr.querySelector(".mbar i");
      bar.style.width = `${z.moisture}%`;
      bar.className = moistClass(z);
      tr.querySelector(".mval").textContent = `${z.moisture.toFixed(1)}%`;
      const vs = tr.querySelector(".vstate");
      vs.textContent = pst ? (open ? "open" : "closed") : "—";
      vs.className = `vstate${open ? " open" : ""}`;
      tr.querySelector(".run").textContent = pst ? String(pst.run[i]) : "—";
      tr.querySelector(".del").textContent = pst ? `${pst.delivered[i]} L` : "—";
      for (const k of ["low", "high"]) {
        const inp = tr.querySelector(`.${k}`);
        if (document.activeElement !== inp) inp.value = z[k];
        inp.disabled = !online;
      }
      const au = tr.querySelector(".auto");
      au.checked = z.auto;
      au.disabled = !online;
      tr.querySelector(".open-b").disabled = !online || !running || open || busy.has(`open${i}`);
      tr.querySelector(".close-b").disabled = !online || !running || !open || busy.has(`close${i}`);
    });
  }

  function renderEvents() {
    const ol = $("events");
    const evs = [...(S ? S.events : []), ...localErrors].sort((a, b) => b.t - a.t).slice(0, 60);
    ol.replaceChildren(...evs.map((e) => el("li", {},
      el("time", { text: fmtTime(e.t) }), el("span", { class: `k k-${e.kind}`, text: e.kind }), el("span", { text: e.text }))));
  }

  // ---------------------------------------------------------------- wire controls
  $("btn-verify").addEventListener("click", (e) => act("verify", e.target, () => api("POST", "/api/verify", {})));
  for (const name of ["macos", "nanvix"]) {
    const card = $(`rt-${name}`);
    card.querySelector('[data-act="start"]').addEventListener("click", (e) => act(`${name}-start`, e.target, () => api("POST", `/api/runtime/${name}/start`, {})));
    card.querySelector('[data-act="stop"]').addEventListener("click", (e) => act(`${name}-stop`, e.target, () => api("POST", `/api/runtime/${name}/stop`, {})));
  }
  $("rt-nanvix").querySelector('[data-act="probe"]').addEventListener("click", (e) => act("nanvix-probe", e.target, () => api("POST", "/api/nanvix/probe", {})));
  $("rt-nanvix").querySelector('[data-act="sync"]').addEventListener("click", (e) => act("nanvix-sync", e.target, () => api("POST", "/api/nanvix/sync", {})));
  $("btn-run").addEventListener("click", (e) => act("sim", e.target, () => api("POST", "/api/sim", { running: !(S && S.garden.sim.running) })));
  $("tick").addEventListener("input", (e) => ($("tick-out").textContent = `${e.target.value} ms`));
  $("tick").addEventListener("change", (e) => act("tick", null, () => api("POST", "/api/sim", { tick_ms: Number(e.target.value) })));
  $("refill").addEventListener("input", (e) => ($("refill-out").textContent = `${e.target.value} L/tick`));
  $("refill").addEventListener("change", (e) => act("refill", null, () => api("POST", "/api/sim", { refill_per_tick: Number(e.target.value) })));
  $("primary").addEventListener("change", (e) => act("primary", null, () => api("POST", "/api/sim", { primary: e.target.value })));
  $("btn-reset").addEventListener("click", (e) => {
    if (confirm("Reset the garden and stop all controllers?")) act("btn-reset", e.target, () => api("POST", "/api/reset", {}));
  });

  // ---------------------------------------------------------------- loop
  refresh();
  setInterval(() => { if (!busy.size || online) refresh(); }, 800);
  // show the newest job log on load
  setTimeout(() => { if (S && S.jobs.length && !watchedJob) watchJob(S.jobs[S.jobs.length - 1].id, ""); }, 1200);
})();
