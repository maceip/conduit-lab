#!/usr/bin/env python3
"""CONDUIT irrigation bridge: connects the irrigation web page to your local workspace.

Runs on 127.0.0.1 only. It:
  * verifies and builds the irrigation controller with the verus-stack toolchain,
  * runs the controller as a local macOS process,
  * runs the same controller as a Nanvix guest on a Windows/WHP host over SSH,
  * drives a garden simulation whose valves are decided by the verified controller.

Usage:
    python3 bridge/conduit_bridge.py [--port 8787] [--nanvix-host user@host]
                                     [--nanvix-dir 'C:\\Users\\me\\nanvix\\nanvix']

Settings given on the command line are saved to ~/.conduit-lab/bridge.json (never to the repo).
Stdlib only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import queue
import re
import subprocess
import threading
import time
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse

LAB = Path(__file__).resolve().parent.parent
CONTROLLER = LAB / "controller"
HOME_DIR = Path.home() / ".conduit-lab"
CONFIG_FILE = HOME_DIR / "bridge.json"
STATE_FILE = HOME_DIR / "irrigation-state.json"
BUILD_DIR = HOME_DIR / "build"
LOG_DIR = HOME_DIR / "logs"
GUEST_FILES = {  # repo file -> path inside <nanvix>/src/user/irrigation-controller
    "nanvix-guest/Cargo.toml": "Cargo.toml",
    "nanvix-guest/build.rs": "build.rs",
    "nanvix-guest/src/main.rs": "src/main.rs",
    "ctl.rs": "src/ctl.rs",
    "protocol.rs": "src/protocol.rs",
}
NANVIX_BRANCH = "conduit-irrigation"
ALLOWED_ORIGINS = re.compile(r"^(https://maceip\.github\.io|http://(localhost|127\.0\.0\.1)(:\d+)?)$")
VERIFY_RE = re.compile(r"verification results::\s*(\d+) verified,\s*(\d+) errors")

LOCK = threading.RLock()


def now() -> float:
    return round(time.time(), 3)


def load_json(path: Path, default):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return default


def save_json(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, indent=2))
    tmp.replace(path)


CONFIG: dict = {}


def stack_env() -> dict[str, str]:
    stack = Path(CONFIG["verus_stack"])
    out = subprocess.run(["zsh", "-c", f"source {stack / 'env.zsh'} >/dev/null && env -0"],
                         capture_output=True, check=True).stdout.decode()
    return dict(kv.split("=", 1) for kv in out.split("\0") if "=" in kv)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ------------------------------------------------------------------------------------------------
# Background jobs (verify, build, nanvix sync) with streamed logs
# ------------------------------------------------------------------------------------------------

JOBS: dict[str, dict] = {}


def run_job(kind: str, steps: list[tuple[str, list[str], dict]], on_done=None) -> str:
    """steps: (label, argv, popen kwargs). Runs sequentially in a thread; stops on first failure."""
    jid = uuid.uuid4().hex[:10]
    job = {"id": jid, "kind": kind, "status": "running", "started": now(), "finished": None,
           "log": [], "exit_code": None, "result": None}
    with LOCK:
        JOBS[jid] = job

    def work():
        code = 0
        for label, argv, kw in steps:
            job["log"].append(f"$ {label}")
            try:
                p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                     errors="replace", **kw)
                for line in p.stdout:
                    job["log"].append(line.rstrip("\n").replace(str(Path.home()), "~"))
                    if len(job["log"]) > 4000:
                        del job["log"][:1000]
                code = p.wait()
            except OSError as e:
                job["log"].append(f"failed to start: {e}")
                code = 127
            if code != 0:
                break
        job["exit_code"] = code
        job["status"] = "passed" if code == 0 else "failed"
        job["finished"] = now()
        if on_done:
            try:
                job["result"] = on_done(job)
            except Exception as e:  # noqa: BLE001 - report, never hide
                job["log"].append(f"post-processing failed: {e}")
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        (LOG_DIR / f"{kind}-{jid}.log").write_text("\n".join(job["log"]))

    threading.Thread(target=work, daemon=True).start()
    return jid


def verus_steps(compile_: bool) -> list:
    env = stack_env()
    argv = ["verus", str(CONTROLLER / "irrigation.rs")]
    if compile_:
        BUILD_DIR.mkdir(parents=True, exist_ok=True)
        argv += ["--compile", "-o", str(BUILD_DIR / "irrigation")]
    return [(" ".join(a if " " not in a else repr(a) for a in argv).replace(str(Path.home()), "~"), argv,
             {"env": env, "cwd": str(LAB)})]


def parse_verify(job) -> dict:
    text = "\n".join(job["log"])
    m = VERIFY_RE.search(text)
    res = {"verified": int(m.group(1)) if m else None, "errors": int(m.group(2)) if m else None,
           "exit_code": job["exit_code"], "at": job["finished"], "job": job["id"],
           "ctl_sha256": sha256(CONTROLLER / "ctl.rs")}
    with LOCK:
        GARDEN["verification"] = res
        persist()
    return res


# ------------------------------------------------------------------------------------------------
# Controller runtimes: the same line protocol, local process or Nanvix guest over SSH
# ------------------------------------------------------------------------------------------------

class Runtime:
    def __init__(self, name: str):
        self.name = name
        self.proc: subprocess.Popen | None = None
        self.replies: queue.Queue = queue.Queue()
        self.last: dict | None = None
        self.error: str | None = None
        self.started: float | None = None
        self.transcript: list[str] = []
        self.wlock = threading.Lock()

    def argv(self) -> list[str]:
        raise NotImplementedError

    @property
    def running(self) -> bool:
        return self.proc is not None and self.proc.poll() is None

    def start(self) -> None:
        if self.running:
            return
        self.error = None
        self.last = None
        self.replies = queue.Queue()
        self.proc = subprocess.Popen(self.argv(), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, text=True, bufsize=1, errors="replace")
        self.started = now()
        threading.Thread(target=self._reader, args=(self.proc,), daemon=True).start()
        ready = self._await(timeout=60)
        if ready is None:
            self.error = "controller did not report ready: " + " | ".join(self.transcript[-5:])
            self.stop()
            raise RuntimeError(self.error)

    def _reader(self, proc: subprocess.Popen) -> None:
        for line in proc.stdout:
            line = line.strip()
            self.transcript.append(line)
            del self.transcript[:-200]
            if line.startswith("{") and line.endswith("}"):
                try:
                    self.replies.put(json.loads(line))
                except ValueError:
                    pass
        self.replies.put(None)

    def _await(self, timeout: float) -> dict | None:
        try:
            msg = self.replies.get(timeout=timeout)
        except queue.Empty:
            return None
        if msg is not None:
            self.last = msg
        return msg

    def send(self, cmd: str, timeout: float = 15) -> dict | None:
        with self.wlock:
            if not self.running:
                return None
            try:
                self.proc.stdin.write(cmd + "\n")
                self.proc.stdin.flush()
            except OSError as e:
                self.error = f"write failed: {e}"
                return None
            reply = self._await(timeout)
            if reply is None:
                self.error = f"no reply to '{cmd}'"
            return reply

    def stop(self) -> None:
        if self.proc:
            try:
                if self.proc.poll() is None:
                    self.proc.stdin.write("quit\n")
                    self.proc.stdin.flush()
                    self.proc.wait(timeout=5)
            except (OSError, subprocess.TimeoutExpired):
                self.proc.kill()
        self.proc = None

    def info(self) -> dict:
        return {"name": self.name, "running": self.running, "started": self.started, "error": self.error,
                "state": self.last, "transcript_tail": self.transcript[-8:]}


class MacRuntime(Runtime):
    def argv(self):
        binary = BUILD_DIR / "irrigation"
        if not binary.exists():
            raise RuntimeError("controller not built yet: press Verify & build")
        return [str(binary)]

    def info(self):
        d = super().info()
        b = BUILD_DIR / "irrigation"
        d["binary"] = str(b).replace(str(Path.home()), "~") if b.exists() else None
        return d


def ssh_base() -> list[str]:
    return ["ssh", "-T", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", "-o", "ServerAliveInterval=15",
            CONFIG["nanvix_host"]]


def ps(script: str) -> list[str]:
    return ssh_base() + [f'powershell -NoProfile -ExecutionPolicy Bypass -Command "{script}"']


class NanvixRuntime(Runtime):
    def argv(self):
        if not CONFIG.get("nanvix_host"):
            raise RuntimeError("no Nanvix host configured (start the bridge with --nanvix-host)")
        d = CONFIG["nanvix_dir"]
        return ssh_base() + [f'cd /d "{d}" && bin\\nanvixd.exe -- bin\\irrigation-controller.elf']

    def info(self):
        d = super().info()
        d["host"] = CONFIG.get("nanvix_host")
        d["dir"] = CONFIG.get("nanvix_dir")
        d["probe"] = NANVIX_PROBE
        return d


RUNTIMES = {"macos": MacRuntime("macos"), "nanvix": NanvixRuntime("nanvix")}
NANVIX_PROBE: dict = {"checked": None}


def probe_nanvix() -> dict:
    """Checks the Windows host: reachable, WHP present, branch checked out, guest built."""
    global NANVIX_PROBE
    if not CONFIG.get("nanvix_host"):
        NANVIX_PROBE = {"checked": now(), "reachable": False, "error": "no host configured"}
        return NANVIX_PROBE
    d = CONFIG["nanvix_dir"]
    script = (f"cd '{d}'; "
              "Write-Output ('whp=' + (Test-Path C:/Windows/System32/WinHvPlatform.dll)); "
              "Write-Output ('branch=' + (git rev-parse --abbrev-ref HEAD)); "
              "Write-Output ('commit=' + (git rev-parse HEAD)); "
              "Write-Output ('nanvixd=' + (Test-Path bin/nanvixd.exe)); "
              "Write-Output ('guest=' + (Test-Path bin/irrigation-controller.elf)); "
              "if (Test-Path src/user/irrigation-controller/src/ctl.rs) "
              "{ Write-Output ('ctl=' + (Get-FileHash src/user/irrigation-controller/src/ctl.rs).Hash.ToLower()) }")
    try:
        p = subprocess.run(ps(script), capture_output=True, text=True, timeout=30)
    except subprocess.TimeoutExpired:
        NANVIX_PROBE = {"checked": now(), "reachable": False, "error": "ssh timed out"}
        return NANVIX_PROBE
    kv = dict(l.strip().split("=", 1) for l in p.stdout.splitlines() if "=" in l)
    local = sha256(CONTROLLER / "ctl.rs")
    NANVIX_PROBE = {
        "checked": now(), "reachable": p.returncode == 0, "error": p.stderr.strip()[-300:] or None,
        "whp": kv.get("whp") == "True", "branch": kv.get("branch"), "commit": kv.get("commit"),
        "nanvixd_built": kv.get("nanvixd") == "True", "guest_built": kv.get("guest") == "True",
        "ctl_sha256": kv.get("ctl"), "ctl_matches_local": kv.get("ctl") == local,
    }
    return NANVIX_PROBE


def nanvix_sync_steps() -> list:
    """Copies the guest sources to the Windows host and builds them there."""
    d = CONFIG["nanvix_dir"]
    host = CONFIG["nanvix_host"]
    steps = [("git fetch + checkout " + NANVIX_BRANCH,
              ps(f"cd '{d}'; git fetch https://github.com/maceip/nanvix.git {NANVIX_BRANCH} 2>&1; "
                 f"git checkout -B {NANVIX_BRANCH} FETCH_HEAD 2>&1; exit $LASTEXITCODE"), {})]
    remote_dir = d.replace("\\", "/") + "/src/user/irrigation-controller"
    for src, dst in GUEST_FILES.items():
        steps.append((f"scp controller/{src} -> {dst}",
                      ["scp", "-q", "-o", "BatchMode=yes", str(CONTROLLER / src), f"{host}:{remote_dir}/{dst}"], {}))
    # Nanvix's Windows build needs an MSVC-host Rust; pin it for this build only (no global rustup change).
    channel = "(Select-String -Path rust-toolchain -Pattern 'channel' | % { ($_ -split [char]34)[1] })"
    steps.append(("z.ps1 build -- all (MSVC host toolchain)",
                  ps(f"cd '{d}'; $env:RUSTUP_TOOLCHAIN = {channel} + '-x86_64-pc-windows-msvc'; "
                     "Write-Output ('toolchain=' + $env:RUSTUP_TOOLCHAIN); "
                     ".\\z.ps1 build -- all 2>&1; exit $LASTEXITCODE"), {}))
    return steps


# ------------------------------------------------------------------------------------------------
# Garden simulation
# ------------------------------------------------------------------------------------------------
# RYAN EXPLICIT MOCK/FALLBACK AUTHORIZATION: "it does something via the web that has some controls that like do some form of irrigation type work" / selected option: "Literal irrigation sim"
# The soil-moisture model below is a simulation by design. Valve decisions, tank level and
# delivered water are NOT simulated here: they come from the verified controller's replies.

ZONE_NAMES = ["North beds", "Orchard", "Greenhouse", "Lawn"]
DEFAULT_GARDEN = {
    "zones": [{"name": n, "moisture": 55.0, "low": 35.0, "high": 70.0, "auto": True,
               "et_per_tick": et, "pct_per_liter": 0.4} for n, et in zip(ZONE_NAMES, [0.35, 0.25, 0.5, 0.45])],
    "sim": {"running": False, "tick_ms": 1000, "refill_per_tick": 6, "primary": "macos"},
    "events": [],
    "verification": None,
    "ticks": 0,
}
GARDEN: dict = {}


def persist() -> None:
    save_json(STATE_FILE, GARDEN)


def event(kind: str, text: str) -> None:
    GARDEN["events"].append({"t": now(), "kind": kind, "text": text})
    del GARDEN["events"][:-200]


def broadcast(cmd: str) -> dict:
    """Sends a command to every running runtime. Returns replies keyed by runtime."""
    replies = {}
    for name, rt in RUNTIMES.items():
        if rt.running:
            replies[name] = rt.send(cmd)
    return replies


def comparable(state: dict | None):
    if not state:
        return None
    return {k: state[k] for k in ("open", "run", "delivered", "tank", "ticks")}


def agreement() -> dict:
    states = {n: comparable(rt.last) for n, rt in RUNTIMES.items() if rt.running and rt.last}
    vals = list(states.values())
    return {"runtimes": list(states), "agree": len(vals) >= 2 and all(v == vals[0] for v in vals) if vals else None}


def primary_state() -> dict | None:
    want = GARDEN["sim"]["primary"]
    rt = RUNTIMES.get(want)
    if rt and rt.running and rt.last:
        return rt.last
    return None


def sim_step() -> None:
    with LOCK:
        before = primary_state()
        if before is None:
            return
        prev_delivered = list(before["delivered"])
        refill = int(GARDEN["sim"]["refill_per_tick"])
        if refill > 0:
            broadcast(f"refill {refill}")
        replies = broadcast("tick")
        after = primary_state()
        if after is None:
            return
        GARDEN["ticks"] += 1
        for i, z in enumerate(GARDEN["zones"]):
            gained = after["delivered"][i] - prev_delivered[i]
            z["moisture"] = round(min(100.0, max(0.0, z["moisture"] - z["et_per_tick"] + gained * z["pct_per_liter"])), 2)
            if before["open"][i] and not after["open"][i]:
                event("auto-close", f"controller closed {z['name']} (run limit or tank)")
        # auto mode: ask the verified controller; it may deny
        for i, z in enumerate(GARDEN["zones"]):
            if not z["auto"]:
                continue
            is_open = after["open"][i]
            if not is_open and z["moisture"] < z["low"]:
                r = broadcast(f"open {i}").get(GARDEN["sim"]["primary"])
                if r and r["ok"]:
                    event("open", f"auto: opened {z['name']} at {z['moisture']}%")
                elif r:
                    z.setdefault("denied", 0)
                    z["denied"] += 1
            elif is_open and z["moisture"] >= z["high"]:
                broadcast(f"close {i}")
                event("close", f"auto: closed {z['name']} at {z['moisture']}%")
        if not agreement()["agree"] and len(agreement()["runtimes"]) >= 2:
            event("divergence", "runtimes disagree: " + json.dumps({n: comparable(RUNTIMES[n].last) for n in agreement()["runtimes"]}))
        if GARDEN["ticks"] % 5 == 0:
            persist()


def sim_loop() -> None:
    while True:
        tick = max(200, int(GARDEN["sim"]["tick_ms"])) / 1000
        if GARDEN["sim"]["running"]:
            try:
                sim_step()
            except Exception as e:  # noqa: BLE001
                with LOCK:
                    event("error", f"sim step failed: {e}")
        time.sleep(tick)


# ------------------------------------------------------------------------------------------------
# HTTP API
# ------------------------------------------------------------------------------------------------

def status() -> dict:
    with LOCK:
        return {
            "bridge": {"version": 1, "pid": os.getpid(), "lab": str(LAB).replace(str(Path.home()), "~"),
                       "verus_stack": CONFIG["verus_stack"].replace(str(Path.home()), "~"),
                       "state_file": str(STATE_FILE).replace(str(Path.home()), "~")},
            "garden": {k: GARDEN[k] for k in ("zones", "sim", "ticks", "verification")},
            "events": GARDEN["events"][-40:],
            "runtimes": {n: rt.info() for n, rt in RUNTIMES.items()},
            "agreement": agreement(),
            "jobs": [{k: j[k] for k in ("id", "kind", "status", "started", "finished", "exit_code", "result")}
                     for j in list(JOBS.values())[-10:]],
        }


class Handler(BaseHTTPRequestHandler):
    server_version = "conduit-bridge/1"

    def log_message(self, fmt, *args):  # quieter console
        pass

    def _origin_ok(self) -> bool:
        origin = self.headers.get("Origin")
        return origin is None or bool(ALLOWED_ORIGINS.match(origin))

    def _cors(self):
        origin = self.headers.get("Origin")
        if origin and ALLOWED_ORIGINS.match(origin):
            self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Vary", "Origin")
            self.send_header("Access-Control-Allow-Private-Network", "true")

    def _send(self, code: int, body: dict):
        data = json.dumps(body).encode()
        self.send_response(code)
        self._cors()
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_OPTIONS(self):
        if not self._origin_ok():
            return self._send(403, {"error": "origin not allowed"})
        self.send_response(204)
        self._cors()
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Max-Age", "600")
        self.end_headers()

    def do_GET(self):
        if not self._origin_ok():
            return self._send(403, {"error": "origin not allowed"})
        path = urlparse(self.path).path
        if path == "/api/status":
            return self._send(200, status())
        m = re.fullmatch(r"/api/jobs/(\w+)", path)
        if m and m.group(1) in JOBS:
            j = JOBS[m.group(1)]
            return self._send(200, {**{k: j[k] for k in j if k != "log"}, "log": j["log"][-400:]})
        return self._send(404, {"error": "not found"})

    def do_POST(self):
        # JSON content type forces a CORS preflight, so other websites cannot fire blind POSTs.
        if not self._origin_ok() or "application/json" not in (self.headers.get("Content-Type") or ""):
            return self._send(403, {"error": "origin or content type not allowed"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            return self._send(400, {"error": "invalid JSON"})
        path = urlparse(self.path).path
        try:
            return self._send(200, self.route(path, body))
        except LookupError as e:
            return self._send(404, {"error": str(e)})
        except (RuntimeError, ValueError, OSError) as e:
            return self._send(409, {"error": str(e)})

    def route(self, path: str, body: dict) -> dict:
        if path == "/api/verify":
            return {"job": run_job("verify", verus_steps(compile_=True), on_done=parse_verify)}
        if path == "/api/nanvix/probe":
            return {"probe": probe_nanvix()}
        if path == "/api/nanvix/sync":
            if not CONFIG.get("nanvix_host"):
                raise RuntimeError("no Nanvix host configured")
            return {"job": run_job("nanvix-build", nanvix_sync_steps(), on_done=lambda j: probe_nanvix())}
        m = re.fullmatch(r"/api/runtime/(macos|nanvix)/(start|stop)", path)
        if m:
            rt = RUNTIMES[m.group(1)]
            if m.group(2) == "start":
                rt.start()
                with LOCK:
                    event("runtime", f"{rt.name} controller started")
            else:
                rt.stop()
                with LOCK:
                    event("runtime", f"{rt.name} controller stopped")
            return {"runtime": rt.info()}
        if path == "/api/command":
            cmd = str(body.get("cmd", ""))
            if not re.fullmatch(r"(open|close) [0-3]|refill \d{1,4}|state|tick", cmd):
                raise ValueError("unsupported command")
            with LOCK:
                replies = broadcast(cmd)
                if not replies:
                    raise RuntimeError("no controller running")
                if cmd.startswith(("open", "close")):
                    z = GARDEN["zones"][int(cmd.split()[1])]
                    r = replies.get(GARDEN["sim"]["primary"]) or next(iter(replies.values()))
                    event(cmd.split()[0] if r and r["ok"] else "denied",
                          f"manual {cmd.split()[0]} {z['name']}: {r['msg'] if r else 'no reply'}")
                return {"replies": replies, "agreement": agreement()}
        if path == "/api/sim":
            with LOCK:
                s = GARDEN["sim"]
                if "running" in body:
                    s["running"] = bool(body["running"])
                    event("sim", "simulation " + ("started" if s["running"] else "paused"))
                if "tick_ms" in body:
                    s["tick_ms"] = min(10000, max(200, int(body["tick_ms"])))
                if "refill_per_tick" in body:
                    s["refill_per_tick"] = min(50, max(0, int(body["refill_per_tick"])))
                if body.get("primary") in RUNTIMES:
                    s["primary"] = body["primary"]
                persist()
                return {"sim": s}
        m = re.fullmatch(r"/api/zone/([0-3])", path)
        if m:
            with LOCK:
                z = GARDEN["zones"][int(m.group(1))]
                for k in ("low", "high"):
                    if k in body:
                        z[k] = min(100.0, max(0.0, float(body[k])))
                if "auto" in body:
                    z["auto"] = bool(body["auto"])
                if z["low"] >= z["high"]:
                    raise ValueError("low threshold must be below high threshold")
                persist()
                return {"zone": z}
        if path == "/api/reset":
            with LOCK:
                GARDEN.clear()
                GARDEN.update(json.loads(json.dumps(DEFAULT_GARDEN)))
                event("sim", "garden reset")
                persist()
            for rt in RUNTIMES.values():
                if rt.running:
                    rt.stop()
            return {"ok": True}
        raise LookupError("not found")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--port", type=int)
    ap.add_argument("--verus-stack")
    ap.add_argument("--nanvix-host", help="SSH target of the Windows/WHP machine, e.g. user@10.0.0.5")
    ap.add_argument("--nanvix-dir", help="Nanvix checkout on that machine")
    ap.add_argument("--state-dir", help="where config, garden state, builds and logs live (default ~/.conduit-lab)")
    ap.add_argument("--no-save-config", action="store_true", help="do not write CLI settings back to the config file")
    args = ap.parse_args()

    global HOME_DIR, CONFIG_FILE, STATE_FILE, BUILD_DIR, LOG_DIR
    if args.state_dir:
        HOME_DIR = Path(args.state_dir).expanduser().resolve()
        CONFIG_FILE, STATE_FILE = HOME_DIR / "bridge.json", HOME_DIR / "irrigation-state.json"
        BUILD_DIR, LOG_DIR = HOME_DIR / "build", HOME_DIR / "logs"

    CONFIG.update({"port": 8787, "verus_stack": str(Path.home() / "workspaces" / "verus-stack"),
                   "nanvix_host": None, "nanvix_dir": None})
    CONFIG.update(load_json(CONFIG_FILE, {}))
    for k in ("port", "verus_stack", "nanvix_host", "nanvix_dir"):
        v = getattr(args, k)
        if v is not None:
            CONFIG[k] = v
    if CONFIG["nanvix_host"] and not CONFIG["nanvix_dir"]:
        user = CONFIG["nanvix_host"].split("@")[0]
        CONFIG["nanvix_dir"] = f"C:\\Users\\{user}\\nanvix\\nanvix"
    if not args.no_save_config:
        save_json(CONFIG_FILE, CONFIG)

    GARDEN.update(json.loads(json.dumps(DEFAULT_GARDEN)))
    saved = load_json(STATE_FILE, None)
    if saved:
        GARDEN.update({k: saved[k] for k in DEFAULT_GARDEN if k in saved})
    GARDEN["sim"]["running"] = False  # never resume watering unattended after a restart

    threading.Thread(target=sim_loop, daemon=True).start()
    if CONFIG["nanvix_host"]:
        threading.Thread(target=probe_nanvix, daemon=True).start()
    srv = ThreadingHTTPServer(("127.0.0.1", int(CONFIG["port"])), Handler)
    print(f"conduit bridge on http://127.0.0.1:{CONFIG['port']}  (config: {CONFIG_FILE})")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        for rt in RUNTIMES.values():
            rt.stop()


if __name__ == "__main__":
    main()
