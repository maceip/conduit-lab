#!/usr/bin/env python3
"""Regenerate data/stats.json by actually running the CONDUIT workspace tools.

Every value the site displays comes from this file. Nothing is hard-coded in
index.html; if a check is not run, it is recorded as not run, never guessed.

Usage:
    python3 scripts/collect_stats.py                # default workspace
    python3 scripts/collect_stats.py --with-mathlib # also build mathlib benchmarks
    VERUS_STACK=/path/to/verus-stack python3 scripts/collect_stats.py
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import platform
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

SITE = Path(__file__).resolve().parent.parent
DATA = SITE / "data"
LOGS = DATA / "logs"
STACK = Path(os.environ.get("VERUS_STACK", Path.home() / "workspaces" / "verus-stack"))
REPOS = ["verus", "VeriStruct", "skydiscover", "vero"]
EXAMPLES = ["vectors.rs"]


def stack_env() -> dict[str, str]:
    """Load the environment exported by env.zsh (the workspace's single source of truth)."""
    out = subprocess.run(
        ["zsh", "-c", f"source {STACK / 'env.zsh'} >/dev/null && env -0"],
        capture_output=True, check=True,
    ).stdout.decode()
    return dict(kv.split("=", 1) for kv in out.split("\0") if "=" in kv)


ENV: dict[str, str] = {}


def run(cmd: list[str], cwd: Path | None = None, log: str | None = None,
        timeout: int = 1800, extra_env: dict[str, str] | None = None) -> tuple[int, str, float]:
    env = {**ENV, **(extra_env or {})}
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        code, text = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        code = -1
        text = f"TIMEOUT after {timeout}s\n" + ((e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""))
    secs = round(time.monotonic() - t0, 2)
    if log:
        LOGS.mkdir(parents=True, exist_ok=True)
        body = f"$ {' '.join(cmd)}\n# cwd: {cwd}\n# exit: {code}  seconds: {secs}\n\n{text}"
        (LOGS / log).write_text(body.replace(str(Path.home()), "~"))  # logs are published
    return code, text, secs


def first_line(cmd: list[str]) -> str | None:
    code, text, _ = run(cmd)
    return text.strip().splitlines()[0] if code == 0 and text.strip() else None


VERIFY_RE = re.compile(r"verification results::\s*(\d+) verified,\s*(\d+) errors")


def parse_verus(code: int, text: str, secs: float, log: str) -> dict:
    m = VERIFY_RE.search(text)
    return {
        "exit_code": code,
        "verified": int(m.group(1)) if m else None,
        "errors": int(m.group(2)) if m else None,
        "seconds": secs,
        "log": f"data/logs/{log}",
    }


def toolchains() -> dict:
    release = Path(ENV["VERUS_RELEASE"])
    ver = release / "version.txt"
    return {
        "z3": first_line([ENV["VERUS_Z3_PATH"], "--version"]),
        "rustc": first_line(["rustc", "--version"]),
        "verus": ver.read_text().strip() if ver.exists() else None,
        "lean": first_line(["lean", "--version"]),
        "lake": first_line(["lake", "--version"]),
        "uv": first_line(["uv", "--version"]),
    }


def repos() -> list[dict]:
    out = []
    for name in REPOS:
        d = STACK / name
        _, sha, _ = run(["git", "-C", str(d), "rev-parse", "HEAD"])
        _, date, _ = run(["git", "-C", str(d), "log", "-1", "--format=%cI"])
        _, dirty, _ = run(["git", "-C", str(d), "status", "--porcelain"])
        _, url, _ = run(["git", "-C", str(d), "remote", "get-url", "origin"])
        out.append({
            "name": name,
            "commit": sha.strip() or None,
            "commit_date": date.strip() or None,
            "uncommitted_files": len([l for l in dirty.splitlines() if l.strip()]),
            "remote": url.strip() or None,
        })
    return out


def verify_vstd() -> dict:
    """Same invocation vstd_build uses (std + alloc features), but into a temp out-dir
    so the installed release artifacts are never overwritten."""
    r = Path(ENV["VERUS_RELEASE"])
    with tempfile.TemporaryDirectory() as out:
        cmd = [
            "verus", "--internal-test-mode",
            "--extern", f"verus_builtin={r / 'libverus_builtin.rlib'}",
            "--extern", f"verus_builtin_macros={r / 'libverus_builtin_macros.dylib'}",
            "--extern", f"verus_state_machines_macros={r / 'libverus_state_machines_macros.dylib'}",
            "--crate-type=lib", "--export", f"{out}/vstd.vir", "--out-dir", out,
            "--multiple-errors", "2", "--is-vstd",
            "--cfg", 'feature="std"', "--cfg", 'feature="alloc"', "vstd.rs",
        ]
        code, text, secs = run(cmd, cwd=Path(ENV["VERUS_SOURCE"]) / "vstd", log="vstd.log",
                               extra_env={"VSTD_KIND": "IsVstd", "RUST_MIN_STACK": str(10 * 1024 * 1024)})
    return parse_verus(code, text, secs, "vstd.log")


def verify_examples() -> list[dict]:
    res = []
    (DATA / "examples").mkdir(parents=True, exist_ok=True)
    for ex in EXAMPLES:
        # publish the exact source that was verified, so the page never embeds a stale copy
        shutil.copyfile(Path(ENV["VERUS_SOURCE"]).parent / "examples" / ex, DATA / "examples" / ex)
        log = f"example-{ex}.log"
        code, text, secs = run(["verus", f"../examples/{ex}"], cwd=Path(ENV["VERUS_SOURCE"]), log=log)
        res.append({"file": f"verus/examples/{ex}", "source": f"data/examples/{ex}",
                    **parse_verus(code, text, secs, log)})
    return res


SORRY_RE = re.compile(r"\bsorry\b")
JOBS_RE = re.compile(r"Build completed successfully \((\d+) jobs?\)")


def lean_benchmarks(with_mathlib: bool) -> list[dict]:
    root = STACK / "vero" / "benchmarks"
    res = []
    for d in sorted(p for p in root.iterdir() if p.is_dir()):
        lakefiles = list(d.glob("lakefile.*"))
        needs_mathlib = any("mathlib" in f.read_text().lower() for f in lakefiles)
        sorries = sum(len(SORRY_RE.findall(f.read_text(errors="ignore")))
                      for f in d.rglob("*.lean") if ".lake" not in f.parts)
        entry = {"name": d.name, "needs_mathlib": needs_mathlib, "sorry_count": sorries}
        if not lakefiles:
            res.append({**entry, "status": "no_lakefile"})
            continue
        if needs_mathlib and not with_mathlib:
            res.append({**entry, "status": "skipped_mathlib"})
            continue
        log = f"lean-{d.name}.log"
        code, text, secs = run(["lake", "build"], cwd=d, log=log, timeout=3600)
        m = JOBS_RE.search(text)
        res.append({
            **entry,
            "status": "passed" if code == 0 else ("timeout" if code == -1 else "failed"),
            "jobs": int(m.group(1)) if m else None,
            "seconds": secs,
            "log": f"data/logs/{log}",
        })
    return res


def cli_smoke() -> list[dict]:
    checks = [
        ("cargo-verus", ["cargo", "verus", "--help"], STACK),
        ("skydiscover", ["uv", "run", "skydiscover", "--help"], STACK / "skydiscover"),
    ]
    out = []
    for name, cmd, cwd in checks:
        log = f"cli-{name}.log"
        code, _, secs = run(cmd, cwd=cwd, log=log, timeout=300)
        out.append({"name": name, "command": " ".join(cmd), "exit_code": code,
                    "seconds": secs, "log": f"data/logs/{log}"})
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--with-mathlib", action="store_true",
                    help="also build benchmarks that depend on mathlib (large download)")
    args = ap.parse_args()

    global ENV
    ENV = stack_env()
    if LOGS.exists():
        shutil.rmtree(LOGS)
    LOGS.mkdir(parents=True)

    started = dt.datetime.now(dt.timezone.utc)
    stats = {
        "schema": 1,
        "generated_at": started.isoformat(timespec="seconds"),
        "generator": "scripts/collect_stats.py",
        "host": {"machine": platform.machine(), "system": platform.system(),
                 "release": platform.mac_ver()[0] or platform.release()},
        "toolchains": toolchains(),
        "repos": repos(),
        "verus": {"vstd": verify_vstd(), "examples": verify_examples()},
        "lean": {"benchmarks": lean_benchmarks(args.with_mathlib)},
        "cli": cli_smoke(),
    }
    stats["duration_seconds"] = round((dt.datetime.now(dt.timezone.utc) - started).total_seconds(), 1)
    (DATA / "stats.json").write_text(json.dumps(stats, indent=2) + "\n")
    print(f"wrote {DATA / 'stats.json'}")


if __name__ == "__main__":
    main()
